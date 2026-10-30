/*
 * Copyright (c) 2025 OceanBase.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#define USING_LOG_PREFIX SERVER

#include "ob_ai_column_worker.h"

#include <atomic>
#include <cctype>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <thread>
#include <vector>

#include "lib/ob_define.h"
#include "lib/oblog/ob_log_module.h"
#include "lib/string/ob_string.h"
#include "lib/time/ob_time_utility.h"
#include "lib/worker.h"
#include "common/mysqlclient/ob_mysql_proxy.h"
#include "common/mysqlclient/ob_mysql_result.h"

// The AI column DML hook (sql/engine/dml/ob_table_modify_op.cpp) skips all AI
// column maintenance when this thread local flag is set. Keep this one call
// site: the Lead replaces the body of set_ai_column_internal_write() with the
// shared hook-suppression helper at integration time.
namespace oceanbase
{
namespace sql
{
namespace ai_column_dml_util
{
extern thread_local bool g_ai_column_internal_write;
}
}
namespace observer
{

void set_ai_column_internal_write(bool value)
{
  ::oceanbase::sql::ai_column_dml_util::g_ai_column_internal_write = value;
}

namespace
{

// Polling cadence. The official tests sleep 100ms between retries and the
// stale-guard case requires the worker to have picked up a task within 300ms,
// so keep the idle interval at 50ms.
const int64_t AI_COLUMN_WORKER_POLL_INTERVAL_MS = 50;
const int64_t AI_COLUMN_WORKER_STARTUP_DELAY_MS = 200;
// task.eligible_ts is an epoch microsecond integer (ObTimeUtility::current_time()).
// The DML hook writes it and the worker compares it against a C++ computed
// microsecond literal: "eligible_ts <= now(6)" in SQL has surprising implicit
// cast semantics, so it is deliberately not used here.
const int64_t AI_COLUMN_WORKER_RETRY_BACKOFF_US = 1000000; // 1s

const char *const AI_TYPE_PROMPT_MARKER = " [AI_TYPE_PROMPT]";
const char *const AI_DEPS_MARKER = " [AI_DEPS]";

struct AITaskRow
{
  AITaskRow()
    : task_id_(0),
      table_id_(0),
      column_id_(0),
      state_(0),
      retry_count_(0),
      eligible_ts_(0),
      result_type_(0),
      vector_dim_(0),
      max_retries_(0)
  {}
  int64_t task_id_;
  int64_t table_id_;
  int64_t column_id_;
  int64_t state_;
  int64_t retry_count_;
  int64_t eligible_ts_;
  int64_t result_type_;
  int64_t vector_dim_;
  int64_t max_retries_;
  std::string request_id_;
  std::string rowkey_predicate_;
  std::string column_name_;
  std::string normalized_expr_;
  std::string model_name_;
  std::string func_type_;
  std::string db_name_;
  std::string table_name_;
};

struct AIColumnCall
{
  AIColumnCall() : func_type_(0) {}
  int64_t func_type_; // 1: ai_complete, 2: ai_embed
  std::string model_literal_;
  std::string prompt_expr_;
  std::string type_prompt_;
  std::string extra_arg_;
};

struct AIWriteValue
{
  std::string column_name_;
  std::string sql_value_;
};

bool iequals(const std::string &lhs, const char *rhs)
{
  bool equal = true;
  const int64_t lhs_len = static_cast<int64_t>(lhs.length());
  const int64_t rhs_len = NULL == rhs ? 0 : static_cast<int64_t>(strlen(rhs));
  if (lhs_len != rhs_len) {
    equal = false;
  } else {
    for (int64_t i = 0; equal && i < lhs_len; ++i) {
      equal = (tolower(static_cast<unsigned char>(lhs[static_cast<size_t>(i)]))
               == tolower(static_cast<unsigned char>(rhs[i])));
    }
  }
  return equal;
}

std::string trim_copy(const std::string &input)
{
  size_t begin = 0;
  size_t end = input.size();
  while (begin < end && isspace(static_cast<unsigned char>(input[begin]))) {
    ++begin;
  }
  while (end > begin && isspace(static_cast<unsigned char>(input[end - 1]))) {
    --end;
  }
  return input.substr(begin, end - begin);
}

void append_int64(std::string &sql, const int64_t value)
{
  char buf[32];
  const int n = snprintf(buf, sizeof(buf), "%ld", value);
  if (n > 0) {
    sql.append(buf, static_cast<size_t>(n));
  }
}

void append_quoted_string(std::string &sql, const std::string &value)
{
  sql.push_back('\'');
  for (size_t i = 0; i < value.size(); ++i) {
    const char c = value[i];
    if ('\'' == c) {
      sql.append("''");
    } else if ('\\' == c) {
      sql.append("\\\\");
    } else {
      sql.push_back(c);
    }
  }
  sql.push_back('\'');
}

void append_backtick_ident(std::string &sql, const std::string &name)
{
  sql.push_back('`');
  for (size_t i = 0; i < name.size(); ++i) {
    const char c = name[i];
    if ('`' == c) {
      sql.push_back('`');
    }
    sql.push_back(c);
  }
  sql.push_back('`');
}

void append_qualified_table(std::string &sql,
                            const std::string &db_name,
                            const std::string &table_name)
{
  append_backtick_ident(sql, db_name);
  sql.push_back('.');
  append_backtick_ident(sql, table_name);
}

void append_task_id_list(std::string &sql, const std::vector<AITaskRow> &group)
{
  for (size_t i = 0; i < group.size(); ++i) {
    if (i > 0) {
      sql.push_back(',');
    }
    append_int64(sql, group[i].task_id_);
  }
}

// Splits the argument list of a rendered SQL function call on top level commas,
// honouring quoted strings, backtick identifiers and nested parentheses.
int split_top_level_args(const std::string &text, std::vector<std::string> &args)
{
  int ret = OB_SUCCESS;
  int64_t depth = 0;
  char quote = '\0';
  bool escape = false;
  std::string current;
  for (size_t i = 0; OB_SUCC(ret) && i < text.size(); ++i) {
    const char c = text[i];
    if ('\0' != quote) {
      current.push_back(c);
      if (escape) {
        escape = false;
      } else if ('\\' == c) {
        escape = true;
      } else if (c == quote) {
        quote = '\0';
      }
    } else if ('\'' == c || '\"' == c || '`' == c) {
      quote = c;
      current.push_back(c);
    } else if ('(' == c || '[' == c) {
      ++depth;
      current.push_back(c);
    } else if (')' == c || ']' == c) {
      --depth;
      current.push_back(c);
    } else if (',' == c && 0 == depth) {
      args.push_back(trim_copy(current));
      current.clear();
    } else {
      current.push_back(c);
    }
  }
  if (OB_SUCC(ret)) {
    if ('\0' != quote || 0 != depth) {
      ret = OB_ERR_UNEXPECTED;
    } else {
      args.push_back(trim_copy(current));
    }
  }
  return ret;
}

// __all_ai_column.normalized_expr has the shape
//   AI_COMPLETE('model', concat('Classify: ', content)) [AI_TYPE_PROMPT]... [AI_DEPS]content
// AI_EMBED columns carry no typed-result prompt. The " [AI_TYPE_PROMPT]" part is
// the system message for the typed result contract which the worker must send.
int parse_ai_column_desc(const std::string &raw_expr,
                         const std::string &func_type_hint,
                         AIColumnCall &call)
{
  int ret = OB_SUCCESS;
  call = AIColumnCall();
  const size_t type_prompt_pos = raw_expr.find(AI_TYPE_PROMPT_MARKER);
  const size_t deps_pos = raw_expr.find(AI_DEPS_MARKER);
  size_t call_end = raw_expr.size();
  if (std::string::npos != type_prompt_pos && type_prompt_pos < call_end) {
    call_end = type_prompt_pos;
  }
  if (std::string::npos != deps_pos && deps_pos < call_end) {
    call_end = deps_pos;
  }
  const std::string call_text = trim_copy(raw_expr.substr(0, call_end));
  if (std::string::npos != type_prompt_pos) {
    const size_t prompt_begin = type_prompt_pos + strlen(AI_TYPE_PROMPT_MARKER);
    size_t prompt_end = raw_expr.size();
    if (std::string::npos != deps_pos && deps_pos >= prompt_begin && deps_pos < prompt_end) {
      prompt_end = deps_pos;
    }
    if (prompt_end > prompt_begin) {
      call.type_prompt_ = trim_copy(raw_expr.substr(prompt_begin, prompt_end - prompt_begin));
    }
  }
  const size_t lparen = call_text.find('(');
  if (call_text.empty() || std::string::npos == lparen
      || ')' != call_text[call_text.size() - 1]) {
    ret = OB_ERR_UNEXPECTED;
    LOG_WARN("[AI_COLUMN_WORKER] invalid normalized ai expression", K(ret),
             "expr", raw_expr.c_str());
  } else {
    const std::string func_name = trim_copy(call_text.substr(0, lparen));
    const std::string args_text = call_text.substr(lparen + 1, call_text.size() - lparen - 2);
    std::vector<std::string> args;
    int64_t hint = 0;
    if ("1" == func_type_hint) {
      hint = 1;
    } else if ("2" == func_type_hint) {
      hint = 2;
    }
    if (OB_FAIL(split_top_level_args(args_text, args))) {
      LOG_WARN("[AI_COLUMN_WORKER] split ai call args failed", K(ret), "args", args_text.c_str());
    } else if (args.size() < 2) {
      ret = OB_ERR_UNEXPECTED;
      LOG_WARN("[AI_COLUMN_WORKER] too few ai call args", K(ret), "args", args_text.c_str());
    } else {
      int64_t parsed = 0;
      if (iequals(func_name, "ai_complete")) {
        parsed = 1;
      } else if (iequals(func_name, "ai_embed")) {
        parsed = 2;
      } else {
        parsed = hint;
      }
      if (0 == parsed) {
        ret = OB_ERR_UNEXPECTED;
        LOG_WARN("[AI_COLUMN_WORKER] unknown ai function", K(ret), "func", func_name.c_str());
      } else {
        call.func_type_ = parsed;
        call.model_literal_ = args[0];
        call.prompt_expr_ = args[1];
        if (args.size() > 2) {
          call.extra_arg_ = args[2];
        }
      }
    }
  }
  return ret;
}

int build_ai_sql(const AITaskRow &task, const AIColumnCall &call, std::string &sql)
{
  int ret = OB_SUCCESS;
  std::string model_literal;
  if (!task.model_name_.empty()) {
    append_quoted_string(model_literal, task.model_name_);
  } else {
    model_literal = call.model_literal_;
  }
  if (model_literal.empty() || call.prompt_expr_.empty()) {
    ret = OB_ERR_UNEXPECTED;
    LOG_WARN("[AI_COLUMN_WORKER] incomplete ai call", K(ret),
             "model", task.model_name_.c_str(), "column", task.column_name_.c_str());
  } else {
    sql.assign("SELECT ");
    if (2 == call.func_type_) {
      sql.append("AI_EMBED(");
      sql.append(model_literal);
      sql.append(", ");
      sql.append(call.prompt_expr_);
      if (!call.extra_arg_.empty()) {
        sql.append(", ");
        sql.append(call.extra_arg_);
      }
      sql.append(")");
    } else {
      sql.append("AI_COMPLETE(");
      sql.append(model_literal);
      sql.append(", ");
      sql.append(call.prompt_expr_);
      if (!call.type_prompt_.empty()) {
        // The typed result contract has to be sent as the system message. The
        // ai_complete() config argument is merged into the request JSON, so a
        // full "messages" array replaces the default single user message.
        // IMPORTANT: the config argument must be a *character* value. Passing
        // the json_object(...) datum directly fails inside ai_complete with
        // "ERROR 3140 Invalid JSON text" because the JSON datum encoding is not
        // a JSON text (read_real_string_data + get_json_object_form_str), so
        // cast it to CHAR explicitly.
        sql.append(", CAST(json_object('messages', json_array("
                   "json_object('role', 'system', 'content', ");
        append_quoted_string(sql, call.type_prompt_);
        sql.append("), json_object('role', 'user', 'content', ");
        sql.append(call.prompt_expr_);
        sql.append("))) AS CHAR)");
      }
      sql.append(")");
    }
    sql.append(" AS ai_result FROM ");
    append_qualified_table(sql, task.db_name_, task.table_name_);
    sql.append(" WHERE ");
    sql.append(task.rowkey_predicate_);
    sql.append(" LIMIT 1");
  }
  return ret;
}

// Renders the AI result into a SQL literal suitable for the destination column.
//   - vector AI columns (vector_dim > 0): ai_embed returns a JSON array text such
//     as [0,0,0,0]; the array literal form is used because this fork's parser
//     does not support CAST(... AS VECTOR(n)).
//   - integer result columns: the typed prompt asks for a base-10 integer; only
//     a strict integer is accepted, otherwise the attempt counts as a failure.
//   - everything else (json/varchar/text): a quoted SQL string literal.
int format_result_value(const AITaskRow &task,
                        const std::string &raw_result,
                        std::string &sql_value)
{
  int ret = OB_SUCCESS;
  const std::string trimmed = trim_copy(raw_result);
  if (task.vector_dim_ > 0) {
    if (trimmed.size() >= 2 && '[' == trimmed[0] && ']' == trimmed[trimmed.size() - 1]) {
      sql_value = trimmed;
    } else {
      append_quoted_string(sql_value, raw_result);
    }
  } else if (task.result_type_ >= 1 && task.result_type_ <= 10) {
    size_t begin = 0;
    if (!trimmed.empty() && ('-' == trimmed[0] || '+' == trimmed[0])) {
      begin = 1;
    }
    bool is_integer = !trimmed.empty() && begin < trimmed.size();
    for (size_t i = begin; is_integer && i < trimmed.size(); ++i) {
      if (!isdigit(static_cast<unsigned char>(trimmed[i]))) {
        is_integer = false;
      }
    }
    if (!is_integer) {
      ret = OB_INVALID_DATA;
      LOG_WARN("[AI_COLUMN_WORKER] ai result is not an integer", K(ret),
               "column", task.column_name_.c_str(), "result", raw_result.c_str());
    } else {
      sql_value = trimmed;
    }
  } else {
    append_quoted_string(sql_value, raw_result);
  }
  return ret;
}

int get_int64_field(common::sqlclient::ObMySQLResult *result,
                    const char *column_name,
                    int64_t &value)
{
  int ret = OB_SUCCESS;
  if (OB_ISNULL(result) || OB_ISNULL(column_name)) {
    ret = OB_INVALID_ARGUMENT;
  } else if (OB_SUCCESS == (ret = result->get_int(column_name, value))) {
    // done
  } else {
    // Some expression results come back as unsigned or numeric; fall back to a
    // textual extraction before giving up.
    uint64_t unsigned_value = 0;
    common::ObString text;
    if (OB_SUCCESS == result->get_uint(column_name, unsigned_value)) {
      value = static_cast<int64_t>(unsigned_value);
      ret = OB_SUCCESS;
    } else if (OB_SUCCESS == result->get_varchar(column_name, text)) {
      char buf[64];
      const int64_t len = text.length() < static_cast<int64_t>(sizeof(buf)) - 1
                              ? text.length()
                              : static_cast<int64_t>(sizeof(buf)) - 1;
      if (len > 0 && NULL != text.ptr()) {
        memcpy(buf, text.ptr(), static_cast<size_t>(len));
      }
      buf[len] = '\0';
      value = strtoll(buf, NULL, 10);
      ret = OB_SUCCESS;
    }
  }
  return ret;
}

int get_string_field(common::sqlclient::ObMySQLResult *result,
                     const char *column_name,
                     std::string &value)
{
  int ret = OB_SUCCESS;
  common::ObString text;
  if (OB_ISNULL(result) || OB_ISNULL(column_name)) {
    ret = OB_INVALID_ARGUMENT;
  } else if (OB_SUCCESS == (ret = result->get_varchar(column_name, text))) {
    if (NULL != text.ptr() && text.length() > 0) {
      value.assign(text.ptr(), static_cast<size_t>(text.length()));
    } else {
      value.clear();
    }
  } else if (OB_ERR_NULL_VALUE == ret) {
    value.clear();
    ret = OB_SUCCESS;
  }
  return ret;
}

class AIColumnInternalWriteGuard
{
public:
  AIColumnInternalWriteGuard()
    : prev_(::oceanbase::sql::ai_column_dml_util::g_ai_column_internal_write)
  {
    set_ai_column_internal_write(true);
  }
  ~AIColumnInternalWriteGuard() { set_ai_column_internal_write(prev_); }
private:
  bool prev_;
};

class ObAIColumnWorker
{
public:
  static ObAIColumnWorker &get_instance();
  int start(common::ObMySQLProxy *sql_proxy);
  void stop();
  bool is_running() const { return started_.load(std::memory_order_acquire); }

private:
  ObAIColumnWorker();
  ~ObAIColumnWorker();
  void run();
  int poll_once(bool &did_work);
  int query_tasks(std::vector<AITaskRow> &rows);
  int read_task_rows(const std::string &sql, std::vector<AITaskRow> &rows);
  int process_group(const std::vector<AITaskRow> &group);
  int call_ai(const AITaskRow &task, const AIColumnCall &call, std::string &result);
  int check_tasks_still_valid(const std::vector<AITaskRow> &group, bool &valid);
  int write_back(const std::vector<AITaskRow> &group,
                 const std::vector<AIWriteValue> &values);
  int delete_tasks(const std::vector<AITaskRow> &group);
  int mark_retry(const std::vector<AITaskRow> &group, const int err_code);
  int mark_terminal_failed(const std::vector<AITaskRow> &group);
  void log_throttled(const int err_code, const char *action);

private:
  ObAIColumnWorker(const ObAIColumnWorker &) = delete;
  ObAIColumnWorker &operator=(const ObAIColumnWorker &) = delete;

  common::ObMySQLProxy *sql_proxy_;
  std::thread thread_;
  std::atomic<bool> started_;
  std::atomic<bool> stop_;
  int64_t last_err_ts_;
  int last_err_code_;
  int64_t processed_group_cnt_;
};

ObAIColumnWorker::ObAIColumnWorker()
  : sql_proxy_(NULL),
    started_(false),
    stop_(true),
    last_err_ts_(0),
    last_err_code_(0),
    processed_group_cnt_(0)
{
}

ObAIColumnWorker::~ObAIColumnWorker()
{
  stop();
}

ObAIColumnWorker &ObAIColumnWorker::get_instance()
{
  static ObAIColumnWorker instance;
  return instance;
}

void ObAIColumnWorker::log_throttled(const int err_code, const char *action)
{
  const int64_t now = common::ObTimeUtility::current_time();
  if (err_code != last_err_code_ || now - last_err_ts_ > 10 * 1000 * 1000) {
    last_err_code_ = err_code;
    last_err_ts_ = now;
    LOG_WARN_RET(err_code, "[AI_COLUMN_WORKER] operation failed",
                 "action", NULL == action ? "" : action);
  }
}

int ObAIColumnWorker::start(common::ObMySQLProxy *sql_proxy)
{
  int ret = OB_SUCCESS;
  if (OB_ISNULL(sql_proxy)) {
    ret = OB_INVALID_ARGUMENT;
    LOG_WARN("[AI_COLUMN_WORKER] null sql proxy", K(ret));
  } else if (started_.load(std::memory_order_acquire) || thread_.joinable()) {
    ret = OB_INIT_TWICE;
    LOG_WARN("[AI_COLUMN_WORKER] worker already started", K(ret));
  } else {
    sql_proxy_ = sql_proxy;
    stop_.store(false, std::memory_order_release);
    last_err_ts_ = 0;
    last_err_code_ = 0;
    processed_group_cnt_ = 0;
    started_.store(true, std::memory_order_release);
    thread_ = std::thread(&ObAIColumnWorker::run, this);
    LOG_INFO("[AI_COLUMN_WORKER] async worker started");
  }
  return ret;
}

void ObAIColumnWorker::stop()
{
  if (!started_.load(std::memory_order_acquire) && !thread_.joinable()) {
    // nothing to do
  } else {
    stop_.store(true, std::memory_order_release);
    if (thread_.joinable() && std::this_thread::get_id() != thread_.get_id()) {
      thread_.join();
    }
    started_.store(false, std::memory_order_release);
    sql_proxy_ = NULL;
    LOG_INFO("[AI_COLUMN_WORKER] async worker stopped", K(processed_group_cnt_));
  }
}

void ObAIColumnWorker::run()
{
  // Inner SQL runs on this thread; give it the same thread-local worker context
  // that every other observer background thread has (timeout/retry defaults).
  lib::Worker worker;
  lib::Worker::set_worker_to_thread_local(&worker);
  LOG_INFO("[AI_COLUMN_WORKER] worker thread enter");
  if (stop_.load(std::memory_order_acquire)) {
    // stopped before we started
  } else {
    std::this_thread::sleep_for(std::chrono::milliseconds(AI_COLUMN_WORKER_STARTUP_DELAY_MS));
  }
  while (!stop_.load(std::memory_order_acquire)) {
    bool did_work = false;
    const int ret = poll_once(did_work);
    if (OB_SUCCESS != ret) {
      log_throttled(ret, "poll");
    }
    if (stop_.load(std::memory_order_acquire)) {
      break;
    }
    if (!did_work) {
      std::this_thread::sleep_for(
          std::chrono::milliseconds(AI_COLUMN_WORKER_POLL_INTERVAL_MS));
    }
  }
  lib::Worker::set_worker_to_thread_local(NULL);
  LOG_INFO("[AI_COLUMN_WORKER] worker thread exit");
}

int ObAIColumnWorker::read_task_rows(const std::string &sql,
                                     std::vector<AITaskRow> &rows)
{
  int ret = OB_SUCCESS;
  common::ObMySQLProxy::MySQLResult res;
  common::sqlclient::ObMySQLResult *result = NULL;
  rows.clear();
  if (OB_ISNULL(sql_proxy_)) {
    ret = OB_NOT_INIT;
  } else if (OB_FAIL(sql_proxy_->read(res, sql.c_str()))) {
    LOG_DEBUG("[AI_COLUMN_WORKER] read task rows failed", "errno", ret);
  } else if (OB_ISNULL(result = res.get_result())) {
    ret = OB_ERR_UNEXPECTED;
  } else {
    while (OB_SUCC(ret) && OB_SUCC(result->next())) {
      AITaskRow row;
      if (OB_FAIL(get_int64_field(result, "task_id", row.task_id_))
          || OB_FAIL(get_int64_field(result, "table_id", row.table_id_))
          || OB_FAIL(get_int64_field(result, "column_id", row.column_id_))
          || OB_FAIL(get_int64_field(result, "state", row.state_))
          || OB_FAIL(get_int64_field(result, "retry_count", row.retry_count_))
          || OB_FAIL(get_int64_field(result, "eligible_ts", row.eligible_ts_))
          || OB_FAIL(get_int64_field(result, "result_type", row.result_type_))
          || OB_FAIL(get_int64_field(result, "vector_dim", row.vector_dim_))
          || OB_FAIL(get_int64_field(result, "max_retries", row.max_retries_))
          || OB_FAIL(get_string_field(result, "request_id", row.request_id_))
          || OB_FAIL(get_string_field(result, "rowkey_predicate", row.rowkey_predicate_))
          || OB_FAIL(get_string_field(result, "column_name", row.column_name_))
          || OB_FAIL(get_string_field(result, "normalized_expr", row.normalized_expr_))
          || OB_FAIL(get_string_field(result, "model_name", row.model_name_))
          || OB_FAIL(get_string_field(result, "func_type", row.func_type_))
          || OB_FAIL(get_string_field(result, "table_name", row.table_name_))
          || OB_FAIL(get_string_field(result, "database_name", row.db_name_))) {
        LOG_WARN("[AI_COLUMN_WORKER] extract task row failed", K(ret));
      } else {
        rows.push_back(row);
      }
    }
    if (OB_ITER_END == ret) {
      ret = OB_SUCCESS;
    }
    int close_ret = result->close();
    if (OB_SUCCESS == ret && OB_SUCCESS != close_ret) {
      ret = close_ret;
    }
  }
  return ret;
}

int ObAIColumnWorker::query_tasks(std::vector<AITaskRow> &rows)
{
  int ret = OB_SUCCESS;
  std::string sql;
  sql.assign(
      "SELECT task.task_id AS task_id, task.table_id AS table_id,"
      " task.column_id AS column_id, IFNULL(task.request_id, '') AS request_id,"
      " task.state AS state, task.retry_count AS retry_count,"
      " IFNULL(task.rowkey_predicate, '') AS rowkey_predicate,"
      " task.eligible_ts AS eligible_ts,"
      " IFNULL(a.column_name, '') AS column_name,"
      " IFNULL(a.normalized_expr, '') AS normalized_expr,"
      " IFNULL(a.model_name, '') AS model_name,"
      " IFNULL(a.func_type, '') AS func_type,"
      " IFNULL(a.max_retries, 0) AS max_retries,"
      " IFNULL(a.result_type, 0) AS result_type,"
      " IFNULL(a.vector_dim, 0) AS vector_dim,"
      " IFNULL(t.table_name, '') AS table_name,"
      " IFNULL(d.database_name, '') AS database_name"
      " FROM oceanbase.__all_ai_column_task task"
      " JOIN oceanbase.__all_ai_column a ON a.table_id = task.table_id"
      "  AND a.column_id = task.column_id"
      " JOIN oceanbase.__all_table t ON t.table_id = task.table_id"
      " JOIN oceanbase.__all_database d ON d.database_id = t.database_id"
      " WHERE task.state IN (1, 3) AND task.eligible_ts <= ");
  // Compare against a C++ computed epoch microsecond literal so the backoff
  // semantics do not depend on SQL implicit casts between int and datetime.
  append_int64(sql, common::ObTimeUtility::current_time());
  sql.append(" ORDER BY task.task_id LIMIT 64");
  if (OB_FAIL(read_task_rows(sql, rows))) {
  }
  return ret;
}

int ObAIColumnWorker::call_ai(const AITaskRow &task,
                              const AIColumnCall &call,
                              std::string &result)
{
  int ret = OB_SUCCESS;
  std::string sql;
  common::ObMySQLProxy::MySQLResult res;
  common::sqlclient::ObMySQLResult *mysql_result = NULL;
  common::ObString value;
  if (OB_FAIL(build_ai_sql(task, call, sql))) {
  } else if (OB_FAIL(sql_proxy_->read(res, sql.c_str()))) {
    LOG_WARN("[AI_COLUMN_WORKER] ai sql failed", K(ret),
             "table", task.table_name_.c_str(), "column", task.column_name_.c_str());
  } else if (OB_ISNULL(mysql_result = res.get_result())) {
    ret = OB_ERR_UNEXPECTED;
  } else if (OB_FAIL(mysql_result->next())) {
    if (OB_ITER_END == ret) {
      LOG_INFO("[AI_COLUMN_WORKER] row no longer exists",
               "table", task.table_name_.c_str(), "predicate", task.rowkey_predicate_.c_str());
    } else {
      LOG_WARN("[AI_COLUMN_WORKER] ai result iteration failed", K(ret));
    }
  } else if (OB_FAIL(mysql_result->get_varchar("ai_result", value))) {
    LOG_WARN("[AI_COLUMN_WORKER] read ai result failed", K(ret));
  } else if (NULL == value.ptr()) {
    ret = OB_ERR_UNEXPECTED;
  } else {
    result.assign(value.ptr(), static_cast<size_t>(value.length()));
  }
  if (NULL != mysql_result) {
    int close_ret = mysql_result->close();
    if (OB_SUCCESS == ret && OB_SUCCESS != close_ret) {
      ret = close_ret;
    }
  }
  return ret;
}

int ObAIColumnWorker::check_tasks_still_valid(const std::vector<AITaskRow> &group,
                                              bool &valid)
{
  int ret = OB_SUCCESS;
  valid = false;
  common::ObMySQLProxy::MySQLResult res;
  common::sqlclient::ObMySQLResult *result = NULL;
  std::string sql;
  int64_t row_count = 0;
  if (group.empty() || OB_ISNULL(sql_proxy_)) {
    ret = OB_INVALID_ARGUMENT;
  } else {
    sql.assign("SELECT task_id AS task_id FROM oceanbase.__all_ai_column_task"
               " WHERE request_id = ");
    append_quoted_string(sql, group[0].request_id_);
    sql.append(" AND task_id IN (");
    append_task_id_list(sql, group);
    sql.append(")");
    if (OB_FAIL(sql_proxy_->read(res, sql.c_str()))) {
      LOG_WARN("[AI_COLUMN_WORKER] stale guard query failed", K(ret));
    } else if (OB_ISNULL(result = res.get_result())) {
      ret = OB_ERR_UNEXPECTED;
    } else {
      while (OB_SUCC(ret) && OB_SUCC(result->next())) {
        ++row_count;
      }
      if (OB_ITER_END == ret) {
        ret = OB_SUCCESS;
        valid = (row_count == static_cast<int64_t>(group.size()));
      }
      int close_ret = result->close();
      if (OB_SUCCESS == ret && OB_SUCCESS != close_ret) {
        ret = close_ret;
      }
    }
  }
  return ret;
}

int ObAIColumnWorker::write_back(const std::vector<AITaskRow> &group,
                                 const std::vector<AIWriteValue> &values)
{
  int ret = OB_SUCCESS;
  int64_t affected_rows = 0;
  std::string sql;
  if (group.empty() || values.empty() || OB_ISNULL(sql_proxy_)) {
    ret = OB_INVALID_ARGUMENT;
  } else {
    sql.assign("UPDATE ");
    append_qualified_table(sql, group[0].db_name_, group[0].table_name_);
    sql.append(" SET ");
    for (size_t i = 0; i < values.size(); ++i) {
      if (i > 0) {
        sql.append(", ");
      }
      append_backtick_ident(sql, values[i].column_name_);
      sql.append(" = ");
      sql.append(values[i].sql_value_);
    }
    sql.append(" WHERE ");
    sql.append(group[0].rowkey_predicate_);
    {
      // The write-back update must not be seen by the AI column DML hook,
      // otherwise it would invalidate the results it is writing.
      AIColumnInternalWriteGuard guard;
      ret = sql_proxy_->write(sql.c_str(), affected_rows);
    }
    if (OB_FAIL(ret)) {
      LOG_WARN("[AI_COLUMN_WORKER] write back failed", K(ret),
               "table", group[0].table_name_.c_str());
    } else if (0 == affected_rows) {
      LOG_INFO("[AI_COLUMN_WORKER] write back affected no row",
               "table", group[0].table_name_.c_str(),
               "predicate", group[0].rowkey_predicate_.c_str());
      ret = OB_ITER_END; // signal: row is gone, caller drops the tasks
    }
  }
  return ret;
}

int ObAIColumnWorker::delete_tasks(const std::vector<AITaskRow> &group)
{
  int ret = OB_SUCCESS;
  int64_t affected_rows = 0;
  std::string sql;
  if (group.empty() || OB_ISNULL(sql_proxy_)) {
    ret = OB_INVALID_ARGUMENT;
  } else {
    sql.assign("DELETE FROM oceanbase.__all_ai_column_task WHERE task_id IN (");
    append_task_id_list(sql, group);
    sql.append(")");
    if (OB_FAIL(sql_proxy_->write(sql.c_str(), affected_rows))) {
      LOG_WARN("[AI_COLUMN_WORKER] delete task rows failed", K(ret),
               K(affected_rows));
    }
  }
  return ret;
}

int ObAIColumnWorker::mark_retry(const std::vector<AITaskRow> &group,
                                 const int err_code)
{
  int ret = OB_SUCCESS;
  if (group.empty() || OB_ISNULL(sql_proxy_)) {
    ret = OB_INVALID_ARGUMENT;
  } else {
    std::string err_text("errno=");
    append_int64(err_text, static_cast<int64_t>(err_code));
    std::string sql;
    int64_t affected_rows = 0;
    sql.assign("UPDATE oceanbase.__all_ai_column_task SET state = 3,"
               " retry_count = retry_count + 1, eligible_ts = ");
    append_int64(sql, common::ObTimeUtility::current_time() + AI_COLUMN_WORKER_RETRY_BACKOFF_US);
    sql.append(", last_error = ");
    append_quoted_string(sql, err_text);
    sql.append(" WHERE task_id IN (");
    append_task_id_list(sql, group);
    sql.append(")");
    if (OB_FAIL(sql_proxy_->write(sql.c_str(), affected_rows))) {
      LOG_WARN("[AI_COLUMN_WORKER] mark retry failed", K(ret));
    } else {
      LOG_INFO("[AI_COLUMN_WORKER] task retry scheduled", "errno", err_code,
               "max_retries", group[0].max_retries_, "retry_count", group[0].retry_count_);
    }
  }
  return ret;
}

int ObAIColumnWorker::mark_terminal_failed(const std::vector<AITaskRow> &group)
{
  int ret = OB_SUCCESS;
  LOG_INFO("[AI_COLUMN_WORKER] task reached max retries, drop task rows",
           "max_retries", group.empty() ? 0 : group[0].max_retries_,
           "retry_count", group.empty() ? 0 : group[0].retry_count_);
  if (OB_FAIL(delete_tasks(group))) {
  } else if (!group.empty()) {
    LOG_INFO("[AI_COLUMN_WORKER] terminal failure row keeps NULL result",
             "table", group[0].table_name_.c_str(),
             "predicate", group[0].rowkey_predicate_.c_str());
  }
  return ret;
}

int ObAIColumnWorker::process_group(const std::vector<AITaskRow> &group)
{
  int ret = OB_SUCCESS;
  int ai_err = OB_SUCCESS;
  bool stale = false;
  bool group_done = false;
  std::vector<AIWriteValue> values;
  for (size_t i = 0; OB_SUCC(ret) && !stale && !group_done && i < group.size(); ++i) {
    const AITaskRow &task = group[i];
    AIColumnCall call;
    std::string ai_result;
    std::string sql_value;
    int call_ret = OB_SUCCESS;
    if (OB_FAIL(parse_ai_column_desc(task.normalized_expr_, task.func_type_, call))) {
      ai_err = ret;
      ret = OB_SUCCESS;
      group_done = true;
    } else if (OB_SUCCESS != (call_ret = call_ai(task, call, ai_result))) {
      if (OB_ITER_END == call_ret) {
        stale = true;
      } else {
        ai_err = call_ret;
        group_done = true;
      }
    } else if (OB_FAIL(format_result_value(task, ai_result, sql_value))) {
      ai_err = ret;
      ret = OB_SUCCESS;
      group_done = true;
    } else {
      AIWriteValue value;
      value.column_name_ = task.column_name_;
      value.sql_value_ = sql_value;
      bool duplicated = false;
      for (size_t k = 0; !duplicated && k < values.size(); ++k) {
        duplicated = (values[k].column_name_ == value.column_name_);
      }
      if (!duplicated) {
        values.push_back(value);
      }
      // The stale guard is checked after every AI call so that a request that
      // has been superseded by a newer DML does not spend more HTTP calls.
      bool valid = true;
      if (OB_FAIL(check_tasks_still_valid(group, valid))) {
        stale = false;
        group_done = true;
        ai_err = ret;
        ret = OB_SUCCESS;
      } else if (!valid) {
        stale = true;
      }
    }
  }
  if (OB_FAIL(ret)) {
    // unexpected internal error
  } else if (stale) {
    LOG_INFO("[AI_COLUMN_WORKER] request superseded, discard current results",
             "table", group[0].table_name_.c_str(),
             "predicate", group[0].rowkey_predicate_.c_str());
    int tmp = delete_tasks(group);
    if (OB_SUCCESS != tmp) {
      LOG_WARN("[AI_COLUMN_WORKER] drop stale task rows failed", K(tmp));
    }
  } else if (OB_SUCCESS != ai_err) {
    bool valid = true;
    if (OB_FAIL(check_tasks_still_valid(group, valid))) {
      ret = OB_SUCCESS;
      log_throttled(ai_err, "stale guard (retry path)");
    } else if (!valid) {
      int tmp = delete_tasks(group);
      if (OB_SUCCESS != tmp) {
        LOG_WARN("[AI_COLUMN_WORKER] drop superseded task rows failed", K(tmp));
      }
    } else if (group[0].retry_count_ < group[0].max_retries_) {
      if (OB_FAIL(mark_retry(group, ai_err))) {
      }
    } else if (OB_FAIL(mark_terminal_failed(group))) {
    }
  } else {
    bool valid = true;
    int write_ret = OB_SUCCESS;
    if (OB_FAIL(check_tasks_still_valid(group, valid))) {
      ret = OB_SUCCESS;
      log_throttled(OB_ERR_UNEXPECTED, "stale guard (write path)");
    } else if (!valid) {
      int tmp = delete_tasks(group);
      if (OB_SUCCESS != tmp) {
        LOG_WARN("[AI_COLUMN_WORKER] drop superseded task rows failed", K(tmp));
      }
    } else if (OB_SUCCESS != (write_ret = write_back(group, values))) {
      // The result could not be persisted: count it as a failed attempt.
      if (OB_ITER_END == write_ret) {
        int tmp = delete_tasks(group);
        if (OB_SUCCESS != tmp) {
          LOG_WARN("[AI_COLUMN_WORKER] drop task rows of vanished row failed", K(tmp));
        }
      } else if (group[0].retry_count_ < group[0].max_retries_) {
        if (OB_FAIL(mark_retry(group, write_ret))) {
        }
      } else if (OB_FAIL(mark_terminal_failed(group))) {
      }
    } else if (OB_FAIL(delete_tasks(group))) {
    } else {
      ++processed_group_cnt_;
      LOG_INFO("[AI_COLUMN_WORKER] ai column result written back",
               "table", group[0].table_name_.c_str(),
               "predicate", group[0].rowkey_predicate_.c_str(),
               "column_cnt", static_cast<int64_t>(values.size()),
               "total_groups", processed_group_cnt_);
    }
  }
  return ret;
}

int ObAIColumnWorker::poll_once(bool &did_work)
{
  int ret = OB_SUCCESS;
  did_work = false;
  std::vector<AITaskRow> rows;
  if (OB_FAIL(query_tasks(rows))) {
  } else if (rows.empty()) {
    // idle
  } else {
    // The poll query already filtered on eligible_ts, so the first row is
    // runnable. Group the tasks that belong to the same DML request (same
    // request_id / row / predicate) so that all AI columns of the row are
    // written back in one UPDATE statement (grouped visibility).
    const AITaskRow &head = rows[0];
    std::vector<AITaskRow> group;
    for (size_t i = 0; i < rows.size(); ++i) {
      if (rows[i].request_id_ == head.request_id_
          && rows[i].table_id_ == head.table_id_
          && rows[i].rowkey_predicate_ == head.rowkey_predicate_) {
        group.push_back(rows[i]);
      }
    }
    if (!group.empty()) {
      ret = process_group(group);
      did_work = true;
    }
  }
  return ret;
}

} // namespace

int start_ai_column_worker(common::ObMySQLProxy *sql_proxy)
{
  return ObAIColumnWorker::get_instance().start(sql_proxy);
}

void stop_ai_column_worker()
{
  ObAIColumnWorker::get_instance().stop();
}

bool is_ai_column_worker_running()
{
  return ObAIColumnWorker::get_instance().is_running();
}

} // namespace observer
} // namespace oceanbase
