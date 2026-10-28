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

#define USING_LOG_PREFIX SQL

#include "sql/ob_file_sql_rewriter.h"

#include <algorithm>
#include <cerrno>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <limits>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>
#include <glob.h>
#include <sys/stat.h>
#include <unistd.h>

#include "lib/oblog/ob_log.h"
#include "lib/utility/ob_print_utils.h"
#include "share/ob_errno.h"
#include "sql/resolver/ob_resolver_utils.h"
#include "sql/session/ob_sql_session_info.h"

namespace oceanbase
{
namespace sql
{
namespace
{

const int64_t FILE_SQL_MAX_FILE_SIZE = 128LL * 1024 * 1024;
const int64_t FILE_SQL_MAX_ROWS = 2000000;

enum FileFieldType
{
  FT_NULL = 0,
  FT_BIGINT,
  FT_DOUBLE,
  FT_BOOLEAN,
  FT_VARCHAR,
  FT_DATE,
  FT_DATETIME
};

struct FileCell
{
  bool is_null_;
  std::string text_;
  FileFieldType json_type_;
  FileCell() : is_null_(true), text_(), json_type_(FT_NULL) {}
};

struct FileColumn
{
  std::string name_;
  FileFieldType type_;
  bool nullable_;
  FileColumn() : name_(), type_(FT_NULL), nullable_(true) {}
};

struct FileTable
{
  std::vector<FileColumn> columns_;
  std::vector<std::vector<FileCell> > rows_;
  FileTable() : columns_(), rows_() {}
};

struct FileCsvOptions
{
  bool header_;
  char delimiter_;
  char quote_;
  char escape_;
  std::string nullstr_;
  bool has_nullstr_;
  FileCsvOptions()
    : header_(true), delimiter_(','), quote_('"'), escape_('"'), nullstr_(), has_nullstr_(false) {}
};

static std::string to_lower(const std::string &s)
{
  std::string r(s);
  for (size_t i = 0; i < r.size(); ++i) {
    if (r[i] >= 'A' && r[i] <= 'Z') {
      r[i] = static_cast<char>(r[i] - 'A' + 'a');
    }
  }
  return r;
}

static std::string trim_str(const std::string &s)
{
  size_t b = 0;
  size_t e = s.size();
  while (b < e && (s[b] == ' ' || s[b] == '\t' || s[b] == '\r' || s[b] == '\n')) {
    ++b;
  }
  while (e > b && (s[e - 1] == ' ' || s[e - 1] == '\t' || s[e - 1] == '\r' || s[e - 1] == '\n')) {
    --e;
  }
  return s.substr(b, e - b);
}

static bool starts_with_ci(const std::string &s, size_t pos, const char *word)
{
  size_t len = strlen(word);
  if (pos + len > s.size()) {
    return false;
  }
  for (size_t i = 0; i < len; ++i) {
    char a = s[pos + i];
    if (a >= 'A' && a <= 'Z') {
      a = static_cast<char>(a - 'A' + 'a');
    }
    char b = word[i];
    if (b >= 'A' && b <= 'Z') {
      b = static_cast<char>(b - 'A' + 'a');
    }
    if (a != b) {
      return false;
    }
  }
  return true;
}

static bool is_ident_start(char c)
{
  return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_';
}

static bool is_ident_char(char c)
{
  return is_ident_start(c) || (c >= '0' && c <= '9') || c == '$';
}

static std::string sql_quote(const std::string &s)
{
  std::string out;
  out.reserve(s.size() + 2);
  out.push_back('\'');
  for (size_t i = 0; i < s.size(); ++i) {
    char c = s[i];
    if (c == '\'') {
      out += "''";
    } else if (c == '\\') {
      out += "\\\\";
    } else {
      out.push_back(c);
    }
  }
  out.push_back('\'');
  return out;
}

static std::string bt_quote(const std::string &s)
{
  std::string out;
  out.reserve(s.size() + 2);
  out.push_back('`');
  for (size_t i = 0; i < s.size(); ++i) {
    if (s[i] == '`') {
      out += "``";
    } else {
      out.push_back(s[i]);
    }
  }
  out.push_back('`');
  return out;
}

static std::string json_escape(const std::string &s)
{
  std::string out;
  out.reserve(s.size() + 8);
  static const char *hex = "0123456789abcdef";
  for (size_t i = 0; i < s.size(); ++i) {
    unsigned char c = static_cast<unsigned char>(s[i]);
    switch (c) {
      case '"': out += "\\\""; break;
      case '\\': out += "\\\\"; break;
      case '\b': out += "\\b"; break;
      case '\f': out += "\\f"; break;
      case '\n': out += "\\n"; break;
      case '\r': out += "\\r"; break;
      case '\t': out += "\\t"; break;
      default:
        if (c < 0x20) {
          out += "\\u00";
          out.push_back(hex[(c >> 4) & 0x0f]);
          out.push_back(hex[c & 0x0f]);
        } else {
          out.push_back(static_cast<char>(c));
        }
    }
  }
  return out;
}

static std::string to_hex(const std::string &s)
{
  static const char *hex = "0123456789abcdef";
  std::string out;
  out.reserve(s.size() * 2);
  for (size_t i = 0; i < s.size(); ++i) {
    unsigned char c = static_cast<unsigned char>(s[i]);
    out.push_back(hex[(c >> 4) & 0x0f]);
    out.push_back(hex[c & 0x0f]);
  }
  return out;
}

static bool parse_int64(const std::string &s, int64_t &v)
{
  if (s.empty()) {
    return false;
  }
  size_t i = 0;
  if (s[0] == '-' || s[0] == '+') {
    i = 1;
  }
  if (i >= s.size()) {
    return false;
  }
  for (size_t j = i; j < s.size(); ++j) {
    if (s[j] < '0' || s[j] > '9') {
      return false;
    }
  }
  errno = 0;
  char *end = NULL;
  long long tmp = strtoll(s.c_str(), &end, 10);
  if (errno == ERANGE || end == NULL || *end != '\0') {
    return false;
  }
  v = static_cast<int64_t>(tmp);
  return true;
}

static bool parse_double(const std::string &s, double &v)
{
  if (s.empty()) {
    return false;
  }
  bool has_digit = false;
  for (size_t i = 0; i < s.size(); ++i) {
    if (s[i] >= '0' && s[i] <= '9') {
      has_digit = true;
    }
  }
  if (!has_digit) {
    return false;
  }
  errno = 0;
  char *end = NULL;
  double tmp = strtod(s.c_str(), &end);
  if (errno == ERANGE || end == NULL || *end != '\0' || !std::isfinite(tmp)) {
    return false;
  }
  v = tmp;
  return true;
}

static bool is_digit_at(const std::string &s, size_t p)
{
  return p < s.size() && s[p] >= '0' && s[p] <= '9';
}

static bool parse_date_str(const std::string &s)
{
  if (s.size() != 10 || s[4] != '-' || s[7] != '-') {
    return false;
  }
  for (size_t i = 0; i < s.size(); ++i) {
    if (i == 4 || i == 7) {
      continue;
    }
    if (!is_digit_at(s, i)) {
      return false;
    }
  }
  int y = atoi(s.substr(0, 4).c_str());
  int m = atoi(s.substr(5, 2).c_str());
  int d = atoi(s.substr(8, 2).c_str());
  if (y < 1 || m < 1 || m > 12 || d < 1) {
    return false;
  }
  static const int mdays[] = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
  int max_day = mdays[m - 1];
  if (m == 2 && ((y % 4 == 0 && y % 100 != 0) || y % 400 == 0)) {
    max_day = 29;
  }
  return d <= max_day;
}

static bool parse_datetime_str(const std::string &s)
{
  if (s.size() < 19) {
    return false;
  }
  if (!parse_date_str(s.substr(0, 10))) {
    return false;
  }
  if (s[10] != ' ' && s[10] != 'T') {
    return false;
  }
  if (s[13] != ':' || s[16] != ':') {
    return false;
  }
  if (!is_digit_at(s, 11) || !is_digit_at(s, 12) ||
      !is_digit_at(s, 14) || !is_digit_at(s, 15) ||
      !is_digit_at(s, 17) || !is_digit_at(s, 18)) {
    return false;
  }
  int hh = atoi(s.substr(11, 2).c_str());
  int mm = atoi(s.substr(14, 2).c_str());
  int ss = atoi(s.substr(17, 2).c_str());
  if (hh > 23 || mm > 59 || ss > 59) {
    return false;
  }
  size_t p = 19;
  if (p < s.size() && s[p] == '.') {
    ++p;
    if (p >= s.size()) {
      return false;
    }
    while (p < s.size() && is_digit_at(s, p)) {
      ++p;
    }
  }
  return p == s.size();
}

static FileFieldType merge_type(FileFieldType a, FileFieldType b)
{
  if (a == FT_NULL) {
    return b;
  }
  if (b == FT_NULL) {
    return a;
  }
  if (a == b) {
    return a;
  }
  if ((a == FT_BIGINT && b == FT_DOUBLE) || (a == FT_DOUBLE && b == FT_BIGINT)) {
    return FT_DOUBLE;
  }
  if ((a == FT_DATE && b == FT_DATETIME) || (a == FT_DATETIME && b == FT_DATE)) {
    return FT_DATETIME;
  }
  return FT_VARCHAR;
}

static FileFieldType infer_text_type(const std::string &s)
{
  int64_t iv = 0;
  double dv = 0;
  if (s.empty()) {
    return FT_VARCHAR;
  }
  if (parse_int64(s, iv)) {
    return FT_BIGINT;
  }
  if (parse_double(s, dv)) {
    return FT_DOUBLE;
  }
  if (0 == strcasecmp(s.c_str(), "true") || 0 == strcasecmp(s.c_str(), "false")) {
    return FT_BOOLEAN;
  }
  if (parse_date_str(s)) {
    return FT_DATE;
  }
  if (parse_datetime_str(s)) {
    return FT_DATETIME;
  }
  return FT_VARCHAR;
}

static void infer_table_types(FileTable &table)
{
  for (size_t c = 0; c < table.columns_.size(); ++c) {
    FileFieldType type = FT_NULL;
    bool nullable = false;
    for (size_t r = 0; r < table.rows_.size(); ++r) {
      const FileCell &cell = table.rows_[r][c];
      if (cell.is_null_) {
        nullable = true;
      } else {
        type = merge_type(type, infer_text_type(cell.text_));
      }
    }
    table.columns_[c].type_ = type;
    table.columns_[c].nullable_ = nullable || 0 == table.rows_.size();
  }
}

static int read_file_bytes(const std::string &path, std::string &data)
{
  int ret = OB_SUCCESS;
  struct stat st;
  if (0 != stat(path.c_str(), &st) || !S_ISREG(st.st_mode)) {
    ret = OB_FILE_NOT_EXIST;
  } else if (st.st_size > FILE_SQL_MAX_FILE_SIZE) {
    ret = OB_SIZE_OVERFLOW;
  } else {
    std::ifstream in(path.c_str(), std::ios::binary);
    if (!in) {
      ret = OB_FILE_NOT_EXIST;
    } else {
      data.assign(std::istreambuf_iterator<char>(in), std::istreambuf_iterator<char>());
      if (in.bad()) {
        ret = OB_IO_ERROR;
      }
    }
  }
  return ret;
}

static int split_csv_records(const std::string &data,
                             const FileCsvOptions &opt,
                             std::vector<std::vector<FileCell> > &rows,
                             int64_t &bad_line)
{
  int ret = OB_SUCCESS;
  rows.clear();
  size_t p = 0;
  if (data.size() >= 3 &&
      static_cast<unsigned char>(data[0]) == 0xef &&
      static_cast<unsigned char>(data[1]) == 0xbb &&
      static_cast<unsigned char>(data[2]) == 0xbf) {
    p = 3;
  }
  int64_t line = 1;
  while (p < data.size() && OB_SUCC(ret)) {
    if (rows.size() >= FILE_SQL_MAX_ROWS) {
      ret = OB_SIZE_OVERFLOW;
      break;
    }
    std::vector<FileCell> row;
    bool row_done = false;
    while (!row_done && OB_SUCC(ret)) {
      FileCell cell;
      cell.is_null_ = false;
      cell.json_type_ = FT_VARCHAR;
      bool quoted = false;
      bool field_done = false;
      if (p < data.size() && data[p] == opt.quote_) {
        quoted = true;
        ++p;
      }
      std::string value;
      while (!field_done && OB_SUCC(ret)) {
        if (p >= data.size()) {
          if (quoted) {
            bad_line = line;
            ret = OB_INVALID_DATA;
          } else {
            field_done = true;
            row_done = true;
          }
        } else {
          char c = data[p];
          if (quoted) {
            if (c == opt.quote_) {
              if (p + 1 < data.size() && data[p + 1] == opt.quote_) {
                value.push_back(opt.quote_);
                p += 2;
              } else {
                ++p;
                quoted = false;
              }
            } else if (c == opt.escape_ && opt.escape_ != opt.quote_ && p + 1 < data.size()) {
              value.push_back(data[p + 1]);
              p += 2;
            } else {
              if (c == '\n') {
                ++line;
              }
              value.push_back(c);
              ++p;
            }
          } else {
            if (c == opt.delimiter_) {
              ++p;
              field_done = true;
            } else if (c == '\r') {
              ++p;
              if (p < data.size() && data[p] == '\n') {
                ++p;
              }
              ++line;
              field_done = true;
              row_done = true;
            } else if (c == '\n') {
              ++p;
              ++line;
              field_done = true;
              row_done = true;
            } else {
              value.push_back(c);
              ++p;
            }
          }
        }
      }
      if (OB_SUCC(ret)) {
        cell.text_ = value;
        if (!quoted && value.empty()) {
          cell.is_null_ = true;
          cell.text_.clear();
        } else if (!quoted && opt.has_nullstr_ && !opt.nullstr_.empty() && value == opt.nullstr_) {
          cell.is_null_ = true;
          cell.text_.clear();
        }
        row.push_back(cell);
      }
    }
    if (OB_SUCC(ret)) {
      if (!row.empty() && row.size() == 1 && row[0].is_null_ && p >= data.size()) {
        // ignore trailing empty record
      } else {
        rows.push_back(row);
      }
    }
  }
  return ret;
}

static std::string make_column_name(const std::string &base, int64_t idx)
{
  std::string name = trim_str(base);
  if (name.empty()) {
    std::ostringstream oss;
    oss << "column" << idx;
    name = oss.str();
  }
  return name;
}

static void dedup_column_names(std::vector<FileColumn> &cols)
{
  std::map<std::string, int64_t> seen;
  for (size_t i = 0; i < cols.size(); ++i) {
    std::string base = cols[i].name_;
    int64_t n = ++seen[base];
    if (n > 1) {
      std::ostringstream oss;
      oss << base << "__" << n;
      cols[i].name_ = oss.str();
    }
  }
}

static int load_csv(const std::string &path, const FileCsvOptions &opt, FileTable &table)
{
  int ret = OB_SUCCESS;
  std::string data;
  std::vector<std::vector<FileCell> > rows;
  int64_t bad_line = 0;
  if (OB_FAIL(read_file_bytes(path, data))) {
  } else if (OB_FAIL(split_csv_records(data, opt, rows, bad_line))) {
    LOG_WARN("failed to parse csv", K(ret), K(path.c_str()), K(bad_line));
  } else if (rows.empty()) {
    ret = OB_INVALID_DATA;
  } else {
    size_t first = 0;
    std::vector<std::string> names;
    if (opt.header_) {
      for (size_t i = 0; i < rows[0].size(); ++i) {
        names.push_back(make_column_name(rows[0][i].is_null_ ? std::string() : rows[0][i].text_, i));
      }
      first = 1;
    } else {
      for (size_t i = 0; i < rows[0].size(); ++i) {
        std::ostringstream oss;
        oss << "column" << i;
        names.push_back(oss.str());
      }
    }
    for (size_t i = 0; i < names.size(); ++i) {
      FileColumn col;
      col.name_ = names[i];
      table.columns_.push_back(col);
    }
    dedup_column_names(table.columns_);
    for (size_t r = first; r < rows.size(); ++r) {
      if (rows[r].size() != table.columns_.size()) {
        bad_line = static_cast<int64_t>(r + 1);
        ret = OB_INVALID_DATA;
        LOG_WARN("csv row has wrong field count", K(ret), K(bad_line),
                 "expected", table.columns_.size(), "actual", rows[r].size());
        break;
      }
      table.rows_.push_back(rows[r]);
    }
    if (OB_SUCC(ret)) {
      infer_table_types(table);
    }
  }
  return ret;
}

class JsonValueParser
{
public:
  JsonValueParser(const char *p, const char *end)
    : p_(p), end_(end), nested_(false) {}
  int parse_object(std::vector<std::pair<std::string, FileCell> > &fields);
  bool nested() const { return nested_; }
private:
  void skip_ws();
  int parse_string(std::string &out);
  int parse_number(FileCell &cell);
  int parse_literal(FileCell &cell);
  int parse_value(FileCell &cell);
  const char *p_;
  const char *end_;
  bool nested_;
};

void JsonValueParser::skip_ws()
{
  while (p_ < end_ && (*p_ == ' ' || *p_ == '\t' || *p_ == '\r' || *p_ == '\n')) {
    ++p_;
  }
}

int JsonValueParser::parse_string(std::string &out)
{
  int ret = OB_SUCCESS;
  out.clear();
  if (p_ >= end_ || *p_ != '"') {
    ret = OB_INVALID_DATA;
  } else {
    ++p_;
    while (p_ < end_) {
      unsigned char c = static_cast<unsigned char>(*p_++);
      if (c == '"') {
        break;
      } else if (c == '\\') {
        if (p_ >= end_) {
          ret = OB_INVALID_DATA;
          break;
        }
        char e = *p_++;
        switch (e) {
          case '"': out.push_back('"'); break;
          case '\\': out.push_back('\\'); break;
          case '/': out.push_back('/'); break;
          case 'b': out.push_back('\b'); break;
          case 'f': out.push_back('\f'); break;
          case 'n': out.push_back('\n'); break;
          case 'r': out.push_back('\r'); break;
          case 't': out.push_back('\t'); break;
          case 'u': {
            if (end_ - p_ < 4) {
              ret = OB_INVALID_DATA;
              break;
            }
            unsigned int cp = 0;
            for (int i = 0; i < 4; ++i) {
              char h = *p_++;
              cp <<= 4;
              if (h >= '0' && h <= '9') cp |= (h - '0');
              else if (h >= 'a' && h <= 'f') cp |= (h - 'a' + 10);
              else if (h >= 'A' && h <= 'F') cp |= (h - 'A' + 10);
              else { ret = OB_INVALID_DATA; break; }
            }
            if (OB_FAIL(ret)) break;
            if (cp <= 0x7f) {
              out.push_back(static_cast<char>(cp));
            } else if (cp <= 0x7ff) {
              out.push_back(static_cast<char>(0xc0 | (cp >> 6)));
              out.push_back(static_cast<char>(0x80 | (cp & 0x3f)));
            } else {
              out.push_back(static_cast<char>(0xe0 | (cp >> 12)));
              out.push_back(static_cast<char>(0x80 | ((cp >> 6) & 0x3f)));
              out.push_back(static_cast<char>(0x80 | (cp & 0x3f)));
            }
            break;
          }
          default:
            ret = OB_INVALID_DATA;
            break;
        }
      } else {
        out.push_back(static_cast<char>(c));
      }
    }
    if (p_ > end_) {
      ret = OB_INVALID_DATA;
    }
  }
  return ret;
}

int JsonValueParser::parse_number(FileCell &cell)
{
  int ret = OB_SUCCESS;
  const char *start = p_;
  if (p_ < end_ && (*p_ == '-' || *p_ == '+')) {
    ++p_;
  }
  bool has_digit = false;
  while (p_ < end_ && *p_ >= '0' && *p_ <= '9') { has_digit = true; ++p_; }
  if (p_ < end_ && *p_ == '.') {
    ++p_;
    while (p_ < end_ && *p_ >= '0' && *p_ <= '9') { has_digit = true; ++p_; }
  }
  if (p_ < end_ && (*p_ == 'e' || *p_ == 'E')) {
    ++p_;
    if (p_ < end_ && (*p_ == '-' || *p_ == '+')) ++p_;
    while (p_ < end_ && *p_ >= '0' && *p_ <= '9') ++p_;
  }
  if (!has_digit) {
    ret = OB_INVALID_DATA;
  } else {
    cell.is_null_ = false;
    cell.text_.assign(start, p_ - start);
    int64_t iv = 0;
    cell.json_type_ = parse_int64(cell.text_, iv) ? FT_BIGINT : FT_DOUBLE;
  }
  return ret;
}

int JsonValueParser::parse_literal(FileCell &cell)
{
  int ret = OB_SUCCESS;
  if (end_ - p_ >= 4 && 0 == strncmp(p_, "true", 4)) {
    cell.is_null_ = false;
    cell.json_type_ = FT_BOOLEAN;
    cell.text_ = "true";
    p_ += 4;
  } else if (end_ - p_ >= 5 && 0 == strncmp(p_, "false", 5)) {
    cell.is_null_ = false;
    cell.json_type_ = FT_BOOLEAN;
    cell.text_ = "false";
    p_ += 5;
  } else if (end_ - p_ >= 4 && 0 == strncmp(p_, "null", 4)) {
    cell.is_null_ = true;
    cell.json_type_ = FT_NULL;
    cell.text_.clear();
    p_ += 4;
  } else {
    ret = OB_INVALID_DATA;
  }
  return ret;
}

int JsonValueParser::parse_value(FileCell &cell)
{
  int ret = OB_SUCCESS;
  skip_ws();
  if (p_ >= end_) {
    ret = OB_INVALID_DATA;
  } else if (*p_ == '"') {
    cell.is_null_ = false;
    cell.json_type_ = FT_VARCHAR;
    if (OB_FAIL(parse_string(cell.text_))) {
    } else if (parse_date_str(cell.text_)) {
      cell.json_type_ = FT_DATE;
    } else if (parse_datetime_str(cell.text_)) {
      cell.json_type_ = FT_DATETIME;
    }
  } else if (*p_ == '{' || *p_ == '[') {
    nested_ = true;
    ret = OB_NOT_SUPPORTED;
  } else if (*p_ == 't' || *p_ == 'f' || *p_ == 'n') {
    ret = parse_literal(cell);
  } else {
    ret = parse_number(cell);
  }
  return ret;
}

int JsonValueParser::parse_object(std::vector<std::pair<std::string, FileCell> > &fields)
{
  int ret = OB_SUCCESS;
  skip_ws();
  if (p_ >= end_ || *p_ != '{') {
    ret = OB_INVALID_DATA;
  } else {
    ++p_;
    skip_ws();
    if (p_ < end_ && *p_ == '}') {
      ++p_;
    } else {
      while (OB_SUCC(ret)) {
        skip_ws();
        std::string key;
        if (OB_FAIL(parse_string(key))) {
        } else {
          skip_ws();
          if (p_ >= end_ || *p_ != ':') {
            ret = OB_INVALID_DATA;
          } else {
            ++p_;
            FileCell cell;
            if (OB_FAIL(parse_value(cell))) {
            } else {
              fields.push_back(std::make_pair(key, cell));
              skip_ws();
              if (p_ < end_ && *p_ == ',') {
                ++p_;
              } else if (p_ < end_ && *p_ == '}') {
                ++p_;
                break;
              } else {
                ret = OB_INVALID_DATA;
              }
            }
          }
        }
      }
    }
  }
  return ret;
}

static int load_jsonl(const std::string &path, FileTable &table)
{
  int ret = OB_SUCCESS;
  std::string data;
  if (OB_FAIL(read_file_bytes(path, data))) {
  } else {
    std::map<std::string, size_t> index;
    size_t line_start = 0;
    int64_t line_no = 0;
    while (line_start <= data.size() && OB_SUCC(ret)) {
      size_t line_end = data.find('\n', line_start);
      if (line_end == std::string::npos) {
        line_end = data.size();
      }
      std::string line = data.substr(line_start, line_end - line_start);
      if (!line.empty() && line[line.size() - 1] == '\r') {
        line.erase(line.size() - 1);
      }
      ++line_no;
      if (!trim_str(line).empty()) {
        if (table.rows_.size() >= FILE_SQL_MAX_ROWS) {
          ret = OB_SIZE_OVERFLOW;
        } else {
          JsonValueParser parser(line.data(), line.data() + line.size());
          std::vector<std::pair<std::string, FileCell> > fields;
          if (OB_FAIL(parser.parse_object(fields))) {
            LOG_WARN("invalid jsonl object", K(ret), K(line_no));
            if (OB_NOT_SUPPORTED == ret) {
              LOG_USER_ERROR(OB_NOT_SUPPORTED, "nested JSON objects or arrays in read_json");
            }
          } else if (parser.nested()) {
            ret = OB_NOT_SUPPORTED;
            LOG_USER_ERROR(OB_NOT_SUPPORTED, "nested JSON objects or arrays in read_json");
          } else {
            for (size_t i = 0; i < fields.size(); ++i) {
              if (index.find(fields[i].first) == index.end()) {
                size_t idx = table.columns_.size();
                index[fields[i].first] = idx;
                FileColumn col;
                col.name_ = fields[i].first;
                table.columns_.push_back(col);
              }
            }
            std::vector<FileCell> row(table.columns_.size());
            for (size_t i = 0; i < fields.size(); ++i) {
              row[index[fields[i].first]] = fields[i].second;
            }
            table.rows_.push_back(row);
          }
        }
      }
      if (line_end >= data.size()) {
        break;
      }
      line_start = line_end + 1;
    }
    if (OB_SUCC(ret)) {
      for (size_t r = 0; r < table.rows_.size(); ++r) {
        table.rows_[r].resize(table.columns_.size());
      }
      for (size_t c = 0; c < table.columns_.size(); ++c) {
        FileFieldType type = FT_NULL;
        bool nullable = false;
        for (size_t r = 0; r < table.rows_.size(); ++r) {
          const FileCell &cell = table.rows_[r][c];
          if (cell.is_null_) {
            nullable = true;
          } else {
            type = merge_type(type, cell.json_type_);
          }
        }
        table.columns_[c].type_ = type;
        table.columns_[c].nullable_ = nullable || 0 == table.rows_.size();
      }
    }
  }
  return ret;
}

static const char *type_name(FileFieldType t)
{
  switch (t) {
    case FT_BIGINT: return "BIGINT";
    case FT_DOUBLE: return "DOUBLE";
    case FT_BOOLEAN: return "BOOLEAN";
    case FT_DATE: return "DATE";
    case FT_DATETIME: return "DATETIME";
    case FT_VARCHAR: return "VARCHAR";
    default: return "NULL";
  }
}

static const char *sql_type_name(FileFieldType t)
{
  switch (t) {
    case FT_BIGINT: return "BIGINT";
    case FT_DOUBLE: return "DOUBLE";
    case FT_BOOLEAN: return "BOOLEAN";
    case FT_DATE: return "DATE";
    case FT_DATETIME: return "DATETIME";
    case FT_VARCHAR: return "VARCHAR(16384)";
    default: return "VARCHAR(1)";
  }
}

static std::string build_json_array(const FileTable &table)
{
  std::string json;
  json.reserve(table.rows_.size() * 64 + 2);
  json.push_back('[');
  for (size_t r = 0; r < table.rows_.size(); ++r) {
    if (r > 0) json.push_back(',');
    json.push_back('{');
    for (size_t c = 0; c < table.columns_.size(); ++c) {
      if (c > 0) json.push_back(',');
      json += "\"c";
      char buf[32];
      snprintf(buf, sizeof(buf), "%zu", c);
      json += buf;
      json += "\":";
      if (c >= table.rows_[r].size() || table.rows_[r][c].is_null_) {
        json += "null";
        continue;
      }
      const FileCell &cell = table.rows_[r][c];
      if (cell.is_null_) {
        json += "null";
      } else if (table.columns_[c].type_ == FT_BOOLEAN) {
        if (0 == strcasecmp(cell.text_.c_str(), "true")) {
          json += "true";
        } else if (0 == strcasecmp(cell.text_.c_str(), "false")) {
          json += "false";
        } else {
          json += "null";
        }
      } else {
        std::string value = cell.text_;
        if (table.columns_[c].type_ == FT_DATETIME && value.size() > 10 && value[10] == 'T') {
          value[10] = ' ';
        }
        json.push_back('"');
        json += json_escape(value);
        json.push_back('"');
      }
    }
    json.push_back('}');
  }
  json.push_back(']');
  return json;
}

static std::string build_json_table(const FileTable &table, const std::string &alias)
{
  std::string sql;
  sql += "JSON_TABLE(CONVERT(0x";
  sql += to_hex(build_json_array(table));
  sql += " USING utf8mb4), '$[*]' COLUMNS(";
  for (size_t c = 0; c < table.columns_.size(); ++c) {
    if (c > 0) sql += ",";
    sql += bt_quote(table.columns_[c].name_);
    sql += " ";
    sql += sql_type_name(table.columns_[c].type_);
    sql += " PATH '$.";
    char buf[32];
    snprintf(buf, sizeof(buf), "c%zu", c);
    sql += buf;
    sql += "'";
  }
  sql += "))";
  if (!alias.empty()) {
    sql += " AS ";
    sql += alias;
  }
  return sql;
}

static bool is_reserved_alias_word(const std::string &word)
{
  static const char *words[] = {
    "where", "on", "join", "left", "right", "inner", "outer", "cross", "full",
    "group", "order", "having", "limit", "union", "except", "intersect", "using",
    "natural", "straight_join", "for", "lock", "into", "offset", "fetch", "window"
  };
  std::string w = to_lower(word);
  for (size_t i = 0; i < sizeof(words) / sizeof(words[0]); ++i) {
    if (w == words[i]) return true;
  }
  return false;
}

static bool has_alias_after(const std::string &s, size_t pos)
{
  size_t p = pos;
  while (p < s.size() && (s[p] == ' ' || s[p] == '\t' || s[p] == '\r' || s[p] == '\n')) ++p;
  if (p >= s.size()) return false;
  if (starts_with_ci(s, p, "as")) {
    size_t q = p + 2;
    if (q >= s.size() || !is_ident_char(s[q])) return true;
  }
  if (is_ident_start(s[p])) {
    size_t q = p;
    while (q < s.size() && is_ident_char(s[q])) ++q;
    std::string word = s.substr(p, q - p);
    if (!is_reserved_alias_word(word)) return true;
  }
  return false;
}

static size_t find_matching_paren(const std::string &s, size_t open)
{
  int depth = 0;
  bool in_single = false;
  bool in_double = false;
  bool in_backtick = false;
  bool in_line_comment = false;
  bool in_block_comment = false;
  for (size_t i = open; i < s.size(); ++i) {
    char c = s[i];
    if (in_line_comment) {
      if (c == '\n') in_line_comment = false;
      continue;
    }
    if (in_block_comment) {
      if (c == '*' && i + 1 < s.size() && s[i + 1] == '/') { in_block_comment = false; ++i; }
      continue;
    }
    if (in_single) {
      if (c == '\\') { ++i; continue; }
      if (c == '\'') {
        if (i + 1 < s.size() && s[i + 1] == '\'') { ++i; continue; }
        in_single = false;
      }
      continue;
    }
    if (in_double) {
      if (c == '\\') { ++i; continue; }
      if (c == '"') {
        if (i + 1 < s.size() && s[i + 1] == '"') { ++i; continue; }
        in_double = false;
      }
      continue;
    }
    if (in_backtick) {
      if (c == '`') {
        if (i + 1 < s.size() && s[i + 1] == '`') { ++i; continue; }
        in_backtick = false;
      }
      continue;
    }
    if (c == '-' && i + 1 < s.size() && s[i + 1] == '-') { in_line_comment = true; ++i; continue; }
    if (c == '#') { in_line_comment = true; continue; }
    if (c == '/' && i + 1 < s.size() && s[i + 1] == '*') { in_block_comment = true; ++i; continue; }
    if (c == '\'') { in_single = true; continue; }
    if (c == '"') { in_double = true; continue; }
    if (c == '`') { in_backtick = true; continue; }
    if (c == '(') {
      ++depth;
    } else if (c == ')') {
      --depth;
      if (depth == 0) return i;
    }
  }
  return std::string::npos;
}

static std::vector<std::string> split_top_level(const std::string &s, char sep)
{
  std::vector<std::string> out;
  size_t start = 0;
  int paren = 0;
  bool in_single = false;
  bool in_double = false;
  bool in_backtick = false;
  for (size_t i = 0; i < s.size(); ++i) {
    char c = s[i];
    if (in_single) {
      if (c == '\\') { ++i; }
      else if (c == '\'') {
        if (i + 1 < s.size() && s[i + 1] == '\'') ++i; else in_single = false;
      }
    } else if (in_double) {
      if (c == '\\') { ++i; }
      else if (c == '"') {
        if (i + 1 < s.size() && s[i + 1] == '"') ++i; else in_double = false;
      }
    } else if (in_backtick) {
      if (c == '`') {
        if (i + 1 < s.size() && s[i + 1] == '`') ++i; else in_backtick = false;
      }
    } else if (c == '\'') in_single = true;
    else if (c == '"') in_double = true;
    else if (c == '`') in_backtick = true;
    else if (c == '(') ++paren;
    else if (c == ')') --paren;
    else if (c == sep && paren == 0) {
      out.push_back(trim_str(s.substr(start, i - start)));
      start = i + 1;
    }
  }
  out.push_back(trim_str(s.substr(start)));
  return out;
}

static bool parse_sql_string(const std::string &s, std::string &out)
{
  std::string t = trim_str(s);
  if (t.size() < 2 || (t[0] != '\'' && t[0] != '"')) return false;
  char q = t[0];
  if (t[t.size() - 1] != q) return false;
  out.clear();
  for (size_t i = 1; i + 1 < t.size(); ++i) {
    char c = t[i];
    if (c == '\\' && i + 2 < t.size()) {
      char e = t[++i];
      switch (e) {
        case 'n': out.push_back('\n'); break;
        case 'r': out.push_back('\r'); break;
        case 't': out.push_back('\t'); break;
        case '0': out.push_back('\0'); break;
        case 'b': out.push_back('\b'); break;
        default: out.push_back(e); break;
      }
    } else if (c == q && i + 2 < t.size() && t[i + 1] == q) {
      out.push_back(q);
      ++i;
    } else {
      out.push_back(c);
    }
  }
  return true;
}

static std::string get_arg_value(const std::vector<std::string> &args,
                                 const std::string &key,
                                 size_t positional,
                                 bool &found)
{
  found = false;
  std::string lkey = to_lower(key);
  for (size_t i = 0; i < args.size(); ++i) {
    const std::string &a = args[i];
    size_t eq = a.find("=>");
    size_t eq_len = 2;
    if (eq == std::string::npos) {
      eq = a.find('=');
      eq_len = 1;
    }
    if (eq != std::string::npos) {
      std::string k = to_lower(trim_str(a.substr(0, eq)));
      if (k == lkey) {
        found = true;
        return trim_str(a.substr(eq + eq_len));
      }
    }
  }
  if (positional != static_cast<size_t>(-1)) {
    size_t idx = 0;
    for (size_t i = 0; i < args.size(); ++i) {
      if (args[i].find('=') == std::string::npos) {
        if (idx == positional) {
          found = true;
          return args[i];
        }
        ++idx;
      }
    }
  }
  return std::string();
}

static bool parse_bool_literal(const std::string &s, bool &v)
{
  std::string t = to_lower(trim_str(s));
  if (t == "true" || t == "1" || t == "on") { v = true; return true; }
  if (t == "false" || t == "0" || t == "off") { v = false; return true; }
  return false;
}

static bool get_positional_string(const std::vector<std::string> &args,
                                  size_t index, std::string &out)
{
  size_t pos = 0;
  for (size_t i = 0; i < args.size(); ++i) {
    if (args[i].find('=') == std::string::npos) {
      if (pos == index) {
        return parse_sql_string(args[i], out);
      }
      ++pos;
    }
  }
  return false;
}

static std::string get_option_string(const std::vector<std::string> &args,
                                     const std::string &key,
                                     const std::string &def)
{
  bool found = false;
  std::string raw = get_arg_value(args, key, static_cast<size_t>(-1), found);
  std::string out;
  if (found && parse_sql_string(raw, out)) {
    return out;
  }
  return def;
}

struct FunctionCall
{
  std::string name_;
  std::string args_text_;
  size_t begin_;
  size_t end_;
  FunctionCall() : name_(), args_text_(), begin_(0), end_(0) {}
};

static bool find_next_function(const std::string &sql, size_t from, FunctionCall &call)
{
  bool in_single = false;
  bool in_double = false;
  bool in_backtick = false;
  bool in_line_comment = false;
  bool in_block_comment = false;
  for (size_t i = from; i < sql.size(); ++i) {
    char c = sql[i];
    if (in_line_comment) {
      if (c == '\n') in_line_comment = false;
      continue;
    }
    if (in_block_comment) {
      if (c == '*' && i + 1 < sql.size() && sql[i + 1] == '/') { in_block_comment = false; ++i; }
      continue;
    }
    if (in_single) {
      if (c == '\\') { ++i; continue; }
      if (c == '\'') {
        if (i + 1 < sql.size() && sql[i + 1] == '\'') { ++i; continue; }
        in_single = false;
      }
      continue;
    }
    if (in_double) {
      if (c == '\\') { ++i; continue; }
      if (c == '"') {
        if (i + 1 < sql.size() && sql[i + 1] == '"') { ++i; continue; }
        in_double = false;
      }
      continue;
    }
    if (in_backtick) {
      if (c == '`') {
        if (i + 1 < sql.size() && sql[i + 1] == '`') { ++i; continue; }
        in_backtick = false;
      }
      continue;
    }
    if (c == '-' && i + 1 < sql.size() && sql[i + 1] == '-') { in_line_comment = true; ++i; continue; }
    if (c == '#') { in_line_comment = true; continue; }
    if (c == '/' && i + 1 < sql.size() && sql[i + 1] == '*') { in_block_comment = true; ++i; continue; }
    if (c == '\'') { in_single = true; continue; }
    if (c == '"') { in_double = true; continue; }
    if (c == '`') { in_backtick = true; continue; }
    if (is_ident_start(c)) {
      size_t j = i;
      while (j < sql.size() && is_ident_char(sql[j])) ++j;
      std::string word = to_lower(sql.substr(i, j - i));
      bool is_file_func = (word == "read_csv" || word == "read_json" ||
                           word == "read_ndjson" || word == "read_parquet" ||
                           word == "glob");
      if (is_file_func) {
        size_t p = j;
        while (p < sql.size() && (sql[p] == ' ' || sql[p] == '\t' || sql[p] == '\r' || sql[p] == '\n')) ++p;
        if (p < sql.size() && sql[p] == '(') {
          size_t close = find_matching_paren(sql, p);
          if (close == std::string::npos) return false;
          call.name_ = word;
          call.args_text_ = sql.substr(p + 1, close - p - 1);
          call.begin_ = i;
          call.end_ = close + 1;
          return true;
        }
      }
      i = j - 1;
    }
  }
  return false;
}

static int check_path_access(ObSQLSessionInfo &session, const std::string &path)
{
  int ret = OB_SUCCESS;
  ObString secure;
  char resolved[PATH_MAX];
  if (OB_FAIL(session.get_secure_file_priv(secure))) {
  } else {
    std::string check_path;
    if (NULL != realpath(path.c_str(), resolved)) {
      check_path.assign(resolved);
    } else {
      // The path may be a COPY target or a glob pattern. Resolve its parent
      // directory so path escapes are still detected before the file exists.
      size_t slash = path.find_last_of('/');
      std::string parent = (slash == std::string::npos) ? "." : path.substr(0, slash);
      std::string base = (slash == std::string::npos) ? path : path.substr(slash + 1);
      if (parent.empty()) parent = "/";
      if (NULL == realpath(parent.c_str(), resolved)) {
        ret = OB_FILE_NOT_EXIST;
      } else {
        check_path.assign(resolved);
        if (check_path.empty() || check_path[check_path.size() - 1] != '/') check_path.push_back('/');
        check_path += base;
      }
    }
    if (OB_SUCC(ret) &&
        OB_FAIL(ObResolverUtils::check_secure_path(
            secure, ObString(static_cast<int32_t>(check_path.size()), check_path.data())))) {
      LOG_WARN("file path is not allowed by secure_file_priv", K(ret), K(path.c_str()));
    }
  }
  return ret;
}

// ---------------------------------------------------------------------------
// Minimal Parquet reader (flat schema, optional/required scalar columns).
// Supports PLAIN and dictionary pages, V1/V2 data pages, Snappy compression.
// ---------------------------------------------------------------------------

struct PqSchemaElem
{
  int type_;
  int rep_;
  int converted_;
  int type_length_;
  std::string name_;
  int children_;
  PqSchemaElem() : type_(-1), rep_(0), converted_(-1), type_length_(0), name_(), children_(0) {}
};

struct PqColMeta
{
  int type_;
  int codec_;
  int64_t num_values_;
  int64_t data_offset_;
  int64_t dict_offset_;
  int64_t compressed_size_;
  std::vector<std::string> path_;
  PqColMeta()
    : type_(-1), codec_(0), num_values_(0), data_offset_(0), dict_offset_(-1),
      compressed_size_(0), path_() {}
};

struct PqRowGroup
{
  std::vector<PqColMeta> cols_;
  int64_t num_rows_;
  PqRowGroup() : cols_(), num_rows_(0) {}
};

struct PqMeta
{
  std::vector<PqSchemaElem> schema_;
  std::vector<PqRowGroup> groups_;
  int64_t num_rows_;
  PqMeta() : schema_(), groups_(), num_rows_(0) {}
};

class PqCompactReader
{
public:
  PqCompactReader(const unsigned char *p, const unsigned char *end)
    : p_(p), end_(end), last_(0) {}
  bool field(int &id, int &type)
  {
    if (p_ >= end_) return false;
    unsigned char b = *p_++;
    if (0 == b) { id = 0; type = 0; return true; }
    type = b & 0x0f;
    int delta = b >> 4;
    if (0 == delta) {
      int64_t z = zigzag();
      id = static_cast<int>(last_ + z);
    } else {
      id = last_ + delta;
    }
    last_ = static_cast<int16_t>(id);
    return true;
  }
  bool skip(int type)
  {
    switch (type) {
      case 1: case 2: return true;
      case 3: return p_ < end_ ? (++p_, true) : false;
      case 4: case 5: case 6: varint(); return true;
      case 7: p_ += 8; return p_ <= end_;
      case 8: { uint64_t n = varint(); p_ += n; return p_ <= end_; }
      case 9: case 10: {
        if (p_ >= end_) return false;
        unsigned char h = *p_++;
        uint64_t n = h >> 4;
        int et = h & 0x0f;
        if (15 == n) n = varint();
        for (uint64_t i = 0; i < n; ++i) if (!skip(et)) return false;
        return true;
      }
      case 11: {
        uint64_t n = varint();
        if (n > 0) {
          if (p_ >= end_) return false;
          unsigned char h = *p_++;
          skip(h >> 4);
          skip(h & 0x0f);
        }
        return true;
      }
      case 12: {
        int16_t save = last_; last_ = 0;
        int id = 0, t = 0;
        while (field(id, t)) {
          if (0 == id) break;
          if (!skip(t)) { last_ = save; return false; }
        }
        last_ = save;
        return true;
      }
      default: return false;
    }
  }
  uint64_t varint()
  {
    uint64_t v = 0;
    int shift = 0;
    while (p_ < end_) {
      unsigned char c = *p_++;
      v |= static_cast<uint64_t>(c & 0x7f) << shift;
      if (!(c & 0x80)) break;
      shift += 7;
    }
    return v;
  }
  int64_t zigzag()
  {
    uint64_t n = varint();
    return static_cast<int64_t>(n >> 1) ^ -static_cast<int64_t>(n & 1);
  }
  bool read_binary(std::string &out)
  {
    uint64_t n = varint();
    if (p_ + n > end_) return false;
    out.assign(reinterpret_cast<const char *>(p_), n);
    p_ += n;
    return true;
  }
  bool read_list_header(uint64_t &n, int &elem_type)
  {
    if (p_ >= end_) return false;
    unsigned char h = *p_++;
    n = h >> 4;
    elem_type = h & 0x0f;
    if (15 == n) n = varint();
    return true;
  }
  const unsigned char *pos() const { return p_; }
  int16_t &last() { return last_; }
private:
  const unsigned char *p_;
  const unsigned char *end_;
  int16_t last_;
};

static bool pq_parse_schema(PqCompactReader &r, PqSchemaElem &s)
{
  int16_t save = r.last(); r.last() = 0;
  int id = 0, type = 0;
  while (r.field(id, type)) {
    if (0 == id) break;
    if (1 == id) s.type_ = static_cast<int>(r.zigzag());
    else if (2 == id) s.type_length_ = static_cast<int>(r.zigzag());
    else if (3 == id) s.rep_ = static_cast<int>(r.zigzag());
    else if (4 == id) { if (!r.read_binary(s.name_)) { r.last() = save; return false; } }
    else if (5 == id) s.children_ = static_cast<int>(r.zigzag());
    else if (6 == id) s.converted_ = static_cast<int>(r.zigzag());
    else if (!r.skip(type)) { r.last() = save; return false; }
  }
  r.last() = save;
  return true;
}

static bool pq_parse_col_meta(PqCompactReader &r, PqColMeta &m)
{
  int16_t save = r.last(); r.last() = 0;
  int id = 0, type = 0;
  while (r.field(id, type)) {
    if (0 == id) break;
    if (1 == id) m.type_ = static_cast<int>(r.zigzag());
    else if (2 == id) {
      uint64_t n = 0; int et = 0;
      if (!r.read_list_header(n, et)) { r.last() = save; return false; }
      for (uint64_t i = 0; i < n; ++i) r.zigzag();
    } else if (3 == id) {
      uint64_t n = 0; int et = 0;
      if (!r.read_list_header(n, et)) { r.last() = save; return false; }
      for (uint64_t i = 0; i < n; ++i) {
        std::string p;
        if (!r.read_binary(p)) { r.last() = save; return false; }
        m.path_.push_back(p);
      }
    } else if (4 == id) m.codec_ = static_cast<int>(r.zigzag());
    else if (5 == id) m.num_values_ = r.zigzag();
    else if (7 == id) m.compressed_size_ = r.zigzag();
    else if (9 == id) m.data_offset_ = r.zigzag();
    else if (11 == id) m.dict_offset_ = r.zigzag();
    else if (!r.skip(type)) { r.last() = save; return false; }
  }
  r.last() = save;
  return true;
}

static bool pq_parse_col_chunk(PqCompactReader &r, PqColMeta &m)
{
  int16_t save = r.last(); r.last() = 0;
  int id = 0, type = 0;
  while (r.field(id, type)) {
    if (0 == id) break;
    if (3 == id) {
      if (!pq_parse_col_meta(r, m)) { r.last() = save; return false; }
    } else if (!r.skip(type)) { r.last() = save; return false; }
  }
  r.last() = save;
  return true;
}

static bool pq_parse_row_group(PqCompactReader &r, PqRowGroup &g)
{
  int16_t save = r.last(); r.last() = 0;
  int id = 0, type = 0;
  while (r.field(id, type)) {
    if (0 == id) break;
    if (1 == id) {
      uint64_t n = 0; int et = 0;
      if (!r.read_list_header(n, et)) { r.last() = save; return false; }
      for (uint64_t i = 0; i < n; ++i) {
        PqColMeta m;
        if (!pq_parse_col_chunk(r, m)) { r.last() = save; return false; }
        g.cols_.push_back(m);
      }
    } else if (2 == id) { (void)r.zigzag(); }
    else if (3 == id) g.num_rows_ = r.zigzag();
    else if (!r.skip(type)) { r.last() = save; return false; }
  }
  r.last() = save;
  return true;
}

static bool pq_parse_meta(PqCompactReader &r, PqMeta &meta)
{
  int16_t save = r.last(); r.last() = 0;
  int id = 0, type = 0;
  while (r.field(id, type)) {
    if (0 == id) break;
    if (1 == id) { (void)r.zigzag(); }
    else if (2 == id) {
      uint64_t n = 0; int et = 0;
      if (!r.read_list_header(n, et)) { r.last() = save; return false; }
      for (uint64_t i = 0; i < n; ++i) {
        PqSchemaElem s;
        if (!pq_parse_schema(r, s)) { r.last() = save; return false; }
        meta.schema_.push_back(s);
      }
    } else if (3 == id) meta.num_rows_ = r.zigzag();
    else if (4 == id) {
      uint64_t n = 0; int et = 0;
      if (!r.read_list_header(n, et)) { r.last() = save; return false; }
      for (uint64_t i = 0; i < n; ++i) {
        PqRowGroup g;
        if (!pq_parse_row_group(r, g)) { r.last() = save; return false; }
        meta.groups_.push_back(g);
      }
    } else if (!r.skip(type)) { r.last() = save; return false; }
  }
  r.last() = save;
  return true;
}

static bool pq_snappy(const unsigned char *in, size_t in_len, std::string &out)
{
  size_t p = 0;
  uint64_t expected = 0;
  int shift = 0;
  while (p < in_len) {
    unsigned char c = in[p++];
    expected |= static_cast<uint64_t>(c & 0x7f) << shift;
    if (!(c & 0x80)) break;
    shift += 7;
  }
  out.clear();
  out.reserve(expected);
  while (p < in_len && out.size() < expected) {
    unsigned char tag = in[p++];
    int t = tag & 3;
    if (0 == t) {
      size_t len = (tag >> 2) + 1;
      if (len > 60) {
        size_t nb = len - 60;
        len = 0;
        for (size_t i = 0; i < nb; ++i) len |= static_cast<size_t>(in[p++]) << (8 * i);
        ++len;
      }
      if (p + len > in_len) return false;
      out.append(reinterpret_cast<const char *>(in + p), len);
      p += len;
    } else if (1 == t) {
      size_t len = ((tag >> 2) & 7) + 4;
      size_t off = ((tag & 0xe0) << 3) | in[p++];
      if (0 == off || off > out.size()) return false;
      for (size_t i = 0; i < len; ++i) out.push_back(out[out.size() - off]);
    } else if (2 == t) {
      size_t len = (tag >> 2) + 1;
      size_t off = static_cast<size_t>(in[p]) | (static_cast<size_t>(in[p + 1]) << 8);
      p += 2;
      if (0 == off || off > out.size()) return false;
      for (size_t i = 0; i < len; ++i) out.push_back(out[out.size() - off]);
    } else {
      size_t len = (tag >> 2) + 1;
      size_t off = static_cast<size_t>(in[p]) | (static_cast<size_t>(in[p + 1]) << 8) |
                   (static_cast<size_t>(in[p + 2]) << 16) | (static_cast<size_t>(in[p + 3]) << 24);
      p += 4;
      if (0 == off || off > out.size()) return false;
      for (size_t i = 0; i < len; ++i) out.push_back(out[out.size() - off]);
    }
  }
  return out.size() == expected;
}

static bool pq_varint(const unsigned char *&p, const unsigned char *end, uint64_t &v)
{
  v = 0;
  int shift = 0;
  while (p < end) {
    unsigned char c = *p++;
    v |= static_cast<uint64_t>(c & 0x7f) << shift;
    if (!(c & 0x80)) return true;
    shift += 7;
  }
  return false;
}

static bool pq_rle(const unsigned char *&p, const unsigned char *end,
                   int bit_width, size_t count, bool len_prefix,
                   std::vector<uint32_t> &out)
{
  const unsigned char *stop = end;
  if (len_prefix) {
    if (end - p < 4) return false;
    uint32_t len = static_cast<uint32_t>(p[0]) | (static_cast<uint32_t>(p[1]) << 8) |
                   (static_cast<uint32_t>(p[2]) << 16) | (static_cast<uint32_t>(p[3]) << 24);
    p += 4;
    stop = p + len;
    if (stop > end) return false;
  }
  out.clear();
  out.reserve(count);
  while (p < stop && out.size() < count) {
    uint64_t header = 0;
    if (!pq_varint(p, stop, header)) return false;
    if ((header & 1) == 0) {
      size_t run = static_cast<size_t>(header >> 1);
      size_t nbytes = (bit_width + 7) / 8;
      if (p + nbytes > stop) return false;
      uint32_t v = 0;
      for (size_t i = 0; i < nbytes; ++i) v |= static_cast<uint32_t>(p[i]) << (8 * i);
      p += nbytes;
      for (size_t i = 0; i < run && out.size() < count; ++i) out.push_back(v);
    } else {
      size_t groups = static_cast<size_t>(header >> 1);
      size_t total = groups * 8;
      size_t nbytes = (total * bit_width + 7) / 8;
      if (p + nbytes > stop) return false;
      uint64_t bit = 0;
      for (size_t i = 0; i < total && out.size() < count; ++i) {
        uint32_t v = 0;
        for (int b = 0; b < bit_width; ++b) {
          size_t byte_i = (bit + b) / 8;
          size_t bit_i = (bit + b) % 8;
          if (p[byte_i] & (1 << bit_i)) v |= (1u << b);
        }
        bit += bit_width;
        out.push_back(v);
      }
      p += nbytes;
    }
  }
  return out.size() == count;
}

struct PqPageHeader
{
  int type_;
  int compressed_;
  int uncompressed_;
  int num_values_;
  int encoding_;
  int def_encoding_;
  int v2_num_values_;
  int v2_num_nulls_;
  int v2_def_len_;
  int v2_rep_len_;
  bool v2_compressed_;
  PqPageHeader()
    : type_(-1), compressed_(0), uncompressed_(0), num_values_(0), encoding_(-1),
      def_encoding_(-1), v2_num_values_(0), v2_num_nulls_(0), v2_def_len_(0), v2_rep_len_(0),
      v2_compressed_(true) {}
};

static bool pq_data_page_header(PqCompactReader &r, PqPageHeader &h)
{
  int16_t save = r.last(); r.last() = 0;
  int id = 0, type = 0;
  while (r.field(id, type)) {
    if (0 == id) break;
    if (1 == id) h.num_values_ = static_cast<int>(r.zigzag());
    else if (2 == id) h.encoding_ = static_cast<int>(r.zigzag());
    else if (3 == id) h.def_encoding_ = static_cast<int>(r.zigzag());
    else if (!r.skip(type)) { r.last() = save; return false; }
  }
  r.last() = save;
  return true;
}

static bool pq_dict_page_header(PqCompactReader &r, PqPageHeader &h)
{
  int16_t save = r.last(); r.last() = 0;
  int id = 0, type = 0;
  while (r.field(id, type)) {
    if (0 == id) break;
    if (1 == id) h.num_values_ = static_cast<int>(r.zigzag());
    else if (2 == id) h.encoding_ = static_cast<int>(r.zigzag());
    else if (!r.skip(type)) { r.last() = save; return false; }
  }
  r.last() = save;
  return true;
}

static bool pq_data_page_v2_header(PqCompactReader &r, PqPageHeader &h)
{
  int16_t save = r.last(); r.last() = 0;
  int id = 0, type = 0;
  while (r.field(id, type)) {
    if (0 == id) break;
    if (1 == id) h.v2_num_values_ = static_cast<int>(r.zigzag());
    else if (2 == id) h.v2_num_nulls_ = static_cast<int>(r.zigzag());
    else if (4 == id) h.encoding_ = static_cast<int>(r.zigzag());
    else if (5 == id) h.v2_def_len_ = static_cast<int>(r.zigzag());
    else if (6 == id) h.v2_rep_len_ = static_cast<int>(r.zigzag());
    else if (7 == id) h.v2_compressed_ = (1 == type);
    else if (!r.skip(type)) { r.last() = save; return false; }
  }
  r.last() = save;
  return true;
}

static bool pq_page_header(const std::string &data, size_t off, PqPageHeader &h, size_t &used)
{
  if (off >= data.size()) return false;
  PqCompactReader r(reinterpret_cast<const unsigned char *>(data.data()) + off,
                    reinterpret_cast<const unsigned char *>(data.data()) + data.size());
  int16_t save = r.last(); r.last() = 0;
  int id = 0, type = 0;
  while (r.field(id, type)) {
    if (0 == id) break;
    if (1 == id) h.type_ = static_cast<int>(r.zigzag());
    else if (2 == id) h.uncompressed_ = static_cast<int>(r.zigzag());
    else if (3 == id) h.compressed_ = static_cast<int>(r.zigzag());
    else if (5 == id) { if (!pq_data_page_header(r, h)) return false; }
    else if (7 == id) { if (!pq_dict_page_header(r, h)) return false; }
    else if (8 == id) { if (!pq_data_page_v2_header(r, h)) return false; }
    else if (!r.skip(type)) return false;
  }
  r.last() = save;
  used = static_cast<size_t>(r.pos() - (reinterpret_cast<const unsigned char *>(data.data()) + off));
  return true;
}

static std::string pq_date(int32_t days)
{
  int64_t z = static_cast<int64_t>(days) + 719468;
  int64_t era = (z >= 0 ? z : z - 146096) / 146097;
  unsigned doe = static_cast<unsigned>(z - era * 146097);
  unsigned yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
  int64_t y = static_cast<int64_t>(yoe) + era * 400;
  unsigned doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
  unsigned mp = (5 * doy + 2) / 153;
  unsigned d = doy - (153 * mp + 2) / 5 + 1;
  unsigned m = mp + (mp < 10 ? 3 : -9);
  y += (m <= 2);
  char buf[64];
  snprintf(buf, sizeof(buf), "%04lld-%02u-%02u", static_cast<long long>(y), m, d);
  return buf;
}

static std::string pq_datetime(int64_t millis)
{
  int64_t days = millis / 86400000LL;
  int64_t rem = millis % 86400000LL;
  if (rem < 0) { rem += 86400000LL; --days; }
  int hh = static_cast<int>(rem / 3600000); rem %= 3600000;
  int mm = static_cast<int>(rem / 60000); rem %= 60000;
  int ss = static_cast<int>(rem / 1000);
  char buf[64];
  snprintf(buf, sizeof(buf), "%s %02d:%02d:%02d", pq_date(static_cast<int32_t>(days)).c_str(), hh, mm, ss);
  return buf;
}

static bool pq_plain_values(const unsigned char *&p, const unsigned char *end,
                            int type, size_t count, std::vector<std::string> &out)
{
  out.clear();
  out.reserve(count);
  for (size_t i = 0; i < count; ++i) {
    if (0 == type) {
      size_t byte_i = i / 8;
      size_t bit_i = i % 8;
      if (p + byte_i >= end) return false;
      out.push_back((p[byte_i] & (1 << bit_i)) ? "true" : "false");
    } else if (1 == type) {
      if (end - p < 4) return false;
      int32_t v = static_cast<int32_t>(static_cast<uint32_t>(p[0]) |
                                       (static_cast<uint32_t>(p[1]) << 8) |
                                       (static_cast<uint32_t>(p[2]) << 16) |
                                       (static_cast<uint32_t>(p[3]) << 24));
      p += 4;
      char buf[32]; snprintf(buf, sizeof(buf), "%d", v); out.push_back(buf);
    } else if (2 == type) {
      if (end - p < 8) return false;
      uint64_t u = 0;
      for (int b = 0; b < 8; ++b) u |= static_cast<uint64_t>(p[b]) << (8 * b);
      p += 8;
      char buf[32]; snprintf(buf, sizeof(buf), "%lld", static_cast<long long>(u)); out.push_back(buf);
    } else if (4 == type) {
      if (end - p < 4) return false;
      uint32_t u = static_cast<uint32_t>(p[0]) | (static_cast<uint32_t>(p[1]) << 8) |
                   (static_cast<uint32_t>(p[2]) << 16) | (static_cast<uint32_t>(p[3]) << 24);
      float f; memcpy(&f, &u, 4); p += 4;
      char buf[64]; snprintf(buf, sizeof(buf), "%.9g", f); out.push_back(buf);
    } else if (5 == type) {
      if (end - p < 8) return false;
      uint64_t u = 0;
      for (int b = 0; b < 8; ++b) u |= static_cast<uint64_t>(p[b]) << (8 * b);
      double d; memcpy(&d, &u, 8); p += 8;
      char buf[64]; snprintf(buf, sizeof(buf), "%.17g", d); out.push_back(buf);
    } else if (6 == type) {
      if (end - p < 4) return false;
      uint32_t len = static_cast<uint32_t>(p[0]) | (static_cast<uint32_t>(p[1]) << 8) |
                     (static_cast<uint32_t>(p[2]) << 16) | (static_cast<uint32_t>(p[3]) << 24);
      p += 4;
      if (static_cast<size_t>(end - p) < len) return false;
      out.push_back(std::string(reinterpret_cast<const char *>(p), len));
      p += len;
    } else {
      return false;
    }
  }
  return true;
}

static int load_parquet(const std::string &path, FileTable &table)
{
  int ret = OB_SUCCESS;
  std::string data;
  if (OB_FAIL(read_file_bytes(path, data))) {
  } else if (data.size() < 12 || 0 != data.compare(0, 4, "PAR1") ||
             0 != data.compare(data.size() - 4, 4, "PAR1")) {
    ret = OB_INVALID_DATA;
  } else {
    uint32_t footer_len = static_cast<uint32_t>(static_cast<unsigned char>(data[data.size() - 8])) |
                          (static_cast<uint32_t>(static_cast<unsigned char>(data[data.size() - 7])) << 8) |
                          (static_cast<uint32_t>(static_cast<unsigned char>(data[data.size() - 6])) << 16) |
                          (static_cast<uint32_t>(static_cast<unsigned char>(data[data.size() - 5])) << 24);
    size_t footer_off = data.size() - 8 - footer_len;
    if (footer_off >= data.size()) {
      ret = OB_INVALID_DATA;
    } else {
      PqMeta meta;
      PqCompactReader r(reinterpret_cast<const unsigned char *>(data.data()) + footer_off,
                        reinterpret_cast<const unsigned char *>(data.data()) + data.size() - 8);
      if (!pq_parse_meta(r, meta)) {
        ret = OB_INVALID_DATA;
      } else if (meta.schema_.size() < 2) {
        ret = OB_INVALID_DATA;
      } else {
        // Flat schema: every non-root element is a column.
        for (size_t i = 1; i < meta.schema_.size(); ++i) {
          FileColumn col;
          col.name_ = meta.schema_[i].name_;
          col.nullable_ = (meta.schema_[i].rep_ == 1);
          int t = meta.schema_[i].type_;
          int conv = meta.schema_[i].converted_;
          if (0 == t) col.type_ = FT_BOOLEAN;
          else if (1 == t && 6 == conv) col.type_ = FT_DATE;
          else if (2 == t && (9 == conv || 10 == conv)) col.type_ = FT_DATETIME;
          else if (1 == t || 2 == t) col.type_ = FT_BIGINT;
          else if (4 == t || 5 == t) col.type_ = FT_DOUBLE;
          else col.type_ = FT_VARCHAR;
          table.columns_.push_back(col);
        }
        dedup_column_names(table.columns_);
        table.rows_.resize(static_cast<size_t>(meta.num_rows_));
        for (size_t g = 0; g < meta.groups_.size(); ++g) {
          PqRowGroup &group = meta.groups_[g];
          size_t row_base = 0;
          for (size_t pg = 0; pg < g; ++pg) row_base += static_cast<size_t>(meta.groups_[pg].num_rows_);
          for (size_t c = 0; c < group.cols_.size() && c < table.columns_.size(); ++c) {
            PqColMeta &m = group.cols_[c];
            int64_t start = (m.dict_offset_ >= 0) ? m.dict_offset_ : m.data_offset_;
            int64_t end = start + m.compressed_size_;
            if (start < 0 || end > static_cast<int64_t>(data.size())) {
              ret = OB_INVALID_DATA;
              break;
            }
            std::vector<std::string> dictionary;
            std::vector<FileCell> values;
            values.reserve(static_cast<size_t>(group.num_rows_));
            size_t off = static_cast<size_t>(start);
            while (off < static_cast<size_t>(end) && values.size() < static_cast<size_t>(group.num_rows_)) {
              PqPageHeader h;
              size_t used = 0;
              if (!pq_page_header(data, off, h, used) || h.compressed_ < 0 ||
                  off + used + static_cast<size_t>(h.compressed_) > data.size()) {
                ret = OB_INVALID_DATA;
                break;
              }
              const unsigned char *payload = reinterpret_cast<const unsigned char *>(data.data()) + off + used;
              size_t payload_len = static_cast<size_t>(h.compressed_);
              std::string raw;
              if (2 == h.type_) { // dictionary page
                if (1 == m.codec_) {
                  if (!pq_snappy(payload, payload_len, raw)) { ret = OB_INVALID_DATA; break; }
                } else {
                  raw.assign(reinterpret_cast<const char *>(payload), payload_len);
                }
                const unsigned char *p = reinterpret_cast<const unsigned char *>(raw.data());
                const unsigned char *e = p + raw.size();
                if (!pq_plain_values(p, e, m.type_, static_cast<size_t>(h.num_values_), dictionary)) {
                  ret = OB_INVALID_DATA; break;
                }
              } else if (0 == h.type_ || 3 == h.type_) { // data page v1/v2
                int num_values = (3 == h.type_) ? h.v2_num_values_ : h.num_values_;
                int encoding = h.encoding_;
                const unsigned char *data_ptr = payload;
                const unsigned char *data_end = payload + payload_len;
                size_t def_count = static_cast<size_t>(num_values);
                std::vector<uint32_t> def_levels;
                if (3 == h.type_) {
                  if (h.v2_rep_len_ > 0) { data_ptr += h.v2_rep_len_; }
                  size_t def_len = static_cast<size_t>(h.v2_def_len_);
                  if (data_ptr + def_len > data_end) { ret = OB_INVALID_DATA; break; }
                  if (0 == meta.schema_[c + 1].rep_ || 0 == h.v2_num_nulls_) {
                    def_levels.assign(def_count, 1);
                  } else {
                    const unsigned char *dp = data_ptr;
                    const unsigned char *de = data_ptr + def_len;
                    if (!pq_rle(dp, de, 1, def_count, false, def_levels)) { ret = OB_INVALID_DATA; break; }
                  }
                  data_ptr += def_len;
                  if (h.v2_compressed_ && 1 == m.codec_) {
                    size_t expect = 0;
                    if (1 == m.type_ || 4 == m.type_) expect = def_count * 4;
                    else if (2 == m.type_ || 5 == m.type_) expect = def_count * 8;
                    else if (0 == m.type_) expect = (def_count + 7) / 8;
                    bool decompressed = false;
                    if (expect > 0) {
                      for (size_t cand = 0; cand <= 8 && cand < payload_len; ++cand) {
                        if (pq_snappy(payload + cand, payload_len - cand, raw) && raw.size() == expect) {
                          decompressed = true;
                          break;
                        }
                      }
                    }
                    if (!decompressed && !pq_snappy(data_ptr, static_cast<size_t>(data_end - data_ptr), raw)) {
                      ret = OB_INVALID_DATA; break;
                    }
                    data_ptr = reinterpret_cast<const unsigned char *>(raw.data());
                    data_end = data_ptr + raw.size();
                  }
                } else {
                  if (0 == meta.schema_[c + 1].rep_) {
                    def_levels.assign(def_count, 1);
                  } else {
                    const unsigned char *dp = data_ptr;
                    if (!pq_rle(dp, data_end, 1, def_count, true, def_levels)) { ret = OB_INVALID_DATA; break; }
                    data_ptr = dp;
                  }
                  if (1 == m.codec_) {
                    if (!pq_snappy(data_ptr, static_cast<size_t>(data_end - data_ptr), raw)) {
                      ret = OB_INVALID_DATA; break;
                    }
                    data_ptr = reinterpret_cast<const unsigned char *>(raw.data());
                    data_end = data_ptr + raw.size();
                  }
                }
                size_t non_null = 0;
                for (size_t i = 0; i < def_levels.size(); ++i) if (def_levels[i] != 0) ++non_null;
                std::vector<std::string> decoded;
                bool ok = true;
                if (0 == encoding) {
                  ok = pq_plain_values(data_ptr, data_end, m.type_, non_null, decoded);
                } else if (2 == encoding || 8 == encoding) {
                  if (data_ptr >= data_end) { ok = false; }
                  else {
                    int bit_width = *data_ptr++;
                    std::vector<uint32_t> indices;
                    if (!pq_rle(data_ptr, data_end, bit_width, non_null, false, indices)) {
                      ok = false;
                    } else {
                      for (size_t i = 0; i < indices.size() && ok; ++i) {
                        if (indices[i] >= dictionary.size()) ok = false;
                        else decoded.push_back(dictionary[indices[i]]);
                      }
                    }
                  }
                } else {
                  ok = false;
                }
                if (!ok) { ret = OB_INVALID_DATA; break; }
                size_t vi = 0;
                for (size_t i = 0; i < def_levels.size() && values.size() < static_cast<size_t>(group.num_rows_); ++i) {
                  FileCell cell;
                  if (def_levels[i] != 0) {
                    if (vi >= decoded.size()) { ret = OB_INVALID_DATA; break; }
                    cell.is_null_ = false;
                    cell.text_ = decoded[vi++];
                    if (table.columns_[c].type_ == FT_DATE && m.type_ == 1) {
                      cell.text_ = pq_date(atoi(cell.text_.c_str()));
                    } else if (table.columns_[c].type_ == FT_DATETIME && m.type_ == 2) {
                      int64_t v = atoll(cell.text_.c_str());
                      if (10 == meta.schema_[c + 1].converted_) v /= 1000;
                      cell.text_ = pq_datetime(v);
                    }
                  } else {
                    cell.is_null_ = true;
                  }
                  values.push_back(cell);
                }
              } else {
                // index page or unsupported page type; skip it
              }
              off += used + payload_len;
            }
            if (OB_FAIL(ret)) break;
            for (size_t i = 0; i < values.size() && row_base + i < table.rows_.size(); ++i) {
              if (table.rows_[row_base + i].size() < table.columns_.size()) {
                table.rows_[row_base + i].resize(table.columns_.size());
              }
              table.rows_[row_base + i][c] = values[i];
            }
          }
          if (OB_FAIL(ret)) break;
        }
      }
    }
  }
  return ret;
}

static int load_file_table(ObSQLSessionInfo &session,
                           const std::string &path,
                           const std::string &format,
                           const std::vector<std::string> &args,
                           FileTable &table)
{
  int ret = OB_SUCCESS;
  if (OB_FAIL(check_path_access(session, path))) {
  } else if (format == "csv") {
    FileCsvOptions opt;
    bool found = false;
    std::string raw = get_arg_value(args, "header", static_cast<size_t>(-1), found);
    if (found) {
      bool v = false;
      if (!parse_bool_literal(raw, v)) {
        ret = OB_ERR_PARSE_SQL;
      } else {
        opt.header_ = v;
      }
    }
    raw = get_arg_value(args, "sample_size", static_cast<size_t>(-1), found);
    if (OB_SUCC(ret) && found) {
      int64_t v = 0;
      if (!parse_int64(trim_str(raw), v) || v != -1) {
        ret = OB_NOT_SUPPORTED;
        LOG_USER_ERROR(OB_NOT_SUPPORTED, "read_csv sample_size other than -1");
      }
    }
    std::string delim = get_option_string(args, "delimiter", ",");
    std::string quote = get_option_string(args, "quote", "\"");
    std::string escape = get_option_string(args, "escape", "\"");
    if (OB_SUCC(ret)) {
      if (delim.empty() || quote.empty() || escape.empty()) ret = OB_ERR_PARSE_SQL;
      else { opt.delimiter_ = delim[0]; opt.quote_ = quote[0]; opt.escape_ = escape[0]; }
    }
    bool has_null = false;
    std::string null_raw = get_arg_value(args, "nullstr", static_cast<size_t>(-1), has_null);
    if (OB_SUCC(ret) && has_null) {
      if (parse_sql_string(null_raw, opt.nullstr_)) opt.has_nullstr_ = true;
      else ret = OB_ERR_PARSE_SQL;
    }
    if (OB_SUCC(ret) && OB_FAIL(load_csv(path, opt, table))) {
    }
  } else if (format == "json" || format == "ndjson" || format == "newline_delimited") {
    if (OB_FAIL(load_jsonl(path, table))) {
    }
  } else if (format == "parquet") {
    ret = load_parquet(path, table);
  } else {
    ret = OB_ERR_PARSE_SQL;
  }
  return ret;
}

static int build_glob_replacement(const std::string &pattern,
                                 const std::string &alias,
                                 std::string &out)
{
  int ret = OB_SUCCESS;
  glob_t g;
  memset(&g, 0, sizeof(g));
  int grc = glob(pattern.c_str(), GLOB_NOSORT, NULL, &g);
  std::vector<std::string> files;
  if (0 == grc) {
    for (size_t i = 0; i < g.gl_pathc; ++i) {
      struct stat st;
      if (0 == stat(g.gl_pathv[i], &st) && S_ISREG(st.st_mode)) {
        files.push_back(g.gl_pathv[i]);
      }
    }
  } else if (GLOB_NOMATCH != grc) {
    ret = OB_ERR_UNEXPECTED;
  }
  globfree(&g);
  if (OB_SUCC(ret)) {
    std::sort(files.begin(), files.end());
    out = "(SELECT ";
    if (files.empty()) {
      out += "CAST(NULL AS CHAR(1024)) AS file WHERE 1=0";
    } else {
      for (size_t i = 0; i < files.size(); ++i) {
        if (i > 0) out += " UNION ALL SELECT ";
        out += "_utf8mb4";
        out += sql_quote(files[i]);
        out += " AS file";
      }
    }
    out += ")";
    if (!alias.empty()) {
      out += " AS ";
      out += alias;
    }
  }
  return ret;
}

static int rewrite_general(const std::string &input,
                           ObSQLSessionInfo &session,
                           std::string &out);

static int rewrite_describe(const std::string &input,
                            ObSQLSessionInfo &session,
                            std::string &out)
{
  int ret = OB_SUCCESS;
  std::string s = trim_str(input);
  size_t pos = 0;
  if (starts_with_ci(s, 0, "describe")) pos = 8;
  else if (starts_with_ci(s, 0, "desc")) pos = 4;
  while (pos < s.size() && (s[pos] == ' ' || s[pos] == '\t' || s[pos] == '\r' || s[pos] == '\n')) ++pos;
  if (!starts_with_ci(s, pos, "select")) {
    ret = OB_ERR_PARSE_SQL;
  } else {
    pos += 6;
    std::string inner = s.substr(pos);
    FunctionCall call;
    if (!find_next_function(inner, 0, call)) {
      out = input;
    } else {
      std::vector<std::string> args = split_top_level(call.args_text_, ',');
      std::string path;
      bool found = false;
      std::string raw = get_arg_value(args, "path", 0, found);
      if (!found || !parse_sql_string(raw, path)) {
        ret = OB_ERR_PARSE_SQL;
      } else {
        std::string format;
        if (call.name_ == "read_csv") format = "csv";
        else if (call.name_ == "read_parquet") format = "parquet";
        else format = "json";
        std::string fmt_opt = get_option_string(args, "format", "");
        if (fmt_opt.empty()) {
          std::string pos_fmt;
          if (get_positional_string(args, 1, pos_fmt) && !pos_fmt.empty()) fmt_opt = pos_fmt;
        }
        if (!fmt_opt.empty()) format = fmt_opt;
        FileTable table;
        if (OB_FAIL(load_file_table(session, path, format, args, table))) {
        } else if (table.columns_.empty()) {
          ret = OB_INVALID_DATA;
        } else {
          out.clear();
          for (size_t c = 0; c < table.columns_.size(); ++c) {
            if (c > 0) out += " UNION ALL ";
            out += "SELECT ";
            out += "_utf8mb4";
            out += sql_quote(table.columns_[c].name_);
            out += " AS column_name, _utf8mb4";
            out += sql_quote(type_name(table.columns_[c].type_));
            out += " AS column_type, _utf8mb4";
            out += sql_quote(table.columns_[c].nullable_ ? "YES" : "NO");
            out += " AS `null`, NULL AS `key`, NULL AS `default`, NULL AS `extra`";
          }
        }
      }
    }
  }
  return ret;
}

static int extract_select_names(const std::string &sql, std::vector<std::string> &names)
{
  int ret = OB_SUCCESS;
  std::string s = trim_str(sql);
  size_t p = 0;
  if (!starts_with_ci(s, 0, "select")) return OB_ERR_PARSE_SQL;
  p = 6;
  int depth = 0;
  bool in_single = false;
  bool in_double = false;
  bool in_backtick = false;
  size_t from_pos = std::string::npos;
  for (size_t i = p; i < s.size(); ++i) {
    char c = s[i];
    if (in_single) {
      if (c == '\\') ++i;
      else if (c == '\'') { if (i + 1 < s.size() && s[i + 1] == '\'') ++i; else in_single = false; }
    } else if (in_double) {
      if (c == '\\') ++i;
      else if (c == '"') { if (i + 1 < s.size() && s[i + 1] == '"') ++i; else in_double = false; }
    } else if (in_backtick) {
      if (c == '`') { if (i + 1 < s.size() && s[i + 1] == '`') ++i; else in_backtick = false; }
    } else if (c == '\'') in_single = true;
    else if (c == '"') in_double = true;
    else if (c == '`') in_backtick = true;
    else if (c == '(') ++depth;
    else if (c == ')') --depth;
    else if (depth == 0 && starts_with_ci(s, i, "from") &&
             (i == 0 || !is_ident_char(s[i - 1])) &&
             (i + 4 >= s.size() || !is_ident_char(s[i + 4]))) {
      from_pos = i;
      break;
    }
  }
  if (from_pos == std::string::npos) return OB_ERR_PARSE_SQL;
  std::string list = s.substr(p, from_pos - p);
  std::vector<std::string> items = split_top_level(list, ',');
  for (size_t i = 0; i < items.size(); ++i) {
    std::string item = trim_str(items[i]);
    std::string name;
    size_t as_pos = std::string::npos;
    int d = 0;
    bool qs = false, qd = false, qb = false;
    for (size_t j = 0; j < item.size(); ++j) {
      char c = item[j];
      if (qs) { if (c == '\\') ++j; else if (c == '\'') qs = false; }
      else if (qd) { if (c == '\\') ++j; else if (c == '"') qd = false; }
      else if (qb) { if (c == '`') qb = false; }
      else if (c == '\'') qs = true;
      else if (c == '"') qd = true;
      else if (c == '`') qb = true;
      else if (c == '(') ++d;
      else if (c == ')') --d;
      else if (d == 0 && starts_with_ci(item, j, "as") &&
               (j == 0 || !is_ident_char(item[j - 1])) &&
               (j + 2 >= item.size() || !is_ident_char(item[j + 2]))) {
        as_pos = j;
      }
    }
    if (as_pos != std::string::npos) {
      name = trim_str(item.substr(as_pos + 2));
    } else {
      size_t e = item.size();
      while (e > 0 && (item[e - 1] == ' ' || item[e - 1] == '\t')) --e;
      size_t b = e;
      while (b > 0 && (is_ident_char(item[b - 1]) || item[b - 1] == '.')) --b;
      if (b < e) name = item.substr(b, e - b);
    }
    if (!name.empty()) {
      if (name[0] == '`' && name[name.size() - 1] == '`') name = name.substr(1, name.size() - 2);
      size_t dot = name.rfind('.');
      if (dot != std::string::npos) name = name.substr(dot + 1);
      names.push_back(name);
    } else {
      std::ostringstream oss;
      oss << "c" << i;
      names.push_back(oss.str());
    }
  }
  return ret;
}

static int rewrite_copy(const std::string &input,
                        ObSQLSessionInfo &session,
                        std::string &out)
{
  int ret = OB_SUCCESS;
  std::string s = input;
  size_t p = 0;
  if (!starts_with_ci(s, 0, "copy")) return OB_ERR_PARSE_SQL;
  p = 4;
  while (p < s.size() && isspace(static_cast<unsigned char>(s[p]))) ++p;
  if (p >= s.size() || s[p] != '(') return OB_ERR_PARSE_SQL;
  size_t close = find_matching_paren(s, p);
  if (close == std::string::npos) return OB_ERR_PARSE_SQL;
  std::string inner = trim_str(s.substr(p + 1, close - p - 1));
  size_t q = close + 1;
  while (q < s.size() && isspace(static_cast<unsigned char>(s[q]))) ++q;
  if (!starts_with_ci(s, q, "to")) return OB_ERR_PARSE_SQL;
  q += 2;
  while (q < s.size() && isspace(static_cast<unsigned char>(s[q]))) ++q;
  if (q >= s.size() || (s[q] != '\'' && s[q] != '"')) return OB_ERR_PARSE_SQL;
  char quote = s[q];
  size_t path_begin = q;
  ++q;
  while (q < s.size()) {
    if (s[q] == '\\') { q += 2; continue; }
    if (s[q] == quote) {
      if (q + 1 < s.size() && s[q + 1] == quote) { q += 2; continue; }
      break;
    }
    ++q;
  }
  if (q >= s.size()) return OB_ERR_PARSE_SQL;
  std::string path_raw = s.substr(path_begin, q - path_begin + 1);
  std::string path;
  if (!parse_sql_string(path_raw, path)) return OB_ERR_PARSE_SQL;
  ++q;
  while (q < s.size() && isspace(static_cast<unsigned char>(s[q]))) ++q;
  bool header = false;
  std::string delimiter = ",";
  std::string quote_str = "\"";
  std::string escape = "\\";
  std::string nullstr = "NULL";
  if (q < s.size() && s[q] == '(') {
    size_t opt_close = find_matching_paren(s, q);
    if (opt_close == std::string::npos) return OB_ERR_PARSE_SQL;
    std::vector<std::string> opts = split_top_level(s.substr(q + 1, opt_close - q - 1), ',');
    for (size_t i = 0; i < opts.size(); ++i) {
      std::string opt = trim_str(opts[i]);
      std::string lopt = to_lower(opt);
      if (lopt == "header" || lopt == "header true" || lopt == "header=true") {
        header = true;
      } else if (lopt == "header false" || lopt == "header=false") {
        header = false;
      } else if (starts_with_ci(lopt, 0, "format")) {
        // format csv
      } else {
        size_t sp = opt.find_first_of(" \t=");
        if (sp != std::string::npos) {
          std::string key = to_lower(trim_str(opt.substr(0, sp)));
          std::string val = trim_str(opt.substr(sp + 1));
          std::string sv;
          if (key == "delimiter" && parse_sql_string(val, sv)) delimiter = sv;
          else if (key == "quote" && parse_sql_string(val, sv)) quote_str = sv;
          else if (key == "escape" && parse_sql_string(val, sv)) escape = sv;
          else if (key == "nullstr" && parse_sql_string(val, sv)) nullstr = sv;
        }
      }
    }
  }
  std::string rewritten_inner;
  if (OB_FAIL(rewrite_general(inner, session, rewritten_inner))) {
  } else if (OB_FAIL(check_path_access(session, path))) {
  } else {
    std::vector<std::string> names;
    if (OB_FAIL(extract_select_names(inner, names))) {
    } else {
      std::vector<std::string> uniq;
      std::map<std::string, int64_t> seen;
      for (size_t i = 0; i < names.size(); ++i) {
        std::string n = names[i];
        int64_t cnt = ++seen[n];
        if (cnt > 1) {
          std::ostringstream oss;
          oss << n << "__" << cnt;
          n = oss.str();
        }
        uniq.push_back(n);
      }
      out.clear();
      out += "SELECT ";
      for (size_t i = 0; i < uniq.size(); ++i) {
        if (i > 0) out += ",";
        out += bt_quote(uniq[i]);
      }
      out += " FROM (";
      if (header) {
        out += "SELECT 0 AS __fs_ord";
        for (size_t i = 0; i < uniq.size(); ++i) {
          out += ", _utf8mb4";
          out += sql_quote(uniq[i]);
          out += " AS ";
          out += bt_quote(uniq[i]);
        }
        out += " UNION ALL ";
      }
      out += "SELECT 1 AS __fs_ord";
      for (size_t i = 0; i < uniq.size(); ++i) {
        out += ", CAST(";
        out += bt_quote(uniq[i]);
        out += " AS CHAR) AS ";
        out += bt_quote(uniq[i]);
      }
      out += " FROM (";
      out += rewritten_inner;
      out += ") AS __fs_src) AS __fs_out ORDER BY __fs_ord INTO OUTFILE ";
      out += sql_quote(path);
      out += " FORMAT (TYPE='CSV', FIELD_DELIMITER=";
      out += sql_quote(delimiter);
      out += ", FIELD_ENCLOSED_BY=";
      out += sql_quote(quote_str);
      out += ", ESCAPE=";
      out += sql_quote(escape);
      out += ", NULL_IF=(";
      out += sql_quote(nullstr);
      out += "), LINE_DELIMITER='\\n')";
    }
  }
  return ret;
}

static int rewrite_general(const std::string &input,
                           ObSQLSessionInfo &session,
                           std::string &out)
{
  int ret = OB_SUCCESS;
  bool enable = false;
  out.clear();
  size_t pos = 0;
  int64_t alias_id = 0;
  while (OB_SUCC(ret) && pos < input.size()) {
    FunctionCall call;
    if (!find_next_function(input, pos, call)) {
      out.append(input, pos, std::string::npos);
      break;
    }
    if (OB_FAIL(session.get_enable_file_sql(enable))) {
    } else if (!enable) {
      ret = OB_NOT_SUPPORTED;
      LOG_USER_ERROR(OB_NOT_SUPPORTED, "file sql is disabled, set enable_file_sql=ON first");
    } else {
      std::vector<std::string> args = split_top_level(call.args_text_, ',');
      std::string path;
      bool found = false;
      std::string raw = get_arg_value(args, "path", 0, found);
      if (!found || !parse_sql_string(raw, path)) {
        ret = OB_ERR_PARSE_SQL;
      } else if (call.name_ == "glob") {
        std::string alias;
        if (!has_alias_after(input, call.end_)) {
          std::ostringstream oss;
          oss << "__fs" << alias_id++;
          alias = oss.str();
        }
        std::string replacement;
        if (OB_FAIL(check_path_access(session, path))) {
        } else if (OB_FAIL(build_glob_replacement(path, alias, replacement))) {
        } else {
          out.append(input, pos, call.begin_ - pos);
          out += replacement;
          pos = call.end_;
        }
      } else {
        std::string format;
        if (call.name_ == "read_csv") format = "csv";
        else if (call.name_ == "read_parquet") format = "parquet";
        else format = "json";
        std::string fmt_opt = get_option_string(args, "format", "");
        if (fmt_opt.empty()) {
          std::string pos_fmt;
          if (get_positional_string(args, 1, pos_fmt) && !pos_fmt.empty()) fmt_opt = pos_fmt;
        }
        if (!fmt_opt.empty()) format = fmt_opt;
        if (format == "xml") {
          ret = OB_ERR_PARSE_SQL;
        } else {
          FileTable table;
          if (OB_FAIL(load_file_table(session, path, format, args, table))) {
          } else if (table.columns_.empty()) {
            ret = OB_INVALID_DATA;
          } else {
            std::string alias;
            if (!has_alias_after(input, call.end_)) {
              std::ostringstream oss;
              oss << "__fs" << alias_id++;
              alias = oss.str();
            }
            std::string replacement = build_json_table(table, alias);
            out.append(input, pos, call.begin_ - pos);
            out += replacement;
            pos = call.end_;
          }
        }
      }
    }
  }
  return ret;
}

} // namespace

bool ObFileSqlRewriter::maybe_file_sql(const common::ObString &sql)
{
  if (sql.empty()) return false;
  std::string s(sql.ptr(), sql.length());
  std::string lower = to_lower(s);
  return lower.find("read_csv") != std::string::npos ||
         lower.find("read_json") != std::string::npos ||
         lower.find("read_ndjson") != std::string::npos ||
         lower.find("read_parquet") != std::string::npos ||
         lower.find("glob(") != std::string::npos ||
         lower.find("copy ") != std::string::npos ||
         lower.find("describe select") != std::string::npos ||
         lower.find("desc select") != std::string::npos;
}

int ObFileSqlRewriter::rewrite(const common::ObString &sql,
                               ObSQLSessionInfo &session,
                               common::ObIAllocator &allocator,
                               common::ObString &rewritten)
{
  int ret = OB_SUCCESS;
  rewritten.reset();
  if (!maybe_file_sql(sql)) {
    // no-op
  } else {
    std::string input(sql.ptr(), sql.length());
    std::string trimmed = trim_str(input);
    std::string output;
    if (starts_with_ci(trimmed, 0, "copy") &&
        (trimmed.size() == 4 || isspace(static_cast<unsigned char>(trimmed[4])))) {
      ret = rewrite_copy(input, session, output);
    } else if ((starts_with_ci(trimmed, 0, "describe") || starts_with_ci(trimmed, 0, "desc")) &&
               (trimmed.find("select") != std::string::npos)) {
      ret = rewrite_describe(input, session, output);
    } else {
      ret = rewrite_general(input, session, output);
    }
    if (OB_SUCC(ret)) {
      if (output.empty()) {
        rewritten = sql;
      } else if (OB_FAIL(ob_write_string(allocator,
                                         ObString(static_cast<int32_t>(output.size()), output.data()),
                                         rewritten))) {
      }
    }
  }
  return ret;
}

} // namespace sql
} // namespace oceanbase
