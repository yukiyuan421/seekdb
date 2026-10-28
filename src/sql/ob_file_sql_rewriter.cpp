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
    LOG_WARN("failed to parse csv", K(ret), K(path), K(bad_line));
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
  } else if (NULL == realpath(path.c_str(), resolved)) {
    ret = OB_FILE_NOT_EXIST;
  } else if (OB_FAIL(ObResolverUtils::check_secure_path(secure, ObString(static_cast<int32_t>(strlen(resolved)), resolved)))) {
    LOG_WARN("file path is not allowed by secure_file_priv", K(ret), K(path));
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
    ret = OB_NOT_SUPPORTED;
    LOG_USER_ERROR(OB_NOT_SUPPORTED, "read_parquet");
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
