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

#ifndef OCEANBASE_SQL_OB_FILE_SQL_REWRITER_H_
#define OCEANBASE_SQL_OB_FILE_SQL_REWRITER_H_

#include "lib/string/ob_string.h"
#include "lib/allocator/ob_allocator.h"

namespace oceanbase
{
namespace sql
{
class ObSQLSessionInfo;

// Rewrites DuckDB-style file table functions into native seekdb SQL.
// The rewrite keeps all filtering/aggregation/join work in the seekdb engine.
class ObFileSqlRewriter
{
public:
  static bool maybe_file_sql(const common::ObString &sql);
  static int rewrite(const common::ObString &sql,
                     ObSQLSessionInfo &session,
                     common::ObIAllocator &allocator,
                     common::ObString &rewritten);
};

} // namespace sql
} // namespace oceanbase

#endif // OCEANBASE_SQL_OB_FILE_SQL_REWRITER_H_