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

#ifndef OCEANBASE_OBSERVER_OB_AI_COLUMN_WORKER_H_
#define OCEANBASE_OBSERVER_OB_AI_COLUMN_WORKER_H_

namespace oceanbase
{
namespace common
{
class ObMySQLProxy;
}
namespace observer
{

// The AI COLUMN async worker owns one dedicated background thread. It polls
// oceanbase.__all_ai_column_task for runnable tasks, calls the AI SQL functions
// (ai_complete / ai_embed) through @sql_proxy (inner SQL session, i.e. the same
// inner SQL seam the DML hook uses) and writes the results back to the user
// table. Write-back updates are executed with the AI column DML hook suppressed
// so that they never invalidate the very result they just produced.
//
// Lifecycle: ObServer::start() calls start_ai_column_worker() once the server
// metadata is ready; ObServer::stop() calls stop_ai_column_worker() before the
// inner SQL proxy is stopped.
int start_ai_column_worker(common::ObMySQLProxy *sql_proxy);
void stop_ai_column_worker();
bool is_ai_column_worker_running();

// Hook suppression seam. The implementation lives in
// sql/engine/dml/ob_table_modify_op.cpp (ai_column_dml_util namespace). Keep the
// signature stable: the Lead wires this function to the shared suppression flag
// at integration time.
void set_ai_column_internal_write(bool value);

} // namespace observer
} // namespace oceanbase

#endif // OCEANBASE_OBSERVER_OB_AI_COLUMN_WORKER_H_
