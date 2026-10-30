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

#define USING_LOG_PREFIX SQL_ENG

#include "ob_table_modify_op.h"
#include <atomic>
#include <mutex>
#include <string>
#include <unordered_map>
#include <vector>
#include "lib/string/ob_sql_string.h"
#include "lib/time/ob_time_utility.h"
#include "share/schema/ob_column_schema.h"
#include "share/inner_table/ob_inner_table_schema_constants.h"
#include "common/mysqlclient/ob_mysql_proxy.h"
#include "common/mysqlclient/ob_mysql_result.h"
#include "share/ob_autoincrement_service.h"
#include "query/session/ob_inner_sql_connection_access.h"
#include "data_plane/ob_i_dml_service.h"
#include "data_plane/ob_i_write_context_service.h"
#include "data_plane/transaction/ob_i_transaction_service.h"
#include "data_plane/access/ob_dml_table_plan.h"
#include "data_plane/access/ob_dml_execution.h"
#include "data_plane/blocksstable/ob_datum_row.h"
#include "data_plane/blocksstable/ob_datum_row_iterator.h"
#include "sql/engine/ob_physical_plan.h"
#include "sql/engine/dml/ob_dml_service.h"

namespace oceanbase
{
using namespace common;
using namespace common::sqlclient;
using namespace storage;
using namespace share;
using namespace share::schema;
using namespace observer;
namespace sql
{
int ForeignKeyHandle::do_handle(ObTableModifyOp &op,
                                const ObDMLBaseCtDef &dml_ctdef,
                                ObDMLBaseRtDef &dml_rtdef)
{
  int ret = OB_SUCCESS;
  if (op.need_foreign_key_checks()) {
    const ObExprPtrIArray &old_row = dml_ctdef.old_row_;
    const ObExprPtrIArray &new_row = dml_ctdef.new_row_;
    const bool save_in_ignore_cascading = op.get_exec_ctx().get_das_ctx().in_ignore_cascading_;
    op.get_exec_ctx().get_das_ctx().is_fk_cascading_ = true;
    op.get_exec_ctx().get_das_ctx().in_ignore_cascading_ = dml_ctdef.das_base_ctdef_.is_ignore_;
    if (OB_FAIL(op.check_stack())) {
    }
    for (int i = 0; OB_SUCC(ret) && i < dml_ctdef.fk_args_.count(); i++) {
      const ObForeignKeyArg &fk_arg = dml_ctdef.fk_args_.at(i);
      ObForeignKeyChecker *fk_checker = dml_rtdef.fk_checker_array_.at(i);
      if (OB_SUCC(ret) && !new_row.empty()) {
        if (ACTION_CHECK_EXIST == fk_arg.ref_action_) {
          // insert or update.
          bool is_foreign_key_cascade = ObSQLUtils::is_fk_nested_sql(&op.get_exec_ctx());
          bool in_ignore_cascading = false;
          ObExecContext* parent_ctx = op.get_exec_ctx().get_parent_ctx();
          if (OB_NOT_NULL(parent_ctx)) {
            in_ignore_cascading = parent_ctx->get_das_ctx().in_ignore_cascading_;
          }

          if (is_foreign_key_cascade && !in_ignore_cascading) {
            // nested update can not check parent row.
          } else if (OB_FAIL(check_exist(op, fk_arg, new_row, fk_checker, false, fk_arg.use_das_scan_))) {
          }
        }
      }
      if (OB_SUCC(ret) && !old_row.empty()) {
        if (ACTION_RESTRICT == fk_arg.ref_action_ || ACTION_NO_ACTION == fk_arg.ref_action_) {
          // update or delete.
          bool has_changed = false;
          if (OB_FAIL(value_changed(op, fk_arg.columns_, old_row, new_row, has_changed))) {
          } else if (!has_changed) {
            // nothing.
          } else if (OB_FAIL(check_exist(op, fk_arg, old_row, fk_checker, true, fk_arg.use_das_scan_))) {
          }
        } else if (ACTION_CASCADE == fk_arg.ref_action_) {
          // update or delete.
          bool is_self_ref = false;
          if (OB_FAIL(is_self_ref_row(op.get_eval_ctx(), old_row, fk_arg, is_self_ref))) {
          } else if (new_row.empty() && is_self_ref && op.is_fk_nested_session()) {
            // delete self refercnced row should not cascade delete.
          } else if (OB_FAIL(check_exist_inner_sql(op, fk_arg, old_row, true, true))) {
          } else if (OB_FAIL(cascade(op, fk_arg, old_row, new_row))) {
          } else if (!new_row.empty() && is_self_ref) {
            // we got here only when:
            //  1. handling update operator and
            //  2. foreign key constraint is self reference
            // need to change %new_row and %old_row
            //   (see 
            // xxx_row_res_info helps to restore row. restore row before get_next_row()
            //op.fk_self_ref_row_res_infos_.reset();
            for (int64_t i = 0; OB_SUCC(ret) && i < fk_arg.columns_.count(); i++) {
              const int32_t val_idx = fk_arg.columns_.at(i).idx_;
              const int32_t name_idx = fk_arg.columns_.at(i).name_idx_;
              if (OB_SUCC(ret)) {
                const ObDatum &updated_value = new_row.at(val_idx)->
                                                    locate_expr_datum(op.get_eval_ctx());
                ObDatum &new_row_name_col = new_row.at(name_idx)->
                                                  locate_expr_datum(op.get_eval_ctx());
                ObDatum &old_row_name_col = old_row.at(name_idx)->
                                                  locate_expr_datum(op.get_eval_ctx());

                OX(new_row_name_col = updated_value);
                OX(old_row_name_col = updated_value);
              }
            }
          }
        } else if (ACTION_SET_NULL == fk_arg.ref_action_) {
          if (OB_FAIL(check_exist_inner_sql(op, fk_arg, old_row, true, true))) {
          } else if (OB_FAIL(set_null(op, fk_arg, old_row))) {
          }
        }
      } // if (old_row.is_valid())
    } // for
    //fk cascading end
    op.get_exec_ctx().get_das_ctx().is_fk_cascading_ = false;
    op.get_exec_ctx().get_das_ctx().in_ignore_cascading_ = save_in_ignore_cascading;
  } else {
  }
  return ret;
}

int ForeignKeyHandle::value_changed(ObTableModifyOp &op,
                                    const ObIArray<ObForeignKeyColumn> &columns,
                                    const ObExprPtrIArray &old_row,
                                    const ObExprPtrIArray &new_row,
                                    bool &has_changed)
{
  int ret = OB_SUCCESS;
  has_changed = false;
  if (!old_row.empty() && !new_row.empty()) {
    ObDatum *old_row_col = NULL;
    ObDatum *new_row_col = NULL;
    for (int64_t i = 0; OB_SUCC(ret) && !has_changed && i < columns.count(); ++i) {
      int64_t col_idx = columns.at(i).idx_;
      CK(col_idx < old_row.count());
      CK(col_idx < new_row.count());
      CK(OB_NOT_NULL(old_row.at(col_idx)));
      CK(OB_NOT_NULL(new_row.at(col_idx)));
      OZ(old_row.at(col_idx)->eval(op.get_eval_ctx(), old_row_col));
      OZ(new_row.at(col_idx)->eval(op.get_eval_ctx(), new_row_col));
      OX(has_changed = (false == ObDatum::binary_equal(*old_row_col, *new_row_col)));
    }
  } else {
    has_changed = true;
  }
  return ret;
}

int ForeignKeyHandle::check_exist(ObTableModifyOp &modify_op, const ObForeignKeyArg &fk_arg,
                         const ObExprPtrIArray &row, ObForeignKeyChecker *fk_checker, bool expect_zero, bool use_das_scan)
{
  int ret = OB_SUCCESS;
  DEBUG_SYNC(BEFORE_FOREIGN_KEY_CONSTRAINT_CHECK);
  // insertup and merge_into currently have a core problem when checking foreign keys through das_scan_task.
  // Because both insertup and merge_into have both INSERT and UPDATE semantics,
  // the data may come from the new_row of INSERT or the new_row of UPDATE during the operation.
  // Earlier versions did not consider this problem, so there is a possibility of core
  bool is_insertup = false;
  ObPhyOperatorType op_type = modify_op.get_spec().get_type();
  if (op_type == PHY_INSERT_ON_DUP) {
    is_insertup = true;
  }
  if (use_das_scan && !is_insertup) {
    ret = check_exist_scan_task(modify_op, fk_arg, row, fk_checker);
  } else {
    if (OB_FAIL(check_exist_inner_sql(modify_op, fk_arg, row, expect_zero, true))) {
    } else if (OB_FAIL(check_exist_inner_sql(modify_op, fk_arg, row, expect_zero, false))) {
    }
  }
  return ret;
}

int ForeignKeyHandle::check_exist_scan_task(ObTableModifyOp &modify_op, const ObForeignKeyArg &fk_arg,
                         const ObExprPtrIArray &row, ObForeignKeyChecker *fk_checker)
{
  int ret = OB_SUCCESS;
  bool has_result = false;
  if (OB_ISNULL(fk_checker)) {
    ret = OB_ERR_UNEXPECTED;
  } else if (!fk_arg.use_das_scan_) {
    ret = OB_ERR_UNEXPECTED;
  } else if (OB_FAIL(fk_checker->do_fk_check_single_row(fk_arg.columns_, row, has_result))) {
  } else {
    if (!has_result) {
      ret = OB_ERR_NO_REFERENCED_ROW;
    } else {
      ret = OB_SUCCESS;
    }
  }
  return ret;
}

int ForeignKeyHandle::check_exist_inner_sql(ObTableModifyOp &op,
                                            const ObForeignKeyArg &fk_arg,
                                            const ObExprPtrIArray &row,
                                            bool expect_zero,
                                            bool iter_uncommitted_row)
{
  int ret = OB_SUCCESS;
  const char *select_fmt = "select /*+ no_parallel */ 1 from `%.*s`.`%.*s` where %.*s for update";
  ObArenaAllocator alloc(ObModIds::OB_MODULE_PAGE_ALLOCATOR,
                          OB_MALLOC_NORMAL_BLOCK_SIZE);
  char *stmt_buf = nullptr;
  int64_t stmt_len = 0;
  char *where_buf = nullptr;
  int64_t where_len = 0;
  int64_t stmt_pos = 0;
  int64_t where_pos = 0;
  const ObString &database_name = fk_arg.database_name_;
  const ObString &table_name = fk_arg.table_name_;
  if (row.empty()) {
    ret = OB_INVALID_ARGUMENT;
  } else if (OB_FAIL(gen_where(op.get_eval_ctx(), where_buf, where_len, where_pos,
                               fk_arg.columns_, row, alloc, op.get_obj_print_params()))) {
    if (OB_LIKELY(OB_ERR_NULL_VALUE == ret)) {
      // skip check exist if any column in foreign key is NULL.
      ret = OB_SUCCESS;
      stmt_pos = 0;
    } else {
    }
  } else if (OB_FAIL(databuff_printf(stmt_buf, stmt_len, stmt_pos, alloc, select_fmt,
                                     database_name.length(), database_name.ptr(),
                                     table_name.length(), table_name.ptr(),
                                     static_cast<int>(where_pos), where_buf))) {
  } else {
    stmt_buf[stmt_pos++] = 0;
  }
  if (OB_SUCC(ret) && stmt_pos > 0) {
    if (iter_uncommitted_row) {
      op.get_exec_ctx().get_das_ctx().iter_uncommitted_row_ = true;
    }
    SMART_VAR(ObMySQLProxy::MySQLResult, res) {
      if (OB_FAIL(op.begin_nested_session(fk_arg.is_self_ref_))) {
      } else {
        // must call end_nested_session() if begin_nested_session() success.
        bool is_zero = false;
        if (OB_FAIL(op.execute_read(stmt_buf, res))) {
        } else {
          // must call res.get_result()->close() if execute_read() success.
          if (OB_ISNULL(res.get_result())) {
            ret = OB_ERR_UNEXPECTED;
          } else if (OB_FAIL(res.get_result()->next())) {
            if (OB_ITER_END == ret) {
              is_zero = true;
              ret = OB_SUCCESS;
            } else {
            }
          }
          if (OB_SUCC(ret)) {
            if (is_zero != expect_zero) {
              // If it is a self-referencing foreign key new row references new row
              bool is_self_ref = false;
              // The FOR UPDATE check query does not use aggregate functions, so when is_zero is false
              // judge whether only one row is affected by whether the second record can be obtained.
              bool is_affect_only_one = false;
              if (!is_zero && OB_FAIL(res.get_result()->next())) {
                if (OB_ITER_END == ret) {
                  is_affect_only_one = true;
                  ret = OB_SUCCESS;
                } else {
                }
              }
              /**
               *  expect_zero is false when fk_arg.ref_action_ is equal to
               *  ACTION_CHECK_EXIST, if the is_zero != expect_zero condition is
               *  true, then is_zero is true, need to exclude the case of self reference.
               *  other cases return OB_ERR_NO_REFERENCED_ROW.
               *
               *  expect_zero is true when fk_arg.ref_action_ is equal to
               *  ACTION_RESTRICT or ACTION_NO_ACTION, if is_zero != expect_zero condition
               *  is true, then is_zero is false, need to exclude the case of self reference and
               *  only affect one row. other cases return OB_ERR_ROW_IS_REFERENCED.
               */
              if (!iter_uncommitted_row) {
                if (OB_FAIL(is_self_ref_row(op.get_eval_ctx(), row, fk_arg, is_self_ref))) {
                } else if (is_zero && !is_self_ref) {
                  ret = OB_ERR_NO_REFERENCED_ROW;
                } else if (!is_zero) {
                  ret = OB_ERR_ROW_IS_REFERENCED;
                }
              }
            }
          }
          int close_ret = res.get_result()->close();
          if (OB_SUCCESS != close_ret) {
            LOG_WARN("failed to close", K(close_ret));
            if (OB_SUCCESS == ret) {
              ret = close_ret;
            }
          }
        }
        int end_ret = op.end_nested_session();
        if (OB_SUCCESS != end_ret) {
          LOG_WARN("failed to end nested session", K(end_ret));
          if (OB_SUCCESS == ret) {
            ret = end_ret;
          }
        }
      }
    }
  }
  op.get_exec_ctx().get_das_ctx().iter_uncommitted_row_ = false;

  return ret;
}

int ForeignKeyHandle::cascade(ObTableModifyOp &op,
                              const ObForeignKeyArg &fk_arg,
                              const ObExprPtrIArray &old_row,
                              const ObExprPtrIArray &new_row)
{
  int ret = OB_SUCCESS;
  ObArenaAllocator alloc(ObModIds::OB_MODULE_PAGE_ALLOCATOR,
                          OB_MALLOC_NORMAL_BLOCK_SIZE);
  char *stmt_buf = nullptr;
  int64_t stmt_len = 0;
  char *where_buf = nullptr;
  int64_t where_len = 0;
  int64_t stmt_pos = 0;
  int64_t where_pos = 0;
  const ObString &database_name = fk_arg.database_name_;
  const ObString &table_name = fk_arg.table_name_;
  if (OB_FAIL(op.get_exec_ctx().check_status())) {
  } else if (old_row.empty()) {
    ret = OB_INVALID_ARGUMENT;
  } else if (OB_FAIL(gen_where(op.get_eval_ctx(), where_buf, where_len, where_pos,
                               fk_arg.columns_, old_row, alloc, op.get_obj_print_params()))) {
    if (OB_LIKELY(OB_ERR_NULL_VALUE == ret)) {
      // skip cascade if any column in foreign key is NULL.
      ret = OB_SUCCESS;
      stmt_pos = 0;
    } else {
    }
  } else {
    if (!new_row.empty()) {
      // update.
      const char *update_fmt = "update `%.*s`.`%.*s` set %.*s where %.*s";
      char *set_buf = nullptr;
      int64_t set_len = 0;
      int64_t set_pos = 0;
      if (OB_FAIL(gen_set(op.get_eval_ctx(), set_buf, set_len, set_pos,
                          fk_arg.columns_, new_row, alloc, op.get_obj_print_params()))) {
      } else if (OB_FAIL(databuff_printf(stmt_buf, stmt_len, stmt_pos, alloc, update_fmt,
                                         database_name.length(), database_name.ptr(),
                                         table_name.length(), table_name.ptr(),
                                         static_cast<int>(set_pos), set_buf,
                                         static_cast<int>(where_pos), where_buf))) {
      } else {
        stmt_buf[stmt_pos++] = 0;
      }
    } else {
      // delete.
      const char *delete_fmt = "delete from `%.*s`.`%.*s` where %.*s";
      if (OB_FAIL(databuff_printf(stmt_buf, stmt_len, stmt_pos, alloc, delete_fmt,
                                  database_name.length(), database_name.ptr(),
                                  table_name.length(), table_name.ptr(),
                                  static_cast<int>(where_pos), where_buf))) {
      } else {
        stmt_buf[stmt_pos++] = 0;
      }
    }
  }
  if (OB_SUCC(ret) && stmt_pos > 0) {
    if (OB_FAIL(op.begin_nested_session(fk_arg.is_self_ref_))) {
    } else {
      if (OB_FAIL(op.execute_write(stmt_buf))) {
      }
      int end_ret = op.end_nested_session();
      if (OB_SUCCESS != end_ret) {
        LOG_WARN("failed to end nested session", K(end_ret));
        if (OB_SUCCESS == ret) {
          ret = end_ret;
        }
      }
    }
  }
  return ret;
}

int ForeignKeyHandle::set_null(ObTableModifyOp &op,
                              const ObForeignKeyArg &fk_arg,
                              const ObExprPtrIArray &old_row)
{
  int ret = OB_SUCCESS;
  
  ObArenaAllocator alloc(ObModIds::OB_MODULE_PAGE_ALLOCATOR,
                          OB_MALLOC_NORMAL_BLOCK_SIZE);
  char *stmt_buf = nullptr;
  int64_t stmt_len = 0;
  char *where_buf = nullptr;
  int64_t where_len = 0;
  int64_t stmt_pos = 0;
  int64_t where_pos = 0;
  const ObString &database_name = fk_arg.database_name_;
  const ObString &table_name = fk_arg.table_name_;
  if (old_row.empty()) {
    ret = OB_INVALID_ARGUMENT;
  } else if (OB_FAIL(gen_where(op.get_eval_ctx(), where_buf, where_len, where_pos,
                               fk_arg.columns_, old_row, alloc, op.get_obj_print_params()))) {
    if (OB_LIKELY(OB_ERR_NULL_VALUE == ret)) {
      // skip cascade if any column in foreign key is NULL.
      ret = OB_SUCCESS;
      stmt_pos = 0;
    } else {
    }
  } else {
    const char *update_fmt = "update `%.*s`.`%.*s` set %.*s where %.*s";
    char *set_buf = nullptr;
    int64_t set_len = 0;
    int64_t set_pos = 0;
    if (OB_FAIL(gen_column_null_value(op.get_eval_ctx(), set_buf, set_len, set_pos, fk_arg.columns_, alloc, op.get_obj_print_params()))) {
    } else if (OB_FAIL(databuff_printf(stmt_buf, stmt_len, stmt_pos, alloc, update_fmt,
                                      database_name.length(), database_name.ptr(),
                                        table_name.length(), table_name.ptr(),
                                        static_cast<int>(set_pos), set_buf,
                                        static_cast<int>(where_pos), where_buf))) {
    } else {
      stmt_buf[stmt_pos++] = 0;
    }
  }
  
  if (OB_SUCC(ret) && stmt_pos > 0) {
    if (OB_FAIL(op.begin_nested_session(fk_arg.is_self_ref_))) {
    } else {
      if (OB_FAIL(op.execute_write(stmt_buf))) {
      }
      int end_ret = op.end_nested_session();
      if (OB_SUCCESS != end_ret) {
        LOG_WARN("failed to end nested session", K(end_ret));
        if (OB_SUCCESS == ret) {
          ret = end_ret;
        }
      }
    }
  }

  return ret;
}

int ForeignKeyHandle::gen_set(ObEvalCtx &eval_ctx, char *&buf, int64_t &len, int64_t &pos,
                              const ObIArray<ObForeignKeyColumn> &columns,
                              const ObExprPtrIArray &row,
                              ObIAllocator &alloc,
                              const ObObjPrintParams &print_params)
{
  return gen_column_value(eval_ctx, buf, len, pos, columns, row, ", ", alloc, print_params, false);
}

int ForeignKeyHandle::gen_where(ObEvalCtx &eval_ctx, char *&buf, int64_t &len, int64_t &pos,
                                const ObIArray<ObForeignKeyColumn> &columns,
                                const ObExprPtrIArray &row,
                                ObIAllocator &alloc,
                                const ObObjPrintParams &print_params)
{
  return gen_column_value(eval_ctx, buf, len, pos, columns, row, " and ", alloc, print_params, true);
}

int ForeignKeyHandle::gen_column_value(ObEvalCtx &eval_ctx, char *&buf, int64_t &len, int64_t &pos,
                                       const ObIArray<ObForeignKeyColumn> &columns,
                                       const ObExprPtrIArray &row,
                                       const char *delimiter,
                                       ObIAllocator &alloc,
                                       const ObObjPrintParams &print_params,
                                       bool forbid_null)
{
  const char *column_fmt = "`%.*s` = ";
  int ret = OB_SUCCESS;
  ObDatum *col_datum = NULL;
  if (OB_ISNULL(delimiter) || OB_ISNULL(print_params.tz_info_)) {
    ret = OB_INVALID_ARGUMENT;
  } else if (columns.count() <= 0) {
    ret= OB_ERR_UNEXPECTED;
    LOG_ERROR("columns count of fk is zero or less than zero", K(ret), K(columns.count()), K(columns));
  }
  for (int64_t i = 0; OB_SUCC(ret) && i < columns.count(); i++) {
    OZ(row.at(columns.at(i).idx_)->eval(eval_ctx, col_datum));
    if (OB_SUCC(ret)) {
      const ObString &col_name = columns.at(i).name_;
      const ObObjMeta &col_obj_meta = row.at(columns.at(i).idx_)->obj_meta_;
      ObObj col_obj;
      if (forbid_null && col_datum->is_null()) {
        ret = OB_ERR_NULL_VALUE;
        // NO LOG.
      } else if (OB_FAIL(databuff_printf(buf, len, pos, alloc, column_fmt,
                                        col_name.length(), col_name.ptr()))) {
      } else if (OB_FAIL(col_datum->to_obj(col_obj, col_obj_meta))) {
      } else if (OB_FAIL(col_obj.print_sql_literal(buf, len, pos, alloc, print_params))) {
      } else if (OB_FAIL(databuff_printf(buf, len, pos, alloc, "%s", delimiter))) {
      }
    }
  }
  if (OB_SUCC(ret)) {
    pos -= STRLEN(delimiter);
    buf[pos++] = 0;
  }
  return ret;
}

int  ForeignKeyHandle::gen_column_null_value(ObEvalCtx &ctx, char *&buf, int64_t &len, int64_t &pos,
                              const common::ObIArray<ObForeignKeyColumn> &columns,
                              common::ObIAllocator &alloc,
                              const common::ObObjPrintParams &print_params)
{
  int ret = OB_SUCCESS;
  const char *column_fmt = "`%.*s` = ";
  const char *delimiter = ", ";
  if (OB_ISNULL(delimiter) || OB_ISNULL(print_params.tz_info_)) {
    ret = OB_INVALID_ARGUMENT;
  } else if (columns.count() <= 0) {
    ret= OB_ERR_UNEXPECTED;
    LOG_ERROR("columns count of fk is zero or less than zero", K(ret), K(columns.count()), K(columns));
  }
  ObObj col_obj;
  col_obj.set_null();
  for (int64_t i = 0; OB_SUCC(ret) && i < columns.count(); i++) {
    if (OB_SUCC(ret)) {
      const ObString &col_name = columns.at(i).name_;
      if (OB_FAIL(databuff_printf(buf, len, pos, alloc, column_fmt,
                                        col_name.length(), col_name.ptr()))) {
      } else if (OB_FAIL(col_obj.print_sql_literal(buf, len, pos, alloc, print_params))) {
      } else if (OB_FAIL(databuff_printf(buf, len, pos, alloc, "%s", delimiter))) {
      }
    }
  }
  if (OB_SUCC(ret)) {
    pos -= STRLEN(delimiter);
    buf[pos++] = 0;
  }
  return ret;
}

int ForeignKeyHandle::is_self_ref_row(ObEvalCtx &eval_ctx,
                                      const ObExprPtrIArray &row,
                                      const ObForeignKeyArg &fk_arg,
                                      bool &is_self_ref)
{
  int ret = OB_SUCCESS;
  const common::ObDatumAccessContext *access_ctx = nullptr;
  is_self_ref = fk_arg.is_self_ref_;
  ObDatum *name_col = NULL;
  ObDatum *val_col = NULL;
  if (OB_FAIL(eval_ctx.get_datum_access_ctx(access_ctx))) {
  }
  for (int64_t i = 0; OB_SUCC(ret) && is_self_ref && i < fk_arg.columns_.count(); i++) {
    const int32_t name_idx = fk_arg.columns_.at(i).name_idx_;
    const int32_t val_idx = fk_arg.columns_.at(i).idx_;
    ObExprCmpFuncType cmp_func = row.at(name_idx)->basic_funcs_->null_first_cmp_;
    // TODO qubin.qb: uncomment below block revert the defensive check
    //OZ((cmp_func = (row.at(name_idx)->basic_funcs_->null_first_cmp_))
    //   != row.at(val_idx)->basic_funcs_->null_first_cmp_);
    OZ(row.at(name_idx)->eval(eval_ctx, name_col));
    OZ(row.at(val_idx)->eval(eval_ctx, val_col));
    int cmp_ret = 0;
    if (OB_FAIL(cmp_func(*name_col, *val_col, cmp_ret, access_ctx))) {
    } else {
      is_self_ref = (0 == cmp_ret);
    }
  }
  return ret;
}

// make MY_SPEC macro available.
OB_INLINE static const ObTableModifySpec &get_my_spec(const ObTableModifyOp &op)
{
  return op.get_spec();
}

ObTableModifySpec::ObTableModifySpec(common::ObIAllocator &alloc,
                                     const ObPhyOperatorType type)
  : ObOpSpec(alloc, type),
    expr_frame_info_(NULL),
    ab_stmt_id_(nullptr),
    flags_(0),
    das_dop_(0)
{
}

OB_DEF_SERIALIZE(ObTableModifySpec)
{
  int ret = OB_SUCCESS;
  BASE_SER((ObTableModifySpec, ObOpSpec));
  OB_UNIS_ENCODE(flags_);
  OB_UNIS_ENCODE(ab_stmt_id_);
  OB_UNIS_ENCODE(das_dop_);
  return ret;
}

OB_DEF_DESERIALIZE(ObTableModifySpec)
{
  int ret = OB_SUCCESS;
  BASE_DESER((ObTableModifySpec, ObOpSpec));
  OB_UNIS_DECODE(flags_);
  OB_UNIS_DECODE(ab_stmt_id_);
  OB_UNIS_DECODE(das_dop_);
  return ret;
}

OB_DEF_SERIALIZE_SIZE(ObTableModifySpec)
{
  int64_t len = 0;
  BASE_ADD_LEN((ObTableModifySpec, ObOpSpec));
  OB_UNIS_ADD_LEN(flags_);
  OB_UNIS_ADD_LEN(ab_stmt_id_);
  OB_UNIS_ADD_LEN(das_dop_);
  return len;
}

OB_SERIALIZE_MEMBER(ObTableModifyOpInput);

ObTableModifyOp::ObTableModifyOp(ObExecContext &ctx,
                                 const ObOpSpec &spec,
                                 ObOpInput *input)
  : ObOperator(ctx, spec, input),
    sql_proxy_(NULL),
    inner_conn_guard_(),
    inner_conn_(NULL),
    saved_conn_(),
    need_foreign_key_check_(false),
    need_close_conn_(false),
    iter_end_(false),
    dml_rtctx_(eval_ctx_, ctx, *this),
    execute_single_row_(false),
    dml_modify_rows_(ctx.get_allocator()),
    last_store_row_(),
    saved_session_(NULL)
{
  obj_print_params_ = CREATE_OBJ_PRINT_PARAM(ctx_.get_my_session());
  obj_print_params_.need_cast_expr_ = true;
  // bugfix:
  // in NO_BACKSLASH_ESCAPES, obj_print_sql<ObVarcharType> won't escape.
  // We use skip_escape_ to indicate this case. It will finally be passed to ObHexEscapeSqlStr.
  GET_SQL_MODE_BIT(IS_NO_BACKSLASH_ESCAPES, ctx_.get_my_session()->get_sql_mode(), obj_print_params_.skip_escape_);
}

int ObTableModifyOp::inner_open()
{
  int ret = OB_SUCCESS;
  ObSQLSessionInfo *my_session = GET_MY_SESSION(ctx_);
  if (OB_FAIL(init_foreign_key_operation())) {
  } else if (MY_SPEC.plan_->has_nested_sql() && OB_FAIL(open_inner_conn())) {
  } else if (OB_FAIL(calc_single_table_loc())) {
  } else if (OB_FAIL(check_need_exec_single_row())) {
  } else {
    init_das_dml_ctx();
  }
  return ret;
}

void ObTableModifyOp::clear_dml_evaluated_flag(ObExpr *clear_expr)
{
  if (clear_expr->is_batch_result()) {
    clear_expr->get_evaluated_flags(eval_ctx_).unset(eval_ctx_.get_batch_idx());
  } else {
    clear_expr->get_eval_info(eval_ctx_).clear_evaluated_flag();
  }
  if (0 < clear_expr->parent_cnt_) {
    clear_dml_evaluated_flag(clear_expr->parent_cnt_, clear_expr->parents_);
  }
}

void ObTableModifyOp::clear_dml_evaluated_flag(int64_t parent_cnt, ObExpr **parent_exprs)
{
  for (int64_t i = 0; i < parent_cnt; ++i) {
    clear_dml_evaluated_flag(parent_exprs[i]);
  }
}

void ObTableModifyOp::clear_dml_evaluated_flag()
{
  // Clear the parent expr because the assignment expr may be changed
  for (int64_t i = 0; i < trigger_clear_exprs_.count(); ++i) {
    ObExpr *expr = trigger_clear_exprs_.at(i);
    clear_dml_evaluated_flag(expr);
  }
}

ObDasParallelType ObTableModifyOp::check_das_parallel_type()
{
  ObDasParallelType type = DAS_SERIALIZATION;
  // Local DAS modification runs serially.
  return type;
}

OB_INLINE int ObTableModifyOp::init_das_dml_ctx()
{
  ObSQLSessionInfo *session = GET_MY_SESSION(ctx_);
  const char *label = nullptr;
  switch(MY_SPEC.type_) {
  case PHY_INSERT:
    label = "InsDASCtx";
    break;
  case PHY_UPDATE:
    label = "UpdDASCtx";
    break;
  case PHY_DELETE:
    label = "DelDASCtx";
    break;
  case PHY_LOCK:
    label = "LockDASCtx";
    break;
  default:
    label = "DmlDASCtx";
    break;
  }
  ObMemAttr memattr(label, ObCtxIds::EXECUTE_CTX_ID);
  dml_rtctx_.das_ref_.set_expr_frame_info(nullptr != MY_SPEC.expr_frame_info_
                                        ? MY_SPEC.expr_frame_info_
                                        : &MY_SPEC.plan_->get_expr_frame_info());
  dml_rtctx_.das_ref_.set_mem_attr(memattr);
  dml_rtctx_.das_ref_.get_das_parallel_ctx().set_das_parallel_type(check_das_parallel_type());
  dml_rtctx_.das_ref_.get_das_parallel_ctx().set_das_dop(ctx_.get_das_ctx().get_real_das_dop());
  if (check_das_parallel_type() != DAS_SERIALIZATION) {
    LOG_TRACE("this sql use das parallel submit", K(check_das_parallel_type()));
  }
  return OB_SUCCESS;
}

int ObTableModifyOp::replace_implict_cursor(int64_t affected_rows,
                                            int64_t found_rows,
                                            int64_t matched_rows,
                                            int64_t duplicated_rows)
{
  int ret = OB_SUCCESS;
  bool is_ins_val_opt = ctx_.get_sql_ctx()->is_do_insert_batch_opt();
  ObPhysicalPlanCtx *plan_ctx = GET_PHY_PLAN_CTX(ctx_);
  if (MY_SPEC.ab_stmt_id_ != nullptr && !is_ins_val_opt) {
    ObDatum *stmt_id_datum = nullptr;
    ObImplicitCursorInfo implicit_cursor;
    if (OB_FAIL(prepare_implict_cursor(affected_rows,
                                       found_rows,
                                       matched_rows,
                                       duplicated_rows,
                                       implicit_cursor))) {
    } else if (OB_FAIL(plan_ctx->replace_implicit_cursor_info(implicit_cursor))) {
    }
  }
  return ret;
}

int ObTableModifyOp::prepare_implict_cursor(int64_t affected_rows,
                                            int64_t found_rows,
                                            int64_t matched_rows,
                                            int64_t duplicated_rows,
                                            ObImplicitCursorInfo &implicit_cursor)
{
  int ret = OB_SUCCESS;
  ObDatum *stmt_id_datum = nullptr;
  if (OB_FAIL(MY_SPEC.ab_stmt_id_->eval(eval_ctx_, stmt_id_datum))) {
  } else {
    ObPhysicalPlanCtx *plan_ctx = GET_PHY_PLAN_CTX(ctx_);
    int64_t stmt_id = stmt_id_datum->get_int();
    implicit_cursor.stmt_id_ = stmt_id;
    implicit_cursor.found_rows_ += found_rows;
    implicit_cursor.matched_rows_ += matched_rows;
    implicit_cursor.affected_rows_ += affected_rows;
    implicit_cursor.duplicated_rows_ += duplicated_rows;
    implicit_cursor.last_insert_id_ = plan_ctx->get_autoinc_col_value();
  }
  return ret;
}

int ObTableModifyOp::merge_implict_cursor(int64_t affected_rows,
                                          int64_t found_rows,
                                          int64_t matched_rows,
                                          int64_t duplicated_rows)
{
  int ret = OB_SUCCESS;
  bool is_ins_val_opt = ctx_.get_sql_ctx()->is_do_insert_batch_opt();
  ObPhysicalPlanCtx *plan_ctx = GET_PHY_PLAN_CTX(ctx_);
  if (MY_SPEC.ab_stmt_id_ != nullptr && !is_ins_val_opt) {
    ObDatum *stmt_id_datum = nullptr;
    ObImplicitCursorInfo implicit_cursor;
    if (OB_FAIL(prepare_implict_cursor(affected_rows,
                                       found_rows,
                                       matched_rows,
                                       duplicated_rows,
                                       implicit_cursor))) {
    } else if (OB_FAIL(plan_ctx->merge_implicit_cursor_info(implicit_cursor))) {
    }
  }
  return ret;
}

int ObTableModifyOp::inner_switch_iterator()
{
  int ret = OB_SUCCESS;
  if (OB_FAIL(ObOperator::inner_switch_iterator())) {
  }

  return ret;
}

int ObTableModifyOp::inner_close()
{
  int ret = OB_SUCCESS;
  ObPhysicalPlanCtx *plan_ctx = ctx_.get_physical_plan_ctx();
  // release cache_handle for auto-increment
  share::ObAutoincrementService &auto_service = share::ObAutoincrementService::get_instance();
  ObIArray<share::AutoincParam> &autoinc_params = plan_ctx->get_autoinc_params();
  for (int64_t i = 0; i < autoinc_params.count(); ++i) {
    if (NULL != autoinc_params.at(i).cache_handle_) {
      auto_service.release_handle(autoinc_params.at(i).cache_handle_);
    }
  }
  close_inner_conn();
  if (dml_rtctx_.das_ref_.has_task()) {
    if (OB_FAIL(dml_rtctx_.das_ref_.close_all_task())) {
    } else {
      dml_rtctx_.das_ref_.reset();
    }
  }
  dml_modify_rows_.clear();
  return ret;
}

OB_INLINE int ObTableModifyOp::init_foreign_key_operation()
{
  int ret = OB_SUCCESS;
  ObPhysicalPlanCtx *phy_plan_ctx = GET_PHY_PLAN_CTX(ctx_);
  if (OB_ISNULL(phy_plan_ctx)) {
    ret = OB_ERR_UNEXPECTED;
  } else if (!phy_plan_ctx->need_foreign_key_checks()) {
    // set fk check even if ret != OB_SUCCESS. see ObTableModifyOp::inner_close()
    need_foreign_key_check_ = false;
  } else {
    need_foreign_key_check_ = MY_SPEC.need_foreign_key_check_;
  }
  return ret;
}

int ObTableModifyOp::inner_rescan()
{
  int ret = OB_SUCCESS;
  if (OB_FAIL(ObOperator::inner_rescan())) {
  } else {
    iter_end_ = false;
    if (dml_rtctx_.das_ref_.has_task()) {
      if (OB_FAIL(dml_rtctx_.das_ref_.close_all_task())) {
      } else {
        dml_rtctx_.reuse();
      }
    }
  }
  if (OB_SUCC(ret)) {
    dml_modify_rows_.clear();
    if (OB_FAIL(calc_single_table_loc())) {
    }
  }
  return ret;
}

int ObTableModifyOp::check_need_exec_single_row() {
  int ret = OB_SUCCESS;
  if (MY_SPEC.is_returning_ && (need_foreign_key_checks() || MY_SPEC.need_trigger_fire_)) {
    execute_single_row_ = true;
  }
  return ret;
}

int ObTableModifyOp::get_gi_task()
{
  int ret = OB_SUCCESS;
  ObGranuleTaskInfo gi_task_info;
  GIPrepareTaskMap *gi_prepare_map = nullptr;
  ObDASCtx &das_ctx = ctx_.get_das_ctx();
  ObTableID table_loc_id = OB_INVALID_ID;
  ObTableID ref_table_id = OB_INVALID_ID;
  ObTabletID tablet_id;
  if (OB_FAIL(MY_SPEC.get_single_table_loc_id(table_loc_id, ref_table_id))) {
  } else if (OB_FAIL(ctx_.get_gi_task_map(gi_prepare_map))) {
  } else if (OB_FAIL(gi_prepare_map->get_refactored(MY_SPEC.id_, gi_task_info))) {
    if (ret != OB_HASH_NOT_EXIST) {
    } else {
      LOG_DEBUG("no prepared task info, set table modify to end",
        K(MY_SPEC.get_id()), K(this), K(lbt()));
      // Current DML operator cannot obtain task from GI, indicating current DML operator iter end
      iter_end_ = true;
      ret = OB_SUCCESS;
    }
  } else if (OB_ISNULL(get_input()->table_loc_) &&
      OB_ISNULL(get_input()->table_loc_ = das_ctx.get_table_loc_by_id(table_loc_id, ref_table_id))) {
    ret = OB_ERR_UNEXPECTED;
  } else {
    get_input()->tablet_loc_ = gi_task_info.tablet_loc_;
    LOG_DEBUG("DML operator consume a task", K(ret),
              K(gi_task_info), KPC(get_input()), K(MY_SPEC.id_), K(get_input()));
  }
  return ret;
}

int ObTableModifyOp::calc_single_table_loc()
{
  int ret = OB_SUCCESS;
  if (!MY_SPEC.use_dist_das_) {
    ObTableID table_loc_id = OB_INVALID_ID;
    ObTableID ref_table_id = OB_INVALID_ID;
    ObDASCtx &das_ctx = ctx_.get_das_ctx();
    ObDASTableLoc *table_loc = nullptr;
    if (OB_UNLIKELY(MY_SPEC.gi_above_)) {
      if (OB_FAIL(get_gi_task())) {
      }
    } else if (OB_FAIL(MY_SPEC.get_single_table_loc_id(table_loc_id, ref_table_id))) {
    } else if (OB_ISNULL(table_loc = das_ctx.get_table_loc_by_id(table_loc_id, ref_table_id))) {
      ret = OB_ERR_UNEXPECTED;
    } else {
      get_input()->table_loc_ = table_loc;
      get_input()->tablet_loc_ = table_loc->get_first_tablet_loc();
    }
  }
  return ret;
}

int ObTableModifyOp::open_inner_conn()
{
  int ret = OB_SUCCESS;
  ObSQLSessionInfo *session = NULL;
  if (OB_ISNULL(sql_proxy_ = ctx_.get_sql_proxy())) {
    ret = OB_NOT_INIT;
  } else if (OB_ISNULL(session = ctx_.get_my_session())) {
    ret = OB_NOT_INIT;
  } else if (NULL != session->get_inner_conn()) {
    // do nothing.
  } else if (OB_FAIL(
                 query::ObInnerSQLConnectionAccess::
                     create_connection_with_external_session(
                         session, inner_conn_guard_))) {
  } else if (OB_ISNULL(inner_conn_guard_.get_ptr())) {
    ret = OB_ERR_UNEXPECTED;
  } else {
    /**
     * session is the only data struct which can pass through multi layer nested sql,
     * so we put inner conn in session to share it within multi layer nested sql.
     */
    session->set_inner_conn(inner_conn_guard_.get_ptr());
    need_close_conn_ = true;
  }
  if (OB_SUCC(ret)) {
    inner_conn_ = as_inner_sql_connection(session->get_inner_conn());
    if (OB_ISNULL(inner_conn_)) {
      ret = OB_ERR_UNEXPECTED;
    }
  }
  return ret;
}

int ObTableModifyOp::close_inner_conn()
{
  /**
   * we can call it even if open_inner_conn() failed, because only the one who call
   * open_inner_conn() succeed first will do close job by "if (need_close_conn_)".
   */
  int ret = OB_SUCCESS;
  if (need_close_conn_) {
    ObSQLSessionInfo *session = ctx_.get_my_session();
    if (OB_ISNULL(sql_proxy_) || OB_ISNULL(session)) {
      ret = OB_INVALID_ARGUMENT;
    } else {
      OX(session->set_inner_conn(NULL));
      OX(inner_conn_guard_.reset());
    }
    need_close_conn_ = false;
  }
  sql_proxy_ = NULL;
  inner_conn_guard_.reset();
  inner_conn_ = NULL;
  return ret;
}

int ObTableModifyOp::begin_nested_session(bool skip_cur_stmt_tables)
{
  int ret = OB_SUCCESS;
  if (OB_ISNULL(inner_conn_)) {
    ret = OB_NOT_INIT;
  } else if (OB_FAIL(inner_conn_->begin_nested_session(get_saved_session(), saved_conn_,
                                                       skip_cur_stmt_tables))) {
  }
  return ret;
}

int ObTableModifyOp::end_nested_session()
{
  int ret = OB_SUCCESS;
  if (OB_ISNULL(inner_conn_)) {
    ret = OB_NOT_INIT;
  } else if (OB_FAIL(inner_conn_->end_nested_session(get_saved_session(), saved_conn_))) {
  }
  return ret;
}
int ObTableModifyOp::execute_write(const char *sql)
{
  int ret = OB_SUCCESS;
  int64_t affected_rows = 0;
  if (OB_ISNULL(inner_conn_)) {
    ret = OB_NOT_INIT;
  } else if (OB_ISNULL(sql)) {
    ret = OB_ERR_UNEXPECTED;
  } else if (OB_FAIL(inner_conn_->execute_write(sql, affected_rows))) {
  }
  return ret;
}

int ObTableModifyOp::execute_read(const char *sql, ObMySQLProxy::MySQLResult &res)
{
  int ret = OB_SUCCESS;
  if (OB_ISNULL(inner_conn_) || OB_ISNULL(sql_proxy_)) {
    ret = OB_NOT_INIT;
  } else if (OB_ISNULL(sql)) {
    ret = OB_ERR_UNEXPECTED;
  } else if (OB_FAIL(inner_conn_->execute_read(sql, res))) {
  }
 return ret;
}

int ObTableModifyOp::check_stack()
{
  int ret = OB_SUCCESS;
  const int max_stack_deep = 16;
  bool is_stack_overflow = false;
  ObSQLSessionInfo *session = ctx_.get_my_session();
  if (OB_ISNULL(session)) {
    ret = OB_ERR_NULL_VALUE;
  } else if (session->get_nested_count() > max_stack_deep) {
    ret = OB_SIZE_OVERFLOW;
  } else if (OB_FAIL(check_stack_overflow(is_stack_overflow))) {
  } else if (is_stack_overflow) {
    ret = OB_SIZE_OVERFLOW;
  }
  return ret;
}
OperatorOpenOrder ObTableModifyOp::get_operator_open_order() const
{
  OperatorOpenOrder open_order = OPEN_CHILDREN_FIRST;
  if (spec_.plan_->is_use_px()) {
    // If PX is enabled in DML, there are two scenarios:
    // 1. PDML: in pdml, pdml-op completely does not need its corresponding input to provide runtime parameters, so it will directly return
    // open_order = OPEN_CHILDREN_FIRST
    // 2. DML+PX: In this case, the parameters of the dml run are completely fed by the GI operator above it, for example, such a plan:
    //   PX COORD
    //    PX TRANSMIT
    //      GI (FULL PARTITION WISE)
    //       DELETE
    //        TSC
    //  Such a plan requires GI to drive the deletion, GI rescan delete each time a new Task is iterated,
    //  Pass the information of the corresponding Task to the delete operator.
    open_order = OPEN_CHILDREN_FIRST;
  }
  return open_order;
}

namespace ai_column_dml_util
{
thread_local bool g_ai_column_internal_write = false;

// Task rows created by a still running transaction are invisible to the dedicated
// metadata connection used by delete_task_rows(), so a DELETE/UPDATE issued in the
// same transaction as its INSERT could not clean them up. Remember the task ids a
// transaction wrote, keyed by (transaction id, table id, rowkey predicate), and
// consume them from the delete path.
struct AITaskCacheKey
{
  int64_t tx_id_;
  uint64_t table_id_;
  std::string predicate_;
  bool operator==(const AITaskCacheKey &other) const
  {
    return tx_id_ == other.tx_id_ && table_id_ == other.table_id_
           && predicate_ == other.predicate_;
  }
};

struct AITaskCacheKeyHash
{
  size_t operator()(const AITaskCacheKey &key) const
  {
    size_t h = std::hash<std::string>()(key.predicate_);
    h ^= static_cast<size_t>(key.table_id_) + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    h ^= static_cast<size_t>(key.tx_id_) + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    return h;
  }
};

std::mutex g_tx_task_cache_lock;
std::unordered_map<AITaskCacheKey, std::vector<int64_t>, AITaskCacheKeyHash> g_tx_task_cache;

void remember_tx_task_id(const int64_t tx_id,
                         const uint64_t table_id,
                         const common::ObString &predicate,
                         const int64_t task_id)
{
  if (tx_id > 0 && NULL != predicate.ptr() && predicate.length() > 0) {
    AITaskCacheKey key;
    key.tx_id_ = tx_id;
    key.table_id_ = table_id;
    key.predicate_.assign(predicate.ptr(), static_cast<size_t>(predicate.length()));
    std::lock_guard<std::mutex> guard(g_tx_task_cache_lock);
    // The map is only a same-transaction accelerator; bound the memory even if a
    // transaction never consumed its entries (e.g. committed insert-only work).
    if (g_tx_task_cache.size() > 8192) {
      g_tx_task_cache.clear();
    }
    g_tx_task_cache[key].push_back(task_id);
  }
}

bool take_tx_task_ids(const int64_t tx_id,
                      const uint64_t table_id,
                      const common::ObString &predicate,
                      common::ObIArray<int64_t> &task_ids)
{
  bool found = false;
  if (tx_id > 0 && NULL != predicate.ptr() && predicate.length() > 0) {
    AITaskCacheKey key;
    key.tx_id_ = tx_id;
    key.table_id_ = table_id;
    key.predicate_.assign(predicate.ptr(), static_cast<size_t>(predicate.length()));
    std::lock_guard<std::mutex> guard(g_tx_task_cache_lock);
    auto it = g_tx_task_cache.find(key);
    if (it != g_tx_task_cache.end()) {
      for (size_t i = 0; i < it->second.size(); ++i) {
        if (OB_SUCCESS != task_ids.push_back(it->second[i])) {
          break;
        }
      }
      g_tx_task_cache.erase(it);
      found = !task_ids.empty();
    }
  }
  return found;
}

struct AIColumnInfo
{
  AIColumnInfo() : column_id_(0), max_retries_(0) {}
  int64_t column_id_;
  int64_t max_retries_;
  common::ObString normalized_expr_; // in statement allocator
  common::ObString deps_;            // in statement allocator
};

int append_sql_quoted(common::ObSqlString &sql, const common::ObString &value)
{
  int ret = OB_SUCCESS;
  if (OB_FAIL(sql.append("'"))) {
  }
  for (int64_t i = 0; OB_SUCC(ret) && i < value.length(); ++i) {
    if ('\'' == value.ptr()[i]) {
      if (OB_FAIL(sql.append("''"))) {
      }
    } else if (OB_FAIL(sql.append_fmt("%c", value.ptr()[i]))) {
    }
  }
  if (OB_SUCC(ret) && OB_FAIL(sql.append("'"))) {
  }
  return ret;
}

// A normalized expr may carry deps as the suffix " [AI_DEPS]col1,col2"
void split_deps(common::ObString &normalized_expr, common::ObString &deps)
{
  deps.reset();
  static const char marker[] = " [AI_DEPS]";
  const int64_t marker_len = static_cast<int64_t>(sizeof(marker) - 1);
  if (normalized_expr.length() > marker_len) {
    for (int64_t i = normalized_expr.length() - marker_len; i >= 0; --i) {
      if (0 == MEMCMP(normalized_expr.ptr() + i, marker, marker_len)) {
        deps.assign_ptr(normalized_expr.ptr() + i + marker_len,
                        static_cast<int32_t>(normalized_expr.length() - i - marker_len));
        normalized_expr.assign_ptr(normalized_expr.ptr(), static_cast<int32_t>(i));
        break;
      }
    }
  }
}

int append_rowkey_predicate(const share::schema::ObTableSchema &table,
                            const ObDMLBaseCtDef &ctdef,
                            const ObChunkDatumStore::StoredRow &row,
                            common::ObSqlString &sql)
{
  int ret = OB_SUCCESS;
  common::ObSEArray<const share::schema::ObColumnSchemaV2 *, 4> pk_columns;
  for (share::schema::ObTableSchema::const_column_iterator it = table.column_begin();
       OB_SUCC(ret) && it != table.column_end(); ++it) {
    const share::schema::ObColumnSchemaV2 *col = *it;
    if (OB_ISNULL(col)) {
      ret = OB_ERR_UNEXPECTED;
    } else if (col->is_rowkey_column() && OB_FAIL(pk_columns.push_back(col))) {
    }
  }
  for (int64_t i = 0; OB_SUCC(ret) && i < pk_columns.count(); ++i) {
    for (int64_t j = i + 1; OB_SUCC(ret) && j < pk_columns.count(); ++j) {
      if (pk_columns.at(j)->get_rowkey_position() < pk_columns.at(i)->get_rowkey_position()) {
        const share::schema::ObColumnSchemaV2 *tmp = pk_columns.at(i);
        pk_columns.at(i) = pk_columns.at(j);
        pk_columns.at(j) = tmp;
      }
    }
  }
  const int64_t pk_cnt = pk_columns.count();
  const int64_t row_cnt = row.cnt_;
  const int64_t ctdef_col_cnt = ctdef.column_ids_.count();
  if (OB_SUCC(ret) && (0 == pk_cnt || row_cnt < ctdef_col_cnt)) {
    ret = OB_ERR_UNEXPECTED;
    LOG_WARN("invalid ai column dml row", K(ret), K(pk_cnt), K(row_cnt), K(ctdef_col_cnt));
  }
  for (int64_t i = 0; OB_SUCC(ret) && i < pk_columns.count(); ++i) {
    const share::schema::ObColumnSchemaV2 *col = pk_columns.at(i);
    int64_t idx = -1;
    for (int64_t j = 0; -1 == idx && j < ctdef.column_ids_.count(); ++j) {
      if (ctdef.column_ids_.at(j) == col->get_column_id()) {
        idx = j;
      }
    }
    if (OB_UNLIKELY(idx < 0 || idx >= row.cnt_)) {
      ret = OB_ERR_UNEXPECTED;
      LOG_WARN("ai column rowkey not found in dml row", K(ret), KPC(col));
    } else {
      const common::ObDatum &datum = row.cells()[idx];
      const common::ObString col_name = col->get_column_name_str();
      if (i > 0 && OB_FAIL(sql.append(" AND "))) {
      } else if (datum.is_null()) {
        if (OB_FAIL(sql.append_fmt("`%.*s` IS NULL",
                                   static_cast<int>(col_name.length()), col_name.ptr()))) {
        }
      } else if (ob_is_integer_type(col->get_data_type())) {
        if (OB_FAIL(sql.append_fmt("`%.*s` = %ld",
                                   static_cast<int>(col_name.length()), col_name.ptr(),
                                   datum.get_int()))) {
        }
      } else if (ob_is_string_tc(col->get_data_type())) {
        common::ObString value(static_cast<int32_t>(datum.len_),
                               const_cast<char *>(datum.ptr_));
        if (OB_FAIL(sql.append_fmt("`%.*s` = ",
                                   static_cast<int>(col_name.length()), col_name.ptr()))) {
        } else if (OB_FAIL(append_sql_quoted(sql, value))) {
        }
      } else {
        ret = OB_NOT_SUPPORTED;
        LOG_WARN("unsupported ai column rowkey type", K(ret), K(col->get_data_type()));
      }
    }
  }
  return ret;
}

bool table_has_ai_column(const share::schema::ObTableSchema &table)
{
  bool found = false;
  for (share::schema::ObTableSchema::const_column_iterator it = table.column_begin();
       !found && it != table.column_end(); ++it) {
    found = (NULL != *it) && (*it)->is_ai_column();
  }
  return found;
}

} // namespace ai_column_dml_util

bool ObTableModifyOp::dml_table_has_ai_column(const ObDMLBaseCtDef &dml_ctdef)
{
  bool found = false;
  if (dml_ctdef.is_primary_index_) {
    const uint64_t table_id =
        dml_ctdef.das_base_ctdef_.table_param_.get_data_table().get_table_id();
    if (table_id < common::OB_MIN_USER_OBJECT_ID) {
      // inner tables never have AI columns; keep this path cheap
    } else {
      share::schema::ObSchemaGetterGuard *schema_guard =
          (NULL != ctx_.get_sql_ctx()) ? ctx_.get_sql_ctx()->schema_guard_ : NULL;
      const share::schema::ObTableSchema *table = NULL;
      if (NULL != schema_guard
          && OB_SUCCESS == schema_guard->get_table_schema(table_id, table)
          && NULL != table) {
        found = ai_column_dml_util::table_has_ai_column(*table);
      }
    }
  }
  return found;
}

int ObTableModifyOp::handle_ai_column_row_processing()
{
  int ret = OB_SUCCESS;
  using namespace ai_column_dml_util;
  share::schema::ObSchemaGetterGuard *schema_guard =
      (NULL != ctx_.get_sql_ctx()) ? ctx_.get_sql_ctx()->schema_guard_ : NULL;
  if (g_ai_column_internal_write || dml_modify_rows_.empty() || NULL == schema_guard) {
    LOG_INFO("ai column row processing skipped", K(g_ai_column_internal_write),
             K(dml_modify_rows_.size()), KP(schema_guard));
  } else {
    LOG_INFO("ai column row processing start");
    common::ObArenaAllocator tmp_allocator("AIColumnDml");
    static std::atomic<int64_t> task_seq(0);
    int64_t grand_task_cnt = 0;

    // Build AI column descriptors from the table schema. The descriptor of each
    // AI column is packed into the comment of its hidden state column, which
    // survives schema refresh (unlike the in-memory ai_column_meta_ attribute).
    auto load_ai_columns = [&](const share::schema::ObTableSchema &table,
                               common::ObIArray<AIColumnInfo> &infos) -> int {
      int lret = OB_SUCCESS;
      const char deps_marker[] = " [AI_DEPS]";
      const char retry_marker[] = " [AI_MAX_RETRIES]";
      const int64_t deps_marker_len = static_cast<int64_t>(sizeof(deps_marker) - 1);
      const int64_t retry_marker_len = static_cast<int64_t>(sizeof(retry_marker) - 1);
      for (share::schema::ObTableSchema::const_column_iterator it = table.column_begin();
           OB_SUCC(lret) && it != table.column_end(); ++it) {
        const share::schema::ObColumnSchemaV2 *col = *it;
        if (NULL == col || !col->is_ai_column()) {
          continue;
        }
        char name_buf[OB_MAX_COLUMN_NAME_LENGTH + 32];
        int64_t name_pos = 0;
        if (OB_SUCCESS != (lret = databuff_printf(name_buf, sizeof(name_buf), name_pos,
                                                  "%.*s__ai_state",
                                                  static_cast<int>(col->get_column_name_str().length()),
                                                  col->get_column_name_str().ptr()))) {
        } else {
          const share::schema::ObColumnSchemaV2 *hidden_col =
              table.get_column_schema(common::ObString(static_cast<int32_t>(name_pos), name_buf));
          if (NULL == hidden_col) {
            lret = OB_ERR_UNEXPECTED;
            LOG_WARN("ai hidden state column not found", K(lret),
                     K(col->get_column_name_str()));
          } else {
            const common::ObString packed = hidden_col->get_comment_str();
            int64_t deps_pos = -1;
            int64_t retry_pos = -1;
            for (int64_t i = 0; i + deps_marker_len <= packed.length(); ++i) {
              if (0 == MEMCMP(packed.ptr() + i, deps_marker, deps_marker_len)) {
                deps_pos = i;
                break;
              }
            }
            for (int64_t i = 0; i + retry_marker_len <= packed.length(); ++i) {
              if (0 == MEMCMP(packed.ptr() + i, retry_marker, retry_marker_len)) {
                retry_pos = i;
                break;
              }
            }
            AIColumnInfo info;
            info.column_id_ = col->get_column_id();
            info.max_retries_ = 0;
            int64_t expr_end = packed.length();
            if (deps_pos >= 0) {
              expr_end = deps_pos;
            } else if (retry_pos >= 0) {
              expr_end = retry_pos;
            }
            if (retry_pos >= 0 && retry_pos + retry_marker_len <= packed.length()) {
              int err = 0;
              info.max_retries_ = common::ObCharset::strntoll(
                  packed.ptr() + retry_pos + retry_marker_len,
                  static_cast<int32_t>(packed.length() - retry_pos - retry_marker_len),
                  10, &err);
            }
            if (expr_end > 0) {
              char *expr_buf = static_cast<char *>(tmp_allocator.alloc(expr_end));
              if (NULL == expr_buf) {
                lret = OB_ALLOCATE_MEMORY_FAILED;
              } else {
                MEMCPY(expr_buf, packed.ptr(), expr_end);
                info.normalized_expr_.assign_ptr(expr_buf, static_cast<int32_t>(expr_end));
              }
            }
            if (OB_SUCC(lret) && deps_pos >= 0) {
              const int64_t deps_begin = deps_pos + deps_marker_len;
              const int64_t deps_end = retry_pos >= 0 ? retry_pos : packed.length();
              if (deps_end > deps_begin) {
                const int64_t deps_len = deps_end - deps_begin;
                char *deps_buf = static_cast<char *>(tmp_allocator.alloc(deps_len));
                if (NULL == deps_buf) {
                  lret = OB_ALLOCATE_MEMORY_FAILED;
                } else {
                  MEMCPY(deps_buf, packed.ptr() + deps_begin, deps_len);
                  info.deps_.assign_ptr(deps_buf, static_cast<int32_t>(deps_len));
                }
              }
            }
            if (OB_SUCC(lret) && OB_FAIL(infos.push_back(info))) {
              lret = ret;
            }
          }
        }
      }
      return lret;
    };

    struct TaskRowValue
    {
      int64_t task_id_;
      int64_t table_id_;
      int64_t column_id_;
      int64_t state_;
      int64_t retry_count_;
      int64_t eligible_ts_;
      common::ObString request_id_;
      common::ObString rowkey_predicate_;
      common::ObString group_id_;
    };

    auto get_task_table_store_column_ids = [&](const share::schema::ObTableSchema &task_table,
                                               common::ObIArray<uint64_t> &column_ids) -> int {
      int lret = OB_SUCCESS;
      common::ObSEArray<share::schema::ObColDesc, 32> store_cols;
      if (OB_FAIL(task_table.get_store_column_ids(store_cols, false))) {
        lret = ret;
      }
      for (int64_t i = 0; OB_SUCC(lret) && i < store_cols.count(); ++i) {
        if (OB_FAIL(column_ids.push_back(store_cols.at(i).col_id_))) {
          lret = ret;
        }
      }
      return lret;
    };

    class TaskRowIter : public blocksstable::ObDatumRowIterator
    {
    public:
      explicit TaskRowIter(common::ObIArray<blocksstable::ObDatumRow *> &rows)
        : rows_(rows), cur_(0) {}
      virtual ~TaskRowIter() {}
      int get_next_row(blocksstable::ObDatumRow *&row) override
      {
        int ret = OB_SUCCESS;
        if (cur_ >= rows_.count()) {
          ret = OB_ITER_END;
        } else {
          row = rows_.at(cur_++);
        }
        return ret;
      }
      void reset() override { cur_ = 0; }
    private:
      common::ObIArray<blocksstable::ObDatumRow *> &rows_;
      int64_t cur_;
    };

    // Insert task rows through the data-plane DML seam. The write joins the
    // caller transaction directly, so it never goes through the SQL layer and
    // therefore cannot disturb the outer statement's transaction state.
    // batch task insert through data-plane dml seam
    auto insert_task_rows = [&](const share::schema::ObTableSchema &task_table,
                                const common::ObIArray<TaskRowValue> &values) -> int {
      int lret = OB_SUCCESS;
      data_plane::ObIDmlService *dml_service =
          share::server_service<data_plane::ObIDmlService>();
      data_plane::ObIWriteContextService *wcs =
          share::server_service<data_plane::ObIWriteContextService>();
      data_plane::ObITransactionService *txs =
          data_plane::query_transaction_service();
      ObSQLSessionInfo *session = ctx_.get_my_session();
      transaction::ObTxDesc *tx_desc = (NULL == session) ? NULL : session->get_tx_desc();
      transaction::ObTxReadSnapshot snapshot;
      concurrent_control::ObWriteFlag write_flag;
      data_plane::ObWriteContext write_context;
      data_plane::ObDmlExecution execution;
      data_plane::ObDmlTablePlan table_plan(tmp_allocator);
      common::ObSEArray<uint64_t, 32> column_ids;
      int64_t tenant_schema_version = 0;
      const int64_t timeout_us = common::ObTimeUtility::current_time() + 10000000;
      LOG_INFO("ai col ins stage entry", K(values.count()), KP(tx_desc));
      if (OB_ISNULL(dml_service) || OB_ISNULL(wcs) || OB_ISNULL(txs)
          || OB_ISNULL(session) || OB_ISNULL(tx_desc)) {
        lret = OB_ERR_UNEXPECTED;
        LOG_WARN("ai column task insert env not ready", K(lret));
      } else if (OB_SUCCESS != (lret = get_task_table_store_column_ids(task_table, column_ids))) {
        LOG_INFO("ai col ins stage cols failed", K(lret));
      } else if (OB_SUCCESS != (lret = schema_guard->get_schema_version(tenant_schema_version))) {
        LOG_INFO("ai col ins stage schema ver failed", K(lret));
      } else if (OB_SUCCESS != (lret = txs->get_read_snapshot(
                     *tx_desc, transaction::ObTxIsolationLevel::RC,
                     timeout_us, snapshot))) {
        LOG_WARN("ai column task insert get snapshot failed", K(lret));
      } else if (OB_SUCCESS != (lret = table_plan.build(&task_table,
                                                        tenant_schema_version,
                                                        column_ids))) {
        LOG_INFO("ai col ins stage plan failed", K(lret));
      } else {
        data_plane::ObDmlWriteSpec write_spec;
        write_spec.timeout_ = timeout_us;
        write_spec.schema_version_ = tenant_schema_version;
        write_spec.sql_mode_ = session->get_sql_mode();
        write_spec.tz_info_ = session->get_timezone_info();
        write_spec.branch_id_ = 0;
        write_spec.check_schema_version_ = false;
        if (OB_SUCCESS != (lret = wcs->acquire_write_context(
                               timeout_us, *tx_desc, snapshot, 0,
                               write_flag, write_context))) {
          LOG_INFO("ai col ins stage acquire ctx failed", K(lret));
        } else if (OB_SUCCESS != (lret = dml_service->prepare_execution(
                      write_spec, table_plan, snapshot, tmp_allocator,
                      write_context, write_flag, execution))) {
          LOG_INFO("ai col ins stage prepare failed", K(lret));
        } else {
          common::ObSEArray<blocksstable::ObDatumRow *, 8> rows;
          const int64_t col_cnt = column_ids.count();
          for (int64_t r = 0; OB_SUCC(lret) && r < values.count(); ++r) {
            const TaskRowValue &v = values.at(r);
            blocksstable::ObDatumRow *row = static_cast<blocksstable::ObDatumRow *>(
                tmp_allocator.alloc(sizeof(blocksstable::ObDatumRow)));
            if (OB_ISNULL(row)) {
              lret = OB_ALLOCATE_MEMORY_FAILED;
            } else {
              new (row) blocksstable::ObDatumRow();
              if (OB_SUCCESS != (lret = row->init(col_cnt))) {
              } else {
                row->count_ = static_cast<uint16_t>(col_cnt);
                row->row_flag_.set_flag(blocksstable::DF_INSERT);
                for (int64_t c = 0; OB_SUCC(lret) && c < col_cnt; ++c) {
                  const share::schema::ObColumnSchemaV2 *col =
                      task_table.get_column_schema(column_ids.at(c));
                  if (OB_ISNULL(col)) {
                    lret = OB_ERR_UNEXPECTED;
                  } else {
                    const common::ObString name = col->get_column_name_str();
                    blocksstable::ObStorageDatum &datum = row->storage_datums_[c];
                    if (0 == name.case_compare("task_id")) {
                      datum.set_int(v.task_id_);
                    } else if (0 == name.case_compare("table_id")) {
                      datum.set_int(v.table_id_);
                    } else if (0 == name.case_compare("column_id")) {
                      datum.set_int(v.column_id_);
                    } else if (0 == name.case_compare("request_id")) {
                      datum.set_string(v.request_id_.ptr(), v.request_id_.length());
                    } else if (0 == name.case_compare("state")) {
                      datum.set_int(v.state_);
                    } else if (0 == name.case_compare("retry_count")) {
                      datum.set_int(v.retry_count_);
                    } else if (0 == name.case_compare("rowkey_predicate")) {
                      datum.set_string(v.rowkey_predicate_.ptr(),
                                       v.rowkey_predicate_.length());
                    } else if (0 == name.case_compare("eligible_ts")) {
                      datum.set_int(v.eligible_ts_);
                    } else if (0 == name.case_compare("group_id")) {
                      datum.set_string(v.group_id_.ptr(), v.group_id_.length());
                    } else if (0 == name.case_compare("attempt_ts")) {
                      datum.set_int(0);
                    } else if (0 == name.case_compare("gmt_create")
                               || 0 == name.case_compare("gmt_modified")) {
                      datum.set_int(common::ObTimeUtility::current_time());
                    } else {
                      datum.set_null();
                    }
                  }
                }
                if (OB_SUCC(lret) && OB_FAIL(rows.push_back(row))) {
                  lret = ret;
                }
              }
            }
          }
          if (OB_SUCC(lret)) {
            TaskRowIter iter(rows);
            int64_t affected = 0;
            lret = dml_service->insert_rows(
                common::ObTabletID(task_table.get_table_id()),
                *tx_desc, execution, column_ids, &iter, affected);
            LOG_INFO("ai col ins stage insert done", K(lret), K(affected));
            if (OB_SUCCESS == lret) {
              const int64_t ins_tx_id = (NULL == session)
                                            ? 0 : session->get_tx_id_with_thread_data_lock();
              for (int64_t v = 0; v < values.count(); ++v) {
                remember_tx_task_id(ins_tx_id, static_cast<uint64_t>(values.at(v).table_id_),
                                    values.at(v).rowkey_predicate_,
                                    values.at(v).task_id_);
              }
            }
          }
        }
      }
      return lret;
    };

    auto delete_task_rows_by_id = [&](const common::ObIArray<int64_t> &task_ids) -> int {
      int lret = OB_SUCCESS;
      const share::schema::ObTableSchema *task_table = NULL;
      data_plane::ObIDmlService *dml_service =
          share::server_service<data_plane::ObIDmlService>();
      data_plane::ObIWriteContextService *wcs =
          share::server_service<data_plane::ObIWriteContextService>();
      data_plane::ObITransactionService *txs =
          data_plane::query_transaction_service();
      ObSQLSessionInfo *session = ctx_.get_my_session();
      transaction::ObTxDesc *tx_desc = (NULL == session) ? NULL : session->get_tx_desc();
      transaction::ObTxReadSnapshot snapshot;
      concurrent_control::ObWriteFlag write_flag;
      data_plane::ObWriteContext write_context;
      data_plane::ObDmlExecution execution;
      common::ObSEArray<uint64_t, 4> column_ids;
      int64_t tenant_schema_version = 0;
      const int64_t timeout_us = common::ObTimeUtility::current_time() + 10000000;
      if (OB_ISNULL(dml_service) || OB_ISNULL(wcs) || OB_ISNULL(txs)
          || OB_ISNULL(session) || OB_ISNULL(tx_desc)) {
        lret = OB_ERR_UNEXPECTED;
      } else if (OB_SUCCESS != (lret = schema_guard->get_table_schema(
                     OB_ALL_AI_COLUMN_TASK_TID, task_table))) {
      } else if (OB_ISNULL(task_table)) {
        lret = OB_ERR_UNEXPECTED;
      } else if (OB_SUCCESS != (lret = schema_guard->get_schema_version(
                     tenant_schema_version))) {
      } else if (OB_SUCCESS != (lret = txs->get_read_snapshot(
                     *tx_desc, transaction::ObTxIsolationLevel::RC,
                     timeout_us, snapshot))) {
      } else if (OB_SUCCESS != (lret = task_table->get_rowkey_column_ids(column_ids))) {
      } else {
        data_plane::ObDmlTablePlan table_plan(tmp_allocator);
        if (OB_SUCCESS != (lret = table_plan.build(task_table, tenant_schema_version,
                                                    column_ids))) {
          LOG_INFO("ai col delete table plan failed", K(lret));
        } else {
          data_plane::ObDmlWriteSpec write_spec;
          write_spec.timeout_ = timeout_us;
          write_spec.schema_version_ = tenant_schema_version;
          write_spec.sql_mode_ = session->get_sql_mode();
          write_spec.tz_info_ = session->get_timezone_info();
          write_spec.branch_id_ = 0;
          write_spec.check_schema_version_ = false;
          if (OB_SUCCESS != (lret = wcs->acquire_write_context(
                                 timeout_us, *tx_desc, snapshot, 0,
                                 write_flag, write_context))) {
            LOG_INFO("ai col delete acquire write ctx failed", K(lret));
          } else if (OB_SUCCESS != (lret = dml_service->prepare_execution(
                        write_spec, table_plan, snapshot, tmp_allocator,
                        write_context, write_flag, execution))) {
            LOG_INFO("ai col delete prepare execution failed", K(lret));
          } else {
            common::ObSEArray<blocksstable::ObDatumRow *, 8> rows;
            for (int64_t i = 0; OB_SUCC(lret) && i < task_ids.count(); ++i) {
              blocksstable::ObDatumRow *row = static_cast<blocksstable::ObDatumRow *>(
                  tmp_allocator.alloc(sizeof(blocksstable::ObDatumRow)));
              if (OB_ISNULL(row)) {
                lret = OB_ALLOCATE_MEMORY_FAILED;
              } else {
                new (row) blocksstable::ObDatumRow();
                if (OB_SUCCESS != (lret = row->init(column_ids.count()))) {
                } else {
                  row->count_ = static_cast<uint16_t>(column_ids.count());
                  row->row_flag_.set_flag(blocksstable::DF_DELETE);
                  row->storage_datums_[0].set_int(task_ids.at(i));
                  if (OB_FAIL(rows.push_back(row))) {
                    lret = ret;
                  }
                }
              }
            }
            if (OB_SUCC(lret)) {
              TaskRowIter iter(rows);
              int64_t affected = 0;
              lret = dml_service->delete_rows(
                  common::ObTabletID(task_table->get_table_id()),
                  *tx_desc, execution, column_ids, &iter, affected);
              LOG_INFO("ai col delete rows done", K(lret), K(affected),
                       K(task_ids.count()));
            }
          }
        }
      }
      return lret;
    };

    // Delete the task rows of one data row. The catalog is read through a
    // dedicated connection (committed metadata), then the rowkeys are removed
    // through the data-plane DML seam inside the current transaction.
    auto delete_task_rows = [&](const uint64_t table_id,
                                const common::ObSqlString &predicate) -> int {
      int lret = OB_SUCCESS;
      ObSQLSessionInfo *del_session = ctx_.get_my_session();
      const int64_t del_tx_id = (NULL == del_session)
                                    ? 0 : del_session->get_tx_id_with_thread_data_lock();
      common::ObSEArray<int64_t, 8> cached_task_ids;
      if (del_tx_id > 0) {
        (void)take_tx_task_ids(del_tx_id, table_id, predicate.string(), cached_task_ids);
      }
      if (!cached_task_ids.empty()) {
        // Delete rows this very transaction inserted; the committed metadata view
        // below cannot see them.
        lret = delete_task_rows_by_id(cached_task_ids);
        if (OB_SUCCESS != lret) {
          LOG_INFO("ai col delete own txn tasks failed", K(lret), K(cached_task_ids.count()));
        }
      }
      common::ObMySQLProxy *sql_proxy = ctx_.get_sql_proxy();
      common::ObSqlString select;
      common::ObSEArray<int64_t, 8> task_ids;
      common::ObMySQLProxy::MySQLResult res;
      if (OB_FAIL(lret)) {
      } else if (OB_ISNULL(sql_proxy)) {
        lret = OB_NOT_INIT;
      } else if (OB_SUCCESS != (lret = select.assign_fmt(
                     "SELECT task_id FROM oceanbase.%s WHERE table_id = %ld"
                     " AND rowkey_predicate = ",
                     OB_ALL_AI_COLUMN_TASK_TNAME, table_id))) {
      } else if (OB_SUCCESS != (lret = append_sql_quoted(select, predicate.string()))) {
      } else if (OB_SUCCESS != (lret = sql_proxy->read(res, select.ptr()))) {
        LOG_INFO("ai col delete read tasks failed", K(lret));
      } else if (OB_ISNULL(res.get_result())) {
        lret = OB_ERR_UNEXPECTED;
      } else {
        common::sqlclient::ObMySQLResult *result = res.get_result();
        while (OB_SUCC(lret) && OB_SUCC(result->next())) {
          int64_t task_id = 0;
          if (OB_FAIL(result->get_int("task_id", task_id))) {
            lret = ret;
          } else if (OB_FAIL(task_ids.push_back(task_id))) {
            lret = ret;
          }
        }
        if (OB_ITER_END == lret) {
          lret = OB_SUCCESS;
        }
        int close_ret = res.get_result()->close();
        if (OB_SUCCESS != close_ret && OB_SUCCESS == lret) {
          lret = close_ret;
        }
      }
      if (OB_SUCC(lret) && !task_ids.empty()) {
        lret = delete_task_rows_by_id(task_ids);
      }
      return lret;
    };

    common::ObSEArray<TaskRowValue, 8> all_values;

    auto enqueue_tasks = [&](const uint64_t table_id,
                             const char *db_name,
                             const char *table_name,
                             const common::ObIArray<AIColumnInfo> &infos,
                             const common::ObSqlString &predicate) -> int {
      int lret = OB_SUCCESS;
      const int64_t request_id = common::ObTimeUtility::current_time() * 1000
                                 + (task_seq.fetch_add(1) % 1000);
      char *request_id_buf = static_cast<char *>(tmp_allocator.alloc(32));
      char *predicate_buf = static_cast<char *>(tmp_allocator.alloc(predicate.length() + 1));
      if (OB_ISNULL(request_id_buf) || OB_ISNULL(predicate_buf)) {
        lret = OB_ALLOCATE_MEMORY_FAILED;
      } else {
        int64_t request_pos = 0;
        if (OB_SUCCESS != (lret = databuff_printf(request_id_buf, 32, request_pos,
                                                  "%ld", request_id))) {
        } else {
          MEMCPY(predicate_buf, predicate.ptr(), predicate.length());
          const common::ObString request_id_str(static_cast<int32_t>(request_pos),
                                                request_id_buf);
          const common::ObString predicate_str(static_cast<int32_t>(predicate.length()),
                                               predicate_buf);
          for (int64_t i = 0; OB_SUCC(lret) && i < infos.count(); ++i) {
            TaskRowValue v;
            v.task_id_ = request_id * 100 + i;
            v.table_id_ = static_cast<int64_t>(table_id);
            v.column_id_ = infos.at(i).column_id_;
            v.state_ = 1;
            v.retry_count_ = 0;
            v.eligible_ts_ = common::ObTimeUtility::current_time();
            v.request_id_ = request_id_str;
            v.rowkey_predicate_ = predicate_str;
            v.group_id_ = request_id_str;
            if (OB_FAIL(all_values.push_back(v))) {
              lret = ret;
            } else {
              ++grand_task_cnt;
            }
          }
        }
      }
      UNUSEDx(db_name, table_name);
      return lret;
    };

    for (ObDMLModifyRowsList::iterator it = dml_modify_rows_.begin();
         OB_SUCC(ret) && it != dml_modify_rows_.end(); ++it) {
      ObDMLModifyRowNode &node = *it;
      const ObDMLBaseCtDef *ctdef = node.dml_ctdef_;
      const share::schema::ObTableSchema *table = NULL;
      uint64_t table_id = common::OB_INVALID_ID;
      common::ObSEArray<AIColumnInfo, 4> infos;
      if (OB_ISNULL(ctdef) || !ctdef->is_primary_index_) {
        continue;
      }
      table_id = ctdef->das_base_ctdef_.table_param_.get_data_table().get_table_id();
      if (table_id < common::OB_MIN_USER_OBJECT_ID) {
        continue;
      } else if (OB_FAIL(schema_guard->get_table_schema(table_id, table))) {
      } else if (OB_ISNULL(table)) {
        ret = OB_ERR_UNEXPECTED;
      } else if (!table_has_ai_column(*table)) {
        continue;
      } else if (OB_FAIL(load_ai_columns(*table, infos))) {
      } else if (infos.empty()) {
        continue;
      }

      const share::schema::ObDatabaseSchema *db_schema = NULL;
      const char *db_name = "";
      if (OB_FAIL(ret)) {
      } else if (OB_FAIL(schema_guard->get_database_schema(table->get_database_id(), db_schema))
                 || OB_ISNULL(db_schema)) {
        ret = OB_ERR_UNEXPECTED;
      } else {
        db_name = db_schema->get_database_name_str().ptr();
      }
      const char *table_name = table->get_table_name_str().ptr();

      LOG_INFO("ai column dml row event", K(table_id), "event",
               static_cast<int>(node.dml_event_), K(infos.count()));
      common::ObSqlString predicate;
      common::ObSqlString old_predicate;
      if (OB_FAIL(ret)) {
      } else if (ObDmlEventType::DE_DELETING == node.dml_event_) {
        if (OB_ISNULL(node.old_row_)) {
          ret = OB_ERR_UNEXPECTED;
        } else if (OB_FAIL(append_rowkey_predicate(*table, *ctdef, *node.old_row_, old_predicate))) {
        } else if (OB_FAIL(delete_task_rows(table_id, old_predicate))) {
        }
      } else if (ObDmlEventType::DE_UPDATING == node.dml_event_) {
        // UPDATE invalidation. The resolver has already added an implicit
        // "<ai_col> = NULL" assignment for every AI column whose dependencies (or
        // rowkey) are touched; the code generator therefore lists those AI result
        // columns in updated_column_ids_. That marker is plan-persistent, so it also
        // works when the statement is re-executed from the plan cache.
        const ObUpdCtDef *upd_ctdef = static_cast<const ObUpdCtDef *>(ctdef);
        const bool is_pk_update = upd_ctdef->das_base_ctdef_.is_update_pk_;
        const bool row_changed = (NULL != node.full_row_) || is_pk_update;
        common::ObSEArray<AIColumnInfo, 4> invalidated_infos;
        // Do not gate on row_changed: an explicit assignment of an AI result column
        // (e.g. ALTER TABLE ... RETRY AI COLUMN rewrites "<col> = NULL") is a
        // regeneration request even when the stored value is already NULL, and the
        // resolver's implicit invalidation also shows up in updated_column_ids_.
        {
          const ObChunkDatumStore::StoredRow *old_stored = node.old_row_;
          const ObChunkDatumStore::StoredRow *new_stored = node.new_row_;
          if (NULL == old_stored) {
            old_stored = node.full_row_;
          }
          if (NULL == new_stored) {
            new_stored = (NULL != node.full_row_) ? node.full_row_ : old_stored;
          }
          if (OB_ISNULL(old_stored) || OB_ISNULL(new_stored)) {
            ret = OB_ERR_UNEXPECTED;
            LOG_WARN("ai column update row data is null", K(ret));
          } else if (OB_FAIL(append_rowkey_predicate(*table, *ctdef, *new_stored, predicate))) {
            LOG_WARN("append ai column new rowkey predicate failed", K(ret));
          } else if (OB_FAIL(append_rowkey_predicate(*table, *ctdef, *old_stored, old_predicate))) {
            LOG_WARN("append ai column old rowkey predicate failed", K(ret));
          } else {
            for (int64_t i = 0; OB_SUCC(ret) && i < infos.count(); ++i) {
              const AIColumnInfo &info = infos.at(i);
              bool invalidated = is_pk_update;
              for (int64_t u = 0; !invalidated
                                  && u < upd_ctdef->dupd_ctdef_.updated_column_ids_.count(); ++u) {
                if (upd_ctdef->dupd_ctdef_.updated_column_ids_.at(u)
                    == static_cast<uint64_t>(info.column_id_)) {
                  invalidated = true;
                }
              }
              if (OB_SUCC(ret) && invalidated && OB_FAIL(invalidated_infos.push_back(info))) {
              }
            }
            LOG_INFO("ai col upd invalidation", K(is_pk_update), K(row_changed),
                     K(invalidated_infos.count()), "new", predicate.ptr(),
                     "old", old_predicate.ptr());
            if (OB_SUCC(ret) && !invalidated_infos.empty()) {
              if (OB_FAIL(delete_task_rows(table_id, old_predicate))) {
                LOG_WARN("ai col delete stale tasks failed", K(ret));
              } else if (OB_FAIL(enqueue_tasks(table_id, db_name, table_name,
                                               invalidated_infos, predicate))) {
                LOG_WARN("ai col enqueue tasks for invalidated columns failed", K(ret));
              }
            }
          }
        }
      } else if (OB_ISNULL(node.new_row_)) {
        ret = OB_ERR_UNEXPECTED;
      } else if (OB_FAIL(append_rowkey_predicate(*table, *ctdef, *node.new_row_, predicate))) {
      } else if (OB_FAIL(enqueue_tasks(table_id, db_name, table_name, infos, predicate))) {
      }
    }

    if (OB_SUCC(ret) && !all_values.empty()) {
      const share::schema::ObTableSchema *task_table = NULL;
      if (OB_FAIL(schema_guard->get_table_schema(OB_ALL_AI_COLUMN_TASK_TID, task_table))) {
        LOG_INFO("ai col get task table schema failed", K(ret));
      } else if (OB_ISNULL(task_table)) {
        ret = OB_ERR_UNEXPECTED;
      } else if (OB_FAIL(insert_task_rows(*task_table, all_values))) {
        LOG_INFO("ai col batch insert tasks failed", K(ret), K(all_values.count()));
      }
    }
    if (OB_SUCC(ret) && grand_task_cnt > 0) {
      LOG_INFO("ai column enqueue tasks done", K(grand_task_cnt));
    }
    if (OB_FAIL(ret)) {
      LOG_WARN("ai column row processing failed", K(ret));
    }
  }
  return ret;
}

int ObTableModifyOp::submit_all_dml_task()
{
  int ret = OB_SUCCESS;
  LOG_INFO("ai column submit_all_dml_task enter", K(dml_modify_rows_.size()),
           K(dml_rtctx_.das_ref_.has_task()));
  if (dml_rtctx_.das_ref_.has_task()) {
    bool need_fk_or_trigger = false;
    for (ObDMLModifyRowsList::iterator row_it = dml_modify_rows_.begin();
         !need_fk_or_trigger && row_it != dml_modify_rows_.end(); ++row_it) {
      const ObDMLBaseCtDef *row_ctdef = (*row_it).dml_ctdef_;
      if (NULL != row_ctdef
          && (need_foreign_key_check(*row_ctdef) || has_after_row_trigger(*row_ctdef))) {
        need_fk_or_trigger = true;
      }
    }
    if (dml_rtctx_.need_pick_del_task_first() &&
                OB_FAIL(dml_rtctx_.das_ref_.pick_del_task_to_first())) {
      LOG_INFO("ai col submit stage pick del failed", K(ret));
    } else if (OB_FAIL(dml_rtctx_.das_ref_.execute_all_task())) {
      LOG_INFO("ai col submit stage execute all failed", K(ret));
    } else if (OB_FAIL(dml_rtctx_.das_ref_.close_all_task())) {
      LOG_INFO("ai col submit stage close all failed", K(ret));
    } else if (need_fk_or_trigger
               && OB_FAIL(ObDMLService::handle_after_row_processing(this, &get_dml_modify_row_list()))) {
      LOG_INFO("ai col submit stage fk/trigger failed", K(ret));
    } else if (OB_FAIL(handle_ai_column_row_processing())) {
      LOG_INFO("ai col submit stage ai column failed", K(ret));
    } else {
      dml_modify_rows_.clear();
      dml_rtctx_.reuse();
    }
  }
  return ret;
}

//The data to be written by DML will be buffered in the DAS Write Buffer
//When the buffer data exceeds 6M,
//needs to be written to the storage to release the memory.
int ObTableModifyOp::discharge_das_write_buffer()
{
  int ret = OB_SUCCESS;
  if (dml_rtctx_.need_submit_all_tasks()) {
    LOG_INFO("DASWriteBuffer full, now to write storage",
             "buffer memory", dml_rtctx_.das_ref_.get_das_alloc().used(),
             K(dml_rtctx_.get_das_task_memory_size()), K(dml_rtctx_.get_das_parallel_task_size()));
    ret = submit_all_dml_task();
  } else if (execute_single_row_) {
    if (REACH_COUNT_INTERVAL(100)) { // print log per 100 times.
    }
    ret = submit_all_dml_task();
  }
  return ret;
}

int ObTableModifyOp::get_next_row_from_child()
{
  int ret = OB_SUCCESS;
  clear_evaluated_flag();
  if (OB_FAIL(child_->get_next_row())) {
    if (OB_ITER_END != ret) {
    }
  } else {
    LOG_DEBUG("child output row", "row", ROWEXPR2STR(eval_ctx_, child_->get_spec().output_));
  }
  return ret;
}

int ObTableModifyOp::inner_get_next_row()
{
  int ret = OB_SUCCESS;
  if (iter_end_) {
    ret = OB_ITER_END;
  } else {
    int64_t row_count = 0;
    while (OB_SUCC(ret)) {
      if (OB_FAIL(try_check_status())) {
      } else if (OB_FAIL(get_next_row_from_child())) {
        if (OB_ITER_END != ret) {
        } else {
          iter_end_ = true;
          ret = OB_SUCCESS;
          break;
        }
      } else if (OB_FAIL(write_row_to_das_buffer())) {
      } else if (OB_FAIL(discharge_das_write_buffer())) {
      } else if (MY_SPEC.is_returning_) {
        break;
      }
      row_count ++;
    }

    if (OB_FAIL(ret)) {
      record_err_for_load_data(ret, row_count);
    }

    if (OB_SUCC(ret) && iter_end_ && dml_rtctx_.das_ref_.has_task()) {
      //DML operator reach iter end,
      //now submit the remaining rows in the DAS Write Buffer to the storage
      if (OB_FAIL(submit_all_dml_task())) {
      }
    }
    //to post process the DML info after writing all data to the storage or returning one row
    ret = write_rows_post_proc(ret);
    if (OB_SUCC(ret) && iter_end_) {
      ret = OB_ITER_END;
    }
  }
  return ret;
}

int ObTableModifyOp::perform_batch_fk_check()
{
  DEBUG_SYNC(BEFORE_FOREIGN_KEY_CONSTRAINT_CHECK);
  int ret = OB_SUCCESS;
  for (int64_t i = 0; OB_SUCC(ret) && i < fk_checkers_.count(); ++i) {
    bool all_has_result = false;
    ObForeignKeyChecker *fk_checker = fk_checkers_.at(i);
    if (OB_ISNULL(fk_checker)) {
      ret = OB_ERR_UNEXPECTED;
    } else if (OB_FAIL(fk_checker->do_fk_check_batch(all_has_result))) {
    } else if (!all_has_result) {
      ret = OB_ERR_NO_REFERENCED_ROW;
    }
  }
  return ret;
}
}  // namespace sql
}  // namespace oceanbase

