# 页表形状分布

样本 1516；形状 79；处理耗时 2.130 秒。

truncated=true：1513。计数表示导出代表样本频数，不表示全部具体状态的概率。

| 形状 | 计数 | 占比 |
| --- | ---: | ---: |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_r-x_u1--leaf-l0--Retire_Success--success` | 85 | 5.6069% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_r--_u0--leaf-l0--Retire_Success--success` | 83 | 5.4749% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_rwx_u0--leaf-l0--Retire_Success--success` | 81 | 5.3430% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_rw-_u0--leaf-l0--Retire_Success--success` | 79 | 5.2111% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_rw-_u1--leaf-l0--Retire_Success--success` | 79 | 5.2111% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_rwx_u1--leaf-l0--Retire_Success--success` | 77 | 5.0792% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_r--_u1--leaf-l0--Retire_Success--success` | 74 | 4.8813% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_r-x_u0--leaf-l0--Retire_Success--success` | 71 | 4.6834% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_r-x_u0--leaf-l0--E_Load_Access_Fault--data_read_pma_access_fault` | 54 | 3.5620% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_rw-_u1--leaf-l0--E_Load_Access_Fault--data_read_pma_access_fault` | 54 | 3.5620% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_rwx_u1--leaf-l0--E_Load_Access_Fault--data_read_pma_access_fault` | 54 | 3.5620% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_rwx_u0--leaf-l0--E_Load_Access_Fault--data_read_pma_access_fault` | 53 | 3.4960% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_r--_u1--leaf-l0--E_Load_Access_Fault--data_read_pma_access_fault` | 52 | 3.4301% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_r-x_u1--leaf-l0--E_Load_Access_Fault--data_read_pma_access_fault` | 52 | 3.4301% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_rw-_u0--leaf-l0--E_Load_Access_Fault--data_read_pma_access_fault` | 51 | 3.3641% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_r--_u0--leaf-l0--E_Load_Access_Fault--data_read_pma_access_fault` | 49 | 3.2322% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_rwx_u1--leaf-l0--E_Load_Page_Fault--accessed_update_disabled` | 34 | 2.2427% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_r-x_u1--leaf-l0--E_Load_Page_Fault--accessed_update_disabled` | 30 | 1.9789% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_r-x_u0--leaf-l0--E_Load_Page_Fault--accessed_update_disabled` | 28 | 1.8470% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_rwx_u0--leaf-l0--E_Load_Page_Fault--accessed_update_disabled` | 27 | 1.7810% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_rw-_u0--leaf-l0--E_Load_Page_Fault--accessed_update_disabled` | 25 | 1.6491% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_rw-_u1--leaf-l0--E_Load_Page_Fault--accessed_update_disabled` | 23 | 1.5172% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_r--_u1--leaf-l0--E_Load_Page_Fault--accessed_update_disabled` | 22 | 1.4512% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_r--_u0--leaf-l0--E_Load_Page_Fault--accessed_update_disabled` | 21 | 1.3852% |
| `load--sv39--l2-pointer--l1-pointer--l0-invalid_reserved_nonzero--no-leaf--E_Load_Page_Fault--reserved_nonzero` | 19 | 1.2533% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_--x_u1--leaf-l0--E_Load_Page_Fault--load_permission` | 14 | 0.9235% |
| `load--sv39--l2-pointer--l1-pointer--l0-pointer--no-leaf--E_Load_Page_Fault--pointer_at_level0` | 14 | 0.9235% |
| `load--sv39--l2-pointer--l1-pointer--l0-leaf_--x_u0--leaf-l0--E_Load_Page_Fault--load_permission` | 13 | 0.8575% |
| `load--sv39--l2-pointer--l1-leaf_rwx_u1--leaf-l1--Retire_Success--success` | 11 | 0.7256% |
| `load--sv39--l2-pointer--l1-leaf_r--_u0--leaf-l1--Retire_Success--success` | 10 | 0.6596% |
| `load--sv39--l2-pointer--l1-leaf_r-x_u1--leaf-l1--E_Load_Access_Fault--data_read_pma_access_fault` | 10 | 0.6596% |
| `load--sv39--l2-pointer--l1-leaf_r-x_u1--leaf-l1--Retire_Success--success` | 10 | 0.6596% |
| `load--sv39--l2-pointer--l1-leaf_rw-_u1--leaf-l1--Retire_Success--success` | 10 | 0.6596% |
| `load--sv39--l2-pointer--l1-leaf_r--_u0--leaf-l1--E_Load_Access_Fault--data_read_pma_access_fault` | 9 | 0.5937% |
| `load--sv39--l2-pointer--l1-leaf_r-x_u0--leaf-l1--Retire_Success--success` | 9 | 0.5937% |
| `load--sv39--l2-pointer--l1-leaf_rwx_u0--leaf-l1--E_Load_Access_Fault--data_read_pma_access_fault` | 8 | 0.5277% |
| `load--sv39--l2-pointer--l1-pointer--l0-invalid_n_disabled--no-leaf--E_Load_Page_Fault--n_disabled` | 8 | 0.5277% |
| `load--sv39--l2-pointer--l1-leaf_r--_u1--leaf-l1--Retire_Success--success` | 7 | 0.4617% |
| `load--sv39--l2-pointer--l1-leaf_rwx_u0--leaf-l1--Retire_Success--success` | 7 | 0.4617% |
| `load--sv39--l2-pointer--l1-pointer--l0-invalid_pbmt_disabled--no-leaf--E_Load_Page_Fault--pbmt_disabled` | 7 | 0.4617% |
| `load--sv39--l2-pointer--l1-leaf_r-x_u0--leaf-l1--E_Load_Page_Fault--accessed_update_disabled` | 6 | 0.3958% |
| `load--sv39--l2-pointer--l1-leaf_rw-_u0--leaf-l1--Retire_Success--success` | 6 | 0.3958% |
| `load--sv39--l2-pointer--l1-leaf_rw-_u1--leaf-l1--E_Load_Access_Fault--data_read_pma_access_fault` | 6 | 0.3958% |
| `load--sv39--l2-pointer--l1-pointer--l0-invalid_write_without_read--no-leaf--E_Load_Page_Fault--write_without_read` | 6 | 0.3958% |
| `load--sv39--l2-pointer--l1-leaf_rw-_u0--leaf-l1--E_Load_Access_Fault--data_read_pma_access_fault` | 5 | 0.3298% |
| `load--sv39--l2-pointer--l1-leaf_rwx_u1--leaf-l1--E_Load_Access_Fault--data_read_pma_access_fault` | 5 | 0.3298% |
| `load--sv39--l2-pointer--l1-leaf_rw-_u0--leaf-l1--E_Load_Page_Fault--accessed_update_disabled` | 4 | 0.2639% |
| `load--sv39--l2-pointer--l1-leaf_rw-_u1--leaf-l1--E_Load_Page_Fault--accessed_update_disabled` | 4 | 0.2639% |
| `load--sv39--l2-pointer--l1-leaf_rwx_u1--leaf-l1--E_Load_Page_Fault--accessed_update_disabled` | 4 | 0.2639% |
| `load--sv39--l2-pointer--l1-pointer--l0-invalid_v_zero--no-leaf--E_Load_Page_Fault--v_zero` | 4 | 0.2639% |
| `load--sv39--l2-pointer--l1-invalid_reserved_nonzero--no-leaf--E_Load_Page_Fault--reserved_nonzero` | 3 | 0.1979% |
| `load--sv39--l2-pointer--l1-leaf_r--_u0--leaf-l1--E_Load_Page_Fault--accessed_update_disabled` | 3 | 0.1979% |
| `load--sv39--l2-pointer--l1-leaf_r--_u1--leaf-l1--E_Load_Access_Fault--data_read_pma_access_fault` | 3 | 0.1979% |
| `load--sv39--l2-pointer--l1-leaf_r-x_u0--leaf-l1--E_Load_Page_Fault--superpage_misaligned` | 3 | 0.1979% |
| `load--sv39--l2-pointer--l1-pointer--no-leaf--E_Load_Access_Fault--pte_read_pma_access_fault` | 3 | 0.1979% |
| `load--sv39--l2-leaf_rw-_u0--leaf-l2--Retire_Success--success` | 2 | 0.1319% |
| `load--sv39--l2-pointer--l1-leaf_--x_u1--leaf-l1--E_Load_Page_Fault--load_permission` | 2 | 0.1319% |
| `load--sv39--l2-pointer--l1-leaf_r--_u1--leaf-l1--E_Load_Page_Fault--accessed_update_disabled` | 2 | 0.1319% |
| `load--sv39--l2-invalid_reserved_nonzero--no-leaf--E_Load_Page_Fault--reserved_nonzero` | 1 | 0.0660% |
| `load--sv39--l2-leaf_--x_u1--leaf-l2--E_Load_Page_Fault--load_permission` | 1 | 0.0660% |
| `load--sv39--l2-leaf_r--_u0--leaf-l2--Retire_Success--success` | 1 | 0.0660% |
| `load--sv39--l2-leaf_r--_u1--leaf-l2--Retire_Success--success` | 1 | 0.0660% |
| `load--sv39--l2-leaf_r-x_u0--leaf-l2--E_Load_Access_Fault--data_read_pma_access_fault` | 1 | 0.0660% |
| `load--sv39--l2-leaf_r-x_u0--leaf-l2--E_Load_Page_Fault--accessed_update_disabled` | 1 | 0.0660% |
| `load--sv39--l2-leaf_r-x_u0--leaf-l2--Retire_Success--success` | 1 | 0.0660% |
| `load--sv39--l2-leaf_rw-_u0--leaf-l2--E_Load_Access_Fault--data_read_pma_access_fault` | 1 | 0.0660% |
| `load--sv39--l2-leaf_rw-_u1--leaf-l2--E_Load_Page_Fault--accessed_update_disabled` | 1 | 0.0660% |
| `load--sv39--l2-leaf_rwx_u0--leaf-l2--E_Load_Page_Fault--superpage_misaligned` | 1 | 0.0660% |
| `load--sv39--l2-leaf_rwx_u1--leaf-l2--E_Load_Access_Fault--data_read_pma_access_fault` | 1 | 0.0660% |
| `load--sv39--l2-leaf_rwx_u1--leaf-l2--E_Load_Page_Fault--accessed_update_disabled` | 1 | 0.0660% |
| `load--sv39--l2-leaf_rwx_u1--leaf-l2--Retire_Success--success` | 1 | 0.0660% |
| `load--sv39--l2-pointer--l1-invalid_write_without_read--no-leaf--E_Load_Page_Fault--write_without_read` | 1 | 0.0660% |
| `load--sv39--l2-pointer--l1-leaf_--x_u0--leaf-l1--E_Load_Page_Fault--load_permission` | 1 | 0.0660% |
| `load--sv39--l2-pointer--l1-leaf_r--_u0--leaf-l1--E_Load_Page_Fault--superpage_misaligned` | 1 | 0.0660% |
| `load--sv39--l2-pointer--l1-leaf_r-x_u0--leaf-l1--E_Load_Access_Fault--data_read_pma_access_fault` | 1 | 0.0660% |
| `load--sv39--l2-pointer--l1-leaf_r-x_u1--leaf-l1--E_Load_Page_Fault--accessed_update_disabled` | 1 | 0.0660% |
| `load--sv39--l2-pointer--l1-leaf_rw-_u0--leaf-l1--E_Load_Page_Fault--superpage_misaligned` | 1 | 0.0660% |
| `load--sv39--l2-pointer--l1-leaf_rwx_u0--leaf-l1--E_Load_Page_Fault--superpage_misaligned` | 1 | 0.0660% |
| `load--sv39--l2-pointer--no-leaf--E_Load_Access_Fault--pte_read_pma_access_fault` | 1 | 0.0660% |

## 结果类别

| 类别 | 计数 | 占比 |
| --- | ---: | ---: |
| Retire_Success | 705 | 46.5040% |
| E_Load_Access_Fault | 473 | 31.2005% |
| E_Load_Page_Fault | 338 | 22.2955% |

## 叶子层（包括叶子处失败）

| 类别 | 计数 | 占比 |
| --- | ---: | ---: |
| L0 | 1285 | 84.7625% |
| L1 | 150 | 9.8945% |
| 无叶子 | 67 | 4.4195% |
| L2 | 14 | 0.9235% |

位约束仅由本形状的已导出样本推断，非求解器约束；free 位不可独立任意组合。
