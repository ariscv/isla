# 页表形状分布

样本 11162；形状 118；处理耗时 15.618 秒。

truncated=true：11154。计数表示导出代表样本频数，不表示全部具体状态的概率。

| 形状 | 计数 | 占比 |
| --- | ---: | ---: |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_r-x_u0--leaf-l0--Retire_Success--success` | 575 | 5.1514% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_rwx_u1--leaf-l0--Retire_Success--success` | 568 | 5.0887% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_rw-_u1--leaf-l0--Retire_Success--success` | 567 | 5.0797% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_r--_u1--leaf-l0--Retire_Success--success` | 563 | 5.0439% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_r--_u0--leaf-l0--Retire_Success--success` | 560 | 5.0170% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_rwx_u0--leaf-l0--Retire_Success--success` | 553 | 4.9543% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_rw-_u0--leaf-l0--Retire_Success--success` | 546 | 4.8916% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_r-x_u1--leaf-l0--Retire_Success--success` | 537 | 4.8110% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_rwx_u1--leaf-l0--E_Load_Access_Fault--data_read_pma_access_fault` | 378 | 3.3865% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_r-x_u1--leaf-l0--E_Load_Access_Fault--data_read_pma_access_fault` | 376 | 3.3686% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_rw-_u1--leaf-l0--E_Load_Access_Fault--data_read_pma_access_fault` | 376 | 3.3686% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_r-x_u0--leaf-l0--E_Load_Access_Fault--data_read_pma_access_fault` | 374 | 3.3507% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_r--_u1--leaf-l0--E_Load_Access_Fault--data_read_pma_access_fault` | 373 | 3.3417% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_r--_u0--leaf-l0--E_Load_Access_Fault--data_read_pma_access_fault` | 370 | 3.3148% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_rwx_u0--leaf-l0--E_Load_Access_Fault--data_read_pma_access_fault` | 368 | 3.2969% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_rw-_u0--leaf-l0--E_Load_Access_Fault--data_read_pma_access_fault` | 364 | 3.2611% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_rw-_u1--leaf-l0--E_Load_Page_Fault--accessed_update_disabled` | 194 | 1.7380% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_r-x_u1--leaf-l0--E_Load_Page_Fault--accessed_update_disabled` | 191 | 1.7112% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_rw-_u0--leaf-l0--E_Load_Page_Fault--accessed_update_disabled` | 188 | 1.6843% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_r-x_u0--leaf-l0--E_Load_Page_Fault--accessed_update_disabled` | 187 | 1.6753% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_r--_u0--leaf-l0--E_Load_Page_Fault--accessed_update_disabled` | 186 | 1.6664% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_rwx_u0--leaf-l0--E_Load_Page_Fault--accessed_update_disabled` | 185 | 1.6574% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_rwx_u1--leaf-l0--E_Load_Page_Fault--accessed_update_disabled` | 184 | 1.6485% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_r--_u1--leaf-l0--E_Load_Page_Fault--accessed_update_disabled` | 175 | 1.5678% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-invalid_reserved_nonzero--no-leaf--E_Load_Page_Fault--reserved_nonzero` | 138 | 1.2363% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-pointer--no-leaf--E_Load_Page_Fault--pointer_at_level0` | 99 | 0.8869% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_--x_u1--leaf-l0--E_Load_Page_Fault--load_permission` | 94 | 0.8421% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-leaf_--x_u0--leaf-l0--E_Load_Page_Fault--load_permission` | 93 | 0.8332% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_rw-_u0--leaf-l1--Retire_Success--success` | 82 | 0.7346% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_rwx_u0--leaf-l1--Retire_Success--success` | 82 | 0.7346% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_r--_u0--leaf-l1--Retire_Success--success` | 81 | 0.7257% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_r-x_u1--leaf-l1--Retire_Success--success` | 81 | 0.7257% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_r--_u1--leaf-l1--Retire_Success--success` | 79 | 0.7078% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_r-x_u0--leaf-l1--Retire_Success--success` | 77 | 0.6898% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_rw-_u1--leaf-l1--Retire_Success--success` | 75 | 0.6719% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_rwx_u1--leaf-l1--Retire_Success--success` | 72 | 0.6450% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-invalid_pbmt_disabled--no-leaf--E_Load_Page_Fault--pbmt_disabled` | 72 | 0.6450% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-invalid_n_disabled--no-leaf--E_Load_Page_Fault--n_disabled` | 63 | 0.5644% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_r--_u0--leaf-l1--E_Load_Access_Fault--data_read_pma_access_fault` | 56 | 0.5017% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_r-x_u1--leaf-l1--E_Load_Access_Fault--data_read_pma_access_fault` | 55 | 0.4927% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_rw-_u0--leaf-l1--E_Load_Access_Fault--data_read_pma_access_fault` | 54 | 0.4838% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_rw-_u1--leaf-l1--E_Load_Access_Fault--data_read_pma_access_fault` | 54 | 0.4838% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_rwx_u0--leaf-l1--E_Load_Access_Fault--data_read_pma_access_fault` | 53 | 0.4748% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_r-x_u0--leaf-l1--E_Load_Access_Fault--data_read_pma_access_fault` | 50 | 0.4479% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_rwx_u1--leaf-l1--E_Load_Access_Fault--data_read_pma_access_fault` | 49 | 0.4390% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_r--_u1--leaf-l1--E_Load_Access_Fault--data_read_pma_access_fault` | 48 | 0.4300% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-invalid_write_without_read--no-leaf--E_Load_Page_Fault--write_without_read` | 46 | 0.4121% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--l0-invalid_v_zero--no-leaf--E_Load_Page_Fault--v_zero` | 31 | 0.2777% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_rwx_u1--leaf-l1--E_Load_Page_Fault--accessed_update_disabled` | 30 | 0.2688% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_r--_u0--leaf-l1--E_Load_Page_Fault--accessed_update_disabled` | 28 | 0.2509% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_rwx_u0--leaf-l1--E_Load_Page_Fault--accessed_update_disabled` | 27 | 0.2419% |
| `load--sv48--l3-pointer--l2-pointer--l1-pointer--no-leaf--E_Load_Access_Fault--pte_read_pma_access_fault` | 27 | 0.2419% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_r-x_u0--leaf-l1--E_Load_Page_Fault--accessed_update_disabled` | 26 | 0.2329% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_rw-_u1--leaf-l1--E_Load_Page_Fault--accessed_update_disabled` | 26 | 0.2329% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_r-x_u1--leaf-l1--E_Load_Page_Fault--accessed_update_disabled` | 25 | 0.2240% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_r--_u1--leaf-l1--E_Load_Page_Fault--accessed_update_disabled` | 24 | 0.2150% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_rw-_u0--leaf-l1--E_Load_Page_Fault--accessed_update_disabled` | 24 | 0.2150% |
| `load--sv48--l3-pointer--l2-pointer--l1-invalid_reserved_nonzero--no-leaf--E_Load_Page_Fault--reserved_nonzero` | 19 | 0.1702% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_rwx_u0--leaf-l1--E_Load_Page_Fault--superpage_misaligned` | 18 | 0.1613% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_r--_u0--leaf-l1--E_Load_Page_Fault--superpage_misaligned` | 15 | 0.1344% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_--x_u1--leaf-l1--E_Load_Page_Fault--load_permission` | 14 | 0.1254% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_--x_u0--leaf-l1--E_Load_Page_Fault--load_permission` | 13 | 0.1165% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_r-x_u0--leaf-l1--E_Load_Page_Fault--superpage_misaligned` | 13 | 0.1165% |
| `load--sv48--l3-pointer--l2-leaf_r-x_u0--leaf-l2--Retire_Success--success` | 10 | 0.0896% |
| `load--sv48--l3-pointer--l2-leaf_rw-_u0--leaf-l2--Retire_Success--success` | 10 | 0.0896% |
| `load--sv48--l3-pointer--l2-leaf_rw-_u1--leaf-l2--Retire_Success--success` | 10 | 0.0896% |
| `load--sv48--l3-pointer--l2-leaf_r-x_u1--leaf-l2--Retire_Success--success` | 9 | 0.0806% |
| `load--sv48--l3-pointer--l2-leaf_rwx_u1--leaf-l2--Retire_Success--success` | 9 | 0.0806% |
| `load--sv48--l3-pointer--l2-pointer--l1-invalid_n_disabled--no-leaf--E_Load_Page_Fault--n_disabled` | 9 | 0.0806% |
| `load--sv48--l3-pointer--l2-leaf_r--_u0--leaf-l2--Retire_Success--success` | 8 | 0.0717% |
| `load--sv48--l3-pointer--l2-leaf_r--_u1--leaf-l2--Retire_Success--success` | 8 | 0.0717% |
| `load--sv48--l3-pointer--l2-pointer--l1-invalid_pbmt_disabled--no-leaf--E_Load_Page_Fault--pbmt_disabled` | 7 | 0.0627% |
| `load--sv48--l3-pointer--l2-pointer--l1-leaf_rw-_u0--leaf-l1--E_Load_Page_Fault--superpage_misaligned` | 7 | 0.0627% |
| `load--sv48--l3-pointer--l2-leaf_rwx_u0--leaf-l2--Retire_Success--success` | 6 | 0.0538% |
| `load--sv48--l3-pointer--l2-leaf_rwx_u1--leaf-l2--E_Load_Access_Fault--data_read_pma_access_fault` | 6 | 0.0538% |
| `load--sv48--l3-pointer--l2-leaf_r-x_u0--leaf-l2--E_Load_Access_Fault--data_read_pma_access_fault` | 5 | 0.0448% |
| `load--sv48--l3-pointer--l2-leaf_r-x_u0--leaf-l2--E_Load_Page_Fault--accessed_update_disabled` | 5 | 0.0448% |
| `load--sv48--l3-pointer--l2-leaf_rw-_u0--leaf-l2--E_Load_Page_Fault--accessed_update_disabled` | 5 | 0.0448% |
| `load--sv48--l3-pointer--l2-leaf_rw-_u1--leaf-l2--E_Load_Access_Fault--data_read_pma_access_fault` | 5 | 0.0448% |
| `load--sv48--l3-pointer--l2-leaf_rwx_u1--leaf-l2--E_Load_Page_Fault--accessed_update_disabled` | 5 | 0.0448% |
| `load--sv48--l3-pointer--l2-pointer--l1-invalid_write_without_read--no-leaf--E_Load_Page_Fault--write_without_read` | 5 | 0.0448% |
| `load--sv48--l3-pointer--l2-leaf_--x_u1--leaf-l2--E_Load_Page_Fault--load_permission` | 4 | 0.0358% |
| `load--sv48--l3-pointer--l2-leaf_r--_u0--leaf-l2--E_Load_Access_Fault--data_read_pma_access_fault` | 4 | 0.0358% |
| `load--sv48--l3-pointer--l2-leaf_r--_u0--leaf-l2--E_Load_Page_Fault--accessed_update_disabled` | 4 | 0.0358% |
| `load--sv48--l3-pointer--l2-leaf_r--_u1--leaf-l2--E_Load_Access_Fault--data_read_pma_access_fault` | 4 | 0.0358% |
| `load--sv48--l3-pointer--l2-leaf_r--_u1--leaf-l2--E_Load_Page_Fault--accessed_update_disabled` | 4 | 0.0358% |
| `load--sv48--l3-pointer--l2-leaf_r-x_u1--leaf-l2--E_Load_Access_Fault--data_read_pma_access_fault` | 4 | 0.0358% |
| `load--sv48--l3-pointer--l2-leaf_r-x_u1--leaf-l2--E_Load_Page_Fault--accessed_update_disabled` | 4 | 0.0358% |
| `load--sv48--l3-pointer--l2-leaf_rw-_u0--leaf-l2--E_Load_Access_Fault--data_read_pma_access_fault` | 4 | 0.0358% |
| `load--sv48--l3-pointer--l2-leaf_rw-_u1--leaf-l2--E_Load_Page_Fault--accessed_update_disabled` | 4 | 0.0358% |
| `load--sv48--l3-pointer--l2-leaf_rwx_u0--leaf-l2--E_Load_Page_Fault--accessed_update_disabled` | 4 | 0.0358% |
| `load--sv48--l3-pointer--l2-pointer--l1-invalid_v_zero--no-leaf--E_Load_Page_Fault--v_zero` | 4 | 0.0358% |
| `load--sv48--l3-pointer--l2-invalid_pbmt_disabled--no-leaf--E_Load_Page_Fault--pbmt_disabled` | 3 | 0.0269% |
| `load--sv48--l3-pointer--l2-leaf_r--_u0--leaf-l2--E_Load_Page_Fault--superpage_misaligned` | 3 | 0.0269% |
| `load--sv48--l3-pointer--l2-leaf_rwx_u0--leaf-l2--E_Load_Access_Fault--data_read_pma_access_fault` | 3 | 0.0269% |
| `load--sv48--l3-pointer--l2-pointer--no-leaf--E_Load_Access_Fault--pte_read_pma_access_fault` | 3 | 0.0269% |
| `load--sv48--l3-pointer--l2-invalid_reserved_nonzero--no-leaf--E_Load_Page_Fault--reserved_nonzero` | 2 | 0.0179% |
| `load--sv48--l3-pointer--l2-leaf_r-x_u0--leaf-l2--E_Load_Page_Fault--superpage_misaligned` | 2 | 0.0179% |
| `load--sv48--l3-pointer--l2-leaf_rw-_u0--leaf-l2--E_Load_Page_Fault--superpage_misaligned` | 2 | 0.0179% |
| `load--sv48--l3-pointer--l2-leaf_rwx_u0--leaf-l2--E_Load_Page_Fault--superpage_misaligned` | 2 | 0.0179% |
| `load--sv48--l3-invalid_reserved_nonzero--no-leaf--E_Load_Page_Fault--reserved_nonzero` | 1 | 0.0090% |
| `load--sv48--l3-leaf_--x_u1--leaf-l3--E_Load_Page_Fault--load_permission` | 1 | 0.0090% |
| `load--sv48--l3-leaf_r--_u0--leaf-l3--Retire_Success--success` | 1 | 0.0090% |
| `load--sv48--l3-leaf_r--_u1--leaf-l3--E_Load_Page_Fault--accessed_update_disabled` | 1 | 0.0090% |
| `load--sv48--l3-leaf_r--_u1--leaf-l3--Retire_Success--success` | 1 | 0.0090% |
| `load--sv48--l3-leaf_r-x_u1--leaf-l3--E_Load_Access_Fault--data_read_pma_access_fault` | 1 | 0.0090% |
| `load--sv48--l3-leaf_r-x_u1--leaf-l3--Retire_Success--success` | 1 | 0.0090% |
| `load--sv48--l3-leaf_rw-_u0--leaf-l3--E_Load_Access_Fault--data_read_pma_access_fault` | 1 | 0.0090% |
| `load--sv48--l3-leaf_rw-_u0--leaf-l3--Retire_Success--success` | 1 | 0.0090% |
| `load--sv48--l3-leaf_rw-_u1--leaf-l3--E_Load_Page_Fault--accessed_update_disabled` | 1 | 0.0090% |
| `load--sv48--l3-leaf_rw-_u1--leaf-l3--Retire_Success--success` | 1 | 0.0090% |
| `load--sv48--l3-leaf_rwx_u0--leaf-l3--E_Load_Page_Fault--superpage_misaligned` | 1 | 0.0090% |
| `load--sv48--l3-leaf_rwx_u1--leaf-l3--E_Load_Access_Fault--data_read_pma_access_fault` | 1 | 0.0090% |
| `load--sv48--l3-leaf_rwx_u1--leaf-l3--E_Load_Page_Fault--accessed_update_disabled` | 1 | 0.0090% |
| `load--sv48--l3-leaf_rwx_u1--leaf-l3--Retire_Success--success` | 1 | 0.0090% |
| `load--sv48--l3-pointer--l2-invalid_write_without_read--no-leaf--E_Load_Page_Fault--write_without_read` | 1 | 0.0090% |
| `load--sv48--l3-pointer--l2-leaf_--x_u0--leaf-l2--E_Load_Page_Fault--load_permission` | 1 | 0.0090% |
| `load--sv48--l3-pointer--no-leaf--E_Load_Access_Fault--pte_read_pma_access_fault` | 1 | 0.0090% |

## 结果类别

| 类别 | 计数 | 占比 |
| --- | ---: | ---: |
| Retire_Success | 5174 | 46.3537% |
| E_Load_Access_Fault | 3467 | 31.0607% |
| E_Load_Page_Fault | 2521 | 22.5856% |

## 叶子层（包括叶子处失败）

| 类别 | 计数 | 占比 |
| --- | ---: | ---: |
| L0 | 9125 | 81.7506% |
| L1 | 1338 | 11.9871% |
| 无叶子 | 531 | 4.7572% |
| L2 | 154 | 1.3797% |
| L3 | 14 | 0.1254% |

位约束仅由本形状的已导出样本推断，非求解器约束；free 位不可独立任意组合。
