# list-instructions 测试

## 数据流

```
expected_data/*.py  →  extract_sail_clauses.py generate  →  expected/*.txt  →  与 CLI 输出比对
```

- `expected_data/*.py`：每个文件定义一个 Sail clause 对应的预期数据（汇编名等）。
- **`extract_sail_clauses.py`**（入口文件）：提供 `generate` 和 `verify` 子命令，读取 `expected_data/*.py` 生成 txt 或比对 CLI 输出。
- `expected/clause_names.txt`、`expected/assembly_names.txt`、`expected/summary.txt`：测试直接比对的目标文件。

## 测试脚本中的使用方式

测试入口为上层目录的 **`test_isarch_cli.sh`**，其中与 list-instructions 相关的测试项：

- **数量比对**（`t_list_instructions_clause_count`）：读取 `clause_names.txt` 的行数，与 CLI 输出中的 clause 数量比较。
- **集合级比对**（`t_list_instructions_assembly_names`）：调用 `extract_sail_clauses.py verify` 对 CLI 输出做集合检查。
- **漂移检测**（`t_expected_files_fresh`）：重新 generate txt 文件，与已提交版本 diff，防止数据不同步。
