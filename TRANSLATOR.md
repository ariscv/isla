# 中英文术语对照

本文件是本工作区中英文术语对照的统一依据。编写提交说明、代码注释、文档和技术解释时，先查本文件；新增或修订术语时在这里维护。符号值取具体值的代码命名使用下列约定；已有公共 API 的改名需核对调用方。历史提交原文按其版本保留。

## 符号执行与求解

| 英文 | 中文 | 适用含义 |
| --- | --- | --- |
| symbolic value | 符号值 | 由符号变量或符号表达式表示的值。 |
| concrete value | 具体值 | 已确定的取值。 |
| concretize / concretization | 具体化 | 根据求解模型，为符号值取得具体值。 |
| materialize a symbolic value | 将符号值具体化 | 在本项目的符号执行语境中，与根据求解模型取得具体值相对应，不译为“物化符号值”。 |
| solver model / SMT model | 求解模型 / SMT 模型 | 满足当前约束的一组变量解释；与 Sail 的指令集模型区分。 |
| concretize the return value using the final solver model | 使用最终求解模型具体化返回值 | 例如在最终见证使用的同一个 `Model` 上调用 `model.get_val(ret_val)`，再格式化输出。 |

代码命名约定：

- 动作使用 `concretize`，过程使用 `concretization`。
- 具体值变量使用 `concrete_*`，例如 `concrete_ret_val`。
- 符号值求解场景优先使用上述词形，避免使用 `materialize/materialization`。
- `materialize` 若指延迟生成 SMT-LIB2 诊断文本，则是不同动作；现有 `TimeoutSmtDump::materialize` 等接口保留，中文说明使用“生成 SMT-LIB2 文本”。

提交说明示例：

```text
fix(solve): 使用最终求解模型具体化返回值
```
