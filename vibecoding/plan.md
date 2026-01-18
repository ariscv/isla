完成cargo run --bin isarch --release -- -A ./rv32d.ir -C ./configs/riscv32.toml tree命令的实现。
在isla-lib/src/isarch.rs中“符号执行部分”，用start_single来符号执行，追踪jump指令产生的分支情况，遇到各种类型的函数调用要递归、嵌套地符号执行进去。