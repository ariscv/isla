# AGENTS.md

- 所有的回答、书写的文档都必须使用中文
- make run为验收功能使用的命令，输出在output/
- 不要额外地在未使用的变量前面加下划线
- 测试命令`RUST_BACKTRACE=1 cargo run --bin isarch --release -- -A ./rv64d.ir -C ./configs/riscv64_difftest.toml --verbose --probe-all --trace-all list-instructions`