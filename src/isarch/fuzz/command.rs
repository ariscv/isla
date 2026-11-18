//! scheduler 的任务工作目录由运行时决定；只展开命令参数里的 @/，不自行调度。
fn main() {
    let cwd = std::env::current_dir().unwrap();
    let mut args = std::env::args().skip(1).map(|arg| match arg.strip_prefix("@/") {
        Some(relative) => cwd.join(relative).to_str().unwrap().to_owned(),
        None => arg,
    });
    let program = args.next().expect("需要被执行的 Rust 命令");
    let mut command = std::process::Command::new(program);
    command.args(args);
    if let Some(relative) = std::env::var_os("ISARCH_TOOLCHAIN") {
        let root = cwd.join(relative);
        assert!(root.is_dir(), "声明的工具链目录不存在");
        command.env("ISARCH_TOOLCHAIN", &root);
        command.env("GCC_EXEC_PREFIX", format!("{}/", root.join("lib/gcc").display()));
        command.env("COMPILER_PATH", root.join("riscv64-unknown-elf/bin"));
        command.env("LD_LIBRARY_PATH", root.join("host-libs"));
    }
    let status = command.status().expect("无法启动任务");
    std::process::exit(status.code().unwrap_or(125));
}
