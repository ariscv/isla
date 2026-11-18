//! 可搬移工具链启动器；仅替换动态加载器，不参与输入生成或调度。
use std::os::unix::process::CommandExt;
use std::{env, path::PathBuf, process::Command};
fn main() {
    let mut arguments = env::args_os();
    let invoked = PathBuf::from(arguments.next().expect("缺少工具名称"));
    let root = PathBuf::from(env::var_os("ISARCH_TOOLCHAIN").expect("未声明工具链目录"));
    let root = if root.is_absolute() { root } else { env::current_dir().unwrap().join(root) };
    let invoked = if invoked.is_absolute() { invoked } else { env::current_dir().unwrap().join(invoked) };
    let relative = invoked.strip_prefix(&root).expect("工具别名必须位于工具链内");
    let real = root.join("real").join(relative);
    assert!(real.is_file(), "工具实体不存在：{}", real.display());
    let error = Command::new(root.join("host-libs/ld-linux-x86-64.so.2"))
        .arg("--library-path")
        .arg(root.join("host-libs"))
        .arg(real)
        .args(arguments)
        .exec();
    panic!("启动工具失败：{error}");
}
