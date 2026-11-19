// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
//
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
//
// 1. Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the following disclaimer in the
// documentation and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

use std::path::Path;
use std::process::Command;

#[cfg(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu"))]
#[path = "src/smt/z3_version.rs"]
mod z3_version;

fn git_version() -> Option<String> {
    let output = Command::new("git").args(["describe", "--dirty"]).output().ok()?;
    if !output.status.success() {
        return None;
    }
    String::from_utf8(output.stdout).ok()
}

fn version() -> String {
    match git_version() {
        None => {
            let mut s = String::from("v");
            s.push_str(env!("CARGO_PKG_VERSION"));
            s
        }
        Some(version) => version,
    }
}

#[cfg(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu"))]
fn configure_z3() {
    use std::env;
    use std::os::raw::c_uint;
    use std::path::PathBuf;

    println!("cargo:rerun-if-changed=.");
    println!("cargo:rerun-if-env-changed=ISLA_Z3_PREFIX");
    println!("cargo:rerun-if-env-changed=HOME");
    let prefix = match env::var_os("ISLA_Z3_PREFIX") {
        Some(prefix) => PathBuf::from(prefix),
        None => PathBuf::from(env::var_os("HOME").expect("请用 Cargo 配置 env.ISLA_Z3_PREFIX 指定 Z3 安装前缀"))
            .join(".local/opt/z3-official-d6c9b4fbb"),
    };
    assert!(prefix.is_absolute(), "Z3 安装前缀必须是绝对路径：{}", prefix.display());
    let lib_dir = prefix.join("lib");
    let library = lib_dir.join("libz3.so");
    println!("cargo:rerun-if-changed={}", library.display());
    let real_library = library.canonicalize().unwrap_or_else(|error| {
        panic!(
            "找不到 Z3 共享库 {}：{error}。请安装官方 Z3，或用 Cargo 配置 env.ISLA_Z3_PREFIX 指定前缀",
            library.display()
        )
    });
    println!("cargo:rerun-if-changed={}", real_library.display());

    // 在构建期读取实际共享库的版本。
    let version = unsafe {
        let lib = libloading::Library::new(&real_library)
            .unwrap_or_else(|error| panic!("无法加载 Z3 共享库 {}：{error}", real_library.display()));
        let get_version = lib
            .get::<unsafe extern "C" fn(*mut c_uint, *mut c_uint, *mut c_uint, *mut c_uint)>(b"Z3_get_version\0")
            .unwrap_or_else(|error| panic!("Z3 共享库 {} 缺少 Z3_get_version：{error}", real_library.display()));
        let mut version = (0, 0, 0, 0);
        get_version(&mut version.0, &mut version.1, &mut version.2, &mut version.3);
        version
    };
    let (major, minor, build, revision) = version;
    let (min_major, min_minor, min_build, min_revision) = z3_version::MIN_Z3_VERSION;
    assert!(version >= z3_version::MIN_Z3_VERSION,
        "Z3 共享库 {} 的版本 {major}.{minor}.{build}.{revision} 低于最低版本 {min_major}.{min_minor}.{min_build}.{min_revision}",
        real_library.display());

    let lib_dir = lib_dir.to_str().expect("Z3 安装路径必须是 UTF-8");
    println!("cargo:rustc-link-search=native={lib_dir}");
    println!("cargo:rustc-link-arg=-Wl,-rpath,{lib_dir}");
    // Cargo 不会把 rustc-link-arg 传给依赖方。由生成可执行文件的包设置 RUNPATH。
    println!("cargo:lib_dir={lib_dir}");
}

fn main() {
    match (std::env::var("HOST").unwrap().as_str(), std::env::var("TARGET").unwrap().as_str()) {
        #[cfg(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu"))]
        ("x86_64-unknown-linux-gnu", "x86_64-unknown-linux-gnu") => configure_z3(),
        _ => println!("cargo:rustc-link-search=.."),
    }
    lalrpop::process_root().unwrap();

    // On macos, libz3 might be installed via homebrew
    if cfg!(target_os = "macos") && cfg!(target_arch = "aarch64") {
        let homebrew_lib_dir = Path::new("/opt/homebrew/lib");
        if homebrew_lib_dir.exists() {
            println!("cargo:rustc-link-search=/opt/homebrew/lib")
        }
    }

    println!("cargo:rustc-env=ISLA_VERSION={}", version());
}
