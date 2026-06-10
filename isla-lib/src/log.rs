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

use std::sync::atomic::{AtomicU32, Ordering::*};

pub static FLAGS: AtomicU32 = AtomicU32::new(0);

pub fn color(tid: usize) -> &'static str {
    match tid % 14 {
        0 => "\x1b[91m",
        1 => "\x1b[92m",
        2 => "\x1b[93m",
        3 => "\x1b[94m",
        4 => "\x1b[95m",
        5 => "\x1b[96m",
        6 => "\x1b[97m",
        7 => "\x1b[91m\x1b[4m",
        8 => "\x1b[92m\x1b[4m",
        9 => "\x1b[93m\x1b[4m",
        10 => "\x1b[94m\x1b[4m",
        11 => "\x1b[95m\x1b[4m",
        12 => "\x1b[96m\x1b[4m",
        13 => "\x1b[97m\x1b[4m",
        _ => unreachable!(),
    }
}

macro_rules! define_log_flags {
    ($( $(#[$meta:meta])* $name:ident = ($value:expr, $debug_flag:expr, $label:expr); )+) => {
        $(
            $(#[$meta])*
            pub const $name: u32 = $value;
        )+

        pub fn flags_from_debug_opts(debug_opts: &str) -> u32 {
            let mut flags = 0u32;

            $(
                if let Some(debug_flag) = $debug_flag {
                    if debug_opts.contains(debug_flag) {
                        flags |= $name;
                    }
                }
            )+

            flags
        }

        pub fn flag_label(flags: u32) -> String {
            let mut labels = Vec::new();

            $(
                if flags & $name > 0 {
                    labels.push($label);
                }
            )+

            if labels.is_empty() {
                format!("0x{:x}", flags)
            } else {
                labels.join("|")
            }
        }
    };
}

define_log_flags! {
    VERBOSE = (1u32, None::<char>, "VERBOSE");
    MEMORY = (2u32, Some('m'), "MEMORY");
    FORK = (4u32, Some('f'), "FORK");
    LITMUS = (8u32, Some('l'), "LITMUS");
    PROBE = (16u32, Some('p'), "PROBE");
    CACHE = (32u32, Some('c'), "CACHE");
    GRAPH = (64u32, Some('g'), "GRAPH");
    /// 符号执行引擎层 — 参数生成、solver 状态、执行流程控制等
    SYM_EXEC = (128u32, Some('s'), "SYM_EXEC");
    /// 执行路径结果层 — 每条路径的寄存器/汇编/model 求解结果
    PATH_RESULT = (256u32, Some('r'), "PATH_RESULT");
    /// 架构信息层 — xlen 检测、ISA 状态列表、Target 配置
    ARCH_INFO = (512u32, Some('a'), "ARCH_INFO");
}

pub fn set_flags(flags: u32) {
    FLAGS.store(flags, SeqCst);
}

#[macro_export]
macro_rules! log {
    ($flags: expr, $msg: expr) => {{
        let flags = $flags;
        if log::FLAGS.load(std::sync::atomic::Ordering::Relaxed) & flags > 0u32 {
            eprintln!("[{}]: {}", log::flag_label(flags), $msg)
        }
    }};
}

#[macro_export]
macro_rules! log_from {
    ($tid: expr, $flags: expr, $msg: expr) => {{
        let flags = $flags;
        if log::FLAGS.load(std::sync::atomic::Ordering::Relaxed) & flags > 0u32 {
            eprintln!("[{}{:<3}\x1b[0m][{}]: {}", log::color($tid), $tid, log::flag_label(flags), $msg)
        }
    }};
}

#[macro_export]
macro_rules! if_logging {
    ($flags: expr, $body:block) => {
        if log::FLAGS.load(std::sync::atomic::Ordering::Relaxed) & $flags > 0u32 $body
    };
}
