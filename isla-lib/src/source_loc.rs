// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
// Copyright (c) 2020 Brian Campbell
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

use std::cmp;
use std::convert::TryInto;
use std::path::Path;

use serde::{Deserialize, Serialize};

pub static RED: &str = "\x1b[0;31m";
pub static GREEN: &str = "\x1b[0;32m";
pub static BLUE: &str = "\x1b[0;34m";
pub static NO_COLOR: &str = "\x1b[0m";

/// 以源码文件名和半开起止位置描述一个 region，并在 IR 文件表可用后解析为 [`SourceRegion`]。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceRegionSpec {
    file: String,
    start: (u32, u16),
    end: (u32, u16),
}

impl SourceRegionSpec {
    pub fn new(file: impl Into<String>, start: (u32, u16), end: (u32, u16)) -> Self {
        SourceRegionSpec { file: file.into(), start, end }
    }

    pub fn resolve(&self, files: &[&str]) -> Option<SourceRegion> {
        assert!(
            !self.file.is_empty() && self.start.0 > 0 && self.end.0 > 0 && self.start <= self.end,
            "SourceRegion span 非法: {} {}:{} - {}:{}",
            self.file,
            self.start.0,
            self.start.1,
            self.end.0,
            self.end.1
        );

        let mut matches = files.iter().enumerate().filter(|(_, file)| **file == self.file);
        let (file_index, _) = matches.next()?;
        assert!(matches.next().is_none(), "SourceRegion 文件重复: {}", self.file);
        let file_index = i16::try_from(file_index).expect("SourceLoc 文件索引超过 i16 范围");

        Some(SourceRegion::new(file_index, self.start, self.end))
    }
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct SourceLoc {
    file: i16,
    line1: u32,
    char1: u16,
    line2: u32,
    char2: u16,
}

/// 同一源码文件中由明确起点和终点定义的半开区间 `[start, end)`。
///
/// 它只描述静态源码范围，不包含调用栈或运行时控制流语义。
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct SourceRegion {
    file: i16,
    start: (u32, u16),
    end: (u32, u16),
}

impl SourceRegion {
    pub fn new(file: i16, start: (u32, u16), end: (u32, u16)) -> Self {
        assert!(file >= 0, "SourceRegion 必须使用已知源码文件");
        assert!(start.0 > 0 && end.0 > 0, "SourceRegion 行号必须大于 0");
        assert!(start <= end, "SourceRegion 起点不能晚于终点");
        SourceRegion { file, start, end }
    }

    pub fn from_source_loc(source_location: SourceLoc) -> Self {
        SourceRegion::new(
            source_location.file,
            (source_location.line1, source_location.char1),
            (source_location.line2, source_location.char2),
        )
    }

    pub fn file(self) -> i16 {
        self.file
    }

    pub fn start(self) -> (u32, u16) {
        self.start
    }

    pub fn end(self) -> (u32, u16) {
        self.end
    }

    fn source_span(self, source_location: SourceLoc) -> Option<((u32, u16), (u32, u16))> {
        if source_location.file < 0 || source_location.file != self.file {
            return None;
        }

        let start = (source_location.line1, source_location.char1);
        let end = (source_location.line2, source_location.char2);
        assert!(start.0 > 0 && end.0 > 0, "SourceLoc 行号必须大于 0");
        assert!(start <= end, "SourceLoc 起点不能晚于终点");
        Some((start, end))
    }

    /// 判断 `source_location` 是否与 region 共享至少一个源码字符。
    ///
    /// Sail 和 Isla IR 的源码位置使用半开区间，因此仅在端点相接不算重叠。
    pub fn overlaps(self, source_location: SourceLoc) -> bool {
        let Some((start, end)) = self.source_span(source_location) else { return false };
        self.start < end && start < self.end
    }

    /// 判断一个 IR SourceLoc 是否应被该 region 选择器选中。
    ///
    /// 该方法在普通半开区间重叠的基础上，排除严格包围整个 region 的外层 IR
    /// SourceLoc。它用于从嵌套语法块中选择内层 IR，不是普通的 in-region 判定；
    /// 普通 in-region 判定应使用 [`SourceRegion::overlaps`]。
    pub fn selects_ir_location(self, source_location: SourceLoc) -> bool {
        let Some((start, end)) = self.source_span(source_location) else { return false };
        let overlaps = self.start < end && start < self.end;
        let encloses_region = start <= self.start && self.end <= end;
        let equals_region = start == self.start && end == self.end;

        overlaps && (!encloses_region || equals_region)
    }
}

impl SourceLoc {
    pub fn unknown() -> Self {
        SourceLoc { file: -1, line1: 0, char1: 0, line2: 0, char2: 0 }
    }

    pub fn is_unknown(self) -> bool {
        self.file == -1
    }

    pub(crate) fn unknown_unique(n: u32) -> Self {
        SourceLoc { file: -1, line1: n, char1: 0, line2: 0, char2: 0 }
    }

    pub fn command_line() -> Self {
        SourceLoc { file: -2, line1: 0, char1: 0, line2: 0, char2: 0 }
    }

    pub fn new(file: i16, line1: u32, char1: u16, line2: u32, char2: u16) -> Self {
        if file < 0 {
            SourceLoc::unknown()
        } else {
            SourceLoc { file, line1, char1, line2, char2 }
        }
    }

    fn canonicalize(self) -> Self {
        if self.line1 > self.line2 {
            SourceLoc { line1: self.line2, line2: self.line1, ..self }
        } else if self.line1 == self.line2 && self.char1 > self.char2 {
            SourceLoc { char1: self.char2, char2: self.char1, ..self }
        } else {
            self
        }
    }

    fn one_line_message(
        self,
        buf: &str,
        message: &str,
        file_info: &str,
        red: &str,
        blue: &str,
        no_color: &str,
    ) -> String {
        let mut line = "";

        for (n, l) in buf.lines().enumerate() {
            if n == (self.line1 - 1) as usize {
                line = l;
                break;
            };
        }

        let line_number = self.line1.to_string();
        let number_column_width = line_number.len();

        let file_info = format!("{:width$}{}", "", file_info, width = number_column_width);
        let extra_padding = format!("{:width$} {}|{}", "", blue, no_color, width = number_column_width);

        let line_display =
            format!("{}{:>width$} |{} {}", blue, line_number, no_color, line, width = number_column_width);
        let line_marker = {
            let dashes = "-".repeat(self.char2.saturating_sub(self.char1 + 2) as usize);
            let highlight = if self.char1 + 1 < self.char2 { format!("^{}^", dashes) } else { "^".to_string() };
            format!(
                "{:width$} {}|{} {:gap$}{}{}{}",
                "",
                blue,
                no_color,
                "",
                red,
                highlight,
                no_color,
                width = number_column_width,
                gap = (self.char1 as usize)
            )
        };

        format!("{}{}\n{}\n{}\n{}", message, file_info, extra_padding, line_display, line_marker,)
    }

    fn two_line_message(
        self,
        buf: &str,
        message: &str,
        file_info: &str,
        red: &str,
        blue: &str,
        no_color: &str,
    ) -> String {
        let mut line1 = "";
        let mut line2 = "";

        for (n, line) in buf.lines().enumerate() {
            if n == (self.line1 - 1) as usize {
                line1 = line
            };
            if n == (self.line2 - 1) as usize {
                line2 = line;
                break;
            };
        }

        let line1_number = self.line1.to_string();
        let line2_number = self.line2.to_string();
        let number_column_width = cmp::max(line1_number.len(), line2_number.len());

        let file_info = format!("{:width$}{}", "", file_info, width = number_column_width);
        let extra_padding = format!("{:width$} {}|{}", "", blue, no_color, width = number_column_width);

        let line1_display =
            format!("{}{:>width$} |{} {}", blue, line1_number, no_color, line1, width = number_column_width);
        let line1_marker = {
            let dashes = if usize::from(self.char1) >= line1.len() {
                "".to_string()
            } else {
                "-".repeat(line1.len() - (self.char1 as usize + 1))
            };
            format!(
                "{:width$} {}|{} {:gap$}{}^{}{}",
                "",
                blue,
                no_color,
                "",
                red,
                dashes,
                no_color,
                width = number_column_width,
                gap = (self.char1 as usize)
            )
        };

        let inbetween_marker =
            if self.line1 + 1 < self.line2 { format!("{}...{}\n", blue, no_color) } else { "".to_string() };

        let line2_display =
            format!("{}{:>width$} |{} {}", blue, line2_number, no_color, line2, width = number_column_width);
        let line2_marker = {
            let dashes = if self.char2 <= 1 { "".to_string() } else { "-".repeat(self.char2 as usize - 1) };
            format!("{:width$} {}|{} {}{}^{}", "", blue, no_color, red, dashes, no_color, width = number_column_width)
        };

        format!(
            "{}{}\n{}\n{}\n{}\n{}{}\n{}",
            message,
            file_info,
            extra_padding,
            line1_display,
            line1_marker,
            inbetween_marker,
            line2_display,
            line2_marker,
        )
    }

    fn message_str(self, buf: &str, message: &str, file_info: &str, red: &str, blue: &str, no_color: &str) -> String {
        if self.line1 == self.line2 {
            self.canonicalize().one_line_message(buf, message, file_info, red, blue, no_color)
        } else {
            self.canonicalize().two_line_message(buf, message, file_info, red, blue, no_color)
        }
    }

    pub fn location_string(self, files: &[&str]) -> String {
        if let Some(file) = TryInto::<usize>::try_into(self.file).ok().and_then(|i| files.get(i)) {
            format!("{} {}:{} - {}:{}", file, self.line1, self.char1, self.line2, self.char2)
        } else {
            format!("{}:{} - {}:{}", self.line1, self.char1, self.line2, self.char2)
        }
    }

    pub fn message_file_contents(
        self,
        buf_name: &str,
        buf: &str,
        message: &str,
        is_error: bool,
        use_colors: bool,
    ) -> String {
        let red = if use_colors && is_error {
            RED
        } else if use_colors {
            GREEN
        } else {
            ""
        };
        let blue = if use_colors { BLUE } else { "" };
        let no_color = if use_colors { NO_COLOR } else { "" };

        let file_info = format!("{}-->{} {}:{}:{}", blue, no_color, buf_name, self.line1, self.char1);

        self.message_str(buf, &format!("{}error{}: {}\n", red, no_color, message), &file_info, red, blue, no_color)
    }

    /// Print a message associated with an original source code
    /// location. It takes a base directory and a list of source file
    /// paths relative to that base directory. The file index in the
    /// location will then be used to choose while file to read.
    pub fn message<P: AsRef<Path>>(
        self,
        dir: Option<P>,
        files: &[&str],
        message: &str,
        is_error: bool,
        use_colors: bool,
    ) -> String {
        let red = if use_colors && is_error {
            RED
        } else if use_colors {
            GREEN
        } else {
            ""
        };
        let blue = if use_colors { BLUE } else { "" };
        let no_color = if use_colors { NO_COLOR } else { "" };

        let (short_error, error_sep) = if is_error {
            (format!("{}error{}: {}", red, no_color, message), "\n")
        } else {
            (message.to_string(), "\n")
        };

        let file = TryInto::<usize>::try_into(self.file).ok().and_then(|i| files.get(i));
        if file.is_none() {
            return short_error;
        }
        let file_info = format!("{}-->{} {}:{}:{}", blue, no_color, file.unwrap(), self.line1, self.char1);

        if let Some(dir) = dir {
            let path = dir.as_ref().join(file.unwrap());
            if !path.is_file() {
                return format!("{}{} {}", short_error, error_sep, file_info);
            }

            if let Ok(buf) = std::fs::read_to_string(&path) {
                self.message_str(&buf, &format!("{}{}", short_error, error_sep), &file_info, red, blue, no_color)
            } else {
                format!("{}{} {}", short_error, error_sep, file_info)
            }
        } else {
            format!("{}{} {}", short_error, error_sep, file_info)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::ir::{Def, Instr, Name, Symtab};
    use crate::{ir_lexer, ir_parser};

    fn instruction_source_loc(instruction: &Instr<Name, B64>) -> Option<SourceLoc> {
        match instruction {
            Instr::Decl(_, _, info)
            | Instr::Init(_, _, _, info)
            | Instr::Jump(_, _, info)
            | Instr::Copy(_, _, info)
            | Instr::Monomorphize(_, _, info)
            | Instr::Call(_, _, _, _, info)
            | Instr::PrimopUnary(_, _, _, info)
            | Instr::PrimopBinary(_, _, _, _, info)
            | Instr::PrimopVariadic(_, _, _, info)
            | Instr::PrimopReset(_, _, info)
            | Instr::Exit(_, info) => Some(*info),
            Instr::Goto(_) | Instr::Arbitrary | Instr::End => None,
        }
    }

    fn verify_generated_source_region_ir(ir: &str) {
        let mut symtab = Symtab::new();
        let defs: Vec<Def<Name, B64>> = ir_parser::IrParser::new()
            .parse(&mut symtab, ir_lexer::new_ir_lexer(ir))
            .expect("source region fixture IR 解析失败");
        let file = symtab
            .files()
            .iter()
            .position(|file| *file == "source_region_foreach_match.unsat.sail")
            .expect("fixture IR files 表缺少 Sail 源文件");
        let file = i16::try_from(file).expect("fixture IR 文件索引超过 i16 范围");
        let prop = symtab.lookup("zprop");
        let instructions = defs
            .iter()
            .find_map(|def| match def {
                Def::Fn(function, _, instructions) if *function == prop => Some(instructions),
                _ => None,
            })
            .expect("fixture IR 缺少 zprop 函数");

        let region = SourceRegion::new(file, (12, 4), (19, 5));
        let foreach_jump = SourceLoc::new(file, 11, 2, 21, 3);
        let match_jump = SourceLoc::new(file, 12, 4, 19, 5);
        let after_match_jump = SourceLoc::new(file, 20, 4, 20, 40);
        let expected_internal_locations = [
            SourceLoc::new(file, 14, 8, 14, 23),
            SourceLoc::new(file, 14, 17, 14, 23),
            SourceLoc::new(file, 17, 8, 17, 23),
            SourceLoc::new(file, 17, 17, 17, 23),
        ];
        let jumps: Vec<_> = instructions
            .iter()
            .filter_map(|instruction| match instruction {
                Instr::Jump(_, _, info) => Some(*info),
                _ => None,
            })
            .collect();
        let locations: Vec<_> = instructions.iter().filter_map(instruction_source_loc).collect();

        assert!(jumps.contains(&foreach_jump));
        assert!(jumps.contains(&match_jump));
        assert!(jumps.contains(&after_match_jump));
        assert!(instructions
            .iter()
            .enumerate()
            .any(|(pc, instruction)| matches!(instruction, Instr::Goto(target) if *target < pc)));
        assert!(region.overlaps(foreach_jump));
        assert!(!region.selects_ir_location(foreach_jump));
        assert!(region.selects_ir_location(match_jump));
        assert!(!region.selects_ir_location(after_match_jump));
        assert!(expected_internal_locations
            .into_iter()
            .all(|expected| locations.contains(&expected) && region.selects_ir_location(expected)));
    }

    #[test]
    fn source_region_generated_ir_matches_fixture() {
        let ir = match std::env::var_os("ISLA_SOURCE_REGION_TEST_IR") {
            Some(path) => std::fs::read_to_string(path).expect("读取动态生成的 source region IR 失败"),
            None => include_str!("../tests/fixtures/source_region_foreach_match.ir").to_string(),
        };

        verify_generated_source_region_ir(&ir);
    }

    #[test]
    fn source_region_spec_resolves_exact_file_name() {
        let files = ["core/types.sail", "extensions/V/vext_arith_insts.sail"];
        let spec = SourceRegionSpec::new("extensions/V/vext_arith_insts.sail", (186, 6), (192, 7));

        assert_eq!(spec.resolve(&files), Some(SourceRegion::new(1, (186, 6), (192, 7))));
    }

    #[test]
    fn source_region_spec_missing_file_resolves_to_no_matching_region() {
        let files = ["extensions/V/vext_utils_insts.sail"];
        let spec = SourceRegionSpec::new("extensions/V/vext_arith_insts.sail", (186, 6), (192, 7));

        assert_eq!(spec.resolve(&files), None);
    }

    #[test]
    #[should_panic(expected = "SourceRegion 文件重复")]
    fn source_region_spec_rejects_duplicate_file() {
        let files = ["extensions/V/vext_arith_insts.sail", "extensions/V/vext_arith_insts.sail"];
        SourceRegionSpec::new("extensions/V/vext_arith_insts.sail", (186, 6), (192, 7)).resolve(&files);
    }

    #[test]
    #[should_panic(expected = "SourceRegion span 非法")]
    fn source_region_spec_rejects_reversed_span() {
        let files = ["extensions/V/vext_arith_insts.sail"];
        SourceRegionSpec::new("extensions/V/vext_arith_insts.sail", (192, 7), (186, 6)).resolve(&files);
    }

    #[test]
    fn source_region_overlaps_half_open_ranges_by_line_then_column() {
        let region = SourceRegion::new(1, (10, 5), (20, 8));

        assert_eq!(region.file(), 1);
        assert_eq!(region.start(), (10, 5));
        assert_eq!(region.end(), (20, 8));
        assert_eq!(SourceRegion::from_source_loc(SourceLoc::new(1, 10, 5, 20, 8)), region);

        assert!(region.overlaps(SourceLoc::new(1, 10, 5, 20, 8)));
        assert!(region.overlaps(SourceLoc::new(1, 10, 6, 20, 7)));
        assert!(region.overlaps(SourceLoc::new(1, 9, 0, 10, 6)));
        assert!(region.overlaps(SourceLoc::new(1, 20, 7, 21, 0)));

        assert!(!region.overlaps(SourceLoc::new(1, 9, 0, 10, 5)));
        assert!(!region.overlaps(SourceLoc::new(1, 20, 8, 21, 0)));
    }

    #[test]
    fn source_region_rejects_disjoint_or_enclosing_locations() {
        let region = SourceRegion::new(1, (10, 5), (20, 8));

        assert!(!region.selects_ir_location(SourceLoc::new(1, 9, 0, 10, 4)));
        assert!(!region.selects_ir_location(SourceLoc::new(1, 20, 9, 21, 0)));
        assert!(!region.selects_ir_location(SourceLoc::new(1, 9, 0, 21, 0)));
        assert!(!region.selects_ir_location(SourceLoc::new(2, 10, 5, 20, 8)));
        assert!(!region.selects_ir_location(SourceLoc::unknown()));
    }

    #[test]
    fn source_region_selects_match_ir_and_excludes_enclosing_foreach_ir() {
        let source = include_str!("../../test/property/source_region_foreach_match.unsat.sail");
        let lines: Vec<_> = source.lines().collect();
        assert_eq!(lines[10], "  foreach (i from 0 to a) {");
        assert_eq!(lines[11], "    match x {");
        assert_eq!(lines[13], "        result = i >= 0");
        assert_eq!(lines[16], "        result = i >= 0");
        assert_eq!(lines[19], "    if i == 0 then return result else ()");

        // 由上述 property fixture 编译出的 IR SourceLoc：
        // foreach jump: 11:2-21:3, match jump: 12:4-19:5；a 是经过 assume(a > 0)
        // 约束的任意 int 参数，不具有有限上界。match 内部赋值落在 region 中，match 后的
        // return guard 不落在 region 中；IR 同时保留 foreach 回边。
        let region = SourceRegion::new(0, (12, 4), (19, 5));
        let foreach_jump = SourceLoc::new(0, 11, 2, 21, 3);
        let match_jump = SourceLoc::new(0, 12, 4, 19, 5);
        let match_statements = [
            SourceLoc::new(0, 14, 8, 14, 23),
            SourceLoc::new(0, 14, 17, 14, 23),
            SourceLoc::new(0, 17, 8, 17, 23),
            SourceLoc::new(0, 17, 17, 17, 23),
        ];
        let after_match_jump = SourceLoc::new(0, 20, 4, 20, 40);

        assert!(region.overlaps(foreach_jump));
        assert!(!region.selects_ir_location(foreach_jump));
        assert!(region.selects_ir_location(match_jump));
        assert!(match_statements.into_iter().all(|statement| region.selects_ir_location(statement)));
        assert!(!region.selects_ir_location(after_match_jump));
    }

    #[test]
    #[should_panic(expected = "SourceRegion 起点不能晚于终点")]
    fn source_region_rejects_reversed_range() {
        SourceRegion::new(1, (20, 8), (10, 5));
    }
}
