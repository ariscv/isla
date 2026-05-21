// BSD 2-Clause License
//
// Copyright (c) 2026
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

use std::collections::HashMap;
use std::fs::File;
use std::io::{Error, Write};
use std::path::PathBuf;

use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;

use crate::bitvector::BV;
use crate::execution_tree::ExecutionTree;
use crate::smt::smtlib::{Def, Exp};
use crate::smt::{Event, Sym};
use serde_json::{json, Value};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CfgOutputFormat {
    Dot,
    Json,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CfgOutputConfig {
    pub format: CfgOutputFormat,
    pub output_path: Option<PathBuf>,
    pub expand_fork_condition: bool,
}

fn event_summary<B: BV>(events: &[Event<B>]) -> String {
    if events.is_empty() {
        return "(empty)".to_string();
    }
    let max_events = 5;
    let mut parts: Vec<String> = events
        .iter()
        .take(max_events)
        .map(|e| match e {
            Event::Smt(def, _, _) => match def {
                Def::DeclareConst(_, _) => "DeclConst".to_string(),
                Def::DefineConst(_, _) => "DefConst".to_string(),
                Def::DeclareFun(_, _, _) => "DeclFun".to_string(),
                Def::DefineEnum(_, _) => "DefEnum".to_string(),
                Def::Assert(_) => "Assert".to_string(),
            },
            Event::Fork(id, _, _, _) => format!("Fork#{}", id),
            Event::Function { name, call } => {
                if *call {
                    format!("Call({:?})", name)
                } else {
                    format!("Ret({:?})", name)
                }
            }
            Event::Abstract { name, .. } => format!("Abstract({:?})", name),
            Event::ReadReg(name, _, _) => format!("ReadReg({:?})", name),
            Event::WriteReg(name, _, _) => format!("WriteReg({:?})", name),
            Event::AssumeReg(name, _, _) => format!("AssumeReg({:?})", name),
            Event::ReadMem { bytes, .. } => format!("ReadMem({}B)", bytes),
            Event::WriteMem { bytes, .. } => format!("WriteMem({}B)", bytes),
            Event::MarkReg { .. } => "MarkReg".to_string(),
            Event::AddressAnnounce { .. } => "AddrAnn".to_string(),
            Event::Branch { .. } => "Branch".to_string(),
            Event::Cycle => "Cycle".to_string(),
            Event::Instr(_) => "Instr".to_string(),
            Event::Assume(_) => "Assume".to_string(),
            Event::AssumeFun { name, .. } => format!("AssumeFun({:?})", name),
            Event::UseFunAssumption { name, .. } => format!("UseFunAssume({:?})", name),
        })
        .collect();
    if events.len() > max_events {
        parts.push("...".to_string());
    }
    parts.join("\\n")
}

/// Format a SMTLIB expression as a human-readable string with sym substitution.
fn format_exp_sym(exp: &Exp<Sym>, subst: &HashMap<Sym, Exp<Sym>>) -> String {
    let resolved = expand_expression(exp, subst);
    format_exp(&resolved)
}

fn format_exp<V: std::fmt::Display + std::fmt::Debug>(exp: &Exp<V>) -> String {
    match exp {
        Exp::Var(v) => format!("{}", v),
        Exp::Bits(bits) => {
            let s: String = bits.iter().rev().map(|b| if *b { '1' } else { '0' }).collect();
            format!("0b{}", s)
        }
        Exp::Bits64(bv) => format!("0x{:0width$x}", bv.lower_u64(), width = (bv.len() as usize + 3) / 4),
        Exp::Enum(_) => "<enum>".to_string(),
        Exp::Bool(b) => format!("{}", b),
        Exp::Eq(a, b) => format!("({} = {})", format_exp(a), format_exp(b)),
        Exp::Neq(a, b) => format!("({} != {})", format_exp(a), format_exp(b)),
        Exp::And(a, b) => format!("({} & {})", format_exp(a), format_exp(b)),
        Exp::Or(a, b) => format!("({} | {})", format_exp(a), format_exp(b)),
        Exp::Not(a) => format!("!{}", format_exp(a)),
        Exp::Bvnot(a) => format!("~{}", format_exp(a)),
        Exp::Bvand(a, b) => format!("({} & {})", format_exp(a), format_exp(b)),
        Exp::Bvor(a, b) => format!("({} | {})", format_exp(a), format_exp(b)),
        Exp::Bvxor(a, b) => format!("({} ^ {})", format_exp(a), format_exp(b)),
        Exp::Bvneg(a) => format!("-{}", format_exp(a)),
        Exp::Bvadd(a, b) => format!("({} + {})", format_exp(a), format_exp(b)),
        Exp::Bvsub(a, b) => format!("({} - {})", format_exp(a), format_exp(b)),
        Exp::Bvmul(a, b) => format!("({} * {})", format_exp(a), format_exp(b)),
        Exp::Bvudiv(a, b) => format!("({} /u {})", format_exp(a), format_exp(b)),
        Exp::Bvsdiv(a, b) => format!("({} /s {})", format_exp(a), format_exp(b)),
        Exp::Bvult(a, b) => format!("({} <u {})", format_exp(a), format_exp(b)),
        Exp::Bvslt(a, b) => format!("({} <s {})", format_exp(a), format_exp(b)),
        Exp::Bvule(a, b) => format!("({} <=u {})", format_exp(a), format_exp(b)),
        Exp::Bvsle(a, b) => format!("({} <=s {})", format_exp(a), format_exp(b)),
        Exp::Extract(hi, lo, a) => format!("({}[{}:{}])", format_exp(a), hi, lo),
        Exp::ZeroExtend(n, a) => format!("(zext{} {})", n, format_exp(a)),
        Exp::SignExtend(n, a) => format!("(sext{} {})", n, format_exp(a)),
        Exp::Ite(c, t, e) => format!("(ite {} {} {})", format_exp(c), format_exp(t), format_exp(e)),
        Exp::Bvnand(a, b) => format!("({} ~(&) {})", format_exp(a), format_exp(b)),
        Exp::Bvnor(a, b) => format!("({} ~(|) {})", format_exp(a), format_exp(b)),
        Exp::Bvxnor(a, b) => format!("({} ~(^) {})", format_exp(a), format_exp(b)),
        Exp::Bvurem(a, b) => format!("({} %u {})", format_exp(a), format_exp(b)),
        Exp::Bvsrem(a, b) => format!("({} %s {})", format_exp(a), format_exp(b)),
        Exp::Bvsmod(a, b) => format!("({} %%s {})", format_exp(a), format_exp(b)),
        Exp::Bvuge(a, b) => format!("({} >=u {})", format_exp(a), format_exp(b)),
        Exp::Bvsge(a, b) => format!("({} >=s {})", format_exp(a), format_exp(b)),
        Exp::Bvugt(a, b) => format!("({} >u {})", format_exp(a), format_exp(b)),
        Exp::Bvsgt(a, b) => format!("({} >s {})", format_exp(a), format_exp(b)),
        Exp::Bvshl(a, b) => format!("({} << {})", format_exp(a), format_exp(b)),
        Exp::Bvlshr(a, b) => format!("({} >>u {})", format_exp(a), format_exp(b)),
        Exp::Bvashr(a, b) => format!("({} >>s {})", format_exp(a), format_exp(b)),
        Exp::Concat(a, b) => format!("({} ++ {})", format_exp(a), format_exp(b)),
        Exp::Select(a, b) => format!("(select {} {})", format_exp(a), format_exp(b)),
        Exp::Store(a, b, c) => format!("(store {} {} {})", format_exp(a), format_exp(b), format_exp(c)),
        Exp::Distinct(es) => {
            let arg_strs: Vec<String> = es.iter().map(format_exp).collect();
            format!("(distinct {})", arg_strs.join(" "))
        }
        Exp::App(f, args) => {
            let arg_strs: Vec<String> = args.iter().map(format_exp).collect();
            format!("(f{} {})", f, arg_strs.join(" "))
        }
        _ => format!("{:?}", exp),
    }
}

/// Recursively expand an expression by substituting known definitions.
fn expand_expression(exp: &Exp<Sym>, subst: &HashMap<Sym, Exp<Sym>>) -> Exp<Sym> {
    match exp {
        Exp::Var(sym) => {
            if let Some(replacement) = subst.get(sym) {
                expand_expression(replacement, subst)
            } else {
                exp.clone()
            }
        }
        Exp::Eq(a, b) => Exp::Eq(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Neq(a, b) => Exp::Neq(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::And(a, b) => Exp::And(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Or(a, b) => Exp::Or(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Not(a) => Exp::Not(Box::new(expand_expression(a, subst))),
        Exp::Extract(hi, lo, a) => Exp::Extract(*hi, *lo, Box::new(expand_expression(a, subst))),
        Exp::ZeroExtend(n, a) => Exp::ZeroExtend(*n, Box::new(expand_expression(a, subst))),
        Exp::SignExtend(n, a) => Exp::SignExtend(*n, Box::new(expand_expression(a, subst))),
        Exp::Ite(c, t, e) => Exp::Ite(
            Box::new(expand_expression(c, subst)),
            Box::new(expand_expression(t, subst)),
            Box::new(expand_expression(e, subst)),
        ),
        Exp::Bvnot(a) => Exp::Bvnot(Box::new(expand_expression(a, subst))),
        Exp::Bvneg(a) => Exp::Bvneg(Box::new(expand_expression(a, subst))),
        Exp::Bvand(a, b) => Exp::Bvand(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvor(a, b) => Exp::Bvor(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvxor(a, b) => Exp::Bvxor(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvnand(a, b) => Exp::Bvnand(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvnor(a, b) => Exp::Bvnor(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvxnor(a, b) => Exp::Bvxnor(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvadd(a, b) => Exp::Bvadd(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvsub(a, b) => Exp::Bvsub(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvmul(a, b) => Exp::Bvmul(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvudiv(a, b) => Exp::Bvudiv(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvsdiv(a, b) => Exp::Bvsdiv(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvurem(a, b) => Exp::Bvurem(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvsrem(a, b) => Exp::Bvsrem(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvsmod(a, b) => Exp::Bvsmod(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvult(a, b) => Exp::Bvult(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvslt(a, b) => Exp::Bvslt(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvule(a, b) => Exp::Bvule(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvsle(a, b) => Exp::Bvsle(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvuge(a, b) => Exp::Bvuge(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvsge(a, b) => Exp::Bvsge(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvugt(a, b) => Exp::Bvugt(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvsgt(a, b) => Exp::Bvsgt(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvshl(a, b) => Exp::Bvshl(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvlshr(a, b) => Exp::Bvlshr(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Bvashr(a, b) => Exp::Bvashr(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Concat(a, b) => Exp::Concat(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Select(a, b) => Exp::Select(Box::new(expand_expression(a, subst)), Box::new(expand_expression(b, subst))),
        Exp::Store(a, b, c) => Exp::Store(
            Box::new(expand_expression(a, subst)),
            Box::new(expand_expression(b, subst)),
            Box::new(expand_expression(c, subst)),
        ),
        Exp::Distinct(es) => Exp::Distinct(es.iter().map(|e| expand_expression(e, subst)).collect()),
        Exp::App(f, args) => Exp::App(*f, args.iter().map(|e| expand_expression(e, subst)).collect()),
        // leaf nodes or rare expression variants (FP*)
        _ => exp.clone(),
    }
}

/// Collect all DefineConst definitions from a node's events into a substitution map.
fn collect_definitions<B: BV>(events: &[Event<B>]) -> HashMap<Sym, Exp<Sym>> {
    let mut subst = HashMap::new();
    for event in events {
        if let Event::Smt(Def::DefineConst(sym, exp), _, _) = event {
            subst.insert(*sym, exp.clone());
        }
    }
    subst
}

/// Build a full substitution map by walking from root to each node.
fn build_subst_for_node<B: BV>(
    graph: &petgraph::graph::DiGraph<(), crate::execution_tree::TreeEdge>,
    nodes: &std::collections::HashMap<NodeIndex, std::sync::Arc<crate::execution_tree::NodeData<B>>>,
    target: NodeIndex,
) -> HashMap<Sym, Exp<Sym>> {
    let mut subst = HashMap::new();
    let mut path = Vec::new();
    let mut current = target;
    loop {
        path.push(current);
        match graph.neighbors_directed(current, petgraph::Direction::Incoming).next() {
            Some(parent) => current = parent,
            None => break,
        }
    }
    path.reverse();
    for node_idx in path {
        if let Some(data) = nodes.get(&node_idx) {
            let events = data.events.lock().unwrap();
            let node_subst = collect_definitions(&events);
            subst.extend(node_subst);
        }
    }
    subst
}

/// Format the condition label for an edge.
fn format_condition_label(
    edge: &crate::execution_tree::TreeEdge,
    config: &CfgOutputConfig,
    subst: &HashMap<Sym, Exp<Sym>>,
) -> String {
    let taken_str = if edge.taken { "T" } else { "F" };
    let cond_str = if config.expand_fork_condition {
        if let Some(ref expr) = edge.condition_expr {
            expr.clone()
        } else if let Some(sym) = edge.condition {
            format_exp_sym(&Exp::Var(sym), subst)
        } else {
            "???".to_string()
        }
    } else if let Some(sym) = edge.condition {
        format!("v{}", sym)
    } else {
        "???".to_string()
    };
    format!("fork#{} {}\\n{}", edge.fork_id, cond_str, taken_str)
}

/// Escape special DOT characters in a label string.
fn dot_escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"").replace('\n', "\\n")
}

pub fn output_cfg_dot<B: BV>(tree: &ExecutionTree<B>, config: &CfgOutputConfig) -> Result<(), Error> {
    let output_path = config
        .output_path
        .as_ref()
        .ok_or_else(|| Error::new(std::io::ErrorKind::InvalidInput, "missing cfg dot output path"))?;

    let graph = tree.read_graph();
    let nodes = tree.read_nodes();

    let mut file = File::create(output_path)?;
    writeln!(file, "digraph execution_tree {{")?;
    writeln!(file, "  rankdir=TB;")?;
    writeln!(file, "  node [shape=box, fontname=\"monospace\"];")?;

    for node_index in graph.node_indices() {
        let node_data = nodes
            .get(&node_index)
            .ok_or_else(|| Error::new(std::io::ErrorKind::InvalidData, "execution tree node missing"))?;
        let events = node_data.events.lock().unwrap();
        let label = event_summary(&events);
        let cfg_info = node_data.get_cfg_info();
        let mut attrs = format!("label=\"{}\"", dot_escape(&label));
        match cfg_info.as_deref() {
            Some("dead") => attrs.push_str(", style=filled, fillcolor=\"#ffcccc\", fontcolor=\"#cc0000\""),
            Some("concretize") => attrs.push_str(", style=\"filled,dashed\", fillcolor=\"#FFE0B2\""),
            _ => {}
        }
        writeln!(file, "  node{} [{}];", node_index.index(), attrs)?;
    }

    for edge_ref in graph.edge_references() {
        let source = edge_ref.source();
        let target = edge_ref.target();
        let edge = edge_ref.weight();

        let subst = build_subst_for_node(&*graph, &*nodes, target);
        let label = format_condition_label(edge, config, &subst);

        let source_data = nodes.get(&source);
        let source_cfg_info = source_data.as_ref().and_then(|d| d.get_cfg_info());
        let edge_style = match source_cfg_info.as_deref() {
            Some("concretize") => ", style=dashed",
            _ => "",
        };

        writeln!(
            file,
            "  node{} -> node{} [label=\"{}\"{}];",
            source.index(),
            target.index(),
            dot_escape(&label),
            edge_style
        )?;
    }

    writeln!(file, "}}")?;
    Ok(())
}

pub fn output_cfg_json<B: BV>(tree: &ExecutionTree<B>, config: &CfgOutputConfig) -> Result<(), Error> {
    let output_path = config
        .output_path
        .as_ref()
        .ok_or_else(|| Error::new(std::io::ErrorKind::InvalidInput, "missing cfg json output path"))?;

    let graph = tree.read_graph();
    let nodes = tree.read_nodes();

    let mut node_entries = Vec::new();
    for node_index in graph.node_indices() {
        let node_data = nodes
            .get(&node_index)
            .ok_or_else(|| Error::new(std::io::ErrorKind::InvalidData, "execution tree node missing"))?;
        let events = node_data.events.lock().unwrap().iter().map(|event| format!("{:?}", event)).collect::<Vec<_>>();
        let node_type = match node_data.get_cfg_info().as_deref() {
            Some("dead") => "dead",
            Some("concretize") => "concretize",
            _ => "normal",
        };

        node_entries.push(json!({
            "id": node_index.index(),
            "events": events,
            "type": node_type,
        }));
    }

    let mut edge_entries = Vec::new();
    for edge in graph.edge_references() {
        let edge_data = edge.weight();
        let target = edge.target();

        let condition_expr = if config.expand_fork_condition {
            if let Some(sym) = edge_data.condition {
                let subst = build_subst_for_node(&*graph, &*nodes, target);
                Some(format_exp_sym(&Exp::Var(sym), &subst))
            } else {
                None
            }
        } else {
            None
        };

        edge_entries.push(json!({
            "from": edge.source().index(),
            "to": target.index(),
            "fork_id": edge_data.fork_id,
            "condition": edge_data.condition.map(|sym| format!("v{}", sym)),
            "condition_expr": condition_expr,
            "taken": edge_data.taken,
        }));
    }

    let document: Value = json!({
        "nodes": node_entries,
        "edges": edge_entries,
    });

    let mut file = File::create(output_path)?;
    serde_json::to_writer_pretty(&mut file, &document)?;
    file.write_all(b"\n")?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::execution_tree::TreeEdge;
    use crate::smt::Sym;
    use crate::source_loc::SourceLoc;
    use petgraph::graph::NodeIndex;
    use std::fs;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn temp_output_path(ext: &str) -> PathBuf {
        std::env::temp_dir().join(format!(
            "isla-cfg-output-{}-{}.{}",
            std::process::id(),
            SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos(),
            ext
        ))
    }

    fn read_json(path: &PathBuf) -> Value {
        let content = fs::read_to_string(path).unwrap();
        serde_json::from_str(&content).unwrap()
    }

    #[test]
    fn constructs_cfg_output_config() {
        let config = CfgOutputConfig {
            format: CfgOutputFormat::Dot,
            output_path: Some(PathBuf::from("cfg.dot")),
            expand_fork_condition: true,
        };

        assert_eq!(config.format, CfgOutputFormat::Dot);
        assert_eq!(config.output_path, Some(PathBuf::from("cfg.dot")));
        assert!(config.expand_fork_condition);
    }

    #[test]
    fn writes_valid_cfg_json() {
        let tree = ExecutionTree::<B64>::new();
        let (child, _) = tree.add_node();
        tree.add_edge(
            NodeIndex::new(0),
            child,
            TreeEdge {
                fork_id: 7,
                condition: Some(Sym::from_u32(11)),
                condition_expr: Some("x > 0".to_string()),
                taken: true,
                source_loc: SourceLoc::unknown(),
            },
        );

        let output_path = std::env::temp_dir().join(format!(
            "isla-cfg-output-{}-{}.json",
            std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
        ));

        let config = CfgOutputConfig {
            format: CfgOutputFormat::Json,
            output_path: Some(output_path.clone()),
            expand_fork_condition: false,
        };

        output_cfg_json(&tree, &config).unwrap();

        let content = fs::read_to_string(&output_path).unwrap();
        let parsed: Value = serde_json::from_str(&content).unwrap();
        assert_eq!(parsed["nodes"].as_array().unwrap().len(), 2);
        assert_eq!(parsed["edges"].as_array().unwrap().len(), 1);

        let _ = fs::remove_file(&output_path);
    }

    #[test]
    fn writes_valid_cfg_dot_structure() {
        let tree = ExecutionTree::<B64>::new();
        let root = tree.root().0;
        let ((_left_index, _left_node), (_right_index, _right_node)) =
            tree.fork(root, 7, Sym::from_u32(11), SourceLoc::unknown());

        let output_path = temp_output_path("dot");
        let config = CfgOutputConfig {
            format: CfgOutputFormat::Dot,
            output_path: Some(output_path.clone()),
            expand_fork_condition: false,
        };

        output_cfg_dot(&tree, &config).unwrap();

        let content = fs::read_to_string(&output_path).unwrap();
        assert!(content.contains("digraph"));
        assert!(content.contains("node0 ["));
        assert!(content.contains("node0 -> node1"));
        assert!(content.contains("->"));

        let _ = fs::remove_file(&output_path);
    }

    #[test]
    fn json_node_type_reflects_tag() {
        let tree = ExecutionTree::<B64>::new();
        let root = tree.root().0;
        let ((left_index, left_node), (right_index, right_node)) =
            tree.fork(root, 8, Sym::from_u32(13), SourceLoc::unknown());

        left_node.set_cfg_info("dead");
        right_node.set_cfg_info("concretize");

        let output_path = temp_output_path("json");
        let config = CfgOutputConfig {
            format: CfgOutputFormat::Json,
            output_path: Some(output_path.clone()),
            expand_fork_condition: false,
        };

        output_cfg_json(&tree, &config).unwrap();

        let parsed = read_json(&output_path);
        let nodes = parsed["nodes"].as_array().unwrap();
        assert_eq!(nodes.len(), 3);

        let mut node_types = std::collections::HashMap::new();
        for node in nodes {
            let id = node["id"].as_u64().unwrap();
            let node_type = node["type"].as_str().unwrap().to_string();
            node_types.insert(id, node_type);
        }

        assert_eq!(node_types.get(&(root.index() as u64)).unwrap(), "normal");
        assert_eq!(node_types.get(&(left_index.index() as u64)).unwrap(), "dead");
        assert_eq!(node_types.get(&(right_index.index() as u64)).unwrap(), "concretize");

        let _ = fs::remove_file(&output_path);
    }

    #[test]
    fn json_condition_expr_expanded_when_enabled() {
        let tree = ExecutionTree::<B64>::new();
        let root = tree.root().0;
        let (_, _) = tree.fork(root, 9, Sym::from_u32(21), SourceLoc::unknown());

        let disabled_output_path = temp_output_path("json");
        let disabled_config = CfgOutputConfig {
            format: CfgOutputFormat::Json,
            output_path: Some(disabled_output_path.clone()),
            expand_fork_condition: false,
        };
        output_cfg_json(&tree, &disabled_config).unwrap();
        let disabled_parsed = read_json(&disabled_output_path);
        assert!(disabled_parsed["edges"][0]["condition_expr"].is_null());

        let enabled_output_path = temp_output_path("json");
        let enabled_config = CfgOutputConfig {
            format: CfgOutputFormat::Json,
            output_path: Some(enabled_output_path.clone()),
            expand_fork_condition: true,
        };
        output_cfg_json(&tree, &enabled_config).unwrap();
        let enabled_parsed = read_json(&enabled_output_path);
        assert!(enabled_parsed["edges"][0]["condition_expr"].is_string());

        let _ = fs::remove_file(&disabled_output_path);
        let _ = fs::remove_file(&enabled_output_path);
    }
}
