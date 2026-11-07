//! 直接输出 Isla 的有类型定义序列，不经 Z3 化简或规范化。
use super::*;
use crate::executor::merge_record::{context, guard_order};
use crate::simplify::{write_events_in_context, WriteOpts};
use crate::smt::{
    smtlib::{Def, Ty},
    DefAttrs,
};
use std::borrow::Cow;
use std::collections::{HashMap, HashSet};

fn type_json(ty: &Ty, shared: &impl DagNames) -> Value {
    match ty {
        Ty::Bool => json!({"kind":"bool"}),
        Ty::BitVec(width) => json!({"kind":"bitvector","width":width}),
        Ty::Enum(id) => json!({"kind":"enum","name":shared.name(id.to_name())}),
        Ty::Array(domain, range) => {
            json!({"kind":"array","domain":type_json(domain.as_ref(),shared),"range":type_json(range.as_ref(),shared)})
        }
        Ty::Float(exponent, significand) => json!({"kind":"float","exponent":exponent,"significand":significand}),
        Ty::RoundingMode => json!({"kind":"rounding_mode"}),
    }
}
trait DagNames {
    fn name(&self, name: crate::ir::Name) -> String;
}
impl<B: BV> DagNames for SharedState<'_, B> {
    fn name(&self, name: crate::ir::Name) -> String {
        zencode::decode(self.symtab.to_str(name))
    }
}

impl<B: BV> SamplePath<B> {
    pub fn export_dag(
        &self,
        solver: &Solver<B>,
        shared: &SharedState<B>,
        records: &[super::super::RegionMergeRecord<B>],
        signature: u64,
    ) -> Value {
        assert_eq!(solver.transaction_depth(), 0, "DAG 必须在探索结束后导出");
        let mut types = Cow::Owned(HashMap::new());
        let mut functions = Cow::Owned(HashMap::new());
        let mut definitions = Vec::new();
        let mut declared = HashSet::new();
        for (trace_index, event) in solver.trace().to_vec().into_iter().rev().enumerate() {
            if let Event::Smt(def, attrs, location) = event {
                let mut text = Vec::new();
                write_events_in_context(
                    &mut text,
                    std::slice::from_ref(event),
                    shared,
                    &WriteOpts::smtlib(),
                    &mut types,
                    &mut functions,
                )
                .expect("DAG 定义写出失败");
                let mut row = json!({"sequence":definitions.len(),"trace_index":trace_index,"smtlib":String::from_utf8(text).unwrap().trim(),"source":location.location_string(shared.symtab.files()),"attributes":format!("{attrs:?}")});
                match def {
                    Def::DeclareConst(symbol, ty) => {
                        declared.insert(*symbol);
                        row["kind"] = json!("declare_const");
                        row["symbol"] = json!(format!("v{symbol}"));
                        row["type"] = type_json(ty, shared);
                    }
                    Def::DeclareFun(symbol, args, ret) => {
                        row["kind"] = json!("declare_fun");
                        row["symbol"] = json!(format!("v{symbol}"));
                        row["arguments"] = json!(args.iter().map(|t| type_json(t, shared)).collect::<Vec<_>>());
                        row["type"] = type_json(ret, shared);
                    }
                    Def::DefineConst(symbol, expression) => {
                        row["kind"] = json!("define_const");
                        row["symbol"] = json!(format!("v{symbol}"));
                        row["type"] = type_json(&types[symbol], shared);
                        let mut refs = expression.variables().iter().map(|s| format!("v{s}")).collect::<Vec<_>>();
                        refs.sort();
                        row["references"] = json!(refs);
                    }
                    Def::Assert(expression) => {
                        row["kind"] = json!("assert");
                        row["type"] = json!({"kind":"bool"});
                        let mut refs = expression.variables().iter().map(|s| format!("v{s}")).collect::<Vec<_>>();
                        refs.sort();
                        row["references"] = json!(refs);
                    }
                    Def::DefineEnum(name, size) => {
                        row["kind"] = json!("define_enum");
                        row["name"] = json!(shared.name(*name));
                        row["members"] =
                            json!(shared.type_info.enums[name].iter().map(|n| shared.name(*n)).collect::<Vec<_>>());
                        row["size"] = json!(size);
                    }
                }
                definitions.push(row);
            }
        }
        let expression = |e: &Exp<Sym>| {
            let mut text = Vec::new();
            write_events_in_context(
                &mut text,
                &[Event::<B>::Smt(Def::Assert(e.clone()), DefAttrs::default(), SourceLoc::unknown())],
                shared,
                &WriteOpts::smtlib(),
                &mut Cow::Borrowed(&types),
                &mut Cow::Borrowed(&functions),
            )
            .unwrap();
            let text = String::from_utf8(text).unwrap();
            let text = text.trim().strip_prefix("(assert ").unwrap().strip_suffix(')').unwrap();
            json!({"smtlib":text,"type":type_json(&e.infer(&types,&functions).expect("DAG 引用必须有类型"),shared)})
        };
        fn value<B: BV>(v: &Val<B>, shared: &SharedState<B>, expression: &impl Fn(&Exp<Sym>) -> Value) -> Value {
            match v {
                Val::Symbolic(symbol) => {
                    let mut result = expression(&Exp::Var(*symbol));
                    result["symbol"] = json!(format!("v{symbol}"));
                    result
                }
                Val::MixedBits(_) => expression(&smt_value(v, SourceLoc::unknown()).unwrap()),
                Val::Struct(fields) => {
                    json!({"struct":fields.iter().map(|(n,v)|(shared.name(*n),value(v,shared,expression))).collect::<BTreeMap<_,_>>()})
                }
                Val::Ctor(n, v) => json!({"ctor":shared.name(*n),"value":value(v,shared,expression)}),
                Val::SymbolicCtor(discriminant, possibilities) => {
                    json!({"discriminant":expression(&Exp::Var(*discriminant)),"possibilities":possibilities.iter().map(|(n,v)|(shared.name(*n),value(v,shared,expression))).collect::<BTreeMap<_,_>>()})
                }
                Val::Vector(values) => {
                    json!({"vector":values.iter().map(|v|value(v,shared,expression)).collect::<Vec<_>>()})
                }
                Val::List(values) => {
                    json!({"list":values.iter().map(|v|value(v,shared,expression)).collect::<Vec<_>>()})
                }
                _ => encode(v, shared),
            }
        }
        let by_id = records.iter().map(|r| (r.record_id, r)).collect();
        let mut contexts = HashMap::new();
        let mut visiting = HashSet::new();
        let order = guard_order(records);
        let coordinates = order
            .iter()
            .enumerate()
            .map(|(coordinate, i)| (records[*i].record_id, coordinate))
            .collect::<HashMap<_, _>>();
        let guards=order.iter().enumerate().map(|(coordinate,i)| {
            let r=&records[*i];
            let active=context(r,&by_id,&mut visiting,&mut contexts);
            json!({"coordinate":coordinate,"record_id":r.record_id,"parent_coordinate":r.parent_record.map(|p|coordinates[&p]),"arm":r.arm,"condition":expression(&Exp::Var(r.condition)),"active":expression(&active),"canonical":expression(&Exp::And(Box::new(active),Box::new(Exp::Var(r.condition)))),"function":shared.name(r.function),"branch_pc":r.branch_pc,"dead":r.dead})
        }).collect::<Vec<_>>();
        let memory=self.memory.iter().enumerate().map(|(i,event)| {
            let (kind,address,data,count,commit,tag)=match event {
                Event::ReadMem{address,value,bytes,tag_value,..} => ("read",address,value,bytes,Exp::Bool(true),tag_value),
                Event::WriteMem{address,data,bytes,value,opts,tag_value,..} => ("write",address,data,bytes,if opts.is_exclusive(){Exp::Var(*value)}else{Exp::Bool(true)},tag_value),
                _ => panic!("SamplePath 只允许访存事件"),
            };
            let active=Exp::And(Box::new(self.memory_guards.get(&i).cloned().unwrap_or(Exp::Bool(true))),Box::new(commit));
            json!({"index":i,"kind":kind,"address":value(address,shared,&expression),"data":value(data,shared,&expression),"bytes":count,"active":expression(&active),"tag":tag.as_ref().map(|v|value(v,shared,&expression))})
        }).collect::<Vec<_>>();
        let mut input_symbols = HashSet::new();
        for v in self.pre.values() {
            input_symbols.extend(v.symbolic_variables());
        }
        for event in &self.memory {
            if let Event::ReadMem { value, .. } = event {
                input_symbols.extend(value.symbolic_variables());
            }
        }
        let mut declarations=declared.into_iter().map(|s|json!({"symbol":format!("v{s}"),"type":type_json(&types[&s],shared),"input_reference":input_symbols.contains(&s),"meaning":"声明保持自由；约束见 definitions，活动读取由具体前态内存绑定"})).collect::<Vec<_>>();
        declarations.sort_by(|a, b| a["symbol"].as_str().cmp(&b["symbol"].as_str()));
        json!({"schema_version":1,"path_signature":signature,"definitions":definitions,"guards":guards,"declarations":declarations,"state":{"pre":self.pre.iter().map(|(n,v)|(n,value(v,shared,&expression))).collect::<BTreeMap<_,_>>(),"post":self.post.iter().map(|(n,v)|(n,value(v,shared,&expression))).collect::<BTreeMap<_,_>>(),"result":value(&self.result,shared,&expression),"ret_val":self.result.to_string(shared),"memory":memory}})
    }
}
