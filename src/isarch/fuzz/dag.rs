//! 每路径一个文件，写出后立即重读，核对路径身份、定义序列及守卫数量。
use super::io::write_json;
use crate::isarch::resident::ResidentPath;
use isla_lib::{
    bitvector::BV,
    ir::SharedState,
    smt::{Context, Solver},
};
use serde_json::{json, Value};
use std::path::Path;

pub fn export<B: BV>(paths: &[ResidentPath<B>], context: &Context, shared: &SharedState<B>, output: &Path) {
    let directory = output.join("dag");
    std::fs::create_dir(&directory).unwrap();
    let mut manifest = Vec::new();
    let mut guards = 0;
    for path in paths {
        let solver = Solver::from_checkpoint(context, path.checkpoint.clone());
        let value = path.path.export_dag(&solver, shared, &path.records, path.signature);
        let name = format!("path-{}.json", path.signature);
        write_json(&directory.join(&name), &value);
        let reread: Value =
            serde_json::from_reader(std::fs::File::open(directory.join(&name)).unwrap()).expect("DAG 重读失败");
        assert_eq!(reread, value, "DAG 重读改变内容");
        assert_eq!(reread["path_signature"], json!(path.signature));
        assert_eq!(reread["guards"].as_array().unwrap().len(), path.records.len());
        guards += path.records.len();
        manifest.push(json!({"file":format!("dag/{name}"),"path_signature":path.signature,"guards":path.records.len(),"definitions":reread["definitions"].as_array().unwrap().len()}));
    }
    assert_eq!(manifest.len(), paths.len());
    write_json(
        &output.join("dag-manifest.json"),
        &json!({"schema_version":1,"paths":paths.len(),"guards":guards,"reread_consistent":true,"entries":manifest}),
    );
}
