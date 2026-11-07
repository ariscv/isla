//! 常驻 fuzz 骨架：一次探索、corpus 认证、确定性批次与 v1 输出。
mod campaign;
mod classifier;
mod corpus;
mod dag;
mod io;
mod mutator;
mod options;
mod replay;
mod report;
mod traits;

use isla_lib::executor::samples::{Sample, SampleChecker};
pub use options::{Mode, Options};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use sha2::{Digest, Sha256};
pub use traits::*;

pub fn random_stream(seed: u64, scenario: &str, sample_id: u64) -> ChaCha8Rng {
    let mut digest = Sha256::new();
    digest.input(b"isarch-fuzz-v1\0");
    digest.input(seed.to_le_bytes());
    digest.input((scenario.len() as u64).to_le_bytes());
    digest.input(scenario.as_bytes());
    digest.input(sample_id.to_le_bytes());
    let key: [u8; 32] = digest.result().into();
    ChaCha8Rng::from_seed(key)
}

pub struct Session {
    options: Options,
    corpus: Vec<Sample>,
}
impl Session {
    pub fn new(options: &Options) -> Result<Self, String> {
        let corpus = SampleChecker::load(&options.corpus, None)?.samples;
        if corpus.is_empty() {
            return Err("corpus 不得为空".into());
        }
        if !options.output.is_absolute() {
            return Err("--fuzz-output 必须是绝对路径，避免探索阶段改变输出位置".into());
        }
        std::fs::create_dir_all(options.output.parent().unwrap()).map_err(|e| e.to_string())?;
        std::fs::create_dir(&options.output).map_err(|e| format!("fuzz 输出必须是新目录：{e}"))?;
        let mut source_records = serde_json::Map::new();
        for name in ["done.json", "samples.manifest.json"] {
            let path = options.corpus.parent().unwrap().join(name);
            if path.exists() {
                let value: serde_json::Value =
                    serde_json::from_reader(std::fs::File::open(path).unwrap()).expect("来源记录损坏");
                source_records.insert(name.into(), value);
            }
        }
        io::write_json(
            &options.output.join("provenance.json"),
            &serde_json::json!({
                "source_records":source_records,"current_executable":std::env::current_exe().unwrap(),
                "validity":"当前模型语义重新确认；来源哈希仅记录，不作为门槛"
            }),
        );
        Ok(Self { options: options.clone(), corpus })
    }
}

pub use classifier::run;
#[cfg(test)]
use io::canonical_coordinates;
#[cfg(test)]
mod tests;
