use isla_lib::error::{ExecError, SmtError};
use isla_lib::timeout::TimeoutDiagnostic;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct TimeoutSmtOutput {
    pub file: bool,
    pub stdout: bool,
    pub itrace: bool,
}

impl TimeoutSmtOutput {
    pub fn new(file: bool, stdout: bool, itrace: bool) -> Self {
        assert!(file || stdout || itrace, "timeout SMT output must select at least one destination");
        TimeoutSmtOutput { file, stdout, itrace }
    }
}

#[derive(Clone, Debug)]
pub struct TimeoutReportConfig {
    pub output: TimeoutSmtOutput,
    pub directory: PathBuf,
}

#[derive(Clone)]
pub(super) struct TimeoutReporter {
    config: TimeoutReportConfig,
    next_file_sequence: Arc<AtomicU64>,
}

impl TimeoutReporter {
    pub(super) fn new(config: TimeoutReportConfig) -> Self {
        TimeoutReporter { config, next_file_sequence: Arc::new(AtomicU64::new(1)) }
    }

    pub(super) fn itrace_enabled(&self) -> bool {
        self.config.output.itrace
    }

    pub(super) fn report_error(&self, clause: &str, error: &ExecError) {
        let (stem, diagnostic) = match error {
            ExecError::Smt(SmtError::Timeout(timeout)) => {
                (format!("{:?}", timeout.operation), TimeoutDiagnostic::Smt(timeout.clone()))
            }
            _ => return,
        };

        eprintln!("timeout diagnostic [{}]:", clause);
        for line in diagnostic.metadata_lines() {
            eprintln!("  {}", line);
        }
        if !self.config.output.file && !self.config.output.stdout {
            return;
        }
        let smt2 = match diagnostic.dump().materialize() {
            Ok(smt2) => smt2,
            Err(dump_error) => {
                eprintln!("timeout SMT2 materialize failed [{}]: {}", clause, dump_error);
                return;
            }
        };

        if self.config.output.stdout {
            println!("; timeout diagnostic [{}]", clause);
            for line in diagnostic.metadata_lines() {
                println!("; {}", line);
            }
            println!("; ---- timeout smt2 begin ----");
            print!("{}", smt2);
            if !smt2.ends_with('\n') {
                println!();
            }
            println!("; ---- timeout smt2 end ----");
        }
        if self.config.output.file {
            fs::create_dir_all(&self.config.directory).expect("failed to create timeout SMT2 output directory");
            let sequence = self.next_file_sequence.fetch_add(1, Ordering::Relaxed);
            let filename = format!(
                "{}-pid{}-{}-event{}.smt2",
                sanitize_filename(clause),
                std::process::id(),
                sanitize_filename(&stem),
                sequence
            );
            let path = self.config.directory.join(filename);
            let mut file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&path)
                .unwrap_or_else(|error| panic!("failed to create timeout SMT2 file {}: {}", path.display(), error));
            file.write_all(smt2.as_bytes())
                .unwrap_or_else(|error| panic!("failed to write timeout SMT2 file {}: {}", path.display(), error));
            eprintln!("timeout SMT2 [{}]: {}", clause, path.display());
        }
    }
}

fn sanitize_filename(value: &str) -> String {
    value
        .chars()
        .map(
            |character| {
                if character.is_ascii_alphanumeric() || matches!(character, '-' | '_') {
                    character
                } else {
                    '_'
                }
            },
        )
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use isla_lib::source_loc::SourceLoc;
    use isla_lib::timeout::{SmtDumpSource, SmtOperation, SmtTimeout, TimeoutSmtDump};
    use std::time::{Duration, SystemTime, UNIX_EPOCH};

    struct FixedDump;

    impl SmtDumpSource for FixedDump {
        fn materialize(&self) -> Result<String, String> {
            Ok("(check-sat)\n".to_string())
        }
    }

    fn timeout_error() -> ExecError {
        ExecError::Smt(SmtError::Timeout(Arc::new(SmtTimeout {
            source_loc: SourceLoc::unknown(),
            operation: SmtOperation::CheckSat,
            limit: Duration::from_secs(1),
            operation_wall: Duration::from_secs(1),
            dump: Arc::new(TimeoutSmtDump::new(Arc::new(FixedDump))),
        })))
    }

    #[test]
    fn reporter_keeps_distinct_artifacts_for_repeated_operations() {
        let unique = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
        let directory = std::env::temp_dir().join(format!("isla-timeout-reporter-{}-{}", std::process::id(), unique));
        let reporter = TimeoutReporter::new(TimeoutReportConfig {
            output: TimeoutSmtOutput::new(true, false, false),
            directory: directory.clone(),
        });

        reporter.report_error("zTEST", &timeout_error());
        reporter.report_error("zTEST", &timeout_error());
        reporter.report_error("zTEST", &timeout_error());

        let files: Vec<_> = fs::read_dir(&directory).unwrap().map(|entry| entry.unwrap().path()).collect();
        assert_eq!(files.len(), 3);
        for file in &files {
            assert_eq!(fs::read_to_string(file).unwrap(), "(check-sat)\n");
        }
        fs::remove_dir_all(directory).unwrap();
    }
}
