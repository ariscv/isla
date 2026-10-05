//! 三种轨迹共用的文件提交与写线程生命周期。
use crossbeam::queue::SegQueue;
use std::fs::{File, OpenOptions};
use std::io::Write;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread::{self, JoinHandle};

pub(super) fn clear_output_file(output_path: &Option<PathBuf>) {
    let Some(path) = output_path else {
        return;
    };
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            std::fs::create_dir_all(parent)
                .unwrap_or_else(|error| panic!("trace: 无法创建输出目录 {}: {}", parent.display(), error));
        }
    }
    File::create(path).unwrap_or_else(|error| panic!("trace: 无法创建/清空输出文件 {}: {}", path.display(), error));
}

// ============ TraceWriter ============
// Writer 独立管理输出路径、完成队列和后台写线程。TraceHandler 只需要把
// 已完成的组合轨迹路径 交给 writer，不再暴露 String 队列和线程细节。

pub(super) struct TraceWriter {
    pub(super) output_path: Mutex<Option<PathBuf>>,
    pub(super) completed_queue: Arc<SegQueue<String>>,
    pub(super) shutdown: Arc<AtomicBool>,
    pub(super) write_thread: Mutex<Option<JoinHandle<()>>>,
}

impl Default for TraceWriter {
    fn default() -> Self {
        Self {
            output_path: Mutex::new(None),
            completed_queue: Arc::new(SegQueue::new()),
            shutdown: Arc::new(AtomicBool::new(false)),
            write_thread: Mutex::new(None),
        }
    }
}

impl TraceWriter {
    pub(super) fn start_write_thread(&self) {
        let output_path = self.output_path.lock().expect("trace mutex poisoned").clone();
        let path = match output_path {
            Some(p) => p,
            None => return,
        };

        let mut thread_handle = self.write_thread.lock().expect("trace mutex poisoned");
        if thread_handle.is_some() {
            return;
        }

        self.shutdown.store(false, Ordering::Release);

        if let Some(parent) = path.parent() {
            if !parent.as_os_str().is_empty() {
                std::fs::create_dir_all(parent)
                    .unwrap_or_else(|error| panic!("trace: 无法创建输出目录 {}: {}", parent.display(), error));
            }
        }

        let queue = Arc::clone(&self.completed_queue);
        let shutdown = Arc::clone(&self.shutdown);
        let path_for_error = path.clone();

        let handle = thread::Builder::new()
            .name("trace-writer".into())
            .spawn(move || {
                let mut file = OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open(&path)
                    .unwrap_or_else(|error| panic!("trace: 无法打开输出文件 {}: {}", path.display(), error));

                loop {
                    match queue.pop() {
                        Some(text) => {
                            writeln!(file, "{}", text).unwrap_or_else(|write_error| {
                                panic!("trace: 写入输出文件 {} 失败: {}", path.display(), write_error)
                            });
                        }
                        None => {
                            if shutdown.load(Ordering::Acquire) {
                                break;
                            }
                            thread::yield_now();
                        }
                    }
                }

                // Drain remaining items after shutdown signal
                while let Some(text) = queue.pop() {
                    writeln!(file, "{}", text).unwrap_or_else(|write_error| {
                        panic!("trace: 写入输出文件 {} 失败: {}", path.display(), write_error)
                    });
                }
                file.flush().unwrap_or_else(|flush_error| {
                    panic!("trace: 刷新输出文件 {} 失败: {}", path.display(), flush_error)
                });
            })
            .unwrap_or_else(|spawn_error| {
                panic!("trace: 无法启动写入线程 (输出路径 {}): {}", path_for_error.display(), spawn_error)
            });

        *thread_handle = Some(handle);
    }

    pub(super) fn stop_write_thread(&self) {
        self.shutdown.store(true, Ordering::Release);
        if let Ok(mut thread_handle) = self.write_thread.lock() {
            if let Some(handle) = thread_handle.take() {
                match handle.join() {
                    Ok(()) => {}
                    Err(panic_payload) => {
                        let message = panic_payload
                            .downcast_ref::<String>()
                            .map(String::as_str)
                            .or_else(|| panic_payload.downcast_ref::<&str>().copied())
                            .unwrap_or("未知写入线程 panic");
                        panic!("trace: 写入线程异常退出: {}", message);
                    }
                }
            }
        }
    }

    pub(super) fn set_path(&self, output_path: Option<PathBuf>) {
        let current_path = self.output_path.lock().expect("trace mutex poisoned").clone();
        if current_path != output_path {
            self.stop_write_thread();
        }

        *self.output_path.lock().expect("trace mutex poisoned") = output_path.clone();
        let needs_spawn = {
            let thread_handle = self.write_thread.lock().expect("trace mutex poisoned");
            thread_handle.is_none() && output_path.is_some()
        };
        if needs_spawn {
            self.start_write_thread();
        }
    }

    pub(super) fn configure_path(&self, output_path: Option<PathBuf>) {
        self.stop_write_thread();
        clear_output_file(&output_path);
        self.set_path(output_path);
    }

    pub(super) fn with_output_path(output_path: Option<PathBuf>) -> Self {
        let writer = Self::default();
        writer.configure_path(output_path);
        writer
    }

    pub(super) fn submit_text(&self, text: String) {
        self.completed_queue.push(text);
    }

    pub(super) fn dump(&self) {
        self.stop_write_thread();
    }

    #[cfg(test)]
    pub(super) fn has_write_thread(&self) -> bool {
        self.write_thread.lock().expect("trace mutex poisoned").is_some()
    }

    pub(super) fn output_path(&self) -> Option<PathBuf> {
        self.output_path.lock().expect("trace mutex poisoned").clone()
    }
}

impl Drop for TraceWriter {
    fn drop(&mut self) {
        self.dump();
    }
}
