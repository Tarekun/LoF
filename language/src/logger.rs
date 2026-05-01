use crate::config::Config;
use chrono::Local;
use std::fs::File;
use std::path::PathBuf;
use tracing_subscriber::filter::LevelFilter;
use tracing_subscriber::fmt::{self, format::Writer, time::FormatTime};
use tracing_subscriber::prelude::*; // Needed for `.with(...)`
use tracing_subscriber::Registry;

/// Custom time formatter to use local time.
struct LocalTimer;
impl FormatTime for LocalTimer {
    fn format_time(&self, w: &mut Writer<'_>) -> std::fmt::Result {
        write!(w, "{}", Local::now().format("%H:%M:%S"))
        // write!(w, "{}", Local::now().format("%Y-%m-%d %H:%M:%S"))
    }
}

/// Get the log file name with proper rotation
fn get_file_name() -> String {
    let out_dir = PathBuf::from("out");
    if !out_dir.exists() {
        match std::fs::create_dir(&out_dir) {
            Ok(_) => {}
            Err(e) => panic!("Failed to create log directory: {}", e),
        }
    }

    let mut counter = 0;
    loop {
        if counter == 0 {
            let path = out_dir.join("lof.log");
            if !path.exists() {
                return path.to_string_lossy().to_string();
            }
        } else {
            let path = out_dir.join(format!("lof-{}.log", counter));
            if !path.exists() {
                return path.to_string_lossy().to_string();
            }
        }
        counter += 1;
    }
}

/// Initializes logging with both console and file outputs.
pub fn init_logger(config: &Config) {
    let log_file_name = get_file_name();
    let log_level = LevelFilter::from_level(config.log_level);

    // Console logger (with color)
    let console_layer = fmt::layer()
        .with_ansi(true)
        .with_timer(LocalTimer)
        .with_target(false)
        .with_level(true)
        .with_thread_names(false);

    // File logger (without color)
    let file = File::create(log_file_name).expect("Failed to create log file");
    let file_layer = fmt::layer()
        .with_writer(file)
        .with_ansi(false)
        .with_timer(LocalTimer)
        .with_target(false)
        .with_level(true)
        .with_thread_names(false);

    // Combine everything
    Registry::default()
        .with(log_level)
        .with(console_layer)
        .with(file_layer)
        .init();
}
