//! Reading `.lean` source files and discovering them under a directory.
//! Mirrors `language/src/file_manager.rs`'s shape (`read_source_file`,
//! `list_sources`) but returns `Result` throughout instead of panicking
//! on a bad path -- that file's `panic!`s on a malformed workspace are a
//! wart deliberately not inherited here.

use std::path::{Path, PathBuf};

use crate::error::LeanError;

const EXTENSION: &str = "lean";

/// Reads a single `.lean` file's contents. Does not enforce the
/// extension itself (callers that discover files via `list_sources`
/// already only see `.lean` paths); a caller handed an arbitrary path
/// gets a plain read.
pub fn read_source_file(path: &Path) -> Result<String, LeanError> {
    std::fs::read_to_string(path).map_err(LeanError::Io)
}

/// Lists every `.lean` file directly under `root` if `root` is a
/// directory (or `recursive` to descend into subdirectories), or
/// `[root]` if `root` is itself a `.lean` file. Returned in sorted
/// order so output is deterministic across runs/platforms.
pub fn list_sources(
    root: &Path,
    recursive: bool,
) -> Result<Vec<PathBuf>, LeanError> {
    if root.is_file() {
        return Ok(vec![root.to_path_buf()]);
    }
    let mut out = Vec::new();
    collect(root, recursive, &mut out)?;
    out.sort();
    Ok(out)
}

fn collect(
    dir: &Path,
    recursive: bool,
    out: &mut Vec<PathBuf>,
) -> Result<(), LeanError> {
    for entry in std::fs::read_dir(dir).map_err(LeanError::Io)? {
        let entry = entry.map_err(LeanError::Io)?;
        let path = entry.path();
        if path.is_dir() {
            if recursive {
                collect(&path, recursive, out)?;
            }
            continue;
        }
        if path.extension().and_then(|e| e.to_str()) == Some(EXTENSION) {
            out.push(path);
        }
    }
    Ok(())
}

#[cfg(test)]
mod unit_tests {
    use super::*;
    use std::fs;

    #[test]
    fn list_sources_finds_top_level_lean_files_only_by_default() {
        let dir = std::env::temp_dir()
            .join(format!("lean_parser_test_{}", std::process::id()));
        let sub = dir.join("sub");
        fs::create_dir_all(&sub).unwrap();
        fs::write(dir.join("a.lean"), "").unwrap();
        fs::write(dir.join("b.txt"), "").unwrap();
        fs::write(sub.join("c.lean"), "").unwrap();

        let top = list_sources(&dir, false).unwrap();
        assert_eq!(top, vec![dir.join("a.lean")]);

        let all = list_sources(&dir, true).unwrap();
        assert_eq!(all, vec![dir.join("a.lean"), sub.join("c.lean")]);

        fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn list_sources_on_a_single_file_returns_just_that_file() {
        let path = std::env::temp_dir().join(format!(
            "lean_parser_test_single_{}.lean",
            std::process::id()
        ));
        fs::write(&path, "").unwrap();
        assert_eq!(list_sources(&path, false).unwrap(), vec![path.clone()]);
        fs::remove_file(&path).unwrap();
    }

    #[test]
    fn read_source_file_reports_io_errors() {
        let missing = Path::new("/nonexistent/path/does_not_exist.lean");
        assert!(matches!(read_source_file(missing), Err(LeanError::Io(_))));
    }
}
