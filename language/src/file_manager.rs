use rand::prelude::IndexedRandom;
use std::fs;
use std::io;
use std::path::Path;
use std::path::PathBuf;

const SOURCE_FILE_EXTENSION: &str = ".lof";
const LOGOS_DIRECTORY: &str = "./ascii_logos";

/// Opens the file at `filepath` and returns its content in the returned string
pub fn read_file(filepath: &str) -> Result<String, io::Error> {
    fs::read_to_string(filepath)
}

/// Opens the source file at `filepath` and returns its content in the returned string.
/// Fails in case the file extension isn't .lof
pub fn read_source_file(filepath: &str) -> Result<String, io::Error> {
    if !filepath.ends_with(SOURCE_FILE_EXTENSION) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!(
                "Unprocessable file format. Expected a '{}' file extension",
                SOURCE_FILE_EXTENSION
            ),
        ));
    }

    read_file(filepath)
}

/// Lists all source files contained at `workspace`. A workspace is either a source file
/// or a directory containing multiples.
/// Returns a vector containing all found file paths.
pub fn list_sources(workspace: &str) -> Vec<String> {
    let path = PathBuf::from(workspace);

    if path.is_dir() {
        let entries = fs::read_dir(&path).expect("Failed to read directory");
        let lof_files: Vec<String> = entries
            .filter_map(|entry| entry.ok())
            .map(|entry| entry.path())
            .filter(|path| {
                path.is_file()
                    && path.extension().and_then(|ext| ext.to_str())
                        == Some(&SOURCE_FILE_EXTENSION[1..])
            })
            .map(|path| path.display().to_string())
            .collect();

        lof_files
    } else if path.is_file() {
        if !workspace.ends_with(SOURCE_FILE_EXTENSION) {
            panic!(
                "Unprocessable file format. Expected a '{}' file extension",
                SOURCE_FILE_EXTENSION
            );
        }

        vec![workspace.to_string()]
    } else {
        panic!("Workspace path does not point to an existing directory or file: {}", workspace);
    }
}

/// Reads one of the LoF logos in ASCII art at random
pub fn read_ascii_logo() -> std::io::Result<String> {
    let dir = Path::new(LOGOS_DIRECTORY);
    let logos: Vec<PathBuf> = fs::read_dir(dir)?
        .filter_map(|entry| {
            let entry = entry.ok()?;
            let path = entry.path();

            if path.extension()?.to_str()? == "txt" {
                Some(path)
            } else {
                None
            }
        })
        .collect();

    if logos.is_empty() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("No logos found in directory {}", LOGOS_DIRECTORY),
        ));
    }

    let mut rng = rand::rng();
    let picked_logo = logos.choose(&mut rng).unwrap().to_str().unwrap();
    let logo_content = read_file(picked_logo)?;

    let logo_width = logo_content
        .lines()
        .map(|line| line.chars().count())
        .max()
        .unwrap_or(0);
    let border = "=".repeat(logo_width);
    let label = "LoF Proof Assistant".to_string();
    let padding = if label.len() < logo_width {
        " ".repeat((logo_width - label.len()) / 2)
    } else {
        "".to_string()
    };
    let final_logo = format!(
        "{}\n{}\n{}\n{}{}{}\n",
        border, logo_content, border, padding, label, padding
    );

    Ok(final_logo)
}
