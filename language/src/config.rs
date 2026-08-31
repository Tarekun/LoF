use crate::error::LofError;
use crate::file_manager::read_file;
use std::sync::OnceLock;

#[derive(Debug, PartialEq, Clone)]
pub enum TypeSystem {
    Cic,
    Fol,
}
#[derive(Debug, Clone)]
pub enum SelectionFunction {
    Maximal,
    All,
}

#[derive(Debug, Clone)]
pub enum GivingClause {
    Fifo,
    Weighted,
}

pub fn id_to_system(system_id: &str) -> Result<TypeSystem, LofError> {
    map_type_system(system_id)
}

#[derive(Debug, Clone)]
pub struct Config {
    pub system: TypeSystem,
    pub log_level: tracing::Level,
    pub selection_fn: SelectionFunction,
    pub giving_clause_fn: GivingClause,
}
impl Default for Config {
    fn default() -> Self {
        Config {
            system: TypeSystem::Cic,
            log_level: tracing::Level::INFO,
            selection_fn: SelectionFunction::Maximal,
            giving_clause_fn: GivingClause::Weighted,
        }
    }
}
impl Config {
    pub fn new(type_system: TypeSystem) -> Self {
        Config {
            system: type_system,
            log_level: tracing::Level::INFO,
            selection_fn: SelectionFunction::Maximal,
            giving_clause_fn: GivingClause::Weighted,
        }
    }
}

/// Loads configuration from a YAML file.
/// If left unspecified config defaults are
/// `system`: cic
/// `log_level`: INFO
pub fn load_config(config_path: &str) -> Result<Config, LofError> {
    let mut config = Config::default();

    let config_content = read_file(config_path)?;
    let overrides: serde_yaml::Value = serde_yaml::from_str(&config_content)?;

    if let Some(system) = overrides.get("system") {
        if let Some(system_str) = system.as_str() {
            if !system_str.is_empty() {
                config.system = map_type_system(system_str)?;
            }
        }
    }
    if let Some(log_level) = overrides.get("log_level") {
        if let Some(level_str) = log_level.as_str() {
            config.log_level = map_log_level(level_str)?;
        }
    }
    if let Some(selection_fn) = overrides.get("selection_fn") {
        if let Some(selection_fn_str) = selection_fn.as_str() {
            config.selection_fn = map_selection_fn(selection_fn_str)?;
        }
    }
    if let Some(giving_clause_fn) = overrides.get("giving_clause_fn") {
        if let Some(giving_clause_fn_str) = giving_clause_fn.as_str() {
            config.giving_clause_fn =
                map_giving_clause_fn(giving_clause_fn_str)?;
        }
    }

    Ok(config)
}

fn map_type_system(system: &str) -> Result<TypeSystem, LofError> {
    match system {
        "cic" => Ok(TypeSystem::Cic),
        "fol" => Ok(TypeSystem::Fol),
        _ => Err(LofError::invalid_config_value("system", system, "cic, fol")),
    }
}

fn map_log_level(log_level: &str) -> Result<tracing::Level, LofError> {
    match log_level.to_lowercase().as_str() {
        "info" => Ok(tracing::Level::INFO),
        "error" => Ok(tracing::Level::ERROR),
        "debug" => Ok(tracing::Level::DEBUG),
        "trace" => Ok(tracing::Level::TRACE),
        "warn" => Ok(tracing::Level::WARN),
        _ => Err(LofError::invalid_config_value(
            "log_level",
            log_level,
            "info, error, debug, trace, warn",
        )),
    }
}

fn map_selection_fn(selection_fn: &str) -> Result<SelectionFunction, LofError> {
    match selection_fn.to_lowercase().as_str() {
        "maximal" => Ok(SelectionFunction::Maximal),
        "all" => Ok(SelectionFunction::All),
        _ => Err(LofError::invalid_config_value(
            "selection_fn",
            selection_fn,
            "maximal, all",
        )),
    }
}

fn map_giving_clause_fn(
    giving_clause_fn: &str,
) -> Result<GivingClause, LofError> {
    match giving_clause_fn.to_lowercase().as_str() {
        "fifo" => Ok(GivingClause::Fifo),
        "weighted" => Ok(GivingClause::Weighted),
        _ => Err(LofError::invalid_config_value(
            "giving_clause_fn",
            giving_clause_fn,
            "fifo, weighted",
        )),
    }
}

static GLOBAL_CONFIG: OnceLock<Config> = OnceLock::new();

/// Configures the global Config to be used for this run
pub fn init_global_config(config: Config) {
    let _ = GLOBAL_CONFIG.set(config);
}

/// Reads singleton global Config object used for this run of the program
pub fn global_config() -> &'static Config {
    GLOBAL_CONFIG.get_or_init(Config::default)
}
