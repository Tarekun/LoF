mod cli;
mod config;
mod entrypoints;
mod file_manager;
mod logger;
mod misc;
mod parser {
    pub mod api;
    mod commons;
    mod expressions;
    mod statements;
    mod tactics;
}
mod runtime {
    pub mod program;
}
mod type_theory {
    // pub mod commons;
    pub mod environment;
    pub mod interface;
    pub mod commons {
        pub mod elaboration;
        pub mod evaluation;
        pub mod type_check;
        pub mod utils;
    }
    pub mod cic {
        pub mod cic;
        mod cic_utils;
        pub mod elaboration;
        mod evaluation;
        mod tactics;
        mod type_check;
        mod type_check_inductive;
        mod unification;
        pub mod tests {
            pub mod type_check;
        }
    }
    // pub mod stlc {
    //     pub mod elaboration;
    //     pub mod stlc;
    // }
    pub mod fol {
        mod elaboration;
        mod evaluation;
        pub mod fol;
        pub mod fol_utils;
        mod type_check;
    }
    pub mod sup {
        mod saturation;
        pub mod sup;
        mod sup_utils;
        mod type_check;
    }
}
mod tests {
    mod fol {
        mod utils;
    }
}

use cli::get_flag_value;
use config::{load_config, Config, TypeSystem};
use entrypoints::{
    execute, help, parse_and_elaborate, parse_only, type_check, EntryPoint,
};
use logger::init_logger;
use std::env;
use tracing::{debug, error};
use type_theory::{
    cic::cic::Cic,
    fol::fol::Fol,
    interface::{Kernel, Reducer, TypeTheory},
};

use crate::{entrypoints::interactive, file_manager::read_ascii_logo};

fn determine_entrypoint(args: &[String]) -> EntryPoint {
    if args.len() < 2 {
        return EntryPoint::Interactive;
    }

    match args[1].as_str() {
        "check" => EntryPoint::TypeCheck,
        "elaborate" => EntryPoint::Elaborate,
        "parse" => EntryPoint::ParseOnly,
        "help" => EntryPoint::Help,
        "run" => EntryPoint::Execute,
        "interactive" => EntryPoint::Interactive,
        _ => EntryPoint::Help,
    }
}

fn run_with_theory<T: TypeTheory + Kernel + Reducer>(
    config: Config,
    filepath: &str,
    entrypoint: EntryPoint,
) {
    match entrypoint {
        EntryPoint::Execute => match execute::<T>(&config, filepath) {
            Err(message) => error!("Program failed: {}", message),
            Ok(_) => {}
        },
        EntryPoint::TypeCheck => match type_check::<T>(&config, filepath) {
            Err(message) => error!("Program failed: {}", message),
            Ok(_) => {}
        },
        EntryPoint::Elaborate => {
            match parse_and_elaborate::<T>(&config, filepath) {
                Err(message) => error!("Program failed: {}", message),
                Ok(_) => {}
            }
        }
        EntryPoint::ParseOnly => match parse_only(&config, filepath) {
            Err(message) => error!("Program failed: {}", message),
            Ok(_) => {}
        },
        EntryPoint::Help => help(),
        EntryPoint::Interactive => match interactive::<T>(&config, filepath) {
            Err(message) => error!("Program failed: {}", message),
            Ok(_) => {}
        },
    }
}

fn main() {
    println!("{}", read_ascii_logo().unwrap());
    let args: Vec<String> = env::args().collect();

    // get cli args
    let entrypoint = determine_entrypoint(&args);
    let filepath = &args.get(2).cloned().unwrap_or_else(|| ".".to_string());
    let config_path = match get_flag_value(&args, "--config") {
        Some(path) => path,
        None => "./config.yml".to_string(),
    };

    let config = load_config(&config_path).unwrap();
    init_logger(&config);

    debug!("Specified config: {:?}", config);
    debug!("Requested entrypoint: {:?}", entrypoint);

    match config.system {
        TypeSystem::Cic() => {
            run_with_theory::<Cic>(config, &filepath, entrypoint)
        }
        TypeSystem::Fol() => {
            run_with_theory::<Fol>(config, &filepath, entrypoint)
        }
    };
}
