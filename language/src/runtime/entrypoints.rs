use crate::config::Config;
use crate::error::LofError;
use crate::misc::Union::{L, R};
use crate::parser::api::LofAst;
use crate::parser::api::LofParser;
use crate::runtime::program::Schedule;
use crate::runtime::program::{Program, ProgramNode};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::{Kernel, Reducer, TypeTheory};
use std::io::{self, Write};
use tracing::debug;

#[derive(Debug)]
pub enum EntryPoint {
    Execute,
    TypeCheck,
    Elaborate,
    ParseOnly,
    Help,
    Interactive,
}

pub fn parse_only(config: &Config, workspace: &str) -> Result<LofAst, LofError> {
    debug!("Parsing of workspace: '{}'...", workspace);
    let parser = LofParser::new(config.clone());
    let ast = parser.parse_workspace(config, &workspace)?;
    debug!("Parsing done.");
    debug!("Parsed AST: {:?}", ast);

    Ok(ast)
}

pub fn parse_and_elaborate<T: TypeTheory + Kernel>(
    config: &Config,
    workspace: &str,
) -> Result<Schedule<T>, LofError> {
    let ast = parse_only(config, workspace)?;

    debug!("Elaboration of the AST into a program...");
    let schedule = T::elaborate_ast(&ast)?;
    debug!("Elaboration done.");

    for node in schedule.iter() {
        debug!("node in the elaborated program: {:?}", node);
    }
    Ok(schedule)
}

pub fn type_check<T: TypeTheory + Kernel + Reducer>(
    config: &Config,
    workspace: &str,
) -> Result<Schedule<T>, LofError> {
    let schedule = parse_and_elaborate::<T>(config, workspace)?;
    debug!("Type checking of the program...");
    let mut environment: Environment<T> = T::default_environment();
    let mut errors = vec![];

    for node in schedule.iter() {
        match node {
            ProgramNode::OfExp(exp) => {
                match T::type_check_expression(exp, &mut environment) {
                    Err(message) => {
                        errors.push(message);
                    }
                    Ok(_) => {
                        debug!("type checked expression: {:?}", exp);
                    }
                }
            }
            ProgramNode::OfStm(stm) => {
                match T::type_check_stm(stm, &mut environment) {
                    Err(message) => {
                        errors.push(message);
                    }
                    Ok(_) => {
                        debug!("type checked statement: {:?}", stm);
                    }
                }
            }
        }
    }
    debug!("Type checking done.");

    if errors.is_empty() {
        Ok(schedule)
    } else {
        Err(LofError::aggregate(errors))
    }
}

pub fn execute<T: TypeTheory + Kernel + Reducer>(
    config: &Config,
    workspace: &str,
) -> Result<(), LofError> {
    let schedule: Schedule<T> = type_check(config, workspace)?;
    let mut program = Program::with_schedule(schedule);
    program.execute()
}

pub fn read_input() -> Result<String, LofError> {
    let mut buffer = String::new();

    loop {
        let mut input = String::new();
        io::stdin().read_line(&mut input)?;
        buffer.push_str(&input);

        if buffer.ends_with("\\\n") || buffer.ends_with("\\\r\n") {
            if let Some(pos) = buffer.rfind('\\') {
                buffer.remove(pos);
            }
        } else {
            break;
        }
    }

    Ok(buffer)
}

pub fn interactive<T: TypeTheory + Kernel + Reducer>(
    config: &Config,
    _workspace: &str,
) -> Result<(), LofError> {
    let parser = LofParser::new(config.clone());
    let mut program: Program<T> = Program::new();

    loop {
        print!("> ");
        // make sure the prompt shows immediately
        io::stdout().flush().unwrap();
        let input = read_input()?;

        let node = match parser.parse_node(input.trim()) {
            Err(message) => {
                println!("Parsing error: {:?}", message);
                continue;
            }
            Ok((_, node)) => node,
        };
        match T::elaborate_node(&node)? {
            L(exp) => {
                match T::type_check_expression(&exp, &mut program.environment) {
                    Err(message) => {
                        println!("Type checking error: {}", message);
                        continue;
                    }
                    Ok(_) => {}
                }
                let result =
                    T::normalize_expression(&mut program.environment, &exp);
                println!("{:?}", result);
            }
            R(stm) => {
                match T::type_check_stm(&stm, &mut program.environment) {
                    Err(message) => {
                        println!("Type checking error: {}", message);
                        continue;
                    }
                    Ok(_) => {}
                }
                if let Err(msg) =
                    T::evaluate_statement(&mut program.environment, &stm)
                {
                    println!("Execution error: {}", msg);
                    //TODO see if i can write better handling
                    panic!();
                }
            }
        }
    }
}

pub fn help() {
    println!("Usage: lof <operation> <workspace> [--flags]");
    println!("workspace can be a path to either a .lof file or a directory");
    println!();
    println!("Operations:");
    println!("\trun\t\tExecute the code");
    println!("\tcheck\t\tParse and type check the code");
    println!("\tparse\t\tOnly parse code");
    println!(
        "\telaborate\tParse and map the AST to the configured type system"
    );
    println!();
    println!("Flags:");
    println!("\t--config <path>\t\tSpecify a custom config file path (defaults to ./config.yml)");
}

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::{
        config::{Config, TypeSystem},
        runtime::entrypoints::{
            execute, parse_and_elaborate, parse_only, type_check,
        },
        type_theory::{
            cic::cic::Cic,
            fol::fol::Fol,
            interface::{Kernel, Reducer},
        },
    };

    fn all_system_configs() -> Vec<Config> {
        vec![
            Config::default(),
            // Config {
            //     system: TypeSystem::Fol,
            // },
        ]
    }

    #[test]
    fn test_parsing() {
        for config in all_system_configs() {
            assert!(
                parse_only(&config, "../library").is_ok(),
                "Parsing entrypoint cant process std library"
            );
        }
    }

    #[test]
    fn test_elaboration() {
        for config in all_system_configs() {
            match config.system {
                TypeSystem::Cic => {
                    assert!(
                        parse_and_elaborate::<Cic>(&config, "../library")
                            .is_ok(),
                        "Elaboration entrypoint cant process std library"
                    );
                }
                TypeSystem::Fol => {
                    assert!(
                        parse_and_elaborate::<Fol>(&config, "./library")
                            .is_ok(),
                        "Elaboration entrypoint cant process std library"
                    );
                }
            }
        }
    }

    //TODO test everything
    #[test]
    fn test_type_check() {
        for config in all_system_configs() {
            let res = type_check::<Cic>(&config, "../library");
            assert!(
                res.is_ok(),
                "Type checking entrypoint cant process std library:\n{:?}",
                res.err()
            );
        }
    }

    #[test]
    fn test_execution() {
        for config in all_system_configs() {
            let res = match config.system {
                TypeSystem::Cic => execute::<Cic>(&config, "../library"),
                TypeSystem::Fol => execute::<Fol>(&config, "../library"),
            };
            assert!(
                res.is_ok(),
                "Execution cant process std library:\n{:?}",
                res.err()
            );
        }
    }

    #[test]
    fn test_dedicated_scripts() {
        /// directory navigation & script execution function
        fn test_scripts_run<T: Kernel + Reducer>(
            base_dir: &str,
            config: Config,
            error_prefix: &str,
        ) {
            let lof_files: Vec<_> = std::fs::read_dir(base_dir)
                .expect("failed to read test directory")
                .flat_map(|entry| {
                    let path = entry.expect("invalid dir entry").path();
                    if path.is_dir() {
                        std::fs::read_dir(&path)
                            .expect("failed to read subdirectory")
                            .map(|e| e.expect("invalid entry").path())
                            .collect::<Vec<_>>()
                    } else {
                        vec![path]
                    }
                })
                .filter(|p| {
                    p.extension().and_then(|e| e.to_str()) == Some("lof")
                })
                .collect();

            for file in &lof_files {
                let path_str = file.to_str().expect("non-UTF-8 path");
                let res = execute::<T>(&config, path_str);
                assert!(
                    res.is_ok(),
                    "{}. File: {}, Error: {:?}",
                    error_prefix,
                    path_str,
                    res.err()
                );
            }
        }

        // test complex CIC expressions parsing and type checking
        test_scripts_run::<Cic>(
            "../library/tests/expressions",
            Config::new(TypeSystem::Cic),
            "CIC complex expressions failed",
        );
        // test CIC proof checking
        test_scripts_run::<Cic>(
            "../library/tests/proofs",
            Config::new(TypeSystem::Cic),
            "CIC proofs execution failed",
        );
        // test FOL logic programming
        test_scripts_run::<Fol>(
            "../library/tests/loprog",
            Config::new(TypeSystem::Fol),
            "FOL solve execution failed",
        );
    }
}
