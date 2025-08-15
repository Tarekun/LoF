use crate::config::Config;
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

pub fn parse_only(config: &Config, workspace: &str) -> Result<LofAst, String> {
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
) -> Result<Schedule<T>, String> {
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
) -> Result<Schedule<T>, String> {
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
        Err(format!(
            "Type checking failed with errors:\n{}",
            errors.join("\n")
        ))
    }
}

pub fn execute<T: TypeTheory + Kernel + Reducer>(
    config: &Config,
    workspace: &str,
) -> Result<(), String> {
    let schedule: Schedule<T> = type_check(config, workspace)?;
    let mut program = Program::with_schedule(schedule);
    program.execute()
}

pub fn interactive<T: TypeTheory + Kernel + Reducer>(
    config: &Config,
    _workspace: &str,
) -> Result<(), String> {
    let parser = LofParser::new(config.clone());
    let mut program: Program<T> = Program::new();

    loop {
        print!("> ");
        // make sure the prompt shows immediately
        io::stdout().flush().unwrap();

        let mut input = String::new();
        io::stdin()
            .read_line(&mut input)
            .map_err(|e| e.to_string())?;

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
                let () = T::evaluate_statement(&mut program.environment, &stm);
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
        entrypoints::{execute, parse_and_elaborate, parse_only, type_check},
        type_theory::{cic::cic::Cic, fol::fol::Fol},
    };

    fn all_system_configs() -> Vec<Config> {
        vec![
            Config::default(),
            // Config {
            //     system: TypeSystem::Fol(),
            // },
        ]
    }

    #[test]
    fn test_parsing() {
        for config in all_system_configs() {
            assert!(
                parse_only(&config, "./library").is_ok(),
                "Parsing entrypoint cant process std library"
            );
        }
    }

    #[test]
    fn test_elaboration() {
        for config in all_system_configs() {
            match config.system {
                TypeSystem::Cic() => {
                    assert!(
                        parse_and_elaborate::<Cic>(&config, "./library")
                            .is_ok(),
                        "Elaboration entrypoint cant process std library"
                    );
                }
                TypeSystem::Fol() => {
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
            let res = type_check::<Cic>(&config, "./library");
            assert!(
                type_check::<Cic>(&config, "./library").is_ok(),
                "Type checking entrypoint cant process std library:\n{:?}",
                res.err()
            );
        }
    }

    #[test]
    fn test_execution() {
        for config in all_system_configs() {
            let res = match config.system {
                TypeSystem::Cic() => execute::<Cic>(&config, "./library"),
                TypeSystem::Fol() => execute::<Fol>(&config, "./library"),
            };
            assert!(
                res.is_ok(),
                "Execution cant process std library:\n{:?}",
                res.err()
            );
        }
    }
}
