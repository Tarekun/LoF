use crate::config::Config;
use crate::misc::Union::{L, R};
use crate::parser::api::LofParser;
use crate::parser::api::{Expression, LofAst, Tactic};
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
    Help(Vec<String>),
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

pub fn read_input() -> Result<String, String> {
    let mut buffer = String::new();

    loop {
        let mut input = String::new();
        io::stdin()
            .read_line(&mut input)
            .map_err(|e| e.to_string())?;
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
) -> Result<(), String> {
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

fn print_entries(entries: &[(&str, &str)]) {
    let w = entries.iter().map(|(key, _)| key.len()).max().unwrap_or(0);
    for (key, val) in entries {
        println!("\t{key:<w$}\t{val}");
    }
}

pub fn help(args: Vec<String>) {
    fn generic() {
        println!("Usage: lof <operation> <arg> [--flags]");
        println!();
        println!("Operations:");
        print_entries(&[
            ("run <workspace>",    "Execute the code at the path pointed by <workspace>"),
            ("check <workspace>",  "Run type checking on the code at the path pointed by <workspace>"),
            ("help [subcommands]", "Access LoF documentation (use `lof help help` to see extended functionality)"),
            ("parse",              "Only parse code"),
            ("elaborate",          "Parse and map the AST to the configured type system"),
        ]);
        println!();
        println!("Flags:");
        print_entries(&[(
            "--config <path>",
            "Specify a custom config file path (defaults to ./config.yml)",
        )]);
    }
    fn help_help() {
        println!("Usage: lof help [subcommands]");
        println!("Without a subcommand, prints the general usage message.");
        println!();
        println!("Subcommands:");
        print_entries(&[
            ("help", "Show this message"),
            ("tactics", "List tactics supported in the language"),
            ("systems", "List type systems supported in the language"),
            ("run", "Details on how to run LoF scripts"),
        ]);
    }
    fn help_systems() {
        println!("Type systems define what LoF expressions are considered well-formed expressions and affects the type (or proof) checking algorithm.");
        println!("You can use the `system` field in the YAML config to select the type system to use (defaults to 'cic')");
        println!();
        println!("Type systems supported");
        print_entries(&[
            ("cic", "Calculus of Inductive Constructions, higher-order type system mainly use for ITP (constructive system)"),
            ("fol", "First-Order Logic, traditional logic system in its classical form"),
            ("sup", "Superposition calculus, FO grammar in CNF used for proof automation")
        ]);
    }
    fn help_tactics(tactic: Option<&String>) {
        match tactic {
            Some(tactic) => match tactic.as_str() {
                "intro" => {
                    println!("`intro` is used to introduce a new hypothesis.");
                    println!();
                    println!("When the current goal contains an hypothesis (you have to prove an implication H -> T or the quantification a ∀x:H. T) `intro` introduces that hypothesis.");
                    println!("Using `intro` alone will use the same variable name found for the goal's type declaration, but you can override the hypothesis name with `intro h_name`");
                }
                "exact" => {
                    println!("`exact` is used to close the current goal by providing a term with a type that unifies with it.");
                    println!();
                    println!("Say you have to prove the goal P 1 and have the following hypothesis:");
                    print_entries(&[
                        ("bc :", "P 0"),
                        ("ic :", "P n -> P (s n)"),
                    ]);
                    println!("Then you can close the goal with the tactic `exact (ic bc)` and conclude the proof (by ic P 0 implies P 1).");
                    println!();
                    println!(
                        "{}. {}. {}",
                        "Note this tactic normalizes both the provided term and the target before computing unification",
                        "Suppose you have defined the `plus` function on naturals and trying to prove plus 0 1 = 1, where equality = is inductively defined with the `refl` constructor",
                        "Then you can prove plus 0 1 = 1 by simply using `exact refl Nat (plus 0 1) 1`, since `plus 0 1` will be reduced to 1"
                    );
                }
                "apply" => {
                    println!("`apply` is used when you need to close a goal that is given by the conclusion of some theorem you already have.");
                    println!();
                    println!("{}, {}. {}",
                        "If you need to prove goal G and you have a functional term with type  f: H -> G",
                        "then you can use `apply f` to close G. This will open the new goal H, moving the proof by backwards reasoning",
                        "Once you construct a term `h: H` you'll be able to close goal H and the obtained proof is equivalent to using `exact f h`"
                    );
                    println!("The same concept applies if the the applied term is a universal quantification f: ∀x:H. G");
                }
                _ => println!("Tactic named `{}` does not exist", tactic),
            },
            None => {
                println!("Tactics are commands that can be used in interactive proofs, to code your proof without having to build convoluted proof terms.");
                println!("Use `lof help tactics <tactic>` to get more details on a specific tactic");
                println!("Currently tactics and interactive proofs are only supported with the 'cic' type system");
                println!();
                println!("Tactics supported:");
                print_entries(&[
                    ("intro [name]", "When the open goal is an implication or universal quantification, assume the hypothesis and optionally give it a name"),
                    ("exact <term>", "Prove a goal with the supplied term of appropriate type"),
                    ("apply <lemma>", "Prove a goal with the supplied lemma, opening subgoals for its hypothesis"),
                ]);
            }
        }
    }
    fn help_run() {
        println!("Usage: lof run <workspace>");
        println!();
        println!("This command executes the LoF scripts at the workspace path provided.");
        println!("A workspace can either be a single .lof file or a directory containing multiple files.");
        println!("This means that both `lof run ./my_lof_project/main.lof` and `lof run ./my_lof_project/` are allowed commands.");
        println!();
        println!(
            "{}, {}. {}",
            "Note that when running a single file the execution is carried out within the current working directory",
            "but if the workspace points to a directory it will be set as the root directory for the execution",
            "This can impact relative imports defined in source files."
        );
    }

    if args.len() == 0 {
        generic()
    } else {
        match args[0].as_str() {
            "help" => help_help(),
            "systems" => help_systems(),
            "tactics" => help_tactics(args.get(1)),
            "run" => help_run(),
            _ => println!("No help available for subcommand `{}`. Run `lof help help` to see what is available", args[0]),
        }
    }
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
