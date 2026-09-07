//! Hand-rolled command-line argument parsing, matching the repo's style
//! (`language` has no `clap` dependency; this crate follows suit -- the
//! whole surface is seven flags, and `clap` would be the single largest
//! dependency in the crate by a wide margin).
//!
//! Note: `language/src/cli.rs::get_flag_value` has a bug -- it returns
//! the flag token itself rather than the argument following it. This
//! module's `flag_value` is a from-scratch, correct implementation, not
//! a port of that one.

pub struct Options {
    pub path: String,
    pub output: Option<String>,
    pub pretty: bool,
    pub tokens: bool,
    pub no_spans: bool,
    pub lenient: bool,
    pub recursive: bool,
    pub help: bool,
}

pub const USAGE: &str = "\
lean_parser [OPTIONS] <PATH>

Parses a subset of Lean 4 source into JSON.

  <PATH>              a .lean file, or a directory of .lean files

  -o, --output FILE   write JSON to FILE (default: stdout)
  -p, --pretty        pretty-print the JSON
      --tokens        emit the token stream instead of the AST (debugging)
      --no-spans      strip all \"span\" objects from the output
      --lenient       exit 0 even when the AST contains error nodes
      --recursive     recurse into subdirectories (default: top level only)
  -h, --help          print this message
";

/// Returns the value following `--flag VALUE` or `--flag=VALUE` in
/// `args`, given `--flag`'s short and long spellings. Unlike
/// `language/src/cli.rs::get_flag_value`, this actually returns the
/// following argument, not the flag itself.
fn flag_value(args: &[String], short: &str, long: &str) -> Option<String> {
    let eq_prefix = format!("{long}=");
    for (i, arg) in args.iter().enumerate() {
        if arg == short || arg == long {
            return args.get(i + 1).cloned();
        }
        if let Some(v) = arg.strip_prefix(&eq_prefix) {
            return Some(v.to_string());
        }
    }
    None
}

fn has_flag(args: &[String], short: &str, long: &str) -> bool {
    args.iter().any(|a| a == short || a == long)
}

/// Parses CLI arguments into `Options`. The last non-flag argument is
/// taken as `<PATH>`; returns `None` if no path was given and `--help`
/// wasn't requested either.
pub fn parse_args(args: &[String]) -> Option<Options> {
    let help = has_flag(args, "-h", "--help");
    let output = flag_value(args, "-o", "--output");
    let pretty = has_flag(args, "-p", "--pretty");
    let tokens = args.iter().any(|a| a == "--tokens");
    let no_spans = args.iter().any(|a| a == "--no-spans");
    let lenient = args.iter().any(|a| a == "--lenient");
    let recursive = args.iter().any(|a| a == "--recursive");

    if help {
        return Some(Options {
            path: String::new(),
            output,
            pretty,
            tokens,
            no_spans,
            lenient,
            recursive,
            help: true,
        });
    }

    // The path is whichever positional argument isn't consumed by a
    // flag or a flag's value.
    let mut skip_next = false;
    let mut path = None;
    for arg in args {
        if skip_next {
            skip_next = false;
            continue;
        }
        if arg == "-o" || arg == "--output" {
            skip_next = true;
            continue;
        }
        if arg.starts_with('-') {
            continue;
        }
        path = Some(arg.clone());
    }

    let path = path?;
    Some(Options {
        path,
        output,
        pretty,
        tokens,
        no_spans,
        lenient,
        recursive,
        help: false,
    })
}

#[cfg(test)]
mod unit_tests {
    use super::*;

    fn args(v: &[&str]) -> Vec<String> {
        v.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn parses_a_bare_path() {
        let o = parse_args(&args(&["foo.lean"])).unwrap();
        assert_eq!(o.path, "foo.lean");
        assert!(!o.pretty);
        assert!(o.output.is_none());
    }

    #[test]
    fn flag_value_returns_the_following_argument_not_the_flag() {
        let o = parse_args(&args(&["foo.lean", "-o", "out.json"])).unwrap();
        assert_eq!(o.output, Some("out.json".to_string()));
    }

    #[test]
    fn flag_value_supports_equals_syntax() {
        let o = parse_args(&args(&["foo.lean", "--output=out.json"])).unwrap();
        assert_eq!(o.output, Some("out.json".to_string()));
    }

    #[test]
    fn boolean_flags_are_detected() {
        let o = parse_args(&args(&[
            "foo.lean",
            "--pretty",
            "--tokens",
            "--no-spans",
            "--lenient",
            "--recursive",
        ]))
        .unwrap();
        assert!(o.pretty);
        assert!(o.tokens);
        assert!(o.no_spans);
        assert!(o.lenient);
        assert!(o.recursive);
    }

    #[test]
    fn help_flag_short_circuits_path_requirement() {
        let o = parse_args(&args(&["--help"])).unwrap();
        assert!(o.help);
    }

    #[test]
    fn missing_path_returns_none() {
        assert!(parse_args(&args(&["--pretty"])).is_none());
    }
}
