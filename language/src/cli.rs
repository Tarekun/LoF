pub fn get_flag_value(args: &[String], flag: &str) -> Option<String> {
    for (index, arg) in args.iter().enumerate() {
        if arg == flag {
            return args.get(index + 1).cloned();
        }
    }

    return None;
}

#[cfg(test)]
mod unit_tests {
    use super::get_flag_value;

    #[test]
    fn test_get_flag_value_returns_the_following_argument() {
        // Regression test: `get_flag_value` used to return the *flag itself*
        // (`arg.to_string()` on the element that matched `flag`) instead of
        // the argument following it, so `--config path/to/config.yml` was
        // read back as the config path literally being the string
        // `"--config"` - which doesn't exist as a file, so every use of
        // `--config <path>` crashed instead of loading the given config.
        let args: Vec<String> = vec![
            "run".to_string(),
            ".".to_string(),
            "--config".to_string(),
            "path/to/config.yml".to_string(),
        ];

        assert_eq!(
            get_flag_value(&args, "--config"),
            Some("path/to/config.yml".to_string()),
            "must return the value following the flag, not the flag itself"
        );
        assert_eq!(
            get_flag_value(&args, "--missing"),
            None,
            "must return None for a flag that isn't present"
        );
        assert_eq!(
            get_flag_value(
                &vec!["run".to_string(), "--config".to_string()],
                "--config"
            ),
            None,
            "must return None rather than panic when the flag is the last argument with no value after it"
        );
    }
}
