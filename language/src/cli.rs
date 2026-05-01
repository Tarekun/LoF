pub fn get_flag_value(args: &[String], flag: &str) -> Option<String> {
    for arg in args {
        if arg == flag {
            return Some(arg.to_string());
        }
    }

    return None;
}
