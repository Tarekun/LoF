pub fn elaborate_let(
    environment: &mut Environment<StlcTerm, StlcType>,
    var_name: String,
    var_type: Expression,
    var_body: Expression,
) {
    let assigned_term = Stlc::elaborate_expression(var_body);
    match Stlc::type_check(assigned_term.clone(), environment) {
        Ok(assigned_type) => {
            environment.add_variable_definition(
                &var_name,
                &assigned_term,
                &assigned_type,
            );
        }
        Err(_) => panic!("ill-typed body in variable definition"),
    }
}
