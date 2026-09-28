use crate::type_theory::{
    environment::Environment,
    f::f::SystemF,
    grammars::{
        f::{
            FTerm::{
                self, Abstraction, Application, TypeAbstraction,
                TypeApplication, Variable,
            },
            FType::{self, Arrow, Atomic, Forall},
        },
        traits::{NamedSubstitution, Reduction},
    },
    interface::TypeTheory,
};
use std::collections::HashSet;

fn var(name: &str) -> FTerm {
    Variable(name.to_string())
}
fn ty(name: &str) -> FType {
    Atomic(name.to_string())
}
fn kind() -> Box<FType> {
    Box::new(ty("*"))
}
fn arrow(domain: FType, codomain: FType) -> FType {
    Arrow(Box::new(domain), Box::new(codomain))
}
fn forall(var_name: &str, body: FType) -> FType {
    Forall(var_name.to_string(), kind(), Box::new(body))
}
fn lambda(var_name: &str, var_type: FType, body: FTerm) -> FTerm {
    Abstraction(var_name.to_string(), var_type, Box::new(body))
}
fn type_lambda(var_name: &str, body: FTerm) -> FTerm {
    TypeAbstraction(var_name.to_string(), kind(), Box::new(body))
}
fn app(fun: FTerm, arg: FTerm) -> FTerm {
    Application(Box::new(fun), Box::new(arg))
}
fn type_app(fun: FTerm, type_arg: FType) -> FTerm {
    TypeApplication(Box::new(fun), type_arg)
}
fn names(names: &[&str]) -> HashSet<String> {
    names.iter().map(|name| name.to_string()).collect()
}
/// Λα. λx:α. x
fn polymorphic_id() -> FTerm {
    type_lambda("A", lambda("x", ty("A"), var("x")))
}

#[test]
fn test_free_vars() {
    let term = type_lambda(
        "A",
        lambda("x", arrow(ty("A"), ty("nat")), app(var("x"), var("y"))),
    );
    assert_eq!(term.free_vars(), names(&["y"]));
    assert_eq!(
        term.free_type_vars(),
        names(&["nat"]),
        "Type variables bound by Λ are reported free"
    );
    assert_eq!(
        forall("A", arrow(ty("A"), ty("B"))).free_type_vars(),
        names(&["B"])
    );
}

#[test]
fn test_alpha_equivalence() {
    assert!(
        forall("A", arrow(ty("A"), ty("A")))
            .alpha_equivalent(&forall("B", arrow(ty("B"), ty("B")))),
        "Types differing by the name of a bound variable arent α-equivalent"
    );
    assert!(
        !forall("A", arrow(ty("A"), ty("B")))
            .alpha_equivalent(&forall("B", arrow(ty("B"), ty("B")))),
        "A free type name is confused with a bound one"
    );
    assert!(
        forall("A", forall("B", arrow(ty("A"), ty("B")))).alpha_equivalent(
            &forall("B", forall("A", arrow(ty("B"), ty("A"))))
        ),
        "Swapped binder names arent α-equivalent"
    );
    assert!(
        !forall("A", forall("B", ty("A")))
            .alpha_equivalent(&forall("A", forall("B", ty("B")))),
        "Shadowing is ignored by α-equivalence"
    );
}

#[test]
fn test_type_substitution() {
    assert_eq!(
        forall("B", arrow(ty("A"), ty("B"))).substitute_name("A", &ty("nat")),
        forall("B", arrow(ty("nat"), ty("B")))
    );
    assert_eq!(
        forall("A", ty("A")).substitute_name("A", &ty("nat")),
        forall("A", ty("A")),
        "Substitution replaces a bound type variable"
    );

    let substituted =
        forall("B", arrow(ty("A"), ty("B"))).substitute_name("A", &ty("B"));
    assert!(
        substituted.alpha_equivalent(&forall("C", arrow(ty("B"), ty("C")))),
        "Type substitution captures a free type variable: {:?}",
        substituted
    );
}

#[test]
fn test_term_substitution() {
    assert_eq!(
        lambda("x", ty("nat"), app(var("f"), var("y")))
            .substitute_name("y", &var("z")),
        lambda("x", ty("nat"), app(var("f"), var("z")))
    );
    assert_eq!(
        lambda("x", ty("nat"), var("x")).substitute_name("x", &var("z")),
        lambda("x", ty("nat"), var("x")),
        "Substitution replaces a bound variable"
    );

    // (λx. y)[x/y] must not become λx. x
    let substituted =
        lambda("x", ty("nat"), var("y")).substitute_name("y", &var("x"));
    let Abstraction(fresh, _, body) = &substituted else {
        panic!("Substitution didnt preserve the abstraction")
    };
    assert!(
        fresh != "x" && **body == var("x"),
        "Term substitution captures a free variable: {:?}",
        substituted
    );

    // types in annotations are substituted too
    assert_eq!(
        type_app(lambda("x", ty("A"), var("x")), ty("A"))
            .substitute_name("A", &ty("nat")),
        type_app(lambda("x", ty("nat"), var("x")), ty("nat"))
    );
}

#[test]
fn test_beta_reduction() {
    let env = SystemF::default_environment();
    assert_eq!(
        app(lambda("x", ty("nat"), app(var("f"), var("x"))), var("a"))
            .step(&env),
        app(var("f"), var("a")),
        "One step reduction doesnt β-reduce"
    );
    assert_eq!(
        type_app(polymorphic_id(), ty("nat")).step(&env),
        lambda("x", ty("nat"), var("x")),
        "One step reduction doesnt reduce type applications"
    );
    assert_eq!(
        app(type_app(polymorphic_id(), ty("nat")), var("a"))
            .reduce_to_normal(&env),
        var("a"),
        "Normalization doesnt chain type and term β-reduction"
    );
    assert_eq!(
        lambda(
            "y",
            ty("nat"),
            app(lambda("x", ty("nat"), var("x")), var("y"))
        )
        .step(&env),
        lambda("y", ty("nat"), var("y")),
        "One step reduction doesnt reduce under binders"
    );
}

#[test]
fn test_delta_reduction() {
    let mut env: Environment<SystemF> = SystemF::default_environment();
    env.add_substitution("id", &polymorphic_id());

    assert_eq!(
        var("id").step(&env),
        polymorphic_id(),
        "One step reduction doesnt δ-reduce globals"
    );
    assert_eq!(
        app(type_app(var("id"), ty("nat")), var("a")).reduce_to_normal(&env),
        var("a")
    );
    assert_eq!(
        lambda("id", ty("nat"), var("id")).step(&env),
        lambda("id", ty("nat"), var("id")),
        "Bound variables are δ-reduced to globals of the same name"
    );
    assert_eq!(
        var("constant").step(&env),
        var("constant"),
        "Undefined names should be values"
    );
}

#[test]
fn test_church_numerals() {
    // Nat := ∀A. (A → A) → A → A, two := ΛA. λs. λz. s (s z)
    let church = |n: usize| {
        let body = (0..n).fold(var("z"), |acc, _| app(var("s"), acc));
        type_lambda(
            "A",
            lambda("s", arrow(ty("A"), ty("A")), lambda("z", ty("A"), body)),
        )
    };
    // plus := λn. λm. ΛA. λs. λz. n [A] s (m [A] s z)
    let church_nat =
        forall("A", arrow(arrow(ty("A"), ty("A")), arrow(ty("A"), ty("A"))));
    let plus = lambda(
        "n",
        church_nat.clone(),
        lambda(
            "m",
            church_nat,
            type_lambda(
                "A",
                lambda(
                    "s",
                    arrow(ty("A"), ty("A")),
                    lambda(
                        "z",
                        ty("A"),
                        app(
                            app(type_app(var("n"), ty("A")), var("s")),
                            app(
                                app(type_app(var("m"), ty("A")), var("s")),
                                var("z"),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );

    let env = SystemF::default_environment();
    assert_eq!(
        app(app(plus, church(2)), church(1)).reduce_to_normal(&env),
        church(3),
        "Church numerals addition doesnt normalize to the expected numeral"
    );
}

#[test]
fn test_debug_printing() {
    assert_eq!(
        format!("{:?}", forall("A", arrow(arrow(ty("A"), ty("A")), ty("A")))),
        "∀A:*. (A → A) → A"
    );
    assert_eq!(
        format!(
            "{:?}",
            app(
                app(type_app(var("f"), ty("nat")), var("x")),
                lambda("y", ty("nat"), var("y"))
            )
        ),
        "f [nat] x (λy:nat. y)"
    );
}
