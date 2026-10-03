#[cfg(test)]
mod unit_tests {
    use crate::tptp::header::{parse_header, Form, Order, Status};

    const HEADER: &str = "\
%------------------------------------------------------------------------------
% File     : GRP194+1 : TPTP v8.0.0. Released v2.0.0.
% Domain   : Group Theory (Semigroups)
% English  : If (F,*) and (H,+) are two semigroups, phi is a surjective
%            homomorphism from F to H, and id is a left zero for F,
%            then phi(id) is a left zero for H.

% Status   : Theorem
% Syntax   : Number of formulae    :    8 (   2 unt;   0 def)
%            Number of atoms       :   21 (   4 equ)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(a, axiom, p).
% Status   : Unsatisfiable
";

    #[test]
    fn test_fields() {
        let header = parse_header(HEADER).unwrap();
        assert_eq!(
            header.field("File"),
            Some("GRP194+1 : TPTP v8.0.0. Released v2.0.0.")
        );
        assert_eq!(
            header.field("English"),
            Some(
                "If (F,*) and (H,+) are two semigroups, phi is a surjective \
                 homomorphism from F to H, and id is a left zero for F, \
                 then phi(id) is a left zero for H."
            ),
            "Continuation lines arent joined to their field"
        );
        assert_eq!(
            header.field("Syntax"),
            Some(
                "Number of formulae    :    8 (   2 unt;   0 def) \
                 Number of atoms       :   21 (   4 equ)"
            ),
            "Continuation lines containing `:` are taken for fields"
        );
        assert_eq!(header.field("Comments"), Some(""));
        assert_eq!(
            header.status,
            Status::Theorem,
            "Comments after the first formula are read as part of the header"
        );
        assert_eq!(header.form, Form::Fof);
        assert_eq!(header.order, Some(Order::ReallyFirstOrder));
    }

    #[test]
    fn test_spc() {
        let header = |spc: &str| {
            parse_header(&format!("% Status : Theorem\n% SPC : {}", spc))
        };
        let cnf = header("CNF_UNS_EPR_NEQ_HRN").unwrap();
        assert_eq!(
            (cnf.form, cnf.order),
            (Form::Cnf, Some(Order::EffectivelyPropositional))
        );
        let thf = header("TH0_THM_NEQ_NAR").unwrap();
        assert_eq!(
            (thf.form, thf.order),
            (Form::Th0, None),
            "Only FOF and CNF classes have an order component"
        );
        assert!(header("XYZ_THM_PRP").is_err(), "Unknown forms are accepted");
    }

    #[test]
    fn test_invalid_headers() {
        assert!(
            parse_header("% SPC : FOF_THM_PRP\nfof(a, axiom, p).").is_err(),
            "Headers without a status are accepted"
        );
        assert!(
            parse_header("% Status : Theorem\nfof(a, axiom, p).").is_err(),
            "Headers without an SPC are accepted"
        );
        assert!(
            parse_header("% Status : Provable\n% SPC : FOF_THM_PRP").is_err(),
            "Unknown statuses are accepted"
        );
    }
}
