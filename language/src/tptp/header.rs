use crate::error::LofError;

#[derive(Debug, Clone, Copy, PartialEq)]
/// SZS status of a problem, given by the `% Status` header field
pub enum Status {
    /// Every model of the axioms (and there are some) is a model of the
    /// conjectures
    Theorem,
    /// The axioms have no models
    ContradictoryAxioms,
    /// Some models of the axioms (and there are some) are models of the
    /// negation of a conjecture
    CounterSatisfiable,
    /// There are no conjectures, and the axioms have no models
    Unsatisfiable,
    /// There are no conjectures, and the axioms have some models
    Satisfiable,
    /// The problem has never been solved by an ATP system
    Unknown,
    /// The abstract problem has never been solved
    Open,
}

#[derive(Debug, Clone, Copy, PartialEq)]
/// Language form of a problem, first component of its SPC
pub enum Form {
    Cnf,
    Fof,
    Tf0,
    Tf1,
    Tx0,
    Tx1,
    Th0,
    Th1,
}

#[derive(Debug, Clone, Copy, PartialEq)]
/// Effective order of the logic of FOF and CNF problems, third component of
/// their SPC
pub enum Order {
    /// `PRP`
    Propositional,
    /// `EPR`, first order without function symbols
    EffectivelyPropositional,
    /// `RFO`
    ReallyFirstOrder,
}

#[derive(Debug, Clone, PartialEq)]
/// The header of a TPTP problem file: the leading comment block made of
/// `% Field : value` lines. The `Status` and `SPC` fields determine the
/// logic of the problem
pub struct TptpHeader {
    /// Every field of the header in order, continuation lines joined
    pub fields: Vec<(String, String)>,
    pub status: Status,
    pub form: Form,
    pub order: Option<Order>,
}

impl TptpHeader {
    /// Returns the value of the field `name`, if present
    pub fn field(&self, name: &str) -> Option<&str> {
        self.fields
            .iter()
            .find(|(field, _)| field == name)
            .map(|(_, value)| value.as_str())
    }
}

/// Parses the header of the TPTP problem `source`. Field lines look like
/// `% Name : value`, lines indented further continue the previous field.
/// The header ends at the first line that is neither a comment nor blank
pub fn parse_header(source: &str) -> Result<TptpHeader, LofError> {
    let mut fields: Vec<(String, String)> = vec![];
    let comments = source
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map_while(|line| line.strip_prefix('%'));
    for comment in comments {
        let field = comment
            .strip_prefix(' ')
            .and_then(|line| line.split_once(':'))
            .map(|(name, value)| (name.trim_end(), value.trim()));
        match field {
            Some((name, value))
                if !name.is_empty()
                    && name.chars().all(|c| c.is_ascii_alphabetic()) =>
            {
                fields.push((name.to_string(), value.to_string()))
            }
            _ if comment.starts_with("  ") => {
                if let Some((_, value)) = fields.last_mut() {
                    if !value.is_empty() {
                        value.push(' ');
                    }
                    value.push_str(comment.trim());
                }
            }
            _ => {}
        }
    }

    // the first word, as further words may qualify the value
    let first_word = |name: &str| {
        fields
            .iter()
            .find(|(field, _)| field == name)
            .and_then(|(_, value)| value.split_whitespace().next())
            .ok_or_else(|| {
                LofError::custom(format!(
                    "TPTP problem header lacks the `% {} :` field",
                    name
                ))
            })
    };

    let status = match first_word("Status")? {
        "Theorem" => Status::Theorem,
        "ContradictoryAxioms" => Status::ContradictoryAxioms,
        "CounterSatisfiable" => Status::CounterSatisfiable,
        "Unsatisfiable" => Status::Unsatisfiable,
        "Satisfiable" => Status::Satisfiable,
        "Unknown" => Status::Unknown,
        "Open" => Status::Open,
        other => {
            return Err(LofError::custom(format!(
                "Unknown TPTP status `{}`",
                other
            )))
        }
    };

    // eg `FOF_THM_PRP`: the form, the status again and, for FOF and CNF, the order
    let spc: Vec<&str> = first_word("SPC")?.split('_').collect();
    let form = match spc[0] {
        "CNF" => Form::Cnf,
        "FOF" => Form::Fof,
        "TF0" => Form::Tf0,
        "TF1" => Form::Tf1,
        "TX0" => Form::Tx0,
        "TX1" => Form::Tx1,
        "TH0" => Form::Th0,
        "TH1" => Form::Th1,
        other => {
            return Err(LofError::custom(format!(
                "Unknown TPTP language form `{}`",
                other
            )))
        }
    };
    let order = match spc.get(2) {
        Some(&"PRP") => Some(Order::Propositional),
        Some(&"EPR") => Some(Order::EffectivelyPropositional),
        Some(&"RFO") => Some(Order::ReallyFirstOrder),
        _ => None,
    };

    Ok(TptpHeader {
        fields,
        status,
        form,
        order,
    })
}
