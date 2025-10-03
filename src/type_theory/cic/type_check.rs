use super::cic::{Cic, CicTerm};
use crate::type_theory::commons::type_check::type_check_variable;
use crate::type_theory::environment::Environment;

//########################### EXPRESSIONS TYPE CHECKING
//
pub fn type_check_sort(
    environment: &mut Environment<Cic>,
    sort_name: &str,
) -> Result<CicTerm, String> {
    //TODO check that the type is a sort itself?
    type_check_variable::<Cic>(environment, sort_name)
}
//
//########################### EXPRESSIONS TYPE CHECKING
