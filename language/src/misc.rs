/// Tag union type with a left and a right constructor
/// how rust doesnt natively have this is beyond me
#[derive(Debug, PartialEq, Clone)]
pub enum Union<L, R> {
    L(L),
    R(R),
}
impl<L, R> Union<L, R> {
    pub fn left_or_panic(self) -> L {
        match self {
            Union::L(left) => left,
            Union::R(_) => {
                panic!("left expected but union is right-constructed")
            }
        }
    }
}

// im like fr?
pub fn simple_map<T, R>(
    vector: Vec<T>,
    iterator: impl FnMut(T) -> R,
) -> Vec<R> {
    vector.into_iter().map(iterator).collect()
}

pub fn simple_map_indexed<T, R>(
    vector: Vec<T>,
    iterator: impl FnMut((usize, T)) -> R,
) -> Vec<R> {
    vector.into_iter().enumerate().map(iterator).collect()
}
