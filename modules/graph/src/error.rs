#[derive(Debug, Clone, Copy)]
pub enum GraphError {
    TextTooLong,
    TooManyAtoms,
    InvalidAtomPtr,
}
