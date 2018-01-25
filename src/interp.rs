use rustc::ty::Ty;

// Stores a value represented as a vector of bytes, along with its type annotation.
// It's important to keep track of a value's type while it is being evaluated,
// so that we know how to interpret the bytes.
pub struct TypedVal<'tcx> {
    pub ty: Ty<'tcx>,
    pub val: Vec<u8>,
}
