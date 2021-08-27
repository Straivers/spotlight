use super::atom;

// all 0: none
// bit 0 == 0: remainder is inline atom::Ptr
// bit 0 == 1: remainder points to set
    // bit 1 == 0: bits 2-30 point to small link set
    // bit 1 == 1: bits 2-30 point to large link set

#[derive(Debug, PartialEq, Eq)]
enum PtrKind {
    /// This pointer does not point to anything.
    None,
    /// The following 3 bytes may each be interpreted as signed offsets from the
    /// current `Atom`.
    Adjescent,
    /// The following 30 bits index into a SmallPtrSet array in the graph.
    FarSmall,
    /// The following 30 bits index into a LargePtrSet array in the graph.
    FarLarge,
}

// first 3 bits indicate type (none, unary, small, large)
pub struct Ptr(pub u32);

impl Ptr {
    pub fn kind(&self) -> PtrKind {
        if self.0 == 0 {
            return PtrKind::None;
        }

        if (self.0 & 1) == 0 {
            return PtrKind::Adjescent;
        }

        if (self.0 & 0b10) == 0 {
            return PtrKind::Small;
        }

        return PtrKind::Large;
    }

    pub fn as_unary(&self) -> atom::Ptr {
        assert_eq!(self.kind(), PtrKind::Unary);



        todo!()
    }
}

enum Type {
    None,
    Set1,
    Set7,
    Set63
}

pub struct Set {
    next: Ptr,
}
