#[derive(Debug, Default)]
#[repr(transparent)]
pub struct TextLength(pub u16);

#[derive(Debug, Default)]
#[repr(transparent)]
pub struct TextOffset(pub u32);

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct AtomPtr(pub u32);

impl AtomPtr {
    pub const MAX: AtomPtr = AtomPtr(u32::MAX);
}

/// An [Atom] is the unit of information stored within a [Graph](crate::graph::Graph), and is
/// connected to other atoms through [Link](crate::link::Link)s.
#[repr(C)]
#[derive(Debug)]
pub struct Atom {
    /// Bytes (10) reserved for future usage
    unused: [u8; 10],

    /// The length of the text associated with this atom. This must never be
    /// modified. Create a new atom instead.
    pub text_length: TextLength,

    /// The index of the first character of this atom's text in the Graph's text
    /// block. This must never be modified. Create a new atom instead.
    pub text_offset: TextOffset,
}

#[test]
fn atom_size() {
    assert_eq!(std::mem::size_of::<Atom>(), 16);
}

impl Atom {
    #[must_use]
    pub fn new(text_length: TextLength, text_offset: TextOffset) -> Self {
        Self {
            unused: [0; 10],
            text_length,
            text_offset,
        }
    }
}
