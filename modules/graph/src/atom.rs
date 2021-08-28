use std::convert::TryFrom;

use crate::error::GraphError;

/// A 32-bit pointer to an [Atom].
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
    /// The length of the `atom`'s text
    pub text_length: u16,
    /// The `atom`'s text
    pub text_content: [u8; 510],
}

#[test]
fn atom_size() {
    assert_eq!(std::mem::size_of::<Atom>(), 512);
}

impl Atom {
    /// Creates a new [Atom].
    ///
    /// # Errors
    /// [Atom] creation fails if the text is longer than 510 bytes long.
    pub fn new(text: &str) -> Result<Self, GraphError> {
        let mut atom = Self {
            text_length: u16::try_from(text.len()).map_err(|_| GraphError::TextTooLong)?,
            text_content: [0; 510],
        };

        atom.text_content[0..text.len()].copy_from_slice(text.as_bytes());

        Ok(atom)
    }
}
