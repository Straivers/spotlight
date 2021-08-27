use std::cell::Cell;


#[derive(Debug, Default)]
#[repr(transparent)]
pub struct TextLength(pub u16);

#[derive(Debug, Default)]
#[repr(transparent)]
pub struct TextOffset(pub u32);

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Ptr(pub u32);


//         0               1-3      4-7
// [ is_data/extension | subtype | unused ]
#[repr(transparent)]
#[derive(Default, Clone, Copy)]
pub struct Type(u8);

impl Type {
    pub const EXT_NEXT: u8 = 1 << 0;
    pub const EXT_PREV: u8 = 1 << 1;
    pub const EXT_LINK: u8 = 1 << 2;

    pub fn new(is_extension: bool, subtype: u8) -> Type {
        let mut data = is_extension as u8;
        data |= (0b111 & subtype) << 1;
        Type(data)
    }

    pub fn is_extension(&self) -> bool {
        (self.0 & 0b1) != 0
    }

    pub fn subtype(&self) -> u8 {
        0b111 & (self.0 >> 1)
    }
}

impl std::fmt::Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "{} {{ type: {}, subtype: {} }}",
            "Type",
            if self.is_extension() {
                "Extension"
            } else {
                "Atom"
            },
            if self.is_extension() {
                let mut s = String::new();
                if (self.subtype() & Self::EXT_NEXT) != 0 {
                    s.push_str("EXT_NEXT");
                }
                if (self.subtype() & Self::EXT_PREV) != 0 {
                    if s.len() > 0 {
                        s.push('|');
                    }
                    s.push_str("EXT_PREV");
                }
                if (self.subtype() & Self::EXT_LINK) != 0 {
                    if s.len() > 0 {
                        s.push('|');
                    }
                    s.push_str("EXT_LINK");
                }
                if s.is_empty() {
                    s.push_str("None");
                }
                s
            } else {
                "None".to_owned()
            }
        ))
    }
}


#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct Metadata {
    /// Pointers to atoms that were derived from this one. Each atom can be
    /// forked to produce multiple versions.
    pub next: [Ptr; 8],

    /// Pointers to atoms that were used to derive this one. A single entry
    /// indicates that this atom is a modified entry, and multiple entries
    /// indicates that it is the result of a merge operation.
    pub prev: [Ptr; 7],

    /// Links to other atoms.
    pub links: [Ptr; 44],

    /// An extension is used when one of the members in the atom has exceeded
    /// its capacity. For example, if an atom has more than 8 descendants, a
    /// singly-linked list of extension atoms may be used to add additional
    /// descendants.
    pub extension: Ptr,

    /// The type of the atom.
    pub atype: Type,

    /// Bytes (6) reserved for future usage
    unused: [u8; 7],
}

impl Default for Metadata {
    fn default() -> Self {
        Metadata {
            next: [Ptr(0); 8],
            prev: [Ptr(0); 7],
            links: [Ptr(0); 44],
            extension: Ptr(0),
            atype: Type::default(),
            unused: [0; 7],
        }
    }
}

/// An `Atom` is the unit of information stored within a `Graph`, and is
/// connected to other `atom`s through `link`s. `Atom`s must never be modified.
/// Instead, a new version of the atom is appended to the end of the graph to
/// form a doubly-linked list, such that a user may quickly retrieve both older
/// and newer versions of an `atom`.
///
/// `Link`s that pointed to the old version of the `atom` are not modified
/// automatically, but must be promoted by the user. This is to prevent
/// subgraphs from breaking if an `atom` no longer contains the information that
/// it did when a `link` was made.
#[repr(C)]
#[derive(Debug)]
pub struct Atom {
    pub metadata: Cell<Metadata>,

    /// Bytes (2) reserved for future usage
    unused: [u8; 2],

    // Immutable part
    /// The length of the text associated with this atom. This must never be
    /// modified. Create a new atom instead.
    pub text_length: TextLength,

    /// The index of the first character of this atom's text in the Graph's text
    /// block. This must never be modified. Create a new atom instead.
    pub text_offset: TextOffset,
}

impl Atom {
    pub fn new(text_length: TextLength, text_offset: TextOffset) -> Self {
        Self {
            metadata: Cell::new(Metadata::default()),
            unused: [0; 2],
            text_length,
            text_offset,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn atom_type() {
        assert_eq!(
            format!("{:?}", Type::new(false, 0)),
            "AtomType { type: Atom, subtype: None }"
        );
        assert_eq!(
            format!("{:?}", Type::new(true, 0)),
            "AtomType { type: Extension, subtype: None }"
        );
        assert_eq!(
            format!("{:?}", Type::new(true, Type::EXT_NEXT)),
            "AtomType { type: Extension, subtype: EXT_NEXT }"
        );
        assert_eq!(
            format!("{:?}", Type::new(true, Type::EXT_PREV)),
            "AtomType { type: Extension, subtype: EXT_PREV }"
        );
        assert_eq!(
            format!("{:?}", Type::new(true, Type::EXT_LINK)),
            "AtomType { type: Extension, subtype: EXT_LINK }"
        );
        assert_eq!(
            format!(
                "{:?}",
                Type::new(true, Type::EXT_NEXT | Type::EXT_PREV)
            ),
            "AtomType { type: Extension, subtype: EXT_NEXT|EXT_PREV }"
        );
        assert_eq!(
            format!(
                "{:?}",
                Type::new(true, Type::EXT_NEXT | Type::EXT_LINK)
            ),
            "AtomType { type: Extension, subtype: EXT_NEXT|EXT_LINK }"
        );
        assert_eq!(
            format!(
                "{:?}",
                Type::new(true, Type::EXT_PREV | Type::EXT_LINK)
            ),
            "AtomType { type: Extension, subtype: EXT_PREV|EXT_LINK }"
        );
        assert_eq!(
            format!(
                "{:?}",
                Type::new(true, Type::EXT_NEXT | Type::EXT_PREV | Type::EXT_LINK)
            ),
            "AtomType { type: Extension, subtype: EXT_NEXT|EXT_PREV|EXT_LINK }"
        );
    }
}
