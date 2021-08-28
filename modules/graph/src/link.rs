use crate::atom::AtomPtr;

/// Holds the collected link pointers associated with an [Atom](crate::atom::Atom).
#[derive(Debug)]
pub struct Links {
    pub next: LinkPtr,
    pub prev: LinkPtr,
    pub links: LinkPtr,
    _unused: [u8; 4],
}

#[test]
fn links_size() {
    assert_eq!(std::mem::size_of::<Links>(), 16);
}

/// Describes the format that the [Link] is using.
#[derive(Debug, PartialEq, Eq)]
pub enum LinkKind {
    /// This pointer does not point to anything.
    None,

    /// The upper 30 bits may be interpreted as a single 30-bit [AtomPtr]. If
    /// more than 30-bits are required to store an [AtomPtr], a [SmallLinkSet]
    /// must be used instead.
    AtomPointer,

    /// The pointer contains 5 6-bit packed signed offsets from the current [Atom](crate::atom::Atom).
    PackedOffsets,

    /// The upper 30 bits index into a [SmallLinkSet] array in the graph.
    SmallLinkSetIndex,

    /// The upper 30 bits index into a [LargeLinkSet] array in the graph.
    LargeLinkSetIndex,
}

impl LinkKind {
    const ATOM_POINTER: u32 = 0b00;
    const PACKED_OFFSETS: u32 = 0b01;
    const SMALL_LINK_SET_INDEX: u32 = 0b10;
    const LARGE_LINK_SET_INDEX: u32 = 0b11;

    /// The smallest offset that a packed reference can have, relative tothe base [Atom](crate::atom::Atom).
    pub const PACKED_MIN: i32 = -32;

    /// The largest offset that a packed reference can have, relative to the base [Atom](crate::atom::Atom).
    pub const PACKED_MAX: i32 = 31;

    const PACKED_MASK: u32 = 0b11_1111;

    /// 1 Billion indices should be plenty. That figures to (32*4 * 2 ^ 30) =
    /// 128 GiB of [SmallLinkSet]s, or (512 * 4 ^ 30) = 2 TiB of [LargeLinkSet]s.
    pub const INDEX_MAX: u32 = u32::MAX >> 2;
}

/// A pointer to a link set.
///
/// There are four kinds of link sets:
///
/// - An in-line atom pointer.
/// - A packed format, which can hold 5 references packed into 6-bit signed
///   offsets.
/// - An index to a [SmallLinkSet], which can hold up to 30 reference.
/// - An index to a [LargeLinkSet], which can hold up to 510 references.
///
/// In every case, it is invalid for a link set to hold no references except in
/// its default state.
#[repr(transparent)]
#[derive(Default, Clone, Copy)]
pub struct LinkPtr(u32);

impl LinkPtr {
    /// Returns what kind of pointer this is.
    #[must_use]
    pub fn kind(&self) -> LinkKind {
        if self.is_null() {
            return LinkKind::None;
        }

        match self.0 & 0b11 {
            LinkKind::PACKED_OFFSETS => LinkKind::PackedOffsets,
            LinkKind::ATOM_POINTER => LinkKind::AtomPointer,
            LinkKind::SMALL_LINK_SET_INDEX => LinkKind::SmallLinkSetIndex,
            LinkKind::LARGE_LINK_SET_INDEX => LinkKind::LargeLinkSetIndex,
            _ => unreachable!(),
        }
    }

    /// Returns true if the pointer is null.
    pub fn is_null(&self) -> bool {
        self.0 == 0
    }

    /// Creates a null LinkPtr.
    pub fn null() -> Self {
        Self(0)
    }

    /// Creates a set of up to 5 delta-encoded pointers and packs them into the
    /// pointer itself. It is invalid for the `current` pointer to be null.
    ///
    /// ```
    /// # use graph::{AtomPtr, LinkPtr};
    /// LinkPtr::new_packed_set(AtomPtr(5), &[AtomPtr(1), AtomPtr(2), AtomPtr(35)]);
    /// ```
    ///
    /// To pack in 5 link pointers, each must obey certain restrictions:
    ///
    ///  - The pointer must be between [LinkKind::PACKED_MIN] and
    ///    [LinkKind::PACKED_MAX]
    ///  - It must not be an interior null pointer.
    ///
    /// ```should_panic
    /// # use graph::{AtomPtr, LinkPtr};
    /// LinkPtr::new_packed_set(AtomPtr(5), &[AtomPtr(1), AtomPtr(2), AtomPtr(60)]);
    /// // Index out of range here ---------------------------------------^
    /// ```
    ///
    /// ```should_panic
    /// # use graph::{AtomPtr, LinkPtr};
    /// LinkPtr::new_packed_set(AtomPtr(5), &[AtomPtr(1), AtomPtr(0), AtomPtr(3)]);
    /// // Interior null here --------------------------------^
    /// ```
    #[must_use]
    pub fn new_packed_set(current: AtomPtr, pointers: &[AtomPtr]) -> Self {
        assert!(
            pointers.len() <= 5,
            "A packed set can contain at most 5 pointers."
        );

        for p in pointers {
            assert_ne!(
                *p, current,
                "A packed-offset link pointer must not point to itself."
            );
            // check for non-trailing 0s
            assert!(p.0 != 0, "Packed sets should not have null pointers.");
        }

        let low_bits = LinkKind::PACKED_OFFSETS;

        // Use i32 offsets because it's the same size as Ptr.0
        let mut offsets: [i32; 5] = [0; 5];
        for (i, p) in pointers.iter().enumerate() {
            let offset = i64::from(p.0) - i64::from(current.0);
            assert!(
                i64::from(LinkKind::PACKED_MIN) <= offset
                    && offset <= i64::from(LinkKind::PACKED_MAX),
                "Pointer offset {} is too large to fit in a packed link set",
                offset
            );
            offsets[i] = offset as i32;
        }

        let offset_bits: [u32; 5] = unsafe { std::mem::transmute(offsets) };

        let value = low_bits
            | ((offset_bits[0] & LinkKind::PACKED_MASK) << 2)
            | ((offset_bits[1] & LinkKind::PACKED_MASK) << 8)
            | ((offset_bits[2] & LinkKind::PACKED_MASK) << 14)
            | ((offset_bits[3] & LinkKind::PACKED_MASK) << 20)
            | ((offset_bits[4] & LinkKind::PACKED_MASK) << 26);

        Self(value)
    }

    /// Creates a new [Link] that points directly to an [Atom](crate::atom::Atom). The
    /// [AtomPtr] is stored internally, so no additional allocations are
    /// necessary. As a consequence of this storage, only [AtomPtr] values up
    /// to [LinkKind::INDEX_MAX] may be stored. If a larger [AtomPtr] is
    /// needed, use a [SmallLinkSet] instead.
    #[must_use]
    pub fn new_atom_ptr(pointer: AtomPtr) -> Self {
        assert!(pointer.0 <= LinkKind::INDEX_MAX);
        assert_ne!(pointer.0, 0, "Unary links cannot be null.");

        Self((pointer.0 << 2) | LinkKind::ATOM_POINTER)
    }

    /// Creates a new [Link] to a [SmallLinkSet]. It is assumed that the
    /// [SmallLinkSet] has at least one item.
    #[must_use]
    pub fn new_small_link_set_index(index: u32) -> Self {
        assert!(index <= LinkKind::INDEX_MAX);
        Self((index << 2) | LinkKind::SMALL_LINK_SET_INDEX)
    }

    /// Creates a new [Link] to a [LargeLinkSet]. It is assumed that the
    /// [LargeLinkSet] has at least one item.
    #[must_use]
    pub fn new_large_link_set_index(index: u32) -> Self {
        assert!(index <= LinkKind::INDEX_MAX);
        Self((index << 2) | LinkKind::LARGE_LINK_SET_INDEX)
    }

    /// Extracts the packed link set iff the pointer was created with
    /// [new_packed_set()](Self::new_packed_set).
    #[must_use]
    pub fn as_packed_set(&self, current: AtomPtr) -> [AtomPtr; 5] {
        assert_eq!(self.kind(), LinkKind::PackedOffsets);

        let i = self.0 >> 2;
        let offsets = [
            i6_to_i64(i & LinkKind::PACKED_MASK),
            i6_to_i64((i >> 6) & LinkKind::PACKED_MASK),
            i6_to_i64((i >> 12) & LinkKind::PACKED_MASK),
            i6_to_i64((i >> 18) & LinkKind::PACKED_MASK),
            i6_to_i64((i >> 24) & LinkKind::PACKED_MASK),
        ];

        let p = i64::from(current.0);

        let mut array = [AtomPtr::null(); 5];
        for (i, offset) in offsets.iter().enumerate() {
            if *offset == 0 {
                break;
            }
            array[i] = AtomPtr((p + *offset) as u32);
        }

        array
    }

    /// Extracts the in-line [AtomPtr] iff the pointer was created with
    /// [new_atom_ptr()](Self::new_atom_ptr).
    #[must_use]
    pub fn as_atom_ptr(&self) -> AtomPtr {
        assert_eq!(self.kind(), LinkKind::AtomPointer);
        AtomPtr(self.0 >> 2)
    }

    /// Extracts the pointer to the [SmallLinkSet] iff the pointer was created with
    /// [new_small_link_set_index()](Self::new_small_link_set_index).
    #[must_use]
    pub fn as_small_link_set_index(&self) -> u32 {
        assert_eq!(self.kind(), LinkKind::SmallLinkSetIndex);
        self.0 >> 2
    }

    /// Extracts the pointer to the [SmallLinkSet] iff the pointer was created with
    /// [new_large_link_set_index()](Self::new_large_link_set_index).
    #[must_use]
    pub fn as_large_link_set_index(&self) -> u32 {
        assert_eq!(self.kind(), LinkKind::LargeLinkSetIndex);
        self.0 >> 2
    }
}

impl std::fmt::Debug for LinkPtr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let kind = self.kind();

        let mut builder = f.debug_struct("Ptr");
        builder.field("kind", &kind);

        match kind {
            LinkKind::None => {}
            LinkKind::PackedOffsets => {
                let pointers = self.as_packed_set(AtomPtr(0));
                builder.field("adjescent_pointers", &pointers);
            }
            LinkKind::AtomPointer => {
                builder.field("unary_atom", &self.as_atom_ptr());
            }
            LinkKind::SmallLinkSetIndex => {
                builder.field("small_link_set_index", &self.as_small_link_set_index());
            }
            LinkKind::LargeLinkSetIndex => {
                builder.field("large_link_set_index", &self.as_large_link_set_index());
            }
        }

        builder.finish()
    }
}

#[repr(C)]
#[derive(Debug, Default, Clone, Copy)]
pub struct Link {
    pub atom: AtomPtr,
    pub link: LinkPtr,
}

/// A [LinkSet] is a fixed-size list of [AtomPtr]s that can be chained to form
/// a linked list of arbitrary length.
///
/// Such a linked list will always be in order of decreasing size, but not
/// otherwise sorted.
///
/// e.g.: [LargeLinkSet]->[SmallLinkSet]->[SmallLinkSet]->[Link] (packed)
#[repr(C)]
#[derive(Debug)]
pub struct LinkSet<const SIZE: usize> {
    next: Link,
    length: u16,
    unused: [u8; 2],
    pointers: [AtomPtr; SIZE],
}

impl<const SIZE: usize> LinkSet<SIZE> {
    #[must_use]
    pub fn from_slice(pointers: &[AtomPtr]) -> Self {
        assert!(pointers.len() <= SIZE);

        for pointer in pointers {
            assert!(
                !pointer.is_null(),
                "A LinkSet must not have interior null pointers."
            );
        }

        let mut set = Self {
            next: Link::default(),
            length: pointers.len() as u16,
            unused: [0; 2],
            pointers: [AtomPtr::null(); SIZE],
        };

        set.pointers[0..pointers.len()].copy_from_slice(pointers);
        set
    }
}

/// A small [LinkSet] of 30 references. See the documentation of [LinkSet] for more details.
pub type SmallLinkSet = LinkSet<30>;

/// A large [LinkSet] of 510 references. See the documentation of [LinkSet] for
/// more details.
pub type LargeLinkSet = LinkSet<510>;

/// Iterator that traverses a list of [LinkPtr]s and produces [AtomPtr]s.
pub struct LinkIter<'a> {
    index: u16,
    current: Link,
    small_sets: &'a [SmallLinkSet],
    large_sets: &'a [LargeLinkSet],
}

impl<'a> LinkIter<'a> {
    pub fn new(link: Link, small_sets: &'a [SmallLinkSet], large_sets: &'a [LargeLinkSet]) -> Self {
        Self {
            index: 0,
            current: link,
            small_sets,
            large_sets,
        }
    }
}

impl<'a> Iterator for LinkIter<'a> {
    type Item = AtomPtr;

    fn next(&mut self) -> Option<Self::Item> {
        match self.current.link.kind() {
            LinkKind::AtomPointer => {
                let p = self.current.link.as_atom_ptr();
                self.current = Link::default();
                Some(p)
            }
            LinkKind::PackedOffsets => {
                let set = self.current.link.as_packed_set(self.current.atom);
                let p = set[self.index as usize];

                self.index += 1;
                if self.index == 5 || set[self.index as usize].is_null() {
                    self.current = Link::default();
                }

                Some(p)
            }
            LinkKind::SmallLinkSetIndex => {
                let set = &self.small_sets[self.current.link.as_small_link_set_index() as usize];
                let p = set.pointers[self.index as usize];

                self.index += 1;
                if self.index == 30 || set.pointers[self.index as usize].is_null() {
                    self.index = 0;
                    self.current = set.next;
                }

                Some(p)
            }
            LinkKind::LargeLinkSetIndex => {
                let set = &self.large_sets[self.current.link.as_large_link_set_index() as usize];
                let p = set.pointers[self.index as usize];

                self.index += 1;
                if self.index == 510 || set.pointers[self.index as usize].is_null() {
                    self.index = 0;
                    self.current = set.next;
                }

                Some(p)
            }
            LinkKind::None => None,
        }
    }
}

/// Does a raw conversion of the low 6 bits to an i64
fn i6_to_i64(raw_i6: u32) -> i64 {
    const OTHER_BITS: u32 = i64::BITS - 6;
    (i64::from(raw_i6))
        .wrapping_shl(OTHER_BITS)
        .wrapping_shr(OTHER_BITS)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn packed_set() {
        {
            let ptr = LinkPtr::new_packed_set(
                AtomPtr(3),
                &[AtomPtr(1), AtomPtr(2), AtomPtr(4), AtomPtr(4), AtomPtr(5)],
            );
            let offsets = ptr.as_packed_set(AtomPtr(3));

            assert_eq!(offsets[0], AtomPtr(1));
            assert_eq!(offsets[1], AtomPtr(2));
            assert_eq!(offsets[2], AtomPtr(4));
            assert_eq!(offsets[3], AtomPtr(4));
            assert_eq!(offsets[4], AtomPtr(5));
        }
        {
            let ptr = LinkPtr::new_packed_set(AtomPtr::MAX, &[AtomPtr(u32::MAX - 4)]);

            let set = ptr.as_packed_set(AtomPtr::MAX);
            assert_eq!(set[0], AtomPtr(u32::MAX - 4));
            assert_eq!(set[1], AtomPtr::null());
            assert_eq!(set[2], AtomPtr::null());
            assert_eq!(set[3], AtomPtr::null());
            assert_eq!(set[4], AtomPtr::null());
        }
    }

    #[test]
    #[should_panic]
    fn bad_packed_set1() {
        // Packed sets must never be completely empty.
        let _ = LinkPtr::new_packed_set(
            AtomPtr(3),
            &[AtomPtr(0), AtomPtr(0), AtomPtr(0), AtomPtr(0), AtomPtr(0)],
        );
    }

    #[test]
    #[should_panic]
    fn bad_packed_set2() {
        // Packed sets must never have an interior null pointer.
        let _ = LinkPtr::new_packed_set(
            AtomPtr(3),
            &[AtomPtr(1), AtomPtr(1), AtomPtr(0), AtomPtr(1), AtomPtr(1)],
        );
    }

    #[test]
    fn atom_ptr() {
        let ptr = LinkPtr::new_atom_ptr(AtomPtr(20));
        assert_eq!(ptr.kind(), LinkKind::AtomPointer);
        assert_eq!(ptr.as_atom_ptr(), AtomPtr(20));
    }

    #[test]
    fn large_link_set_index() {
        let ptr = LinkPtr::new_large_link_set_index(100);
        assert_eq!(ptr.kind(), LinkKind::LargeLinkSetIndex);
        assert_eq!(ptr.as_large_link_set_index(), 100);
    }

    #[test]
    fn small_link_set_index() {
        let ptr = LinkPtr::new_small_link_set_index(100);
        assert_eq!(ptr.kind(), LinkKind::SmallLinkSetIndex);
        assert_eq!(ptr.as_small_link_set_index(), 100);
    }

    #[test]
    fn iter_packed_link_set() {
        let ptr = LinkPtr::new_packed_set(
            AtomPtr(1),
            &[AtomPtr(2), AtomPtr(3), AtomPtr(4), AtomPtr(5)],
        );
        let mut iter = LinkIter::new(
            Link {
                atom: AtomPtr(1),
                link: ptr,
            },
            &[],
            &[],
        );

        for i in 2..=5 {
            assert_eq!(iter.next(), Some(AtomPtr(i)));
        }
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn iter_atom_ptr() {
        let ptr = LinkPtr::new_atom_ptr(AtomPtr(20));
        let mut iter = LinkIter::new(
            Link {
                atom: AtomPtr(20),
                link: ptr,
            },
            &[],
            &[],
        );

        assert_eq!(iter.next(), Some(AtomPtr(20)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn iter_small_set() {
        let pointers = (10..=17).map(|i| AtomPtr(i)).collect::<Vec<_>>();
        let mut sets = [SmallLinkSet::from_slice(&pointers)];

        sets[0].next = Link {
            atom: AtomPtr(20),
            link: LinkPtr::new_atom_ptr(AtomPtr(18)),
        };

        let mut iter = LinkIter::new(
            Link {
                atom: AtomPtr(9),
                link: LinkPtr::new_small_link_set_index(0),
            },
            &sets,
            &[],
        );

        for i in 10..=18 {
            assert_eq!(iter.next(), Some(AtomPtr(i)));
        }
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn iter_large_set() {
        let pointers_large = (10..=17).map(|i| AtomPtr(i)).collect::<Vec<_>>();
        let mut large_sets = [LargeLinkSet::from_slice(&pointers_large)];

        let pointers_small = (18..=20).map(|i| AtomPtr(i)).collect::<Vec<_>>();
        let mut small_sets = [SmallLinkSet::from_slice(&pointers_small)];

        let pointers_packed = (21..=25).map(|i| AtomPtr(i)).collect::<Vec<_>>();

        large_sets[0].next = Link {
            atom: AtomPtr(1000),
            link: LinkPtr::new_small_link_set_index(0),
        };

        small_sets[0].next = Link {
            atom: AtomPtr(50),
            link: LinkPtr::new_packed_set(AtomPtr(50), &pointers_packed[0..5]),
        };

        let mut iter = LinkIter::new(
            Link {
                atom: AtomPtr(9),
                link: LinkPtr::new_large_link_set_index(0),
            },
            &small_sets,
            &large_sets,
        );

        for i in 10..=25 {
            assert_eq!(iter.next(), Some(AtomPtr(i)));
        }
        assert_eq!(iter.next(), None);
    }
}
