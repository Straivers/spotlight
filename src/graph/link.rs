use super::atom;
use std::convert::TryFrom;

#[derive(Debug, PartialEq, Eq)]
pub enum PtrKind {
    /// This pointer does not point to anything. The entire pointer is 0.
    None,

    /// The upper 30 bytes may be interpreted as 5 6-bit signed offsets from
    /// the current `Atom`. The low bits of the pointer are 0b01.
    Adjescent,

    /// The upper 30 bits may be interpreted as a single 30-bit `AtomPtr`. The
    /// low bits of the pointer are 0b11.
    FarUnary,

    /// The upper 30 bits index into a SmallPtrSet array in the graph. The low
    /// bits of the pointer are 0b10.
    FarSmall,

    /// The upper 30 bits index into a LargePtrSet array in the graph. The low
    /// bits of the pointer are 0b00.
    FarLarge,
}

impl PtrKind {
    pub const ADJESCENT: u32 = 0b01;
    pub const FAR_UNARY: u32 = 0b11;
    pub const FAR_SMALL: u32 = 0b10;
    pub const FAR_LARGE: u32 = 0b00;

    pub const ADJESCENT_MIN: i32 = -32;
    pub const ADJESCENT_MAX: i32 = 31;

    pub const FAR_INDEX_MAX: u32 = u32::MAX >> 2;
}

/// A packed link to atoms
#[repr(transparent)]
pub struct Ptr(u32);

impl Ptr {
    pub fn kind(&self) -> PtrKind {
        if self.0 == 0 {
            return PtrKind::None;
        }

        match self.0 & 0b11 {
            PtrKind::ADJESCENT => PtrKind::Adjescent,
            PtrKind::FAR_UNARY => PtrKind::FarUnary,
            PtrKind::FAR_SMALL => PtrKind::FarSmall,
            PtrKind::FAR_LARGE => PtrKind::FarLarge,
            _ => unreachable!(),
        }
    }

    pub fn new_adjescent(current: atom::Ptr, pointers: [atom::Ptr; 5]) -> Self {
        #[cfg(debug_assertions)]
        {
            let mut found_0 = false;
            for p in pointers {
                debug_assert_ne!(p, current);
                // check for non-trailing 0s
                debug_assert!(!found_0 || (p.0 == 0));
                found_0 = found_0 || p.0 == 0;
            }
        }

        let low_bits = PtrKind::ADJESCENT;

        // Use i32 offsets bc it's the same size as Ptr.0
        let mut offsets: [i32; 5] = [0; 5];
        for (i, p) in pointers.iter().enumerate() {
            let offset = i32::try_from((p.0 as i64) - (current.0 as i64)).unwrap();
            assert!(PtrKind::ADJESCENT_MIN <= offset && offset <= PtrKind::ADJESCENT_MAX);
            offsets[i] = offset;
        }

        let offset_bits: [u32; 5] = unsafe { std::mem::transmute(offsets) };

        let value = low_bits
            | ((offset_bits[0] & 0b111111) << 2)
            | ((offset_bits[1] & 0b111111) << 8)
            | ((offset_bits[2] & 0b111111) << 14)
            | ((offset_bits[3] & 0b111111) << 20)
            | ((offset_bits[4] & 0b111111) << 26);

        Self(value)
    }

    pub fn new_far_unary(pointer: atom::Ptr) -> Self {
        assert!(pointer.0 <= PtrKind::FAR_INDEX_MAX);
        Self((pointer.0 << 2) | PtrKind::FAR_UNARY)
    }

    pub fn as_adjescent(&self, current: atom::Ptr) -> [atom::Ptr; 5] {
        assert_eq!(self.kind(), PtrKind::Adjescent);

        let i = self.0 >> 2;
        let offsets = [
            i6_to_i32(i & 0b111111),
            i6_to_i32((i >> 6) & 0b111111),
            i6_to_i32((i >> 12) & 0b111111),
            i6_to_i32((i >> 18) & 0b111111),
            i6_to_i32((i >> 24) & 0b111111),
        ];

        let p = current.0 as i32;
        let p0 = p + offsets[0];
        let p1 = p + offsets[1];
        let p2 = p + offsets[2];
        let p3 = p + offsets[3];
        let p4 = p + offsets[4];

        [
            atom::Ptr(u32::try_from(p0).unwrap()),
            atom::Ptr(u32::try_from(p1).unwrap()),
            atom::Ptr(u32::try_from(p2).unwrap()),
            atom::Ptr(u32::try_from(p3).unwrap()),
            atom::Ptr(u32::try_from(p4).unwrap()),
        ]
    }

    pub fn as_far_unary(&self) -> atom::Ptr {
        assert_eq!(self.kind(), PtrKind::FarUnary);
        atom::Ptr(self.0 >> 2)
    }
}

enum Type {
    None,
    Set1,
    Set7,
    Set63,
}

pub struct Set {
    next: Ptr,
}

/// Does a raw conversion of the low 6 bits to an i64
fn i6_to_i32(raw_i6: u32) -> i32 {
    const OTHER_BITS: u32 = i32::BITS - 6;
    (raw_i6 as i32)
        .wrapping_shl(OTHER_BITS)
        .wrapping_shr(OTHER_BITS)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ptr_adjescent() {
        let ptr = Ptr::new_adjescent(
            atom::Ptr(3),
            [
                atom::Ptr(0),
                atom::Ptr(0),
                atom::Ptr(0),
                atom::Ptr(0),
                atom::Ptr(0),
            ],
        );

        {
            let ptr = Ptr::new_adjescent(
                atom::Ptr(3),
                [
                    atom::Ptr(1),
                    atom::Ptr(2),
                    atom::Ptr(4),
                    atom::Ptr(4),
                    atom::Ptr(5),
                ],
            );
            let offsets = ptr.as_adjescent(atom::Ptr(3));

            assert_eq!(offsets[0], atom::Ptr(1));
            assert_eq!(offsets[1], atom::Ptr(2));
            assert_eq!(offsets[2], atom::Ptr(4));
            assert_eq!(offsets[3], atom::Ptr(4));
            assert_eq!(offsets[4], atom::Ptr(5));
        }
    }

    #[test]
    #[should_panic]
    fn bad_ptr_adjescent() {
        let _ = Ptr::new_adjescent(
            atom::Ptr(3),
            [
                atom::Ptr(1),
                atom::Ptr(1),
                atom::Ptr(0),
                atom::Ptr(1),
                atom::Ptr(1),
            ],
        );
    }
}
