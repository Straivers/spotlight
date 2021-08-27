mod atom;
mod link;

use std::{convert::TryFrom, mem::MaybeUninit};

#[derive(Debug, Clone, Copy)]
pub enum Error {
    TextTooLong,
    TooManyAtoms,
    InvalidAtomPtr,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct LinkPtr(u32);

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct LinkSet {

}

#[repr(C)]
#[derive(Debug)]
pub struct Graph<'a> {
    old_text: &'a str,
    old_atoms: &'a mut [atom::Atom],

    new_text: String,
    new_atoms: Vec<atom::Atom>,
    empty_atoms: atom::Ptr,
}

impl<'a> Graph<'a> {
    pub fn new(old_text: &'a str, old_atoms: &'a mut [atom::Atom]) -> Self {
        Self {
            old_text,
            old_atoms,
            new_text: String::new(),
            new_atoms: Vec::new(),
            empty_atoms: atom::Ptr(0),
        }
    }

    pub fn add_atom(&mut self, prev_versions: &[atom::Ptr], text: &str) -> Result<atom::Ptr, Error> {
        let text_length = atom::TextLength(u16::try_from(text.len()).map_err(|_| Error::TextTooLong)?);
        let text_offset = atom::TextOffset(
            u32::try_from(self.old_text.len() + self.new_text.len())
                .map_err(|_| Error::TextTooLong)?,
        );
        self.new_text.push_str(text);

        let mut atom = atom::Atom::new(text_length, text_offset);

        atom.metadata
            .get_mut()
            .next
            .copy_from_slice(&prev_versions[..std::cmp::min(8, prev_versions.len())]);

        let (ptr, mut slot) = self.alloc()?;
        unsafe { slot.as_mut_ptr().write(&mut atom) };

        // extensions

        todo!()
    }

    pub fn atom(&self, pointer: atom::Ptr) -> Result<&atom::Atom, Error> {
        let end = atom::Ptr(
            u32::try_from(self.old_atoms.len() + self.new_atoms.len())
                .map_err(|_| Error::TooManyAtoms)?,
        );

        if (pointer.0 as usize) < self.old_atoms.len() {
            Ok(&self.old_atoms[pointer.0 as usize])
        } else if pointer < end {
            Ok(&self.new_atoms[pointer.0 as usize - self.old_atoms.len()])
        } else {
            Err(Error::InvalidAtomPtr)
        }
    }

    pub fn atom_mut(&mut self, pointer: atom::Ptr) -> Result<&mut atom::Atom, Error> {
        let end = atom::Ptr(
            u32::try_from(self.old_atoms.len() + self.new_atoms.len())
                .map_err(|_| Error::TooManyAtoms)?,
        );

        if (pointer.0 as usize) < self.old_atoms.len() {
            Ok(&mut self.old_atoms[pointer.0 as usize])
        } else if pointer < end {
            Ok(&mut self.new_atoms[pointer.0 as usize - self.old_atoms.len()])
        } else {
            Err(Error::InvalidAtomPtr)
        }
    }

    fn alloc(&mut self) -> Result<(atom::Ptr, MaybeUninit<&mut atom::Atom>), Error> {
        if self.empty_atoms == atom::Ptr(0) {
            let ptr = atom::Ptr(
                u32::try_from(self.old_atoms.len() + self.new_atoms.len())
                    .map_err(|_| Error::TooManyAtoms)?,
            );

            let atom = {
                let len = self.new_atoms.len() + 1;
                self.new_atoms.reserve(1);
                unsafe { self.new_atoms.set_len(len) };
                MaybeUninit::new(&mut self.new_atoms[ptr.0 as usize])
            };

            Ok((ptr, atom))
        } else {
            let ptr = self.empty_atoms;
            self.empty_atoms = self.atom(ptr)?.metadata.get().next[0];
            let atom = MaybeUninit::new(self.atom_mut(ptr)?);

            Ok((ptr, atom))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn graph_size() {
        assert_eq!(std::mem::size_of::<atom::Ptr>(), 4);
        assert_eq!(std::mem::size_of::<atom::Type>(), 1);
        assert_eq!(std::mem::size_of::<atom::TextLength>(), 2);
        assert_eq!(std::mem::size_of::<atom::TextOffset>(), 4);

        assert_eq!(std::mem::size_of::<atom::Atom>(), 256);
    }
}
