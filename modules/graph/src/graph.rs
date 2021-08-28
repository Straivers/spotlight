use crate::{link::*, atom::*, error::GraphError};

use std::{convert::TryFrom, mem::MaybeUninit};

#[repr(C)]
#[derive(Debug)]
pub struct Graph<'a> {
    old_text: &'a str,
    old_atoms: &'a mut [Atom],
    old_small_links: &'a mut [SmallLinkSet],
    old_large_links: &'a mut [LargeLinkSet],
    
    empty_atoms: AtomPtr,

    new_text: String,
    new_atoms: Vec<Atom>,
    new_small_links: Vec<SmallLinkSet>,
    new_large_links: Vec<LargeLinkSet>,
}

impl<'a> Graph<'a> {
    pub fn new(old_text: &'a str, old_atoms: &'a mut [Atom], old_small_links: &'a mut [SmallLinkSet], old_large_links: &'a mut [LargeLinkSet]) -> Self {
        Self {
            old_text,
            old_atoms,
            old_small_links,
            old_large_links,
            empty_atoms: AtomPtr(0),
            new_text: String::new(),
            new_atoms: Vec::new(),
            new_small_links: Vec::new(),
            new_large_links: Vec::new(),
        }
    }

    pub fn add_atom(
        &mut self,
        _prev_versions: &[AtomPtr],
        text: &str,
    ) -> Result<AtomPtr, GraphError> {
        let text_length =
            TextLength(u16::try_from(text.len()).map_err(|_| GraphError::TextTooLong)?);
        let text_offset = TextOffset(
            u32::try_from(self.old_text.len() + self.new_text.len())
                .map_err(|_| GraphError::TextTooLong)?,
        );
        self.new_text.push_str(text);

        let mut atom = Atom::new(text_length, text_offset);

        // atom.metadata
        //     .get_mut()
        //     .next
        //     .copy_from_slice(&prev_versions[..std::cmp::min(8, prev_versions.len())]);

        let (_ptr, mut slot) = self.alloc()?;
        unsafe {
            slot.as_mut_ptr().write(&mut atom);
        }

        // extensions

        todo!()
    }

    pub fn atom(&self, pointer: AtomPtr) -> Result<&Atom, GraphError> {
        let end = AtomPtr(
            u32::try_from(self.old_atoms.len() + self.new_atoms.len())
                .map_err(|_| GraphError::TooManyAtoms)?,
        );

        if (pointer.0 as usize) < self.old_atoms.len() {
            Ok(&self.old_atoms[pointer.0 as usize])
        } else if pointer < end {
            Ok(&self.new_atoms[pointer.0 as usize - self.old_atoms.len()])
        } else {
            Err(GraphError::InvalidAtomPtr)
        }
    }

    pub fn atom_mut(&mut self, pointer: AtomPtr) -> Result<&mut Atom, GraphError> {
        let end = AtomPtr(
            u32::try_from(self.old_atoms.len() + self.new_atoms.len())
                .map_err(|_| GraphError::TooManyAtoms)?,
        );

        if (pointer.0 as usize) < self.old_atoms.len() {
            Ok(&mut self.old_atoms[pointer.0 as usize])
        } else if pointer < end {
            Ok(&mut self.new_atoms[pointer.0 as usize - self.old_atoms.len()])
        } else {
            Err(GraphError::InvalidAtomPtr)
        }
    }

    fn alloc(&mut self) -> Result<(AtomPtr, MaybeUninit<&mut Atom>), GraphError> {
        if self.empty_atoms == AtomPtr(0) {
            let ptr = AtomPtr(
                u32::try_from(self.old_atoms.len() + self.new_atoms.len())
                    .map_err(|_| GraphError::TooManyAtoms)?,
            );

            let atom = {
                let len = self.new_atoms.len() + 1;
                self.new_atoms.reserve(1);
                unsafe {
                    self.new_atoms.set_len(len);
                }
                MaybeUninit::new(&mut self.new_atoms[ptr.0 as usize])
            };

            Ok((ptr, atom))
        } else {
            let ptr = self.empty_atoms;
            // self.empty_atoms = self.atom(ptr)?.metadata.get().next[0];
            let atom = MaybeUninit::new(self.atom_mut(ptr)?);

            Ok((ptr, atom))
        }
    }
}
