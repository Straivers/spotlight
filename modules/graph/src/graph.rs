use std::convert::TryFrom;

use crate::{
    atom::{Atom, AtomPtr},
    error::GraphError,
    link::{LargeLinkSet, Link, LinkIter, LinkKind, LinkPtr, Links, SmallLinkSet},
};

#[derive(Debug, Default)]
pub struct Graph {
    atoms: Vec<Atom>,
    links: Vec<Links>,

    small_link_sets: Vec<SmallLinkSet>,
    large_link_sets: Vec<LargeLinkSet>,

    free_small_link_sets: LinkPtr,
    free_large_link_sets: LinkPtr,
}

impl Graph {
    pub fn atom(&self, ptr: AtomPtr) -> &Atom {
        &self.atoms[ptr.0 as usize]
    }

    pub fn atom_mut(&mut self, ptr: AtomPtr) -> &mut Atom {
        &mut self.atoms[ptr.0 as usize]
    }

    pub fn add_atom(&mut self, text: &str) -> Result<AtomPtr, GraphError> {
        let atom = Atom::new(text)?;
        let index = u32::try_from(self.atoms.len()).map_err(|_| GraphError::TooManyAtoms)?;

        self.atoms.push(atom);

        Ok(AtomPtr(index))
    }

    pub fn iter_links(&self, atom: AtomPtr, link: LinkPtr) -> LinkIter {
        LinkIter::new(
            Link { atom, link },
            &self.small_link_sets,
            &self.large_link_sets,
        )
    }

    /// Adds a new link from one [Atom] to another at `index` position.
    pub fn add_link(&mut self, from: AtomPtr, to: AtomPtr, index: u32) {
        self.insert_link(self.links[from.0 as usize].links, from, to, index as usize);
    }

    /// Moves the `atom`'s link at `old_index` to `new_index`.
    pub fn move_link(&mut self, atom: AtomPtr, old_index: u32, new_index: u32) {
        todo!()
    }

    pub fn remove_link(&mut self, from: AtomPtr, to: AtomPtr) {
        todo!()
    }

    fn insert_link(
        &mut self,
        link_root: LinkPtr,
        atom: AtomPtr,
        mut dest: AtomPtr,
        index: usize,
    ) -> LinkPtr {
        match link_root.kind() {
            LinkKind::None => LinkPtr::new_atom_ptr(dest),
            LinkKind::AtomPointer => {
                LinkPtr::new_packed_set(atom, &[link_root.as_atom_ptr(), dest])
            }
            LinkKind::PackedOffsets => {
                let mut set = link_root.as_packed_set(atom);

                // TODO: Handle index positions within the set
                if set[4].is_null() && index < 4 {
                    set.copy_within(index..4, index + 1);
                    set[index] = dest;
                    return link_root;
                }

                let insert_index = set.iter_mut().find(|p| p.is_null());
                if let Some(index) = insert_index {
                    *index = dest;
                    return LinkPtr::new_packed_set(atom, &set);
                } else {
                    // allocate a new SmallLinkSet, copy the elements of set over, and use that
                    todo!()
                }
            }
            LinkKind::SmallLinkSetIndex => {
                let set_index = link_root.as_small_link_set_index() as usize;

                let (next, length) = {
                    let set = &mut self.small_link_sets[set_index];
                    if index <= set.length as usize {
                        if set.capacity() > 0 {
                            set.pointers
                                .copy_within(index..set.length as usize, index + 1);
                            set.pointers[index] = dest;
                            return link_root;
                        } else {
                            let last_index = set.length as usize - 1;
                            let last = set.pointers[last_index];
                            set.pointers.copy_within(index..last_index, index + 1);
                            set.pointers[index] = dest;
                            dest = last;
                        }
                        return link_root;
                    }

                    (set.next.link, set.length as usize)
                };

                let new_next = Link {
                    atom,
                    link: self.insert_link(next, atom, dest, index - length),
                };

                self.small_link_sets[set_index].next = new_next;

                link_root
            }
            _ => todo!(),
        }
    }
}
