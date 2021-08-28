use crate::{
    atom::{Atom, AtomPtr},
    error::GraphError,
    link::{LargeLinkSet, LinkIter, LinkPtr, Links, SmallLinkSet},
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
        todo!()
    }

    pub fn atom_mut(&mut self, ptr: AtomPtr) -> &mut Atom {
        todo!()
    }

    pub fn add_atom(&mut self, text: &str) -> Result<AtomPtr, GraphError> {
        todo!()
    }

    pub fn links_of(&self, atom: AtomPtr) -> LinkIter {
        todo!()
    }

    pub fn add_link(&mut self, from: AtomPtr, to: AtomPtr) {
        todo!()
    }

    pub fn move_link(&mut self, atom: AtomPtr, old_index: u32, new_index: u32) {
        todo!()
    }

    pub fn remove_link(&mut self, from: AtomPtr, to: AtomPtr) {
        todo!()
    }
}
