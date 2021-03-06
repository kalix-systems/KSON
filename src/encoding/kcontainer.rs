use crate::{womp, Kson};

pub(crate) struct KContainer {
    pub(crate) internal: Option<Kson>,
}

impl KContainer {
    pub(crate) fn new() -> KContainer { KContainer { internal: None } }

    pub(crate) fn place(&mut self, k: Kson) {
        assert!(self.internal.is_none());
        self.internal = Some(k);
    }

    pub(crate) fn new_place(k: Kson) -> KContainer { KContainer { internal: Some(k) } }

    // TODO can this return a result?
    pub(crate) fn take(&mut self) -> Kson { self.internal.take().expect(womp!()) }

    pub(crate) fn is_none(&self) -> bool { self.internal.is_none() }
}
