use qcell::{LCellOwner, LCell};

pub struct Pool<'cell, T> {
    values: Vec<LCell<'cell, Option<T>>>,
}

pub struct Object<'pool, 'cell, T> {
    rf: &'pool LCell<'cell, Option<T>>,
}

impl<'cell, T> Default for Pool<'cell, T> {
    fn default() -> Self { Self::new() }
}

impl<'cell, T> Pool<'cell, T> {
    pub fn new() -> Self {
        Pool { values: (0..2).map(|_| LCell::new(None)).collect() }
    }

    pub fn push<'pool>(&'pool self, owner: &mut LCellOwner<'cell>, value: T) -> Object<'pool, 'cell, T> {
        let rf = self.values.iter().find(|cell| cell.ro(owner).is_none())
            .expect("max pool capacity exceeded");

        *rf.rw(owner) = Some(value);
        Object { rf }
    }
}

impl<'pool, 'cell, T>  Object<'pool, 'cell, T> {
    pub fn recover(self, owner: &mut LCellOwner<'cell,>) -> T {
        self.rf.rw(owner).take().unwrap()
    }
}

