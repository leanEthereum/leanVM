//! Typed table names, and values kept one per table.

use super::{ClassSpec, ClassTable};
use crate::rv::Class;
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};
use std::slice::Iter;

/// Number of instruction tables in the proof layout.
pub const N_TABLES: usize = 14;

/// An instruction table, named by the class it proves.
///
/// Every class but the illegal one has a table.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TableId(Class);

impl TableId {
    /// Sums, differences and comparisons.
    pub const ADD: Self = Self(Class::Add);
    /// AND, OR and XOR.
    pub const LOGIC: Self = Self(Class::Logic);
    /// The conditional branches.
    pub const BRANCH: Self = Self(Class::Branch);
    /// `jal`, `jalr` and the exit.
    pub const JUMP: Self = Self(Class::Jump);
    /// Byte, halfword and word loads.
    pub const LOAD: Self = Self(Class::Load);
    /// Byte, halfword and word stores.
    pub const STORE: Self = Self(Class::Store);
    /// Doubleword loads.
    pub const LD: Self = Self(Class::Ld);
    /// Doubleword stores.
    pub const SD: Self = Self(Class::Sd);
    /// Shifts.
    pub const SHIFT: Self = Self(Class::Shift);
    /// The low half of a product.
    pub const MUL: Self = Self(Class::Mul);
    /// The high half of a product.
    pub const MULH: Self = Self(Class::Mulh);
    /// Quotients and remainders.
    pub const DIV: Self = Self(Class::Div);
    /// The BLAKE2s compression.
    pub const HASH: Self = Self(Class::Hash);
    /// The extension-field product.
    pub const EXT: Self = Self(Class::Ext);

    /// Every table, in protocol order.
    pub const ALL: [Self; N_TABLES] = [
        Self::ADD,
        Self::LOGIC,
        Self::BRANCH,
        Self::JUMP,
        Self::LOAD,
        Self::STORE,
        Self::LD,
        Self::SD,
        Self::SHIFT,
        Self::MUL,
        Self::MULH,
        Self::DIV,
        Self::HASH,
        Self::EXT,
    ];

    /// The table proving `class`, if it has one.
    pub const fn of(class: Class) -> Option<Self> {
        match class {
            Class::Illegal => None,
            class => Some(Self(class)),
        }
    }

    /// The class the table proves.
    pub const fn class(self) -> Class {
        self.0
    }

    /// The table's position in protocol order.
    pub const fn index(self) -> usize {
        // Why: the classes with a table are declared in table order.
        self.0 as usize
    }

    /// The table's specification.
    pub const fn spec(self) -> &'static ClassSpec {
        match self.0 {
            Class::Add => &ClassSpec::ADD,
            Class::Logic => &ClassSpec::LOGIC,
            Class::Branch => &ClassSpec::BRANCH,
            Class::Jump => &ClassSpec::JUMP,
            Class::Load => &ClassSpec::LOAD,
            Class::Store => &ClassSpec::STORE,
            Class::Ld => &ClassSpec::LD,
            Class::Sd => &ClassSpec::SD,
            Class::Shift => &ClassSpec::SHIFT,
            Class::Mul => &ClassSpec::MUL,
            Class::Mulh => &ClassSpec::MULH,
            Class::Div => &ClassSpec::DIV,
            Class::Hash => &ClassSpec::HASH,
            Class::Ext => &ClassSpec::EXT,
            Class::Illegal => unreachable!(),
        }
    }

    /// The table's columns and bus interactions.
    pub fn class_table(self) -> &'static ClassTable {
        &ClassTable::all()[self]
    }

    /// The table's name, as reports print it.
    pub const fn name(self) -> &'static str {
        self.spec().name
    }
}

// Every table is at its own position, and proves the class its specification names.
const _: () = {
    let mut t = 0;
    while t < N_TABLES {
        let id = TableId::ALL[t];
        assert!(id.index() == t && id.spec().class as usize == t);
        t += 1;
    }
};

/// A key naming one of a machine's `N` tables.
pub trait TableKey<const N: usize>: Copy {
    /// Every table, in protocol order.
    const ALL: [Self; N];

    /// The table's position in protocol order.
    fn index(self) -> usize;
}

impl TableKey<N_TABLES> for TableId {
    const ALL: [Self; N_TABLES] = Self::ALL;

    fn index(self) -> usize {
        Self::index(self)
    }
}

/// One value per table, indexed by the table.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PerTable<T, K = TableId, const N: usize = N_TABLES> {
    values: [T; N],
    key: PhantomData<K>,
}

impl<T, K: TableKey<N>, const N: usize> PerTable<T, K, N> {
    /// The values, in protocol order.
    pub const fn new(values: [T; N]) -> Self {
        Self {
            values,
            key: PhantomData,
        }
    }

    /// Each table's value from `f`.
    pub fn from_fn(f: impl FnMut(K) -> T) -> Self {
        Self::new(K::ALL.map(f))
    }

    /// Each table's value through `f`.
    pub fn map<U>(self, f: impl FnMut(T) -> U) -> PerTable<U, K, N> {
        PerTable::new(self.values.map(f))
    }

    /// Each table with its value, in protocol order.
    pub fn iter(&self) -> impl Iterator<Item = (K, &T)> {
        K::ALL.into_iter().zip(&self.values)
    }

    /// The values, in protocol order.
    pub fn values(&self) -> Iter<'_, T> {
        self.values.iter()
    }

    /// Mutable references to the values of distinct tables, or none if a table repeats.
    pub fn get_disjoint_mut<const M: usize>(&mut self, tables: [K; M]) -> Option<[&mut T; M]> {
        self.values.get_disjoint_mut(tables.map(K::index)).ok()
    }

    /// The values as a slice, in protocol order.
    pub const fn as_slice(&self) -> &[T] {
        &self.values
    }

    /// The values, in protocol order.
    pub fn into_values(self) -> [T; N] {
        self.values
    }
}

impl<T, K: TableKey<N>, const N: usize> Index<K> for PerTable<T, K, N> {
    type Output = T;

    fn index(&self, table: K) -> &T {
        &self.values[table.index()]
    }
}

impl<T, K: TableKey<N>, const N: usize> IndexMut<K> for PerTable<T, K, N> {
    fn index_mut(&mut self, table: K) -> &mut T {
        &mut self.values[table.index()]
    }
}

impl<T: Default, K: TableKey<N>, const N: usize> Default for PerTable<T, K, N> {
    fn default() -> Self {
        Self::from_fn(|_| T::default())
    }
}
