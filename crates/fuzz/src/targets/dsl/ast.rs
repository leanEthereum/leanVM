//! The generator's program representation: what a generated program means, printed by [`super::print`] in any of
//! several equivalent spellings.

use primitives::field::{F64, F128};
use std::collections::HashMap;

pub type V = usize;
pub type FnId = usize;

/// A value expression.
#[derive(Clone, Debug)]
pub enum Ex {
    Lit(u128),
    /// A literal `0` that must be spelled as one (a `keccak` cell past `len`).
    Zero,
    Fe(F128),
    GPow(u64),
    Var(V),
    Add(Box<Ex>, Box<Ex>),
    Mul(Box<Ex>, Box<Ex>),
    Div(Box<Ex>, Box<Ex>),
    Pow(Box<Ex>, u32),
    /// `const(<integer expression>)`, already spelled.
    ConstInt(String),
    Arr(usize, Ix),
    SRead(V, Ix),
    HRead(V, HIx),
    /// The parameter of the enclosing `match` arm, as a value.
    J,
    /// `GEN ** (j + off)` for the enclosing arm's parameter.
    JPow(u32),
    /// `GEN ** (k + off)` for a `Const` parameter.
    KPow(V, u32),
    /// A call in expression position, of a function with one return.
    Call(Box<Call>),
}

/// A compile-time integer index.
#[derive(Clone, Copy, Debug)]
pub enum Ix {
    Lit(u32),
    /// An `unroll` counter plus an offset.
    Counter(V, u32),
    /// A `Const` parameter plus an offset.
    Param(V, u32),
    /// The `match` arm's parameter plus an offset.
    J(u32),
}

/// A heap index: a g-power.
#[derive(Clone, Copy, Debug)]
pub enum HIx {
    Const(u32),
    /// A scalar holding a g-power, times `GEN ** off`.
    Rt(V, u32),
}

#[derive(Clone, Debug)]
pub struct Call {
    pub f: FnId,
    pub args: Vec<Arg>,
}

#[derive(Clone, Debug)]
pub enum Arg {
    Val(Ex),
    Buf(V),
    Int(u32),
    J,
}

#[derive(Clone, Debug)]
pub enum Ret {
    Val(Ex),
    Buf(V),
}

/// A run of cells: a `keccak` operand, a hint destination.
#[derive(Clone, Debug)]
pub enum Run {
    Whole(V),
    Slice(V, u32, u32),
    /// `hb[x:x + len]`, `x` a scalar holding a g-power.
    HeapRt(V, V, u32),
    List(Vec<Ex>),
}

#[derive(Clone, Debug)]
pub enum Place {
    Stack(V, Ix),
    Heap(V, HIx),
}

#[derive(Clone, Debug)]
pub struct Seg {
    pub lo: u32,
    pub hi: u32,
    pub arm: Arm,
}

#[derive(Clone, Debug)]
pub enum Arm {
    Ex(Ex),
    Call(Call),
}

#[derive(Clone, Debug)]
pub enum Target {
    Var(V),
    Cell(V, u32),
}

/// What a `Let` may be spelled as besides `v = e`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Route {
    Direct,
    Any,
}

#[derive(Clone, Debug)]
pub enum St {
    Let(V, Ex, Route),
    LetHint(V, String),
    Hint(Run, String),
    Stack(V, u32),
    Heap(V, u32),
    HeapDyn(V, Ex),
    List(V, Vec<Ex>),
    Store(Place, Ex),
    AssertEq(Ex, Ex),
    AssertNe(Ex, Ex),
    AssertLt(Ex, u32),
    AssertLtRt(Ex, Ex),
    AssertInK(Ex, Ex),
    If {
        ne: bool,
        lhs: Ex,
        rhs: Ex,
        then: Vec<St>,
        els: Vec<St>,
    },
    /// `if const(k % m == r):` on a `Const` parameter.
    IfConst {
        k: V,
        m: u32,
        r: u32,
        then: Vec<St>,
        els: Vec<St>,
    },
    Match {
        targets: Vec<Target>,
        x: Ex,
        segs: Vec<Seg>,
    },
    Call(Vec<V>, Call),
    Loop(usize),
    Keccak {
        a: Run,
        b: Run,
        tail: Option<Run>,
        out: Run,
        len: Option<u32>,
    },
    KeccakCells {
        cells: Run,
        out: Run,
        len: Option<u32>,
    },
    Publish(u8, Ex),
    Return(Vec<Ret>),
}

/// Which spellings a construct allows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Never,
    Always,
    Either,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Form {
    Either,
    Unroll,
    MulRange,
}

#[derive(Clone, Debug)]
pub enum Hi {
    Const(u32),
    Rt(Ex),
}

#[derive(Clone, Debug)]
pub struct Loop {
    pub var: V,
    pub lo: u32,
    pub hi: Hi,
    pub body: Vec<St>,
    pub form: Form,
    /// The function the loop sits in.
    pub fun: FnId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PK {
    Scalar,
    Const,
    Stack(u32),
    Heap,
}

#[derive(Clone, Debug)]
pub struct Fun {
    pub params: Vec<(V, PK)>,
    pub body: Vec<St>,
    pub inline: Mode,
    /// Whether a `Const` parameter must be spelled `Const`, or may be a plain one.
    pub konst: Mode,
}

/// A generated program, before spelling.
#[derive(Clone, Debug, Default)]
pub struct Prog {
    /// `funs[0]` is `main`.
    pub funs: Vec<Fun>,
    pub loops: Vec<Loop>,
    pub arrays: Vec<Vec<u128>>,
    pub nvars: usize,
    /// The loop each counter variable belongs to.
    pub counter_of: HashMap<V, usize>,
    pub stack_sizes: HashMap<V, u32>,
}

pub fn lit(n: u128) -> F128 {
    F128::new(n as u64, (n >> 64) as u64)
}

pub fn gpow(k: u64) -> F128 {
    F64::G.pow(k as u128).into()
}

/// The literal spelling a value has: every word's bits spell one integer below `2^128`.
pub fn lit_of(v: F128) -> Ex {
    Ex::Lit(v.c0 as u128 | (v.c1 as u128) << 64)
}

/// Exponents of the g-powers the generator may meet as indices, scrutinees and range-checked values.
pub const LOG_TABLE: u32 = 1 << 17;

/// `e` when `v = g^e` with `e < LOG_TABLE`.
pub fn log_of(v: F128) -> Option<u32> {
    static TABLE: std::sync::OnceLock<HashMap<u64, u32>> = std::sync::OnceLock::new();
    if v.c1 != 0 {
        return None;
    }
    let table = TABLE.get_or_init(|| {
        let mut t = HashMap::with_capacity(LOG_TABLE as usize);
        let mut acc = F64::ONE;
        for e in 0..LOG_TABLE {
            t.entry(acc.0).or_insert(e);
            acc *= F64::G;
        }
        t
    });
    table.get(&v.c0).copied()
}
