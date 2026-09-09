//! The surface AST produced by the parser: expressions, statements, functions.

use primitives::field::F192;

/// An expression. Arithmetic is the field's own: `+` is `XOR`, `*` is `MUL`.
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    /// Integer / field literal: the source syntax provides a raw 128-bit value,
    /// embedded into the low two limbs of the 192-bit tower element (`c2 = 0`).
    Lit(u128),
    /// The generator `g`, written `GEN`. A logical index `i` rides the exponent
    /// as `gⁱ`, so `GEN` is the unit step.
    Gen,
    /// The field constant `g^k`. The exponent is a `u128`, so an index can be a
    /// large logical value.
    GPow(u128),
    /// `GEN ** e` for a compile-time integer *expression* `e` (an `unroll`
    /// variable, a constant, index arithmetic of those), resolved to a concrete
    /// `g^k` at lowering. Lets `buf[GEN ** i]` name cell `i` with no cursor.
    GenPow(Box<Expr>),
    /// `base ** e` with a non-`GEN` base and a compile-time exponent, by
    /// square-and-multiply at lowering: integer arithmetic in an index or bound
    /// position, field arithmetic in a value. The base may be runtime.
    Pow(Box<Expr>, Box<Expr>),
    /// A variable in scope.
    Var(String),
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    /// Integer subtraction, **compile-time only**: field subtraction is `+`
    /// (XOR), so `-` means something only in index space. Using one as a runtime
    /// field value is an error.
    Sub(Box<Expr>, Box<Expr>),
    /// Integer floor-division `a // b` and remainder `a % b`, **compile-time
    /// only** (the field has no integer division). Valid where an index /
    /// slice bound / `Const` argument is expected, or as a folded `if`
    /// condition; using one as a runtime field value is an error.
    Div(Box<Expr>, Box<Expr>),
    Mod(Box<Expr>, Box<Expr>),
    /// Field division `a / b` (single slash): a **runtime** field operation,
    /// `a · b⁻¹`. Lowered to one `MUL` whose quotient operand is unset, so the
    /// write-once back-solve fills it with `a · b⁻¹` and the `MUL` constraint
    /// pins `quotient · b == a` (§range-check trick). No hint: the inverse is
    /// nondeterministic but the constraint binds it. `b == 0` is rejected,
    /// including `0 / 0`; `1 / b` therefore also enforces `b != 0`. Distinct
    /// from the compile-time `//` ([`Expr::Div`]).
    FieldDiv(Box<Expr>, Box<Expr>),
    /// Single-return function call in expression position.
    Call(String, Vec<Expr>),
    /// `HeapBuf(n)`: allocate a heap buffer of `n` cells; evaluates to its pointer.
    HeapBuf(u64),
    /// `HeapBuf(size)` with a *runtime* size carried **in the exponent**: the
    /// buffer holds `k` cells where `size = g^k` (so a size derived from a
    /// g-power count `n` is plain field arithmetic: `HeapBuf(n * n * GEN**2)`
    /// is `2·log(n) + 2` cells). The allocation is a prover convenience (like
    /// every base pointer), so an under-size only hurts the prover:
    /// overlapping regions trip write-once. Evaluates to the pointer.
    HeapBufDyn(Box<Expr>),
    /// `StackBuf(n)`: allocate `n` *consecutive* frame (stack) cells, bound as a
    /// stack value. Its cells `sa[0..n]` are written/read directly (no heap deref),
    /// and a size-2 `StackBuf` is a valid `blake2s` operand (the four 64-bit hash
    /// words live as two lanes in each of two consecutive 128-bit cells).
    StackBuf(u64),
    /// `arr[idx]`: read a cell. For a heap `arr` (a pointer), `m[arr·idx]` (idx a
    /// g-power). For a [`Expr::StackBuf`]: the frame cell `base + idx` (idx a
    /// compile-time integer), read directly.
    Index(Box<Expr>, Box<Expr>),
    /// `buf[lo:hi]`: a run of cells of a [`Expr::StackBuf`] (frame cells
    /// `base+lo..base+hi`) or of a [`Expr::HeapBuf`] (heap cells
    /// `ptr·g^lo..ptr·g^hi`), with compile-time integer bounds (`hi`
    /// exclusive). Only meaningful as a `blake2s` operand, where it must span
    /// exactly 2 cells (one 256-bit value).
    Slice(Box<Expr>, Box<Expr>, Box<Expr>),
    /// `[a, b, …]`: an initialized [`Expr::StackBuf`], so `x = [a, b]` allocates
    /// a StackBuf of the element count and writes each element in place, sugar
    /// for the alloc-then-store idiom. Only meaningful as the RHS of a plain
    /// assignment (inside a function; a *top-level* `NAME = […]` is a constant
    /// array, see [`Ast::const_arrays`]).
    ListLit(Vec<Expr>),
}

/// A statement, with the source line it came from. The line is what every
/// lowering diagnostic names and what the pc-to-line table is built from: the
/// AST is the only place that still knows it, since lowering works in frame
/// cells and program counters.
#[derive(Clone, Debug)]
pub struct Stmt {
    pub line: u32,
    pub kind: StmtKind,
}

impl Stmt {
    pub fn new(line: u32, kind: StmtKind) -> Self {
        Self { line, kind }
    }

    /// A statement the compiler synthesized (a loop helper's body, a desugared
    /// tail call): it inherits the line of whatever it was generated for.
    pub fn at(&self, kind: StmtKind) -> Self {
        Self { line: self.line, kind }
    }
}

/// What a statement does.
#[derive(Clone, Debug)]
pub enum StmtKind {
    /// `x = expr` (immutable binding).
    Let(String, Expr),
    /// `x, y, … = f(args)`: call with multiple returns.
    LetTuple(Vec<String>, String, Vec<Expr>),
    /// `assert a == b`: a proof-enforced equality.
    AssertEq(Expr, Expr),
    /// `assert a != b`. Lowers to `x = a + b`, a hinted `inv = x⁻¹`, `p = x·inv`
    /// and `SET p = 1`: `x = 0` forces `p = 0` whatever the hint, so the
    /// write-once conflict is the assertion. See `FnLower::lower_assert_ne`.
    AssertNe(Expr, Expr),
    /// `assert log X < log Y`, or `assert log X < k`: a range check in the
    /// exponent, proving `x < k` for `X = g^x`. See `FnLower::lower_assert_lt`.
    AssertLt(Expr, LtBound),
    /// `f(args)` as a statement (returns discarded).
    Call(String, Vec<Expr>),
    /// `hint_witness(dest, "name")`: fill `dest` from the next entry of the named
    /// witness stream (`Program::set_witness`), whose length must match. The same
    /// name may be hinted many times, each call popping the next entry. Zero
    /// cycles and completely unconstrained, so the program must constrain the
    /// values itself.
    HintWitness { dest: Expr, name: String },
    /// `x = hint_witness("stream")`: one hinted value bound to a name, as
    /// unconstrained as any other hint. The run form above needs a destination
    /// that already exists, so a lone scalar otherwise costs a one-cell
    /// `StackBuf`, a slice of it, and a read back out.
    LetHintWitness { name: String, stream: String },
    /// `print("label", expr)`: a prover-side debug print, witness generation only.
    Print { label: String, value: Expr },
    /// `if lhs == rhs:` (`eq`) / `if lhs != rhs:`, with an optional `else` (an
    /// `elif` parses as an `else` holding a nested `if`). One conditional `JUMP`
    /// on the XOR of the sides. Bindings inside a branch are local to it, and the
    /// branches communicate through write-once memory, only one of them running.
    /// See `FnLower::lower_if`.
    If {
        eq: bool,
        lhs: Expr,
        rhs: Expr,
        then: Vec<Stmt>,
        els: Vec<Stmt>,
        /// Written `if const(a == b):`. The author asks for the branch to be
        /// decided while compiling, so a condition that cannot be decided then is
        /// an error rather than a runtime test, and one whose integer and field
        /// readings disagree is an error rather than a silent choice.
        force_const: bool,
    },
    /// `targets = match(log(x), range(a, b), lambda i: expr, …)`: the one dispatch
    /// construct. Arm `j` is the lambda body with the parameter replaced by the
    /// literal `j`, expanded at parse time, and `x = g^j` runs arm `j` through a
    /// trampoline table in the bytecode. Every arm writes the same cells, exactly
    /// one of them running, so a target may be a name bound at the join or a
    /// `StackBuf` element written in place. See `FnLower::lower_match`.
    Match {
        targets: Vec<Expr>,
        x: Expr,
        arms: Vec<Expr>,
    },
    /// `arr[idx] = value`: store into a heap cell (write-once).
    Store(Expr, Expr, Expr),
    /// `for i in mul_range(GEN ** lo, stop)`: the counter rides the exponent as
    /// `gⁱ`, advancing by `×g` from `g^lo` until it reaches `stop`, which is not
    /// itself executed. There is no step knob, the bounds being field elements
    /// (`mul_range(1, GEN ** 10)` runs ten times). A runtime `stop` must be known
    /// reachable: range-check its log, or the walk never terminates.
    For {
        var: String,
        lo: u64,
        hi: ForBound,
        body: Vec<Stmt>,
    },
    /// `for i in unroll(a, b)`: the body emitted `b − a` times with `i`
    /// substituted by each literal, so `i` is usable wherever a literal is. No
    /// call, no frame, no counter, at the price of code size. The bounds are
    /// compile-time integer expressions evaluated at lowering, after
    /// `Const`-parameter specialization, so `unroll(0, n)` with `n: Const` works.
    Unroll {
        var: String,
        lo: Expr,
        hi: Expr,
        body: Vec<Stmt>,
    },
    /// `return e, …` (a bare `return` is the empty vector).
    Return(Vec<Expr>),
    /// Internal, from loop lowering: `if lhs != rhs: callee(args)` in tail
    /// position, dispatched by `JUMP`'s nonzero test.
    CallIfNe(Expr, Expr, String, Vec<Expr>),
}

/// A `mul_range` stop bound: a compile-time `GEN ** k`, or a runtime g-power
/// element (evaluated once in the enclosing scope and threaded through the
/// loop helper as a parameter).
#[derive(Clone, Debug)]
pub enum ForBound {
    Const(u64),
    Runtime(Expr),
}

/// A range-check bound (`assert log X < …`): a compile-time exponent, or a
/// runtime `g^n`. Same gadget either way, only the cell holding `g^{k-1}`
/// differing.
///
/// A runtime bound loses the `k ≤ 2^MIN_LOG_MEM` cap the compiler would check,
/// so the PROGRAM owes it: range-check the bound itself first, or `log X < log n`
/// bounds `X` only by the prover-announced memory size.
#[derive(Clone, Debug)]
pub enum LtBound {
    Const(u64),
    Runtime(Expr),
}

/// Compile-time representation of a runtime parameter or return value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Shape {
    /// One ordinary field element or address cell. Heap buffers use this shape:
    /// allocation happens in the callee and only their pointer crosses.
    Scalar,
    /// A compile-time-sized run of consecutive frame cells.
    StackBuf(u32),
}

impl Shape {
    /// Number of physical call-frame cells occupied by this value.
    pub(crate) fn cells(self) -> u32 {
        match self {
            Self::StackBuf(n) => n,
            Self::Scalar => 1,
        }
    }
}

/// A function parameter and its calling convention.
#[derive(Clone, Debug)]
pub struct Param {
    pub name: String,
    pub kind: ParamKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParamKind {
    /// Substituted at the call site, with no runtime argument cell.
    Const,
    Runtime(Shape),
}

impl Param {
    pub(crate) fn shape(&self) -> Shape {
        match self.kind {
            ParamKind::Const => Shape::Scalar,
            ParamKind::Runtime(shape) => shape,
        }
    }
}

/// A function definition. `main` is the entry point.
#[derive(Clone, Debug)]
pub struct Func {
    pub name: String,
    /// A function with a `Const` parameter is a template, specialized per
    /// distinct constant tuple before lowering.
    pub params: Vec<Param>,
    /// Compile-time shape of each source-level return value. Stack buffers use
    /// multiple physical ABI cells; everything else uses one cell.
    pub return_shapes: Vec<Shape>,
    pub body: Vec<Stmt>,
    /// `@inline`: expand at each call site instead of emitting a call, so the
    /// frame and the argument and return plumbing vanish. The body must be a
    /// single tail `return`, and is never lowered standalone.
    pub inline: bool,
}

impl Func {
    pub(crate) fn has_const_params(&self) -> bool {
        self.params.iter().any(|p| p.kind == ParamKind::Const)
    }

    pub(crate) fn param_shapes(&self) -> impl Iterator<Item = Shape> + '_ {
        self.params.iter().map(Param::shape)
    }
}

/// A whole program: a set of functions including `main`.
#[derive(Clone, Debug)]
pub struct Ast {
    pub funcs: Vec<Func>,
    /// Top-level constant arrays `NAME = [a, b, c]`, in declaration order.
    /// Indexed `NAME[i]` and measured `len(NAME)` at compile time only, `i` being
    /// a literal, a constant or an `unroll` variable. Unlike a scalar constant
    /// these are not textually substituted, but resolved at lowering.
    pub const_arrays: Vec<(String, Vec<F192>)>,
}

// Free-variable analysis: pure AST, no lowering state. Its one consumer is the
// `for` desugaring, which needs the names a loop body reads from outside itself.

use std::collections::HashSet;

/// Collect variable references in `e` into `refs` (in source order).
fn free_vars_expr(e: &Expr, refs: &mut Vec<String>) {
    match e {
        Expr::Var(v) => refs.push(v.clone()),
        Expr::Add(a, b)
        | Expr::Mul(a, b)
        | Expr::Sub(a, b)
        | Expr::Div(a, b)
        | Expr::FieldDiv(a, b)
        | Expr::Mod(a, b)
        | Expr::Index(a, b)
        | Expr::Pow(a, b) => {
            free_vars_expr(a, refs);
            free_vars_expr(b, refs);
        }
        Expr::Slice(a, lo, hi) => {
            free_vars_expr(a, refs);
            free_vars_expr(lo, refs);
            free_vars_expr(hi, refs);
        }
        Expr::Call(_, args) | Expr::ListLit(args) => args.iter().for_each(|a| free_vars_expr(a, refs)),
        Expr::HeapBufDyn(sz) | Expr::GenPow(sz) => free_vars_expr(sz, refs),
        Expr::Lit(_) | Expr::Gen | Expr::GPow(_) | Expr::HeapBuf(_) | Expr::StackBuf(_) => {}
    }
}

/// Collect references in `s` into `refs` and names it binds into `bound`.
/// Every name the block binds, ignoring scope. [`free_vars_stmt`] deliberately
/// does not answer this: its `bound` set is scoped, so an arm-local binding is
/// discarded with the arm.
pub(crate) fn binds_anywhere(body: &[Stmt], out: &mut HashSet<String>) {
    for s in body {
        match &s.kind {
            StmtKind::Let(n, _) | StmtKind::LetHintWitness { name: n, .. } => {
                out.insert(n.clone());
            }
            StmtKind::LetTuple(ns, ..) => ns.iter().for_each(|n| {
                out.insert(n.clone());
            }),
            StmtKind::Match { targets, .. } => targets.iter().for_each(|t| {
                if let Expr::Var(n) = t {
                    out.insert(n.clone());
                }
            }),
            StmtKind::If { then, els, .. } => {
                binds_anywhere(then, out);
                binds_anywhere(els, out);
            }
            StmtKind::For { var, body, .. } | StmtKind::Unroll { var, body, .. } => {
                out.insert(var.clone());
                binds_anywhere(body, out);
            }
            _ => {}
        }
    }
}

/// Free variables of a block whose bindings do NOT escape it: it sees everything
/// bound so far, and anything it binds stays inside.
fn scoped_vars(body: &[Stmt], refs: &mut Vec<String>, bound: &HashSet<String>) {
    let mut inner = bound.clone();
    for s in body {
        free_vars_stmt(s, refs, &mut inner);
    }
}

pub(crate) fn free_vars_stmt(s: &Stmt, refs: &mut Vec<String>, bound: &mut HashSet<String>) {
    match &s.kind {
        StmtKind::Let(n, e) => {
            free_vars_expr(e, refs);
            bound.insert(n.clone());
        }
        StmtKind::LetTuple(ns, _, args) => {
            args.iter().for_each(|a| free_vars_expr(a, refs));
            ns.iter().for_each(|n| {
                bound.insert(n.clone());
            });
        }
        StmtKind::AssertEq(a, b) | StmtKind::AssertNe(a, b) => {
            free_vars_expr(a, refs);
            free_vars_expr(b, refs);
        }
        StmtKind::AssertLt(e, bound) => {
            free_vars_expr(e, refs);
            if let LtBound::Runtime(b) = bound {
                free_vars_expr(b, refs);
            }
        }
        StmtKind::HintWitness { dest, .. } => free_vars_expr(dest, refs),
        StmtKind::LetHintWitness { name, .. } => {
            bound.insert(name.clone());
        }
        StmtKind::Print { value, .. } => free_vars_expr(value, refs),
        StmtKind::If {
            lhs,
            rhs,
            then,
            els,
            force_const,
            ..
        } => {
            free_vars_expr(lhs, refs);
            free_vars_expr(rhs, refs);
            // An arm's bindings are local to it (`zkDSL.md` §Control flow), so each
            // gets its own scope. Sharing one made a name rebound in ONE arm count
            // as loop-local everywhere, so the OUTER binding the other arm reads
            // was never captured and a legal program failed with `unbound
            // variable`. Over-collecting into `refs` is harmless: a capture naming
            // nothing in the enclosing scope is dropped.
            // `lower_if` FOLDS a compile-time condition and runs the taken branch
            // without `scoped`, so its bindings persist exactly like an `unroll`
            // body's. Modelling that as scoped over-captured, and the loop's own
            // self-call then read a name the folded arm had rebound to a
            // `StackBuf`. Both sides literal is the syntactic half of that test.
            if *force_const || matches!((lhs, rhs), (Expr::Lit(_), Expr::Lit(_))) {
                then.iter().for_each(|s| free_vars_stmt(s, refs, bound));
                els.iter().for_each(|s| free_vars_stmt(s, refs, bound));
            } else {
                scoped_vars(then, refs, bound);
                scoped_vars(els, refs, bound);
            }
        }
        StmtKind::Match { targets, x, arms } => {
            free_vars_expr(x, refs);
            arms.iter().for_each(|a| free_vars_expr(a, refs));
            for t in targets {
                match t {
                    Expr::Var(n) => {
                        bound.insert(n.clone());
                    }
                    // A store target is READ, not bound: `sb[i], e = …` needs `sb`.
                    other => free_vars_expr(other, refs),
                }
            }
        }
        StmtKind::CallIfNe(a, b, _, args) => {
            free_vars_expr(a, refs);
            free_vars_expr(b, refs);
            args.iter().for_each(|e| free_vars_expr(e, refs));
        }
        StmtKind::Call(_, args) => args.iter().for_each(|a| free_vars_expr(a, refs)),
        StmtKind::Store(arr, idx, val) => {
            free_vars_expr(arr, refs);
            free_vars_expr(idx, refs);
            free_vars_expr(val, refs);
        }
        StmtKind::Return(es) => es.iter().for_each(|e| free_vars_expr(e, refs)),
        StmtKind::For { var, hi, body, .. } => {
            if let ForBound::Runtime(b) = hi {
                free_vars_expr(b, refs);
            }
            // A nested loop's body becomes its own function, so neither its
            // counter nor its bindings exist out here. `unroll` below is the
            // opposite: it replicates straight-line code into THIS scope, so its
            // bindings really do persist and it keeps the shared set.
            let mut inner = bound.clone();
            inner.insert(var.clone());
            body.iter().for_each(|s| free_vars_stmt(s, refs, &mut inner));
        }
        StmtKind::Unroll { var, lo, hi, body } => {
            free_vars_expr(lo, refs);
            free_vars_expr(hi, refs);
            bound.insert(var.clone());
            body.iter().for_each(|s| free_vars_stmt(s, refs, bound));
        }
    }
}
