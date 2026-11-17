//! The surface AST produced by the parser: expressions, statements, functions.

use crate::field::F128;
use std::sync::Arc;

/// An expression. Arithmetic is the field's own: `+` is `XOR`, `*` is `MUL`.
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    /// Integer / field literal: a raw 128-bit value, the tower element whose
    /// two limbs its bits spell.
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
    GenPow(Arc<Expr>),
    /// `base ** e` with a non-`GEN` base and a compile-time exponent, by
    /// square-and-multiply at lowering: integer arithmetic in an index or bound
    /// position, field arithmetic in a value. The base may be runtime.
    Pow(Arc<Expr>, Arc<Expr>),
    /// A variable in scope.
    Var(String),
    Add(Arc<Expr>, Arc<Expr>),
    Mul(Arc<Expr>, Arc<Expr>),
    /// Integer subtraction, **compile-time only**: field subtraction is `+`
    /// (XOR), so `-` means something only in index space. Using one as a runtime
    /// field value is an error.
    Sub(Arc<Expr>, Arc<Expr>),
    /// Integer floor-division `a // b` and remainder `a % b`, **compile-time
    /// only** (the field has no integer division). Valid where an index /
    /// slice bound / `Const` argument is expected, or as a folded `if`
    /// condition; using one as a runtime field value is an error.
    Div(Arc<Expr>, Arc<Expr>),
    Mod(Arc<Expr>, Arc<Expr>),
    /// Field division `a / b` (single slash): a **runtime** field operation,
    /// `a · b⁻¹`. Lowered to one `MUL` whose quotient operand is unset, so the
    /// write-once back-solve fills it with `a · b⁻¹` and the `MUL` constraint
    /// pins `quotient · b == a` (§range-check trick). No hint: the inverse is
    /// nondeterministic but the constraint binds it. `b == 0` is rejected
    /// unless `a == 0` too: `0 / 0` leaves the quotient unconstrained. `1 / b`
    /// therefore enforces `b != 0`. Distinct from the compile-time `//` ([`Expr::Div`]).
    FieldDiv(Arc<Expr>, Arc<Expr>),
    /// Single-return function call in expression position.
    Call(String, Vec<Expr>),
    /// `HeapBuf(n)`: allocate a heap buffer of `n` cells; evaluates to its pointer.
    HeapBuf(u32),
    /// `HeapBuf(size)` with a *runtime* size carried **in the exponent**: the
    /// buffer holds `k` cells where `size = g^k` (so a size derived from a
    /// g-power count `n` is plain field arithmetic: `HeapBuf(n * n * GEN**2)`
    /// is `2·log(n) + 2` cells). The allocation is a prover convenience (like
    /// every base pointer), so an under-size only hurts the prover:
    /// overlapping regions trip write-once. Evaluates to the pointer.
    HeapBufDyn(Arc<Expr>),
    /// `StackBuf(n)`: allocate `n` *consecutive* frame (stack) cells, bound as a
    /// stack value. Its cells `sa[0..n]` are written/read directly (no heap deref),
    /// and a size-2 `StackBuf` is a valid `keccak` operand (the four 64-bit hash
    /// words live as two lanes in each of two consecutive 128-bit cells).
    StackBuf(u32),
    /// `arr[idx]`: read a cell. For a heap `arr` (a pointer), `m[arr·idx]` (idx a
    /// g-power). For a [`Expr::StackBuf`]: the frame cell `base + idx` (idx a
    /// compile-time integer), read directly.
    Index(Arc<Expr>, Arc<Expr>),
    /// `buf[lo:hi]`: a run of cells of a [`Expr::StackBuf`] (frame cells
    /// `base+lo..base+hi`) or of a [`Expr::HeapBuf`] (heap cells
    /// `ptr·g^lo..ptr·g^hi`), with compile-time integer bounds (`hi`
    /// exclusive). Meaningful as a `keccak` operand, a hint destination, or a
    /// function argument run.
    Slice(Arc<Expr>, Arc<Expr>, Arc<Expr>),
    /// `[a, b, …]`: an initialized [`Expr::StackBuf`], so `x = [a, b]` allocates
    /// a StackBuf of the element count and writes each element in place, sugar
    /// for the alloc-then-store idiom. Only meaningful as the RHS of a plain
    /// assignment (inside a function; a *top-level* `NAME = […]` is a constant
    /// array, see [`Ast::const_arrays`]).
    ListLit(Vec<Expr>),
    /// `[body for var in unroll(lo, hi)]`: the list literal of `body` at each integer `var` of
    /// `lo..hi`, expanded once the bounds are compile-time integers. Only a `keccak_cells`
    /// argument.
    ListComp(Arc<Expr>, String, Arc<Expr>, Arc<Expr>),
}

/// A statement, with the source line it came from. The line is what every
/// diagnostic names and what a compiled program's pc-to-line table is built
/// from: the AST is the only place that still knows it.
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
    /// write-once conflict is the assertion. See `FnExpand::lower_assert_ne`.
    AssertNe(Expr, Expr),
    /// `assert log X < log Y`, or `assert log X < k`: a range check in the
    /// exponent, proving `x < k` for `X = g^x`. See `FnExpand::lower_assert_lt`.
    AssertLt(Expr, LtBound),
    /// `f(args)` as a statement (returns discarded).
    Call(String, Vec<Expr>),
    /// `hint_witness(dest, "name")`: fill `dest` from the next entry of the named
    /// witness stream (the prover's `witness` argument), whose length must match. The same
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
    /// See `FnExpand::lower_if`.
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
    /// jump table in `main`'s frame. Every arm writes the same cells, exactly one of them running, so a
    /// target may be a name bound at the join or a `StackBuf` element written in
    /// place. See `FnExpand::lower_match`.
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
/// A runtime bound's meaning is the PROGRAM's to give: it owes a small `n`, by checking it
/// first (`assert_gpow(n)` bounds its log by the memory size), or `log X < log n` bounds `X`
/// by nothing.
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

/// A function parameter and its calling convention.
#[derive(Clone, Debug)]
pub(crate) struct Param {
    pub name: String,
    pub kind: ParamKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ParamKind {
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
pub(crate) struct Func {
    pub name: String,
    /// A function with a `Const` parameter is a template, specialized per
    /// distinct constant tuple before lowering.
    pub params: Vec<Param>,
    /// Compile-time shape of each source-level return value. Stack buffers use
    /// multiple physical ABI cells; everything else uses one cell.
    pub(crate) return_shapes: Vec<Shape>,
    pub body: Vec<Stmt>,
    /// `@inline`: expand at each call site instead of emitting a call, so the
    /// frame and the argument and return plumbing vanish. The body must be a
    /// single tail `return`, and is never lowered standalone.
    #[allow(
        dead_code,
        reason = "read by `formal/lean_vm/scripts/guest-export`, which compiles these sources as a module of its own"
    )]
    pub inline: bool,
}

/// A whole program: a set of functions including `main`.
#[derive(Clone, Debug)]
pub struct Ast {
    #[allow(
        dead_code,
        reason = "read by `formal/lean_vm/scripts/guest-export`, which compiles these sources as a module of its own"
    )]
    pub(crate) funcs: Vec<Func>,
    /// Top-level constant arrays `NAME = [a, b, c]`, in declaration order.
    /// Indexed `NAME[i]` and measured `len(NAME)` at compile time only, `i` being
    /// a literal, a constant or an `unroll` variable. Unlike a scalar constant
    /// these are not textually substituted, but resolved at lowering.
    pub const_arrays: Vec<(String, Vec<F128>)>,
}

/// Whether `s` itself binds `name`, nested blocks aside.
pub(crate) fn binds(s: &StmtKind, name: &str) -> bool {
    match s {
        StmtKind::Let(n, _) | StmtKind::LetHintWitness { name: n, .. } => n == name,
        StmtKind::LetTuple(ns, ..) => ns.iter().any(|n| n == name),
        StmtKind::Match { targets, .. } => targets.iter().any(|t| matches!(t, Expr::Var(n) if n == name)),
        _ => false,
    }
}

/// Whether `body` binds `name` where the binding may outlive the block: at its
/// own level, or in an `if` arm or an `unroll` body, even one whose counter has
/// that name, since only the counter is local to it (a `mul_range` body is a
/// function of its own).
fn binds_through(body: &[Stmt], name: &str) -> bool {
    body.iter().any(|s| match &s.kind {
        StmtKind::If { then, els, .. } => binds_through(then, name) || binds_through(els, name),
        StmtKind::Unroll { body, .. } => binds_through(body, name),
        kind => binds(kind, name),
    })
}

/// Whether `body` rebinds `name` inside an `if` arm or an `unroll` body.
///
/// A `Const` parameter or an `unroll` counter is bound by substituting a literal
/// for it (in Lean's `Expand`), which stops at a rebinding. At the name's own
/// level that is exact, but inside a block it is not: an `unroll` body's bindings
/// outlive it, and an `if` arm's do exactly when the condition folds, which
/// substitution, running first, cannot know.
pub(crate) fn rebinds_in_block(body: &[Stmt], name: &str) -> bool {
    body.iter().any(|s| match &s.kind {
        StmtKind::If { then, els, .. } => [then, els]
            .iter()
            .any(|arm| binds_through(arm, name) || rebinds_in_block(arm, name)),
        StmtKind::Unroll { body, .. } => binds_through(body, name) || rebinds_in_block(body, name),
        // Inside, `name` is the loop's own counter when it is named so.
        StmtKind::For { var, body, .. } => var != name && rebinds_in_block(body, name),
        _ => false,
    })
}
