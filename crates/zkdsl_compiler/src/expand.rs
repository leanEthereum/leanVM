//! The front end: each function the program runs, from its AST to its core function ([`crate::core_ir`]), by the
//! compiler's own rules. Every decision on the source is made here as lowering made it to bytecode: compile-time
//! evaluation ([`mod@eval`]), virtual bindings folded into addresses and constants, `Const` specialization, `@inline`
//! expansion, `unroll`, folded and runtime `if`, `match` with fused dispatch and chains, `mul_range` lifted to a
//! tail-recursive helper, `StackBuf` runs, heap addressing ([`mod@mem`]), calls ([`mod@call`]), the Keccak builtins
//! and the hints ([`mod@builtins`]).
//!
//! What the compiler's back end decided is not here: a value is a fresh number where lowering allocated a frame
//! cell, nothing is shared (a pooled constant, an interned pure result or a repeated load is a second atom on a
//! fresh value), and there is no frame plumbing (frame and return pointers, jump targets, jump tables). Values
//! allocated together ([`FnExpand::alloc_stack`]) are a run, which is what a `keccak` operand used in place needs.
//! Lean's expansion (`formal/lean_vm/LeanVM/Guest/Expand.lean`) is the other implementation of this pass;
//! `scripts/frontend-diff` compares the two on the guest and the test programs.

use super::*;
use crate::core_ir::{Atom, Dest, Hint, Stmt as CStmt, V};
use std::collections::HashSet;

mod builtins;
mod call;
mod eval;
mod mem;
use call::ret_binding;
use eval::{field_pow, small_gpow};

/// A value equal to `base·g^exp`, or the constant `g^exp` without a base; `run` is the length of the frame run an
/// `addr` pointer names.
#[derive(Clone, Copy)]
struct GAddr {
    base: Option<V>,
    exp: u128,
    run: Option<u32>,
}

/// Cap on a `β`-folded exponent, inclusive.
const FOLD_MAX: u128 = 1 << 16;

/// How an inlined tail-return value binds into the caller.
#[derive(Clone, Copy)]
enum RetBind {
    Stack(V, u32),
    Gaddr(GAddr),
    Scalar,
}

/// What a name is bound to.
#[derive(Clone, Copy)]
enum Binding {
    Scalar(V),
    Stack(V, u32),
    Gaddr(GAddr),
    FConst(F128),
}

/// A name's binding and its compile-time integer reading.
#[derive(Clone, Copy)]
struct Bound {
    val: Binding,
    int: Option<u128>,
}

/// A materialized shifted pointer: `out` holds `base·g^exp`, made as `src·g^dist`.
#[derive(Clone, Copy)]
struct Mat {
    exp: u128,
    out: V,
    src: V,
    dist: u128,
}

/// What reverts at a branch join: the name bindings, the constants set (which decide how a shifted pointer is
/// made), the shifted pointers materialized, and the `keccak` padding run.
#[derive(Clone, Default)]
struct Scope {
    names: HashMap<String, Bound>,
    consts: HashSet<F128>,
    mats: HashMap<V, Vec<Mat>>,
    keccak_pad: Option<V>,
}

impl Scope {
    fn bound(&self, n: &str) -> Option<Bound> {
        self.names.get(n).copied()
    }
    fn stack(&self, n: &str) -> Option<(V, u32)> {
        match self.bound(n)?.val {
            Binding::Stack(base, size) => Some((base, size)),
            _ => None,
        }
    }
    fn int(&self, n: &str) -> Option<u128> {
        self.bound(n)?.int
    }
    fn set_int(&mut self, n: &str, k: u128) {
        if let Some(b) = self.names.get_mut(n) {
            b.int = Some(k);
        }
    }
}

/// A run of consecutive values, or a heap slice (the pointer and the first g-power offset).
enum CellRun {
    Stack { base: V, len: u32 },
    Heap { ptr: V, lo: u32, len: u32 },
}

struct FnExpand<'a> {
    scope: Scope,
    next: V,
    /// The first value of each value's run.
    group: Vec<V>,
    return_shapes: &'a [Shape],
    is_main: bool,
    /// The block being written.
    out: Vec<CStmt>,
    /// A hint was emitted since the last instruction.
    pending: bool,
    /// Declared size of each `HeapBuf`, by its pointer.
    heap_sizes: HashMap<V, u128>,
    /// The run each `addr` pointer names, as its first value and length.
    addr_runs: HashMap<V, (V, u32)>,
    inline_ret: Option<Vec<V>>,
    inline_stack_ret: Option<Vec<RetBind>>,
    cur_line: u32,
    /// The scrutinee of the `match` the one being expanded enters directly.
    chain_next: Option<V>,
    /// Set for a `match` an earlier one's arms dispatch into: its scrutinee.
    chain_in: Option<V>,
    inline_calls: Vec<String>,
    queue: &'a mut Vec<Func>,
    loop_ctr: &'a mut usize,
    fn_name: &'a str,
    defs: &'a HashMap<&'a str, &'a Func>,
    const_arrays: &'a HashMap<&'a str, &'a [F128]>,
}

impl FnExpand<'_> {
    /// Abort with a diagnostic naming the source line and the function.
    fn fail(&self, msg: impl std::fmt::Display) -> ! {
        let site = match (self.cur_line, self.fn_name) {
            (0, "main") => String::new(),
            (0, f) => format!("in {f}: "),
            (n, "main") => format!("line {n}: "),
            (n, f) => format!("line {n} in {f}: "),
        };
        match self.inline_calls.as_slice() {
            [] => panic!("{site}{msg}"),
            chain => panic!("{site}{msg} (inlined through {})", chain.join(" -> ")),
        }
    }

    /// `n` fresh values, one run: the first is returned, the others follow it.
    fn alloc_stack(&mut self, n: u32) -> V {
        let base = self.next;
        self.next = base
            .checked_add(n)
            .unwrap_or_else(|| self.fail("the function outgrows 2^32 values"));
        self.group.extend(std::iter::repeat_n(base, n as usize));
        base
    }

    fn fresh(&mut self) -> V {
        self.alloc_stack(1)
    }

    /// Whether `b` follows `a` in one run.
    fn adjacent(&self, a: V, b: V) -> bool {
        b == a + 1 && self.group[a as usize] == self.group[b as usize]
    }

    fn run(base: V, len: u32) -> Vec<V> {
        (base..base + len).collect()
    }

    /// A statement: it carries instructions, so a pending hint fires on it.
    fn emit(&mut self, s: CStmt) {
        self.out.push(s);
        self.pending = false;
    }

    fn atom(&mut self, a: Atom) {
        self.emit(CStmt::Atom(a));
    }

    /// A hint, pending until the next instruction.
    fn hint(&mut self, h: Hint) {
        self.out.push(CStmt::Atom(Atom::Hint(h)));
        self.pending = true;
    }

    /// An `addr`, which is no instruction of its own.
    fn frame_addr(&mut self, p: V, base: V, len: u32) {
        self.out.push(CStmt::Atom(Atom::FrameAddr(p, Self::run(base, len))));
    }

    /// Run `f` writing into a fresh block, and return the block.
    fn capture(&mut self, f: impl FnOnce(&mut Self)) -> Vec<CStmt> {
        let out = std::mem::take(&mut self.out);
        let pending = std::mem::replace(&mut self.pending, false);
        f(self);
        self.pending = pending;
        std::mem::replace(&mut self.out, out)
    }

    fn set_const(&mut self, o: V, v: F128) {
        self.atom(Atom::Const(o, v));
    }

    /// A fresh value holding `v`, recorded as a constant set in this scope.
    fn const_cell(&mut self, v: F128) -> V {
        let o = self.fresh();
        self.set_const(o, v);
        self.scope.consts.insert(v);
        o
    }

    fn pure_add(&mut self, a: V, b: V) -> V {
        let o = self.fresh();
        self.atom(Atom::Add(o, a, b));
        o
    }

    fn pure_mul(&mut self, a: V, b: V) -> V {
        let o = self.fresh();
        self.atom(Atom::Mul(o, a, b));
        o
    }

    /// `dst = src`.
    fn copy(&mut self, src: V, dst: V) {
        self.atom(Atom::Copy(dst, src));
    }

    /// An instruction for a pending hint to fire on, so that it fires here.
    fn anchor(&mut self) {
        let o = self.fresh();
        self.set_const(o, F128::ZERO);
    }

    /// A top-level constant array's name is reserved.
    fn check_not_reserved(&self, name: &str) {
        if self.const_arrays.contains_key(name) {
            self.fail(format!(
                "`{name}` is a top-level constant array, so the name is reserved: rename the local \
             or parameter (zkDSL.md §Global constants)"
            ))
        };
    }

    /// Replace the binding, clearing its previous compile-time integer reading.
    fn rebind(&mut self, name: &str, b: Binding) {
        self.check_not_reserved(name);
        self.scope.names.insert(name.to_string(), Bound { val: b, int: None });
    }

    fn bind_targets(&mut self, binds: &[(&str, V)]) {
        for (name, cell) in binds {
            self.rebind(name, Binding::Scalar(*cell));
        }
    }

    /// The value `arr[idx]` names, bounds-checked, or `None` when `arr` is not a `StackBuf`.
    fn frame_cell(&self, arr: &Expr, idx: &Expr) -> Option<V> {
        let (base, size) = self.stack_of(arr)?;
        let k = self.const_index(idx);
        if k >= size {
            self.fail(format!("index {k} out of bounds (StackBuf size {size})"))
        };
        Some(base + k)
    }

    /// A branch body, its scope reverted afterwards; a hint pending at its end fires on an anchor in it.
    fn branch(&mut self, body: &[Stmt]) -> Vec<CStmt> {
        let saved = self.scope.clone();
        let block = self.capture(|s| {
            for st in body {
                s.stmt(st);
            }
            if s.pending {
                s.anchor();
            }
        });
        self.scope = saved;
        block
    }

    /// The value each multi-value target names, and the names to bind: a name takes a value of one fresh run, a
    /// `StackBuf` element is its own value.
    fn ret_targets<'a>(&mut self, targets: &'a [Expr]) -> (Vec<V>, Vec<(&'a str, V)>) {
        let names = targets.iter().filter(|t| matches!(t, Expr::Var(_))).count() as u32;
        let mut next = self.alloc_stack(names);
        let mut cells = Vec::with_capacity(targets.len());
        let mut binds = Vec::new();
        for t in targets {
            match t {
                Expr::Index(arr, idx) => match self.frame_cell(arr, idx) {
                    Some(c) => cells.push(c),
                    None => self.fail(
                        "a `match` or tuple-call target must be a name or a StackBuf element, not a heap \
                         cell: bind a name and store it",
                    ),
                },
                Expr::Var(n) => {
                    cells.push(next);
                    binds.push((n.as_str(), next));
                    next += 1;
                }
                other => self.fail(format!(
                    "a `match` or tuple-call target must be a name or a StackBuf element, got `{other:?}`"
                )),
            }
        }
        (cells, binds)
    }

    /// `targets = match(log(x), …)`: a fused dispatch when every arm calls one function with the same runtime
    /// arguments, else one block per arm, arm `j` evaluating its body into the values every arm shares.
    fn lower_match(&mut self, targets: &[Expr], x: &Expr, arms: &[Expr]) {
        for arm in arms {
            if let Expr::Call(f, _) = arm
                && self
                    .defs
                    .get(f.as_str())
                    .is_some_and(|d| !d.inline && d.return_shapes.iter().any(|s| matches!(s, Shape::StackBuf(_))))
            {
                self.fail("a normal function's StackBuf return cannot cross a match join; bind it with `let`");
            }
        }
        if arms
            .iter()
            .all(|a| matches!(a, Expr::Call(f, _) if self.defs.get(f.as_str()).is_some_and(|d| !d.inline)))
        {
            let specialized: Vec<(String, Vec<&Expr>)> = arms
                .iter()
                .map(|a| {
                    let Expr::Call(f, cargs) = a else { unreachable!() };
                    self.specialize(f, cargs)
                })
                .collect();
            let rt0 = &specialized[0].1;
            if specialized.iter().all(|(_, rt)| rt == rt0) {
                let callees: Vec<String> = specialized.iter().map(|(c, _)| c.clone()).collect();
                self.lower_dispatched_call(targets, x, &callees, rt0);
                return;
            }
        }
        // A chained match is entered from the previous one's arms: its scrutinee is the value the chain named,
        // and nothing is set above its arms.
        let (chain_next, chain_in) = (self.chain_next.take(), self.chain_in.take());
        let xo = match chain_in {
            Some(c) => c,
            None => self.expr(x),
        };
        let (rcells, binds) = self.ret_targets(targets);
        if chain_in.is_none() && self.all_inline(arms) {
            self.keccak_pad_run();
            self.const_cell(builtins::two_to_one_close());
        }
        let mut blocks = Vec::with_capacity(arms.len());
        for arm in arms {
            let saved = self.scope.clone();
            let block = self.capture(|s| {
                if let [rcell] = rcells.as_slice() {
                    s.expr_into(arm, *rcell);
                } else {
                    let Expr::Call(f, cargs) = arm else {
                        s.fail(format!(
                            "a multi-target match arm must be a function call, got `{arm:?}`"
                        ));
                    };
                    s.inline_stack_ret = None;
                    s.call_into(f, cargs, &rcells);
                    if let Some(binds) = s.inline_stack_ret.take() {
                        for (b, &rc) in binds.iter().zip(&rcells) {
                            match *b {
                                RetBind::Gaddr(ga) => {
                                    let c = s.materialize(ga);
                                    s.copy(c, rc);
                                }
                                RetBind::Stack(base, size) => {
                                    if size != 1 {
                                        s.fail("a multi-cell StackBuf return cannot cross a match join")
                                    }
                                    s.copy(base, rc);
                                }
                                RetBind::Scalar => {}
                            }
                        }
                    }
                }
                if s.pending {
                    s.anchor();
                }
            });
            self.scope = saved;
            blocks.push(block);
        }
        self.emit(CStmt::Match(xo, blocks));
        self.chain_in = chain_next;
        self.bind_targets(&binds);
    }

    /// The value `e` names, if reading it emits nothing and names nothing `targets` rebinds: a scalar variable, or
    /// a `StackBuf` element at a compile-time index. Only such a scrutinee can chain.
    fn free_cell(&self, e: &Expr, targets: &[Expr]) -> Option<V> {
        let mut names = Vec::new();
        crate::ast::free_vars_expr(e, &mut names);
        if names
            .iter()
            .any(|n| targets.iter().any(|t| matches!(t, Expr::Var(v) if v == n)))
        {
            return None;
        }
        match e {
            Expr::Var(n) => match self.scope.bound(n)?.val {
                Binding::Scalar(o) => Some(o),
                _ => None,
            },
            Expr::Index(b, i) => {
                let (Expr::Var(n), Some(k)) = (&**b, self.try_const_index(i)) else {
                    return None;
                };
                let (base, len) = self.scope.stack(n)?;
                (k < len).then_some(base + k)
            }
            _ => None,
        }
    }

    /// Whether every arm is an `@inline` call.
    fn all_inline(&self, arms: &[Expr]) -> bool {
        arms.iter()
            .all(|a| matches!(a, Expr::Call(f, _) if self.defs.get(f.as_str()).is_some_and(|d| d.inline)))
    }

    /// `if` / `else`: folded when both sides are compile-time integers (or `const(...)` field constants), its arm
    /// expanded in place with its bindings persisting; else a branch on `lhs + rhs`, zero for equal.
    fn lower_if(&mut self, eq: bool, lhs: &Expr, rhs: &Expr, then: &[Stmt], els: &[Stmt], force_const: bool) {
        let (a, b) = (self.eval(lhs), self.eval(rhs));
        if let (Some(ai), Some(bi)) = (a.int, b.int) {
            if !force_const {
                for (e, known) in [(lhs, a), (rhs, b)] {
                    if let Some((n, f)) = known.diverging_readings() {
                        self.fail(format!(
                            "`{e:?}` reads as the integer {n} where a condition folds, and as the field \
                             element {:#x}:{:#x} where a value is wanted, so this branch would be decided \
                             by one reading and its body run under the other. Write `if const(...)` to \
                             decide it with integer arithmetic, or spell the operand so the two agree.",
                            f.c1, f.c0
                        ))
                    }
                }
            }
            for st in if (ai == bi) == eq { then } else { els } {
                self.stmt(st);
            }
            return;
        }
        if force_const {
            if let (Some(fa), Some(fb)) = (a.field, b.field) {
                for st in if (fa == fb) == eq { then } else { els } {
                    self.stmt(st);
                }
                return;
            }
            self.fail("`if const(...)` asks for a compile-time decision, but this condition is not one: both sides must be compile-time constants")
        }
        let x = if self.try_lit(rhs) == Some(0) {
            self.expr(lhs)
        } else if self.try_lit(lhs) == Some(0) {
            self.expr(rhs)
        } else {
            let (la, lb) = (self.expr(lhs), self.expr(rhs));
            self.pure_add(la, lb)
        };
        let (zero, nonzero) = if eq { (then, els) } else { (els, then) };
        let zero = self.branch(zero);
        let nonzero = if nonzero.is_empty() {
            Vec::new()
        } else {
            self.branch(nonzero)
        };
        self.emit(CStmt::Ite(x, zero, nonzero));
    }

    /// `assert a != b`: `x = a + b`, a hinted inverse, and the atom `x · inv = 1`.
    fn lower_assert_ne(&mut self, a: &Expr, b: &Expr) {
        if let (Expr::Lit(x), Expr::Lit(y)) = (a, b) {
            if x == y {
                self.fail(format!("assert a != b: sides are the compile-time-equal literal {x}"))
            };
            return;
        }
        let (la, lb) = (self.expr(a), self.expr(b));
        let x = self.pure_add(la, lb);
        let inv = self.fresh();
        self.hint(Hint::Inverse { x, dst: inv });
        let p = self.fresh();
        self.atom(Atom::AssertNe(x, inv, p));
    }

    /// `assert log x < log GEN ** k`: the range check against a value holding `g^{k-1}`.
    fn lower_assert_lt(&mut self, e: &Expr, bound: &LtBound) {
        let kcell = match bound {
            LtBound::Const(k) => {
                if *k < 1 {
                    self.fail("range-check bound GEN ** 0 names the empty set")
                };
                if *k > 1 << verifier::MAX_LOG_MEMORY {
                    self.fail(format!(
                        "range-check bound GEN ** {k} exceeds 2^{} (the largest memory size)",
                        verifier::MAX_LOG_MEMORY
                    ))
                };
                self.const_cell(F64::G.pow(u128::from(*k - 1)).into())
            }
            LtBound::Runtime(b) => {
                if self.try_field_const(b).is_some() {
                    self.fail(
                        "a compile-time range-check bound must be written as `log GEN ** k` or an \
                     integer, so that its cap applies",
                    )
                };
                if let Some(
                    ga @ GAddr {
                        base: Some(_),
                        exp: 1..,
                        run: None,
                    },
                ) = self.gaddr_of(b)
                {
                    let kcell = self.materialize(GAddr { exp: ga.exp - 1, ..ga });
                    return self.range_check(e, kcell);
                }
                let bcell = self.expr(b);
                let inv = self.const_cell(F128::from(F64::G.inv()));
                self.pure_mul(bcell, inv)
            }
        };
        self.range_check(e, kcell);
    }

    fn range_check(&mut self, e: &Expr, kcell: V) {
        let x = self.expr(e);
        let y = self.fresh();
        let t1 = self.fresh();
        let t2 = self.fresh();
        self.atom(Atom::RangeCheck(x, y, t1, t2, kcell));
    }

    /// A value holding `e`.
    fn expr(&mut self, e: &Expr) -> V {
        if let Some(v) = self.try_field_const(e) {
            return self.const_cell(v);
        }
        match e {
            Expr::Lit(_) | Expr::Gen | Expr::GPow(_) => unreachable!("a literal folds above"),
            Expr::GenPow(e) => {
                let k = self.gpow_exp(e);
                self.const_cell(F64::G.pow(k).into())
            }
            Expr::Pow(b, e) => self.pow_expr(b, e),
            Expr::Var(v) => match self.scope.bound(v).map(|b| b.val) {
                Some(Binding::Stack(..)) => {
                    self.fail(format!("StackBuf `{v}` used as a scalar; index it (`{v}[k]`) or pass it to keccak"));
                }
                Some(Binding::Gaddr(ga)) => self.materialize(ga),
                Some(Binding::Scalar(o)) => o,
                _ => {
                    if self.fn_name.starts_with("__loop") {
                        self.fail(format!(
                            "unbound variable `{v}` in a `for` loop body. If `{v}` names a value from \
                             outside the loop that this body also assigns to, the loop cannot carry it: \
                             the helper threads its captures in, not out. Assign to a new name inside \
                             the body, or carry state through a `HeapBuf`."
                        ))
                    }
                    self.fail(format!("unbound variable `{v}`"))
                }
            },
            Expr::Add(a, b) => {
                if let Some(x) = self.add_identity(a, b) {
                    return self.expr(x);
                }
                let (la, lb) = (self.expr(a), self.expr(b));
                self.pure_add(la, lb)
            }
            Expr::Mul(a, b) => {
                if let Some(x) = self.mul_identity(a, b) {
                    return self.expr(x);
                }
                if let Some(ga @ GAddr { base: Some(_), .. }) = self.gaddr_of(e) {
                    return self.materialize(ga);
                }
                let (la, lb) = (self.expr(a), self.expr(b));
                self.pure_mul(la, lb)
            }
            // `q = a / b` as `a = q · b`.
            Expr::FieldDiv(a, b) => {
                let (la, lb) = (self.expr(a), self.expr(b));
                let q = self.fresh();
                self.atom(Atom::Mul(la, q, lb));
                q
            }
            Expr::Call(f, args) if f == "const" => {
                if args.len() != 1 {
                    self.fail(format!("const(...) takes one expression, got {}", args.len()))
                };
                self.fail(format!(
                    "const(...) asks for a compile-time integer, and `{:?}` is not one",
                    args[0]
                ))
            }
            Expr::Call(f, args) if f == "addr" => {
                let ga = self.stack_addr(args);
                self.materialize(ga)
            }
            Expr::Call(f, args) if f == "hint_log2_ceil" => {
                if args.len() != 3 {
                    self.fail(format!(
                        "hint_log2_ceil takes three arguments, `(bits, nbits, floor)`, got {}",
                        args.len()
                    ))
                }
                let nbits = self.const_index(&args[1]);
                if nbits > 128 {
                    self.fail(format!("hint_log2_ceil reads at most 128 bits, got {nbits}"))
                }
                let floor = self.const_index(&args[2]);
                let bits = self.bits_dest(&args[0], nbits, "hint_log2_ceil");
                let dst = self.fresh();
                self.hint(Hint::Log2Ceil { bits, nbits, floor, dst });
                dst
            }
            Expr::Call(f, args) => {
                let d = self.call(f, args, 1)[0];
                self.take_inline_ret_cell(d)
            }
            Expr::HeapBuf(n) => {
                let arr = self.fresh();
                self.heap_sizes.insert(arr, u128::from(*n));
                self.hint(Hint::Alloc { dst: arr, size: *n });
                arr
            }
            Expr::HeapBufDyn(e) => {
                let size = self.expr(e);
                let arr = self.fresh();
                self.hint(Hint::AllocDyn { dst: arr, size });
                arr
            }
            Expr::StackBuf(_) => self.fail("StackBuf(n) must be bound to a name: `x = StackBuf(n)`"),
            Expr::Index(arr, idx) => {
                if let Some(c) = self.frame_cell(arr, idx) {
                    return c;
                }
                let (ptr, o2) = self.heap_addr(arr, idx);
                let dst = self.fresh();
                self.atom(Atom::Load(dst, ptr, o2));
                dst
            }
            Expr::Sub(..) | Expr::Div(..) | Expr::Mod(..) => {
                self.fail(format!(
                    "`-`, `//`, `%` are compile-time only (field subtraction is `+`); use them in an index, a bound, or a `Const` argument, got `{e:?}`"
                ))
            }
            Expr::Slice(..) => self.fail("a slice is not a scalar; it is only a keccak operand"),
            Expr::ListLit(..) => self.fail("a list literal must be bound to a name: `x = [a, b]`"),
            Expr::ListComp(..) => self.fail("a list comprehension is only a keccak_cells argument"),
        }
    }

    /// `base ** e`, a non-`GEN` base and a compile-time exponent: one constant, or square-and-multiply.
    fn pow_expr(&mut self, b: &Expr, e: &Expr) -> V {
        let k = self.try_const_index(e).unwrap_or_else(|| match self.eval(e).int {
            Some(n) => self.fail(format!("`**` exponent {n} does not fit in 32 bits")),
            None => self.fail(format!("`**` exponent must be a compile-time integer, got `{e:?}`")),
        });
        if let Some(bc) = self.try_field_const(b) {
            return self.const_cell(field_pow(bc, k));
        }
        if k == 0 {
            let o = self.fresh();
            self.set_const(o, F128::ONE);
            return o;
        }
        let base = self.expr(b);
        let hi = k.ilog2();
        let mut acc = base;
        for bit in (0..hi).rev() {
            acc = self.pure_mul(acc, acc);
            if (k >> bit) & 1 == 1 {
                acc = self.pure_mul(acc, base);
            }
        }
        acc
    }

    /// Evaluate `e` into `dst`.
    fn expr_into(&mut self, e: &Expr, dst: V) {
        if let Some(v) = self.try_field_const(e) {
            self.set_const(dst, v);
            return;
        }
        match e {
            Expr::Index(arr, idx) => match self.frame_cell(arr, idx) {
                Some(c) => self.copy(c, dst),
                None => {
                    let (ptr, o2) = self.heap_addr(arr, idx);
                    self.atom(Atom::Load(dst, ptr, o2));
                }
            },
            Expr::Pow(b, e) => {
                let v = self.pow_expr(b, e);
                self.copy(v, dst);
            }
            Expr::Add(a, b) => {
                if let Some(x) = self.add_identity(a, b) {
                    self.expr_into(x, dst);
                } else {
                    let (la, lb) = (self.expr(a), self.expr(b));
                    self.atom(Atom::Add(dst, la, lb));
                }
            }
            Expr::Mul(a, b) => {
                if let Some(x) = self.mul_identity(a, b) {
                    self.expr_into(x, dst);
                } else {
                    let (la, lb) = (self.expr(a), self.expr(b));
                    self.atom(Atom::Mul(dst, la, lb));
                }
            }
            Expr::Call(f, args) if self.defs.contains_key(f.as_str()) => {
                self.inline_stack_ret = None;
                self.call_into(f, args, &[dst]);
                let v = self.take_inline_ret_cell(dst);
                if v != dst {
                    self.copy(v, dst);
                }
            }
            _ => {
                let v = self.expr(e);
                self.copy(v, dst);
            }
        }
    }

    fn stmt(&mut self, s: &Stmt) {
        self.cur_line = s.line;
        match &s.kind {
            StmtKind::Let(name, e) => match e {
                Expr::StackBuf(n) => {
                    let base = self.alloc_stack(*n);
                    self.rebind(name, Binding::Stack(base, *n));
                }
                Expr::ListLit(es) => {
                    let base = self.alloc_stack(es.len() as u32);
                    for (k, el) in es.iter().enumerate() {
                        self.expr_into(el, base + k as u32);
                    }
                    self.rebind(name, Binding::Stack(base, es.len() as u32));
                }
                Expr::Call(f, cargs) if f == "addr" => {
                    let ga = self.stack_addr(cargs);
                    self.rebind(name, Binding::Gaddr(ga));
                }
                Expr::Var(v) if self.scope.stack(v).is_some() => {
                    let (base, size) = self.scope.stack(v).expect("guarded above");
                    self.rebind(name, Binding::Stack(base, size));
                }
                _ => {
                    let known = self.eval(e);
                    if let Some(ga) = known.addr {
                        self.rebind(name, Binding::Gaddr(ga));
                    } else if let Some(c) = known.field {
                        self.rebind(name, Binding::FConst(c));
                    } else if let Some(k) = known.int {
                        self.rebind(name, Binding::FConst(crate::field::word(k)));
                    } else if let Expr::Call(cf, cargs) = e
                        && self.defs.contains_key(cf.as_str())
                    {
                        let o = self.call(cf, cargs, 1)[0];
                        let b = ret_binding(self.inline_stack_ret.take().and_then(|b| b.into_iter().next()), o);
                        self.rebind(name, b);
                    } else {
                        let o = self.expr(e);
                        self.rebind(name, Binding::Scalar(o));
                    }
                    if let Some(k) = known.int {
                        self.scope.set_int(name, k);
                    }
                }
            },
            StmtKind::LetTuple(names, f, args) => {
                let dsts = self.call(f, args, names.len());
                let binds = self.inline_stack_ret.take();
                for (i, (n, d)) in names.iter().zip(&dsts).enumerate() {
                    let b = ret_binding(binds.as_ref().and_then(|b| b.get(i).copied()), *d);
                    self.rebind(n, b);
                }
            }
            StmtKind::AssertEq(a, b) => {
                let (la, lb) = (self.expr(a), self.expr(b));
                self.atom(Atom::AssertEq(la, lb));
            }
            StmtKind::AssertNe(a, b) => self.lower_assert_ne(a, b),
            StmtKind::AssertLt(e, bound) => self.lower_assert_lt(e, bound),
            StmtKind::HintWitness { dest, name } => self.lower_hint_witness(dest, name),
            StmtKind::LetHintWitness { name, stream } => {
                let dst = self.fresh();
                self.hint(Hint::Witness {
                    stream: stream.clone(),
                    dest: Dest::Stack(vec![dst]),
                });
                self.rebind(name, Binding::Scalar(dst));
            }
            // A debug print is the prover's alone: the value, and the anchor its hint fires on.
            StmtKind::Print { value, .. } => {
                self.expr(value);
                self.anchor();
            }
            StmtKind::If {
                eq,
                lhs,
                rhs,
                then,
                els,
                force_const,
            } => self.lower_if(*eq, lhs, rhs, then, els, *force_const),
            StmtKind::Match { targets, x, arms } => self.lower_match(targets, x, arms),
            StmtKind::Call(f, args) => {
                if !self.lower_builtin(f, args) {
                    let n_ret = self.defs.get(f.as_str()).map_or(0, |d| d.return_shapes.len());
                    self.call(f, args, n_ret);
                    self.inline_stack_ret = None;
                }
            }
            // The value first: the address may read a value it writes (`hb[sb[0]] = f(sb, …)`).
            StmtKind::Store(arr, idx, val) => {
                if let Some(c) = self.frame_cell(arr, idx) {
                    self.expr_into(val, c);
                } else {
                    let v = self.expr(val);
                    let (ptr, o2) = self.heap_addr(arr, idx);
                    self.atom(Atom::Load(v, ptr, o2));
                }
            }
            StmtKind::Return(es) => self.lower_return(es),
            StmtKind::CallIfNe(lhs, rhs, callee, args) => {
                let (la, lb) = (self.expr(lhs), self.expr(rhs));
                let x = self.pure_add(la, lb);
                self.lower_call(callee, args, Some(x), &[]);
            }
            StmtKind::For { var, lo, hi, body } => self.lower_for(var, *lo, hi, body),
            StmtKind::Unroll { var, lo, hi, body } => {
                let bound = |s: &Self, e: &Expr| {
                    s.try_const_index(e).unwrap_or_else(|| {
                        self.fail(format!("unroll bounds must be compile-time integers, got `{e:?}`"))
                    })
                };
                let (lo, hi) = (bound(self, lo), bound(self, hi));
                if lo > hi {
                    self.fail(format!("unroll(a, b) needs a <= b, got ({lo}, {hi})"))
                };
                let stmts: Vec<Stmt> = (lo..hi)
                    .flat_map(|j| subst_stmts(body, var, &Expr::Lit(j as u128)))
                    .collect();
                for (i, s) in stmts.iter().enumerate() {
                    // Back-to-back dispatches chain: each arm of one enters the next.
                    if let (StmtKind::Match { targets, arms, .. }, Some(next)) = (&s.kind, stmts.get(i + 1))
                        && let StmtKind::Match { x: nx, arms: narms, .. } = &next.kind
                        && self.all_inline(arms)
                        && self.all_inline(narms)
                        && let Some(xo) = self.free_cell(nx, targets)
                    {
                        self.chain_next = Some(xo);
                    }
                    self.stmt(s);
                }
            }
        }
    }

    /// `for i in mul_range(GEN**lo, hi)`: a tail-recursive helper `__loopN(i, [bound,] captures)` that runs the
    /// body, advances `i` by `g` and calls itself while `i` is not the stop, entered when the range is not empty.
    fn lower_for(&mut self, var: &str, lo: u64, hi: &ForBound, body: &[Stmt]) {
        let id = *self.loop_ctr;
        *self.loop_ctr += 1;
        let loop_name = format!("__loop{id}");
        let mut shadowed = HashSet::new();
        binds_anywhere(body, &mut shadowed);
        let bound_var = format!("__bound{id}");
        let (exit, entry_bound): (Expr, Expr) = match hi {
            ForBound::Const(hi) => (Expr::GPow(*hi as u128), Expr::GPow(*hi as u128)),
            ForBound::Runtime(e) => (Expr::Var(bound_var.clone()), e.clone()),
        };
        // Captures: referenced, not bound by the body, not the counter, bound here (in order).
        let mut referenced = Vec::new();
        let mut bound = HashSet::new();
        bound.insert(var);
        for s in body {
            free_vars_stmt(s, &mut referenced, &mut bound);
        }
        let mut captures = Vec::new();
        let mut seen = HashSet::new();
        for r in &referenced {
            if bound.contains(r) {
                continue;
            }
            if let Some((_, len)) = self.scope.stack(r)
                && !shadowed.contains(r)
            {
                if seen.insert(*r) {
                    captures.push(((*r).to_string(), Shape::StackBuf(len)));
                }
                continue;
            }
            if matches!(
                self.scope.bound(r).map(|b| b.val),
                Some(Binding::Scalar(_) | Binding::Gaddr(_) | Binding::FConst(_))
            ) && seen.insert(*r)
            {
                captures.push(((*r).to_string(), Shape::Scalar));
            }
        }
        let runtime = matches!(hi, ForBound::Runtime(_));
        let mut params = vec![(var.to_string(), Shape::Scalar)];
        if runtime {
            params.push((bound_var.clone(), Shape::Scalar));
        }
        params.extend(captures.iter().cloned());
        let cap_args = |first: Expr, bound: Expr| {
            let mut a = vec![first];
            if runtime {
                a.push(bound);
            }
            a.extend(captures.iter().map(|(c, _)| Expr::Var(c.clone())));
            a
        };
        let next_var = format!("__next{id}");
        let next = Expr::Mul(Arc::new(Expr::Var(var.to_string())), Arc::new(Expr::Gen));
        let mut loop_body: Vec<Stmt> = body.to_vec();
        let at = |kind| Stmt::new(self.cur_line, kind);
        loop_body.push(at(StmtKind::Let(next_var.clone(), next)));
        loop_body.push(at(StmtKind::CallIfNe(
            Expr::Var(next_var.clone()),
            exit,
            loop_name.clone(),
            cap_args(Expr::Var(next_var), Expr::Var(bound_var)),
        )));
        loop_body.push(at(StmtKind::Return(vec![])));
        self.queue.push(Func {
            name: loop_name.clone(),
            params: params
                .into_iter()
                .map(|(name, shape)| Param {
                    name,
                    kind: ParamKind::Runtime(shape),
                })
                .collect(),
            return_shapes: vec![],
            body: loop_body,
            inline: false,
        });
        match hi {
            ForBound::Const(hi) => {
                if lo != *hi {
                    self.call(
                        &loop_name,
                        &cap_args(Expr::GPow(lo as u128), Expr::GPow(*hi as u128)),
                        0,
                    );
                }
            }
            ForBound::Runtime(_) => {
                // The entry test and the first call's argument both read the bound, so one with a call or an
                // allocation in it is bound once first.
                let entry_bound = if calls_or_allocates(&entry_bound) {
                    let name = format!("__entry{id}");
                    self.stmt(&Stmt::new(self.cur_line, StmtKind::Let(name.clone(), entry_bound)));
                    Expr::Var(name)
                } else {
                    entry_bound
                };
                let stmt = Stmt::new(
                    self.cur_line,
                    StmtKind::CallIfNe(
                        Expr::GPow(lo as u128),
                        entry_bound.clone(),
                        loop_name,
                        cap_args(Expr::GPow(lo as u128), entry_bound),
                    ),
                );
                self.stmt(&stmt);
            }
        }
    }
}

/// Whether evaluating `e` calls a function or allocates.
fn calls_or_allocates(e: &Expr) -> bool {
    match e {
        Expr::Call(..)
        | Expr::HeapBuf(_)
        | Expr::HeapBufDyn(_)
        | Expr::StackBuf(_)
        | Expr::ListLit(_)
        | Expr::ListComp(..) => true,
        Expr::Add(a, b)
        | Expr::Mul(a, b)
        | Expr::Sub(a, b)
        | Expr::Div(a, b)
        | Expr::FieldDiv(a, b)
        | Expr::Mod(a, b)
        | Expr::Index(a, b)
        | Expr::Pow(a, b) => calls_or_allocates(a) || calls_or_allocates(b),
        Expr::Slice(a, lo, hi) => calls_or_allocates(a) || calls_or_allocates(lo) || calls_or_allocates(hi),
        Expr::GenPow(x) => calls_or_allocates(x),
        Expr::Lit(_) | Expr::Gen | Expr::GPow(_) | Expr::Var(_) => false,
    }
}

/// The literal `k` when `hi` is syntactically `lo + k` (either operand order).
fn plus_k(lo: &Expr, hi: &Expr) -> Option<u128> {
    match hi {
        Expr::Add(a, b) => match (a.as_ref(), b.as_ref()) {
            (Expr::Lit(k), other) | (other, Expr::Lit(k)) if other == lo => Some(*k),
            _ => None,
        },
        _ => None,
    }
}

/// Whether a `return` of this function occurs in `stmts`: nested `if` and `unroll` bodies included, a `mul_range`
/// body not.
fn has_return(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|s| match &s.kind {
        StmtKind::Return(_) => true,
        StmtKind::If { then, els, .. } => has_return(then) || has_return(els),
        StmtKind::Unroll { body, .. } => has_return(body),
        _ => false,
    })
}

/// The core function of `f`.
fn expand_func(
    f: &Func,
    queue: &mut Vec<Func>,
    loop_ctr: &mut usize,
    defs: &HashMap<&str, &Func>,
    const_arrays: &HashMap<&str, &[F128]>,
) -> crate::core_ir::Fn {
    let mut names: HashMap<String, Bound> = HashMap::new();
    let mut pos = 0;
    for p in &f.params {
        assert!(
            !const_arrays.contains_key(p.name.as_str()),
            "`{}`: parameter `{}` collides with a top-level constant array, whose name is \
             reserved (zkDSL.md §Global constants)",
            f.name,
            p.name
        );
        let val = match p.shape() {
            Shape::StackBuf(n) => Binding::Stack(pos, n),
            Shape::Scalar => Binding::Scalar(pos),
        };
        names.insert(p.name.clone(), Bound { val, int: None });
        pos += p.shape().cells();
    }
    let mut ex = FnExpand {
        scope: Scope {
            names,
            ..Default::default()
        },
        next: 0,
        group: Vec::new(),
        return_shapes: &f.return_shapes,
        is_main: f.name == "main",
        out: Vec::new(),
        pending: false,
        heap_sizes: HashMap::new(),
        addr_runs: HashMap::new(),
        inline_ret: None,
        inline_stack_ret: None,
        cur_line: 0,
        chain_next: None,
        chain_in: None,
        inline_calls: Vec::new(),
        queue,
        loop_ctr,
        fn_name: &f.name,
        defs,
        const_arrays,
    };
    // The parameters are one run.
    let params = ex.alloc_stack(pos);
    if ex.is_main {
        for (i, s) in f.body.iter().enumerate() {
            let trailing = i + 1 == f.body.len() && matches!(s.kind, StmtKind::Return(_));
            assert!(
                trailing || !has_return(std::slice::from_ref(s)),
                "line {}: `return` in `main` is allowed only as its last statement",
                s.line
            );
        }
    }
    for s in &f.body {
        ex.stmt(s);
    }
    if ex.is_main {
        ex.emit(CStmt::Ret(Vec::new()));
    } else if !matches!(f.body.last().map(|s| &s.kind), Some(StmtKind::Return(_))) {
        let last = f.body.last().map_or(0, |s| s.line);
        ex.stmt(&Stmt::new(last, StmtKind::Return(vec![])));
    }
    crate::core_ir::Fn {
        name: f.name.clone(),
        params: FnExpand::run(params, pos),
        body: ex.out,
    }
}

/// Every function the program runs, in the compiler's order: `main`, the other functions in source order, then
/// each `Const` specialization and `mul_range` helper in the order expansion asks for it. Panics on a malformed
/// program, as compiling it does.
pub fn expand(ast: &Ast) -> Vec<crate::core_ir::Fn> {
    let main = ast
        .funcs
        .iter()
        .find(|f| f.name == "main")
        .expect("program needs a `main`");
    assert!(!main.has_const_params(), "main cannot take Const parameters");
    assert!(!main.inline, "main cannot be `@inline`");
    let mut queue: Vec<Func> = vec![main.clone()];
    queue.extend(ast.funcs.iter().filter(|f| f.name != "main").cloned());
    let defs: HashMap<&str, &Func> = ast.funcs.iter().map(|f| (f.name.as_str(), f)).collect();
    let const_arrays: HashMap<&str, &[F128]> = ast
        .const_arrays
        .iter()
        .map(|(name, values)| (name.as_str(), values.as_slice()))
        .collect();
    let mut loop_ctr = 0usize;
    let mut out = Vec::new();
    let mut i = 0;
    while i < queue.len() {
        let f = queue[i].clone();
        i += 1;
        if f.has_const_params() || f.inline {
            continue;
        }
        out.push(expand_func(&f, &mut queue, &mut loop_ctr, &defs, &const_arrays));
    }
    out
}
