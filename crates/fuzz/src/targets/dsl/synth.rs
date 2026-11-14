//! A generator of well-formed, self-checking zkDSL programs, Csmith style.
//!
//! It builds a [`Prog`] while evaluating it with the real field arithmetic, so every value is known when it is
//! emitted: the program asserts intermediate values against literals and publishes a fold of them. A construct runs
//! as many times as its context does (once in `main`, once per iteration in a loop body, once per caller lane in a
//! function), so a value is a vector with one entry per *lane*, a dynamic instance of the code being generated; a
//! branch narrows the active lanes. Memory is one write-once map, as the machine's is, and a cell is only read where
//! the write that gives it its value has certainly run first.

use super::ast::*;
use crate::Source;
use primitives::field::F128;
use primitives::hash::hash;
use std::collections::{BTreeSet, HashMap};

pub struct Generated {
    pub prog: Prog,
    pub witness: Vec<(String, Vec<Vec<F128>>)>,
    pub public_input: [F128; 2],
    pub features: BTreeSet<&'static str>,
}

#[derive(Clone, Copy)]
pub struct Limits {
    /// Statements, roughly.
    pub budget: usize,
    pub max_lanes: usize,
    pub max_nest: usize,
}

impl Limits {
    pub fn for_depth(src: &mut Source, depth: u8) -> Self {
        let budget = match depth {
            0 => src.range(8, 30),
            1 => src.range(15, 90),
            _ => src.range(20, 160),
        };
        Self {
            budget,
            max_lanes: 40,
            max_nest: 3,
        }
    }
}

#[derive(Clone)]
enum VK {
    Scalar,
    Counter,
    /// A `Const` parameter: its integer per lane, and the range every specialization of the body spans.
    Const {
        ks: Vec<u32>,
        kmax: u32,
    },
    Stack {
        n: u32,
        inst: Vec<usize>,
    },
    Heap {
        n: u32,
        inst: Vec<usize>,
    },
}

#[derive(Clone)]
struct Var {
    depth: usize,
    kind: VK,
    vals: Vec<F128>,
    /// Derived from a hint, so never a compile-time constant however the program is spelled.
    rt: bool,
    /// Bound to an expression the compiler folds, so the name is a literal to it (`x = 3 * 5`).
    folded: bool,
}

/// Who wrote a cell: a lane of a context still on the stack.
#[derive(Clone, Copy)]
struct Tag {
    depth: usize,
    uid: usize,
    inst: usize,
}

struct Cx {
    uid: usize,
    n: usize,
    parent_of: Vec<usize>,
    written: Vec<(usize, u32)>,
    loop_id: Option<usize>,
    /// For a loop body: the outer `StackBuf`s wholly written on every lane that reaches the loop, which the body
    /// may read. A `mul_range` copies every cell of one it names when its frame is set up, even for no iteration.
    capturable: std::collections::HashSet<V>,
}

/// The `match` arm being generated: each lane's arm index, and the indices every specialization spans.
#[derive(Clone)]
struct JCtx {
    js: Vec<u32>,
    hi: u32,
}

/// The function being generated: its return arity, the lanes that returned early and their values.
struct FnState {
    fun: FnId,
    nret: usize,
    rets: Vec<Vec<F128>>,
    early: bool,
    allow_early: bool,
    has_mul: bool,
    konst_ct: bool,
}

type Tv = (Ex, Vec<F128>);

struct Gen<'a> {
    src: &'a mut Source,
    lim: Limits,
    vars: Vec<Var>,
    scopes: Vec<Vec<V>>,
    barrier: usize,
    cxs: Vec<Cx>,
    active: Vec<usize>,
    mem: HashMap<(usize, u32), (F128, Tag)>,
    nbuf: usize,
    uid: usize,
    prog: Prog,
    streams: Vec<(String, Vec<Vec<F128>>)>,
    budget: usize,
    nest: usize,
    jctx: Option<JCtx>,
    fns: Vec<FnState>,
    features: BTreeSet<&'static str>,
    public_input: [F128; 2],
    /// Buffers a construct being generated will write itself: hidden from its body.
    reserved: std::collections::HashSet<V>,
}

pub fn generate(src: &mut Source, lim: Limits) -> Generated {
    let mut g = Gen {
        src,
        lim,
        vars: Vec::new(),
        scopes: vec![Vec::new()],
        barrier: 0,
        cxs: vec![Cx {
            uid: 0,
            n: 1,
            parent_of: vec![0],
            written: Vec::new(),
            loop_id: None,
            capturable: Default::default(),
        }],
        active: vec![0],
        mem: HashMap::new(),
        nbuf: 0,
        uid: 1,
        prog: Prog::default(),
        streams: Vec::new(),
        budget: lim.budget,
        nest: 0,
        jctx: None,
        fns: Vec::new(),
        features: BTreeSet::new(),
        public_input: [F128::ZERO; 2],
        reserved: Default::default(),
    };
    g.prog.funs.push(Fun {
        params: Vec::new(),
        body: Vec::new(),
        inline: Mode::Never,
        konst: Mode::Never,
    });
    g.fns.push(FnState {
        fun: 0,
        nret: 0,
        rets: Vec::new(),
        early: false,
        allow_early: false,
        has_mul: false,
        konst_ct: false,
    });
    for _ in 0..g.src.range(0, 2) {
        let len = g.src.range(1, 8);
        let arr = (0..len).map(|_| g.small_or_wide()).collect();
        g.prog.arrays.push(arr);
    }
    let mut body = Vec::new();
    for _ in 0..g.src.range(1, 3) {
        body.extend(g.g_hint());
    }
    let budget = g.budget;
    body.extend(g.block(budget));
    body.extend(g.publish());
    g.prog.funs[0].body = body;
    g.prog.nvars = g.vars.len();
    let public_input = g.public_input;
    Generated {
        prog: g.prog,
        witness: g.streams,
        public_input,
        features: g.features,
    }
}

impl Gen<'_> {
    // ----- lanes, scopes and memory -----

    fn depth(&self) -> usize {
        self.cxs.len() - 1
    }

    fn cx(&self) -> &Cx {
        self.cxs.last().unwrap()
    }

    fn n(&self) -> usize {
        self.cx().n
    }

    /// The lane of context `to` that lane `t` of the current context runs inside.
    fn lift(&self, mut t: usize, to: usize) -> usize {
        let mut d = self.depth();
        while d > to {
            t = self.cxs[d].parent_of[t];
            d -= 1;
        }
        t
    }

    fn val(&self, v: V, t: usize) -> F128 {
        let x = &self.vars[v];
        x.vals[self.lift(t, x.depth)]
    }

    fn inst(&self, v: V, t: usize) -> usize {
        let x = &self.vars[v];
        match &x.kind {
            VK::Stack { inst, .. } | VK::Heap { inst, .. } => inst[self.lift(t, x.depth)],
            _ => unreachable!("not a buffer"),
        }
    }

    fn size(&self, v: V) -> u32 {
        match &self.vars[v].kind {
            VK::Stack { n, .. } | VK::Heap { n, .. } => *n,
            _ => unreachable!("not a buffer"),
        }
    }

    fn visible(&self) -> Vec<V> {
        self.scopes[self.barrier..].iter().flatten().copied().collect()
    }

    fn new_var(&mut self, kind: VK, vals: Vec<F128>, rt: bool) -> V {
        let v = self.vars.len();
        self.vars.push(Var {
            depth: self.depth(),
            kind,
            vals,
            rt,
            folded: false,
        });
        self.scopes.last_mut().unwrap().push(v);
        v
    }

    fn fresh_insts(&mut self) -> Vec<usize> {
        let n = self.n();
        let mut inst = vec![usize::MAX; n];
        for &t in &self.active {
            inst[t] = self.nbuf;
            self.nbuf += 1;
        }
        inst
    }

    fn new_stack(&mut self, n: u32) -> V {
        let inst = self.fresh_insts();
        let vals = vec![F128::ZERO; self.n()];
        let v = self.new_var(VK::Stack { n, inst }, vals, false);
        self.prog.stack_sizes.insert(v, n);
        v
    }

    fn new_heap(&mut self, n: u32) -> V {
        let inst = self.fresh_insts();
        let vals = vec![F128::ZERO; self.n()];
        self.new_var(VK::Heap { n, inst }, vals, false)
    }

    fn readable(&self, tag: Tag, t: usize) -> bool {
        tag.depth <= self.depth() && self.cxs[tag.depth].uid == tag.uid && self.lift(t, tag.depth) == tag.inst
    }

    /// The value of cell `c` of buffer `v` in lane `t`, if it has certainly been written by then.
    fn cell(&self, v: V, c: u32, t: usize) -> Option<F128> {
        let (val, tag) = *self.mem.get(&(self.inst(v, t), c))?;
        self.readable(tag, t).then_some(val)
    }

    fn written_anywhere(&self, v: V, c: u32, t: usize) -> bool {
        self.mem.contains_key(&(self.inst(v, t), c))
    }

    /// Cell `c` of `v` on every active lane.
    fn cells_all(&self, v: V, c: u32) -> Option<Vec<F128>> {
        let mut out = vec![F128::ZERO; self.n()];
        for &t in &self.active {
            out[t] = self.cell(v, c, t)?;
        }
        Some(out)
    }

    /// Write `(lane, buffer, cell, value)` if no cell would take two values; a cell that already holds the value is
    /// the write-once equality.
    fn try_write(&mut self, writes: &[(usize, V, u32, F128)]) -> bool {
        let mut batch: HashMap<(usize, u32), F128> = HashMap::new();
        for &(t, v, c, x) in writes {
            let key = (self.inst(v, t), c);
            if let Some((old, _)) = self.mem.get(&key)
                && *old != x
            {
                return false;
            }
            if let Some(old) = batch.insert(key, x)
                && old != x
            {
                return false;
            }
        }
        let depth = self.depth();
        let uid = self.cx().uid;
        for &(t, v, c, x) in writes {
            let key = (self.inst(v, t), c);
            if let std::collections::hash_map::Entry::Vacant(e) = self.mem.entry(key) {
                e.insert((x, Tag { depth, uid, inst: t }));
                self.cxs.last_mut().unwrap().written.push(key);
            }
        }
        true
    }

    fn push_cx(&mut self, parent_of: Vec<usize>, loop_id: Option<usize>) {
        let n = parent_of.len();
        let capturable = if loop_id.is_some() {
            self.stacks()
                .into_iter()
                .filter(|&v| {
                    self.stack_readable(v)
                        && (0..self.size(v)).all(|c| self.active.iter().all(|&t| self.cell(v, c, t).is_some()))
                })
                .collect()
        } else {
            Default::default()
        };
        self.cxs.push(Cx {
            capturable,
            uid: self.uid,
            n,
            parent_of,
            written: Vec::new(),
            loop_id,
        });
        self.uid += 1;
    }

    /// Leave a context: what its lanes wrote now belongs to the lanes that entered it.
    fn pop_cx(&mut self) {
        let cx = self.cxs.pop().unwrap();
        let depth = self.depth();
        let uid = self.cx().uid;
        for key in cx.written {
            if let Some((_, tag)) = self.mem.get_mut(&key)
                && tag.uid == cx.uid
            {
                *tag = Tag {
                    depth,
                    uid,
                    inst: cx.parent_of[tag.inst],
                };
                self.cxs.last_mut().unwrap().written.push(key);
            }
        }
    }

    /// A stack buffer whose cells may be read here: one from outside an enclosing loop only when every loop between
    /// found it wholly written ([`Cx::capturable`]).
    fn stack_readable(&self, v: V) -> bool {
        (self.vars[v].depth + 1..self.cxs.len()).all(|d| self.cxs[d].capturable.contains(&v))
    }

    fn fun(&self) -> &FnState {
        self.fns.last().unwrap()
    }

    fn note(&mut self, f: &'static str) {
        self.features.insert(f);
    }

    // ----- values -----

    fn lanes(&self, f: impl Fn(usize) -> F128) -> Vec<F128> {
        let mut out = vec![F128::ZERO; self.n()];
        for &t in &self.active {
            out[t] = f(t);
        }
        out
    }

    fn all(&self, vals: &[F128], f: impl Fn(F128) -> bool) -> bool {
        self.active.iter().all(|&t| f(vals[t]))
    }

    fn uniform(&self, vals: &[F128]) -> Option<F128> {
        let first = vals[*self.active.first()?];
        self.all(vals, |x| x == first).then_some(first)
    }

    fn logs(&self, vals: &[F128]) -> Option<Vec<u32>> {
        let mut out = vec![0; self.n()];
        for &t in &self.active {
            out[t] = log_of(vals[t])?;
        }
        Some(out)
    }

    fn max_log(&self, logs: &[u32]) -> u32 {
        self.active.iter().map(|&t| logs[t]).max().unwrap_or(0)
    }

    fn small_or_wide(&mut self) -> u128 {
        match self.src.below(8) {
            0..=3 => self.src.below(64) as u128,
            4 => 1u128 << self.src.below(128),
            5 => self.src.u64() as u128,
            _ => self.lit128(),
        }
    }

    fn lit128(&mut self) -> u128 {
        match self.src.below(10) {
            0 => self.src.below(17) as u128,
            1 => 1u128 << self.src.below(128),
            2 => (1u128 << self.src.below(128)).wrapping_sub(1),
            3 => u128::MAX - self.src.below(3) as u128,
            4 => self.src.u64() as u128,
            5 => (1u128 << 64) + self.src.below(5) as u128,
            6 => self.src.u32() as u128,
            7 => (self.src.u64() as u128) << 64,
            _ => (self.src.u64() as u128) << 64 | self.src.u64() as u128,
        }
    }

    fn rt(&self, e: &Ex) -> bool {
        match e {
            Ex::Var(v) => self.vars[*v].rt,
            Ex::Add(a, b) | Ex::Mul(a, b) | Ex::Div(a, b) => self.rt(a) || self.rt(b),
            Ex::Pow(a, _) => self.rt(a),
            _ => false,
        }
    }

    fn add(&self, a: Tv, b: Tv) -> Tv {
        let v = self.lanes(|t| a.1[t] + b.1[t]);
        (Ex::Add(Box::new(a.0), Box::new(b.0)), v)
    }

    fn mul(&self, a: Tv, b: Tv) -> Tv {
        let v = self.lanes(|t| a.1[t] * b.1[t]);
        (Ex::Mul(Box::new(a.0), Box::new(b.0)), v)
    }

    fn div(&self, a: Tv, b: Tv) -> Tv {
        let v = self.lanes(|t| a.1[t] * b.1[t].inv());
        (Ex::Div(Box::new(a.0), Box::new(b.0)), v)
    }

    fn pow(&self, a: Tv, k: u32) -> Tv {
        let v = self.lanes(|t| {
            let mut acc = F128::ONE;
            for _ in 0..k {
                acc *= a.1[t];
            }
            acc
        });
        (Ex::Pow(Box::new(a.0), k), v)
    }

    fn konst(&self, x: F128) -> Tv {
        (lit_of(x), self.lanes(|_| x))
    }

    fn var_tv(&self, v: V) -> Tv {
        (Ex::Var(v), self.lanes(|t| self.val(v, t)))
    }

    fn scalars(&self) -> Vec<V> {
        self.visible()
            .into_iter()
            .filter(|&v| matches!(self.vars[v].kind, VK::Scalar | VK::Counter | VK::Const { .. }))
            .collect()
    }

    fn gpow_candidates(&self) -> Vec<V> {
        self.scalars()
            .into_iter()
            .filter(|&v| matches!(self.vars[v].kind, VK::Scalar | VK::Counter))
            .collect()
    }

    fn stacks(&self) -> Vec<V> {
        self.visible()
            .into_iter()
            .filter(|&v| matches!(self.vars[v].kind, VK::Stack { .. }) && !self.reserved.contains(&v))
            .collect()
    }

    fn heaps(&self) -> Vec<V> {
        self.visible()
            .into_iter()
            .filter(|&v| matches!(self.vars[v].kind, VK::Heap { .. }) && !self.reserved.contains(&v))
            .collect()
    }

    /// Scalars holding a g-power on every active lane, with their exponents.
    fn gpow_scalars(&self, max: u32) -> Vec<(V, Vec<u32>)> {
        self.gpow_candidates()
            .into_iter()
            .filter_map(|v| {
                let vals = self.lanes(|t| self.val(v, t));
                let logs = self.logs(&vals)?;
                (self.max_log(&logs) < max).then_some((v, logs))
            })
            .collect()
    }

    /// Scalars a heap index, a runtime slice start or a scrutinee may name: a hinted g-power or a loop counter. A
    /// name bound to a compile-time constant is not one: the compiler reads it as an integer or a field constant.
    fn index_vars(&self, max: u32) -> Vec<(V, Vec<u32>)> {
        self.gpow_scalars(max)
            .into_iter()
            .filter(|(v, l)| (self.vars[*v].rt || matches!(self.vars[*v].kind, VK::Counter)) && self.smax(*v, l) < max)
            .collect()
    }

    /// The largest exponent `v` takes on an active lane, or in any copy of an unrolled body: the compiler checks
    /// every copy, including those of an arm no lane takes.
    fn smax(&self, v: V, logs: &[u32]) -> u32 {
        let lanes = self.max_log(logs);
        match self.prog.counter_of.get(&v).map(|&l| &self.prog.loops[l].hi) {
            Some(Hi::Const(hi)) => lanes.max(hi.saturating_sub(1)),
            _ => lanes,
        }
    }

    /// A counter usable as a compile-time integer: one of a loop that may be unrolled, in the function it sits in.
    fn int_counters(&self) -> Vec<(V, usize)> {
        self.scalars()
            .into_iter()
            .filter(|&v| matches!(self.vars[v].kind, VK::Counter))
            .filter_map(|v| {
                let l = self.prog.counter_of[&v];
                (self.prog.loops[l].form != Form::MulRange).then_some((v, l))
            })
            .collect()
    }

    /// Every (integer index, per-lane integer, largest index any copy of the code uses) the context offers.
    fn int_indices(&self) -> Vec<(Ix, Vec<u32>, u32)> {
        let n = self.n();
        let mut out = vec![];
        for (v, l) in self.int_counters() {
            let lo = self.prog.loops[l].lo;
            let Hi::Const(hi) = self.prog.loops[l].hi else { continue };
            if hi == lo {
                continue;
            }
            let ks = self.lanes(|t| self.val(v, t));
            let ks: Vec<u32> = (0..n).map(|t| log_of(ks[t]).unwrap_or(0)).collect();
            out.push((Ix::Counter(v, 0), ks, hi - 1));
        }
        for v in self.scalars() {
            if let VK::Const { kmax, .. } = &self.vars[v].kind {
                let kmax = *kmax;
                let ks = (0..n)
                    .map(|t| match &self.vars[v].kind {
                        VK::Const { ks, .. } => ks[self.lift(t, self.vars[v].depth)],
                        _ => 0,
                    })
                    .collect();
                out.push((Ix::Param(v, 0), ks, kmax));
            }
        }
        if let Some(j) = &self.jctx {
            out.push((Ix::J(0), j.js.clone(), j.hi - 1));
        }
        out
    }

    fn use_ix(&mut self, ix: Ix) {
        match ix {
            Ix::Counter(v, _) => {
                let l = self.prog.counter_of[&v];
                self.prog.loops[l].form = Form::Unroll;
                self.note("counter as index");
            }
            Ix::Param(..) => {
                self.fns.last_mut().unwrap().konst_ct = true;
                self.note("Const as index");
            }
            Ix::J(_) => self.note("arm index"),
            Ix::Lit(_) => {}
        }
    }

    fn leaf(&mut self) -> Tv {
        for _ in 0..4 {
            match self.src.below(14) {
                0 => {
                    let n = self.lit128();
                    return (Ex::Lit(n), self.lanes(|_| lit(n)));
                }
                1 => {
                    let n = self.src.below(32) as u128;
                    return (Ex::Lit(n), self.lanes(|_| lit(n)));
                }
                2 => {
                    // Every word's bits spell an integer literal below 2^128, so the
                    // generated spelling is that integer (the parser folds it back).
                    let x = self.src.f128();
                    let n = x.c0 as u128 | (x.c1 as u128) << 64;
                    return (Ex::Lit(n), self.lanes(|_| x));
                }
                3 => {
                    let k = match self.src.below(4) {
                        0 => self.src.below(1 << 20) as u64,
                        1 => 60 + self.src.below(10) as u64,
                        _ => self.src.below(16) as u64,
                    };
                    return (Ex::GPow(k), self.lanes(|_| gpow(k)));
                }
                4..=7 => {
                    let s = self.scalars();
                    if !s.is_empty() {
                        let v = s[self.src.below(s.len())];
                        return self.var_tv(v);
                    }
                }
                8 => {
                    let st = self.stacks();
                    if !st.is_empty() {
                        let v = st[self.src.below(st.len())];
                        if self.stack_readable(v) {
                            let n = self.size(v);
                            if self.src.chance(1, 3) {
                                // A compile-time integer index from the context.
                                let ixs = self.int_indices();
                                if !ixs.is_empty() {
                                    let (ix, ks, kmax) = ixs[self.src.below(ixs.len())].clone();
                                    if kmax < n {
                                        let off = self.src.below((n - kmax) as usize) as u32;
                                        let ok = self.active.iter().all(|&t| self.cell(v, ks[t] + off, t).is_some());
                                        if ok {
                                            let vals = self.lanes(|t| self.cell(v, ks[t] + off, t).unwrap());
                                            let ix = match ix {
                                                Ix::Counter(c, _) => Ix::Counter(c, off),
                                                Ix::Param(c, _) => Ix::Param(c, off),
                                                Ix::J(_) => Ix::J(off),
                                                Ix::Lit(_) => unreachable!(),
                                            };
                                            self.use_ix(ix);
                                            return (Ex::SRead(v, ix), vals);
                                        }
                                    }
                                }
                            }
                            let c = self.src.below(n as usize) as u32;
                            if let Some(vals) = self.cells_all(v, c) {
                                return (Ex::SRead(v, Ix::Lit(c)), vals);
                            }
                        }
                    }
                }
                9 | 10 => {
                    let hs = self.heaps();
                    if !hs.is_empty() {
                        let v = hs[self.src.below(hs.len())];
                        let n = self.size(v);
                        if self.src.bool() {
                            let c = self.src.below(n as usize) as u32;
                            if let Some(vals) = self.cells_all(v, c) {
                                return (Ex::HRead(v, HIx::Const(c)), vals);
                            }
                        } else {
                            let gs = self.index_vars(n);
                            if !gs.is_empty() {
                                let (x, logs) = gs[self.src.below(gs.len())].clone();
                                let room = n - self.smax(x, &logs);
                                let off = self.src.below(room as usize) as u32;
                                if self.active.iter().all(|&t| self.cell(v, logs[t] + off, t).is_some()) {
                                    let vals = self.lanes(|t| self.cell(v, logs[t] + off, t).unwrap());
                                    self.note("runtime heap index");
                                    return (Ex::HRead(v, HIx::Rt(x, off)), vals);
                                }
                            }
                        }
                    }
                }
                11 => {
                    if !self.prog.arrays.is_empty() {
                        let a = self.src.below(self.prog.arrays.len());
                        let len = self.prog.arrays[a].len() as u32;
                        if self.src.bool() {
                            let ixs = self.int_indices();
                            if !ixs.is_empty() {
                                let (ix, ks, kmax) = ixs[self.src.below(ixs.len())].clone();
                                if kmax < len {
                                    let off = self.src.below((len - kmax) as usize) as u32;
                                    let ix = match ix {
                                        Ix::Counter(c, _) => Ix::Counter(c, off),
                                        Ix::Param(c, _) => Ix::Param(c, off),
                                        Ix::J(_) => Ix::J(off),
                                        Ix::Lit(_) => unreachable!(),
                                    };
                                    self.use_ix(ix);
                                    let arr = &self.prog.arrays[a];
                                    let vals = self.lanes(|t| lit(arr[(ks[t] + off) as usize]));
                                    return (Ex::Arr(a, ix), vals);
                                }
                            }
                        }
                        let i = self.src.below(len as usize);
                        let x = lit(self.prog.arrays[a][i]);
                        self.note("const array");
                        return (Ex::Arr(a, Ix::Lit(i as u32)), self.lanes(|_| x));
                    }
                }
                12 => {
                    let (text, n) = self.int_expr(3);
                    self.note("const()");
                    return (Ex::ConstInt(text), self.lanes(|_| lit(n)));
                }
                _ => {
                    if let Some(j) = self.jctx.clone() {
                        if self.src.bool() {
                            return (Ex::J, self.lanes(|t| lit(j.js[t] as u128)));
                        }
                        let off = self.src.below(4) as u32;
                        return (Ex::JPow(off), self.lanes(|t| gpow((j.js[t] + off) as u64)));
                    }
                    // `GEN ** (k + off)` for a Const parameter.
                    let ks: Vec<V> = self
                        .scalars()
                        .into_iter()
                        .filter(|&v| matches!(self.vars[v].kind, VK::Const { .. }))
                        .collect();
                    if !ks.is_empty() {
                        let k = ks[self.src.below(ks.len())];
                        let off = self.src.below(4) as u32;
                        self.fns.last_mut().unwrap().konst_ct = true;
                        let d = self.vars[k].depth;
                        let vals = self.lanes(|t| match &self.vars[k].kind {
                            VK::Const { ks, .. } => gpow((ks[self.lift(t, d)] + off) as u64),
                            _ => unreachable!(),
                        });
                        return (Ex::KPow(k, off), vals);
                    }
                }
            }
        }
        let n = self.src.below(1000) as u128;
        (Ex::Lit(n), self.lanes(|_| lit(n)))
    }

    /// A compile-time integer expression and its value, for `const(...)`.
    fn int_expr(&mut self, depth: u32) -> (String, u128) {
        if depth == 0 || self.src.chance(1, 3) {
            let bits = self.src.range(1, 20);
            let n = self.src.below(1 << bits) as u128;
            return (n.to_string(), n);
        }
        let (a, x) = self.int_expr(depth - 1);
        let (b, y) = self.int_expr(depth - 1);
        match self.src.below(5) {
            0 => (format!("({a} + {b})"), x + y),
            1 if x >= y => (format!("({a} - {b})"), x - y),
            2 if x.checked_mul(y).is_some_and(|p| p < 1 << 100) => (format!("({a} * {b})"), x * y),
            3 if y > 0 => (format!("({a} // {b})"), x / y),
            4 if y > 0 => (format!("({a} % {b})"), x % y),
            _ => (format!("({a} + {b})"), x + y),
        }
    }

    fn ex(&mut self, depth: u32) -> Tv {
        if depth == 0 || self.src.chance(2, 5) {
            return self.leaf();
        }
        match self.src.below(9) {
            0..=2 => {
                let a = self.ex(depth - 1);
                let b = self.ex(depth - 1);
                self.add(a, b)
            }
            3..=5 => {
                let a = self.ex(depth - 1);
                let b = self.ex(depth - 1);
                self.mul(a, b)
            }
            6 | 7 => {
                let a = self.ex(depth - 1);
                let b = self.nonzero(depth - 1);
                self.note("field division");
                self.div(a, b)
            }
            _ => {
                let a = self.ex(depth - 1);
                let k = match self.src.below(6) {
                    0 => 0,
                    1 => 1,
                    2 => self.src.range(5, 70) as u32,
                    _ => self.src.range(2, 4) as u32,
                };
                self.note("power");
                self.pow(a, k)
            }
        }
    }

    fn nonzero(&mut self, depth: u32) -> Tv {
        for _ in 0..3 {
            let b = self.ex(depth);
            if self.all(&b.1, |x| !x.is_zero()) {
                return b;
            }
        }
        let n = self.lit128().max(1);
        (Ex::Lit(n), self.lanes(|_| lit(n)))
    }

    /// An expression whose value is canonical on every active lane: a `keccak` input.
    fn canonical(&mut self) -> Tv {
        for _ in 0..4 {
            let e = self.ex(2);
            if self.all(&e.1, |x| x.c1 == 0) {
                return e;
            }
        }
        let n = self.lit128();
        (Ex::Lit(n), self.lanes(|_| lit(n)))
    }

    /// An expression in `K` on every active lane.
    fn in_k(&mut self) -> Tv {
        self.canonical()
    }

    // ----- statements -----

    fn block(&mut self, budget: usize) -> Vec<St> {
        let mut out = Vec::new();
        let mut left = budget;
        while left > 0 && self.budget > 0 {
            let before = self.budget;
            out.extend(self.statement());
            let spent = (before - self.budget).max(1);
            left = left.saturating_sub(spent);
        }
        out
    }

    fn spend(&mut self, n: usize) {
        self.budget = self.budget.saturating_sub(n);
    }

    fn statement(&mut self) -> Vec<St> {
        self.spend(1);
        let nested = self.nest < self.lim.max_nest && !self.active.is_empty();
        let w = [
            20,                         // let
            8,                          // assert ==
            5,                          // identity
            4,                          // assert !=
            4,                          // range check
            2,                          // assert_in_k
            5,                          // hint
            3,                          // hint a run
            8,                          // store
            3,                          // list
            4,                          // alloc
            if nested { 6 } else { 0 }, // if
            if nested { 5 } else { 0 }, // match
            if nested { 7 } else { 0 }, // call
            if nested { 6 } else { 0 }, // loop
            4,                          // keccak
            3,                          // keccak_cells
            1,                          // dynamic heap
            if nested { 4 } else { 0 }, // if const(...) on a Const parameter
        ];
        match self.src.weighted(&w) {
            0 => self.g_let(),
            1 => self.g_assert_eq(),
            2 => self.g_identity(),
            3 => self.g_assert_ne(),
            4 => self.g_range(),
            5 => self.g_in_k(),
            6 => self.g_hint(),
            7 => self.g_hint_run(),
            8 => self.g_store(),
            9 => self.g_list(),
            10 => self.g_alloc(),
            11 => self.g_if(),
            12 => self.g_match(),
            13 => self.g_call(),
            14 => self.g_loop(),
            15 => self.g_keccak(),
            16 => self.g_keccak_cells(),
            17 => self.g_heap_dyn(),
            _ => self.g_if_const(),
        }
    }

    fn g_let(&mut self) -> Vec<St> {
        let (e, vals) = self.ex(3);
        let rt = self.rt(&e);
        let v = self.new_var(VK::Scalar, vals, rt);
        self.vars[v].folded = self.compile_time(&e);
        vec![St::Let(v, e, Route::Any)]
    }

    fn g_assert_eq(&mut self) -> Vec<St> {
        let (e, vals) = if self.src.bool() {
            let s = self.scalars();
            if s.is_empty() {
                self.ex(2)
            } else {
                let v = s[self.src.below(s.len())];
                self.var_tv(v)
            }
        } else {
            self.ex(3)
        };
        let Some(x) = self.uniform(&vals) else {
            return self.g_identity();
        };
        self.note("assert ==");
        if self.src.bool() {
            vec![St::AssertEq(e, lit_of(x))]
        } else {
            vec![St::AssertEq(lit_of(x), e)]
        }
    }

    fn g_identity(&mut self) -> Vec<St> {
        let a = self.ex(2);
        let b = self.ex(2);
        let c = self.ex(1);
        let (l, r) = match self.src.below(7) {
            0 => {
                let s = self.add(a.clone(), b.clone());
                let l = self.mul(s, c.clone());
                let ac = self.mul(a, c.clone());
                let bc = self.mul(b, c);
                (l, self.add(ac, bc))
            }
            1 => {
                let ab = self.mul(a.clone(), b.clone());
                let l = self.mul(ab, c.clone());
                let bc = self.mul(b, c);
                (l, self.mul(a, bc))
            }
            2 => {
                let s = self.add(a.clone(), b.clone());
                let l = self.pow(s, 2);
                let a2 = self.pow(a, 2);
                let b2 = self.pow(b, 2);
                (l, self.add(a2, b2))
            }
            3 => {
                let d = self.nonzero(1);
                let q = self.div(a.clone(), d.clone());
                (self.mul(q, d), a)
            }
            4 => (self.mul(a.clone(), b.clone()), self.mul(b, a)),
            5 => (self.add(a.clone(), a), self.konst(F128::ZERO)),
            _ => {
                let s = self.add(a.clone(), b.clone());
                (self.add(s, b), a)
            }
        };
        debug_assert!(self.active.iter().all(|&t| l.1[t] == r.1[t]));
        if !self.active.iter().all(|&t| l.1[t] == r.1[t]) {
            return vec![];
        }
        self.note("identity");
        vec![St::AssertEq(l.0, r.0)]
    }

    /// Whether the compiler folds `e` to a constant: a literal in any spelling, a `Const` parameter or arm value, a
    /// constant-array element at a compile-time index, and arithmetic of those.
    fn compile_time(&self, e: &Ex) -> bool {
        match e {
            Ex::Lit(_) | Ex::Zero | Ex::GPow(_) | Ex::ConstInt(_) | Ex::J | Ex::JPow(_) | Ex::KPow(..) => {
                true
            }
            Ex::Arr(..) => true,
            Ex::Var(v) => matches!(self.vars[*v].kind, VK::Const { .. }) || self.vars[*v].folded,
            Ex::Add(x, y) | Ex::Mul(x, y) | Ex::Div(x, y) => self.compile_time(x) && self.compile_time(y),
            Ex::Pow(x, _) => self.compile_time(x),
            Ex::SRead(..) | Ex::HRead(..) | Ex::Call(_) => false,
        }
    }

    fn g_assert_ne(&mut self) -> Vec<St> {
        let a = self.ex(2);
        let b = self.ex(2);
        if !self.active.iter().all(|&t| a.1[t] != b.1[t]) {
            return vec![];
        }
        // Two literals once a `Const` is substituted are compared while compiling, in every specialization, the
        // ones no lane runs included.
        if self.compile_time(&a.0) && self.compile_time(&b.0) {
            return vec![];
        }
        self.note("assert !=");
        vec![St::AssertNe(a.0, b.0)]
    }

    fn g_range(&mut self) -> Vec<St> {
        let gs = self.gpow_scalars(1 << 16);
        if gs.is_empty() {
            return vec![];
        }
        let (x, logs) = gs[self.src.below(gs.len())].clone();
        let m = self.max_log(&logs);
        // A runtime bound: a hinted g-power already range-checked below 2^16, above every lane.
        if self.src.chance(1, 3) {
            let bounds: Vec<(V, Vec<u32>)> = self
                .gpow_scalars(1 << 16)
                .into_iter()
                .filter(|(b, bl)| self.vars[*b].rt && self.active.iter().all(|&t| bl[t] > logs[t]))
                .collect();
            if !bounds.is_empty() {
                let (b, _) = bounds[self.src.below(bounds.len())].clone();
                self.note("runtime range bound");
                return vec![St::AssertLtRt(Ex::Var(x), Ex::Var(b))];
            }
        }
        let k = (m + 1 + self.src.below(3) as u32 * self.src.below(40) as u32).min(1 << 16);
        self.note("range check");
        vec![St::AssertLt(Ex::Var(x), k)]
    }

    fn g_in_k(&mut self) -> Vec<St> {
        let a = self.in_k();
        let b = self.in_k();
        self.note("assert_in_k");
        vec![St::AssertInK(a.0, b.0)]
    }

    fn stream(&mut self) -> usize {
        let i = self.streams.len();
        self.streams.push((format!("s{i}"), Vec::new()));
        i
    }

    fn push_entries(&mut self, s: usize, per_lane: &[Vec<F128>]) {
        let entries: Vec<Vec<F128>> = self.active.iter().map(|&t| per_lane[t].clone()).collect();
        self.streams[s].1.extend(entries);
    }

    fn hint_value(&mut self, kind: usize) -> F128 {
        match kind {
            0 => {
                let bits = self.src.range(1, 9);
                gpow(self.src.below(1 << bits) as u64)
            }
            1 => lit(self.lit128()),
            _ => self.src.f128(),
        }
    }

    fn g_hint(&mut self) -> Vec<St> {
        let kind = self.src.below(3);
        let uniform = self.src.bool();
        let first = self.hint_value(kind);
        let n = self.n();
        let mut per = vec![vec![]; n];
        let mut vals = vec![F128::ZERO; n];
        for t in self.active.clone() {
            let x = if uniform { first } else { self.hint_value(kind) };
            per[t] = vec![x];
            vals[t] = x;
        }
        let s = self.stream();
        self.push_entries(s, &per);
        let v = self.new_var(VK::Scalar, vals.clone(), true);
        let mut out = vec![St::LetHint(v, self.streams[s].0.clone())];
        self.note("hint");
        if kind == 0 {
            let logs = self.logs(&vals).unwrap();
            let k = self.max_log(&logs) + 1 + self.src.below(8) as u32;
            out.push(St::AssertLt(Ex::Var(v), k));
        } else if let Some(x) = self.uniform(&vals)
            && self.src.bool()
        {
            out.push(St::AssertEq(Ex::Var(v), lit_of(x)));
        }
        out
    }

    /// `len` unwritten cells of a buffer the current code may fill: a fresh `StackBuf`, a slice of one of this
    /// context's, or of a visible `HeapBuf` (possibly at a runtime start).
    fn fresh_run(&mut self, len: u32, pre: &mut Vec<St>) -> (Run, V, Vec<u32>) {
        let n = self.n();
        match self.src.below(4) {
            1 => {
                let cands: Vec<V> = self
                    .stacks()
                    .into_iter()
                    .filter(|&v| self.vars[v].depth == self.depth() && self.size(v) >= len)
                    .collect();
                if !cands.is_empty() {
                    let v = cands[self.src.below(cands.len())];
                    let lo = self.src.below((self.size(v) - len + 1) as usize) as u32;
                    if self
                        .active
                        .iter()
                        .all(|&t| (lo..lo + len).all(|c| !self.written_anywhere(v, c, t)))
                    {
                        return (Run::Slice(v, lo, lo + len), v, vec![lo; n]);
                    }
                }
            }
            2 => {
                let hs = self.heaps();
                if !hs.is_empty() {
                    let v = hs[self.src.below(hs.len())];
                    let size = self.size(v);
                    if size >= len {
                        let lo = self.src.below((size - len + 1) as usize) as u32;
                        if self
                            .active
                            .iter()
                            .all(|&t| (lo..lo + len).all(|c| !self.written_anywhere(v, c, t)))
                        {
                            return (Run::Slice(v, lo, lo + len), v, vec![lo; n]);
                        }
                    }
                }
            }
            3 => {
                let hs = self.heaps();
                if !hs.is_empty() {
                    let v = hs[self.src.below(hs.len())];
                    let size = self.size(v);
                    let gs = self.index_vars(size.saturating_sub(len - 1));
                    if !gs.is_empty() {
                        let (x, logs) = gs[self.src.below(gs.len())].clone();
                        let ok = self
                            .active
                            .iter()
                            .all(|&t| (logs[t]..logs[t] + len).all(|c| !self.written_anywhere(v, c, t)));
                        // Two lanes sharing the buffer must not overlap.
                        let mut seen = std::collections::HashSet::new();
                        let disjoint = self
                            .active
                            .iter()
                            .all(|&t| (logs[t]..logs[t] + len).all(|c| seen.insert((self.inst(v, t), c))));
                        if ok && disjoint {
                            self.note("runtime slice");
                            return (Run::HeapRt(v, x, len), v, logs);
                        }
                    }
                }
            }
            _ => {}
        }
        let v = if self.src.bool() {
            self.new_stack(len)
        } else {
            let extra = self.src.below(3) as u32;
            self.new_heap(len + extra)
        };
        pre.push(match self.vars[v].kind {
            VK::Stack { .. } => St::Stack(v, len),
            _ => St::Heap(v, self.size(v)),
        });
        let whole = matches!(self.vars[v].kind, VK::Stack { .. });
        (if whole { Run::Whole(v) } else { Run::Slice(v, 0, len) }, v, vec![0; n])
    }

    fn g_hint_run(&mut self) -> Vec<St> {
        let len = self.src.range(1, 6) as u32;
        let mut out = Vec::new();
        let (run, v, starts) = self.fresh_run(len, &mut out);
        let n = self.n();
        let canonical = self.src.chance(3, 4);
        let mut per = vec![vec![]; n];
        let mut writes = Vec::new();
        for t in self.active.clone() {
            let vals: Vec<F128> = (0..len)
                .map(|_| if canonical { lit(self.lit128()) } else { self.src.f128() })
                .collect();
            for (i, &x) in vals.iter().enumerate() {
                writes.push((t, v, starts[t] + i as u32, x));
            }
            per[t] = vals;
        }
        if !self.try_write(&writes) {
            return vec![];
        }
        let s = self.stream();
        self.push_entries(s, &per);
        self.note("hint run");
        out.push(St::Hint(run, self.streams[s].0.clone()));
        out
    }

    fn g_store(&mut self) -> Vec<St> {
        let e = self.ex(3);
        // A stack cell of this context, or a heap cell.
        let mut places: Vec<(Place, V, Vec<u32>)> = Vec::new();
        let n = self.n();
        for v in self.stacks() {
            if self.vars[v].depth != self.depth() {
                continue;
            }
            let c = self.src.below(self.size(v) as usize) as u32;
            places.push((Place::Stack(v, Ix::Lit(c)), v, vec![c; n]));
        }
        for v in self.heaps() {
            let size = self.size(v);
            let c = self.src.below(size as usize) as u32;
            places.push((Place::Heap(v, HIx::Const(c)), v, vec![c; n]));
            let gs = self.index_vars(size);
            if !gs.is_empty() {
                let (x, logs) = gs[self.src.below(gs.len())].clone();
                let off = self.src.below((size - self.smax(x, &logs)) as usize) as u32;
                let cells = logs.iter().map(|&l| l + off).collect();
                places.push((Place::Heap(v, HIx::Rt(x, off)), v, cells));
            }
        }
        if places.is_empty() {
            return self.g_alloc();
        }
        let (place, v, cells) = places.swap_remove(self.src.below(places.len()));
        // Sometimes store what the cell already holds: the write-once equality.
        let restore = self.src.chance(1, 4);
        let (e, vals) = if restore {
            let held: Option<Vec<F128>> = self
                .active
                .iter()
                .map(|&t| self.cell(v, cells[t], t))
                .collect::<Option<Vec<_>>>()
                .map(|_| self.lanes(|t| self.cell(v, cells[t], t).unwrap()));
            match held.and_then(|h| self.uniform(&h)) {
                Some(x) => {
                    self.note("store as assertion");
                    self.konst(x)
                }
                None => e,
            }
        } else {
            e
        };
        let writes: Vec<_> = self.active.iter().map(|&t| (t, v, cells[t], vals[t])).collect();
        if !self.try_write(&writes) {
            return vec![];
        }
        self.note(if matches!(place, Place::Stack(..)) {
            "stack store"
        } else {
            "heap store"
        });
        vec![St::Store(place, e)]
    }

    fn g_list(&mut self) -> Vec<St> {
        let len = self.src.range(1, 5);
        let items: Vec<Tv> = (0..len).map(|_| self.ex(2)).collect();
        let v = self.new_stack(len as u32);
        let writes: Vec<_> = self
            .active
            .iter()
            .flat_map(|&t| items.iter().enumerate().map(move |(i, it)| (t, v, i as u32, it.1[t])))
            .collect();
        let ok = self.try_write(&writes);
        debug_assert!(ok);
        self.note("list literal");
        vec![St::List(v, items.into_iter().map(|i| i.0).collect())]
    }

    fn g_alloc(&mut self) -> Vec<St> {
        let n = self.src.range(1, 8) as u32;
        if self.src.bool() {
            let v = self.new_stack(n);
            vec![St::Stack(v, n)]
        } else {
            let v = self.new_heap(n);
            vec![St::Heap(v, n)]
        }
    }

    fn g_heap_dyn(&mut self) -> Vec<St> {
        // `HeapBuf(m)` holds `log m` cells; a hinted size keeps it a runtime one.
        let gs: Vec<(V, Vec<u32>)> = self
            .gpow_scalars(12)
            .into_iter()
            .filter(|(v, l)| self.vars[*v].rt && self.active.iter().all(|&t| l[t] > 0))
            .collect();
        if gs.is_empty() {
            return vec![];
        }
        let (m, logs) = gs[self.src.below(gs.len())].clone();
        let square = self.src.bool();
        let min = self.active.iter().map(|&t| logs[t]).min().unwrap_or(1) * if square { 2 } else { 1 };
        let v = self.new_heap(min);
        let size = if square {
            Ex::Mul(Box::new(Ex::Var(m)), Box::new(Ex::Var(m)))
        } else {
            Ex::Var(m)
        };
        self.note("runtime HeapBuf size");
        vec![St::HeapDyn(v, size)]
    }

    fn g_if(&mut self) -> Vec<St> {
        let rts: Vec<V> = self.scalars().into_iter().filter(|&v| self.vars[v].rt).collect();
        if rts.is_empty() {
            return self.g_hint();
        }
        self.nest += 1;
        let lhs = rts[self.src.below(rts.len())];
        let lv = self.lanes(|t| self.val(lhs, t));
        let mut rhs = match self.src.below(3) {
            0 => {
                let t = self.active[self.src.below(self.active.len())];
                self.konst(lv[t])
            }
            1 => {
                let v = rts[self.src.below(rts.len())];
                self.var_tv(v)
            }
            _ => self.ex(2),
        };
        // The test is a `JUMP` on `lhs + rhs`, which zkDSL.md requires in `K`: a condition outside it is the
        // documented `exec-fail` of `compiler/top_limb_branch.py`, not a program this generator may emit.
        let in_k = |g: &Self, r: &[F128]| g.active.iter().all(|&t| (lv[t] + r[t]).as_base().is_some());
        if !in_k(self, &rhs.1) {
            let t = self.active[self.src.below(self.active.len())];
            let delta = if self.src.bool() {
                F128::ZERO
            } else {
                lit(self.src.u64() as u128)
            };
            rhs = self.konst(lv[t] + delta);
            if !in_k(self, &rhs.1) {
                self.nest -= 1;
                return vec![];
            }
        }
        let ne = self.src.bool();
        let outer = self.active.clone();
        let then_lanes: Vec<usize> = outer.iter().copied().filter(|&t| (lv[t] == rhs.1[t]) != ne).collect();
        let else_lanes: Vec<usize> = outer.iter().copied().filter(|&t| (lv[t] == rhs.1[t]) == ne).collect();
        if !then_lanes.is_empty() && !else_lanes.is_empty() {
            self.note("if: both arms taken");
        }
        let mut out = Vec::new();
        // An early return: the lanes that take the arm leave the function.
        let early = self.fun().allow_early && self.fns.len() > 1 && self.depth_is_fn_top() && self.src.chance(1, 3);
        // Cells both arms write, read after the join.
        let joins = if early { 0 } else { self.src.range(1, 2) as u32 };
        let jb = if joins > 0 {
            let v = if self.src.bool() {
                self.new_stack(joins)
            } else {
                self.new_heap(joins)
            };
            out.push(match self.vars[v].kind {
                VK::Stack { .. } => St::Stack(v, joins),
                _ => St::Heap(v, joins),
            });
            self.reserved.insert(v);
            Some(v)
        } else {
            None
        };
        let sub = self.src.range(1, 6);
        let arm = |g: &mut Self, lanes: Vec<usize>, ret: bool| -> Vec<St> {
            g.active = lanes;
            g.scopes.push(Vec::new());
            let mut body = g.block(sub);
            if let Some(jb) = jb {
                for c in 0..joins {
                    let e = g.ex(2);
                    let writes: Vec<_> = g.active.iter().map(|&t| (t, jb, c, e.1[t])).collect();
                    let ok = g.try_write(&writes);
                    debug_assert!(ok);
                    let place = match g.vars[jb].kind {
                        VK::Stack { .. } => Place::Stack(jb, Ix::Lit(c)),
                        _ => Place::Heap(jb, HIx::Const(c)),
                    };
                    body.push(St::Store(place, e.0));
                }
            }
            if ret {
                body.push(g.ret());
            }
            g.scopes.pop();
            body
        };
        let then = arm(self, then_lanes.clone(), early);
        let els = if else_lanes.is_empty() && jb.is_none() && self.src.bool() {
            Vec::new()
        } else if else_lanes.is_empty() && self.src.bool() && !early {
            // An arm no lane takes still has to write the join cells for... nothing: leave it out.
            Vec::new()
        } else {
            arm(self, else_lanes.clone(), false)
        };
        self.active = if early { else_lanes } else { outer };
        if let Some(jb) = jb {
            self.reserved.remove(&jb);
        }
        if early {
            self.fns.last_mut().unwrap().early = true;
            self.note("early return");
        }
        self.nest -= 1;
        self.note("if");
        out.push(St::If {
            ne,
            lhs: Ex::Var(lhs),
            rhs: rhs.0,
            then,
            els,
        });
        if let Some(jb) = jb {
            for c in 0..joins {
                if let Some(vals) = self.cells_all(jb, c) {
                    let rt = false;
                    let read = match self.vars[jb].kind {
                        VK::Stack { .. } => Ex::SRead(jb, Ix::Lit(c)),
                        _ => Ex::HRead(jb, HIx::Const(c)),
                    };
                    let v = self.new_var(VK::Scalar, vals, rt);
                    out.push(St::Let(v, read, Route::Any));
                }
            }
        }
        out
    }

    /// Whether the code being generated is a function's own top-level block (not a loop body or an arm inside it).
    /// `if const(k % m == r):` on a `Const` parameter: decided per specialization, each lane by its own `k`.
    fn g_if_const(&mut self) -> Vec<St> {
        let ks: Vec<V> = self
            .scalars()
            .into_iter()
            .filter(|&v| matches!(self.vars[v].kind, VK::Const { .. }))
            .collect();
        if ks.is_empty() {
            return self.g_let();
        }
        let k = ks[self.src.below(ks.len())];
        let m = self.src.range(2, 3) as u32;
        let r = self.src.below(m as usize) as u32;
        let d = self.vars[k].depth;
        let kv: Vec<u32> = (0..self.n())
            .map(|t| match &self.vars[k].kind {
                VK::Const { ks, .. } => ks[self.lift(t, d)],
                _ => unreachable!(),
            })
            .collect();
        self.fns.last_mut().unwrap().konst_ct = true;
        self.nest += 1;
        let outer = self.active.clone();
        let jb = self.new_stack(1);
        let mut out = vec![St::Stack(jb, 1)];
        self.reserved.insert(jb);
        let mut arms = Vec::new();
        for taken in [true, false] {
            self.active = outer.iter().copied().filter(|&t| (kv[t] % m == r) == taken).collect();
            self.scopes.push(Vec::new());
            let sub = self.src.range(1, 4);
            let mut body = self.block(sub);
            let e = self.ex(2);
            let writes: Vec<_> = self.active.iter().map(|&t| (t, jb, 0, e.1[t])).collect();
            let ok = self.try_write(&writes);
            debug_assert!(ok);
            body.push(St::Store(Place::Stack(jb, Ix::Lit(0)), e.0));
            self.scopes.pop();
            arms.push(body);
        }
        self.active = outer;
        self.reserved.remove(&jb);
        self.nest -= 1;
        let els = arms.pop().unwrap();
        let then = arms.pop().unwrap();
        self.note("if const");
        out.push(St::IfConst { k, m, r, then, els });
        if let Some(vals) = self.cells_all(jb, 0) {
            let v = self.new_var(VK::Scalar, vals, false);
            out.push(St::Let(v, Ex::SRead(jb, Ix::Lit(0)), Route::Any));
        }
        out
    }

    fn depth_is_fn_top(&self) -> bool {
        self.cx().loop_id.is_none() && self.scopes.len() == self.barrier + 1
    }

    /// The `return` of the function being generated, on the active lanes.
    fn ret(&mut self) -> St {
        let nret = self.fun().nret;
        let mut items = Vec::new();
        for i in 0..nret {
            let e = self.ex(2);
            for &t in &self.active {
                self.fns.last_mut().unwrap().rets[i][t] = e.1[t];
            }
            items.push(Ret::Val(e.0));
        }
        St::Return(items)
    }

    /// Generate a function called from `lanes` of the current context with `args`, and return it with each
    /// return's per-caller-lane values (a scalar's value, or a returned buffer's cells).
    fn make_fn(
        &mut self,
        lanes: Vec<usize>,
        args: Vec<(Arg, ArgV)>,
        rets: RetShape,
        as_arm: bool,
    ) -> (Call, Vec<RetV>) {
        let f = self.prog.funs.len();
        self.prog.funs.push(Fun {
            params: Vec::new(),
            body: Vec::new(),
            inline: Mode::Either,
            konst: Mode::Either,
        });
        let caller_n = self.n();
        let saved_active = std::mem::take(&mut self.active);
        let saved_barrier = self.barrier;
        let saved_j = self.jctx.take();
        self.push_cx(lanes.clone(), None);
        let n = lanes.len();
        self.active = (0..n).collect();
        self.barrier = self.scopes.len();
        self.scopes.push(Vec::new());
        let mut params = Vec::new();
        for (_, a) in &args {
            match a {
                ArgV::Val(vals, rt) => {
                    let pv = (0..n).map(|t| vals[lanes[t]]).collect();
                    let v = self.new_var(VK::Scalar, pv, *rt);
                    params.push((v, PK::Scalar));
                }
                ArgV::Const(ks, kmax) => {
                    let ks: Vec<u32> = (0..n).map(|t| ks[lanes[t]]).collect();
                    let pv = ks.iter().map(|&k| lit(k as u128)).collect();
                    let v = self.new_var(VK::Const { ks, kmax: *kmax }, pv, false);
                    params.push((v, PK::Const));
                }
                ArgV::Heap(size, insts) => {
                    let inst = (0..n).map(|t| insts[lanes[t]]).collect();
                    let v = self.new_var(VK::Heap { n: *size, inst }, vec![F128::ZERO; n], false);
                    params.push((v, PK::Heap));
                }
                ArgV::Stack(size, cells) => {
                    let v = self.new_stack(*size);
                    let writes: Vec<_> = (0..n)
                        .flat_map(|t| (0..*size).map(move |c| (t, c)))
                        .map(|(t, c)| (t, v, c, cells[lanes[t]][c as usize]))
                        .collect();
                    let ok = self.try_write(&writes);
                    debug_assert!(ok);
                    params.push((v, PK::Stack(*size)));
                }
            }
        }
        let nret = match &rets {
            RetShape::Scalars(k) => *k,
            RetShape::Buf(..) => 0,
        };
        self.fns.push(FnState {
            fun: f,
            nret,
            rets: vec![vec![F128::ZERO; n]; nret],
            early: false,
            allow_early: !as_arm && matches!(rets, RetShape::Scalars(_)),
            has_mul: false,
            konst_ct: false,
        });
        self.nest += 1;
        let sub = self.src.range(1, 10);
        let mut body = self.block(sub);
        self.nest -= 1;
        let mut out = Vec::new();
        match rets {
            RetShape::Scalars(_) => body.push(self.ret()),
            RetShape::Buf(size) => {
                let len = size;
                let items: Vec<Tv> = (0..len).map(|_| self.ex(2)).collect();
                let v = self.new_stack(len);
                let writes: Vec<_> = self
                    .active
                    .iter()
                    .flat_map(|&t| items.iter().enumerate().map(move |(i, it)| (t, v, i as u32, it.1[t])))
                    .collect();
                let ok = self.try_write(&writes);
                debug_assert!(ok);
                body.push(St::List(v, items.iter().map(|i| i.0.clone()).collect()));
                body.push(St::Return(vec![Ret::Buf(v)]));
                let mut cells = vec![vec![F128::ZERO; len as usize]; caller_n];
                for t in 0..n {
                    cells[lanes[t]] = items.iter().map(|i| i.1[t]).collect();
                }
                out.push(RetV::Buf(len, cells));
            }
        }
        let st = self.fns.pop().unwrap();
        for r in &st.rets {
            let mut vals = vec![F128::ZERO; caller_n];
            for t in 0..n {
                vals[lanes[t]] = r[t];
            }
            out.push(RetV::Val(vals));
        }
        // Returned values are bound in the caller, but what the callee read and wrote stays in memory.
        self.scopes.truncate(self.barrier);
        self.barrier = saved_barrier;
        self.pop_cx();
        self.active = saved_active;
        self.jctx = saved_j;
        let fun = &mut self.prog.funs[f];
        fun.params = params;
        fun.body = body;
        fun.inline = if st.early || st.has_mul {
            Mode::Never
        } else {
            Mode::Either
        };
        fun.konst = if st.konst_ct { Mode::Always } else { Mode::Either };
        if st.early && st.has_mul {
            self.note("early return and loop");
        }
        let call = Call {
            f,
            args: args.into_iter().map(|(a, _)| a).collect(),
        };
        (call, out)
    }

    /// Arguments for a call from the active lanes: scalars, maybe a buffer of each kind, maybe a `Const`.
    fn call_args(&mut self, konst: Option<(Arg, Vec<u32>, u32)>) -> Vec<(Arg, ArgV)> {
        let mut args = Vec::new();
        for _ in 0..self.src.range(0, 3) {
            let (e, vals) = self.ex(2);
            let rt = self.rt(&e);
            args.push((Arg::Val(e), ArgV::Val(vals, rt)));
        }
        if self.src.chance(1, 3) {
            let hs = self.heaps();
            if !hs.is_empty() {
                let v = hs[self.src.below(hs.len())];
                let insts = (0..self.n())
                    .map(|t| {
                        if self.active.contains(&t) {
                            self.inst(v, t)
                        } else {
                            usize::MAX
                        }
                    })
                    .collect();
                args.push((Arg::Buf(v), ArgV::Heap(self.size(v), insts)));
            }
        }
        if self.src.chance(1, 3) {
            // A wholly written StackBuf, copied into the callee.
            let full: Vec<V> = self
                .stacks()
                .into_iter()
                .filter(|&v| self.stack_readable(v) && (0..self.size(v)).all(|c| self.cells_all(v, c).is_some()))
                .collect();
            if !full.is_empty() {
                let v = full[self.src.below(full.len())];
                let size = self.size(v);
                let n = self.n();
                let mut cells = vec![vec![]; n];
                for &t in &self.active {
                    cells[t] = (0..size).map(|c| self.cell(v, c, t).unwrap()).collect();
                }
                self.note("StackBuf argument");
                args.push((Arg::Buf(v), ArgV::Stack(size, cells)));
            }
        }
        if let Some((a, ks, kmax)) = konst {
            args.push((a, ArgV::Const(ks, kmax)));
        }
        // Parameter order is the generator's choice too.
        let len = args.len();
        if len > 1 {
            for i in 0..len {
                let j = self.src.below(len);
                args.swap(i, j);
            }
        }
        args
    }

    fn g_call(&mut self) -> Vec<St> {
        self.spend(2);
        let konst = if self.src.chance(1, 3) {
            let k = self.src.below(12) as u32;
            Some((Arg::Int(k), vec![k; self.n()], k))
        } else {
            None
        };
        if konst.is_some() {
            self.note("Const argument");
        }
        let args = self.call_args(konst);
        let lanes = self.active.clone();
        let shape = match self.src.below(6) {
            0 => RetShape::Buf(self.src.range(1, 4) as u32),
            1 => RetShape::Scalars(0),
            2 | 3 => RetShape::Scalars(1),
            _ => RetShape::Scalars(self.src.range(2, 3)),
        };
        // An expression to combine a single return with, drawn before the call so it reads nothing the call writes.
        let other = matches!(shape, RetShape::Scalars(1)).then(|| self.ex(2));
        let (call, rets) = self.make_fn(lanes, args, shape, false);
        self.note("call");
        let mut out = Vec::new();
        // Returns may be discarded by a call statement.
        if matches!(rets.as_slice(), [RetV::Val(_), ..]) && self.src.chance(1, 6) {
            self.note("returns discarded");
            out.push(St::Call(vec![], call));
            return out;
        }
        match rets.as_slice() {
            [] => out.push(St::Call(vec![], call)),
            [RetV::Buf(len, cells)] => {
                let v = self.new_stack(*len);
                let writes: Vec<_> = self
                    .active
                    .iter()
                    .flat_map(|&t| (0..*len).map(move |c| (t, c)))
                    .map(|(t, c)| (t, v, c, cells[t][c as usize]))
                    .collect();
                let ok = self.try_write(&writes);
                debug_assert!(ok);
                self.note("StackBuf return");
                out.push(St::Call(vec![v], call));
            }
            [RetV::Val(vals)] => {
                let vals = vals.clone();
                let other = other.unwrap();
                match self.src.below(4) {
                    0 => {
                        let combined = self.add((Ex::Call(Box::new(call)), vals), other);
                        let v = self.new_var(VK::Scalar, combined.1, false);
                        self.note("call in expression");
                        out.push(St::Let(v, combined.0, Route::Direct));
                    }
                    1 => {
                        // Into a stack cell of this context, unwritten on every lane.
                        let st = self
                            .stacks()
                            .into_iter()
                            .filter(|&v| self.vars[v].depth == self.depth())
                            .find(|&v| self.active.iter().all(|&t| !self.written_anywhere(v, 0, t)));
                        match st {
                            Some(sb) => {
                                let writes: Vec<_> = self.active.iter().map(|&t| (t, sb, 0, vals[t])).collect();
                                let ok = self.try_write(&writes);
                                debug_assert!(ok);
                                self.note("call into a stack cell");
                                out.push(St::Store(Place::Stack(sb, Ix::Lit(0)), Ex::Call(Box::new(call))));
                            }
                            None => {
                                let v = self.new_var(VK::Scalar, vals, false);
                                out.push(St::Call(vec![v], call));
                            }
                        }
                    }
                    _ => {
                        let v = self.new_var(VK::Scalar, vals, false);
                        out.push(St::Call(vec![v], call));
                    }
                }
            }
            many => {
                let mut vs = Vec::new();
                for r in many {
                    let RetV::Val(vals) = r else { unreachable!() };
                    vs.push(self.new_var(VK::Scalar, vals.clone(), false));
                }
                self.note("tuple return");
                out.push(St::Call(vs, call));
            }
        }
        out
    }

    fn g_match(&mut self) -> Vec<St> {
        self.spend(2);
        // The scrutinee: a g-power below 8 on every lane.
        let gs = self.index_vars(8);
        let (x, logs, smax) = if !gs.is_empty() && self.src.chance(4, 5) {
            let (v, l) = gs[self.src.below(gs.len())].clone();
            let smax = self.smax(v, &l);
            (Ex::Var(v), l, smax)
        } else {
            let k = self.src.below(6) as u32;
            self.note("constant scrutinee");
            (Ex::GPow(k as u64), vec![k; self.n()], k)
        };
        let mut out = Vec::new();
        let m = smax;
        let n = (m + 1 + self.src.below(3) as u32).min(8).max(m + 1);
        if self.rt(&x) {
            out.push(St::AssertLt(x.clone(), n));
        }
        self.nest += 1;
        let split = if n > 1 && self.src.chance(1, 3) {
            Some(self.src.range(1, n as usize - 1) as u32)
        } else {
            None
        };
        let ranges: Vec<(u32, u32)> = match split {
            Some(s) => vec![(0, s), (s, n)],
            None => vec![(0, n)],
        };
        let call_seg = self.src.chance(1, 2).then(|| self.src.below(ranges.len()));
        let nret = if ranges.len() == 1 && call_seg.is_some() {
            self.src.range(1, 2)
        } else {
            1
        };
        let outer = self.active.clone();
        let mut segs = Vec::new();
        let mut results = vec![vec![F128::ZERO; self.n()]; nret];
        for (si, &(lo, hi)) in ranges.iter().enumerate() {
            let lanes: Vec<usize> = outer
                .iter()
                .copied()
                .filter(|&t| logs[t] >= lo && logs[t] < hi)
                .collect();
            if call_seg == Some(si) {
                let js = logs.clone();
                self.active = outer.clone();
                let args = {
                    self.active = lanes.clone();
                    self.call_args_no_stack(Some((Arg::J, js, hi - 1)))
                };
                let (call, rets) = self.make_fn(lanes.clone(), args, RetShape::Scalars(nret), true);
                for (i, r) in rets.iter().enumerate() {
                    let RetV::Val(vals) = r else { unreachable!() };
                    for &t in &lanes {
                        results[i][t] = vals[t];
                    }
                }
                self.note("match: call arm");
                segs.push(Seg {
                    lo,
                    hi,
                    arm: Arm::Call(call),
                });
            } else {
                self.active = lanes.clone();
                self.jctx = Some(JCtx { js: logs.clone(), hi });
                let e = self.ex(2);
                self.jctx = None;
                for &t in &lanes {
                    results[0][t] = e.1[t];
                }
                self.note("match: expression arm");
                segs.push(Seg {
                    lo,
                    hi,
                    arm: Arm::Ex(e.0),
                });
            }
        }
        self.active = outer;
        self.nest -= 1;
        if segs.len() > 1 {
            self.note("match: two segments");
        }
        let mut targets = Vec::new();
        let mut post = Vec::new();
        for (i, vals) in results.into_iter().enumerate() {
            // A single result may land in a stack cell of this context.
            if i == 0 && nret == 1 && self.src.chance(1, 3) {
                let sb = self.new_stack(1);
                out.push(St::Stack(sb, 1));
                let writes: Vec<_> = self.active.iter().map(|&t| (t, sb, 0, vals[t])).collect();
                let ok = self.try_write(&writes);
                debug_assert!(ok);
                targets.push(Target::Cell(sb, 0));
                let v = self.new_var(VK::Scalar, vals, false);
                post.push(St::Let(v, Ex::SRead(sb, Ix::Lit(0)), Route::Any));
                self.note("match into a stack cell");
                continue;
            }
            let v = self.new_var(VK::Scalar, vals, false);
            targets.push(Target::Var(v));
        }
        out.push(St::Match { targets, x, segs });
        out.extend(post);
        out
    }

    fn call_args_no_stack(&mut self, konst: Option<(Arg, Vec<u32>, u32)>) -> Vec<(Arg, ArgV)> {
        let mut args = self.call_args(konst);
        // A fused arm cannot pass a StackBuf.
        args.retain(|(_, a)| !matches!(a, ArgV::Stack(..)));
        args
    }

    fn g_loop(&mut self) -> Vec<St> {
        self.spend(2);
        let mut pre = Vec::new();
        let outer = self.active.clone();
        let lo = self.src.below(3) as u32;
        let budget_lanes = self.lim.max_lanes / outer.len().max(1);
        if budget_lanes == 0 {
            return vec![];
        }
        let maxc = (budget_lanes as u32).min(6);
        let runtime = self.src.chance(1, 3);
        let n = self.n();
        let mut counts = vec![0u32; n];
        let hi_e;
        if runtime {
            let uniform = self.src.bool();
            let c0 = self.src.below(maxc as usize + 1) as u32;
            for &t in &outer {
                counts[t] = if uniform {
                    c0
                } else {
                    self.src.below(maxc as usize + 1) as u32
                };
            }
            let vals = self.lanes(|t| gpow((lo + counts[t]) as u64));
            let s = self.stream();
            let per: Vec<Vec<F128>> = (0..n).map(|t| vec![vals[t]]).collect();
            self.push_entries(s, &per);
            let b = self.new_var(VK::Scalar, vals, true);
            pre.push(St::LetHint(b, self.streams[s].0.clone()));
            pre.push(St::AssertLt(Ex::Var(b), 64));
            hi_e = Hi::Rt(Ex::Var(b));
            self.note("runtime loop bound");
        } else {
            let c = self.src.below(maxc as usize + 1) as u32;
            for &t in &outer {
                counts[t] = c;
            }
            hi_e = Hi::Const(lo + c);
        }
        let hi_max = outer.iter().map(|&t| lo + counts[t]).max().unwrap_or(lo);
        let extra = self.src.below(2) as u32;
        let out_buf = self.new_heap(hi_max + 1 + extra);
        pre.push(St::Heap(out_buf, self.size(out_buf)));
        self.reserved.insert(out_buf);
        // A chain through the iterations: `acc[i·g] = acc[i]·c + e`.
        let chain = self.src.chance(1, 3);
        let acc = if chain {
            let a = self.new_heap(hi_max + 2);
            pre.push(St::Heap(a, hi_max + 2));
            let e0 = self.ex(1);
            let writes: Vec<_> = outer.iter().map(|&t| (t, a, lo, e0.1[t])).collect();
            let ok = self.try_write(&writes);
            debug_assert!(ok);
            pre.push(St::Store(Place::Heap(a, HIx::Const(lo)), e0.0));
            self.reserved.insert(a);
            Some(a)
        } else {
            None
        };
        let l = self.prog.loops.len();
        let fun = self.fun().fun;
        self.prog.loops.push(Loop {
            var: usize::MAX,
            lo,
            hi: hi_e,
            body: Vec::new(),
            form: if runtime { Form::MulRange } else { Form::Either },
            fun,
        });
        if runtime {
            self.fns.last_mut().unwrap().has_mul = true;
        }
        let mut parent_of = Vec::new();
        let mut iters = Vec::new();
        for &t in &outer {
            for it in 0..counts[t] {
                parent_of.push(t);
                iters.push(lo + it);
            }
        }
        self.push_cx(parent_of.clone(), Some(l));
        let saved_active = std::mem::take(&mut self.active);
        self.active = (0..parent_of.len()).collect();
        self.scopes.push(Vec::new());
        let cvals: Vec<F128> = iters.iter().map(|&i| gpow(i as u64)).collect();
        let counter = self.new_var(VK::Counter, cvals, false);
        self.prog.counter_of.insert(counter, l);
        self.prog.loops[l].var = counter;
        self.nest += 1;
        let sub = self.src.range(1, 8);
        let mut body = self.block(sub);
        self.nest -= 1;
        if let Some(a) = acc {
            let c = self.nonzero(0);
            let e = self.ex(1);
            // Lanes in order: each reads what the iteration before it wrote.
            let mut ok = true;
            for &t in &self.active.clone() {
                let i = iters[t];
                let prev = self.mem.get(&(self.inst(a, t), i)).map(|x| x.0);
                let Some(prev) = prev else {
                    ok = false;
                    break;
                };
                let next = prev * c.1[t] + e.1[t];
                ok &= self.try_write(&[(t, a, i + 1, next)]);
            }
            debug_assert!(ok);
            let read = Ex::HRead(a, HIx::Rt(counter, 0));
            let value = Ex::Add(Box::new(Ex::Mul(Box::new(read), Box::new(c.0))), Box::new(e.0));
            body.push(St::Store(Place::Heap(a, HIx::Rt(counter, 1)), value));
            self.note("loop-carried chain");
        }
        let e = self.ex(2);
        let writes: Vec<_> = self.active.iter().map(|&t| (t, out_buf, iters[t], e.1[t])).collect();
        let ok = self.try_write(&writes);
        debug_assert!(ok);
        body.push(St::Store(Place::Heap(out_buf, HIx::Rt(counter, 0)), e.0));
        self.scopes.pop();
        self.pop_cx();
        self.active = saved_active;
        self.reserved.remove(&out_buf);
        if let Some(a) = acc {
            self.reserved.remove(&a);
        }
        self.prog.loops[l].body = body;
        self.note(if runtime { "mul_range" } else { "constant loop" });
        pre.push(St::Loop(l));
        let min = outer.iter().map(|&t| lo + counts[t]).min().unwrap_or(lo);
        for k in lo..min {
            if let Some(vals) = self.cells_all(out_buf, k) {
                let v = self.new_var(VK::Scalar, vals, false);
                pre.push(St::Let(v, Ex::HRead(out_buf, HIx::Const(k)), Route::Any));
            }
        }
        if let Some(a) = acc
            && let Some(vals) = self.cells_all(a, min)
        {
            let v = self.new_var(VK::Scalar, vals, false);
            pre.push(St::Let(v, Ex::HRead(a, HIx::Const(min)), Route::Any));
        }
        pre
    }

    /// Two cells for a `keccak` operand, canonical and readable on every active lane.
    fn pair(&mut self, pre: &mut Vec<St>) -> (Run, Vec<[F128; 2]>) {
        let n = self.n();
        for _ in 0..3 {
            match self.src.below(4) {
                0 => {
                    let st: Vec<V> = self.stacks().into_iter().filter(|&v| self.stack_readable(v)).collect();
                    if !st.is_empty() {
                        let v = st[self.src.below(st.len())];
                        let size = self.size(v);
                        if size >= 2 {
                            let lo = self.src.below((size - 1) as usize) as u32;
                            if let (Some(a), Some(b)) = (self.cells_all(v, lo), self.cells_all(v, lo + 1)) {
                                let run = if size == 2 {
                                    Run::Whole(v)
                                } else {
                                    Run::Slice(v, lo, lo + 2)
                                };
                                return (run, (0..n).map(|t| [a[t], b[t]]).collect());
                            }
                        }
                    }
                }
                1 => {
                    let hs = self.heaps();
                    if !hs.is_empty() {
                        let v = hs[self.src.below(hs.len())];
                        let size = self.size(v);
                        if size >= 2 {
                            if self.src.bool() {
                                let lo = self.src.below((size - 1) as usize) as u32;
                                if let (Some(a), Some(b)) = (self.cells_all(v, lo), self.cells_all(v, lo + 1)) {
                                    return (Run::Slice(v, lo, lo + 2), (0..n).map(|t| [a[t], b[t]]).collect());
                                }
                            } else {
                                let gs = self.index_vars(size - 1);
                                if !gs.is_empty() {
                                    let (x, logs) = gs[self.src.below(gs.len())].clone();
                                    let cells: Option<Vec<[F128; 2]>> = self
                                        .active
                                        .iter()
                                        .map(|&t| Some([self.cell(v, logs[t], t)?, self.cell(v, logs[t] + 1, t)?]))
                                        .collect();
                                    if let Some(cells) = cells
                                        && cells.iter().all(|c| c[0].c1 == 0 && c[1].c1 == 0)
                                    {
                                        let mut out = vec![[F128::ZERO; 2]; n];
                                        for (i, &t) in self.active.iter().enumerate() {
                                            out[t] = cells[i];
                                        }
                                        self.note("runtime keccak slice");
                                        return (Run::HeapRt(v, x, 2), out);
                                    }
                                }
                            }
                        }
                    }
                }
                _ => {
                    let a = self.canonical();
                    let b = self.canonical();
                    return (Run::List(vec![a.0, b.0]), (0..n).map(|t| [a.1[t], b.1[t]]).collect());
                }
            }
        }
        let _ = pre;
        let a = self.canonical();
        let b = self.canonical();
        (Run::List(vec![a.0, b.0]), (0..n).map(|t| [a.1[t], b.1[t]]).collect())
    }

    /// Where a digest goes: `cells` fresh cells, or the cells of an earlier digest of the same message (the
    /// write-once equality, which makes the hash a verification).
    fn digest_out(&mut self, cells: u32, digests: &[Vec<F128>], pre: &mut Vec<St>) -> Option<Run> {
        let (run, v, starts) = self.fresh_run(cells, pre);
        let writes: Vec<_> = self
            .active
            .iter()
            .flat_map(|&t| (0..cells).map(move |c| (t, c)))
            .map(|(t, c)| (t, v, starts[t] + c, digests[t][c as usize]))
            .collect();
        self.try_write(&writes).then_some(run)
    }

    fn digest_reads(&mut self, run: &Run, cells: u32) -> Vec<St> {
        let mut out = Vec::new();
        for c in 0..cells {
            let (read, buf, cell) = match run {
                Run::Whole(v) => (Ex::SRead(*v, Ix::Lit(c)), *v, c),
                Run::Slice(v, lo, _) => match self.vars[*v].kind {
                    VK::Stack { .. } => (Ex::SRead(*v, Ix::Lit(lo + c)), *v, lo + c),
                    _ => (Ex::HRead(*v, HIx::Const(lo + c)), *v, lo + c),
                },
                Run::HeapRt(v, x, _) => {
                    let n = self.n();
                    let Some(logs) = self.logs(&self.lanes(|t| self.val(*x, t))) else {
                        continue;
                    };
                    let vals: Option<Vec<F128>> = (0..n)
                        .map(|t| {
                            if self.active.contains(&t) {
                                self.cell(*v, logs[t] + c, t)
                            } else {
                                Some(F128::ZERO)
                            }
                        })
                        .collect();
                    if let Some(vals) = vals {
                        let nv = self.new_var(VK::Scalar, vals, false);
                        out.push(St::Let(nv, Ex::HRead(*v, HIx::Rt(*x, c)), Route::Any));
                    }
                    continue;
                }
                Run::List(_) => continue,
            };
            if matches!(self.vars[buf].kind, VK::Stack { .. }) && !self.stack_readable(buf) {
                continue;
            }
            if let Some(vals) = self.cells_all(buf, cell) {
                let nv = self.new_var(VK::Scalar, vals, false);
                out.push(St::Let(nv, read, Route::Any));
            }
        }
        out
    }

    fn g_keccak(&mut self) -> Vec<St> {
        let mut pre = Vec::new();
        let n = self.n();
        let (a, av) = self.pair(&mut pre);
        let tail = self.src.chance(1, 5);
        let (b, bv, len) = if !tail && self.src.chance(1, 3) {
            // A message shorter than 64 bytes: the cells past it are literal zeros, the bytes past it in the cell
            // it ends in are zero.
            let len = self.src.range(33, 63) as u32;
            let mask = |m: u32| -> u128 { if m >= 16 { u128::MAX } else { (1u128 << (8 * m)) - 1 } };
            let (b0, b1);
            if len <= 48 {
                let x = self.lit128() & mask(len - 32);
                b0 = (Ex::Lit(x), self.lanes(|_| lit(x)));
                b1 = (Ex::Zero, self.lanes(|_| F128::ZERO));
            } else {
                b0 = self.canonical();
                let x = self.lit128() & mask(len - 48);
                b1 = (Ex::Lit(x), self.lanes(|_| lit(x)));
            }
            self.note("keccak len");
            let bv = (0..n).map(|t| [b0.1[t], b1.1[t]]).collect();
            (Run::List(vec![b0.0, b1.0]), bv, Some(len))
        } else {
            let (b, bv) = self.pair(&mut pre);
            (b, bv, None)
        };
        let tail_run = if tail {
            let items: Vec<Tv> = (0..4).map(|_| self.canonical()).collect();
            self.note("keccak tail");
            Some(items)
        } else {
            None
        };
        let cells = *self.src.pick(&[1u32, 2, 2, 2]);
        let mut digests = vec![vec![]; n];
        for &t in &self.active {
            let mut msg = Vec::new();
            for x in av[t].iter().chain(bv[t].iter()) {
                msg.extend(bytes(*x));
            }
            if let Some(items) = &tail_run {
                for it in items {
                    msg.extend(bytes(it.1[t]));
                }
            }
            if let Some(len) = len {
                msg.truncate(len as usize);
            }
            digests[t] = digest_cells(&hash(&msg));
        }
        let Some(out) = self.digest_out(cells, &digests, &mut pre) else {
            return vec![];
        };
        self.note("keccak");
        let reads = self.digest_reads(&out, cells);
        pre.push(St::Keccak {
            a,
            b,
            tail: tail_run.map(|items| Run::List(items.into_iter().map(|i| i.0).collect())),
            out,
            len,
        });
        pre.extend(reads);
        pre
    }

    fn g_keccak_cells(&mut self) -> Vec<St> {
        let mut pre = Vec::new();
        let n = self.n();
        // A wholly written canonical StackBuf, or a list.
        let full: Vec<V> = self
            .stacks()
            .into_iter()
            .filter(|&v| {
                self.stack_readable(v)
                    && (0..self.size(v)).all(|c| self.cells_all(v, c).is_some_and(|x| self.all(&x, |y| y.c1 == 0)))
            })
            .collect();
        let (run, msgs): (Run, Vec<Vec<F128>>) = if !full.is_empty() && self.src.bool() {
            let v = full[self.src.below(full.len())];
            let size = self.size(v);
            let mut msgs = vec![vec![]; n];
            for &t in &self.active {
                msgs[t] = (0..size).map(|c| self.cell(v, c, t).unwrap()).collect();
            }
            self.note("keccak_cells of a StackBuf");
            (Run::Whole(v), msgs)
        } else {
            let long = self.src.chance(1, 4);
            let len = self.src.range(1, if long { 20 } else { 6 });
            let items: Vec<Tv> = (0..len).map(|_| self.canonical()).collect();
            let mut msgs = vec![vec![]; n];
            for &t in &self.active {
                msgs[t] = items.iter().map(|i| i.1[t]).collect();
            }
            self.note("keccak_cells of a list");
            (Run::List(items.into_iter().map(|i| i.0).collect()), msgs)
        };
        let ncells = msgs.iter().map(|m| m.len()).max().unwrap_or(0).max(match &run {
            Run::Whole(v) => self.size(*v) as usize,
            Run::List(items) => items.len(),
            _ => 0,
        }) as u32;
        // `len` ending inside the last cell, where every lane's bytes past it are zero.
        let mut len = None;
        if self.src.chance(1, 3) {
            let m = self.src.range(1, 16) as u32;
            let fits = self.active.iter().all(|&t| {
                let last = msgs[t][ncells as usize - 1];
                m == 16 || bytes(last)[m as usize..].iter().all(|&b| b == 0)
            });
            if fits {
                len = Some(16 * (ncells - 1) + m);
                self.note("keccak_cells len");
            }
        }
        let cells = *self.src.pick(&[1u32, 2, 2]);
        let mut digests = vec![vec![]; n];
        for &t in &self.active {
            let mut msg: Vec<u8> = msgs[t].iter().flat_map(|x| bytes(*x)).collect();
            if let Some(len) = len {
                msg.truncate(len as usize);
            }
            digests[t] = digest_cells(&hash(&msg));
        }
        let Some(out) = self.digest_out(cells, &digests, &mut pre) else {
            return vec![];
        };
        let reads = self.digest_reads(&out, cells);
        pre.push(St::KeccakCells { cells: run, out, len });
        pre.extend(reads);
        pre
    }

    // ----- the end of main -----

    /// Fold every value `main` can still see into two words, assert them, and publish them.
    fn publish(&mut self) -> Vec<St> {
        let mut out = Vec::new();
        let mut terms: Vec<Tv> = Vec::new();
        for v in self.visible() {
            match &self.vars[v].kind {
                VK::Scalar => terms.push(self.var_tv(v)),
                VK::Stack { n, .. } | VK::Heap { n, .. } => {
                    let stack = matches!(self.vars[v].kind, VK::Stack { .. });
                    for c in 0..*n {
                        if let Some(vals) = self.cells_all(v, c) {
                            let read = if stack {
                                Ex::SRead(v, Ix::Lit(c))
                            } else {
                                Ex::HRead(v, HIx::Const(c))
                            };
                            terms.push((read, vals));
                        }
                    }
                }
                _ => {}
            }
        }
        let mut accs = Vec::new();
        for _ in 0..2 {
            let c = loop {
                let c = self.src.u64() as u128 | 1 << 64 | 1;
                if c > 1 {
                    break c;
                }
            };
            let seed = self.src.below(1000) as u128 + 1;
            let mut acc = self.konst(lit(seed));
            for t in &terms {
                if self.src.chance(1, 4) {
                    continue;
                }
                let m = self.mul(acc, self.konst(lit(c)));
                let s = self.add(m, t.clone());
                let v = self.new_var(VK::Scalar, s.1, false);
                out.push(St::Let(v, s.0, Route::Direct));
                acc = self.var_tv(v);
            }
            let x = acc.1[0];
            out.push(St::AssertEq(acc.0.clone(), lit_of(x)));
            accs.push((acc, x));
        }
        let mut pi = [F128::ZERO; 2];
        for (slot, (acc, x)) in accs.into_iter().enumerate() {
            let e = {
                pi[slot] = x;
                acc.0
            };
            out.push(St::Publish(slot as u8, e));
        }
        self.public_input = pi;
        out
    }
}

enum ArgV {
    Val(Vec<F128>, bool),
    Const(Vec<u32>, u32),
    Heap(u32, Vec<usize>),
    Stack(u32, Vec<Vec<F128>>),
}

enum RetShape {
    Scalars(usize),
    Buf(u32),
}

enum RetV {
    Val(Vec<F128>),
    Buf(u32, Vec<Vec<F128>>),
}

/// A cell's sixteen message bytes, as a `keccak` reads them.
pub fn bytes(x: F128) -> [u8; 16] {
    let mut out = [0; 16];
    out[..8].copy_from_slice(&x.c0.to_le_bytes());
    out[8..].copy_from_slice(&x.c1.to_le_bytes());
    out
}

/// A digest as the two cells it occupies.
pub fn digest_cells(d: &[u8; 32]) -> Vec<F128> {
    let limb = |i: usize| u64::from_le_bytes(d[8 * i..8 * i + 8].try_into().unwrap());
    vec![F128::new(limb(0), limb(1)), F128::new(limb(2), limb(3))]
}
