//! Spelling a generated [`Prog`] as zkDSL source. Every choice here preserves meaning: whether a function is
//! `@inline`, whether a loop is unrolled, how a binding travels (directly, through a `StackBuf`, a `HeapBuf`, a list,
//! a function return), how a constant is written, `x * 1` and `x + 0`, names and indentation. Two styles of one
//! program must publish the same public input.

use super::ast::*;
use crate::source::Rng;
use std::collections::HashMap;
use std::fmt::Write;

/// How a program is spelled: per-choice probabilities, out of 16, and the cosmetic choices.
#[derive(Clone, Debug)]
pub struct Style {
    pub inline: u64,
    pub unroll: u64,
    pub konst: u64,
    pub route: u64,
    pub wrap: u64,
    pub litform: u64,
    pub comments: u64,
    pub prefix: &'static str,
    pub indent: &'static str,
    pub import: bool,
}

const PREFIXES: [&str; 6] = ["v", "x", "val_", "w", "tmp_v", "q_"];
const INDENTS: [&str; 5] = ["    ", "  ", " ", "\t", "        "];

impl Style {
    /// The plainest spelling: what the generator means, written once.
    pub fn plain() -> Self {
        Self {
            inline: 0,
            unroll: 0,
            konst: 16,
            route: 0,
            wrap: 0,
            litform: 0,
            comments: 0,
            prefix: "v",
            indent: "    ",
            import: false,
        }
    }

    pub fn random(rng: &mut Rng) -> Self {
        let p = |rng: &mut Rng| match rng.below(4) {
            0 => 0,
            1 => 16,
            _ => rng.below(17),
        };
        Self {
            inline: p(rng),
            unroll: p(rng),
            konst: p(rng),
            route: p(rng) / 2,
            wrap: p(rng) / 3,
            litform: p(rng) / 2,
            comments: rng.below(3),
            prefix: PREFIXES[rng.below(PREFIXES.len() as u64) as usize],
            indent: INDENTS[rng.below(INDENTS.len() as u64) as usize],
            import: rng.below(2) == 0,
        }
    }

    /// What a style chose, for a note: the knobs that change code, not names or whitespace.
    pub fn knobs(&self) -> String {
        let b = |p: u64| match p {
            0 => "0",
            16 => "1",
            _ => "~",
        };
        format!(
            "inline{} unroll{} konst{} route{} wrap{} lit{}",
            b(self.inline),
            b(self.unroll),
            b(self.konst),
            b(self.route),
            b(self.wrap),
            b(self.litform)
        )
    }
}

struct Printer<'a> {
    prog: &'a Prog,
    style: Style,
    rng: Rng,
    out: String,
    level: usize,
    inline: Vec<bool>,
    konst: Vec<bool>,
    unroll: Vec<bool>,
    helpers: Vec<String>,
    /// The name of the `match` arm parameter being printed.
    j: Option<String>,
    published: Option<String>,
    used: HashMap<&'static str, usize>,
}

pub fn print(prog: &Prog, style: &Style, seed: u64) -> String {
    let mut rng = Rng::new(seed);
    let chance = |p: u64, rng: &mut Rng| rng.below(16) < p;
    let inline: Vec<bool> = prog
        .funs
        .iter()
        .enumerate()
        .map(|(i, f)| {
            i != 0
                && match f.inline {
                    Mode::Always => true,
                    Mode::Never => false,
                    Mode::Either => chance(style.inline, &mut rng),
                }
        })
        .collect();
    let konst: Vec<bool> = prog
        .funs
        .iter()
        .map(|f| match f.konst {
            Mode::Always => true,
            Mode::Never => false,
            Mode::Either => chance(style.konst, &mut rng),
        })
        .collect();
    let unroll: Vec<bool> = prog
        .loops
        .iter()
        .map(|l| match l.form {
            Form::Unroll => true,
            Form::MulRange => false,
            Form::Either => inline[l.fun] || chance(style.unroll, &mut rng),
        })
        .collect();
    let mut p = Printer {
        prog,
        style: style.clone(),
        rng,
        out: String::new(),
        level: 0,
        inline,
        konst,
        unroll,
        helpers: Vec::new(),
        j: None,
        published: None,
        used: HashMap::new(),
    };
    p.program();
    p.out
}

impl Printer<'_> {
    fn chance(&mut self, p: u64) -> bool {
        self.rng.below(16) < p
    }

    fn pick(&mut self, n: usize) -> usize {
        self.rng.below(n as u64) as usize
    }

    fn line(&mut self, text: &str) {
        for _ in 0..self.level {
            self.out.push_str(self.style.indent);
        }
        self.out.push_str(text);
        if self.style.comments > 0 && self.rng.below(12) < self.style.comments {
            self.out.push_str("  # note: \"quoted\", [brackets] and # hashes");
        }
        self.out.push('\n');
        if self.style.comments > 1 && self.rng.below(10) == 0 {
            self.out.push('\n');
        }
    }

    fn fresh(&mut self, kind: &'static str) -> String {
        let n = self.used.entry(kind).or_insert(0);
        *n += 1;
        format!("{kind}{n}")
    }

    fn name(&self, v: V) -> String {
        format!("{}{v}", self.style.prefix)
    }

    fn fname(&self, f: FnId) -> String {
        if f == 0 { "main".into() } else { format!("fn_{f}") }
    }

    fn is_unrolled_counter(&self, v: V) -> bool {
        self.prog.counter_of.get(&v).is_some_and(|&l| self.unroll[l])
    }

    fn program(&mut self) {
        if self.style.import {
            self.out.push_str("from snark_lib import *\n\n");
        }
        for (i, arr) in self.prog.arrays.iter().enumerate() {
            let items: Vec<String> = arr.iter().map(|x| x.to_string()).collect();
            let _ = writeln!(self.out, "TBL{i} = [{}]", items.join(", "));
        }
        self.out.push('\n');
        // `main` first or last: definition order is free.
        let main_last = self.rng.below(2) == 0;
        let order: Vec<FnId> = if main_last {
            (1..self.prog.funs.len()).chain([0]).collect()
        } else {
            (0..self.prog.funs.len()).collect()
        };
        for f in order {
            self.function(f);
        }
        for h in std::mem::take(&mut self.helpers) {
            self.out.push_str(&h);
        }
    }

    fn function(&mut self, f: FnId) {
        let fun = &self.prog.funs[f];
        if self.inline[f] {
            self.out.push_str("@inline\n");
        }
        let params: Vec<String> = fun
            .params
            .iter()
            .map(|&(v, k)| match k {
                PK::Scalar | PK::Heap => self.name(v),
                PK::Const if self.konst[f] => format!("{}: Const", self.name(v)),
                PK::Const => self.name(v),
                PK::Stack(n) => format!("{}: StackBuf({n})", self.name(v)),
            })
            .collect();
        let _ = writeln!(self.out, "def {}({}):", self.fname(f), params.join(", "));
        self.level = 1;
        let body = &self.prog.funs[f].body;
        self.block(body);
        if f == 0 || body.is_empty() {
            self.line("return");
        }
        self.level = 0;
        self.out.push('\n');
    }

    fn block(&mut self, body: &[St]) {
        if body.is_empty() {
            self.line("assert GEN == GEN");
        }
        for st in body {
            self.stmt(st);
        }
    }

    fn stmt(&mut self, st: &St) {
        match st {
            St::Let(v, e, route) => {
                let name = self.name(*v);
                let value = self.ex(e, true);
                if *route == Route::Any && self.chance(self.style.route) {
                    self.routed(&name, &value);
                } else {
                    self.line(&format!("{name} = {value}"));
                }
            }
            St::LetHint(v, s) => {
                let name = self.name(*v);
                if self.chance(self.style.route) {
                    let t = self.fresh("tmp");
                    self.line(&format!("{t} = StackBuf(1)"));
                    self.line(&format!("hint_witness({t}, \"{s}\")"));
                    self.line(&format!("{name} = {t}[0]"));
                } else {
                    self.line(&format!("{name} = hint_witness(\"{s}\")"));
                }
            }
            St::Hint(run, s) => {
                let r = self.run(run);
                self.line(&format!("hint_witness({r}, \"{s}\")"));
            }
            St::Stack(v, n) => {
                let name = self.name(*v);
                self.line(&format!("{name} = StackBuf({n})"));
            }
            St::Heap(v, n) => {
                let name = self.name(*v);
                self.line(&format!("{name} = HeapBuf({n})"));
            }
            St::HeapDyn(v, e) => {
                let name = self.name(*v);
                let e = self.ex(e, false);
                self.line(&format!("{name} = HeapBuf({e})"));
            }
            St::List(v, items) => {
                let name = self.name(*v);
                let items: Vec<String> = items.iter().map(|e| self.ex(e, true)).collect();
                self.line(&format!("{name} = [{}]", items.join(", ")));
            }
            St::Store(place, e) => {
                let value = self.ex(e, true);
                let place = self.place(place);
                self.line(&format!("{place} = {value}"));
            }
            St::AssertEq(a, b) => {
                let (a, b) = (self.ex(a, true), self.ex(b, true));
                self.line(&format!("assert {a} == {b}"));
            }
            St::AssertNe(a, b) => {
                let (a, b) = (self.ex(a, true), self.ex(b, true));
                self.line(&format!("assert {a} != {b}"));
            }
            St::AssertLt(e, k) => {
                let e = self.ex(e, true);
                let bound = if self.rng.below(2) == 0 {
                    k.to_string()
                } else {
                    format!("log(GEN ** {k})")
                };
                self.line(&format!("assert log({e}) < {bound}"));
            }
            St::AssertLtRt(e, b) => {
                let (e, b) = (self.ex(e, true), self.ex(b, false));
                self.line(&format!("assert log({e}) < log({b})"));
            }
            St::AssertInK(a, b) => {
                let (a, b) = (self.ex(a, true), self.ex(b, true));
                self.line(&format!("assert_in_k({a}, {b})"));
            }
            St::If {
                ne,
                lhs,
                rhs,
                then,
                els,
            } => {
                let (l, r) = (self.ex(lhs, false), self.ex(rhs, false));
                let (op, then, els) = if then.is_empty() && !els.is_empty() {
                    (if *ne { "==" } else { "!=" }, els, then)
                } else {
                    (if *ne { "!=" } else { "==" }, then, els)
                };
                let (l, r) = if self.rng.below(2) == 0 { (l, r) } else { (r, l) };
                self.line(&format!("if {l} {op} {r}:"));
                self.nested(then);
                if !els.is_empty() {
                    self.line("else:");
                    self.nested(els);
                }
            }
            St::IfConst { k, m, r, then, els } => {
                let k = self.name(*k);
                self.line(&format!("if const({k} % {m} == {r}):"));
                self.nested(then);
                if !els.is_empty() {
                    self.line("else:");
                    self.nested(els);
                }
            }
            St::Match { targets, x, segs } => {
                let targets: Vec<String> = targets
                    .iter()
                    .map(|t| match t {
                        Target::Var(v) => self.name(*v),
                        Target::Cell(v, c) => format!("{}[{c}]", self.name(*v)),
                    })
                    .collect();
                let x = self.ex(x, true);
                let mut parts = Vec::new();
                for seg in segs {
                    let j = self.fresh("j");
                    let saved = self.j.replace(j.clone());
                    let arm = match &seg.arm {
                        Arm::Ex(e) => self.ex(e, true),
                        Arm::Call(c) => self.call(c),
                    };
                    self.j = saved;
                    parts.push(format!("range({}, {}), lambda {j}: {arm}", seg.lo, seg.hi));
                }
                self.line(&format!(
                    "{} = match(log({x}), {})",
                    targets.join(", "),
                    parts.join(", ")
                ));
            }
            St::Call(rets, call) => {
                let c = self.call(call);
                if rets.is_empty() {
                    self.line(&c);
                } else {
                    let names: Vec<String> = rets.iter().map(|&v| self.name(v)).collect();
                    self.line(&format!("{} = {c}", names.join(", ")));
                }
            }
            St::Loop(l) => self.lp(*l),
            St::Keccak { a, b, tail, out, len } => {
                let mut s = format!("keccak({}, {}, {}", self.run(a), self.run(b), self.run(out));
                if let Some(t) = tail {
                    let _ = write!(s, ", tail={}", self.run(t));
                }
                if let Some(len) = len {
                    let _ = write!(s, ", len={len}");
                }
                s.push(')');
                self.line(&s);
            }
            St::KeccakCells { cells, out, len } => {
                let cells = match cells {
                    Run::Whole(v) if self.chance(self.style.route.max(4)) => {
                        let n = self.prog.stack_sizes[v];
                        let k = self.fresh("k");
                        format!("[{}[{k}] for {k} in unroll(0, {n})]", self.name(*v))
                    }
                    other => self.run(other),
                };
                let mut s = format!("keccak_cells({cells}, {}", self.run(out));
                if let Some(len) = len {
                    let _ = write!(s, ", len={len}");
                }
                s.push(')');
                self.line(&s);
            }
            St::Publish(slot, e) => {
                let p = match self.published.clone() {
                    Some(p) => p,
                    None => {
                        let p = self.fresh("pub");
                        let one = if self.rng.below(2) == 0 { "GEN ** 0" } else { "1" };
                        self.line(&format!("{p} = {one}"));
                        self.published = Some(p.clone());
                        p
                    }
                };
                let e = self.ex(e, true);
                let idx = if *slot == 0 { "1" } else { "GEN" };
                self.line(&format!("{p}[{idx}] = {e}"));
            }
            St::Return(items) => {
                let items: Vec<String> = items
                    .iter()
                    .map(|r| match r {
                        Ret::Val(e) => self.ex(e, true),
                        Ret::Buf(v) => self.name(*v),
                    })
                    .collect();
                if items.is_empty() {
                    self.line("return");
                } else {
                    self.line(&format!("return {}", items.join(", ")));
                }
            }
        }
    }

    fn nested(&mut self, body: &[St]) {
        self.level += 1;
        self.block(body);
        self.level -= 1;
    }

    /// `name = value`, the value travelling through a cell or a call on the way.
    fn routed(&mut self, name: &str, value: &str) {
        match self.pick(5) {
            0 => {
                let t = self.fresh("tmp");
                self.line(&format!("{t} = StackBuf(1)"));
                self.line(&format!("{t}[0] = {value}"));
                self.line(&format!("{name} = {t}[0]"));
            }
            1 => {
                let t = self.fresh("tmp");
                self.line(&format!("{t} = HeapBuf(1)"));
                self.line(&format!("{t}[1] = {value}"));
                self.line(&format!("{name} = {t}[1]"));
            }
            2 => {
                let t = self.fresh("tmp");
                self.line(&format!("{t} = [{value}]"));
                self.line(&format!("{name} = {t}[0]"));
            }
            3 => {
                let f = self.fresh("ident");
                let inline = if self.rng.below(2) == 0 { "@inline\n" } else { "" };
                self.helpers
                    .push(format!("{inline}def {f}(a):\n{}return a\n\n", self.style.indent));
                self.line(&format!("{name} = {f}({value})"));
            }
            _ => {
                let f = self.fresh("pair");
                let inline = if self.rng.below(2) == 0 { "@inline\n" } else { "" };
                let i = self.style.indent;
                self.helpers
                    .push(format!("{inline}def {f}(a):\n{i}return a, a * GEN\n\n"));
                let other = self.fresh("tmp");
                self.line(&format!("{name}, {other} = {f}({value})"));
            }
        }
    }

    fn call(&mut self, c: &Call) -> String {
        let args: Vec<String> = c
            .args
            .iter()
            .map(|a| match a {
                Arg::Val(e) => self.ex(e, true),
                Arg::Buf(v) => self.name(*v),
                Arg::Int(k) => k.to_string(),
                Arg::J => self.j.clone().expect("inside a match arm"),
            })
            .collect();
        format!("{}({})", self.fname(c.f), args.join(", "))
    }

    fn lp(&mut self, l: usize) {
        let lp = &self.prog.loops[l];
        let name = self.name(lp.var);
        if self.unroll[l] {
            let Hi::Const(hi) = lp.hi else {
                unreachable!("a runtime bound is never unrolled")
            };
            self.line(&format!("for {name} in unroll({}, {hi}):", lp.lo));
        } else {
            let start = match lp.lo {
                0 if self.rng.below(2) == 0 => "1".to_string(),
                1 if self.rng.below(2) == 0 => "GEN".to_string(),
                k => format!("GEN ** {k}"),
            };
            let stop = match &lp.hi {
                Hi::Const(h) => format!("GEN ** {h}"),
                Hi::Rt(e) => self.ex(e, false),
            };
            self.line(&format!("for {name} in mul_range({start}, {stop}):"));
        }
        let body = self.prog.loops[l].body.clone();
        self.nested(&body);
    }

    fn ix(&self, ix: &Ix) -> String {
        let plus = |base: String, off: u32| if off == 0 { base } else { format!("{base} + {off}") };
        match *ix {
            Ix::Lit(c) => c.to_string(),
            Ix::Counter(v, off) | Ix::Param(v, off) => plus(self.name(v), off),
            Ix::J(off) => plus(self.j.clone().expect("inside a match arm"), off),
        }
    }

    fn hix(&mut self, h: &HIx) -> String {
        match *h {
            HIx::Const(0) if self.rng.below(2) == 0 => "1".into(),
            HIx::Const(1) if self.rng.below(2) == 0 => "GEN".into(),
            HIx::Const(k) => format!("GEN ** {k}"),
            HIx::Rt(v, off) if self.is_unrolled_counter(v) => {
                let name = self.name(v);
                if off == 0 {
                    format!("GEN ** {name}")
                } else {
                    format!("GEN ** ({name} + {off})")
                }
            }
            HIx::Rt(v, 0) => self.name(v),
            HIx::Rt(v, 1) if self.rng.below(2) == 0 => format!("{} * GEN", self.name(v)),
            HIx::Rt(v, off) => format!("{} * GEN ** {off}", self.name(v)),
        }
    }

    fn place(&mut self, p: &Place) -> String {
        match p {
            Place::Stack(v, ix) => format!("{}[{}]", self.name(*v), self.ix(ix)),
            Place::Heap(v, h) => {
                let h = self.hix(h);
                format!("{}[{h}]", self.name(*v))
            }
        }
    }

    fn run(&mut self, r: &Run) -> String {
        match r {
            Run::Whole(v) => self.name(*v),
            Run::Slice(v, lo, hi) => format!("{}[{lo}:{hi}]", self.name(*v)),
            // An unrolled counter is an integer, which as a slice start names the same cells.
            Run::HeapRt(v, x, len) => {
                let x = self.name(*x);
                format!("{}[{x}:{x} + {len}]", self.name(*v))
            }
            Run::List(items) => {
                let items: Vec<String> = items.iter().map(|e| self.ex(e, true)).collect();
                format!("[{}]", items.join(", "))
            }
        }
    }

    /// An expression; `free` says whether its spelling may change (not an `if` operand, whose integer reading a
    /// condition folds on).
    fn ex(&mut self, e: &Ex, free: bool) -> String {
        let s = self.ex_inner(e, free);
        if free && !matches!(e, Ex::Zero) && self.chance(self.style.wrap) {
            return match self.pick(6) {
                0 => format!("({s} * 1)"),
                1 => format!("({s} + 0)"),
                2 => format!("(1 * {s})"),
                3 => format!("(0 + {s})"),
                4 => {
                    let c = (self.rng.next_u64() | 1) as u128;
                    format!("(({s} * {c}) / {c})")
                }
                _ => {
                    let c = self.rng.next_u64() as u128;
                    format!("({s} + {c} + {c})")
                }
            };
        }
        s
    }

    fn ex_inner(&mut self, e: &Ex, free: bool) -> String {
        match e {
            Ex::Lit(n) => self.lit(*n, free),
            Ex::Zero => "0".into(),
            Ex::Fe(x) => (x.c0 as u128 | (x.c1 as u128) << 64).to_string(),
            Ex::GPow(k) => match k {
                0 if free && self.chance(self.style.litform) => "1".into(),
                1 if free && self.chance(self.style.litform) => "GEN".into(),
                k if *k >= 2 && free && self.chance(self.style.litform) => {
                    let a = self.rng.below(*k);
                    format!("((GEN ** {a}) * (GEN ** {}))", k - a)
                }
                k => format!("(GEN ** {k})"),
            },
            Ex::Var(v) => {
                if self.is_unrolled_counter(*v) {
                    format!("(GEN ** {})", self.name(*v))
                } else {
                    self.name(*v)
                }
            }
            Ex::Add(a, b) => format!("({} + {})", self.ex(a, free), self.ex(b, free)),
            Ex::Mul(a, b) => format!("({} * {})", self.ex(a, free), self.ex(b, free)),
            Ex::Div(a, b) => format!("({} / {})", self.ex(a, free), self.ex(b, free)),
            Ex::Pow(a, k) => format!("(({}) ** {k})", self.ex(a, free)),
            Ex::ConstInt(text) => format!("const({text})"),
            Ex::Arr(a, ix) => format!("TBL{a}[{}]", self.ix(ix)),
            Ex::SRead(v, ix) => format!("{}[{}]", self.name(*v), self.ix(ix)),
            Ex::HRead(v, h) => {
                let h = self.hix(h);
                format!("{}[{h}]", self.name(*v))
            }
            Ex::J => self.j.clone().expect("inside a match arm"),
            Ex::JPow(off) => {
                let j = self.j.clone().expect("inside a match arm");
                if *off == 0 {
                    format!("(GEN ** {j})")
                } else {
                    format!("(GEN ** ({j} + {off}))")
                }
            }
            Ex::KPow(k, off) => {
                let k = self.name(*k);
                if *off == 0 {
                    format!("(GEN ** {k})")
                } else {
                    format!("(GEN ** ({k} + {off}))")
                }
            }
            Ex::Call(c) => self.call(c),
        }
    }

    /// An integer literal in a value position, where `+` is XOR: as itself, as `f192(...)`, as two literals
    /// XORed, as a power of `GEN`, or as an integer `const(...)` sum.
    fn lit(&mut self, n: u128, free: bool) -> String {
        if !free || !self.chance(self.style.litform) {
            return n.to_string();
        }
        match self.pick(5) {
            0 => format!("f192({}, {}, 0)", n as u64, (n >> 64) as u64),
            1 => {
                let a = (self.rng.next_u64() as u128) << 64 | self.rng.next_u64() as u128;
                format!("({} + {})", a, a ^ n)
            }
            2 if n.is_power_of_two() && n < 1 << 64 => format!("(GEN ** {})", n.trailing_zeros()),
            3 if n < 1 << 120 => {
                let a = (self.rng.next_u64() as u128) % (n + 1);
                format!("const({} + {})", a, n - a)
            }
            _ => n.to_string(),
        }
    }
}
