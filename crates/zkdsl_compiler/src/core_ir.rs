//! The core IR the front end expands a program to, the twin of `formal/lean_vm/LeanVM/Guest/Core.lean`: one
//! [`Fn`] per function the program runs, straight-line atoms over values, forward branches, `match`, calls and the
//! conditional call ending a loop helper. A value is a number with no meaning but its identity.
//!
//! [`render`] writes a program in the canonical text both front ends print (`lake exe guest-backend core-text`
//! in `formal/lean_vm`): every function in order, its values renumbered by first occurrence (the parameters first,
//! then the statements' values in the order `Stmt.valsList` lists them, which is the order printed), every field of
//! every atom and hint written out. Two programs print the same text exactly when they are equal up to a renaming
//! of each function's values, which changes no function's relation (`Fn.sem_renumber`).

use crate::field::F128;
use std::collections::HashMap;
use std::fmt::Write as _;

/// A value of a function.
pub type V = u32;

/// Where a hint writes: frame values, or `len` memory words from `ptr·g^off`.
#[derive(Clone, Debug, PartialEq)]
pub enum Dest {
    Stack(Vec<V>),
    Heap { ptr: V, off: u32, len: u32 },
}

/// A hint: values the prover writes, constrained by nothing.
#[derive(Clone, Debug, PartialEq)]
pub enum Hint {
    Witness {
        stream: String,
        dest: Dest,
    },
    Bits {
        value: V,
        start: u32,
        nbits: u32,
        dest: Dest,
    },
    BitsExp {
        value: V,
        nbits: u32,
        dest: Dest,
    },
    DigitsExp {
        value: V,
        nbits: u32,
        ndigits: u32,
        digit_bits: u32,
        start: u32,
        start_cell: Option<V>,
        dest: Dest,
    },
    WindowsExp {
        value: V,
        start: u32,
        width: u32,
        count: u32,
        dest: Dest,
    },
    Limbs {
        value: V,
        dest: Vec<V>,
    },
    Log2Ceil {
        bits: Dest,
        nbits: u32,
        floor: u32,
        dst: V,
    },
    Inverse {
        x: V,
        dst: V,
    },
    Alloc {
        dst: V,
        size: u32,
    },
    AllocDyn {
        dst: V,
        size: V,
    },
}

/// An atom: one or a few instructions on values.
#[derive(Clone, Debug, PartialEq)]
pub enum Atom {
    Const(V, F128),
    Add(V, V, V),
    Mul(V, V, V),
    /// `d = s`.
    Copy(V, V),
    /// The word at `p·g^off` is `d`.
    Load(V, V, u32),
    AssertEq(V, V),
    AssertNe(V, V, V),
    RangeCheck(V, V, V, V, V),
    AssertInK(V, V),
    Keccak {
        ins: Vec<V>,
        outs: Vec<V>,
        in_odd: bool,
        out_odd: bool,
    },
    FrameAddr(V, Vec<V>),
    Hint(Hint),
    Touch(V, V),
}

/// A statement.
#[derive(Clone, Debug, PartialEq)]
pub enum Stmt {
    Atom(Atom),
    /// `zero` runs at `c = 0`.
    Ite(V, Vec<Stmt>, Vec<Stmt>),
    Match(V, Vec<Vec<Stmt>>),
    Call(String, Vec<V>, Vec<V>),
    CallIf(V, String, Vec<V>),
    Dispatch(V, Vec<String>, Vec<V>, Vec<V>),
    Ret(Vec<V>),
}

/// A core function: its flattened parameters and its body.
#[derive(Clone, Debug, PartialEq)]
pub struct Fn {
    pub name: String,
    pub params: Vec<V>,
    pub body: Vec<Stmt>,
}

/// A program in the canonical text, one function after another.
pub fn render(program: &[Fn]) -> String {
    let mut out = String::new();
    for f in program {
        let mut p = Printer {
            out: &mut out,
            numbers: HashMap::new(),
        };
        let params = p.list(&f.params);
        writeln!(p.out, "def {} {params}", f.name).unwrap();
        p.block(&f.body, 1);
    }
    out
}

/// Prints one function, numbering each value at its first occurrence.
struct Printer<'a> {
    out: &'a mut String,
    numbers: HashMap<V, usize>,
}

impl Printer<'_> {
    fn v(&mut self, v: V) -> String {
        let next = self.numbers.len();
        format!("%{}", self.numbers.entry(v).or_insert(next))
    }

    fn list(&mut self, vs: &[V]) -> String {
        let items: Vec<String> = vs.iter().map(|&v| self.v(v)).collect();
        format!("[{}]", items.join(" "))
    }

    fn dest(&mut self, d: &Dest) -> String {
        match d {
            Dest::Stack(cells) => self.list(cells),
            Dest::Heap { ptr, off, len } => format!("heap({} {off} {len})", self.v(*ptr)),
        }
    }

    fn line(&mut self, depth: usize, text: &str) {
        writeln!(self.out, "{}{text}", "  ".repeat(depth)).unwrap();
    }

    fn block(&mut self, body: &[Stmt], depth: usize) {
        for s in body {
            self.stmt(s, depth);
        }
    }

    fn stmt(&mut self, s: &Stmt, depth: usize) {
        match s {
            Stmt::Atom(a) => {
                let text = self.atom(a);
                self.line(depth, &text);
            }
            Stmt::Ite(c, zero, nonzero) => {
                let c = self.v(*c);
                self.line(depth, &format!("if_zero {c}"));
                self.block(zero, depth + 1);
                self.line(depth, "else");
                self.block(nonzero, depth + 1);
                self.line(depth, "end");
            }
            Stmt::Match(x, arms) => {
                let x = self.v(*x);
                self.line(depth, &format!("match {x}"));
                for arm in arms {
                    self.line(depth, "arm");
                    self.block(arm, depth + 1);
                }
                self.line(depth, "end");
            }
            Stmt::Call(f, args, rets) => {
                let (args, rets) = (self.list(args), self.list(rets));
                self.line(depth, &format!("call {f} {args} {rets}"));
            }
            Stmt::CallIf(c, f, args) => {
                let c = self.v(*c);
                let args = self.list(args);
                self.line(depth, &format!("call_if {c} {f} {args}"));
            }
            Stmt::Dispatch(x, fs, args, rets) => {
                let x = self.v(*x);
                let (args, rets) = (self.list(args), self.list(rets));
                self.line(depth, &format!("dispatch {x} [{}] {args} {rets}", fs.join(" ")));
            }
            Stmt::Ret(vs) => {
                let vs = self.list(vs);
                self.line(depth, &format!("ret {vs}"));
            }
        }
    }

    fn atom(&mut self, a: &Atom) -> String {
        match a {
            Atom::Const(d, c) => format!("const {} {} {}", self.v(*d), c.c0, c.c1),
            Atom::Add(d, x, y) => format!("add {} {} {}", self.v(*d), self.v(*x), self.v(*y)),
            Atom::Mul(d, x, y) => format!("mul {} {} {}", self.v(*d), self.v(*x), self.v(*y)),
            Atom::Copy(d, s) => format!("copy {} {}", self.v(*d), self.v(*s)),
            Atom::Load(d, p, off) => format!("load {} {} {off}", self.v(*d), self.v(*p)),
            Atom::AssertEq(x, y) => format!("assert_eq {} {}", self.v(*x), self.v(*y)),
            Atom::AssertNe(x, inv, p) => format!("assert_ne {} {} {}", self.v(*x), self.v(*inv), self.v(*p)),
            Atom::RangeCheck(x, y, t1, t2, k) => format!(
                "range_check {} {} {} {} {}",
                self.v(*x),
                self.v(*y),
                self.v(*t1),
                self.v(*t2),
                self.v(*k)
            ),
            Atom::AssertInK(x, y) => format!("assert_in_k {} {}", self.v(*x), self.v(*y)),
            Atom::Keccak {
                ins,
                outs,
                in_odd,
                out_odd,
            } => format!(
                "keccak {} {} {} {}",
                self.list(ins),
                self.list(outs),
                u8::from(*in_odd),
                u8::from(*out_odd)
            ),
            Atom::FrameAddr(p, run) => format!("addr {} {}", self.v(*p), self.list(run)),
            Atom::Touch(t, p) => format!("touch {} {}", self.v(*t), self.v(*p)),
            Atom::Hint(h) => format!("hint {}", self.hint(h)),
        }
    }

    fn hint(&mut self, h: &Hint) -> String {
        match h {
            Hint::Witness { stream, dest } => format!("witness {stream} {}", self.dest(dest)),
            Hint::Bits {
                value,
                start,
                nbits,
                dest,
            } => {
                format!("bits {} {} {start} {nbits}", self.v(*value), self.dest(dest))
            }
            Hint::BitsExp { value, nbits, dest } => format!("bits_exp {} {} {nbits}", self.v(*value), self.dest(dest)),
            Hint::DigitsExp {
                value,
                nbits,
                ndigits,
                digit_bits,
                start,
                start_cell,
                dest,
            } => {
                let value = self.v(*value);
                let cell = start_cell.map_or_else(|| "-".to_string(), |c| self.v(c));
                format!(
                    "digits_exp {value} {cell} {} {nbits} {ndigits} {digit_bits} {start}",
                    self.dest(dest)
                )
            }
            Hint::WindowsExp {
                value,
                start,
                width,
                count,
                dest,
            } => {
                format!(
                    "windows_exp {} {} {start} {width} {count}",
                    self.v(*value),
                    self.dest(dest)
                )
            }
            Hint::Limbs { value, dest } => format!("limbs {} {}", self.v(*value), self.list(dest)),
            Hint::Log2Ceil {
                bits,
                nbits,
                floor,
                dst,
            } => {
                format!("log2_ceil {} {} {nbits} {floor}", self.dest(bits), self.v(*dst))
            }
            Hint::Inverse { x, dst } => format!("inverse {} {}", self.v(*x), self.v(*dst)),
            Hint::Alloc { dst, size } => format!("alloc {} {size}", self.v(*dst)),
            Hint::AllocDyn { dst, size } => format!("alloc_dyn {} {}", self.v(*dst), self.v(*size)),
        }
    }
}
