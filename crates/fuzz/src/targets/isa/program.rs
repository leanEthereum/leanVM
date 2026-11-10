//! A generator of hand-assembled programs that it also runs in its head: every cell it writes has a value it knows,
//! so a run's final memory is checked against the generator, independently of the interpreter.
//!
//! A program is `main`'s code, then the bodies of the functions it calls (each in a frame of its own, entered by a
//! `DEREF` of the frame pointer and the return address and a `JUMP`, left by a `JUMP` back through them), then
//! padding, then the halt slot `g^(len - 1)`. Most instructions read only written cells and write only fresh ones, so
//! most programs run and prove; a few are wrong on purpose (a conflict, an unwritten read, a wild pointer, a word
//! outside `K` where a `JUMP` wants one) so the refusals are exercised too.

use crate::targets::kernels::reference as r;
use crate::{Finding, Source};
use leanvm_core::cpu::{DerefMode, Op, OutCells, Program};
use leanvm_core::keccak::{STATE_CELLS, cell_lanes};
use primitives::field::{F192, g_pow};
use std::collections::{BTreeMap, HashMap};

/// What a cell holds, as far as an instruction that reads it cares.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    /// In `K`: limbs 1 and 2 zero.
    K,
    /// Canonical, a `KECCAK` input: limb 2 zero.
    Canon,
    Ext,
}

pub fn kind_of(v: F192) -> Kind {
    if v.c1 == 0 && v.c2 == 0 {
        Kind::K
    } else if v.c2 == 0 {
        Kind::Canon
    } else {
        Kind::Ext
    }
}

/// Where a jump's target is resolved once the layout is known.
#[derive(Clone, Copy, Debug)]
enum Label {
    Halt,
    Callee(usize),
}

/// One frame being written: its base, its cells, the values the generator knows.
pub struct Frame {
    pub base: u32,
    pub code: Vec<Op>,
    next: u32,
    /// Frame-relative cells written, with their values.
    pub written: BTreeMap<u32, F192>,
    /// `(index in code, label)`: a `SET` whose immediate is `g^` the label's pc.
    fixups: Vec<(usize, Label)>,
    /// Whether the code may still fall through: false once it ends with a jump away.
    pub open: bool,
    /// Intentional mistakes made: the run is expected to fail.
    pub broken: bool,
}

impl Frame {
    fn new(base: u32, first_free: u32) -> Self {
        Self {
            base,
            code: Vec::new(),
            next: first_free,
            written: BTreeMap::new(),
            fixups: Vec::new(),
            open: true,
            broken: false,
        }
    }

    pub fn fresh(&mut self, n: u32) -> u32 {
        let c = self.next;
        self.next += n;
        c
    }

    fn set(&mut self, o: u32, k: F192) {
        self.code.push(Op::Set { o, k });
        self.written.insert(o, k);
    }

    fn pick(&self, src: &mut Source, want: Option<Kind>) -> Option<(u32, F192)> {
        let ok: Vec<(u32, F192)> = self
            .written
            .iter()
            .filter(|(_, v)| match want {
                None => true,
                Some(Kind::K) => kind_of(**v) == Kind::K,
                Some(Kind::Canon) => kind_of(**v) != Kind::Ext,
                Some(Kind::Ext) => true,
            })
            .map(|(&c, &v)| (c, v))
            .collect();
        (!ok.is_empty()).then(|| ok[src.below(ok.len())])
    }

    /// A value for a `SET`: often in `K`, often canonical, sometimes a full word.
    fn value(src: &mut Source) -> F192 {
        match src.below(6) {
            0 => F192::new(src.edgy_u64(), 0, 0),
            1 => F192::from(g_pow(src.below(64))),
            2 | 3 => F192::new(src.u64(), src.u64(), 0),
            4 => F192::ZERO,
            _ => src.f192(),
        }
    }

    /// One straight-line instruction over this frame's cells.
    pub fn step(&mut self, src: &mut Source) {
        if self.written.len() < 2 || src.chance(1, 6) {
            let o = self.fresh(1);
            let k = Self::value(src);
            self.set(o, k);
            return;
        }
        match src.below(10) {
            0..=2 => {
                let (a, va) = self.pick(src, None).unwrap();
                let (b, vb) = self.pick(src, None).unwrap();
                let c = self.fresh(1);
                self.code.push(Op::Xor { a, b, c });
                self.written.insert(c, va + vb);
            }
            3..=5 => {
                let (a, va) = self.pick(src, None).unwrap();
                let (b, vb) = self.pick(src, None).unwrap();
                let c = self.fresh(1);
                self.code.push(Op::Mul { a, b, c });
                self.written.insert(c, r::mul_e(va, vb));
            }
            6 => {
                // MUL back-solve: `c` and `a` written, `b` fresh, `b = c / a`.
                let (a, va) = self.pick(src, None).unwrap();
                let (c, vc) = self.pick(src, None).unwrap();
                let b = self.fresh(1);
                if a == c || va.is_zero() {
                    // A zero divisor is refused; `a == c` would read `b` in `a·b`, a fine run all the same.
                    let k = Self::value(src);
                    self.set(b, k);
                    return;
                }
                self.code.push(Op::Mul { a, b, c });
                self.written.insert(b, vc * va.inv());
            }
            7 | 8 => self.copy(src),
            _ => {
                if src.chance(1, 3) {
                    self.store_fp(src);
                } else {
                    self.keccak(src);
                }
            }
        }
    }

    /// `DEREF` in cell mode: copy a written cell into a fresh one through a pointer, either direction.
    fn copy(&mut self, src: &mut Source) {
        let (w, v) = self.pick(src, None).unwrap();
        let f = self.fresh(1);
        let ptr = self.fresh(1);
        if src.bool() {
            // a2 = written, a3 = fresh.
            let off = src.below(self.base as usize + w as usize + 1) as u32;
            let base = self.base + w - off;
            self.set(ptr, F192::from(g_pow(base as usize)));
            self.code.push(Op::Deref {
                o1: ptr,
                o2: off,
                o3: f,
                mode: DerefMode::Cell,
            });
        } else {
            // a2 = fresh, a3 = written.
            let off = src.below(self.base as usize + f as usize + 1) as u32;
            let base = self.base + f - off;
            self.set(ptr, F192::from(g_pow(base as usize)));
            self.code.push(Op::Deref {
                o1: ptr,
                o2: off,
                o3: w,
                mode: DerefMode::Cell,
            });
        }
        self.written.insert(f, v);
    }

    /// `DEREF` storing `g^fp` at a fresh cell of this frame, through a pointer to it.
    fn store_fp(&mut self, src: &mut Source) {
        let f = self.fresh(1);
        let ptr = self.fresh(1);
        let off = src.below(f as usize + 1) as u32;
        self.set(ptr, F192::from(g_pow((self.base + f - off) as usize)));
        let o3 = self.pick(src, None).map_or(0, |(c, _)| c);
        self.code.push(Op::Deref {
            o1: ptr,
            o2: off,
            o3,
            mode: DerefMode::Fp,
        });
        self.written.insert(f, F192::from(g_pow(self.base as usize)));
    }

    /// A `KECCAK` over canonical cells, its inputs set first when the frame has too few, its output checked against
    /// the reference permutation.
    fn keccak(&mut self, src: &mut Source) {
        // Thirteen consecutive canonical inputs: a fresh block of them, or a previous output.
        let block = self.fresh(STATE_CELLS as u32);
        for c in 0..STATE_CELLS as u32 {
            let v = match src.below(4) {
                0 => F192::ZERO,
                1 => F192::new(src.u64(), 0, 0),
                _ => F192::new(src.u64(), src.u64(), 0),
            };
            self.set(block + c, v);
        }
        let canon: Vec<(u32, F192)> = self
            .written
            .iter()
            .filter(|(_, v)| v.c2 == 0)
            .map(|(&c, &v)| (c, v))
            .collect();
        let pick = |src: &mut Source| canon[src.below(canon.len())].0;
        let m: [u32; 4] = if src.bool() {
            std::array::from_fn(|i| block + i as u32)
        } else {
            std::array::from_fn(|_| pick(src))
        };
        let run = |src: &mut Source, n: u32| -> u32 {
            // `n` consecutive canonical cells: from the block, or anywhere they happen to be.
            if src.chance(3, 4) {
                return block + src.below(STATE_CELLS - n as usize + 1) as u32;
            }
            let starts: Vec<u32> = canon
                .iter()
                .map(|&(c, _)| c)
                .filter(|&c| (0..n).all(|k| canon.iter().any(|&(d, _)| d == c + k)))
                .collect();
            if starts.is_empty() {
                block
            } else {
                starts[src.below(starts.len())]
            }
        };
        let (tail, cap) = (run(src, 4), run(src, 4));
        let b8 = pick(src);
        let out_cells = *src.pick(&[OutCells::One, OutCells::Two, OutCells::All]);
        let out = self.fresh(STATE_CELLS as u32);
        let (in_odd, out_odd) = (src.bool(), src.bool());
        self.code.push(Op::Keccak {
            m,
            tail,
            b8,
            cap,
            out,
            in_odd,
            out_odd,
            out_cells,
        });
        let input: Vec<F192> = m
            .iter()
            .copied()
            .chain((0..4).map(|k| tail + k))
            .chain([b8])
            .chain((0..4).map(|k| cap + k))
            .map(|c| self.written[&c])
            .collect();
        let mut lanes = [0u64; 25];
        for (c, &(lo, hi)) in cell_lanes(in_odd).iter().enumerate() {
            if let Some(l) = lo {
                lanes[l] = input[c].c0;
            }
            if let Some(h) = hi {
                lanes[h] = input[c].c1;
            }
        }
        r::keccak_f(&mut lanes);
        for (c, &(lo, hi)) in cell_lanes(out_odd).iter().enumerate().take(out_cells.cells()) {
            let v = F192::new(lo.map_or(0, |l| lanes[l]), hi.map_or(0, |h| lanes[h]), 0);
            self.written.insert(out + c as u32, v);
        }
    }

    /// One deliberate mistake: the run must fail cleanly.
    pub fn mistake(&mut self, src: &mut Source) {
        self.broken = true;
        let fresh = self.fresh(1);
        match src.below(7) {
            0 => {
                // A second, different value for a written cell.
                if let Some((c, v)) = self.pick(src, None) {
                    self.code.push(Op::Set { o: c, k: v + F192::ONE });
                }
            }
            1 => {
                // A read of a cell nothing wrote: refused by the prover, not the run.
                let c = self.fresh(1);
                self.code.push(Op::Xor { a: fresh, b: fresh, c });
                self.broken = false;
                self.written.insert(c, F192::ZERO);
                self.written.insert(fresh, F192::ZERO);
            }
            2 => {
                // A pointer that is no g-power in range.
                self.set(fresh, F192::new(src.u64() | 1 << 63, src.u64(), 0));
                let c = self.fresh(1);
                self.code.push(Op::Deref {
                    o1: fresh,
                    o2: 0,
                    o3: c,
                    mode: DerefMode::Cell,
                });
            }
            3 => {
                // A JUMP condition outside K.
                self.set(fresh, F192::new(1, 1 + src.u64() % 7, 0));
                self.code.push(Op::Jump {
                    oc: fresh,
                    od: fresh,
                    of: fresh,
                });
            }
            4 => {
                // A KECCAK reading a non-canonical cell.
                let block = self.fresh(STATE_CELLS as u32);
                for c in 0..STATE_CELLS as u32 {
                    self.set(block + c, F192::new(c as u64, 0, u64::from(c == 5)));
                }
                let out = self.fresh(STATE_CELLS as u32);
                self.code.push(Op::Keccak {
                    m: [block, block + 1, block + 2, block + 3],
                    tail: block + 4,
                    b8: block + 8,
                    cap: block + 9,
                    out,
                    in_odd: false,
                    out_odd: false,
                    out_cells: OutCells::All,
                });
            }
            5 => {
                // A back-solve through zero.
                self.set(fresh, F192::ZERO);
                let c = self.fresh(1);
                self.set(c, F192::ONE);
                let b = self.fresh(1);
                self.code.push(Op::Mul { a: fresh, b, c });
            }
            _ => {
                // A taken JUMP whose target is no pc.
                self.set(fresh, F192::ONE);
                let t = self.fresh(1);
                self.set(t, F192::new(src.u64() | 3, 0, 0));
                self.code.push(Op::Jump {
                    oc: fresh,
                    od: t,
                    of: fresh,
                });
            }
        }
    }
}

/// How a callee ends.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Exit {
    Return,
    /// A jump to the halt slot in main's frame: the machine halts there.
    HaltMain,
    /// A jump to the halt slot in the callee's own frame: `HaltOutsideMain`, unless the halt slot jumps away.
    HaltHere,
}

/// A whole program under construction.
pub struct Builder {
    pub main: Frame,
    /// The callees: their bodies, frame-relative, and the frame each call gives them.
    pub callees: Vec<Frame>,
    pub public_input: [F192; 2],
    /// Once a callee halts the machine: main's cells written by then, and the callees entered by then. Nothing
    /// after runs.
    halted: Option<(Vec<u32>, usize)>,
}

impl Builder {
    pub fn new(public_input: [F192; 2]) -> Self {
        let mut main = Frame::new(0, 2);
        main.written.insert(0, public_input[0]);
        main.written.insert(1, public_input[1]);
        Self {
            main,
            callees: Vec::new(),
            public_input,
            halted: None,
        }
    }

    /// A taken forward jump over `skip` garbage instructions in main.
    pub fn skip(&mut self, src: &mut Source, skip: usize) {
        let m = &mut self.main;
        let (cond, target, fp) = (m.fresh(1), m.fresh(1), m.fresh(1));
        m.set(cond, F192::new(src.u64().max(1), 0, 0));
        m.set(fp, F192::ONE);
        // The target is this jump's pc + 1 + skip: two SETs and the jump come first.
        let pc = m.code.len() as u32 + 1;
        m.set(target, F192::from(g_pow((pc + 1) as usize + skip)));
        m.code.push(Op::Jump {
            oc: cond,
            od: target,
            of: fp,
        });
        m.code.extend((0..skip).map(|_| garbage(src)));
    }

    /// An untaken `JUMP`: condition zero, the other two cells anything in `K`.
    pub fn untaken(&mut self, src: &mut Source) {
        let m = &mut self.main;
        let (cond, a, b) = (m.fresh(1), m.fresh(1), m.fresh(1));
        m.set(cond, F192::ZERO);
        m.set(a, F192::new(src.edgy_u64(), 0, 0));
        m.set(b, F192::new(src.edgy_u64(), 0, 0));
        m.code.push(Op::Jump { oc: cond, od: a, of: b });
    }

    /// A call: a new frame at `base`, its return address and frame pointer stored by `DEREF`, a `JUMP` in, the
    /// callee's body run there, a `JUMP` back. Or the callee jumps to the halt slot instead of returning: in main's
    /// frame, which halts the machine, or in its own, which the halt slot refuses.
    pub fn call(&mut self, src: &mut Source, base: u32, body: usize, exit: Exit) {
        let callee = self.callees.len();
        let m = &mut self.main;
        let (cond, target, ptr) = (m.fresh(1), m.fresh(1), m.fresh(1));
        m.set(cond, F192::ONE);
        m.fixups.push((m.code.len(), Label::Callee(callee)));
        // A placeholder nothing reads until the layout patches it.
        m.code.push(Op::Set {
            o: target,
            k: F192::ZERO,
        });
        m.set(ptr, F192::from(g_pow(base as usize)));
        let o3 = m.pick(src, None).map_or(0, |(c, _)| c);
        m.code.push(Op::Deref {
            o1: ptr,
            o2: 0,
            o3,
            mode: DerefMode::Fp,
        });
        let ret = m.code.len() as u32 + 2;
        m.code.push(Op::Deref {
            o1: ptr,
            o2: 1,
            o3,
            mode: DerefMode::Pc,
        });
        m.code.push(Op::Jump {
            oc: cond,
            od: target,
            of: ptr,
        });
        let mut f = Frame::new(base, 2);
        f.written.insert(0, F192::ONE);
        f.written.insert(1, F192::from(g_pow(ret as usize)));
        for _ in 0..body {
            f.step(src);
        }
        let c = f.fresh(1);
        f.set(c, F192::new(src.u64().max(1), 0, 0));
        match exit {
            Exit::Return => f.code.push(Op::Jump { oc: c, od: 1, of: 0 }),
            Exit::HaltMain | Exit::HaltHere => {
                let t = f.fresh(1);
                f.fixups.push((f.code.len(), Label::Halt));
                f.code.push(Op::Set { o: t, k: F192::ZERO });
                let of = if exit == Exit::HaltMain {
                    0
                } else {
                    let x = f.fresh(1);
                    f.set(x, F192::from(g_pow(base as usize)));
                    f.broken = true;
                    x
                };
                f.code.push(Op::Jump { oc: c, od: t, of });
            }
        }
        f.open = false;
        self.callees.push(f);
        if exit == Exit::HaltMain && self.halted.is_none() {
            let mut cells: Vec<u32> = self.main.written.keys().copied().collect();
            cells.push(target);
            self.halted = Some((cells, self.callees.len()));
        }
    }

    /// Main ends by jumping to the halt slot, past the callees and the padding, which may then be garbage.
    pub fn jump_to_halt(&mut self, src: &mut Source) {
        let m = &mut self.main;
        let (cond, target, fp) = (m.fresh(1), m.fresh(1), m.fresh(1));
        m.set(cond, F192::new(src.u64().max(1), 0, 0));
        m.set(fp, F192::ONE);
        m.fixups.push((m.code.len(), Label::Halt));
        // A placeholder nothing reads until the layout patches it.
        m.code.push(Op::Set {
            o: target,
            k: F192::ZERO,
        });
        m.code.push(Op::Jump {
            oc: cond,
            od: target,
            of: fp,
        });
        m.open = false;
    }

    /// Lay the program out: main, the callees, padding to a power of two at least `min_len`, the halt slot. Padding
    /// that main falls through executes, so it writes fresh cells; padding after a jump is garbage.
    pub fn finish(mut self, src: &mut Source, min_len: usize, halt: Op) -> Built {
        if !self.callees.is_empty() && self.main.open {
            self.jump_to_halt(src);
        }
        let body: usize = self.main.code.len() + self.callees.iter().map(|f| f.code.len()).sum::<usize>();
        let len = (body + 1).max(min_len).next_power_of_two();
        let mut starts = Vec::new();
        let mut at = self.main.code.len();
        for f in &self.callees {
            starts.push(at);
            at += f.code.len();
        }
        let resolve = |label: Label| -> F192 {
            F192::from(g_pow(match label {
                Label::Halt => len - 1,
                Label::Callee(i) => starts[i],
            }))
        };
        let patch = |frame: &mut Frame| {
            for &(i, label) in &frame.fixups {
                if let Op::Set { o, k } = &mut frame.code[i] {
                    *k = resolve(label);
                    frame.written.insert(*o, *k);
                }
            }
        };
        patch(&mut self.main);
        for f in &mut self.callees {
            patch(f);
        }
        let mut prog = self.main.code.clone();
        for f in &self.callees {
            prog.extend(f.code.iter().copied());
        }
        let falls = self.main.open;
        while prog.len() < len - 1 {
            if falls {
                let o = self.main.fresh(1);
                let k = Frame::value(src);
                prog.push(Op::Set { o, k });
                self.main.written.insert(o, k);
            } else {
                prog.push(garbage(src));
            }
        }
        prog.push(halt);
        let (main_cells, entered) = match &self.halted {
            Some((cells, n)) => (Some(cells), *n),
            None => (None, self.callees.len()),
        };
        let mut expect: HashMap<u32, F192> = self
            .main
            .written
            .iter()
            .filter(|(c, _)| main_cells.is_none_or(|cells| cells.contains(c)))
            .map(|(&c, &v)| (c, v))
            .collect();
        for f in &self.callees[..entered] {
            expect.extend(f.written.iter().map(|(&c, &v)| (f.base + c, v)));
        }
        let broken = self.main.broken || self.callees.iter().any(|f| f.broken);
        Built {
            prog,
            expect,
            broken,
            public_input: self.public_input,
            cells: self
                .main
                .next
                .max(self.callees.iter().map(|f| f.base + f.next).max().unwrap_or(0)),
        }
    }
}

/// A random instruction with random operands: dead code, or a sentinel.
pub fn garbage(src: &mut Source) -> Op {
    let o = |src: &mut Source| match src.below(4) {
        0 => src.u32(),
        1 => u32::MAX - src.below(16) as u32,
        _ => src.below(64) as u32,
    };
    match src.below(6) {
        0 => Op::Xor {
            a: o(src),
            b: o(src),
            c: o(src),
        },
        1 => Op::Mul {
            a: o(src),
            b: o(src),
            c: o(src),
        },
        2 => Op::Set {
            o: o(src),
            k: src.f192(),
        },
        3 => Op::Deref {
            o1: o(src),
            o2: o(src),
            o3: o(src),
            mode: *src.pick(&[DerefMode::Cell, DerefMode::Pc, DerefMode::Fp]),
        },
        4 => Op::Jump {
            oc: o(src),
            od: o(src),
            of: o(src),
        },
        _ => Op::Keccak {
            m: [o(src), o(src), o(src), o(src)],
            tail: o(src),
            b8: o(src),
            cap: o(src),
            out: o(src),
            in_odd: src.bool(),
            out_odd: src.bool(),
            out_cells: *src.pick(&[OutCells::One, OutCells::Two, OutCells::All]),
        },
    }
}

pub struct Built {
    pub prog: Vec<Op>,
    /// Every cell the generator wrote, absolute, with its value.
    pub expect: HashMap<u32, F192>,
    /// A deliberate mistake was made: the run should fail.
    pub broken: bool,
    pub public_input: [F192; 2],
    /// One past the highest cell the generator used.
    pub cells: u32,
}

impl Built {
    pub fn program(&self, main_frame: u32) -> Program {
        Program::assemble(self.prog.clone(), HashMap::new(), main_frame)
    }

    /// The final memory against the generator's values.
    pub fn check_memory(&self, mem: &leanvm_core::cpu::Memory, context: &str) -> Result<(), Finding> {
        let mut cells: Vec<(&u32, &F192)> = self.expect.iter().collect();
        cells.sort_by_key(|(c, _)| **c);
        for (&c, &want) in cells {
            let got = mem.word(c as usize);
            if got != want {
                return Err(Finding::high(
                    format!("{context}: the run's memory differs from the generator's"),
                    format!("cell {c}: got {got:?}, want {want:?}"),
                ));
            }
        }
        Ok(())
    }
}
