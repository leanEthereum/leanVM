//! A compiled program as bytes, for a prover that does not compile its program: little-endian integers, a tag byte
//! per variant, a length before each list and string.

use crate::{BitsDest, CompiledProgram, DerefMode, Op, OutCells, Program, RHint};
use std::collections::BTreeMap;
use verifier::{E, K, MAX_LOG_BYTECODE};

impl Program {
    /// The compiled program, which [`Self::from_bytes`] reads back.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut w = Vec::new();
        u32s(&mut w, &[self.main_frame, len(self.prog.len())]);
        for op in &self.prog {
            write_op(&mut w, op);
        }
        u32s(&mut w, &[len(self.hints.len())]);
        for (&pc, hints) in &self.hints {
            u32s(&mut w, &[pc, len(hints.len())]);
            for hint in hints {
                write_hint(&mut w, hint);
            }
        }
        u32s(&mut w, &[len(self.fn_ranges.len())]);
        for (name, entry, size) in &self.fn_ranges {
            string(&mut w, name);
            u32s(&mut w, &[*entry, *size]);
        }
        u32s(&mut w, &[len(self.src_lines.len())]);
        u32s(&mut w, &self.src_lines);
        w
    }

    /// The program `bytes` encode, `None` unless they are exactly one encoding of a program a power of two long, at
    /// most `2^MAX_LOG_BYTECODE`, its hints at increasing pcs inside it.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let mut r = Reader(bytes);
        let main_frame = r.u32()?;
        let prog: Vec<Op> = (0..r.u32()?).map(|_| r.op()).collect::<Option<_>>()?;
        let hints: Vec<(u32, Vec<RHint>)> = (0..r.u32()?)
            .map(|_| Some((r.u32()?, (0..r.u32()?).map(|_| r.hint()).collect::<Option<_>>()?)))
            .collect::<Option<_>>()?;
        let fn_ranges = (0..r.u32()?)
            .map(|_| Some((r.string()?, r.u32()?, r.u32()?)))
            .collect::<Option<_>>()?;
        let src_lines = (0..r.u32()?).map(|_| r.u32()).collect::<Option<_>>()?;
        let n = prog.len();
        let pcs_in_order =
            hints.is_sorted_by(|(a, _), (b, _)| a < b) && hints.last().is_none_or(|(pc, _)| (*pc as usize) < n);
        (r.0.is_empty() && pcs_in_order && n.is_power_of_two() && n <= 1 << MAX_LOG_BYTECODE).then(|| {
            // Inserted one by one: collecting would sort them first.
            let mut by_pc = BTreeMap::new();
            for (pc, h) in hints {
                by_pc.insert(pc, h);
            }
            Self::from(CompiledProgram {
                prog,
                hints: by_pc,
                main_frame,
                fn_ranges,
                src_lines,
            })
        })
    }
}

fn len(n: usize) -> u32 {
    u32::try_from(n).expect("a length below 2^32")
}

fn u32s(w: &mut Vec<u8>, xs: &[u32]) {
    for x in xs {
        w.extend(x.to_le_bytes());
    }
}

fn string(w: &mut Vec<u8>, s: &str) {
    u32s(w, &[len(s.len())]);
    w.extend(s.as_bytes());
}

fn dest(w: &mut Vec<u8>, d: BitsDest) {
    let (tag, o) = match d {
        BitsDest::Stack(o) => (0, o),
        BitsDest::Heap(o) => (1, o),
    };
    w.push(tag);
    u32s(w, &[o]);
}

fn write_op(w: &mut Vec<u8>, op: &Op) {
    match *op {
        Op::Xor { a, b, c } => {
            w.push(0);
            u32s(w, &[a, b, c]);
        }
        Op::Mul { a, b, c } => {
            w.push(1);
            u32s(w, &[a, b, c]);
        }
        Op::Set { o, k } => {
            w.push(2);
            u32s(w, &[o]);
            w.extend(k.c0.to_le_bytes().into_iter().chain(k.c1.to_le_bytes()));
        }
        Op::Deref { o1, o2, o3, mode } => {
            w.push(3);
            u32s(w, &[o1, o2, o3]);
            w.push(mode as u8);
        }
        Op::Jump { oc, od, of } => {
            w.push(4);
            u32s(w, &[oc, od, of]);
        }
        Op::Keccak {
            m,
            tail,
            b8,
            cap,
            out,
            in_odd,
            out_odd,
            out_cells,
        } => {
            w.push(5);
            u32s(w, &m);
            u32s(w, &[tail, b8, cap, out]);
            w.extend([u8::from(in_odd), u8::from(out_odd), out_cells as u8]);
        }
    }
}

fn write_hint(w: &mut Vec<u8>, hint: &RHint) {
    match hint {
        RHint::FrameAddress { offset } => {
            w.push(0);
            u32s(w, &[*offset]);
        }
        RHint::AllocFrames {
            ptr,
            size,
            end,
            start_inverse,
            tail,
        } => {
            w.push(1);
            u32s(w, &[*ptr, *size, *end]);
            w.extend(start_inverse.0.to_le_bytes());
            u32s(w, &[*tail]);
        }
        RHint::Alloc { ptr, size } => {
            w.push(2);
            u32s(w, &[*ptr, *size]);
        }
        RHint::AllocDyn { ptr, size } => {
            w.push(3);
            u32s(w, &[*ptr, *size]);
        }
        RHint::AllocArm { ptr, sel, sizes } => {
            w.push(4);
            u32s(w, &[*ptr, *sel, len(sizes.len())]);
            u32s(w, sizes);
        }
        RHint::CellAddress { ptr, cell } => {
            w.push(5);
            u32s(w, &[*ptr, *cell]);
        }
        RHint::WitnessStack { name, base, len } => {
            w.push(6);
            string(w, name);
            u32s(w, &[*base, *len]);
        }
        RHint::WitnessHeap { name, ptr, lo, len } => {
            w.push(7);
            string(w, name);
            u32s(w, &[*ptr, *lo, *len]);
        }
        RHint::Log2Ceil {
            bits,
            dst,
            nbits,
            floor,
        } => {
            w.push(8);
            dest(w, *bits);
            u32s(w, &[*dst, *nbits, *floor]);
        }
        RHint::BitDecompose { value, bits, nbits } => {
            w.push(9);
            u32s(w, &[*value]);
            dest(w, *bits);
            u32s(w, &[*nbits]);
        }
        RHint::BitDecomposeExp { value, bits, nbits } => {
            w.push(10);
            u32s(w, &[*value]);
            dest(w, *bits);
            u32s(w, &[*nbits]);
        }
        RHint::DigitDecomposeExp {
            value,
            dst,
            nbits,
            ndigits,
            digit_bits,
            start,
            start_cell,
        } => {
            w.push(11);
            u32s(w, &[*value]);
            dest(w, *dst);
            u32s(w, &[*nbits, *ndigits, *digit_bits, *start]);
            w.push(u8::from(start_cell.is_some()));
            u32s(w, &[start_cell.unwrap_or(0)]);
        }
        RHint::WindowsExp {
            value,
            dest: d,
            at,
            start,
            width,
            count,
        } => {
            w.push(12);
            u32s(w, &[*value]);
            dest(w, *d);
            u32s(w, &[*at, *start, *width, *count]);
        }
        RHint::FieldLimbs { value, base, len } => {
            w.push(13);
            u32s(w, &[*value, *base, *len]);
        }
        RHint::Inverse { value, dst } => {
            w.push(14);
            u32s(w, &[*value, *dst]);
        }
        RHint::Print { label, cell } => {
            w.push(15);
            string(w, label);
            u32s(w, &[*cell]);
        }
    }
}

struct Reader<'a>(&'a [u8]);

impl Reader<'_> {
    fn take<const N: usize>(&mut self) -> Option<[u8; N]> {
        let (head, rest) = self.0.split_first_chunk::<N>()?;
        self.0 = rest;
        Some(*head)
    }

    fn u8(&mut self) -> Option<u8> {
        Some(self.take::<1>()?[0])
    }

    fn bool(&mut self) -> Option<bool> {
        match self.u8()? {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        }
    }

    fn u32(&mut self) -> Option<u32> {
        self.take().map(u32::from_le_bytes)
    }

    fn u64(&mut self) -> Option<u64> {
        self.take().map(u64::from_le_bytes)
    }

    fn string(&mut self) -> Option<String> {
        let n = usize::try_from(self.u32()?).ok()?;
        let (head, rest) = self.0.split_at_checked(n)?;
        self.0 = rest;
        String::from_utf8(head.to_vec()).ok()
    }

    fn dest(&mut self) -> Option<BitsDest> {
        match self.u8()? {
            0 => Some(BitsDest::Stack(self.u32()?)),
            1 => Some(BitsDest::Heap(self.u32()?)),
            _ => None,
        }
    }

    fn op(&mut self) -> Option<Op> {
        Some(match self.u8()? {
            0 => Op::Xor {
                a: self.u32()?,
                b: self.u32()?,
                c: self.u32()?,
            },
            1 => Op::Mul {
                a: self.u32()?,
                b: self.u32()?,
                c: self.u32()?,
            },
            2 => Op::Set {
                o: self.u32()?,
                k: E::new(self.u64()?, self.u64()?),
            },
            3 => Op::Deref {
                o1: self.u32()?,
                o2: self.u32()?,
                o3: self.u32()?,
                mode: match self.u8()? {
                    0 => DerefMode::Cell,
                    1 => DerefMode::Pc,
                    2 => DerefMode::Fp,
                    _ => return None,
                },
            },
            4 => Op::Jump {
                oc: self.u32()?,
                od: self.u32()?,
                of: self.u32()?,
            },
            5 => Op::Keccak {
                m: [self.u32()?, self.u32()?, self.u32()?, self.u32()?],
                tail: self.u32()?,
                b8: self.u32()?,
                cap: self.u32()?,
                out: self.u32()?,
                in_odd: self.bool()?,
                out_odd: self.bool()?,
                out_cells: match self.u8()? {
                    0 => OutCells::One,
                    1 => OutCells::Two,
                    2 => OutCells::All,
                    _ => return None,
                },
            },
            _ => return None,
        })
    }

    fn hint(&mut self) -> Option<RHint> {
        Some(match self.u8()? {
            0 => RHint::FrameAddress { offset: self.u32()? },
            1 => RHint::AllocFrames {
                ptr: self.u32()?,
                size: self.u32()?,
                end: self.u32()?,
                start_inverse: K(self.u64()?),
                tail: self.u32()?,
            },
            2 => RHint::Alloc {
                ptr: self.u32()?,
                size: self.u32()?,
            },
            3 => RHint::AllocDyn {
                ptr: self.u32()?,
                size: self.u32()?,
            },
            4 => RHint::AllocArm {
                ptr: self.u32()?,
                sel: self.u32()?,
                sizes: (0..self.u32()?).map(|_| self.u32()).collect::<Option<_>>()?,
            },
            5 => RHint::CellAddress {
                ptr: self.u32()?,
                cell: self.u32()?,
            },
            6 => RHint::WitnessStack {
                name: self.string()?,
                base: self.u32()?,
                len: self.u32()?,
            },
            7 => RHint::WitnessHeap {
                name: self.string()?,
                ptr: self.u32()?,
                lo: self.u32()?,
                len: self.u32()?,
            },
            8 => RHint::Log2Ceil {
                bits: self.dest()?,
                dst: self.u32()?,
                nbits: self.u32()?,
                floor: self.u32()?,
            },
            9 => RHint::BitDecompose {
                value: self.u32()?,
                bits: self.dest()?,
                nbits: self.u32()?,
            },
            10 => RHint::BitDecomposeExp {
                value: self.u32()?,
                bits: self.dest()?,
                nbits: self.u32()?,
            },
            11 => RHint::DigitDecomposeExp {
                value: self.u32()?,
                dst: self.dest()?,
                nbits: self.u32()?,
                ndigits: self.u32()?,
                digit_bits: self.u32()?,
                start: self.u32()?,
                start_cell: match (self.bool()?, self.u32()?) {
                    (true, cell) => Some(cell),
                    (false, 0) => None,
                    (false, _) => return None,
                },
            },
            12 => RHint::WindowsExp {
                value: self.u32()?,
                dest: self.dest()?,
                at: self.u32()?,
                start: self.u32()?,
                width: self.u32()?,
                count: self.u32()?,
            },
            13 => RHint::FieldLimbs {
                value: self.u32()?,
                base: self.u32()?,
                len: self.u32()?,
            },
            14 => RHint::Inverse {
                value: self.u32()?,
                dst: self.u32()?,
            },
            15 => RHint::Print {
                label: self.string()?,
                cell: self.u32()?,
            },
            _ => return None,
        })
    }
}

// The variants' tags are their discriminants.
const _: () = assert!(DerefMode::Fp as u8 == 2 && OutCells::All as u8 == 2);
