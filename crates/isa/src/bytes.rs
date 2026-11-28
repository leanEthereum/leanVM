//! A compiled program as bytes, for a prover that does not compile its program: what proving it needs, without the
//! compiler's function ranges and source lines. Little-endian `u32` words: `main_frame`, the instruction count and the
//! hint count, then each instruction as [`OP_WORDS`] words, then each hint as [`HINT_WORDS`] words and its list or
//! name. A record is a tag and its fields in declaration order, zero past them: a `u64` two words, low first, a flag
//! `0` or `1`, a [`BitsDest`] its variant's index then its offset, an `Option` a flag then its value or zero, a list or
//! name its length, its items or bytes following the record.

use crate::{BitsDest, CompiledProgram, DerefMode, Op, OutCells, Program, RHint};
use verifier::{E, K, MAX_LOG_BYTECODE};

/// An instruction's words: its tag, then at most a `KECCAK`'s eleven fields.
const OP_WORDS: usize = 12;
/// A hint's words: its pc, its tag, then at most a `DigitDecomposeExp`'s nine fields.
const HINT_WORDS: usize = 11;

impl Program {
    /// The compiled program, which [`Self::from_bytes`] reads back.
    pub fn to_bytes(&self) -> Vec<u8> {
        let n_hints = self.hints.iter().map(|(_, hints)| hints.len()).sum();
        let mut w = Vec::new();
        u32s(&mut w, &[self.main_frame, len(self.prog.len()), len(n_hints)]);
        for op in &self.prog {
            record(&mut w, OP_WORDS, &op_words(op));
        }
        for &(pc, ref hints) in &self.hints {
            for hint in hints {
                let (words, tail) = hint_words(hint);
                record(&mut w, HINT_WORDS, &[&[pc][..], &words].concat());
                w.extend(tail);
            }
        }
        w
    }

    /// The program `bytes` encode, `None` unless they encode a program a power of two long, at most
    /// `2^MAX_LOG_BYTECODE`, its hints at pcs inside it, in order.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let mut r = Reader(bytes);
        let [main_frame, n, n_hints] = r.words()?;
        let mut prog = Vec::new();
        for _ in 0..n {
            prog.push(op(r.words()?)?);
        }
        let mut hints: Vec<(u32, Vec<RHint>)> = Vec::new();
        let mut last = 0;
        for _ in 0..n_hints {
            let words: [u32; HINT_WORDS] = r.words()?;
            if words[0] < last || words[0] >= n {
                return None;
            }
            last = words[0];
            let hint = r.hint(words)?;
            match hints.last_mut() {
                Some((pc, list)) if *pc == last => list.push(hint),
                _ => hints.push((last, vec![hint])),
            }
        }
        (r.0.is_empty() && n.is_power_of_two() && n <= 1 << MAX_LOG_BYTECODE).then(|| {
            Self::from(CompiledProgram {
                prog,
                hints,
                main_frame,
                fn_ranges: Vec::new(),
                src_lines: Vec::new(),
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

/// `words`, zero to `size` words.
fn record(w: &mut Vec<u8>, size: usize, words: &[u32]) {
    assert!(words.len() <= size);
    u32s(w, words);
    u32s(w, &vec![0; size - words.len()]);
}

fn u64_words(x: u64) -> [u32; 2] {
    [x as u32, (x >> 32) as u32]
}

fn dest_words(d: BitsDest) -> [u32; 2] {
    match d {
        BitsDest::Stack(o) => [0, o],
        BitsDest::Heap(o) => [1, o],
    }
}

fn op_words(op: &Op) -> Vec<u32> {
    match *op {
        Op::Xor { a, b, c } => vec![0, a, b, c],
        Op::Mul { a, b, c } => vec![1, a, b, c],
        Op::Set { o, k } => [&[2, o][..], &u64_words(k.c0), &u64_words(k.c1)].concat(),
        Op::Deref { o1, o2, o3, mode } => vec![3, o1, o2, o3, mode as u32],
        Op::Jump { oc, od, of } => vec![4, oc, od, of],
        Op::Keccak {
            m,
            tail,
            b8,
            cap,
            out,
            in_odd,
            out_odd,
            out_cells,
        } => [
            &[5][..],
            &m,
            &[tail, b8, cap, out, in_odd.into(), out_odd.into(), out_cells as u32],
        ]
        .concat(),
    }
}

/// A hint's tag and fields, and the list or name bytes after its record.
fn hint_words(hint: &RHint) -> (Vec<u32>, Vec<u8>) {
    let none = Vec::new();
    match hint {
        RHint::FrameAddress { offset } => (vec![0, *offset], none),
        RHint::AllocFrames {
            ptr,
            size,
            end,
            start_inverse,
            tail,
        } => (
            [&[1, *ptr, *size, *end][..], &u64_words(start_inverse.0), &[*tail]].concat(),
            none,
        ),
        RHint::Alloc { ptr, size } => (vec![2, *ptr, *size], none),
        RHint::AllocDyn { ptr, size } => (vec![3, *ptr, *size], none),
        RHint::AllocArm { ptr, sel, sizes } => {
            let mut tail = Vec::new();
            u32s(&mut tail, sizes);
            (vec![4, *ptr, *sel, len(sizes.len())], tail)
        }
        RHint::CellAddress { ptr, cell } => (vec![5, *ptr, *cell], none),
        RHint::WitnessStack { name, base, len: n } => (vec![6, *base, *n, len(name.len())], name.clone().into_bytes()),
        RHint::WitnessHeap { name, ptr, lo, len: n } => {
            (vec![7, *ptr, *lo, *n, len(name.len())], name.clone().into_bytes())
        }
        RHint::Log2Ceil {
            bits,
            dst,
            nbits,
            floor,
        } => ([&[8][..], &dest_words(*bits), &[*dst, *nbits, *floor]].concat(), none),
        RHint::BitDecompose { value, bits, nbits } => {
            ([&[9, *value][..], &dest_words(*bits), &[*nbits]].concat(), none)
        }
        RHint::BitDecomposeExp { value, bits, nbits } => {
            ([&[10, *value][..], &dest_words(*bits), &[*nbits]].concat(), none)
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
            let cell = [u32::from(start_cell.is_some()), start_cell.unwrap_or(0)];
            let fields = [*nbits, *ndigits, *digit_bits, *start];
            ([&[11, *value][..], &dest_words(*dst), &fields, &cell].concat(), none)
        }
        RHint::WindowsExp {
            value,
            dest,
            at,
            start,
            width,
            count,
        } => (
            [&[12, *value][..], &dest_words(*dest), &[*at, *start, *width, *count]].concat(),
            none,
        ),
        RHint::FieldLimbs { value, base, len } => (vec![13, *value, *base, *len], none),
        RHint::Inverse { value, dst } => (vec![14, *value, *dst], none),
        RHint::Print { label, cell } => (vec![15, *cell, len(label.len())], label.clone().into_bytes()),
    }
}

fn flag(x: u32) -> Option<bool> {
    (x < 2).then_some(x == 1)
}

fn dest(tag: u32, offset: u32) -> Option<BitsDest> {
    match tag {
        0 => Some(BitsDest::Stack(offset)),
        1 => Some(BitsDest::Heap(offset)),
        _ => None,
    }
}

fn u64_at(w: &[u32], i: usize) -> u64 {
    u64::from(w[i]) | u64::from(w[i + 1]) << 32
}

fn op(w: [u32; OP_WORDS]) -> Option<Op> {
    Some(match w[0] {
        0 => Op::Xor {
            a: w[1],
            b: w[2],
            c: w[3],
        },
        1 => Op::Mul {
            a: w[1],
            b: w[2],
            c: w[3],
        },
        2 => Op::Set {
            o: w[1],
            k: E::new(u64_at(&w, 2), u64_at(&w, 4)),
        },
        3 => Op::Deref {
            o1: w[1],
            o2: w[2],
            o3: w[3],
            mode: *[DerefMode::Cell, DerefMode::Pc, DerefMode::Fp].get(w[4] as usize)?,
        },
        4 => Op::Jump {
            oc: w[1],
            od: w[2],
            of: w[3],
        },
        5 => Op::Keccak {
            m: [w[1], w[2], w[3], w[4]],
            tail: w[5],
            b8: w[6],
            cap: w[7],
            out: w[8],
            in_odd: flag(w[9])?,
            out_odd: flag(w[10])?,
            out_cells: *[OutCells::One, OutCells::Two, OutCells::All].get(w[11] as usize)?,
        },
        _ => return None,
    })
}

struct Reader<'a>(&'a [u8]);

impl Reader<'_> {
    fn bytes(&mut self, n: u32) -> Option<&[u8]> {
        let (head, rest) = self.0.split_at_checked(n as usize)?;
        self.0 = rest;
        Some(head)
    }

    fn words<const N: usize>(&mut self) -> Option<[u32; N]> {
        let mut words = [0; N];
        self.fill(&mut words)?;
        Some(words)
    }

    /// The next `out.len()` words into `out`, one loop for every record size.
    #[inline(never)]
    fn fill(&mut self, out: &mut [u32]) -> Option<()> {
        for word in out {
            let (head, rest) = self.0.split_first_chunk()?;
            self.0 = rest;
            *word = u32::from_le_bytes(*head);
        }
        Some(())
    }

    fn string(&mut self, n: u32) -> Option<String> {
        String::from_utf8(self.bytes(n)?.to_vec()).ok()
    }

    /// The hint of the record `w`, its pc first, and its list or name.
    fn hint(&mut self, w: [u32; HINT_WORDS]) -> Option<RHint> {
        let w = &w[1..];
        Some(match w[0] {
            0 => RHint::FrameAddress { offset: w[1] },
            1 => RHint::AllocFrames {
                ptr: w[1],
                size: w[2],
                end: w[3],
                start_inverse: K(u64_at(w, 4)),
                tail: w[6],
            },
            2 => RHint::Alloc { ptr: w[1], size: w[2] },
            3 => RHint::AllocDyn { ptr: w[1], size: w[2] },
            4 => RHint::AllocArm {
                ptr: w[1],
                sel: w[2],
                sizes: {
                    let mut sizes = Vec::new();
                    for _ in 0..w[3] {
                        sizes.push(self.words::<1>()?[0]);
                    }
                    sizes
                },
            },
            5 => RHint::CellAddress { ptr: w[1], cell: w[2] },
            6 => RHint::WitnessStack {
                base: w[1],
                len: w[2],
                name: self.string(w[3])?,
            },
            7 => RHint::WitnessHeap {
                ptr: w[1],
                lo: w[2],
                len: w[3],
                name: self.string(w[4])?,
            },
            8 => RHint::Log2Ceil {
                bits: dest(w[1], w[2])?,
                dst: w[3],
                nbits: w[4],
                floor: w[5],
            },
            9 => RHint::BitDecompose {
                value: w[1],
                bits: dest(w[2], w[3])?,
                nbits: w[4],
            },
            10 => RHint::BitDecomposeExp {
                value: w[1],
                bits: dest(w[2], w[3])?,
                nbits: w[4],
            },
            11 => RHint::DigitDecomposeExp {
                value: w[1],
                dst: dest(w[2], w[3])?,
                nbits: w[4],
                ndigits: w[5],
                digit_bits: w[6],
                start: w[7],
                start_cell: flag(w[8])?.then_some(w[9]),
            },
            12 => RHint::WindowsExp {
                value: w[1],
                dest: dest(w[2], w[3])?,
                at: w[4],
                start: w[5],
                width: w[6],
                count: w[7],
            },
            13 => RHint::FieldLimbs {
                value: w[1],
                base: w[2],
                len: w[3],
            },
            14 => RHint::Inverse { value: w[1], dst: w[2] },
            15 => RHint::Print {
                cell: w[1],
                label: self.string(w[2])?,
            },
            _ => return None,
        })
    }
}

// The variants' tags are their discriminants.
const _: () = assert!(DerefMode::Fp as u8 == 2 && OutCells::All as u8 == 2);

#[cfg(test)]
mod tests {
    use super::*;

    /// Every instruction and hint survives the bytes, and a cut or longer encoding is refused.
    #[test]
    fn a_program_round_trips() {
        let name = || String::from("stream");
        let prog = vec![
            Op::Xor {
                a: 1,
                b: 2,
                c: u32::MAX,
            },
            Op::Mul { a: 4, b: 5, c: 6 },
            Op::Set {
                o: 7,
                k: E::new(u64::MAX - 1, 1 << 40),
            },
            Op::Deref {
                o1: 8,
                o2: 9,
                o3: 10,
                mode: DerefMode::Fp,
            },
            Op::Jump { oc: 11, od: 12, of: 13 },
            Op::Keccak {
                m: [14, 15, 16, 17],
                tail: 18,
                b8: 19,
                cap: 20,
                out: 21,
                in_odd: true,
                out_odd: false,
                out_cells: OutCells::Two,
            },
            Op::Deref {
                o1: 0,
                o2: 0,
                o3: 0,
                mode: DerefMode::Pc,
            },
            Op::Xor { a: 0, b: 0, c: 0 },
        ];
        let hints = vec![
            (
                0,
                vec![RHint::FrameAddress { offset: 1 }, RHint::Alloc { ptr: 2, size: 3 }],
            ),
            (
                2,
                vec![
                    RHint::AllocFrames {
                        ptr: 1,
                        size: 2,
                        end: 3,
                        start_inverse: K(u64::MAX),
                        tail: 4,
                    },
                    RHint::AllocDyn { ptr: 5, size: 6 },
                    RHint::AllocArm {
                        ptr: 7,
                        sel: 8,
                        sizes: vec![9, 10, 11],
                    },
                    RHint::CellAddress { ptr: 12, cell: 13 },
                    RHint::WitnessStack {
                        name: name(),
                        base: 14,
                        len: 15,
                    },
                    RHint::WitnessHeap {
                        name: name(),
                        ptr: 16,
                        lo: 17,
                        len: 18,
                    },
                ],
            ),
            (
                7,
                vec![
                    RHint::Log2Ceil {
                        bits: BitsDest::Heap(19),
                        dst: 20,
                        nbits: 21,
                        floor: 22,
                    },
                    RHint::BitDecompose {
                        value: 23,
                        bits: BitsDest::Stack(24),
                        nbits: 25,
                    },
                    RHint::BitDecomposeExp {
                        value: 26,
                        bits: BitsDest::Heap(27),
                        nbits: 28,
                    },
                    RHint::DigitDecomposeExp {
                        value: 29,
                        dst: BitsDest::Stack(30),
                        nbits: 31,
                        ndigits: 32,
                        digit_bits: 33,
                        start: 34,
                        start_cell: Some(35),
                    },
                    RHint::DigitDecomposeExp {
                        value: 0,
                        dst: BitsDest::Heap(0),
                        nbits: 0,
                        ndigits: 0,
                        digit_bits: 0,
                        start: 0,
                        start_cell: None,
                    },
                    RHint::WindowsExp {
                        value: 36,
                        dest: BitsDest::Heap(37),
                        at: 38,
                        start: 39,
                        width: 40,
                        count: 41,
                    },
                    RHint::FieldLimbs {
                        value: 42,
                        base: 43,
                        len: 44,
                    },
                    RHint::Inverse { value: 45, dst: 46 },
                    RHint::Print {
                        label: String::from("label"),
                        cell: 47,
                    },
                ],
            ),
        ];
        let program = Program::from(CompiledProgram {
            prog,
            hints: hints.into_iter().collect(),
            main_frame: 48,
            fn_ranges: Vec::new(),
            src_lines: Vec::new(),
        });
        let bytes = program.to_bytes();
        let decoded = Program::from_bytes(&bytes).expect("the bytes decode");
        assert_eq!(format!("{:?}", *decoded), format!("{:?}", *program));
        assert!(Program::from_bytes(&bytes[..bytes.len() - 1]).is_none());
        assert!(Program::from_bytes(&[&bytes[..], &[0]].concat()).is_none());
    }
}
