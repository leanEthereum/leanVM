//! A line format for a [`CompiledProgram`]: its bytecode before the padding, its hints, `main`'s frame, its function
//! ranges and its source lines. It is what `formal/lean_vm`'s `lake exe guest-backend export` and `lake exe
//! guest-artifact` write of a program compiled in Lean, so a test can compare the two compilers' output as text and
//! run what the Lean one produced.
//!
//! ```text
//! size <slots>
//! main_frame <cells>
//! F <name> <entry> <len>                      one line a function
//! X <a> <b> <c>                               one line an instruction, in pc order:
//! M <a> <b> <c>                               XOR, MUL, SET (two limbs), DEREF (mode 0 cell, 1 pc, 2 fp),
//! S <o> <c0> <c1>                             JUMP, KECCAK (the output's cell count last)
//! D <o1> <o2> <o3> <mode>
//! J <oc> <od> <of>
//! K <m0> <m1> <m2> <m3> <tail> <b8> <cap> <out> <in_odd> <out_odd> <cells>
//! H <pc> <kind> <fields>                      one line a hint, in pc order
//! L <pc> <line>                               the source line from `pc` on (`src_lines`): at pc 0 and wherever it
//!                                             changes, none for a program without source lines
//! ```

use std::collections::HashMap;
use std::fmt::Write;

use crate::{BitsDest, CompiledProgram, DerefMode, Op, OutCells, Program, RHint};
use verifier::{E, K};

fn bits_dest(dest: BitsDest) -> String {
    match dest {
        BitsDest::Stack(base) => format!("stack {base}"),
        BitsDest::Heap(ptr) => format!("heap {ptr}"),
    }
}

fn hint_line(hint: &RHint) -> String {
    match hint {
        RHint::FrameAddress { offset } => format!("frame {offset}"),
        RHint::AllocFrames {
            ptr,
            size,
            end,
            start_inverse,
            tail,
        } => format!("frames {ptr} {size} {end} {} {tail}", start_inverse.0),
        RHint::Alloc { ptr, size } => format!("alloc {ptr} {size}"),
        RHint::AllocDyn { ptr, size } => format!("allocdyn {ptr} {size}"),
        RHint::WitnessStack { name, base, len } => format!("wstack {name} {base} {len}"),
        RHint::WitnessHeap { name, ptr, lo, len } => format!("wheap {name} {ptr} {lo} {len}"),
        RHint::Log2Ceil {
            bits,
            dst,
            nbits,
            floor,
        } => format!("log2 {} {dst} {nbits} {floor}", bits_dest(*bits)),
        RHint::BitDecompose { value, bits, nbits } => format!("bits {value} {} {nbits}", bits_dest(*bits)),
        RHint::BitDecomposeExp { value, bits, nbits } => format!("bitsexp {value} {} {nbits}", bits_dest(*bits)),
        RHint::DigitDecomposeExp {
            value,
            dst,
            nbits,
            ndigits,
            digit_bits,
            start,
            start_cell,
        } => {
            let start_cell = start_cell.map_or_else(|| "-".to_string(), |c| c.to_string());
            format!(
                "digits {value} {} {nbits} {ndigits} {digit_bits} {start} {start_cell}",
                bits_dest(*dst)
            )
        }
        RHint::WindowsExp {
            value,
            dest,
            at,
            start,
            width,
            count,
        } => format!("windows {value} {} {at} {start} {width} {count}", bits_dest(*dest)),
        RHint::FieldLimbs { value, base, len } => format!("limbs {value} {base} {len}"),
        RHint::Inverse { value, dst } => format!("inverse {value} {dst}"),
        RHint::Print { label, cell } => format!("print {cell} {label}"),
    }
}

/// A line's fields after its tag, read in order.
struct Fields<'a> {
    line: &'a str,
    rest: std::str::Split<'a, char>,
}

impl<'a> Fields<'a> {
    fn word(&mut self) -> Result<&'a str, String> {
        self.rest.next().ok_or_else(|| format!("`{}` is short", self.line))
    }

    fn num<T: std::str::FromStr>(&mut self) -> Result<T, String> {
        let word = self.word()?;
        word.parse()
            .map_err(|_| format!("`{word}` in `{}` is no number", self.line))
    }

    fn flag(&mut self) -> Result<bool, String> {
        Ok(self.num::<u8>()? != 0)
    }

    fn bits_dest(&mut self) -> Result<BitsDest, String> {
        match self.word()? {
            "stack" => Ok(BitsDest::Stack(self.num()?)),
            "heap" => Ok(BitsDest::Heap(self.num()?)),
            other => Err(format!("`{other}` in `{}` is no hint destination", self.line)),
        }
    }

    fn op(&mut self, tag: &str) -> Result<Op, String> {
        Ok(match tag {
            "X" => Op::Xor {
                a: self.num()?,
                b: self.num()?,
                c: self.num()?,
            },
            "M" => Op::Mul {
                a: self.num()?,
                b: self.num()?,
                c: self.num()?,
            },
            "S" => Op::Set {
                o: self.num()?,
                k: E::new(self.num()?, self.num()?),
            },
            "D" => Op::Deref {
                o1: self.num()?,
                o2: self.num()?,
                o3: self.num()?,
                mode: match self.num::<u8>()? {
                    0 => DerefMode::Cell,
                    1 => DerefMode::Pc,
                    2 => DerefMode::Fp,
                    mode => return Err(format!("`{}` has no DEREF mode {mode}", self.line)),
                },
            },
            "J" => Op::Jump {
                oc: self.num()?,
                od: self.num()?,
                of: self.num()?,
            },
            "K" => Op::Keccak {
                m: [self.num()?, self.num()?, self.num()?, self.num()?],
                tail: self.num()?,
                b8: self.num()?,
                cap: self.num()?,
                out: self.num()?,
                in_odd: self.flag()?,
                out_odd: self.flag()?,
                out_cells: match self.num::<u8>()? {
                    1 => OutCells::One,
                    2 => OutCells::Two,
                    13 => OutCells::All,
                    cells => return Err(format!("`{}` writes {cells} cells", self.line)),
                },
            },
            _ => return Err(format!("`{}` is no line of a program", self.line)),
        })
    }

    fn hint(&mut self) -> Result<RHint, String> {
        Ok(match self.word()? {
            "frame" => RHint::FrameAddress { offset: self.num()? },
            "frames" => RHint::AllocFrames {
                ptr: self.num()?,
                size: self.num()?,
                end: self.num()?,
                start_inverse: K(self.num()?),
                tail: self.num()?,
            },
            "alloc" => RHint::Alloc {
                ptr: self.num()?,
                size: self.num()?,
            },
            "allocdyn" => RHint::AllocDyn {
                ptr: self.num()?,
                size: self.num()?,
            },
            "wstack" => RHint::WitnessStack {
                name: self.word()?.to_string(),
                base: self.num()?,
                len: self.num()?,
            },
            "wheap" => RHint::WitnessHeap {
                name: self.word()?.to_string(),
                ptr: self.num()?,
                lo: self.num()?,
                len: self.num()?,
            },
            "log2" => RHint::Log2Ceil {
                bits: self.bits_dest()?,
                dst: self.num()?,
                nbits: self.num()?,
                floor: self.num()?,
            },
            "bits" => RHint::BitDecompose {
                value: self.num()?,
                bits: self.bits_dest()?,
                nbits: self.num()?,
            },
            "bitsexp" => RHint::BitDecomposeExp {
                value: self.num()?,
                bits: self.bits_dest()?,
                nbits: self.num()?,
            },
            "digits" => RHint::DigitDecomposeExp {
                value: self.num()?,
                dst: self.bits_dest()?,
                nbits: self.num()?,
                ndigits: self.num()?,
                digit_bits: self.num()?,
                start: self.num()?,
                start_cell: match self.word()? {
                    "-" => None,
                    cell => Some(
                        cell.parse()
                            .map_err(|_| format!("`{cell}` in `{}` is no cell", self.line))?,
                    ),
                },
            },
            "windows" => RHint::WindowsExp {
                value: self.num()?,
                dest: self.bits_dest()?,
                at: self.num()?,
                start: self.num()?,
                width: self.num()?,
                count: self.num()?,
            },
            "limbs" => RHint::FieldLimbs {
                value: self.num()?,
                base: self.num()?,
                len: self.num()?,
            },
            "inverse" => RHint::Inverse {
                value: self.num()?,
                dst: self.num()?,
            },
            "print" => {
                let cell = self.num()?;
                RHint::Print {
                    label: self.rest.by_ref().collect::<Vec<_>>().join(" "),
                    cell,
                }
            }
            other => return Err(format!("`{other}` in `{}` is no hint", self.line)),
        })
    }
}

impl CompiledProgram {
    /// The program in the line format of this module.
    #[doc(hidden)]
    pub fn __to_text(&self) -> String {
        let mut out = format!("size {}\nmain_frame {}\n", self.prog.len(), self.main_frame);
        for (name, entry, len) in &self.fn_ranges {
            writeln!(out, "F {name} {entry} {len}").unwrap();
        }
        for op in &self.prog[..self.code_len()] {
            match *op {
                Op::Xor { a, b, c } => writeln!(out, "X {a} {b} {c}"),
                Op::Mul { a, b, c } => writeln!(out, "M {a} {b} {c}"),
                Op::Set { o, k } => writeln!(out, "S {o} {} {}", k.c0, k.c1),
                Op::Deref { o1, o2, o3, mode } => writeln!(out, "D {o1} {o2} {o3} {}", mode as u8),
                Op::Jump { oc, od, of } => writeln!(out, "J {oc} {od} {of}"),
                Op::Keccak {
                    m,
                    tail,
                    b8,
                    cap,
                    out: dst,
                    in_odd,
                    out_odd,
                    out_cells,
                } => writeln!(
                    out,
                    "K {} {} {} {} {tail} {b8} {cap} {dst} {} {} {}",
                    m[0],
                    m[1],
                    m[2],
                    m[3],
                    u8::from(in_odd),
                    u8::from(out_odd),
                    out_cells.cells()
                ),
            }
            .unwrap();
        }
        let mut pcs: Vec<&u32> = self.hints.keys().collect();
        pcs.sort_unstable();
        for pc in pcs {
            for hint in &self.hints[pc] {
                writeln!(out, "H {pc} {}", hint_line(hint)).unwrap();
            }
        }
        for (pc, &line) in self.src_lines.iter().enumerate() {
            if pc == 0 || self.src_lines[pc - 1] != line {
                writeln!(out, "L {pc} {line}").unwrap();
            }
        }
        out
    }
}

impl Program {
    /// The program a text in the line format of this module describes, with its stacked bytecode.
    #[doc(hidden)]
    pub fn __from_text(text: &str) -> Result<Self, String> {
        let (mut size, mut main_frame) = (None, None);
        let (mut prog, mut fn_ranges) = (Vec::new(), Vec::new());
        let mut hints: HashMap<u32, Vec<RHint>> = HashMap::new();
        let mut lines: Vec<(usize, u32)> = Vec::new();
        for line in text.lines() {
            let mut rest = line.split(' ');
            let tag = rest.next().unwrap_or("");
            let mut fields = Fields { line, rest };
            match tag {
                "size" => size = Some(fields.num::<usize>()?),
                "main_frame" => main_frame = Some(fields.num()?),
                "F" => fn_ranges.push((fields.word()?.to_string(), fields.num()?, fields.num()?)),
                "H" => hints.entry(fields.num()?).or_default().push(fields.hint()?),
                "L" => lines.push((fields.num()?, fields.num()?)),
                _ => prog.push(fields.op(tag)?),
            }
        }
        let size = size.ok_or("no `size` line")?;
        let main_frame = main_frame.ok_or("no `main_frame` line")?;
        if !size.is_power_of_two() || prog.len() >= size {
            return Err(format!("{} instructions do not fit {size} slots", prog.len()));
        }
        let mut src_lines = Vec::new();
        for (i, &(pc, line)) in lines.iter().enumerate() {
            let end = lines.get(i + 1).map_or(prog.len(), |next| next.0);
            if pc != src_lines.len() || end < pc || end > prog.len() {
                return Err(format!("`L {pc} {line}` is out of order or past the code"));
            }
            src_lines.resize(end, line);
        }
        prog.resize(size, Op::Set { o: 0, k: E::new(0, 0) });
        Ok(Self::from(CompiledProgram {
            prog,
            hints,
            main_frame,
            fn_ranges,
            src_lines,
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every instruction, every hint kind and the source lines survive the format.
    #[test]
    fn text_round_trips() {
        let text = "size 16\nmain_frame 9\nF main 0 6\n\
                    X 1 2 3\nM 1 2 3\nS 4 5 6\nD 1 2 3 2\nJ 1 2 3\nK 1 2 3 4 5 6 7 8 1 0 13\n\
                    H 0 frame 7\nH 0 frames 1 2 3 4 5\nH 1 alloc 1 2\nH 1 allocdyn 1 2\nH 2 wstack s 1 2\n\
                    H 2 wheap s 1 2 3\nH 3 log2 stack 1 2 3 4\nH 3 bits 1 heap 2 3\nH 3 bitsexp 1 stack 2 3\n\
                    H 4 digits 1 stack 2 3 4 5 6 -\nH 4 digits 1 heap 2 3 4 5 6 7\nH 4 windows 1 stack 2 3 4 5 6\n\
                    H 5 limbs 1 2 3\nH 5 inverse 1 2\nH 5 print 1 a label\nL 0 0\nL 2 7\nL 5 9\n";
        let program = Program::__from_text(text).unwrap();
        assert_eq!(program.__to_text(), text);
        assert_eq!(program.prog.len(), 16);
        assert_eq!(program.src_lines, [0, 0, 7, 7, 7, 9]);
    }
}
