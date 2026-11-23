//! A program's hints and witness streams as text, for the Lean executor.

use crate::{BitsDest, CompiledProgram, RHint};
use std::fmt::Write;
use verifier::E;

impl CompiledProgram {
    /// What an execution needs besides the bytecode, as text for the Lean executor
    /// (`formal/lean_vm/cli/LeanvmExecute.lean` reads it): `main`'s frame size, the hints by pc
    /// (`Print` left out), and the witness streams by name, each entry's words as hex limbs.
    pub fn export_hints(&self, witness: &[(String, Vec<Vec<E>>)]) -> String {
        let dest = |d: &BitsDest| match d {
            BitsDest::Stack(o) => format!("s {o}"),
            BitsDest::Heap(o) => format!("h {o}"),
        };
        let mut out = format!("leanvm-advice 1\nmain_frame {}\n", self.main_frame);
        let mut pcs: Vec<_> = self.hints.iter().collect();
        pcs.sort_by_key(|(pc, _)| **pc);
        writeln!(out, "hints {}", pcs.len()).unwrap();
        for (pc, hs) in pcs {
            let hs: Vec<String> = hs
                .iter()
                .filter_map(|h| {
                    Some(match h {
                        RHint::FrameAddress { offset } => format!("fa {offset}"),
                        RHint::AllocFrames {
                            ptr,
                            size,
                            end,
                            start_inverse,
                            tail,
                        } => {
                            format!("af {ptr} {size} {end} {:x} {tail}", start_inverse.0)
                        }
                        RHint::Alloc { ptr, size } => format!("al {ptr} {size}"),
                        RHint::AllocDyn { ptr, size } => format!("ad {ptr} {size}"),
                        RHint::AllocArm { ptr, sel, sizes } => {
                            let sizes: Vec<String> = sizes.iter().map(u32::to_string).collect();
                            format!("aa {ptr} {sel} {} {}", sizes.len(), sizes.join(" "))
                        }
                        RHint::CellAddress { ptr, cell } => format!("ca {ptr} {cell}"),
                        RHint::WitnessStack { name, base, len } => format!("ws {name} {base} {len}"),
                        RHint::WitnessHeap { name, ptr, lo, len } => format!("wh {name} {ptr} {lo} {len}"),
                        RHint::Log2Ceil {
                            bits,
                            dst,
                            nbits,
                            floor,
                        } => {
                            format!("lc {} {dst} {nbits} {floor}", dest(bits))
                        }
                        RHint::BitDecompose { value, bits, nbits } => format!("bd {value} {} {nbits}", dest(bits)),
                        RHint::BitDecomposeExp { value, bits, nbits } => {
                            format!("be {value} {} {nbits}", dest(bits))
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
                            let c = start_cell.map_or("-".to_string(), |c| c.to_string());
                            format!("dd {value} {} {nbits} {ndigits} {digit_bits} {start} {c}", dest(dst))
                        }
                        RHint::WindowsExp {
                            value,
                            dest: d,
                            at,
                            start,
                            width,
                            count,
                        } => {
                            format!("we {value} {} {at} {start} {width} {count}", dest(d))
                        }
                        RHint::FieldLimbs { value, base, len } => format!("fl {value} {base} {len}"),
                        RHint::Inverse { value, dst } => format!("iv {value} {dst}"),
                        RHint::Print { .. } => return None,
                    })
                })
                .collect();
            write!(out, "{pc} {}", hs.len()).unwrap();
            for h in hs {
                write!(out, " {h}").unwrap();
            }
            out.push('\n');
        }
        let mut streams: Vec<_> = witness.iter().collect();
        streams.sort_by_key(|(name, _)| name.as_str());
        writeln!(out, "streams {}", streams.len()).unwrap();
        for (name, entries) in streams {
            write!(out, "{name} {}", entries.len()).unwrap();
            for e in entries {
                write!(out, " {}", e.len()).unwrap();
                for w in e {
                    write!(out, " {:x} {:x}", w.c0, w.c1).unwrap();
                }
            }
            out.push('\n');
        }
        out
    }
}
