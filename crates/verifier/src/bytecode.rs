//! The program a proof is about, prepared once so that verifying many proofs of it hashes its bytecode once.

use crate::field::{E, K, ZERO};
use crate::hash::{Digest, keccak_hash};
use crate::layout::{BYTECODE_SLOT_BITS, MAX_LOG_BYTECODE, OP_DEREF, OP_KECCAK, OPCODE_SLOT, TAG};
use crate::multilinear::eq_kernel;
use crate::{VerifierError, require};
use std::collections::BTreeMap;

/// The program, prepared to be split by opcode at the link's points, and the Fiat-Shamir IV it gives every transcript.
///
/// The program is fixed while the points vary, so its instructions are grouped once (`groups`).
#[derive(Clone, Debug)]
pub struct Bytecode {
    len: usize,
    pub(crate) fiat_shamir_iv: Digest,
    /// The instructions cut into blocks of `2^BLOCK_LOG` consecutive ones. For each block, every distinct
    /// `(opcode, slot, word)` with the positions where it occurs: slot 3 with word 1 for the opcode itself, and each
    /// nonzero operand slot.
    groups: Vec<Vec<Group>>,
}

/// One distinct `(opcode, slot, word)` of a block of instructions, with the positions where it occurs.
#[derive(Clone, Debug)]
struct Group {
    op: u8,
    slot: u8,
    word: K,
    at: Vec<u16>,
}

/// How many low coordinates one block of [`Bytecode::split`] spans: their eq table stays in cache.
const BLOCK_LOG: usize = 14;
const _: () = assert!(BLOCK_LOG <= u16::BITS as usize, "a position within a block is a u16");

impl Bytecode {
    /// The Fiat-Shamir IV every transcript of this program starts from.
    pub fn fiat_shamir_iv(&self) -> [u8; 32] {
        self.fiat_shamir_iv.0
    }

    /// From the multilinear's values on the hypercube, LSB-first: what `isa::Program::stacked_bytecode` returns.
    /// Rejects a bytecode that is not the encoding of a program (`is_valid_encoding_of_a_leanisa_program`).
    pub fn new(stacked_bytecode: &[u64]) -> Result<Self, VerifierError> {
        require(
            is_valid_encoding_of_a_leanisa_program(stacked_bytecode),
            VerifierError::BytecodeShape,
        )?;
        let fiat_shamir_iv = {
            let iv_preimage: Vec<u8> = TAG
                .iter()
                .copied()
                .chain(stacked_bytecode.iter().flat_map(|word| word.to_le_bytes()))
                .collect();
            keccak_hash(&iv_preimage)
        };
        let n = stacked_bytecode.len() >> BYTECODE_SLOT_BITS;
        let groups = (0..n)
            .step_by(n.min(1 << BLOCK_LOG))
            .map(|start| {
                let mut members = BTreeMap::<(u8, u8, u64), Vec<u16>>::new();
                for pc in start..n.min(start + (1 << BLOCK_LOG)) {
                    let slot = |s: usize| stacked_bytecode[s * n + pc];
                    let (op, position) = (slot(OPCODE_SLOT).trailing_zeros() as u8, (pc - start) as u16);
                    members.entry((op, OPCODE_SLOT as u8, 1)).or_default().push(position);
                    for s in (OPCODE_SLOT + 1..1 << BYTECODE_SLOT_BITS).filter(|&s| slot(s) != 0) {
                        members.entry((op, s as u8, slot(s))).or_default().push(position);
                    }
                }
                let mut members: Vec<Group> = members
                    .into_iter()
                    .map(|((op, slot, word), at)| Group {
                        op,
                        slot,
                        word: K(word),
                        at,
                    })
                    .collect();
                // Fewest positions first: the sum over a group's positions then runs one length many times over, so
                // its loop exit is predicted.
                members.sort_by_key(|g| g.at.len());
                members
            })
            .collect();
        Ok(Self {
            len: stacked_bytecode.len(),
            fiat_shamir_iv,
            groups,
        })
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

/// The program's slots split by opcode at a point: what [`Bytecode::split`] returns.
pub struct Split {
    /// `count[F] = Σ_k eq(point, k)·[op_k = F]`.
    pub count: Vec<E>,
    /// `slots[F][s] = Σ_k eq(point, k)·[op_k = F]·BC_s(k)`, for the operand slots `s ≥ 4`.
    pub slots: Vec<[E; 1 << BYTECODE_SLOT_BITS]>,
    /// `pc[F][s] = Σ_k eq(point, k)·[op_k = F]·g^k·BC_s(k)`, for the `(F, s)` asked for, zero elsewhere.
    pub pc: Vec<[E; 1 << BYTECODE_SLOT_BITS]>,
}

impl Bytecode {
    /// Each instruction's slots, split by its opcode, at `point` over the instructions (§sec:link-split): a link that
    /// reads a slot only for some opcodes weighs it per opcode. `pc` names the `(opcode, slot)` read times `pc`.
    ///
    /// The low coordinates' eq table weighs the positions of a block and the high coordinates' weighs the blocks, and a
    /// group's word multiplies the sum of its positions' weights once.
    pub fn split(&self, point: &[E], pc: &[(usize, usize)]) -> Result<Split, VerifierError> {
        require(
            point.len() < 64 && self.len >> BYTECODE_SLOT_BITS == 1 << point.len(),
            VerifierError::MultilinearSize,
        )?;
        let ops = OP_KECCAK + 1;
        let mut split = Split {
            count: vec![ZERO; ops],
            slots: vec![[ZERO; 1 << BYTECODE_SLOT_BITS]; ops],
            pc: vec![[ZERO; 1 << BYTECODE_SLOT_BITS]; ops],
        };
        let mut wanted = vec![0u16; ops];
        for &(op, s) in pc {
            wanted[op] |= 1 << s;
        }
        let (low, high) = point.split_at(point.len().min(BLOCK_LOG));
        let (low_weights, high_weights) = (eq_kernel(low), eq_kernel(high));
        // `g^k = g^(block·2^low)·g^position`: the positions' weights times `g^position`, and the step between blocks.
        let low_pc: Vec<E> = if pc.is_empty() {
            Vec::new()
        } else {
            let mut g = K(1);
            low_weights
                .iter()
                .map(|&e| {
                    let v = e * g;
                    g = g * K(2);
                    v
                })
                .collect()
        };
        let step = (0..low.len()).fold(K(2), |g, _| g * g);
        // A block's sums are taken at its positions alone, then weighed by the block once.
        let mut g_block = K(1);
        let mut local = Split {
            count: vec![ZERO; ops],
            slots: vec![[ZERO; 1 << BYTECODE_SLOT_BITS]; ops],
            pc: vec![[ZERO; 1 << BYTECODE_SLOT_BITS]; ops],
        };
        for (block, &weight) in self.groups.iter().zip(&high_weights) {
            for group in block {
                let (op, s) = (group.op as usize, group.slot as usize);
                let sum = E::sum(group.at.iter().map(|&i| low_weights[i as usize]));
                if s == OPCODE_SLOT {
                    local.count[op] += sum;
                    continue;
                }
                local.slots[op][s] += sum * group.word;
                if wanted[op] >> s & 1 == 1 {
                    local.pc[op][s] += E::sum(group.at.iter().map(|&i| low_pc[i as usize])) * group.word;
                }
            }
            let weight_pc = weight * g_block;
            for op in 0..ops {
                split.count[op] += weight * std::mem::replace(&mut local.count[op], ZERO);
                for s in OPCODE_SLOT + 1..1 << BYTECODE_SLOT_BITS {
                    split.slots[op][s] += weight * std::mem::replace(&mut local.slots[op][s], ZERO);
                    if wanted[op] >> s & 1 == 1 {
                        split.pc[op][s] += weight_pc * std::mem::replace(&mut local.pc[op][s], ZERO);
                    }
                }
            }
            g_block = g_block * step;
        }
        Ok(split)
    }
}

fn is_valid_encoding_of_a_leanisa_program(stacked_bytecode: &[u64]) -> bool {
    let n = stacked_bytecode.len() >> BYTECODE_SLOT_BITS;
    let instruction = |pc: usize| {
        let slot = |s: usize| stacked_bytecode[s * n + pc];
        let zero_from = |first: usize| (first..1 << BYTECODE_SLOT_BITS).all(|s| slot(s) == 0);
        (0..OPCODE_SLOT).all(|s| slot(s) == 0)
            && match (0..=OP_KECCAK).find(|&op| slot(OPCODE_SLOT) == 1 << op) {
                Some(OP_DEREF) => matches!((slot(7), slot(8)), (0, 0) | (1, 0) | (0, 1)) && zero_from(9),
                Some(OP_KECCAK) => {
                    slot(12) <= 1 && slot(13) <= 1 && matches!((slot(14), slot(15)), (0, 0) | (1, 0) | (1, 1))
                }
                Some(_) => zero_from(7),
                None => false,
            }
    };
    n.is_power_of_two()
        && stacked_bytecode.len() == n << BYTECODE_SLOT_BITS
        && n <= 1 << MAX_LOG_BYTECODE
        && (0..n).all(instruction)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::layout::OP_XOR;

    #[test]
    fn split_matches_a_sum_over_instructions() {
        // Programs mixing XOR and DEREF with random and repeated operands, small and across the block split, with
        // DEREF's slots 5 and 6 read times `pc`.
        let mut state = 0x2545_F491_4F6C_DD1Du64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let pc = [(OP_DEREF, 5), (OP_DEREF, 6)];
        for log_n in [0, 3, BLOCK_LOG, BLOCK_LOG + 2] {
            let n = 1usize << log_n;
            let mut stacked_bytecode = vec![0u64; n << BYTECODE_SLOT_BITS];
            for k in 0..n {
                let op = if next() % 3 == 0 { OP_DEREF } else { OP_XOR };
                stacked_bytecode[3 * n + k] = 1 << op;
                for s in 4..7 {
                    stacked_bytecode[s * n + k] = if next() % 2 == 0 { next() } else { 7 };
                }
                if op == OP_DEREF {
                    stacked_bytecode[7 * n + k] = next() % 2;
                }
            }
            let point: Vec<E> = (0..log_n).map(|_| E::new(next(), next())).collect();
            let bytecode = Bytecode::new(&stacked_bytecode).expect("a program");
            let split = bytecode.split(&point, &pc).expect("a point over the instructions");

            let ops = OP_KECCAK + 1;
            let (mut count, mut slots, mut at_pc) = (
                vec![ZERO; ops],
                vec![[ZERO; 1 << BYTECODE_SLOT_BITS]; ops],
                vec![[ZERO; 1 << BYTECODE_SLOT_BITS]; ops],
            );
            let (eq, mut g_k) = (eq_kernel(&point), K(1));
            for (k, &e) in eq.iter().enumerate() {
                let op = stacked_bytecode[3 * n + k].trailing_zeros() as usize;
                count[op] += e;
                for s in 4..1 << BYTECODE_SLOT_BITS {
                    let word = K(stacked_bytecode[s * n + k]);
                    slots[op][s] += e * word;
                    if pc.contains(&(op, s)) {
                        at_pc[op][s] += e * (g_k * word);
                    }
                }
                g_k = g_k * K(2);
            }
            assert_eq!(split.count, count);
            assert_eq!(split.slots, slots);
            assert_eq!(split.pc, at_pc);
        }
    }
}
