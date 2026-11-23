//! The verifier after decoding (`NativeVm/Model/Verify.lean`): the seed, the walk, the end check.

use crate::buf::Buf;
use crate::bus::{BusW, verify_bus_balance};
use crate::field::EW;
use crate::input::Decoded;
use crate::keccak::{State, keccak_f, keccak256_words};
use crate::keccak_gkr::{KeccakOutW, KeccakScratch, keccak_phase};
use crate::layout::{LayoutW, N_TABLES, read_announced_sizes};
use crate::ring_switch::{RingW, ring_switch};
use crate::stack::{ClaimsW, EqClaimW, commit_stack, read_ood};
use crate::tables::{TableEvalW, public_input_phase, table_column_claims, table_phase};
use crate::transcript::TState;
use crate::whir::{ScalesW, WhirW, verify_stacked_opening};

/// The first eight bytes of `leanvm-v1`, little-endian (`tagLow`).
const TAG_LOW: u64 = 0x762d_6d76_6e61_656c;
/// The tag's ninth byte (`tagLast`).
const TAG_LAST: u64 = 0x31;

/// Word `k` of `ivWords bytecode`: `tagLow`, then word `k + 1` the top byte of the previous word of
/// `ext` (the tag's ninth for `k = 0`) and the low seven of word `k`.
#[inline(never)]
fn iv_word(bytecode: &[u64], k: usize) -> u64 {
    let ext = |i: usize| match i {
        0 => TAG_LAST << 56,
        _ => bytecode.get(i - 1).copied().unwrap_or(0),
    };
    if k == 0 { TAG_LOW } else { (ext(k - 1) >> 56) | (ext(k) << 8) }
}

/// `fiatShamirIv`: Keccak-256 of the tag and the bytecode, `9 + 8n` bytes of `ivWords`.
#[inline(always)]
fn fiat_shamir_iv(bytecode: &[u64]) -> [u64; 4] {
    let n = bytecode.len();
    keccak256_words(n + 2, 9 + 8 * n, |k| iv_word(bytecode, k))
}

/// `seed`: Keccak-f of the IV, the public input, zeros.
#[inline(never)]
pub fn seed(bytecode: &[u64], public_input: &[u64; 4]) -> State {
    let iv = fiat_shamir_iv(bytecode);
    let mut state = [0u64; 25];
    state[..4].copy_from_slice(&iv);
    state[4..8].copy_from_slice(public_input);
    keccak_f(&mut state);
    state
}

/// The working area's regions (`NativeVm/Code/Data.lean`'s, but the transcript's, which lives on
/// the stack, and `rowsR`: the opened rows are read in place in the decoded proof).
#[repr(C)]
pub struct Work {
    pub layout: LayoutW,
    pub ood: EqClaimW,
    pub bus: BusW,
    pub evals: [TableEvalW; N_TABLES],
    pub claims: ClaimsW,
    pub keccak: KeccakOutW,
    pub ring: RingW,
    pub scales: ScalesW,
    pub whir: WhirW,
    pub scratch: KeccakScratch,
}

/// **The walk** (`verifyExecution`).
#[inline(never)]
fn verify_execution(t: &mut TState, bytecode: &[u64], public_input: &[u64; 4], w: &mut Work) -> Option<()> {
    // 1] memory log-size, table row counts, and the WHIR rate
    let log_inverse_rate = read_announced_sizes(t, bytecode.len() as u64, &mut w.layout)?;
    let layout = &w.layout;
    // 2] the stack's commitment, and its out-of-domain sample
    commit_stack(t, layout.stack_log, log_inverse_rate)?;
    read_ood(t, layout.stack_log, &mut w.ood)?;
    // 3] the bus
    verify_bus_balance(t, layout, bytecode, &mut w.bus, &mut w.claims)?;
    // 4] the table sumcheck, and the tables' column claims
    table_phase(t, layout, &w.bus, &mut w.evals)?;
    table_column_claims(&w.evals, &mut w.claims)?;
    // 5] the public input
    public_input_phase(t, layout, public_input, &mut w.claims)?;
    // 6] KECCAK validity, by GKR over the rounds
    keccak_phase(t, layout, &w.evals, &mut w.scratch, &mut w.claims, &mut w.keccak)?;
    // 7] ring switching, then one opening of the stack for every claim with a placement
    ring_switch(t, &w.keccak.slices, &mut w.ring)?;
    verify_stacked_opening(t, layout, log_inverse_rate, &w.ring, &w.keccak, &w.claims, &w.ood, &mut w.scales, &mut w.whir)
}

/// **The verifier after decoding** (`verify`): the walk from the seed, accepting when it ends with
/// the stream and the openings consumed.
#[inline(never)]
pub fn verify(bytecode: &[u64], public_input: &[u64; 4], dec: Decoded, w: &mut Work) -> bool {
    let mut t = TState::new(seed(bytecode, public_input), dec);
    match verify_execution(&mut t, bytecode, public_input, w) {
        Some(()) => t.cursor as u64 == dec.stream_len() && t.phase as u64 == dec.phase_count(),
        None => false,
    }
}

/// `EW` and `Buf` appear in `Work`'s field types.
const _: Option<Buf<EW, 0>> = None;
