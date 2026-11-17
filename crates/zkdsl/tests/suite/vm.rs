//! The VM and the prover on programs the Lean back end compiled (`tests/vm/*.py`, `tests/compiled/<name>.txt`, written
//! by `lake exe guest-backend export programs`): what a run computes, how much memory it announces, what it reports,
//! and that its proof verifies.

use crate::common::compiled;
use lean_vm_core::cpu::{execute, prove, verify};
use primitives::field::{F64, F128, g_pow};
use primitives::hash::{STATE_LANES, keccak_f};

/// Prove and verify `program` against the public input `want`.
fn proves(program: &isa::Program, witness: &[(String, Vec<Vec<F128>>)], want: [F128; 2]) {
    let (proof, _) = prove(program, witness, want, lean_vm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(program, &want, &proof).expect("verifies");
}

/// The digest cells of the hash of `bytes`: what a `keccak(...)` output `StackBuf(2)` holds
/// cell-by-cell (lo = word 0/2, hi = word 1/3).
fn hash_cells(bytes: &[u8]) -> [F128; 2] {
    let d = primitives::hash::hash(bytes);
    let word = |o: usize| u64::from_le_bytes(d[o..o + 8].try_into().unwrap());
    [F128::new(word(0), word(8)), F128::new(word(16), word(24))]
}

/// The bytes of cells each holding one small scalar in its low lane.
fn scalar_cells(values: impl IntoIterator<Item = u64>) -> Vec<u8> {
    values
        .into_iter()
        .flat_map(|v| v.to_le_bytes().into_iter().chain(0u64.to_le_bytes()))
        .collect()
}

/// A size-2 `StackBuf` fed to `keccak` as a self-hash `keccak(h, h)`, then the
/// digest's two 128-bit cells published to `m[0], m[1]`: the whole path (StackBuf load →
/// aliased keccak → stack read → publish) is exercised end-to-end.
#[test]
fn stack_buf_keccak_self_hash() {
    let program = compiled("keccak_self_hash");
    // Each cell holds one scalar in its low lane.
    let want = hash_cells(&scalar_cells([5, 7, 5, 7]));
    let (proof, _) = prove(&program, &[], want, lean_vm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    assert_eq!(
        execute(&program, &[], want).unwrap().rows()[5],
        1,
        "one KECCAK instruction"
    );
    verify(&program, &want, &proof).expect("StackBuf self-hash verifies");
}

/// A 304-byte message is three blocks: a block pair of seventeen cells absorbed with no
/// padding, the second block starting halfway through the ninth cell, then a final
/// block from the state carried between them.
#[test]
fn keccak_two_blocks() {
    let program = compiled("keccak_two_blocks");
    let want = hash_cells(&scalar_cells(1..=19));
    assert_eq!(execute(&program, &[], want).unwrap().rows()[5], 3);
    proves(&program, &[], want);
}

/// A message on either side of a block's end, 135 and 136 bytes: the padding's last
/// byte in lane 16 of the first block's ninth cell, or the padding a second block,
/// odd, its first byte in that cell's high lane. The program asserts the 136-byte digest, written into it as literals.
#[test]
fn keccak_full_final_block() {
    let mut bytes = scalar_cells(1..=9);
    bytes.truncate(135);
    proves(&compiled("keccak_full_final_block"), &[], hash_cells(&bytes));
}

/// `keccak_cells` hashes a whole run: 20 cells, 320 bytes, are three blocks, the last
/// (block 2) even, and a heap run of 16 is two, whose digest the program asserts as literals.
#[test]
fn keccak_cells_hashes_the_run() {
    proves(&compiled("keccak_cells_run"), &[], hash_cells(&scalar_cells(1..=20)));
}

/// A state carried through the heap, the shape a hash in a runtime loop has: the
/// first block pair writes its 13-cell output to a heap run, the final block reads it
/// back as its `state`.
#[test]
fn keccak_state_through_the_heap() {
    proves(&compiled("keccak_state_heap"), &[], hash_cells(&scalar_cells(1..=19)));
}

/// One overwrite-mode duplex step: lanes `0..16` are `rate` then zeros, lanes `16..25`
/// carry over. Returns the challenge, the output's first two lanes.
fn duplex(state: &mut [u64; STATE_LANES], rate: &[u64]) -> F128 {
    state[..16].fill(0);
    state[..rate.len()].copy_from_slice(rate);
    keccak_f(state);
    F128::new(state[0], state[1])
}

/// The recursion guest's Fiat-Shamir step, written as it is there: a scalar packed into
/// the rate, a `keccak(.., cap=)` duplex step, and a challenge read off the output,
/// against the duplex sponge of `fiat_shamir_prover::FiatShamirState`. The program's capacity cells are the literals of
/// the state below, as the VM reads them: lane 16 alone, then lanes 17..25 two a cell; its scalar is `(5, 6)`.
#[test]
fn guest_transcript_step_matches_the_native_duplex() {
    let mut state: [u64; STATE_LANES] = std::array::from_fn(|i| 0x9e37_79b9_7f4a_7c15u64.wrapping_mul(i as u64 + 1));
    keccak_f(&mut state);
    // A scalar rides its four lanes as `[c0, c1, 0, tag]`.
    let first = duplex(&mut state, &[5, 6, 0, 1]);
    let second = duplex(&mut state, &[]);

    let program = compiled("duplex_step");
    execute(&program, &[], [first, second]).expect("the guest's step is the native duplex");
    let wrong = second + F128::new(1, 0);
    assert!(execute(&program, &[], [first, wrong]).is_err());
}

/// A check whose two touched cells (`m[300]` and the complement's `m[99]`) are
/// never written by the program: their `DEREF`s only link them to fresh cells,
/// all of which stay ZERO, and the bus still balances.
#[test]
fn range_check_unwritten_cells() {
    let want = [F128::from(g_pow(300)), F128::from(g_pow(300))];
    proves(&compiled("range_check_unwritten"), &[], want);
}

/// The complement read sizes the memory: with `x = g^0`, a bound `k` touches `g^{k-1}`,
/// so the run announces the least power of two above `k - 1` cells, exactly `2^16` at
/// `k = 2^16` and `2^17` one past it. An off-by-one in the bound or in the memory size
/// shows up here. The Lean back end refuses a compile-time bound past `2^16`, so the bound
/// past it rides a hint (`assert log x < log n`), as does the same `2^16` again.
#[test]
fn range_check_complement_sizes_the_memory() {
    let want = [F128::from(g_pow(0)); 2];
    let runtime = compiled("range_check_complement_runtime");
    let hinted = |k: usize| vec![("n".to_string(), vec![vec![F128::from(g_pow(k))]])];
    for (program, witness, k, log_mem) in [
        (&compiled("range_check_complement_65536"), vec![], 65536, 16),
        (&runtime, hinted(65536), 65536, 16),
        (&runtime, hinted(65537), 65537, 17),
    ] {
        let (proof, stats) = prove(program, &witness, want, lean_vm_core::pcs::TEST_LOG_INV_RATE).unwrap();
        assert_eq!(stats.memory_used.next_power_of_two().ilog2(), log_mem, "bound {k}");
        verify(program, &want, &proof).unwrap_or_else(|e| panic!("bound {k}: {e:?}"));
    }
}

/// A bound whose complement lies past this prover's address space (here a hinted one)
/// compiles (the protocol admits it) and the run is refused with an error, not a panic.
#[test]
fn range_check_bound_past_the_prover_is_an_error() {
    let program = compiled("range_check_past_the_prover");
    let witness = [("n".to_string(), vec![vec![F128::from(g_pow(268435472))]])];
    match execute(&program, &witness, [F128::ZERO; 2]) {
        Err(err) => assert!(
            matches!(err.fault, lean_vm_core::cpu::Fault::WildPointer { .. }),
            "{err}"
        ),
        Ok(_) => panic!("a run past the prover's address space"),
    }
}

/// A g-power reached only through a hint, past every cell the run otherwise touches:
/// `assert_gpow` on it, and a runtime bound whose complement lies beyond it, prove.
#[test]
fn hinted_gpow_past_the_run_proves() {
    let program = compiled("hinted_gpow_past_the_run");
    let witness = [("n".to_string(), vec![vec![F128::from(g_pow(5000))]])];
    let want = [F128::from(g_pow(3)); 2];
    let (proof, stats) = prove(&program, &witness, want, lean_vm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    assert_eq!(stats.memory_used.next_power_of_two().ilog2(), 13);
    verify(&program, &want, &proof).expect("hinted g-power range checks verify");
}

fn log2_ceil_of(v: u128) -> usize {
    if v <= 1 {
        0
    } else {
        (128 - (v - 1).leading_zeros()) as usize
    }
}

/// `hint_log2_ceil(bits, nbits, floor)`: computed advice returning `g^max(log2_ceil(v), floor)`,
/// where `v` is the integer the `bits` buffer decodes to. The prover fills it at
/// witness-generation; it is unconstrained on its own, so this checks only that the
/// advice computes the right value.
#[test]
fn log2_ceil_advice_computes_the_log() {
    let program = compiled("log2_ceil");
    for v in [1u128, 2, 3, 4, 5, 7, 8, 200] {
        let bits: Vec<F128> = (0..8).map(|j| F128::from(F64(((v >> j) & 1) as u64))).collect();
        let witness = [("bits".to_string(), vec![bits])];
        let want = [F128::from(g_pow(log2_ceil_of(v))), F128::from(F64::ONE)];
        let (proof, _) = prove(&program, &witness, want, lean_vm_core::pcs::TEST_LOG_INV_RATE).unwrap();
        verify(&program, &want, &proof).unwrap_or_else(|_| panic!("v={v}: log2_ceil advice must verify"));
    }
}

/// The `floor` argument: `max(log2_ceil(v), floor)`. With floor = 5, small
/// values are lifted to g^5.
#[test]
fn log2_ceil_advice_floor() {
    let program = compiled("log2_ceil_floor");
    for (v, mu) in [(2u128, 5usize), (4, 5), (64, 6), (200, 8)] {
        let bits: Vec<F128> = (0..8).map(|j| F128::from(F64(((v >> j) & 1) as u64))).collect();
        let witness = [("bits".to_string(), vec![bits])];
        let want = [F128::from(g_pow(mu)), F128::from(F64::ONE)];
        let (proof, _) = prove(&program, &witness, want, lean_vm_core::pcs::TEST_LOG_INV_RATE).unwrap();
        verify(&program, &want, &proof).unwrap_or_else(|_| panic!("v={v}: floored log2_ceil must verify"));
    }
}

/// `a / b` and `1 / b` over runtime values: one `MUL` whose quotient operand is left unset, which the write-once
/// back-solve fills with `a · b⁻¹`. The quotient satisfies `q·b == a`, checked by publishing it and reproducing the
/// dividend.
#[test]
fn field_div_end_to_end() {
    // q·b must reproduce a = g^20; r·b must be 1.
    let want = [F128::from(g_pow(20)), F128::from(F64::ONE)];
    proves(&compiled("field_div"), &[], want);
}

/// `print(...)`: a prover-side debug print executes during witness generation and leaves proving and verification
/// untouched.
#[test]
fn print_is_constraint_free() {
    let want = [F128::from(F64(5) * primitives::field::g_pow(1)), F128::from(F64(3))];
    proves(&compiled("print"), &[], want);
}

/// A heap cell nothing stores to is prover-chosen, so using a value loaded from it
/// is an unconstrained read, exactly as for a stack cell.
#[test]
fn a_load_of_an_unwritten_heap_cell_is_an_unconstrained_read() {
    let exec = execute(&compiled("unwritten_heap_read"), &[], [F128::ZERO; 2]).unwrap();
    assert!(!exec.unconstrained_reads.is_empty());
}

/// A `HeapBuf` sized at run time is bounded by the address space alone, not by how far the g-power table happens to
/// reach.
#[test]
fn heap_buf_runtime_size_beyond_the_g_power_table() {
    let program = compiled("heap_buf_runtime_size");
    let size = (1 << 20) + 1;
    let exec = execute(&program, &[], [F128::from(g_pow(size)), F128::from(g_pow(size - 1))]).unwrap();
    assert!(exec.unconstrained_reads.is_empty());
    assert!(exec.mem_used > size);
}

/// A check that fails at witness generation names its source line, which is the one that
/// matters day to day: a failed guest `assert` surfaces as a write-once conflict.
#[test]
fn a_failed_assert_names_its_source_line() {
    // 1 blank, 2 def, 3 let, 4 blank, 5 the assert that cannot hold.
    let err = execute(&compiled("failed_assert"), &[], [F128::ZERO; 2])
        .err()
        .expect("the assert cannot hold");
    assert!(err.site.contains("line 5"), "{err}");
}
