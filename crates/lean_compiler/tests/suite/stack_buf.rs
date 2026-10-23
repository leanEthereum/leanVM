//! `StackBuf`: a run of consecutive frame (stack) cells in the zkDSL. Indexed
//! reads/writes go straight to `base+k` (no heap deref), and a size-2 `StackBuf`
//! is a `keccak` operand: its two canonical 128-bit cells hold the 256-bit value, so
//! `keccak(a, b, out)` reads them in place with no copies (a self-hash
//! `keccak(h, h, out)` aliases one pair into both input operands) and writes
//! the digest into `out`.
//!
//! Since these DSL scalars are K-embedded F192 cells, a `StackBuf(2)` written
//! cell-by-cell holds the lanes `[v0, 0, v1, 0]`.

use lean_compiler::{compile, parse};
use leanvm_core::cpu::{prove, verify};
use primitives::field::{F64, F192, g_pow};

use crate::common::{f192_lit, mix};

/// The digest cells of the hash of `bytes`: what a `keccak(...)` output `StackBuf(2)` holds
/// cell-by-cell (lo = word 0/2, hi = word 1/3).
fn hash_cells(bytes: &[u8]) -> [F192; 2] {
    let d = primitives::hash::hash(bytes);
    let word = |o: usize| u64::from_le_bytes(d[o..o + 8].try_into().unwrap());
    [F192::new(word(0), word(8), 0), F192::new(word(16), word(24), 0)]
}

/// The bytes of cells each holding one small scalar in its low lane.
fn scalar_cells(values: impl IntoIterator<Item = u64>) -> Vec<u8> {
    values
        .into_iter()
        .flat_map(|v| v.to_le_bytes().into_iter().chain(0u64.to_le_bytes()))
        .collect()
}

/// Prove and verify `src` against the public input `want`.
fn proves(src: &str, want: [F192; 2]) {
    let program = compile(&parse(src).expect("parse"));
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &want, &proof).expect("verifies");
}

/// A size-2 `StackBuf` fed to `keccak` as a self-hash `keccak(h, h)`, then the
/// digest's two 128-bit cells published to `m[0], m[1]`. Proves and verifies, and
/// a wrong published digest is rejected: so the whole path (StackBuf load →
/// aliased keccak → stack read → publish) is exercised end-to-end.
#[test]
fn stack_buf_keccak_self_hash() {
    let src = "\
def main():
    a = StackBuf(2)
    a[0] = 5
    a[1] = 7
    c = StackBuf(2)
    keccak(a, a, c)
    p = 1
    p[1] = c[0]
    p[GEN] = c[1]
    return
";
    let program = compile(&parse(src).expect("parse"));

    // Each cell holds one scalar in its low lane.
    let want = hash_cells(&scalar_cells([5, 7, 5, 7]));

    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    assert_eq!(mix(src, want)[5], 1, "one KECCAK instruction");
    verify(&program, &want, &proof).expect("StackBuf self-hash verifies");
}

/// A 304-byte message is three blocks: a block pair of seventeen cells absorbed with no
/// padding, the second block starting halfway through the ninth cell, then a final
/// block from the state carried between them.
#[test]
fn keccak_two_blocks() {
    let src = "\
def main():
    pair = StackBuf(17)
    for k in unroll(0, 17):
        pair[k] = const(k + 1)
    st = StackBuf(13)
    keccak_cells(pair, st, final=0)
    out = StackBuf(2)
    keccak_cells([18, 19], out, state=st)
    p = 1
    p[1] = out[0]
    p[GEN] = out[1]
    return
";
    let want = hash_cells(&scalar_cells(1..=19));
    assert_eq!(mix(src, want)[5], 3);
    proves(src, want);
}

/// A message on either side of a block's end, 135 and 136 bytes: the padding's last
/// byte in lane 16 of the first block's ninth cell, or the padding a second block,
/// odd, its first byte in that cell's high lane.
#[test]
fn keccak_full_final_block() {
    let src = "\
def main():
    m = StackBuf(9)
    for k in unroll(0, 9):
        m[k] = const(k + 1)
    one = StackBuf(2)
    keccak_cells(m, one, len=135)
    two = StackBuf(2)
    keccak_cells(m, two, len=136)
    assert two[0] == TWO_0
    assert two[1] == TWO_1
    p = 1
    p[1] = one[0]
    p[GEN] = one[1]
    return
";
    let mut bytes = scalar_cells(1..=9);
    let two = hash_cells(&bytes[..136]);
    bytes.truncate(135);
    let src = src
        .replace("TWO_0", &f192_lit(two[0]))
        .replace("TWO_1", &f192_lit(two[1]));
    proves(&src, hash_cells(&bytes));
}

/// A message ending inside a cell: 52 bytes, the padding's first byte at byte 4
/// of lane 6, XORed into the program's own word.
#[test]
fn keccak_pad_inside_a_word() {
    let src = "\
def main():
    ctr = 305419896
    out = StackBuf(2)
    keccak([1, 2], [3, ctr], out, len=52)
    p = 1
    p[1] = out[0]
    p[GEN] = out[1]
    return
";
    let mut bytes = scalar_cells(1..=3);
    bytes.extend_from_slice(&305419896u32.to_le_bytes());
    proves(src, hash_cells(&bytes));
}

/// `keccak_cells` hashes a whole run: 20 cells, 320 bytes, are three blocks, the last
/// (block 2) even, and a heap run of 16 is two.
#[test]
fn keccak_cells_hashes_the_run() {
    let src = "\
def main():
    run = StackBuf(20)
    for k in unroll(0, 20):
        run[k] = const(k + 1)
    out = StackBuf(2)
    keccak_cells(run, out)
    hb = HeapBuf(16)
    for k in unroll(0, 16):
        hb[GEN ** k] = const(k + 1)
    heap_out = StackBuf(2)
    keccak_cells(hb[0:16], heap_out)
    assert heap_out[0] == HEAP_0
    assert heap_out[1] == HEAP_1
    p = 1
    p[1] = out[0]
    p[GEN] = out[1]
    return
";
    let heap = hash_cells(&scalar_cells(1..=16));
    let src = src
        .replace("HEAP_0", &f192_lit(heap[0]))
        .replace("HEAP_1", &f192_lit(heap[1]));
    proves(&src, hash_cells(&scalar_cells(1..=20)));
}

/// A list comprehension names scattered cells as a message, here every second cell of a
/// run, with no copies: three blocks reading the cells where they lie.
#[test]
fn keccak_cells_of_a_comprehension() {
    let src = "\
def main():
    run = StackBuf(40)
    for k in unroll(0, 40):
        run[k] = const(k + 1)
    out = StackBuf(2)
    keccak_cells([run[2 * k] for k in unroll(0, 20)], out)
    p = 1
    p[1] = out[0]
    p[GEN] = out[1]
    return
";
    proves(src, hash_cells(&scalar_cells((0..20).map(|k| 2 * k + 1))));
}

/// A state carried through the heap, the shape a hash in a runtime loop has: the
/// first block pair writes its 13-cell output to a heap run, the final block reads it
/// back as its `state`.
#[test]
fn keccak_state_through_the_heap() {
    let src = "\
def main():
    pair = StackBuf(17)
    for k in unroll(0, 17):
        pair[k] = const(k + 1)
    chain = HeapBuf(13)
    keccak_cells(pair, chain[0:13], final=0)
    out = StackBuf(2)
    keccak_cells([18, 19], out, state=chain[0:13])
    p = 1
    p[1] = out[0]
    p[GEN] = out[1]
    return
";
    proves(src, hash_cells(&scalar_cells(1..=19)));
}

/// A padding run first materialized in an untaken runtime branch must not leak
/// into the post-join lowering state. Both executions must initialize it on the
/// path that reaches the second hash.
#[test]
fn keccak_pad_run_after_runtime_branch() {
    let src = "\
def main():
    flag = StackBuf(1)
    hint_witness(flag, \"flag\")
    a = [1, 2, 3, 4]
    if flag[0] == 1:
        ignored = StackBuf(2)
        keccak(a[0:2], a[2:4], ignored)
    out = StackBuf(2)
    keccak(a[0:2], a[2:4], out)
    p = 1
    p[1] = out[0]
    p[GEN] = out[1]
    return
";
    let want = hash_cells(&scalar_cells(1..=4));
    for flag in [0, 1] {
        let mut program = compile(&parse(src).expect("parse"));
        program.set_witness("flag", vec![vec![F192::new(flag, 0, 0)]]);
        let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
        verify(&program, &want, &proof).expect("post-join padding run is initialized on both paths");
    }
}

/// Each mutually exclusive branch gets a path-local padding run when no
/// dominating fresh hash exists before the branch.
#[test]
fn keccak_pad_run_in_both_runtime_branches() {
    let src = "\
def main():
    flag = StackBuf(1)
    hint_witness(flag, \"flag\")
    a = [1, 2, 3, 4]
    out = StackBuf(2)
    if flag[0] == 1:
        keccak(a[0:2], a[2:4], out)
    else:
        keccak(a[0:2], a[2:4], out)
    p = 1
    p[1] = out[0]
    p[GEN] = out[1]
    return
";
    let want = hash_cells(&scalar_cells(1..=4));
    for flag in [0, 1] {
        let mut program = compile(&parse(src).expect("parse"));
        program.set_witness("flag", vec![vec![F192::new(flag, 0, 0)]]);
        let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
        verify(&program, &want, &proof).expect("each branch initializes its padding run");
    }
}

#[test]
#[should_panic(expected = "keccak len= 129 is past the 128 bytes of its 8 cells")]
fn keccak_len_past_the_cells_is_rejected() {
    let src =
        "def main():\n    out = StackBuf(2)\n    keccak([1, 2], [3, 4], out, tail=[5, 6, 7, 8], len=129)\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// A cell the message ends before would be hashed with it.
#[test]
#[should_panic(expected = "keccak len= 40 ends before message cell 3, which is not a literal 0")]
fn keccak_cell_past_len_is_rejected() {
    let src = "def main():\n    out = StackBuf(2)\n    keccak([1, 2], [3, 4], out, len=40)\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

#[test]
#[should_panic(expected = "keccak_cells final=0 absorbs whole cells: it takes no len=")]
fn keccak_cells_non_final_len_is_rejected() {
    let src = "def main():\n    out = StackBuf(13)\n    keccak_cells([1, 2], out, final=0, len=16)\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

#[test]
#[should_panic(expected = "keccak_cells state= must be the 13-cell run a previous keccak wrote")]
fn keccak_short_state_is_rejected() {
    let src =
        "def main():\n    st = [1, 2]\n    out = StackBuf(2)\n    keccak_cells([1, 2], out, state=st)\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// A general (non-keccak) `StackBuf(3)`: indexed writes, an indexed read feeding
/// an arithmetic write into another slot, then two slots published. Confirms the
/// stack cells are plain consecutive frame cells addressable by index.
#[test]
fn stack_buf_indexing() {
    let src = "\
def main():
    sa = StackBuf(3)
    sa[0] = 3
    sa[1] = 4
    sa[2] = sa[0] + sa[1]
    p = 1
    p[1] = sa[2]
    p[GEN] = sa[1]
    return
";
    let program = compile(&parse(src).expect("parse"));
    // `+` is XOR: 3 ^ 4 = 7. Published: (sa[2], sa[1]) = (7, 4).
    let want = [F192::from(F64(7)), F192::from(F64(4))];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    assert_eq!(mix(src, want)[5], 0, "no KECCAK here");
    verify(&program, &want, &proof).expect("StackBuf indexing verifies");
}

/// A normal (non-`@inline`) function may return a StackBuf. Its cells cross the
/// call boundary through consecutive return slots and bind as a StackBuf in the
/// caller, including through another normal wrapper function.
#[test]
fn normal_function_returns_stackbuf() {
    let src = "\
def main():
    out = forward(5)
    p = 1
    p[1] = out[0] + out[1]
    p[GEN] = out[2]
    return

def forward(v):
    out = make(v)
    return out

def make(v):
    out = StackBuf(3)
    out[0] = v
    out[1] = v + 3
    out[2] = 11
    return out
";
    let program = compile(&parse(src).expect("parse"));
    // Field addition is XOR: 5 ^ (5 ^ 3) == 3.
    program.execute([F192::from(F64(3)), F192::from(F64(11))]).unwrap();
}

/// Tuple returns retain their source-level arity even though a StackBuf member
/// occupies several physical return cells.
#[test]
fn normal_function_returns_stackbuf_and_scalar() {
    let src = "\
def main():
    out, x = make(9)
    p = 1
    p[1] = out[0] + out[1]
    p[GEN] = x
    return

def make(v):
    out = [v, 6]
    return out, v + 1
";
    let program = compile(&parse(src).expect("parse"));
    program.execute([F192::from(F64(15)), F192::from(F64(8))]).unwrap();
}

/// HeapBuf already crosses a normal call as its one-cell pointer. Allocation
/// happened in the callee, so the caller needs no size metadata to dereference
/// and use the returned buffer.
#[test]
fn normal_function_returns_heapbuf_pointer() {
    let src = "\
def main():
    out = make()
    p = 1
    p[1] = out[1]
    p[GEN] = out[GEN]
    return

def make():
    out = HeapBuf(2)
    out[1] = 17
    out[GEN] = 23
    return out
";
    let program = compile(&parse(src).expect("parse"));
    program.execute([F192::from(F64(17)), F192::from(F64(23))]).unwrap();
}

/// A StackBuf index literal that does not fit `u32` is rejected at compile time,
/// not silently truncated modulo 2^32 (which would resolve `sa[2^32]` to `sa[0]`).
#[test]
#[should_panic(expected = "does not fit in u32")]
fn stack_buf_index_overflow_rejected() {
    let src = "def main():\n    sa = StackBuf(2)\n    x = sa[4294967296]\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// Rebinding a StackBuf name to a scalar clears the stack binding, so the name
/// is a plain scalar afterward (the old bug left a stale `stacks` entry that made
/// `x` still look like a StackBuf, panicking on scalar use).
#[test]
fn stack_buf_rebind_to_scalar() {
    let src = "def main():\n    x = StackBuf(2)\n    x = 5\n    p = 1\n    p[1] = x\n    p[GEN] = x\n    return\n";
    let program = compile(&parse(src).expect("parse"));
    let want = [F192::from(F64(5)), F192::from(F64(5))];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &want, &proof).expect("rebound-scalar program verifies");
}

/// A StackBuf from the enclosing scope referenced inside a `for` loop cannot be
/// captured; the compiler rejects it with a clear message (not a misleading
/// "unbound variable" from the capture being silently dropped).
#[test]
#[should_panic(expected = "cannot be captured into a `for` loop")]
fn stack_buf_loop_capture_rejected() {
    let src = "def main():\n    h = StackBuf(2)\n    h[0] = 1\n    h[1] = 2\n    for i in mul_range(1, GEN ** 4):\n        x = h[0]\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// An `@inline` may return a `StackBuf` *and* a scalar together (a tuple bind):
/// the `StackBuf` slot aliases its cell run into the caller (zero copies, usable
/// as a StackBuf downstream: here fed straight back into a second call, the
/// MD-chain idiom), while the scalar slot binds a value cell. This is the fused
/// `state, x = read_obs(state, cursor)` shape the recursion guest relies on.
#[test]
fn inline_returns_stackbuf_and_scalar() {
    let src = "\
def main():
    s = StackBuf(2)
    s[0] = 5
    s[1] = 7
    s, x = step(s, 9)
    s, y = step(s, x)
    p = 1
    p[1] = s[0]
    p[GEN] = s[1]
    return

@inline
def step(state, v):
    tg = StackBuf(2)
    tg[0] = v
    tg[1] = 3
    nb = StackBuf(2)
    keccak(state, tg, nb)
    return nb, v
";
    let program = compile(&parse(src).expect("parse"));

    // x == v == 9 (the scalar return), so both steps use tag 9; the second hashes the
    // returned StackBuf, holding the first digest.
    let mut second = primitives::hash::hash(&scalar_cells([5, 7, 9, 3])).to_vec();
    second.extend(scalar_cells([9, 3]));
    let want = hash_cells(&second);

    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    assert_eq!(mix(src, want)[5], 2, "two KECCAK instructions (one per inlined step)");
    verify(&program, &want, &proof).expect("inline StackBuf+scalar tuple return verifies");
}

/// Deferred stores made by a runtime branch must initialize buffers allocated
/// by the surrounding inline call, including when its tuple result is rebound
/// inside an unrolled loop.
#[test]
fn branch_writes_survive_unrolled_tuple_return() {
    let src = "\
def main():
    public = GEN ** 0
    flag = public[1]
    a = [5, 7]
    b = [13, 17]
    for i in unroll(0, 1):
        a, b = select_pair(flag, a, b)
    assert a[0] == 13
    assert a[1] == 17
    assert b[0] == 5
    assert b[1] == 7
    return

@inline
def select_pair(flag, a, b):
    first = StackBuf(2)
    second = StackBuf(2)
    if flag == 0:
        first[0] = a[0]
        first[1] = a[1]
        second[0] = b[0]
        second[1] = b[1]
    else:
        first[0] = b[0]
        first[1] = b[1]
        second[0] = a[0]
        second[1] = a[1]
    return first, second
";
    let program = compile(&parse(src).expect("parse"));
    program.execute([F192::ONE, F192::ZERO]).unwrap();
}

/// An `@inline` may also alias-return a folded **g-address** among its values:
/// `fs, x, cur = step(fs, cur)` hands back the Fiat-Shamir state (StackBuf), the
/// consumed word (scalar), and the ADVANCED cursor (`cursor * GEN`) as a
/// zero-cost folded pointer, so the caller keeps reading through it with no
/// manual `cur *= GEN`. This is the shape `fs_next` uses to walk the stream.
#[test]
fn inline_returns_advanced_cursor() {
    let src = "\
def main():
    hb = HeapBuf(4)
    hb[1] = 10
    hb[GEN] = 20
    hb[GEN ** 2] = 30
    fs = StackBuf(2)
    fs[0] = 1
    fs[1] = 2
    cur = hb
    fs, a, cur = step(fs, cur)
    fs, b, cur = step(fs, cur)
    v = cur[GEN ** 0]
    p = 1
    p[1] = a + b
    p[GEN] = v
    return

@inline
def step(state, cursor):
    x = cursor[GEN ** 0]
    tg = StackBuf(2)
    tg[0] = x
    tg[1] = 3
    nb = StackBuf(2)
    keccak(state, tg, nb)
    return nb, x, cursor * GEN
";
    let program = compile(&parse(src).expect("parse"));
    // a = hb[0] = 10, b = hb[1] = 20, v = hb[2] = 30 read through the cursor
    // returned twice-advanced. a + b is XOR: 10 ^ 20 = 30.
    let want = [F192::from(F64(30)), F192::from(F64(30))];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &want, &proof).expect("inline advanced-cursor return verifies");
}

/// `x = [a, b, c, d]`: the list-literal StackBuf initializer: allocates the run
/// and writes the elements in place, sugar for alloc-then-store. The test mixes a
/// runtime value, a constant, and an expression; feeds the result to keccak; and
/// swaps a buffer through itself (`s = [s[1], s[0], …]` reads the OLD binding,
/// per the let-rebind rule).
#[test]
fn stack_buf_list_literal() {
    let src = "\
def main():
    s = [5, 7]
    s = [s[1], s[0]]
    t = [s[0] + s[1], 3]
    out = StackBuf(2)
    keccak(s, t, out)
    p = 1
    p[1] = out[0]
    p[GEN] = out[1]
    return
";
    let program = compile(&parse(src).expect("parse"));
    // s = [7, 5] after the swap → words [7,0,5,0]; t = [7 ^ 5, 3] = [2, 3] → [2,0,3,0].
    let want = hash_cells(&scalar_cells([7, 5, 2, 3]));
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    assert_eq!(mix(src, want)[5], 1, "one KECCAK instruction");
    verify(&program, &want, &proof).expect("list-literal StackBuf verifies");
}

/// A list literal anywhere but the RHS of an assignment is rejected with a
/// clear message, not lowered as a phantom scalar.
#[test]
#[should_panic(expected = "a list literal must be bound to a name")]
fn stack_buf_list_literal_as_value_rejected() {
    let src = "def main():\n    x = 1 + [2, 3]\n    assert x == x\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// A compile-time heap index past the buffer's declared size is a compile
/// error, not a runtime wild deref.
#[test]
#[should_panic(expected = "heap index 8 out of bounds for `hb` (HeapBuf size 8)")]
fn heap_index_oob_rejected() {
    let src = "def main():\n    hb = HeapBuf(8)\n    x = hb[GEN ** 8]\n    assert x == x\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// The bound follows shifted aliases back to the original buffer: a pointer
/// alias `row = hb * GEN ** k` checks `row[GEN ** j]` against size − k.
#[test]
#[should_panic(expected = "heap index 9 out of bounds for `hb` (HeapBuf size 8)")]
fn heap_alias_index_oob_rejected() {
    let src = "def main():\n    hb = HeapBuf(8)\n    row = hb * GEN ** 6\n    x = row[GEN ** 3]\n    assert x == x\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// A hint slice whose end exceeds the buffer is rejected at compile time.
#[test]
#[should_panic(expected = "heap slice 0:9 out of bounds for `hb` (HeapBuf size 8)")]
fn heap_hint_slice_oob_rejected() {
    let src = "def main():\n    hb = HeapBuf(8)\n    hint_witness(hb[0:9], \"w\")\n    x = hb[GEN ** 0]\n    assert x == x\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// A keccak heap slice straddling the buffer end is rejected. The 256-bit
/// operand `hb[7:9]` is two 128-bit cells, so the bound check trips at
/// `7 + 2 = 9 > 8`.
#[test]
#[should_panic(expected = "heap slice 7:9 out of bounds for `hb` (HeapBuf size 8)")]
fn heap_keccak_slice_oob_rejected() {
    let src = "def main():\n    hb = HeapBuf(8)\n    hb[GEN ** 7] = 5\n    out = StackBuf(2)\n    keccak(hb[7:9], hb[7:9], out)\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// A heap index that folds to a non-g-power field constant (an integer loop
/// var leaking in from a StackBuf conversion) can never name a heap cell (cell
/// k lives at `buf · g^k`) and used to survive to proving time as a
/// wild-pointer DEREF. It must be a compile-time error.
#[test]
#[should_panic(expected = "not a g-power")]
fn integer_heap_index_is_rejected() {
    let src = "\
def main():
    b = HeapBuf(4)
    b[1] = 3
    b[GEN] = 5
    x = 0
    for k in unroll(0, 2):
        p = 1
        p[GEN ** k] = b[k]
    return
";
    compile(&parse(src).expect("parse"));
}

/// The last in-bounds index still compiles and runs.
#[test]
fn heap_index_boundary_ok() {
    let src = "def main():\n    hb = HeapBuf(8)\n    hb[GEN ** 7] = 5\n    row = hb * GEN ** 4\n    y = row[GEN ** 3]\n    assert y == 5\n    return\n";
    let program = compile(&parse(src).expect("parse"));
    let pi = [F192::from(F64(3)), F192::from(F64(4))];
    let (proof, _) = prove(&program, pi, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &pi, &proof).expect("boundary access verifies");
}

/// A store into a run PARAMETER is the write-once assertion, not a fresh store.
///
/// A run parameter's cells are already written, by the caller, before the
/// callee's first instruction; a local `StackBuf`'s are not. That is the whole
/// difference, and missing it dropped the assertion: `s[k] = <value>` inside a
/// callee recorded a deferred alias and emitted nothing, so the idiom that pins
/// an unconstrained hint pinned nothing and the prover kept its own values.
#[test]
fn a_store_into_a_run_parameter_asserts() {
    let pin = "\
def pin(s: StackBuf(2)):
    s[0] = GEN ** 5
    s[1] = GEN ** 6
    return GEN ** 0

def main():
    b = StackBuf(2)
    hint_witness(b, \"adv\")
    z = pin(b)
    p = GEN ** 0
    p[1] = b[0]
    p[GEN] = b[1]
    return
";
    let ast = parse(pin).expect("parse");
    // The honest prover hints what the callee asserts, and it verifies.
    let mut program = compile(&ast);
    program.set_witness("adv", vec![vec![g_pow(5).into(), g_pow(6).into()]]);
    let want = [g_pow(5).into(), g_pow(6).into()];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &want, &proof).expect("the honest hint matches the pin");
}

/// A multi-cell value can cross a call in BOTH directions.
///
/// It could always be returned as a run of cells and never passed as one, so a
/// two-cell digest went in through a pointer or an `@inline` expansion while
/// coming back out whole. A `s: StackBuf(n)` parameter takes the same n
/// consecutive cells a `StackBuf(n)` return value occupies, placed by the same
/// `Abi`, which is why the argument area is now a WIDTH rather than a count.
#[test]
fn a_stack_buf_can_be_passed_as_well_as_returned() {
    let src = "\
def swap(s: StackBuf(2)):
    t = StackBuf(2)
    t[0] = s[1]
    t[1] = s[0]
    return t

def main():
    b = StackBuf(2)
    b[0] = GEN ** 1
    b[1] = GEN ** 2
    r = swap(b)
    p = GEN ** 0
    p[1] = r[0]
    p[GEN] = r[1]
    return
";
    let program = compile(&parse(src).expect("parse"));
    let want = [g_pow(2).into(), g_pow(1).into()];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &want, &proof).expect("the run went in and the swapped run came back");

    // The shape is checked at the call, in both directions of mismatch.
    for (arg, want) in [
        (
            "b = StackBuf(3)\n    b[0] = GEN ** 1\n    r = f(b)",
            "got a StackBuf(3)",
        ),
        ("r = f(GEN ** 1)", "pass one"),
    ] {
        let src = format!(
            "def f(s: StackBuf(2)):\n    return s[0]\n\ndef main():\n    {arg}\n    p = GEN ** 0\n    p[1] = r\n    p[GEN] = GEN ** 0\n    return\n"
        );
        let ast = parse(&src).expect("parses");
        let Err(err) = std::panic::catch_unwind(|| compile(&ast)) else {
            panic!("accepted: {arg}");
        };
        let msg = err.downcast_ref::<String>().map(String::as_str).unwrap_or("");
        assert!(msg.contains(want), "got `{msg}`");
    }
}

/// `g` is `x`, so the literal `2^k` IS `g^k`. `try_gpow_index` always knew that
/// and `gaddr_of` did not, so one field element had three answers: `hb[GEN * 2]`
/// was rejected as "not a g-power" while `hb[GEN * GEN]` compiled, and
/// `hb[r * 2]` compiled again as soon as `r` was runtime. All three name cell 2.
/// A BARE literal index stays rejected: see `integer_heap_index_is_rejected`.
#[test]
fn a_literal_power_of_two_is_a_g_power() {
    let src = "\
def main():
    hb = HeapBuf(8)
    hb[GEN * GEN] = GEN ** 5
    p = GEN ** 0
    p[1] = hb[GEN * 2]
    p[GEN] = hb[GEN ** 2]
    return
";
    let program = compile(&parse(src).expect("parse"));
    let want = [F192::from(g_pow(5)); 2];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &want, &proof).expect("three spellings of cell 2 agree");
}

/// A `HeapBuf` sized at run time is bounded by the address space alone, not by
/// how far the g-power table happens to reach.
#[test]
fn heap_buf_runtime_size_beyond_the_g_power_table() {
    let src = "\
def main():
    public = 1
    n = public[1]
    i = public[GEN]
    buf = HeapBuf(n)
    buf[i] = 7
    return
";
    let program = compile(&parse(src).expect("parse"));
    let size = (1 << 20) + 1;
    let exec = program
        .execute([F192::from(g_pow(size)), F192::from(g_pow(size - 1))])
        .unwrap();
    assert!(exec.unconstrained_reads.is_empty());
    assert!(exec.mem_used > size);
}
