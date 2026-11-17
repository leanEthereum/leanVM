//! `StackBuf`: a run of consecutive frame (stack) cells in the zkDSL. Indexed
//! reads/writes go straight to `base+k` (no heap deref), and a size-2 `StackBuf`
//! is a `keccak` operand: its two canonical 128-bit cells hold the 256-bit value, so
//! `keccak(a, b, out)` reads them in place with no copies (a self-hash
//! `keccak(h, h, out)` aliases one pair into both input operands) and writes
//! the digest into `out`.
//!
//! Since these DSL scalars are K-embedded F128 cells, a `StackBuf(2)` written
//! cell-by-cell holds the lanes `[v0, 0, v1, 0]`.

use zkdsl::{expand, parse};

#[test]
#[should_panic(expected = "keccak len= 129 is past the 128 bytes of its 8 cells")]
fn keccak_len_past_the_cells_is_rejected() {
    let src =
        "def main():\n    out = StackBuf(2)\n    keccak([1, 2], [3, 4], out, tail=[5, 6, 7, 8], len=129)\n    return\n";
    let _ = expand(&parse(src).expect("parse"));
}

/// A cell the message ends before would be hashed with it.
#[test]
#[should_panic(expected = "keccak len= 40 ends before message cell 3, which is not a literal 0")]
fn keccak_cell_past_len_is_rejected() {
    let src = "def main():\n    out = StackBuf(2)\n    keccak([1, 2], [3, 4], out, len=40)\n    return\n";
    let _ = expand(&parse(src).expect("parse"));
}

#[test]
#[should_panic(expected = "keccak pad_tail=1 needs tail= a StackBuf slice")]
fn keccak_pad_tail_of_a_list_is_rejected() {
    let src = "def main():\n    out = StackBuf(2)\n    keccak([1, 2], [3, 4], out, tail=[5, 0, 0, 0], len=80, pad_tail=1)\n    return\n";
    let _ = expand(&parse(src).expect("parse"));
}

#[test]
#[should_panic(expected = "keccak_cells final=0 absorbs whole cells: it takes no len=")]
fn keccak_cells_non_final_len_is_rejected() {
    let src = "def main():\n    out = StackBuf(13)\n    keccak_cells([1, 2], out, final=0, len=16)\n    return\n";
    let _ = expand(&parse(src).expect("parse"));
}

#[test]
#[should_panic(expected = "keccak_cells state= must be the 13-cell run a previous keccak wrote")]
fn keccak_short_state_is_rejected() {
    let src =
        "def main():\n    st = [1, 2]\n    out = StackBuf(2)\n    keccak_cells([1, 2], out, state=st)\n    return\n";
    let _ = expand(&parse(src).expect("parse"));
}

/// A StackBuf index literal that does not fit `u32` is rejected at compile time,
/// not silently truncated modulo 2^32 (which would resolve `sa[2^32]` to `sa[0]`).
#[test]
#[should_panic(expected = "does not fit in u32")]
fn stack_buf_index_overflow_rejected() {
    let src = "def main():\n    sa = StackBuf(2)\n    x = sa[4294967296]\n    return\n";
    let _ = expand(&parse(src).expect("parse"));
}

/// A list literal anywhere but the RHS of an assignment is rejected with a
/// clear message, not lowered as a phantom scalar.
#[test]
#[should_panic(expected = "a list literal must be bound to a name")]
fn stack_buf_list_literal_as_value_rejected() {
    let src = "def main():\n    x = 1 + [2, 3]\n    assert x == x\n    return\n";
    let _ = expand(&parse(src).expect("parse"));
}

/// A compile-time heap index past the buffer's declared size is a compile
/// error, not a runtime wild deref.
#[test]
#[should_panic(expected = "heap index 8 out of bounds for `hb` (HeapBuf size 8)")]
fn heap_index_oob_rejected() {
    let src = "def main():\n    hb = HeapBuf(8)\n    x = hb[GEN ** 8]\n    assert x == x\n    return\n";
    let _ = expand(&parse(src).expect("parse"));
}

/// The bound follows shifted aliases back to the original buffer: a pointer
/// alias `row = hb * GEN ** k` checks `row[GEN ** j]` against size − k.
#[test]
#[should_panic(expected = "heap index 9 out of bounds for `hb` (HeapBuf size 8)")]
fn heap_alias_index_oob_rejected() {
    let src = "def main():\n    hb = HeapBuf(8)\n    row = hb * GEN ** 6\n    x = row[GEN ** 3]\n    assert x == x\n    return\n";
    let _ = expand(&parse(src).expect("parse"));
}

/// A hint slice whose end exceeds the buffer is rejected at compile time.
#[test]
#[should_panic(expected = "heap slice 0:9 out of bounds for `hb` (HeapBuf size 8)")]
fn heap_hint_slice_oob_rejected() {
    let src = "def main():\n    hb = HeapBuf(8)\n    hint_witness(hb[0:9], \"w\")\n    x = hb[GEN ** 0]\n    assert x == x\n    return\n";
    let _ = expand(&parse(src).expect("parse"));
}

/// A keccak heap slice straddling the buffer end is rejected. The 256-bit
/// operand `hb[7:9]` is two 128-bit cells, so the bound check trips at
/// `7 + 2 = 9 > 8`.
#[test]
#[should_panic(expected = "heap slice 7:9 out of bounds for `hb` (HeapBuf size 8)")]
fn heap_keccak_slice_oob_rejected() {
    let src = "def main():\n    hb = HeapBuf(8)\n    hb[GEN ** 7] = 5\n    out = StackBuf(2)\n    keccak(hb[7:9], hb[7:9], out)\n    return\n";
    let _ = expand(&parse(src).expect("parse"));
}

/// An index whose exponent ends past `u128` is out of bounds: `exp + 1` used to
/// wrap to 0 and pass the check, so `hb[GEN ** (2^128 - 1)]` compiled.
#[test]
#[should_panic(expected = "heap index 340282366920938463463374607431768211455 out of bounds for `hb` (HeapBuf size 8)")]
fn heap_index_exponent_overflow_rejected() {
    let src =
        "def main():\n    hb = HeapBuf(8)\n    hb[GEN ** 340282366920938463463374607431768211455] = 5\n    return\n";
    let _ = expand(&parse(src).expect("parse"));
}

/// An alias shift plus an index that overflows `u128` is out of bounds too,
/// where the check used to be skipped.
#[test]
#[should_panic(expected = "out of bounds for `hb` (HeapBuf size 8)")]
fn heap_alias_exponent_overflow_rejected() {
    let src = "def main():\n    hb = HeapBuf(8)\n    row = hb * GEN ** 340282366920938463463374607431768211455\n    row[GEN ** 2] = 5\n    return\n";
    let _ = expand(&parse(src).expect("parse"));
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
    expand(&parse(src).expect("parse"));
}

/// A multi-cell value can cross a call in BOTH directions.
///
/// It could always be returned as a run of cells and never passed as one, so a
/// two-cell digest went in through a pointer or an `@inline` expansion while
/// coming back out whole. A `s: StackBuf(n)` parameter takes the same n
/// consecutive cells a `StackBuf(n)` return value occupies, which is why the
/// argument area is a WIDTH rather than a count.
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
    expand(&parse(src).expect("parse"));

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
        let Err(err) = std::panic::catch_unwind(|| expand(&ast)) else {
            panic!("accepted: {arg}");
        };
        let msg = err.downcast_ref::<String>().map(String::as_str).unwrap_or("");
        assert!(msg.contains(want), "got `{msg}`");
    }
}
