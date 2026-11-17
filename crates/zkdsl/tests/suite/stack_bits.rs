//! Computed-advice bit buffers in the frame: `hint_decompose_bits` into a
//! `StackBuf`, and `addr()` naming the run so it can still be indexed through a
//! pointer (at a runtime index, or from a callee).

use zkdsl::{expand, parse};

/// A frame pointer carries the same compile-time bound a `HeapBuf` pointer gets.
/// `check_heap_bound` keys `heap_sizes` by the pointer's own cell, but every
/// `addr()` in a function shares the `fp` cell as its base, so the run has to
/// come from the address's own provenance instead.
#[test]
#[should_panic(expected = "out of bounds")]
fn addr_pointers_are_bounds_checked() {
    let src = "\
def main():
    b = StackBuf(2)
    p = addr(b)
    p[GEN ** 40] = GEN ** 3
    return
";
    expand(&parse(src).expect("parse"));
}
