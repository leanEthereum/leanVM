module

public import NativeRustcVm.Transcript.Rep

/-!
# The rows a query opened, read in place

`Rows { openings: &[u64], count, width }` (`transcript.rs`, `#[repr(C)]`, 32 bytes: the slice's
address and length, the count, the width) names a phase's openings in the decoded area: row `j`
is the `width` leaf words of opening `j`, from word `1 + j · openingWords` of the openings
(`RowsAt d r p rows`: the `Rows` at `r`, its openings at `p`, represent the model's rows). The
openings are the phase's words from word `3`, `wireMaxQueries · openingWords` of them; `p` is not
`0` (`Option<Rows>` is `0` in its first word for `None`, `OptRowsAt`).
-/

namespace NativeRustcVm.Sumcheck

open NativeVm NativeVm.Model LeanVM.Protocol.Compile NativeRustcVm.Transcript

@[expose] public section

/-- The openings' words of a phase (`PHASE_WORDS - 3`). -/
def openingsWords : Nat := wireMaxQueries * openingWords

/-- **The `Rows` at `r`, reading the openings at `p`, represent `rows`**: the slice `p`,
`openingsWords`, the count and a width `w ≤ wireMaxLeafWords`; row `j` has `w` words, at word
`1 + j · openingWords` from `p`. -/
def RowsAt (d : Mem 64) (r p : BitVec 64) (rows : Array (Array UInt64)) : Prop :=
  p ≠ 0 ∧ rows.size ≤ wireMaxQueries ∧ ∃ w ≤ wireMaxLeafWords,
    WordsAt d r [UInt64.ofBitVec p, openingsWords.toUInt64, rows.size.toUInt64, w.toUInt64] ∧
    ∀ j (hj : j < rows.size), rows[j].size = w ∧
      WordsAt d (off p (8 * (1 + j * openingWords))) rows[j].toList

/-- `Option<Rows>` at `r`: `0` in the first word, or the rows. -/
def OptRowsAt (d : Mem 64) (r p : BitVec 64) : Option (Array (Array UInt64)) → Prop
  | none => WordAt d r 0
  | some rows => RowsAt d r p rows

end

end NativeRustcVm.Sumcheck
