module

public import Aeneas
public import Statement.Field

/-!
# Reading the models as the statement

One reading function per Rust type a claim compares with a statement value.
-/

@[expose] public section

namespace Refinement.Spec

open Aeneas.Std LeanVM.Parameters

/-- The base-field element held in a 64-bit word (`crates/verifier/src/field.rs`).

Bit `i` of the word is the coefficient of `x^i`. -/
def k (w : U64) : K := BF64.ofBitVec w.bv

end Refinement.Spec
