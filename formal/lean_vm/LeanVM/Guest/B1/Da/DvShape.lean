/-
  LeanVM.Guest.B1.Da.DvShape

  `da_verify`'s honest shape: its calls, its callees' trees' shapes, for the budget.
-/

module

public import LeanVM.Guest.B1.Da.VerifyChk
public import LeanVM.Guest.B1.Da.DvBound
public import LeanVM.Guest.B1.Tables.FlatAtT
public import LeanVM.Guest.B1.Digest.Steps
public import LeanVM.Guest.Budget.Kids
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_pad»
import LeanVM.Guest.Data.ValNames.«da_verify»

/-!
# `da_verify`'s honest shape

`dvCallsS`: `da_verify`'s calls. `padNH d`: `da_pad` at the gap `g^d`. `dvNH r L`: `da_verify` on
`r` blobs padded to `2^L`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (flatCalls)
open LeanVM.Guest.Budget (NodeHonest)
open LeanVM.Guest.B1.Digest

@[expose] public section

theorem one_add_gen_ne_iff {m : ℕ} (hm : m < ordG) : (1 + gen ^ m ≠ 0) ↔ m ≠ 0 :=
  ⟨fun h hm0 => h (by subst hm0; rw [pow_zero]; exact e_add_eq_zero_iff.mpr rfl),
    fun h => one_add_gen_pow_ne_zero (by omega) hm⟩

/-- `da_verify`'s calls. -/
def dvCallsS : List (Option V × String × List V × List V) :=
  [(none, "da_padding", [.n (val% «da_verify» "n_blob_g")], [.n (val% «da_verify» "gap_g")]),
    (none, "da_vector", [.n (val% «da_verify» "z")], [.n (val% «da_verify» "zs"), .n (val% «da_verify» "top_leaves"), .n (val% «da_verify» "cell_factors"), .n (val% «da_verify» "offsets")]),
    (none, "da_weights", [.n (val% «da_verify» "top_leaves"), .n (val% «da_verify» "cell_factors"), .n (val% «da_verify» "zs"), .n (val% «da_verify» "offsets")], [.n (val% «da_verify» "weights")]),
    (some (.n (val% «da_verify» "s6#1")), name% «da_verify_loop0», [.n (val% «da_verify» "s6#2"), .n (val% «da_verify» "n_blob_g"), .n (val% «da_verify» "weights"), .n (val% «da_verify» "roots")], []),
    (none, "da_pad", [.n (val% «da_verify» "roots"), .n (val% «da_verify» "n_blob_g"), .n (val% «da_verify» "gap_g")], []),
    (none, dlTop, [.n (val% «da_verify» "roots")], [.n (val% «da_verify» "r0"), .n (val% «da_verify» "r1")])]

theorem dv_callsSF (σ : Val) : dvP.filterMap (Stmt.callSF σ) = dvCallsS := rfl

theorem dv_flatCalls (σ : Val) : flatCalls dvP σ = dvCallsS.map (Main.mkCall σ) := by
  rw [flatCalls, dv_callsSF]

/-- `da_pad`'s honest valuation at the gap `g^d`: the guard and the loop's start. -/
def padQ (d : ℕ) (σ : Val) : Prop := σ (.n (val% «da_pad» "gap_g")) = gen ^ d ∧ σ (.n (val% «da_pad» "s0#1")) = 1 + gen ^ d ∧ σ (.n (val% «da_pad» "s0#2")) = 1

/-- **`da_pad`'s honest shape** at the gap `g^d`. -/
def padNH (d : ℕ) : Tree → Prop :=
  NodeHonest coreProgram "da_pad" (padQ d) (flatCalls dpadBody.dropLast) (fun _ => []) [fun _ => True]

/-- **`da_verify`'s honest valuation**: its counts, the blob loop's guard and start. -/
def dvQ (r L : ℕ) (σ : Val) : Prop :=
  σ (.n (val% «da_verify» "n_blob_g")) = gen ^ r ∧ σ (.n (val% «da_verify» "gap_g")) = gen ^ (2 ^ L - r) ∧ σ (.n (val% «da_verify» "s6#1")) = 1 + gen ^ r ∧ σ (.n (val% «da_verify» "s6#2")) = 1

/-- The predicates on `da_verify`'s callees' trees. -/
def dvTs (r L : ℕ) : List (Tree → Prop) :=
  [fun _ => True, fun _ => True, fun _ => True, fun _ => True, padNH (2 ^ L - r), fun _ => True]

/-- **`da_verify`'s honest shape** on `r` blobs padded to `2^L`. -/
def dvNH (r L : ℕ) : Tree → Prop :=
  NodeHonest coreProgram "da_verify" (dvQ r L) (flatCalls dvP) (fun _ => dvSizes r L) (dvTs r L)

end
end LeanVM.Guest.B1.Da
