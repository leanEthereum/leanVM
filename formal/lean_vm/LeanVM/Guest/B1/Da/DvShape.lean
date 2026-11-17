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
  [(none, "da_padding", [.n 1], [.n 2]),
    (none, "da_vector", [.n 3], [.n 4, .n 5, .n 6, .n 7]),
    (none, "da_weights", [.n 5, .n 6, .n 4, .n 7], [.n 8]),
    (some (.n 12), name% «da_verify_loop0», [.n 13, .n 1, .n 8, .n 10], []),
    (none, "da_pad", [.n 10, .n 1, .n 2], []),
    (none, dlTop, [.n 10], [.n 14, .n 15])]

theorem dv_callsSF (σ : Val) : dvP.filterMap (Stmt.callSF σ) = dvCallsS := rfl

theorem dv_flatCalls (σ : Val) : flatCalls dvP σ = dvCallsS.map (Main.mkCall σ) := by
  rw [flatCalls, dv_callsSF]

/-- `da_pad`'s honest valuation at the gap `g^d`: the guard and the loop's start. -/
def padQ (d : ℕ) (σ : Val) : Prop := σ (.n 2) = gen ^ d ∧ σ (.n 4) = 1 + gen ^ d ∧ σ (.n 5) = 1

/-- **`da_pad`'s honest shape** at the gap `g^d`. -/
def padNH (d : ℕ) : Tree → Prop :=
  NodeHonest coreProgram "da_pad" (padQ d) (flatCalls dpadBody.dropLast) (fun _ => []) [fun _ => True]

/-- **`da_verify`'s honest valuation**: its counts, the blob loop's guard and start. -/
def dvQ (r L : ℕ) (σ : Val) : Prop :=
  σ (.n 1) = gen ^ r ∧ σ (.n 2) = gen ^ (2 ^ L - r) ∧ σ (.n 12) = 1 + gen ^ r ∧ σ (.n 13) = 1

/-- The predicates on `da_verify`'s callees' trees. -/
def dvTs (r L : ℕ) : List (Tree → Prop) :=
  [fun _ => True, fun _ => True, fun _ => True, fun _ => True, padNH (2 ^ L - r), fun _ => True]

/-- **`da_verify`'s honest shape** on `r` blobs padded to `2^L`. -/
def dvNH (r L : ℕ) : Tree → Prop :=
  NodeHonest coreProgram "da_verify" (dvQ r L) (flatCalls dvP) (fun _ => dvSizes r L) (dvTs r L)

end
end LeanVM.Guest.B1.Da
