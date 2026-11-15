/-
  LeanVM.Guest.B1.Da.DvShape

  `da_verify`'s honest shape (G:4516-4561): its calls, its callees' trees' shapes, for the budget.
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

`dvCallsS j`: `da_verify`'s calls, the roots' tree's arm `j` dispatched. `padNH d`: `da_pad` at the gap `g^d`; `rtNH k d`: the roots' tree's
arm `k`, its `da_pad` of that shape. `dvNH r L`: `da_verify` on `r` blobs padded to `2^L`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (flatCalls)
open LeanVM.Guest.Budget (NodeHonest)
open LeanVM.Guest.B1.Digest

@[expose] public section

/-- The DA levels' names, as the dispatch lists them. -/
def dlList : List String :=
  ["da_levels__L1_L0", "da_levels__L2_L1", "da_levels__L4_L2", "da_levels__L8_L3",
    "da_levels__L16_L4", "da_levels__L32_L5", "da_levels__L64_L6", "da_levels__L128_L7",
    "da_levels__L256_L8", "da_levels__L512_L9", "da_levels__L1024_L10"]

theorem dlList_getD {L : ℕ} (hL : L ≤ 10) : dlList.getD L "" = daLevelsName L := by
  interval_cases L <;> rfl

theorem dlNames_bang {L : ℕ} (hL : L ≤ 10) : dlNames[L]! = daLevelsName L := by
  interval_cases L <;> rfl

theorem one_add_gen_ne_iff {m : ℕ} (hm : m < ordG) : (1 + gen ^ m ≠ 0) ↔ m ≠ 0 :=
  ⟨fun h hm0 => h (by subst hm0; rw [pow_zero]; exact e_add_eq_zero_iff.mpr rfl),
    fun h => one_add_gen_pow_ne_zero (by omega) hm⟩

/-- `da_verify`'s calls, the dispatch at `j`. -/
def dvCallsS (j : ℕ) : List (Option V × String × List V × List V) :=
  [(none, "da_row_shape", [.n 1, .n 2, .n 0], [.n 7, .n 8]),
    (none, "da_vector", [.n 9], [.n 10, .n 11, .n 12, .n 13]),
    (none, "da_weights", [.n 11, .n 12, .n 10, .n 13], [.n 14]),
    (some (.n 19), name% «da_verify_loop0», [.n 20, .n 1, .n 14, .n 17], []),
    (none, rtName j, [.n 17, .n 1, .n 8], [.n 21, .n 22])]

theorem dv_callsSF (σ : Val) : dvP.filterMap (Stmt.callSF σ) = dvCallsS (logG (σ (.n 2))) := rfl

theorem dv_flatCalls (σ : Val) : flatCalls dvP σ = (dvCallsS (logG (σ (.n 2)))).map (Main.mkCall σ) := by
  rw [flatCalls, dv_callsSF]

/-- `da_pad`'s honest valuation at the gap `g^d`: the guard and the loop's start. -/
def padQ (d : ℕ) (σ : Val) : Prop := σ (.n 2) = gen ^ d ∧ σ (.n 4) = 1 + gen ^ d ∧ σ (.n 5) = 1

/-- **`da_pad`'s honest shape** at the gap `g^d`. -/
def padNH (d : ℕ) : Tree → Prop :=
  NodeHonest coreProgram "da_pad" (padQ d) (flatCalls padBody.dropLast) (fun _ => []) [fun _ => True]

/-- **The roots' tree's arm `k`'s honest shape**, its padding at the gap `g^d`. -/
def rtNH (k d : ℕ) : Tree → Prop :=
  NodeHonest coreProgram (rtName k) (fun _ => True) (flatCalls (rtBody k).dropLast) (fun _ => [])
    [padNH d, fun _ => True]

/-- **`da_verify`'s honest valuation**: its counts, its loops' starts and the blob loop's guard. -/
def dvQ (r L : ℕ) (σ : Val) : Prop :=
  σ (.n 1) = gen ^ r ∧ σ (.n 2) = gen ^ L ∧ σ (.n 8) = gen ^ (2 ^ L - r) ∧
    σ (.n 19) = 1 + gen ^ r ∧ σ (.n 20) = 1

/-- The predicates on `da_verify`'s callees' trees. -/
def dvTs (r L : ℕ) : List (Tree → Prop) :=
  [fun _ => True, fun _ => True, fun _ => True, fun _ => True, rtNH L (2 ^ L - r)]

/-- **`da_verify`'s honest shape** on `r` blobs padded to `2^L`. -/
def dvNH (r L : ℕ) : Tree → Prop :=
  NodeHonest coreProgram "da_verify" (dvQ r L) (flatCalls dvP) (fun _ => dvSizes r L) (dvTs r L)

end
end LeanVM.Guest.B1.Da
