/-
  LeanVM.Guest.B1.Main.MainGoalsHClT

  The honest shape of a child's claim list's digest (`ccHonest`): the walk the honest prover
  takes, the gap walk when the list's slots strictly increase, and its hint.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHL5T
public import LeanVM.Guest.B1.Main.MainGoalsClT
public import LeanVM.Guest.B1.Digest.ClaimListsAtM
public import LeanVM.Guest.AcceptableChild

/-!
# A child's claim list's honest shape

`ccHint mono`: the honest hint `child_mono`, `count 1 = g` on the gap walk, `count 0 = 1` on the
walk by hinted indices (`Hints.childSlotPushes`). `ccHonest n mono`: `child_claim_list_digest`'s
tree of honest shape on `n` claims, on the walk `mono`, at that hint (`B1.Digest.ccHonestH`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- The honest hint `child_mono`: `g` on the gap walk, `1` on the other. -/
def ccHint (mono : Bool) : E := if mono then gen else 1

/-- **`child_claim_list_digest`'s honest shape** on `n` claims, on the walk `mono`. -/
def ccHonest (n : ℕ) (mono : Bool) : Tree → Prop := B1.Digest.ccHonestH n mono (ccHint mono)

theorem ccHint_any : ccHint false + word 2 0 ≠ 0 ∧ IsInK (ccHint false + word 2 0) := by
  simp only [ccHint, Bool.false_eq_true, ↓reduceIte, word_gen]
  refine ⟨fun h => ?_, ?_⟩
  · have h1 : gen ^ 1 = 1 := by rw [pow_one]; exact (e_add_eq_zero_iff.mp h).symm
    exact absurd ((gen_pow_eq_one_iff (by norm_num)).mp h1) (by norm_num)
  · simpa using B1.Digest.gen_pow_add_isInK 0 1

end
end LeanVM.Guest.B1.Main
