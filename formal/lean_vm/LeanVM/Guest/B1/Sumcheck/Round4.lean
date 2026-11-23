/-
  LeanVM.Guest.B1.Sumcheck.Round4

  One plain sumcheck round from a round record (`sumcheck_round4`, inlined): its facts.
-/

module

public import LeanVM.Guest.B1.Sumcheck.Meaning
public import LeanVM.Guest.B1.Common.Run
public import LeanVM.Guest.B1.Common.Find

/-!
# `sumcheck_round4` (TRIAGE #30)

`sumcheck_round4` is inlined into its caller: the record's capacity loaded, the three stream words
read and absorbed, the permutation (`fs_grind_squeeze` at zero bits), the capacity stored into the
next record, the challenge (cell `0`) and the fold. Its block's condition (`vc`) is rewritten to
`MeaningSumcheckRound4` by writing out the capacity records (`capAt5`, `exists_capAt`), the sponge
(`round4_sponge`) and the round's polynomial in the guest's Horner form
(`round4_eval`). The window table is not read.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem word_eight : word 8 0 = gen ^ 3 := word_two_pow (a := 3) (by decide)

/-- The round's polynomial at `y`, in the guest's Horner form. -/
theorem round4_eval (c0 c2 c3 claim y : E) :
    c0 + y * (claim + (1 + y) * (c2 + (1 + y) * c3)) =
      polyEval [c0, claim + sumE [c2, c3], c2, c3] y := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  simp only [polyEval, List.foldr, sumE, List.foldl, zero_add, zero_mul]
  linear_combination (y ^ 2 * c3) * h2

/-- The sponge of the round: three scalars waiting on the record's capacity. -/
theorem round4_sponge (cap : List E) (c0 c2 c3 : E) :
    (⟨cap, []⟩ : Fs).absorbAll [c0, c2, c3] dsObserve =
      ⟨cap, [(c0, dsObserve), (c2, dsObserve), (c3, dsObserve)]⟩ := by
  rw [absorbAll_short _ _ _ (by simp)]
  rfl

theorem exists_capAt {rd : Reader} {p : E} {off s : ℕ} {P : List E → Prop} :
    (∃ cap, CapAt rd p off s cap ∧ P cap) ↔
      ∃ a b c d e, CapAt rd p off s [a, b, c, d, e] ∧ P [a, b, c, d, e] :=
  ⟨fun ⟨cap, h, hp⟩ => match cap, h.1 with | [_, _, _, _, _], _ => ⟨_, _, _, _, _, h, hp⟩,
    fun ⟨_, _, _, _, _, h, hp⟩ => ⟨_, h, hp⟩⟩

theorem capAt5 {rd : Reader} {p a b c d e : E} {off s : ℕ} :
    CapAt rd p off s [a, b, c, d, e] ↔ LoadHolds rd p (off + 0 * s) a ∧
      LoadHolds rd p (off + 1 * s) b ∧ LoadHolds rd p (off + 2 * s) c ∧
        LoadHolds rd p (off + 3 * s) d ∧ LoadHolds rd p (off + 4 * s) e := by
  simp only [CapAt, List.length_cons, List.length_nil, Nat.forall_lt_succ_left', Nat.not_lt_zero,
    IsEmpty.forall_iff, implies_true, List.getElem_cons_zero, List.getElem_cons_succ, and_true,
    true_and, Nat.reduceAdd]

end
end LeanVM.Guest.B1
