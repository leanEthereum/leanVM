/-
  LeanVM.Guest.B1.VerifySub.H.Regions

  Every callee of `verify_sub` on an honest child but `verify_tables`, `verify_keccak` and the
  terminal reads slices of the caller's words and of the own buffers.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Lin
public import LeanVM.Guest.B1.Bits.Log2Placed

/-!
# The callees' regions

`expTableWords_sq`, `expTableWords_rank`: the squares and the rank keys are sections of the
exponent table. `kid_lin_sub`: callee `j` (not `10`, `11`, `15`) reads slices of the caller's
words `Lin` (holding the exponent tables, `vsExpLin`) and of the own buffers.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

theorem expTableWords_sq : (expTabAllWords.drop 0).take 34 = Tables.gSquaresList := by
  apply List.ext_getElem (by simp [length_expTabAllWords, Tables.gSquaresList])
  intro k h1 h2
  have hk : k < 34 := by simpa [Tables.gSquaresList] using h2
  rw [List.getElem_take, List.getElem_drop, ← List.getD_eq_getElem _ 0, Nat.zero_add,
    expTabAllWords_getD, ite_eq_left_of_eq_true _ _ (eq_true (by omega)), expTabWord,
    ite_eq_left_of_eq_true _ _ (eq_true (by omega)), expTableWords_getD k (by omega),
    etListK_sq k hk, ofK_pow, ← gen_eq_ofK]
  simp [Tables.gSquaresList]

theorem expTableWords_rank : (expTabAllWords.drop 178).take 34 = Tables.rankKeysList := by
  apply List.ext_getElem (by simp [length_expTabAllWords, Tables.rankKeysList])
  intro k h1 h2
  have hk : k < 34 := by simpa [Tables.rankKeysList] using h2
  rw [List.getElem_take, List.getElem_drop, ← List.getD_eq_getElem _ 0, expTabAllWords_getD,
    ite_eq_left_of_eq_true _ _ (eq_true (by omega)), expTabWord,
    ite_eq_left_of_eq_true _ _ (eq_true (by omega)), expTableWords_getD _ (by omega),
    etListK_rank k hk, ofK_pow, ← gen_eq_ofK]
  simp [Tables.rankKeysList, Tables.rankStride]

/-- **The callees but `verify_tables`, `verify_keccak` and the terminal read the caller's words
and the own buffers.** -/
theorem kid_lin_sub {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) (b : ℕ) {sqE : ℕ} {Lin : Main.Layout}
    (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin) {j : ℕ} (hj : j < 16) (h10 : j ≠ 10) (h11 : j ≠ 11)
    (h15 : j ≠ 15) (pv : List (List E × Main.Layout)) :
    ∀ q ∈ ((S.kids (bases b (vsSizes S.d)) sqE).getD j noKid pv).Lin,
      SubOf Lin q ∨ SubOf (bufL b (vsSizes S.d) S.ownW) q := by
  have own : ∀ i < 15, SubOf (bufL b (vsSizes S.d) S.ownW)
      (vb (bases b (vsSizes S.d)) i, S.ownW.getD i []) := fun i hi ↦ S.sub_own b hi
  have hE : SubOf Lin (sqE, expTabAllWords) := subOf_self (hexp _ List.mem_cons_self)
  interval_cases j
  · intro q hq; simp [ChildSegs.kids] at hq
  · intro q hq; simp [ChildSegs.kids] at hq
  · intro q hq
    simp only [ChildSegs.kids, List.getD_cons_succ, List.getD_cons_zero, log2Lin,
      List.mem_singleton] at hq
    subst hq; exact Or.inl (subOf_expTableWords hexp)
  · intro q hq
    simp only [ChildSegs.kids, List.getD_cons_succ, List.getD_cons_zero, Tables.cpLin,
      List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · have := own 4 (by norm_num)
      rw [show S.ownW.getD 4 [] = vsKbW S.logMem S.hs from rfl, S.kbW_eq hbl] at this
      exact Or.inr this
    · have := subOf_exp hexp 0 Tables.gSquaresList (by simp [Tables.gSquaresList])
        (by rw [show Tables.gSquaresList.length = 34 by simp [Tables.gSquaresList],
          expTableWords_sq])
      rw [Nat.add_zero] at this
      exact Or.inl this
    · exact Or.inl (subOf_exp hexp 178 Tables.rankKeysList (by simp [Tables.rankKeysList])
        (by rw [show Tables.rankKeysList.length = 34 by simp [Tables.rankKeysList],
          expTableWords_rank]))
  · intro q hq
    simp only [ChildSegs.kids, List.getD_cons_succ, List.getD_cons_zero, log2Lin,
      List.mem_singleton] at hq
    subst hq; exact Or.inl (subOf_expTableWords hexp)
  · intro q hq
    simp only [ChildSegs.kids, List.getD_cons_succ, List.getD_cons_zero, vsExpLin,
      List.mem_singleton] at hq
    subst hq; exact Or.inl hE
  · intro q hq
    simp only [ChildSegs.kids, List.getD_cons_succ, List.getD_cons_zero,
      List.mem_singleton] at hq
    subst hq; exact Or.inr (own 6 (by norm_num))
  · intro q hq
    simp only [ChildSegs.kids, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Or.inr (S.sub_omWords b hbl)
    · exact Or.inr (own 7 (by norm_num))
  · intro q hq
    simp only [ChildSegs.kids, List.getD_cons_succ, List.getD_cons_zero, vsExpLin,
      List.mem_singleton] at hq
    subst hq; exact Or.inl hE
  · intro q hq
    simp only [ChildSegs.kids, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Or.inr (S.sub_xsG b hbl)
    · exact Or.inr (own 5 (by norm_num))
  · exact absurd rfl h10
  · exact absurd rfl h11
  · intro q hq
    simp only [ChildSegs.kids, List.getD_cons_succ, List.getD_cons_zero, vsExpLin,
      List.mem_singleton] at hq
    subst hq; exact Or.inl hE
  · intro q hq
    simp only [ChildSegs.kids, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Or.inr (own 12 (by norm_num))
    · exact Or.inr (own 13 (by norm_num))
  · intro q hq
    simp only [ChildSegs.kids, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Or.inr (S.sub_xsW b hbl)
    · exact Or.inl hE
  · exact absurd rfl h15

end
end LeanVM.Guest.B1.VerifySub
