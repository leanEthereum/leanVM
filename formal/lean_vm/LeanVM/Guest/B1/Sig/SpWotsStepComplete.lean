/-
  LeanVM.Guest.B1.Sig.SpWotsStepComplete

  `sp_wots`'s chain step, for completeness: in single-assignment form.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsT
public import LeanVM.Guest.B1.Sig.XmssStep
public import LeanVM.Guest.B1.Sig.KMsgComplete

/-!
# `sp_wots`'s chain step, complete

The step is a 64-byte `keccak` (`k64`) of `pp`, `at[0]`, the step's `A1` and the value, after the
two atoms that add the step's constant to `at[1]` (`spPre2`), none for chain `0`'s first step.

* `spWp_step`: the step in those terms;
* `SpGood b σ`: the padding run at `b`, which the step reads; `spWp_shape`, `spWp_stable`,
  `spWp_atoms`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- The atoms a step with an address constant sets first: the constant and `at[1]` plus it. -/
def spPre2 (i s c : Nat) : List Stmt := [cst c (lit (spStepC i s)), addS (.n (c + 1)) (.n 5) (.n c)]

theorem spWp_step (X i s : Nat) (v : V) (c o : Nat) : (spWp X).step i s v c o =
    if i = 0 ∧ s = 0 then k64 X (.n 0) (.n 4) (.n 5) v c o
    else spPre2 i s c ++ k64 X (.n 0) (.n 4) (.n (c + 1)) v (c + 2) o := rfl

theorem spWp_atoms (X : Nat) : StepAtoms (spWp X) := by
  intro i s v c o
  rw [spWp_step]
  split <;> rfl

theorem spPre2_ssa (i s : Nat) {c : Nat} (hc : 6 ≤ c) : SSA (spPre2 i s c) := by
  simp [spPre2, SSA, cst, addS, aOuts, aReads, outsList, Atom.vals, DefOK]
  omega

theorem spPre2_outs (i s c : Nat) : outsList (spPre2 i s c) = [.n c, .n (c + 1)] := by
  simp [spPre2, cst, addS, outsList, aOuts]

theorem spPre2_vals (i s c : Nat) {x : V} (hx : x ∈ Stmt.valsList (spPre2 i s c)) :
    x = .n c ∨ x = .n (c + 1) ∨ x = .n 5 := by
  simp only [spPre2, cst, addS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp

/-- **The step is in single-assignment form** from bases above `B`, its run below `B`. -/
theorem spWp_shape {b B : Nat} (hB : b + 5 ≤ B) (h6 : 6 ≤ B) : StepShape (spWp b) B := by
  intro i s v c o hc ho hco h1 h2
  have hsz : (spWp b).size = 3 := rfl
  rw [hsz] at hco h1 ⊢
  have hlow : ∀ j < 6, ¬ InR o 1 (.n j) := fun j hj ⟨k, hk, e⟩ => by
    simp only [V.mk.injEq, true_and] at e; omega
  rw [spWp_step]
  split
  · refine ⟨k64_ssa (by omega) (fun x hx => ?_) (Or.inl (by omega)), fun x hx => ?_, fun x hx => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hlow 0 (by norm_num)
      · exact hlow 4 (by norm_num)
      · exact hlow 5 (by norm_num)
      · exact h2
    · rw [k64_outs] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl ⟨0, by norm_num, by simp⟩
      · exact Or.inr (mem_runV.mp hx)
    · rcases k64_vals _ _ _ _ _ c o hx with hx | rfl | ⟨k, hk, rfl⟩ | hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact Or.inr (Or.inl ⟨0, by omega, rfl⟩)
        · exact Or.inr (Or.inl ⟨4, by omega, rfl⟩)
        · exact Or.inr (Or.inl ⟨5, by omega, rfl⟩)
        · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl ⟨0, by norm_num, by simp⟩))
      · exact Or.inr (Or.inl ⟨b + k, by omega, rfl⟩)
      · exact Or.inr (Or.inr (Or.inr hx))
  · refine ⟨SSA.append (spPre2_ssa i s (by omega)) (k64_ssa (by omega) (fun x hx => ?_) (Or.inl (by omega)))
      (fun x hx hm => ?_), fun x hx => ?_, fun x hx => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hlow 0 (by norm_num)
      · exact hlow 4 (by norm_num)
      · rintro ⟨k, hk, e⟩; simp only [V.mk.injEq, true_and] at e; omega
      · exact h2
    · rw [k64_outs] at hx
      rcases spPre2_vals i s c hm with rfl | rfl | rfl <;> rcases List.mem_cons.mp hx with e | hx <;>
        first | (simp only [V.mk.injEq, true_and] at e; omega) |
          (obtain ⟨k, hk, e⟩ := mem_runV.mp hx; simp only [V.mk.injEq, true_and] at e; omega)
    · rw [outsList_append, spPre2_outs, k64_outs] at hx
      simp only [List.cons_append, List.nil_append, List.mem_cons] at hx
      rcases hx with rfl | rfl | rfl | hx
      · exact Or.inl ⟨0, by norm_num, by simp⟩
      · exact Or.inl ⟨1, by norm_num, rfl⟩
      · exact Or.inl ⟨2, by norm_num, rfl⟩
      · exact Or.inr (mem_runV.mp hx)
    · rw [valsList_append] at hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases spPre2_vals i s c hx with rfl | rfl | rfl
        · exact Or.inr (Or.inr (Or.inl ⟨0, by norm_num, by simp⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨1, by norm_num, rfl⟩))
        · exact Or.inr (Or.inl ⟨5, by omega, rfl⟩)
      · rcases k64_vals _ _ _ _ _ (c + 2) o hx with hx | rfl | ⟨k, hk, rfl⟩ | hx
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact Or.inr (Or.inl ⟨0, by omega, rfl⟩)
          · exact Or.inr (Or.inl ⟨4, by omega, rfl⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨1, by norm_num, rfl⟩))
          · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl ⟨2, by norm_num, rfl⟩))
        · exact Or.inr (Or.inl ⟨b + k, by omega, rfl⟩)
        · exact Or.inr (Or.inr (Or.inr hx))

/-- The padding run at `b`, which `sp_wots`'s step reads. -/
def SpGood (b : Nat) (σ : Val) : Prop := PadOK σ b

theorem spGood_congr {b B : Nat} (hB : b + 5 ≤ B) {σ σ' : Val}
    (hσ : AgreeBelow B σ σ') (h : SpGood b σ) : SpGood b σ' :=
  PadOK.congr (b := B) h hB hσ

/-- **The run the step reads survives** every change above `B`. -/
theorem spWp_stable {b B : Nat} (hB : b + 5 ≤ B) : GoodStable B (SpGood b) :=
  fun _ _ hσ h => spGood_congr hB hσ h

end
end LeanVM.Guest.B1.Sig
