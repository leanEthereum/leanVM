/-
  LeanVM.Guest.B1.Sig.SpWotsStepComplete

  `sp_wots`'s chain step, for completeness: in single-assignment form, reading and writing
  canonical cells.
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
* `SpGood b σ`: the values the step reads: `pp`, `at[0]`, `at[1]`, the run at `b`;
  `spWp_shape`, `spWp_canon`, `spWp_atoms`.
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

/-- The values `sp_wots`'s step reads: `pp`, `at[0]`, `at[1]` and the padding run at `b`. -/
def SpGood (b : Nat) (σ : Val) : Prop :=
  IsCanonical128 (σ (.n 0)) ∧ IsCanonical128 (σ (.n 4)) ∧ IsCanonical128 (σ (.n 5)) ∧ PadOK σ b

theorem spGood_congr {b B : Nat} (hB : b + 5 ≤ B) (h6 : 6 ≤ B) {σ σ' : Val}
    (hσ : AgreeBelow B σ σ') (h : SpGood b σ) : SpGood b σ' := by
  obtain ⟨g0, g4, g5, gp⟩ := h
  exact ⟨by rw [hσ.apply ⟨0, by omega, rfl⟩]; exact g0, by rw [hσ.apply ⟨4, by omega, rfl⟩]; exact g4,
    by rw [hσ.apply ⟨5, by omega, rfl⟩]; exact g5, gp.congr (b := B) hB hσ⟩

theorem canon_litC (c : Nat) : IsCanonical128 (lit c) := canon_word _ _

/-- **The step reads and writes canonical cells.** -/
theorem spWp_canon {b B : Nat} (hB : b + 5 ≤ B) (h6 : 6 ≤ B) :
    StepCanon (spWp b) B (SpGood b) := by
  refine ⟨fun σ σ' hσ h => spGood_congr hB h6 hσ h, fun i s v c o σ hc ho hco h1 h2 hg hv => ?_⟩
  obtain ⟨g0, g4, g5, gp⟩ := hg
  have hsz : (spWp b).size = 3 := rfl
  rw [hsz] at hco h1
  have hne : ∀ {x y : Nat}, x ≠ y → V.n x ≠ V.n y := fun h e => h (by simpa using e)
  have hlow : ∀ j < 6, ¬ InR o 1 (.n j) := fun j hj ⟨k, hk, e⟩ => by
    simp only [V.mk.injEq, true_and] at e; omega
  have hvc : ∀ j < 3, v ≠ .n (c + j) := fun j hj e => h1 ⟨j, hj, e⟩
  have hv0 : v ≠ .n c := by simpa using hvc 0 (by norm_num)
  rw [spWp_step]
  split
  · refine k64_fwd_canon σ (by omega) (fun x hx => ?_) (by omega) (by omega) gp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨hlow 0 (by norm_num), hne (by omega), g0⟩
    · exact ⟨hlow 4 (by norm_num), hne (by omega), g4⟩
    · exact ⟨hlow 5 (by norm_num), hne (by omega), g5⟩
    · exact ⟨h2, hv0, hv⟩
  · set σ1 := Function.update σ (.n c) (lit (spStepC i s)) with hσ1
    set σ2 := Function.update σ1 (.n (c + 1)) (σ1 (.n 5) + σ1 (.n c)) with hσ2
    have hf : fwd (spPre2 i s c) σ = σ2 := rfl
    have keep : ∀ x, x ≠ .n c → x ≠ .n (c + 1) → σ2 x = σ x := fun x h1 h2 => by
      rw [hσ2, Function.update_of_ne h2, hσ1, Function.update_of_ne h1]
    have e1 : σ2 (.n (c + 1)) = σ (.n 5) + lit (spStepC i s) := by
      rw [hσ2, Function.update_self, hσ1, Function.update_of_ne (hne (by omega)),
        Function.update_self]
    have hdisj : ∀ x ∈ outsList (k64 b (.n 0) (.n 4) (.n (c + 1)) v (c + 2) o),
        x ∉ Stmt.valsList (spPre2 i s c) := by
      intro x hx hm
      rw [k64_outs] at hx
      rcases spPre2_vals i s c hm with rfl | rfl | rfl <;> rcases List.mem_cons.mp hx with e | hx <;>
        first | (simp only [V.mk.injEq, true_and] at e; omega) |
          (obtain ⟨k, hk, e⟩ := mem_runV.mp hx; simp only [V.mk.injEq, true_and] at e; omega)
    have hk := k64_fwd_canon (pad := b) (m0 := .n 0) (m1 := .n 4) (m2 := .n (c + 1)) (m3 := v)
      (c := c + 2) (o := o) σ2 (by omega) (fun x hx => ?_) (by omega) (by omega)
      (gp.congr (b := c) (by omega) fun k hk => (keep _ (hne (by omega)) (hne (by omega))).symm)
    · refine ⟨KCanon.append (kcanon_noKec fun x hx ins outs i' o' e => ?_) (by rw [hf]; exact hk.1)
        hdisj, fun j hj => ?_⟩
      · simp only [spPre2, cst, addS, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> simp at e
      · rw [fwd_append, hf]; exact hk.2 j hj
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨hlow 0 (by norm_num), hne (by omega),
          by rw [keep _ (hne (by omega)) (hne (by omega))]; exact g0⟩
      · exact ⟨hlow 4 (by norm_num), hne (by omega),
          by rw [keep _ (hne (by omega)) (hne (by omega))]; exact g4⟩
      · exact ⟨by rintro ⟨k, hk, e⟩; simp only [V.mk.injEq, true_and] at e; omega, hne (by omega),
          by rw [e1]; exact canon_add g5 (canon_litC _)⟩
      · exact ⟨h2, hvc 2 (by norm_num),
          by rw [keep _ hv0 (hvc 1 (by norm_num))]; exact hv⟩

end
end LeanVM.Guest.B1.Sig
