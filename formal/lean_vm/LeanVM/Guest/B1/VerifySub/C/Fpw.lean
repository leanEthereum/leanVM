/-
  LeanVM.Guest.B1.VerifySub.C.Fpw

  `verify_sub`'s `fp_w` (G:3419-3422), honestly: the bus challenges' equality weights stored, then
  `β`'s squeeze.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Push
public import LeanVM.Guest.B1.VerifySub.Ctab

/-!
# `fp_w`, honestly

`eqwFactor_complete`, `eqw_complete`: a factor `α_t` or `1 + α_t`, and their product, on the
evaluated valuation, from the challenges in memory. `vsFpw_loop`: the sixteen weights read and
stored in `fp_w` (holding `eqKernel alphas`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr

@[expose] public section

theorem eqwFactor_idx (x t v : ℕ) :
    v ≤ (vsEqwFactor x t v).2.1 ∧ (vsEqwFactor x t v).2.1 < (vsEqwFactor x t v).2.2 ∧
      (vsEqwFactor x t v).2.2 ≤ v + 3 := by
  unfold vsEqwFactor; split <;> simp

variable {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

/-- One factor, honestly. -/
theorem eqwFactor_complete {x t v : ℕ} (hg : ∀ s ∈ (vsEqwFactor x t v).1, GoodS rd S w σ s)
    (hS : Atom.load (.n v) (.n 346) t ∉ S) {a : E} (ha : LoadHolds rd (σ (.n 346)) t a)
    {C : CallRel} {next : Prop} {kret : List E → Prop} (hn : next) :
    σ (.n (vsEqwFactor x t v).2.1) = (if x.testBit t then a else 1 + a) ∧
      Stmt.HoldsList C rd σ (vsEqwFactor x t v).1 next kret := by
  unfold vsEqwFactor at hg ⊢
  by_cases hb : x.testBit t
  · simp only [hb, ↓reduceIte] at hg ⊢
    have r := good_read (w := w) (hg (vsLd v 346 t) (by simp)) hS ha
    simp only [Stmt.HoldsList, Stmt.Holds, vsLd]
    exact ⟨r.1, r.2, hn⟩
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hg ⊢
    have r := good_read (w := w) (hg (vsLd v 346 t) (by simp)) hS ha
    have hc : σ (.n (v + 1)) = word 1 0 0 := hg (vsConst (v + 1) (word 1 0 0)) (by simp)
    have hd : σ (.n (v + 2)) = σ (.n (v + 1)) + σ (.n v) := hg (vsAdd (v + 2) (v + 1) v) (by simp)
    simp only [Stmt.HoldsList, Stmt.Holds, vsLd, vsConst, vsAdd]
    refine ⟨by rw [hd, hc, r.1, word_one], r.2, hc, hd, hn⟩

/-- The weight `eq_weight(alphas, 4, x, 0)` from `v`, honestly. -/
theorem eqw_complete {x v : ℕ} (hg : ∀ s ∈ (vsEqwT x v).1, GoodS rd S w σ s)
    (hS : ∀ d off, v ≤ d → Atom.load (.n d) (.n 346) off ∉ S) {a0 a1 a2 a3 : E}
    (ha : ReadsAt rd (σ (.n 346)) [a0, a1, a2, a3])
    {C : CallRel} {next : Prop} {kret : List E → Prop} (hn : next) :
    σ (.n (vsEqwT x v).2.1) = eqAt [a0, a1, a2, a3] x ∧
      Stmt.HoldsList C rd σ (vsEqwT x v).1 next kret := by
  have l0 : LoadHolds rd (σ (.n 346)) 0 a0 := ha 0 (by simp)
  have l1 : LoadHolds rd (σ (.n 346)) 1 a1 := ha 1 (by simp)
  have l2 : LoadHolds rd (σ (.n 346)) 2 a2 := ha 2 (by simp)
  have l3 : LoadHolds rd (σ (.n 346)) 3 a3 := ha 3 (by simp)
  unfold vsEqwT at hg ⊢
  simp only [List.mem_append, List.mem_singleton] at hg
  have i0 := eqwFactor_idx x 0 v
  have i1 := eqwFactor_idx x 1 (vsEqwFactor x 0 v).2.2
  have i2 := eqwFactor_idx x 2 ((vsEqwFactor x 1 (vsEqwFactor x 0 v).2.2).2.2 + 1)
  have i3 := eqwFactor_idx x 3 ((vsEqwFactor x 2 ((vsEqwFactor x 1 (vsEqwFactor x 0 v).2.2).2.2
    + 1)).2.2 + 1)
  set f0 := vsEqwFactor x 0 v with hf0
  set f1 := vsEqwFactor x 1 f0.2.2 with hf1
  set f2 := vsEqwFactor x 2 (f1.2.2 + 1) with hf2
  set f3 := vsEqwFactor x 3 (f2.2.2 + 1) with hf3
  have g0 : ∀ s ∈ f0.1, GoodS rd S w σ s := fun s hs ↦ hg s (by tauto)
  have g1 : ∀ s ∈ f1.1, GoodS rd S w σ s := fun s hs ↦ hg s (by tauto)
  have g2 : ∀ s ∈ f2.1, GoodS rd S w σ s := fun s hs ↦ hg s (by tauto)
  have g3 : ∀ s ∈ f3.1, GoodS rd S w σ s := fun s hs ↦ hg s (by tauto)
  have gm1 : Good rd S w σ (.mul (.n f1.2.2) (.n f0.2.1) (.n f1.2.1)) := hg (vsMul _ _ _) (by tauto)
  have gm2 : Good rd S w σ (.mul (.n f2.2.2) (.n f1.2.2) (.n f2.2.1)) := hg (vsMul _ _ _) (by tauto)
  have gm3 : Good rd S w σ (.mul (.n f3.2.2) (.n f2.2.2) (.n f3.2.1)) := hg (vsMul _ _ _) (by tauto)
  simp only [Good] at gm1 gm2 gm3
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨show f0.2.1 < f1.2.2 by omega,
    show f1.2.1 < f1.2.2 by omega⟩)] at gm1
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨show f1.2.2 < f2.2.2 by omega,
    show f2.2.1 < f2.2.2 by omega⟩)] at gm2
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨show f2.2.2 < f3.2.2 by omega,
    show f3.2.1 < f3.2.2 by omega⟩)] at gm3
  have e0 := (eqwFactor_complete (C := C) (kret := kret) (next := True) g0 (hS v 0 le_rfl) l0
    trivial).1
  have e1 := (eqwFactor_complete (C := C) (kret := kret) (next := True) g1 (hS _ 1 (by omega)) l1
    trivial).1
  have e2 := (eqwFactor_complete (C := C) (kret := kret) (next := True) g2 (hS _ 2 (by omega)) l2
    trivial).1
  have e3 := (eqwFactor_complete (C := C) (kret := kret) (next := True) g3 (hS _ 3 (by omega)) l3
    trivial).1
  refine ⟨by rw [gm3, gm2, gm1, e0, e1, e2, e3, testBit_eqAt], ?_⟩
  simp only [holdsList_append]
  refine (eqwFactor_complete g0 (hS v 0 le_rfl) l0 ?_).2
  refine (eqwFactor_complete g1 (hS _ 1 (by omega)) l1 ?_).2
  simp only [Stmt.HoldsList, Stmt.Holds, vsMul]
  refine ⟨gm1, ?_⟩
  refine (eqwFactor_complete g2 (hS _ 2 (by omega)) l2 ?_).2
  refine ⟨gm2, ?_⟩
  refine (eqwFactor_complete g3 (hS _ 3 (by omega)) l3 ?_).2
  exact ⟨gm3, hn⟩
/-- The only loads through `bus_alpha` (`346`) the evaluation list stores are the challenges'. -/
def alphaStoreB : Atom → Bool
  | .load d (.n 346) _ => decide (d.idx < 428)
  | _ => true

theorem vsSL_alpha : vsSL.all alphaStoreB = true := by decide +kernel

theorem vsSL_alpha_notS {d off : ℕ} (hd : 428 ≤ d) : Atom.load (.n d) (.n 346) off ∉ vsSL := by
  intro h
  have := List.all_eq_true.mp vsSL_alpha _ h
  simp only [alphaStoreB, decide_eq_true_eq] at this
  exact absurd this (by show ¬ d < 428; omega)

theorem vsFpwT_noNe : vsFpwT.all noNeB = true := by decide +kernel

theorem vsFpwStart_ge : ∀ x < 16, 428 ≤ vsFpwStart x := by decide +kernel

variable {args : List E}

theorem vsFpwT_good (hl : args.length = 6) :
    ∀ s ∈ vsFpwT, GoodS rd vsSL w (vsσ rd w args) s := by
  intro s hs
  have h := vs_goodS (rd := rd) (w := w) hl (vs_mem_slice (n := 346) (blk := vsFpwT)
    (by decide +kernel) hs)
  rwa [fixNe_of_noNe (List.all_eq_true.mp vsFpwT_noNe s hs)] at h

/-- The sixteen weights, honestly. -/
theorem vsFpw_loop (hl : args.length = 6) {a0 a1 a2 a3 : E}
    (ha : ReadsAt rd (vsσ rd w args (.n 346)) [a0, a1, a2, a3])
    (hfp : ReadsAt rd (vsσ rd w args (.n 427)) (eqKernel [a0, a1, a2, a3]))
    {C : CallRel} {kret : List E → Prop} :
    ∀ l : List ℕ, (∀ x ∈ l, x < 16) → ∀ {nx : Prop}, nx →
      Stmt.HoldsList C rd (vsσ rd w args) (l.flatMap fun x ↦
        (vsEqwT x (vsFpwStart x)).1 ++ [vsLd (vsEqwT x (vsFpwStart x)).2.1 427 x]) nx kret
  | [], _, _, h => h
  | x :: l, hx, nx, h => by
    have hG := vsFpwT_good (rd := rd) (w := w) hl
    have h16 := hx x List.mem_cons_self
    have hmem : ∀ s ∈ (vsEqwT x (vsFpwStart x)).1 ++ [vsLd (vsEqwT x (vsFpwStart x)).2.1 427 x],
        s ∈ vsFpwT := fun s hs ↦ by
      rw [vsFpwT]
      exact List.mem_append_left _ (List.mem_cons_of_mem _
        (List.mem_flatMap.2 ⟨x, List.mem_range.2 h16, hs⟩))
    have hS : ∀ d off, vsFpwStart x ≤ d → Atom.load (.n d) (.n 346) off ∉ vsSL :=
      fun d off hd ↦ vsSL_alpha_notS (by have := vsFpwStart_ge x h16; omega)
    obtain ⟨e, -⟩ := eqw_complete (C := C) (kret := kret) (next := True)
      (fun s hs ↦ hG s (hmem s (List.mem_append_left _ hs))) hS ha trivial
    rw [List.flatMap_cons, holdsList_append, holdsList_append]
    refine (eqw_complete (fun s hs ↦ hG s (hmem s (List.mem_append_left _ hs))) hS ha ?_).2
    simp only [Stmt.HoldsList, Stmt.Holds, vsLd]
    refine ⟨?_, vsFpw_loop hl ha hfp l (fun y hy ↦ hx y (List.mem_cons_of_mem _ hy)) h⟩
    show LoadHolds rd _ _ _
    rw [e]
    have hk : x < (eqKernel [a0, a1, a2, a3]).length := by rw [eqKernel_length]; simp; omega
    have := hfp x hk
    rwa [← List.getD_eq_getElem _ 0 hk, eqKernel_getD, ite_eq_left_of_eq_true _ _
      (eq_true (by simp; omega))] at this

end
end LeanVM.Guest.B1.VerifySub
