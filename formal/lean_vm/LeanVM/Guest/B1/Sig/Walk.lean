/-
  LeanVM.Guest.B1.Sig.Walk

  The steps of a WOTS+C chain and a chain's walk from a digit (`walk`, G:2318-2331), sound and
  complete for `chainFrom` and `tipPair`.
-/

module

public import LeanVM.Guest.B1.Sig.Chain

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- `Completes` from a valuation already changed on the same range. -/
theorem Completes.of_ext {lo hi : Nat} {ss : List Stmt} {σ σ1 : Val} {P : Val → Prop}
    (he : Ext lo hi σ σ1) (h : Completes C rd lo hi ss σ1 P) : Completes C rd lo hi ss σ P :=
  let ⟨σ', he', hp, hh⟩ := h
  ⟨σ', fun v hv => (he' v hv).trans (he v hv), hp, hh⟩

theorem ext_update {lo hi k : Nat} (σ : Val) (e : E) (h1 : lo ≤ k) (h2 : k < hi) :
    Ext lo hi σ (Function.update σ (.n k) e) := fun _ hv =>
  Function.update_of_ne (hv k h1 h2) _ _

/-! ## The steps of a chain -/

/-- The fresh values of `m + 1` steps. -/
def stepsSize (lx : Bool) (m : Nat) : Nat := (stepSize lx + 2) * m + stepSize lx

theorem chainFrom_succ (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i m s : Nat) (v : E) :
    chainFrom lx pp adr idx i (m + 1) s v =
      chainFrom lx pp adr idx i m (s + 1) (hcell (stepCells lx pp adr idx i s v)).1 := rfl

theorem cSteps_sound {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true) {i : Nat}
    {t0 t1 : V} : ∀ (m s b : Nat) (v : V) {next : Prop} {kret : List E → Prop},
    Stmt.HoldsList C rd σ (cSteps w i t0 t1 m s b v) next kret →
      (σ t0, σ t1) = chainFrom w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i m s (σ v) ∧ next
  | 0, s, b, v, _, _, h => cStep_sound hmd h
  | m + 1, s, b, v, next, kret, h => by
      rw [cSteps, holdsList_append] at h
      obtain ⟨h1, h2⟩ := cStep_sound hmd h
      obtain ⟨h3, hn⟩ := cSteps_sound hmd m (s + 1) _ _ h2
      refine ⟨?_, hn⟩
      rw [h3, chainFrom_succ, ← congrArg Prod.fst h1]

theorem cSteps_below {w : Wots} {hi i : Nat} {t0 t1 : V} (hw : w.Below hi)
    (ht0 : ∃ k < hi, t0 = .n k) (ht1 : ∃ k < hi, t1 = .n k) :
    ∀ (m s b : Nat) (v : V), (∃ k < hi, v = .n k) → b + stepsSize w.lx m ≤ hi →
      NumBelow hi (Stmt.valsList (cSteps w i t0 t1 m s b v))
  | 0, s, b, v, hv, hb => cStep_below hw hv ht0 ht1 (by simpa [stepsSize] using hb)
  | m + 1, s, b, v, hv, hb => by
      rw [cSteps, valsList_append]
      have hs : b + stepSize w.lx + 2 + stepsSize w.lx m ≤ hi := by
        have : stepsSize w.lx (m + 1) = stepSize w.lx + 2 + stepsSize w.lx m := by
          simp only [stepsSize]; ring
        omega
      exact (cStep_below hw hv ⟨_, by omega, rfl⟩ ⟨_, by omega, rfl⟩ (by omega)).append
        (cSteps_below hw ht0 ht1 m (s + 1) _ _ ⟨_, by omega, rfl⟩ (by omega))

/-- `Completes`, the valuation's change recorded in its postcondition. -/
theorem Completes.withExt {lo hi : Nat} {ss : List Stmt} {σ : Val} {P : Val → Prop}
    (h : Completes C rd lo hi ss σ P) : Completes C rd lo hi ss σ (fun σ' => P σ' ∧ Ext lo hi σ σ') :=
  let ⟨σ', he, hp, hh⟩ := h; ⟨σ', he, ⟨hp, he⟩, hh⟩

theorem Wots.Below.keep {w : Wots} {lo hi : Nat} {σ σ' : Val} (hw : w.Below lo) (he : Ext lo hi σ σ') :
    w.pp' σ' = w.pp' σ ∧ w.adr' σ' = w.adr' σ ∧ w.idx' σ' = w.idx' σ ∧ σ' w.md = σ w.md :=
  (hw.out (hi := hi)).keep he

theorem Wots.Canon.congr {w : Wots} {σ σ' : Val} (h : w.Canon σ)
    (hk : w.pp' σ' = w.pp' σ ∧ w.adr' σ' = w.adr' σ ∧ w.idx' σ' = w.idx' σ ∧ σ' w.md = σ w.md) :
    w.Canon σ' := by
  rw [Wots.Canon, hk.1, hk.2.1, hk.2.2.1]; exact h

theorem Ext.below {lo hi : Nat} {σ σ' : Val} (he : Ext lo hi σ σ') {v : V} (hv : ∃ j < lo, v = .n j) :
    σ' v = σ v := he.out (out_of_lt hv)

/-- **The steps of a chain are complete**: inputs below the range, canonical, the outputs preset
to the chain's end and numbered outside the range. -/
theorem cSteps_complete {w : Wots} {i : Nat} {t0 t1 : V} :
    ∀ (m s b : Nat) (v : V) (σ : Val), w.Below b → (∃ k < b, v = .n k) →
      Out b (b + stepsSize w.lx m) t0 → Out b (b + stepsSize w.lx m) t1 →
      σ w.md = mdw (stepCount w.lx) true → w.Canon σ → IsCanonical128 (σ v) →
      (σ t0, σ t1) = chainFrom w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i m s (σ v) →
      Completes C rd b (b + stepsSize w.lx m) (cSteps w i t0 t1 m s b v) σ (fun _ => True)
  | 0, s, b, v, σ, hw, hv, ht0, ht1, hmd, hc, hvc, ho => by
      simp only [stepsSize, Nat.mul_zero, Nat.zero_add] at *
      exact cStep_complete hw.out (out_of_lt hv) ht0 ht1 hmd hc hvc ho
  | m + 1, s, b, v, σ, hw, hv, ht0, ht1, hmd, hc, hvc, ho => by
      have hsz : stepsSize w.lx (m + 1) = stepSize w.lx + 2 + stepsSize w.lx m := by
        simp only [stepsSize]; ring
      rw [hsz] at ht0 ht1 ⊢
      set h := hcell (stepCells w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i s (σ v)) with hh
      set z := b + stepSize w.lx with hz
      let σ1 := Function.update (Function.update σ (.n z) h.1) (.n (z + 1)) h.2
      have he1' : Ext z (z + 2) σ σ1 :=
        (ext_update σ _ (by omega) (by omega)).comp (ext_update _ _ (by omega) (by omega))
      have he1 : Ext b (b + (stepSize w.lx + 2 + stepsSize w.lx m)) σ σ1 := he1'.mono (by omega) (by omega)
      have hk1 := (hw.mono (show b ≤ z by omega)).keep he1'
      have hv1 : σ1 v = σ v := he1'.below (let ⟨k, hk, e⟩ := hv; ⟨k, by omega, e⟩)
      have hσ1z : σ1 (.n z) = h.1 := by simp [σ1]
      have hσ1z' : σ1 (.n (z + 1)) = h.2 := by simp [σ1]
      have hc1 : w.Canon σ1 := hc.congr hk1
      refine Completes.of_ext he1 ?_
      rw [cSteps, ← hz]
      refine Completes.append (m := z + 2) (P := fun σ' => σ' (.n z) = h.1) (by omega) (by omega)
        ?_ ?_ ?_
      · exact cStep_below (hw.mono (by omega)) (let ⟨k, hk, e⟩ := hv; ⟨k, by omega, e⟩)
          ⟨z, by omega, rfl⟩ ⟨z + 1, by omega, rfl⟩ (by omega)
      · have := (cStep_complete (C := C) (rd := rd) (σ := σ1) (i := i) (s := s) (b := b) (v := v)
          (o0 := .n z) (o1 := .n (z + 1)) hw.out (out_of_lt hv)
          (out_of_ge ⟨z, by omega, rfl⟩) (out_of_ge ⟨z + 1, by omega, rfl⟩) (by rw [hk1.2.2.2, hmd]) hc1
          (by rw [hv1]; exact hvc) (by rw [hσ1z, hσ1z', hk1.1, hk1.2.1, hk1.2.2.1, hv1])).withExt
        exact this.mono le_rfl (by omega) fun σ' hp => by rw [hp.2.apply (by omega), hσ1z]
      · intro σ' he' hp
        have heσ : Ext b (z + 2) σ σ' := (he1'.mono (by omega) le_rfl).comp he'
        have hk' := hw.keep heσ
        have ht0' : Out b (z + 2) t0 := ht0.mono le_rfl (by omega)
        have ht1' : Out b (z + 2) t1 := ht1.mono le_rfl (by omega)
        have := cSteps_complete m (s + 1) (z + 2) (.n z) σ' (hw.mono (by omega))
          ⟨z, by omega, rfl⟩ (ht0.mono (by omega) (by omega)) (ht1.mono (by omega) (by omega))
          (by rw [hk'.2.2.2, hmd]) (hc.congr hk') (by rw [hp]; exact (isCanonical128_hb _).1)
          (by rw [heσ.out ht0', heσ.out ht1', ho, chainFrom_succ, hk'.1, hk'.2.1, hk'.2.2.1, hp])
        rwa [show z + 2 + stepsSize w.lx m = b + (stepSize w.lx + 2 + stepsSize w.lx m) by omega] at this

/-! ## A chain's walk -/

theorem walkSize_eq (lx : Bool) {d : Nat} (hd : d ≠ 3) : walkSize lx d = 1 + stepsSize lx (2 - d) := by
  simp only [walkSize, hd, ↓reduceIte, stepsSize]; ring

theorem holds_hint_cons (h : Hint) (ss : List Stmt) (next : Prop) (kret : List E → Prop) (σ : Val) :
    Stmt.HoldsList C rd σ (.atom (.hint h) :: ss) next kret ↔ Stmt.HoldsList C rd σ ss next kret := by
  simp [Atom.Holds]

theorem Completes.hint_cons {lo hi : Nat} {ss : List Stmt} {σ : Val} {P : Val → Prop} (h : Hint)
    (hc : Completes C rd lo hi ss σ P) : Completes C rd lo hi (.atom (.hint h) :: ss) σ P :=
  let ⟨σ', he, hp, hh⟩ := hc; ⟨σ', he, hp, fun next kret hn => (holds_hint_cons h ss next kret σ').mpr (hh next kret hn)⟩

theorem cWalk_sound {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true) {i d b : Nat}
    {t0 t1 : V} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (cWalk w i d b t0 t1) next kret) :
    (∃ x, σ t0 = (tipPair w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i d x).1 ∧
      (d ≠ 3 → σ t1 = (tipPair w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i d x).2)) ∧ next := by
  unfold cWalk at h
  by_cases hd : d = 3
  · simp only [hd, ↓reduceIte, hintW, holds_hint_cons] at h
    exact ⟨⟨σ t0, by simp [tipPair, hd], fun h' => absurd hd h'⟩, h⟩
  · simp only [hd, ↓reduceIte, hintW, holds_hint_cons] at h
    obtain ⟨ho, hn⟩ := cSteps_sound hmd _ _ _ _ h
    refine ⟨⟨σ (.n b), ?_, fun _ => ?_⟩, hn⟩ <;> simp only [tipPair, hd, ↓reduceIte, ← ho]

theorem cWalk_below {w : Wots} {hi i d b : Nat} {t0 t1 : V} (hw : w.Below hi)
    (ht0 : ∃ k < hi, t0 = .n k) (ht1 : ∃ k < hi, t1 = .n k) (hb : b + walkSize w.lx d ≤ hi) :
    NumBelow hi (Stmt.valsList (cWalk w i d b t0 t1)) := by
  unfold cWalk
  by_cases hd : d = 3
  · simp only [hd, ↓reduceIte]
    simpa [hintW, Stmt.vals, Atom.vals, Hint.vals, Dest.vals] using NumBelow.cons ht0 (NumBelow.nil hi)
  · simp only [hd, ↓reduceIte, hintW, valsList_cons]
    rw [walkSize_eq _ hd] at hb
    exact NumBelow.cons ⟨b, by omega, rfl⟩ (NumBelow.nil hi) |>.append
      (cSteps_below hw ht0 ht1 _ _ _ _ ⟨b, by omega, rfl⟩ (by omega))

/-- **A walk is complete**: from the value `x`, the tips preset to its end. -/
theorem cWalk_complete {w : Wots} {i d b : Nat} {t0 t1 : V} {σ : Val} (hw : w.Below b)
    (ht0 : Out b (b + walkSize w.lx d) t0) (ht1 : Out b (b + walkSize w.lx d) t1)
    (hmd : σ w.md = mdw (stepCount w.lx) true) (hc : w.Canon σ) {x : E} (hx : IsCanonical128 x)
    (ho0 : σ t0 = (tipPair w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i d x).1)
    (ho1 : d ≠ 3 → σ t1 = (tipPair w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i d x).2) :
    Completes C rd b (b + walkSize w.lx d) (cWalk w i d b t0 t1) σ (fun _ => True) := by
  unfold cWalk
  by_cases hd : d = 3
  · simp only [hd, ↓reduceIte, hintW]
    exact ⟨σ, Ext.refl _ _ _, trivial, fun next kret hn => (holds_hint_cons _ _ _ _ _).mpr hn⟩
  · simp only [hd, ↓reduceIte, hintW]
    apply Completes.hint_cons
    rw [walkSize_eq _ hd] at ht0 ht1 ⊢
    let σ1 := Function.update σ (.n b) x
    have he1 : Ext b (b + 1) σ σ1 := ext_update σ x le_rfl (by omega)
    have hk := hw.keep he1
    refine Completes.of_ext (he1.mono le_rfl (by omega)) ?_
    have := cSteps_complete (C := C) (rd := rd) (i := i) (t0 := t0) (t1 := t1) (2 - d) d (b + 1) (.n b) σ1
      (hw.mono (by omega)) ⟨b, by omega, rfl⟩ (ht0.mono (by omega) (by omega)) (ht1.mono (by omega) (by omega))
      (by rw [hk.2.2.2, hmd]) (hc.congr hk) (by simpa [σ1] using hx)
      (by
        rw [he1.out (ht0.mono le_rfl (by omega)), he1.out (ht1.mono le_rfl (by omega)), hk.1, hk.2.1,
          hk.2.2.1, ho0, ho1 hd]
        simp [tipPair, hd, σ1])
    exact this.mono (by omega) (by omega) fun _ h => h

end
end LeanVM.Guest.B1.Sig
