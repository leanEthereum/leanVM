/-
  LeanVM.Guest.Backend.Sound.Fn

  Placement of a function is sound.
-/

module

public import LeanVM.Guest.Backend.Sound.Body

/-!
# Placement of a function
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- What a success of `placeFn` is: its checks passed and the walk of the body succeeded. -/
theorem placeFn_ok {loops : Loops} {sigs : Std.HashMap String (Nat × Nat)} {tables tables' : Tables}
    {tf : TracedFn} {pf : Placed} (h : placeFn loops sigs tables tf = .ok (pf, tables')) :
    ∃ st' : St, placeBody tf (ctxOf loops sigs tf) (initSt loops tables tf) = .ok ((), st') ∧
      pf = ⟨{ name := tf.core.name, body := st'.out.toList, frameSize := st'.next }, st'.locs⟩ ∧
      tables' = st'.tables ∧ st'.next < 2 ^ 64 ∧
      ((loops[tf.core.name]?).any (·.registered) = true → (sigOf tf).2 = 0) ∧
      ∃ vs, tf.core.body.getLast? = some (.ret vs) := by
  unfold placeFn at h
  split at h
  · cases h
  · next hlf =>
    split at h
    · next vs hvs =>
      split at h
      · cases h
      · next st' hrun =>
        split at h
        · cases h
        · rename_i hlt
          cases h
          refine ⟨st', hrun, rfl, rfl, Nat.lt_of_not_le hlt, fun hreg => ?_, vs, hvs⟩
          simpa [hreg] using hlf
    · cases h

/-- A block ending in a `return` holds whatever follows it. -/
theorem holdsList_ret_any {C : CallRel} {rd : Reader} {σ : Val} {ss : List Stmt} {vs : List V}
    (h : ss.getLast? = some (.ret vs)) {next next' : Prop} {kret : List E → Prop}
    (hl : Stmt.HoldsList C rd σ ss next kret) : Stmt.HoldsList C rd σ ss next' kret := by
  obtain ⟨init, rfl⟩ := List.getLast?_eq_some_iff.mp h
  rw [holdsList_append] at hl ⊢
  exact hl

/-- The pools a function's walk starts with hold: there is none but, in a registered loop's
frame, the cell past the arguments holding the frame's own pointer. -/
theorem poolOK_init {κ : ℕ} {L : MemoryImage κ} {fp : K} {loops : Loops} {tables : Tables}
    {tf : TracedFn} (hr0 : (loops[tf.core.name]?).any (·.registered) = true → (sigOf tf).2 = 0)
    (hself : (loops[tf.core.name]?).any (·.registered) = true →
      wd L fp (2 + (sigOf tf).1) = ofK fp) :
    PoolOK L fp (initSt loops tables tf).scope := by
  refine ⟨fun k o h => ?_, fun k o h => ?_, fun k o h => ?_, fun k o h => ?_, fun c l h => ?_,
    fun o h => ?_⟩
  · simp [initSt] at h
  · simp [initSt] at h
  · simp [initSt] at h
  · simp [initSt] at h
  · simp [initSt] at h
  · simp only [initSt] at h
    split at h
    · next hreg =>
      cases h
      rw [hr0 hreg, Nat.add_zero]
      exact hself hreg
    · cases h

/-- **Placement of a function is sound**, on any trace with no `chain` event. -/
theorem placeFn_sound {loops : Loops} {sigs : Std.HashMap String (Nat × Nat)} {tables : Tables}
    {tf : TracedFn} (hnc : NoChain tf) : PlaceFnSound loops sigs tables tf := by
  intro pf tables' h hok κ Γ fp C U slots N kj kretP khalt kret env hfill hent hself hsem hobl hret
  obtain ⟨st', hrun, rfl, rfl, -, hr0, vs, hvs⟩ := placeFn_ok h
  have hnc' : ∀ e ∈ (ctxOf loops sigs tf).trace.toList, e.isChain = false := hnc
  have key : wpP (placeBody tf) (ctxOf loops sigs tf) (initSt loops tables tf) (fun _ st₃ =>
      Lays Γ fp st'.locs (ctxOf loops sigs tf) slots (blockSize st'.out.toList) True
        (initSt loops tables tf) st₃
        (OblList C U Γ.L.read (valP Γ.L fp st'.locs) tf.core.body)
        (fun next kret => (True ∧ ∀ b ∈ tf.core.params.zipIdx,
            valP Γ.L fp st'.locs b.1 = locVal Γ.L fp (.cell (2 + b.2))) ∧
          Stmt.HoldsList C Γ.L.read (valP Γ.L fp st'.locs) tf.core.body next kret)) := by
    unfold placeBody
    refine wp_bind.mpr fun _ st1 he1 => wp_bind.mpr fun _ st2 he2 => wp_bind.mpr fun _ st3 he3 =>
      wp_bind.mpr (wp_get.mpr ?_)
    have e1 := forM_spec (Γ := Γ) (fp := fp) (F := st'.locs) (ctx := ctxOf loops sigs tf)
      (R := fun b : V × ℕ => valP Γ.L fp st'.locs b.1 = locVal Γ.L fp (.cell (2 + b.2)))
      (fun b => bindTo_spec b.1 (.cell (2 + b.2))) _ _ _ st1 he1
    obtain ⟨-, l2⟩ := placeBlock_lays env hnc' tf.core.body st1
      (Plain.of_same ⟨rfl, rfl⟩ e1.same) _ st2 he2
    have e3 := flush_spec (Γ := Γ) (fp := fp) (F := st'.locs) hnc' [] st2 _ st3 he3
    have l := Lays.prefix e1 ((l2.suffix e3).weaken fun _ => trivial).withH
    split
    · exact wp_failP
    · exact wp_pure.mpr l
  obtain ⟨ps, ho, -, -, hm⟩ := key _ st' hrun
  have hps : st'.out.toList = ps := by simpa [initSt] using ho
  have hres := hm hok 0 N kj kretP khalt True True kret trivial (Sub.refl _)
    (poolOK_init hr0 hself) (by rw [hps]; omega) (hps ▸ hfill) hent (hps ▸ hsem) hobl
    (fun _ _ _ => trivial) (fun hk => hret (hk.imp (fun hm => eq_of_beq hm) id))
  refine ⟨?_, hres.2⟩
  apply List.ext_getElem (by simp [frameWords, sigOf])
  intro k h1 h2
  have hk : k < tf.core.params.length := by simpa using h1
  have := hres.1.2 (tf.core.params[k], k) (List.mem_iff_getElem.mpr ⟨k, by simpa using hk, by simp⟩)
  simp only [List.getElem_map, frameWords, List.getElem_range]
  exact this

end
end LeanVM.Guest.Backend
