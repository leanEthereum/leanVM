module

public import Common.Indiff.Bound

@[expose] public section

/-!
# Indifferentiability of the sponge from a random oracle

**Theorem** (`indifferentiability`). Let `D` be a distinguisher that makes at most `q` calls to
the permutation in all — its own forward and inverse queries, and the sponge's calls for its
hash queries, `|pad m|` per message `m` (`queryCost`). For every event `p` of its output,

  `|Pr[D^{sponge^π, π, π⁻¹} ∈ p] − Pr[D^{H, S^H} ∈ p]|`
  `  ≤ q · q / |S| + (q (2q + 1) + q (q + 1)) / |C|`

where `π` is a uniformly random permutation of the state type `S = (Dg × E) × C`, `H` a random
oracle, `S` the simulator of `Common.Indiff.Defs`, and `|C|` the number of capacities
(`indiffBound`). This is the indifferentiability of the sponge construction of Bertoni, Daemen,
Peeters and Van Assche (EUROCRYPT 2008) with inverse queries, for a single-squeeze output that is
a projection of the rate.

The proof chains the games of the previous modules:

1. the real world over a random permutation and over a random function differ by `q² / |S|`
   (`realGame_funGame_le`);
2. the real world over a random function is the combined game answering with its full view
   (`combReal_run_evalDistEq`);
3. the combined game's two sides are identical until their answers differ (`diff`), which
   requires a visible or a hidden collision (`diff_imp_bad_or_EC`);
4. the collisions have the same probability once the sponge's path queries are postponed
   (`visRun_true_evalDistEq_false`), where they are at most `(q (2q + 1) + q (q + 1)) / |C|`
   (`prEvent_visRun_le`);
5. the combined game's ideal side is the ideal world (`map_run_combIdeal`,
   `map_run_visImpl_false`, `idealTGame_evalDistEq_idealGame`).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Common

/-- **The indifferentiability bound** for `q` permutation calls, `nS` states and `nC` capacities:
`q · q / nS + (q (2q + 1) + q (q + 1)) / nC`. -/
noncomputable def indiffBound (nS nC q : ℕ) : ℝ≥0∞ :=
  q * (q / (nS : ℝ≥0∞)) + ((q * (2 * q + 1) + q * (q + 1) : ℕ) : ℝ≥0∞) / nC

section Setting

variable {Dg E C Msg : Type}
  [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C)

/-- While no answer has differed, the combined game's two answers agree. -/
theorem combStep_answer_eq (t : (dSpec Msg Dg (SpState Dg E C)).Domain) (cs : CState Dg E C Msg)
    (c : ACache Msg Dg E C) {w} (hw : w ∈ support ((simulateQ (aSpec Msg Dg E C).romImpl
      ((combStep P iv t).run cs)).run c)) :
    (w.1.2.diff = false → w.1.1.1 = w.1.1.2) ∧ (cs.diff = true → w.1.2.diff = true) := by
  rcases t with n | m | x | y
  · rw [combStep_inl_run] at hw
    simp only [support_map, Set.mem_image] at hw
    obtain ⟨u, -, rfl⟩ := hw
    exact ⟨fun _ ↦ rfl, id⟩
  · obtain ⟨w', c₁, d, -, -, hz⟩ := combHash_support P iv m cs c hw
    rw [hz]
    simp only [hashOut, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_not]
    exact ⟨fun h ↦ h.2, fun h ↦ by simp [h]⟩
  · obtain ⟨u, r, -, hz⟩ := combFwd_support P iv x cs c hw
    rw [hz]
    simp only [fwdOut, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_not]
    exact ⟨fun h ↦ h.2, fun h ↦ by simp [h]⟩
  · obtain ⟨u, rfl⟩ := combInv_support iv y cs c hw
    simp only [invOut, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_not]
    exact ⟨fun h ↦ h.2, fun h ↦ by simp [h]⟩

/-- One step of the folded combined game answering with the simulator. -/
theorem foldIdeal_run (t : (dSpec Msg Dg (SpState Dg E C)).Domain) (cs : CState Dg E C Msg)
    (c : ACache Msg Dg E C) :
    ((foldIdeal P iv) t).run (cs, c) = (fun z ↦ (z.1.1.2, (z.1.2, z.2))) <$>
      (simulateQ (aSpec Msg Dg E C).romImpl ((combStep P iv t).run cs)).run c := by
  rw [foldIdeal, foldRO_run]
  simp [combIdeal, StateT.run_map, simulateQ_map, Functor.map_map]

/-- The combined game's two answers agree on every step that does not raise `diff`. -/
theorem comb_agree (t : (dSpec Msg Dg (SpState Dg E C)).Domain)
    (s : CState Dg E C Msg × ACache Msg Dg E C) (r : _ → Prop) :
    Pr{let z ← ((foldReal P iv) t).run s}[r z ∧ ¬ z.2.1.diff = true] =
      Pr{let z ← ((foldIdeal P iv) t).run s}[r z ∧ ¬ z.2.1.diff = true] := by
  rw [foldReal_run, foldIdeal_run, prEvent_map, prEvent_map]
  refine prEvent_congr_of_support _ _ _ fun w hw ↦ ?_
  constructor
  · rintro ⟨h1, h2⟩
    rw [← (combStep_answer_eq P iv t s.1 s.2 hw).1 (by simpa using h2)]
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    rw [(combStep_answer_eq P iv t s.1 s.2 hw).1 (by simpa using h2)]
    exact ⟨h1, h2⟩

/-- A differing answer stays recorded. -/
theorem comb_mono (sel : (t : (dSpec Msg Dg (SpState Dg E C)).Domain) →
      (dSpec Msg Dg (SpState Dg E C)).Range t × (dSpec Msg Dg (SpState Dg E C)).Range t →
        (dSpec Msg Dg (SpState Dg E C)).Range t)
    (t : (dSpec Msg Dg (SpState Dg E C)).Domain) (s : CState Dg E C Msg × ACache Msg Dg E C)
    (hs : s.1.diff = true) {z}
    (hz : z ∈ support ((foldRO (fun t ↦ sel t <$> combStep P iv t) t).run s)) :
    z.2.1.diff = true := by
  obtain ⟨w, hw, hz2⟩ := mem_support_fold_comb P iv t s sel hz
  rw [hz2]
  exact (combStep_answer_eq P iv t s.1 s.2 hw).2 hs

/-- The collision probability of the combined game's ideal side is bounded. -/
theorem prEvent_comb_bad_or_EC_le {α : Type} (D : OracleComp (dSpec Msg Dg (SpState Dg E C)) α)
    (q : ℕ) (hD : QueryCostAtMost D (queryCost (Dg := Dg) P) q) :
    Pr{let z ← (simulateQ (foldIdeal P iv) D).run ((CState.init iv : CState Dg E C Msg), ∅)}[
      z.2.1.bad = true ∨ EC P iv z.2.1.vis z.2.2] ≤
      ((q * (2 * q + 1) + q * (q + 1) : ℕ) : ℝ≥0∞) / (Fintype.card C : ℝ≥0∞) := by
  calc _ = Pr{let z ← (simulateQ (aSpec Msg Dg E C).romImpl
        ((simulateQ (visImpl P iv true) D).run (SimState.init iv, [], false))).run ∅}[
        z.1.2.2.2 = true ∨ EC P iv z.1.2 z.2] := ?_
    _ ≤ Pr{let z ← (simulateQ (aSpec Msg Dg E C).romImpl
        (visRun P iv false D (SimState.init iv, [], false))).run ∅}[
        z.1.2.2.2 = true ∨ EC P iv z.1.2 z.2] := ?_
    _ ≤ _ := prEvent_visRun_le P iv D q hD
  · -- the folded ideal side is the visible game with path queries
    have h1 := run_simulateQ_foldRO (combIdeal P iv) D (CState.init iv : CState Dg E C Msg)
      (∅ : ACache Msg Dg E C)
    have h2 := map_run_combIdeal P iv D (CState.init iv : CState Dg E C Msg)
    have h3 := congrArg (fun X ↦ (simulateQ (aSpec Msg Dg E C).romImpl X).run
      (∅ : ACache Msg Dg E C)) h2
    simp only [simulateQ_map, StateT.run_map] at h3
    rw [h1, Functor.map_map] at h3
    have h4 := congrArg (fun X ↦ Pr{let z ← X}[z.1.2.2.2 = true ∨ EC P iv z.1.2 z.2]) h3
    simp only [prEvent_map] at h4
    exact h4
  · -- the end phase only adds cached answers
    rw [← (visRun_true_evalDistEq_false P iv D _ ∅).prEvent_eq]
    simp only [visRun, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
    conv_lhs => rw [← bind_pure ((simulateQ (aSpec Msg Dg E C).romImpl
      ((simulateQ (visImpl P iv true) D).run (SimState.init iv, [], false))).run ∅)]
    refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun w _ ↦ ?_
    classical
    by_cases hw : w.1.2.2.2 = true ∨ EC P iv w.1.2 w.2
    · rw [prEvent_pure, prEvent_eq_one_of_forall_mem_support _ _ fun z hz ↦ ?_]
      · simp [hw]
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
        obtain ⟨e, he, rfl⟩ := hz
        have hle := (endPhase_support P _ w.2 he).1
        rcases hw with hw | ⟨β, v, hβ, hv, h⟩
        · exact Or.inl hw
        · refine Or.inr ⟨β, v, hβ, valC_mono P hle hv, ?_⟩
          rcases h with h | ⟨γ, w', hγ, hne, hw', hwv⟩
          · exact Or.inl h
          · exact Or.inr ⟨γ, w', hγ, hne, valC_mono P hle hw', hwv⟩
    · simp [hw]

/-- The output of a visible game run with the end phase is the output of the run without it. -/
theorem visRun_output (pre : Bool) {α : Type} (D : OracleComp (dSpec Msg Dg (SpState Dg E C)) α)
    (vs : VState Dg E C Msg) (c : ACache Msg Dg E C) :
    (fun z ↦ z.1.1) <$> (simulateQ (aSpec Msg Dg E C).romImpl (visRun P iv pre D vs)).run c =ᵈ
      (simulateQ (aSpec Msg Dg E C).romImpl ((simulateQ (visImpl P iv pre) D).run' vs)).run' c := by
  simp only [visRun, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, map_bind,
    map_pure, StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map]
  rw [map_eq_bind_pure_comp]
  exact EvalDistEq.bind_right _ fun w ↦ EvalDistEq.bind_const _ _

/-- **The combined game's ideal side is the ideal world.** -/
theorem foldIdeal_evalDistEq_idealGame {α : Type}
    (D : OracleComp (dSpec Msg Dg (SpState Dg E C)) α) :
    (simulateQ (foldIdeal P iv) D).run' ((CState.init iv : CState Dg E C Msg), ∅) =ᵈ
      idealGame P iv D := by
  rw [foldIdeal, ← run'_simulateQ_foldRO]
  have h2 := map_run_combIdeal P iv D (CState.init iv : CState Dg E C Msg)
  have hv : (simulateQ (combIdeal P iv) D).run' (CState.init iv : CState Dg E C Msg) =
      (simulateQ (visImpl P iv true) D).run' (SimState.init iv, [], false) := by
    have h2' : Prod.map id CState.vis <$> (simulateQ (combIdeal P iv) D).run
        (CState.init iv : CState Dg E C Msg) =
        (simulateQ (visImpl P iv true) D).run (SimState.init iv, [], false) := h2
    rw [StateT.run'_eq, StateT.run'_eq, ← h2', Functor.map_map]
    rfl
  have hf : (simulateQ (visImpl P iv false) D).run' ((SimState.init iv : SimState Dg E C),
      ([] : List Msg), false) = (simulateQ (idealTImpl P) D).run' (SimState.init iv) := by
    have h3 : Prod.map id Prod.fst <$> (simulateQ (visImpl P iv false) D).run
        ((SimState.init iv : SimState Dg E C), ([] : List Msg), false) =
        (simulateQ (idealTImpl P) D).run (SimState.init iv) :=
      map_run_visImpl_false P iv D _
    rw [StateT.run'_eq, StateT.run'_eq, ← h3, Functor.map_map]
    rfl
  rw [hv]
  calc _ =ᵈ (fun z ↦ z.1.1) <$> (simulateQ (aSpec Msg Dg E C).romImpl
        (visRun P iv true D (SimState.init iv, [], false))).run ∅ :=
          (visRun_output P iv _ D _ _).symm
    _ =ᵈ (fun z ↦ z.1.1) <$> (simulateQ (aSpec Msg Dg E C).romImpl
        (visRun P iv false D (SimState.init iv, [], false))).run ∅ :=
          (visRun_true_evalDistEq_false P iv D _ _).map _
    _ =ᵈ _ := visRun_output P iv _ D _ _
    _ = _ := by rw [hf]
    _ =ᵈ _ := idealTGame_evalDistEq_idealGame P iv D

/-- **Indifferentiability of the sponge.** For a distinguisher `D` making at most `q` permutation
calls in all (its own and the sponge's: `queryCost`), every event `p` of its output has
probabilities in the real world (`H = sponge^π`, `π`, `π⁻¹` for a random permutation `π`) and the
ideal world (`H` a random oracle, `π` and `π⁻¹` answered by the simulator) within
`indiffBound |S| |C| q = q² / |S| + (q (2q + 1) + q (q + 1)) / |C|`. -/
theorem indifferentiability {α : Type} (D : OracleComp (dSpec Msg Dg (SpState Dg E C)) α)
    (q : ℕ) (hD : QueryCostAtMost D (queryCost (Dg := Dg) P) q) (p : α → Prop) :
    Pr{let a ← realGame P iv D}[p a] ≤ Pr{let a ← idealGame P iv D}[p a] +
        indiffBound (Fintype.card (SpState Dg E C)) (Fintype.card C) q ∧
      Pr{let a ← idealGame P iv D}[p a] ≤ Pr{let a ← realGame P iv D}[p a] +
        indiffBound (Fintype.card (SpState Dg E C)) (Fintype.card C) q := by
  set s₀ := ((CState.init iv : CState Dg E C Msg), (∅ : ACache Msg Dg E C))
  obtain ⟨hRF, hFR⟩ := realGame_funGame_le P iv D q hD p
  have hFun := (combReal_run_evalDistEq P iv D).prEvent_eq p
  have hIdeal := (foldIdeal_evalDistEq_idealGame P iv D).prEvent_eq p
  -- the combined game's two sides are identical until `diff`
  have hRI := prEvent_run_le_add_bad (spec' := unifSpec) (foldReal P iv) (foldIdeal P iv)
    (fun s ↦ s.1.diff = true) (fun t s _ r ↦ comb_agree P iv t s r)
    (fun t s hs z hz ↦ comb_mono P iv (fun _ p ↦ p.1) t s hs hz)
    (fun t s hs z hz ↦ comb_mono P iv (fun _ p ↦ p.2) t s hs hz) D s₀ p
  have hIR := prEvent_run_le_add_bad (spec' := unifSpec) (foldIdeal P iv) (foldReal P iv)
    (fun s ↦ s.1.diff = true) (fun t s _ r ↦ (comb_agree P iv t s r).symm)
    (fun t s hs z hz ↦ comb_mono P iv (fun _ p ↦ p.2) t s hs hz)
    (fun t s hs z hz ↦ comb_mono P iv (fun _ p ↦ p.1) t s hs hz) D s₀ p
  have hbadEq := prEvent_run_bad_eq (spec' := unifSpec) (foldReal P iv) (foldIdeal P iv)
    (fun s ↦ s.1.diff = true) (fun t s _ r ↦ comb_agree P iv t s r)
    (fun t s hs z hz ↦ comb_mono P iv (fun _ p ↦ p.1) t s hs hz)
    (fun t s hs z hz ↦ comb_mono P iv (fun _ p ↦ p.2) t s hs hz) D s₀
  -- a differing answer needs a collision
  have hdiff : Pr{let z ← (simulateQ (foldIdeal P iv) D).run s₀}[z.2.1.diff = true] ≤
      ((q * (2 * q + 1) + q * (q + 1) : ℕ) : ℝ≥0∞) / (Fintype.card C : ℝ≥0∞) :=
    (prEvent_mono_of_support _ _ _ fun z hz h ↦
      diff_imp_bad_or_EC P iv (fun _ p ↦ p.2) D hz h).trans (prEvent_comb_bad_or_EC_le P iv D q hD)
  rw [StateT.run'_eq, prEvent_map] at hFun hIdeal
  unfold indiffBound
  constructor
  · calc _ ≤ _ := hRF
      _ = Pr{let z ← (simulateQ (foldReal P iv) D).run s₀}[p z.1] +
          q * (q / (Fintype.card (SpState Dg E C) : ℝ≥0∞)) := by rw [← hFun]
      _ ≤ (Pr{let z ← (simulateQ (foldIdeal P iv) D).run s₀}[p z.1] +
          Pr{let z ← (simulateQ (foldIdeal P iv) D).run s₀}[z.2.1.diff = true]) +
          q * (q / (Fintype.card (SpState Dg E C) : ℝ≥0∞)) := by gcongr
      _ ≤ _ := by
          rw [hIdeal, add_assoc]
          exact add_le_add le_rfl ((add_comm _ _).le.trans (add_le_add le_rfl hdiff))
  · calc _ = Pr{let z ← (simulateQ (foldIdeal P iv) D).run s₀}[p z.1] := hIdeal.symm
      _ ≤ Pr{let z ← (simulateQ (foldReal P iv) D).run s₀}[p z.1] +
          Pr{let z ← (simulateQ (foldReal P iv) D).run s₀}[z.2.1.diff = true] := hIR
      _ ≤ _ := by
          rw [hFun, hbadEq]
          refine (add_le_add hFR hdiff).trans (le_of_eq ?_)
          rw [add_assoc]

end Setting

end Common
