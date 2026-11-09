module

public import Common.Duplex.Budget
public import VCVio.OracleComp.EvalDist.Sum

@[expose] public section

/-!
# The duplex challenges are a random oracle of the roots, up to collisions

**Duplex lemma** (`duplex_le`). In the two-oracle random-oracle model (`H` a random oracle, `F` a
random function on states), consider a computation `B` making at most `N_B` calls of `F`, followed
by the challenges `chalP` of a root it chose, derived by the duplex over `F`, and a computation
`post` of the root's challenges using only coins and `H`. Its probability of success is at most
that of the computation where `B`'s calls of `F` are answered by the simulator and `post` receives
the challenges `G (r, j)` of a random oracle `G`, plus `N · (2N · εc)` with `N = N_B + n + 1` and
`εc` the largest probability of a capacity.

The proof: the simulator with lazily sampled challenges is the random function `F`
(`run'_simImpl_evalDistEq`); with the challenges sampled in advance as a table `g`
(`run'_romImpl_evalDistEq_eager`), and unless a collision of capacities occurs, the derived
challenges are the table's (`chal_ok`), and a collision occurs with probability at most
`N · (2N · εc)` (`prob_bad_le`).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec MeasureTheory
open Common
open Common.Duplex (GSpec hP gaP VSpec toV)
open scoped ENNReal

namespace Common

/-- **A pointwise union bound** over a shared prefix. -/
theorem prEvent_bind_le_add {α β γ δ : Type} (mx : ProbComp α) (f : α → ProbComp β)
    (g : α → ProbComp γ) (h : α → ProbComp δ) (P : β → Prop) (Q : γ → Prop) (R : δ → Prop)
    (hp : ∀ x ∈ support mx, Pr{let y ← f x}[P y] ≤ Pr{let y ← g x}[Q y] + Pr{let y ← h x}[R y]) :
    Pr{let y ← mx >>= f}[P y] ≤ Pr{let y ← mx >>= g}[Q y] + Pr{let y ← mx >>= h}[R y] := by
  simp only [OracleComp.prEvent_bind_eq_tsum]
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x ↦ ?_
  by_cases hx : x ∈ support mx
  · rw [← mul_add]; gcongr; exact hp x hx
  · simp [prEvent_eq_zero_of_not_mem_support mx hx]

/-- **A bound outside a bad event** of the prefix. -/
theorem prEvent_bind_le_of_good {α β : Type} (mx : ProbComp α) (f : α → ProbComp β)
    (B : α → Prop) (P : β → Prop) (a : ℝ≥0∞)
    (h : ∀ x ∈ support mx, ¬B x → Pr{let y ← f x}[P y] ≤ a) :
    Pr{let y ← mx >>= f}[P y] ≤ Pr{let x ← mx}[B x] + a := by
  classical
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete]
  calc ∫⁻ x, Pr{let y ← f x}[P y] ∂𝒟[mx]
      ≤ ∫⁻ x, ((if B x then 1 else 0) + a) ∂𝒟[mx] := by
        apply lintegral_mono_ae
        filter_upwards [ae_evalDist_of_forall_mem_support (p := fun x ↦
          Pr{let y ← f x}[P y] ≤ (if B x then 1 else 0) + a) _ fun x hx ↦ by
            by_cases hb : B x
            · simp only [hb, ↓reduceIte]; exact (prEvent_le_one _).trans le_self_add
            · simp only [hb, ↓reduceIte, zero_add]; exact h x hx hb] with x hx using hx
    _ ≤ Pr{let x ← mx}[B x] + a := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
        refine add_le_add (le_of_eq ?_) (mul_le_of_le_one_right' (evalDist_apply_univ_le_one _))
        rw [prEvent_eq_evalDist_of_discrete, ← lintegral_indicator_one MeasurableSet.of_discrete]
        exact lintegral_congr fun x ↦ by by_cases hb : B x <;> simp [hb, Set.indicator]

/-- **A pointwise bound with a constant**, averaged over a prefix. -/
theorem prEvent_bind_le_add_const {α β γ : Type} (mx : ProbComp α) (f : α → ProbComp β)
    (g : α → ProbComp γ) (P : β → Prop) (Q : γ → Prop) (a : ℝ≥0∞)
    (hp : ∀ x, Pr{let y ← f x}[P y] ≤ Pr{let y ← g x}[Q y] + a) :
    Pr{let y ← mx >>= f}[P y] ≤ Pr{let y ← mx >>= g}[Q y] + a := by
  simp only [OracleComp.prEvent_bind_eq_tsum]
  calc ∑' x, Pr{let z ← mx}[z = x] * Pr{let y ← f x}[P y]
      ≤ ∑' x, (Pr{let z ← mx}[z = x] * Pr{let y ← g x}[Q y] + Pr{let z ← mx}[z = x] * a) :=
        ENNReal.tsum_le_tsum fun x ↦ by rw [← mul_add]; gcongr; exact hp x
    _ = (∑' x, Pr{let z ← mx}[z = x] * Pr{let y ← g x}[Q y]) +
          (∑' x, Pr{let z ← mx}[z = x]) * a := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one mx))

/-- **A pointwise bound with a constant on the support**, averaged over a prefix. -/
theorem prEvent_bind_le_add_const_of_support {α β γ : Type} (mx : ProbComp α)
    (f : α → ProbComp β) (g : α → ProbComp γ) (P : β → Prop) (Q : γ → Prop) (a : ℝ≥0∞)
    (hp : ∀ x ∈ support mx, Pr{let y ← f x}[P y] ≤ Pr{let y ← g x}[Q y] + a) :
    Pr{let y ← mx >>= f}[P y] ≤ Pr{let y ← mx >>= g}[Q y] + a := by
  simp only [OracleComp.prEvent_bind_eq_tsum]
  calc ∑' x, Pr{let z ← mx}[z = x] * Pr{let y ← f x}[P y]
      ≤ ∑' x, (Pr{let z ← mx}[z = x] * Pr{let y ← g x}[Q y] + Pr{let z ← mx}[z = x] * a) :=
        ENNReal.tsum_le_tsum fun x ↦ by
          by_cases hx : x ∈ support mx
          · rw [← mul_add]; gcongr; exact hp x hx
          · simp [prEvent_eq_zero_of_not_mem_support mx hx]
    _ = (∑' x, Pr{let z ← mx}[z = x] * Pr{let y ← g x}[Q y]) +
          (∑' x, Pr{let z ← mx}[z = x]) * a := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one mx))

/-- Events of binds with pointwise equal events are equal. -/
theorem prEvent_bind_congr {α β γ : Type} (mx : ProbComp α) (f : α → ProbComp β)
    (g : α → ProbComp γ) (P : β → Prop) (Q : γ → Prop)
    (hp : ∀ x, Pr{let y ← f x}[P y] = Pr{let y ← g x}[Q y]) :
    Pr{let y ← mx >>= f}[P y] = Pr{let y ← mx >>= g}[Q y] := by
  simp only [OracleComp.prEvent_bind_eq_tsum, hp]

/-- **A discarded first hash query is invisible** in the random oracle model. -/
theorem run'_hq_bind_evalDistEq {ι : Type} [DecidableEq ι] {hs : OracleSpec.{0, 0} ι}
    [∀ t : hs.Domain, SampleableType (hs.Range t)] {α : Type} (t : ι)
    (oa : OracleComp (unifSpec + hs) α) (c : hs.QueryCache) :
    (simulateQ hs.romImpl (hq t >>= fun _ ↦ oa)).run' c =ᵈ (simulateQ hs.romImpl oa).run' c := by
  have h := (run_query_bind_evalDistEq t oa c).map Prod.fst
  rw [← StateT.run'_eq] at h
  refine h.trans ?_
  rw [simulateQ_bind, StateT.run_bind, map_bind, StateT.run'_eq, map_eq_bind_pure_comp]
  refine EvalDistEq.bind_right _ fun z ↦ ?_
  simp only [simulateQ_bind, StateT.run_bind, run_hq, simulateQ_pure, StateT.run_pure,
    map_bind, map_pure, Function.comp_apply]
  exact EvalDistEq.bind_const _ _

end Common

namespace Common.SeedDuplex

variable {Msg Dg St Root Z W Cp : Type} {n : ℕ}
  [DecidableEq Msg] [DecidableEq St] [DecidableEq Root] [DecidableEq Cp]
  [SampleableType Dg] [SampleableType St] [SampleableType Z] [SampleableType W]
  [Fintype St] [Fintype Z] [Fintype W] [Fintype Root] [Nonempty Z]
  {D : DuplexSpec Msg Dg St Root Z W Cp n}

/-- A computation with coins and `H`, in the two-oracle model. -/
def embH : QueryImpl (unifSpec + roSpec Msg Dg) (OracleComp (Rom2 Msg Dg St))
  | .inl k => liftM ((Rom2 Msg Dg St).query (.inl k))
  | .inr m => hQ m

/-- A computation with coins and `H`, in the simulated world. -/
def embG : QueryImpl (unifSpec + roSpec Msg Dg) (OracleComp (unifSpec + GSpec Msg Dg Root Z n))
  | .inl k => liftM ((unifSpec + GSpec Msg Dg Root Z n).query (.inl k))
  | .inr m => hP m

theorem tab_coin_run (g : Tab Root Z n) (k : ℕ) (s : SimSt Dg St Root n)
    (c : (GSpec Msg Dg Root Z n).QueryCache) :
    (tabImpl D g (.inl k)).run (s, c) =
      (fun u ↦ (u, (s, c))) <$> (unifSpec.query k : ProbComp (Fin (k + 1))) := by
  rw [tabImpl, foldWith_run]
  simp only [simImpl, StateT.run_monadLift, monadLift_self, simulateQ_bind, StateT.run_bind,
    simulateQ_pure, StateT.run_pure]
  erw [simulateQ_eagerImpl_liftM]
  simp [Functor.map_map]

theorem tab_H_run (g : Tab Root Z n) (m : Msg) (s : SimSt Dg St Root n)
    (c : (GSpec Msg Dg Root Z n).QueryCache) :
    (tabImpl D g (.inr (.inl m))).run (s, c) =
      (fun dc ↦ (dc.1, ((if m = D.label then { s with x0 := some (D.init dc.1), iv := some dc.1 } else s), dc.2))) <$>
        roStep (hs := GSpec Msg Dg Root Z n) (.inl m) c := by
  rw [tabImpl, foldWith_run]
  simp only [simImpl, StateT.run_mk, simulateQ_bind, StateT.run_bind, simulateQ_pure,
    StateT.run_pure, tabOuter_hP, map_bind, map_pure]
  rw [map_eq_bind_pure_comp]
  rfl

theorem tabOuter_coin_run (g : Tab Root Z n) (k : ℕ) (c : (GSpec Msg Dg Root Z n).QueryCache) :
    (tabOuter (Msg := Msg) (Dg := Dg) g (.inl k)).run c =
      (fun u ↦ (u, c)) <$> (unifSpec.query k : ProbComp (Fin (k + 1))) :=
  unifFwdImpl_run' _ k c

/-- **A computation with coins and `H` sees only the cache.** -/
theorem post_indep (g : Tab Root Z n) {γ : Type} (P : OracleComp (unifSpec + roSpec Msg Dg) γ)
    (s : SimSt Dg St Root n) (c : (GSpec Msg Dg Root Z n).QueryCache) :
    (fun z ↦ (z.1, z.2.2)) <$> (simulateQ (tabImpl D g) (simulateQ embH P)).run (s, c) =ᵈ
      (simulateQ (tabOuter g) (simulateQ embG P)).run c := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  have := map_run_simulateQ_evalDistEq_of_inv (tabImpl D g ∘ₛ embH) (tabOuter g ∘ₛ embG)
    (fun _ ↦ True) Prod.snd (fun _ _ _ _ _ ↦ trivial) (fun t sc _ ↦ ?_) P (s, c) trivial
  · exact this
  · obtain ⟨s, c⟩ := sc
    rcases t with k | m
    · simp only [QueryImpl.apply_compose, embH, embG, simulateQ_spec_query]
      rw [tab_coin_run, tabOuter_coin_run, Functor.map_map]
      exact EvalDistEq.rfl
    · simp only [QueryImpl.apply_compose, embH, embG]
      rw [show simulateQ (tabImpl D g) (hQ (St := St) m) = tabImpl D g (.inr (.inl m)) from
        simulateQ_spec_query _ _, tab_H_run, Functor.map_map]
      rw [show (simulateQ (tabOuter g) (hP (Root := Root) (Z := Z) (n := n) m)).run c =
        roStep (.inl m) c from tabOuter_hP g m c]
      simp only [Prod.map]
      simp only [id_eq, Prod.mk.eta]
      exact (id_map (roStep (hs := GSpec Msg Dg Root Z n) (.inl m) c)).symm ▸ EvalDistEq.rfl

/-! ## Weights -/

theorem isWeightBound_hQ (m : Msg) :
    QueryCostAtMost (hQ (Dg := Dg) (St := St) m) (fCalls (Msg := Msg) (Dg := Dg) (St := St)) 0 :=
  isWeightBound_query (spec := Rom2 Msg Dg St) _ (.inr (.inl m))

theorem isWeightBound_fQ (x : St) :
    QueryCostAtMost (fQ (Msg := Msg) (Dg := Dg) x) (fCalls (Msg := Msg) (Dg := Dg) (St := St)) 1 :=
  isWeightBound_query (spec := Rom2 Msg Dg St) _ (.inr (.inr x))

theorem isWeightBound_chainP (k : ℕ) (y : St) :
    QueryCostAtMost (chainP D k y) (fCalls (Msg := Msg) (Dg := Dg) (St := St)) k := by
  induction k generalizing y with
  | zero => exact isWeightBound_pure _ _ _
  | succ k ih =>
    unfold chainP
    exact ((isWeightBound_fQ (Msg := Msg) (Dg := Dg) (D.next y)).bind fun y' ↦
      (ih y').bind fun zs ↦ isWeightBound_pure (D.out y' :: zs) _ 0).mono (by omega)

theorem isWeightBound_chalP (r : Root) :
    QueryCostAtMost (chalP D r) (fCalls (Msg := Msg) (Dg := Dg) (St := St)) (n + 1) := by
  unfold chalP
  have := D.n_pos
  exact ((isWeightBound_hQ (Dg := Dg) (St := St) D.label).bind fun iv ↦
    (isWeightBound_fQ (Msg := Msg) (Dg := Dg) (D.first r iv)).bind fun y₁ ↦
      (isWeightBound_chainP (D := D) (n - 1) y₁).bind fun zs ↦
        isWeightBound_pure (D.out y₁ :: zs) _ 0).mono (by omega)

/-! ## The challenges read from the table -/

/-- The challenges of a root, read from `G`. -/
def readVec [Inhabited Z] (r : Root) : OracleComp (unifSpec + GSpec Msg Dg Root Z n) (Fin n → Z) :=
  (fun l j ↦ l.getD j default) <$> (List.finRange n).mapM (gaP (Msg := Msg) (Dg := Dg) r)

/-- The challenges of a list. -/
def toVec [Inhabited Z] (zs : List Z) : Fin n → Z := fun j ↦ zs.getD j default

theorem mapM_gaP_run (g : Tab Root Z n) (r : Root) (l : List (Fin n))
    (c : (GSpec Msg Dg Root Z n).QueryCache) (hc : GFree c) :
    (simulateQ (tabOuter g) (l.mapM (gaP (Msg := Msg) (Dg := Dg) r))).run c =
      pure (l.map (g.at r), c) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.mapM_cons]
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
    rw [show simulateQ (tabOuter g) (gaP (Msg := Msg) (Dg := Dg) r j) =
      tabOuter g (.inr (.inr (r, j))) from simulateQ_spec_query _ _, tabOuter_G_run]
    simp only [hc (r, j), Option.getD_none, pure_bind]
    rw [ih]
    simp

theorem readVec_run [Inhabited Z] (g : Tab Root Z n) (r : Root)
    (c : (GSpec Msg Dg Root Z n).QueryCache) (hc : GFree c) :
    (simulateQ (tabOuter g) (readVec (Msg := Msg) (Dg := Dg) r)).run c = pure (g.at r, c) := by
  rw [readVec, simulateQ_map, StateT.run_map, mapM_gaP_run g r _ c hc]
  simp only [map_pure]
  congr 2
  funext j
  simp

/-! ## The table world, the label hashed first -/

theorem good_init (g : Tab Root Z n) (iv : Dg) :
    Good D g iv (({ (SimSt.init : SimSt Dg St Root n) with x0 := some (D.init iv), iv := some iv }),
      (∅ : (GSpec Msg Dg Root Z n).QueryCache).cacheQuery (.inl D.label) iv) := by
  refine ⟨⟨rfl, by simp [SimSt.init], rfl, by simp [SimSt.init],
    by simp [SimSt.init], by simp [SimSt.init], by simp [SimSt.init],
    fun r ↦ ⟨fun _ ↦ by simp [efflab, (D.dec_iff iv _ r).mpr rfl], by simp [SimSt.init]⟩,
    by simp [SimSt.init]⟩, fun d ↦ ?_, by simp⟩
  rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
  rfl

/-- Along the computation, the label hashed first: no collision, or a good state. -/
theorem prefix_inv (g : Tab Root Z n) {β : Type} (B : OracleComp (Rom2 Msg Dg St) β) :
    ∀ w ∈ support ((simulateQ (tabImpl D g) (hQ (St := St) D.label >>= fun _ ↦ B)).run
      ((SimSt.init : SimSt Dg St Root n), (∅ : (GSpec Msg Dg Root Z n).QueryCache))),
      GFree w.2.2 ∧ (w.2.1.bad = true ∨ ∃ iv, Good D g iv w.2) := by
  intro w hw
  rw [run_hQ_bind] at hw
  simp only [mem_support_bind_iff] at hw
  obtain ⟨w₀, hw₀, hw⟩ := hw
  rw [tab_H_run] at hw₀
  simp only [support_map, Set.mem_image] at hw₀
  obtain ⟨dc, hdc, rfl⟩ := hw₀
  rw [roStep_of_none (by rfl)] at hdc
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hdc
  obtain ⟨iv, -, rfl⟩ := hdc
  simp only [↓reduceIte] at hw
  refine inv_of_mem_support_run (tabImpl D g)
    (fun sc ↦ GFree sc.2 ∧ (sc.1.bad = true ∨ ∃ iv, Good D g iv sc))
    (fun t sc h z hz ↦ ⟨gfree_step g t sc h.1 hz, ?_⟩) B
    ⟨(good_init (D := D) g iv).gfree, Or.inr ⟨iv, good_init g iv⟩⟩ w hw
  rcases h.2 with hb | ⟨iv', hG⟩
  · exact Or.inl (tab_bad_mono g t sc.1 sc.2 h.1 hb hz)
  · cases hzb : z.2.1.bad
    · exact Or.inr ⟨iv', good_step g iv' t sc hG hz hzb⟩
    · exact Or.inl rfl

theorem toVec_of_chal [Inhabited Z] (g : Tab Root Z n) (r : Root) (zs : List Z)
    (hlen : zs.length = n) (hval : ∀ i (hi : i < zs.length), zs[i] = g.at r ⟨i, by omega⟩) :
    toVec zs = g.at r := by
  funext j
  simp only [toVec]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
    hval j (by omega)]

/-- The first part of a run, through the simulator then the table, is the table world's. -/
theorem run_prefix {β : Type} (g : Tab Root Z n) (P : OracleComp (Rom2 Msg Dg St) β) :
    (simulateQ (tabOuter g) ((simulateQ (simImpl D hP gaP) P).run' SimSt.init)).run ∅ =
      (fun z ↦ (z.1, z.2.2)) <$> (simulateQ (tabImpl D g) P).run (SimSt.init, ∅) := by
  rw [StateT.run'_eq, simulateQ_map, StateT.run_map, run_simulateQ_foldWith, Functor.map_map]
  rfl

/-- **The table world**: the derived challenges against the table's, up to a collision. -/
theorem tab_le [Inhabited Z] {εc : ℝ≥0∞}
    (hcap : ∀ c, Pr{let w ← ($ᵗ W : ProbComp W)}[D.capW w = c] ≤ εc) (g : Tab Root Z n)
    {β : Type} (B : OracleComp (Rom2 Msg Dg St) β) (NB : ℕ)
    (hB : QueryCostAtMost B (fCalls (Msg := Msg) (Dg := Dg) (St := St)) NB) (root : β → Root)
    (post : β → (Fin n → Z) → OracleComp (unifSpec + roSpec Msg Dg) Bool) :
    Pr{let b ← (simulateQ (tabImpl D g) ((hQ (St := St) D.label >>= fun _ ↦ B) >>= fun b ↦
        chalP D (root b) >>= fun zs ↦ simulateQ embH (post b (toVec zs)))).run'
        ((SimSt.init : SimSt Dg St Root n), (∅ : (GSpec Msg Dg Root Z n).QueryCache))}[b = true] ≤
      Pr{let b ← (simulateQ (tabOuter g) ((simulateQ (simImpl D hP gaP)
        (hQ (St := St) D.label >>= fun _ ↦ B)).run' SimSt.init >>= fun b ↦
          readVec (Msg := Msg) (Dg := Dg) (root b) >>= fun l ↦ simulateQ embG (post b l))).run' ∅}[
          b = true] +
        (NB + n + 1 : ℕ) * (2 * (NB + n + 1 : ℕ) * εc) := by
  have hL : (simulateQ (tabImpl D g) ((hQ (St := St) D.label >>= fun _ ↦ B) >>= fun b ↦
        chalP D (root b) >>= fun zs ↦ simulateQ embH (post b (toVec zs)))).run' ((SimSt.init : SimSt Dg St Root n), (∅ : (GSpec Msg Dg Root Z n).QueryCache)) =
      Prod.fst <$> (((simulateQ (tabImpl D g) (hQ (St := St) D.label >>= fun _ ↦ B)).run ((SimSt.init : SimSt Dg St Root n), (∅ : (GSpec Msg Dg Root Z n).QueryCache))) >>= fun p ↦ (simulateQ (tabImpl D g) (chalP D (root p.1) >>= fun zs ↦
        simulateQ embH (post p.1 (toVec zs)))).run p.2) := by
    rw [StateT.run'_eq, simulateQ_bind, StateT.run_bind]
  have hR : (simulateQ (tabOuter g) ((simulateQ (simImpl D hP gaP) (hQ (St := St) D.label >>= fun _ ↦ B)).run' SimSt.init >>= fun b ↦
          readVec (Msg := Msg) (Dg := Dg) (root b) >>= fun l ↦ simulateQ embG (post b l))).run' ∅ =
      Prod.fst <$> (((simulateQ (tabImpl D g) (hQ (St := St) D.label >>= fun _ ↦ B)).run ((SimSt.init : SimSt Dg St Root n), (∅ : (GSpec Msg Dg Root Z n).QueryCache))) >>= fun p ↦ (simulateQ (tabOuter g) (readVec (Msg := Msg) (Dg := Dg)
        (root p.1) >>= fun l ↦ simulateQ embG (post p.1 l))).run p.2.2) := by
    rw [StateT.run'_eq, simulateQ_bind, StateT.run_bind, run_prefix, bind_map_left]
  have hBad : Pr{let z ← ((simulateQ (tabImpl D g) (hQ (St := St) D.label >>= fun _ ↦ B)).run ((SimSt.init : SimSt Dg St Root n), (∅ : (GSpec Msg Dg Root Z n).QueryCache))) >>= fun p ↦ (simulateQ (tabImpl D g) (chalP D (root p.1))).run p.2}[
      z.2.1.bad = true] ≤ (NB + n + 1 : ℕ) * (2 * (NB + n + 1 : ℕ) * εc) := by
    have hX : QueryCostAtMost ((hQ (St := St) D.label >>= fun _ ↦ B) >>= fun b ↦ chalP D (root b))
        (fCalls (Msg := Msg) (Dg := Dg) (St := St)) (NB + n + 1) :=
      (((isWeightBound_hQ (Dg := Dg) (St := St) D.label).bind fun _ ↦ hB).bind fun b ↦
        isWeightBound_chalP (D := D) (root b)).mono (by omega)
    have := prob_bad_le hcap g _ _ hX
    rwa [simulateQ_bind, StateT.run_bind] at this
  rw [hL, hR, prEvent_map, prEvent_map]
  refine le_trans ?_ (add_le_add le_rfl hBad)
  refine prEvent_bind_le_add _ _ _ _ _ _ _ fun p hp ↦ ?_
  obtain ⟨hgf, hpb⟩ := prefix_inv g B p hp
  rw [simulateQ_bind, StateT.run_bind, add_comm]
  refine prEvent_bind_le_of_good (P := fun x : Bool × _ ↦ x.1 = true)
    ((simulateQ (tabImpl D g) (chalP D (root p.1))).run p.2) _ (fun z ↦ z.2.1.bad = true) _
    fun q hq hqb ↦ ?_
  simp only [Bool.not_eq_true] at hqb
  rcases hpb with hb | ⟨iv, hG⟩
  · have := tab_run_bad g _ p.2 hgf hb hq
    rw [hqb] at this; cases this
  obtain ⟨hc, hlen, hval⟩ := chal_ok g iv (root p.1) p.2.1 p.2.2 hG hq hqb
  rw [toVec_of_chal g (root p.1) q.1 hlen hval, simulateQ_bind, StateT.run_bind,
    readVec_run g _ _ hgf, pure_bind]
  have h := (post_indep (D := D) g (post p.1 (g.at (root p.1))) q.2.1 q.2.2).prEvent_eq
    (fun z ↦ z.1 = true)
  rw [prEvent_map] at h
  rw [h, ← hc]


/-- **The duplex lemma.** In the two-oracle random-oracle model, a computation `B` with at most
`NB` calls of `F`, then the duplex challenges `chalP` of a root it chose, then a computation
`post` of the challenges with coins and `H`: its success probability is at most that of the
simulated world, where `B` runs against the simulator (which first queries `H` at the label) and
`post` gets the challenges `G (r, ·)` of a random oracle `G`, plus `N · (2N · εc)` for
`N = NB + n + 1` and `εc` the largest probability of a capacity. -/
theorem duplex_le [Inhabited Z] {εc : ℝ≥0∞}
    (hcap : ∀ c, Pr{let w ← ($ᵗ W : ProbComp W)}[D.capW w = c] ≤ εc)
    {β : Type} (B : OracleComp (Rom2 Msg Dg St) β) (NB : ℕ)
    (hB : QueryCostAtMost B (fCalls (Msg := Msg) (Dg := Dg) (St := St)) NB) (root : β → Root)
    (post : β → (Fin n → Z) → OracleComp (unifSpec + roSpec Msg Dg) Bool) :
    Pr{let b ← (simulateQ (hfSpec Msg Dg St).romImpl (B >>= fun b ↦
        chalP D (root b) >>= fun zs ↦ simulateQ embH (post b (toVec zs)))).run' ∅}[b = true] ≤
      Pr{let b ← (simulateQ (GSpec Msg Dg Root Z n).romImpl ((simulateQ (simImpl D hP gaP)
        (hQ (St := St) D.label >>= fun _ ↦ B)).run' SimSt.init >>= fun b ↦
          readVec (Msg := Msg) (Dg := Dg) (root b) >>= fun l ↦ simulateQ embG (post b l))).run' ∅}[
          b = true] +
        (NB + n + 1 : ℕ) * (2 * (NB + n + 1 : ℕ) * εc) := by
  have h0 := (run'_hq_bind_evalDistEq (hs := hfSpec Msg Dg St) (.inl D.label) (B >>= fun b ↦
        chalP D (root b) >>= fun zs ↦ simulateQ embH (post b (toVec zs))) ∅).prEvent_eq
    (fun b ↦ b = true)
  rw [← h0]
  have h1 := (run'_simImpl_evalDistEq (D := D) (Root := Root) (Z := Z)
    ((hQ (St := St) D.label >>= fun _ ↦ B) >>= fun b ↦
        chalP D (root b) >>= fun zs ↦ simulateQ embH (post b (toVec zs)))).prEvent_eq
    (fun b ↦ b = true)
  rw [show (hq (hs := hfSpec Msg Dg St) (.inl D.label) >>= fun _ ↦ B >>= fun b ↦
        chalP D (root b) >>= fun zs ↦ simulateQ embH (post b (toVec zs))) =
      ((hQ (St := St) D.label >>= fun _ ↦ B) >>= fun b ↦
        chalP D (root b) >>= fun zs ↦ simulateQ embH (post b (toVec zs))) by
    simp only [bind_assoc]; rfl, ← h1]
  rw [(run'_romImpl_evalDistEq_eager (fun _ : Root × Fin n ↦ True) _ ∅).prEvent_eq,
    (run'_romImpl_evalDistEq_eager (fun _ : Root × Fin n ↦ True) _ ∅).prEvent_eq]
  refine prEvent_bind_le_add_const _ _ _ _ _ _ fun g ↦ ?_
  rw [run'_simulateQ_foldWith]
  exact tab_le hcap g B NB hB root post

end Common.SeedDuplex

namespace Common.SeedDuplex

variable {Msg Dg St Root Z W Cp : Type} {n : ℕ}
  [DecidableEq Msg] [DecidableEq St] [DecidableEq Root] [DecidableEq Cp]
  [SampleableType Dg] [SampleableType St] [SampleableType Z] [SampleableType W]
  [Fintype St] [Fintype Z] [Fintype W] [Fintype Root] [Nonempty Z]
  {D : DuplexSpec Msg Dg St Root Z W Cp n}

/-- Two worlds whose events sum to one: one bound on the complements is the reverse bound. -/
theorem le_add_of_compl {x y : ProbComp Bool} {δ : ℝ≥0∞}
    (h : Pr{let b ← x}[b = false] ≤ Pr{let b ← y}[b = false] + δ) :
    Pr{let b ← y}[b = true] ≤ Pr{let b ← x}[b = true] + δ := by
  have tx := prEvent_add_prEvent_not_eq_prEvent_true x (· = true)
  have ty := prEvent_add_prEvent_not_eq_prEvent_true y (· = true)
  rw [OracleComp.prEvent_true_eq_one] at tx ty
  simp only [Bool.not_eq_true] at tx ty
  have hfin : Pr{let b ← x}[b = false] ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _)
  refine (ENNReal.add_le_add_iff_right hfin).mp ?_
  calc Pr{let b ← y}[b = true] + Pr{let b ← x}[b = false]
      ≤ Pr{let b ← y}[b = true] + (Pr{let b ← y}[b = false] + δ) := add_le_add le_rfl h
    _ = 1 + δ := by rw [← add_assoc, ty]
    _ = Pr{let b ← x}[b = true] + δ + Pr{let b ← x}[b = false] := by rw [← tx]; ring

/-- **The duplex lemma, reversed**: the simulated world's success probability is at most the
two-oracle world's plus the same `N · (2N · εc)`. It follows from `duplex_le` for the negated
`post`, the two worlds' successes and failures each summing to one. LeanDA's code binding uses it
to read Benedikt Wagner's knowledge-soundness term back in the random-permutation model
(`lean_da`, `LeanDa/KsRpm.lean`). -/
theorem duplex_ge [Inhabited Z] {εc : ℝ≥0∞}
    (hcap : ∀ c, Pr{let w ← ($ᵗ W : ProbComp W)}[D.capW w = c] ≤ εc)
    {β : Type} (B : OracleComp (Rom2 Msg Dg St) β) (NB : ℕ)
    (hB : QueryCostAtMost B (fCalls (Msg := Msg) (Dg := Dg) (St := St)) NB) (root : β → Root)
    (post : β → (Fin n → Z) → OracleComp (unifSpec + roSpec Msg Dg) Bool) :
    Pr{let b ← (simulateQ (GSpec Msg Dg Root Z n).romImpl ((simulateQ (simImpl D hP gaP)
        (hQ (St := St) D.label >>= fun _ ↦ B)).run' SimSt.init >>= fun b ↦
          readVec (Msg := Msg) (Dg := Dg) (root b) >>= fun l ↦ simulateQ embG (post b l))).run' ∅}[
          b = true] ≤
      Pr{let b ← (simulateQ (hfSpec Msg Dg St).romImpl (B >>= fun b ↦
        chalP D (root b) >>= fun zs ↦ simulateQ embH (post b (toVec zs)))).run' ∅}[b = true] +
        (NB + n + 1 : ℕ) * (2 * (NB + n + 1 : ℕ) * εc) := by
  have h := duplex_le hcap B NB hB root (fun b l ↦ (fun x ↦ !x) <$> post b l)
  simp only [simulateQ_map, ← map_bind, StateT.run'_eq, StateT.run_map, Functor.map_map] at h
  refine le_add_of_compl ?_
  simpa only [StateT.run'_eq, prEvent_map, Function.comp_def, Bool.not_eq_true'] using h

end Common.SeedDuplex
