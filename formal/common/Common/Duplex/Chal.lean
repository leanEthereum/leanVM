module

public import Common.Duplex.Inv

@[expose] public section

/-!
# Without collision, the derived challenges are the table's

From a good state of the table world, running the challenge derivation `chalP` over the
simulator ends, unless a collision occurs, with the table's challenges of the root, the cache
unchanged (`chal_ok`): the first state and every branch are answered, or programmed, with its challenge.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open Common
open Common.Duplex (GSpec hP gaP VSpec toV)

namespace Common.SeedDuplex

variable {Msg Dg St Root Z W Cp : Type} {n : ℕ}
  [DecidableEq Msg] [DecidableEq St] [DecidableEq Root] [DecidableEq Cp]
  [SampleableType Dg] [SampleableType St] [SampleableType Z] [SampleableType W]
  [Fintype St] [Fintype Z] [Fintype W] [Fintype Root] [Nonempty Z]
  {D : DuplexSpec Msg Dg St Root Z W Cp n}

theorem gfree_step (g : Tab Root Z n) (t : (Rom2 Msg Dg St).Domain)
    (sc : SimSt Dg St Root n × (GSpec Msg Dg Root Z n).QueryCache) (hc : GFree sc.2) {z}
    (hz : z ∈ support ((tabImpl D g t).run sc)) : GFree z.2.2 := by
  obtain ⟨s, c⟩ := sc
  rcases t with k | m | x
  · rw [tab_coin D g k s c hz]; exact hc
  · obtain ⟨hv, -⟩ := tab_H D g m s c hz
    rcases hcm : c (.inl m) with _ | u
    · rw [roStep_of_none hcm] at hv
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hv
      obtain ⟨u, -, hu⟩ := hv
      intro d
      rw [(Prod.mk.inj hu).2, QueryCache.cacheQuery_of_ne _ _ (by simp)]
      exact hc d
    · rw [roStep_of_some hcm] at hv
      simp only [support_pure, Set.mem_singleton_iff] at hv
      rw [(Prod.mk.inj hv).2]; exact hc
  · rcases tab_F D g x s c hc hz with ⟨-, h⟩ | ⟨-, h, -⟩ <;> rw [h] <;> exact hc

/-- Along a run of the table world, a collision stays recorded. -/
theorem tab_run_bad {α : Type} (g : Tab Root Z n) (X : OracleComp (Rom2 Msg Dg St) α)
    (sc : SimSt Dg St Root n × (GSpec Msg Dg Root Z n).QueryCache) (hc : GFree sc.2)
    (hb : sc.1.bad = true) {z} (hz : z ∈ support ((simulateQ (tabImpl D g) X).run sc)) :
    z.2.1.bad = true :=
  (inv_of_mem_support_run (tabImpl D g) (fun sc ↦ GFree sc.2 ∧ sc.1.bad = true)
    (fun t sc h _ hz ↦ ⟨gfree_step g t sc h.1 hz, tab_bad_mono g t sc.1 sc.2 h.1 h.2 hz⟩)
    X ⟨hc, hb⟩ z hz).2

/-- A step at a state described by the invariant: its answer carries the challenge `L`. -/
theorem fstep_label (g : Tab Root Z n) (iv : Dg) (x : St) (L : Root × Fin n)
    (s : SimSt Dg St Root n) (c : (GSpec Msg Dg Root Z n).QueryCache) (hG : Good D g iv (s, c))
    (hok : NextOK D s x L) (hfp : s.answer x = none → progLbl D s x = some L) {z}
    (hz : z ∈ support ((tabImpl D g (.inr (.inr x))).run (s, c))) (hb : z.2.1.bad = false) :
    Good D g iv z.2 ∧ z.2.2 = c ∧ ∃ e ∈ z.2.1.log, e.2.1 = z.1 ∧ e.2.2 = some L := by
  have hG' := good_step g iv _ _ hG hz hb
  refine ⟨hG', ?_⟩
  rcases tab_F D g x s c hG.gfree hz with ⟨ha, h⟩ | ⟨ha, h, -⟩
  · rw [h]
    obtain ⟨e, he, hk, hv⟩ := answer_eq_some ha
    exact ⟨rfl, e, he, hv, hok.2 e he hk⟩
  · rw [h]
    refine ⟨rfl, (x, z.1, progLbl D s x), List.mem_cons_self, rfl, hfp ha⟩

theorem run_fQ_bind {β : Type} (g : Tab Root Z n) (x : St)
    (f : St → OracleComp (Rom2 Msg Dg St) β)
    (sc : SimSt Dg St Root n × (GSpec Msg Dg Root Z n).QueryCache) :
    (simulateQ (tabImpl D g) (fQ (Dg := Dg) x >>= f)).run sc =
      (tabImpl D g (.inr (.inr x))).run sc >>= fun w ↦ (simulateQ (tabImpl D g) (f w.1)).run w.2 := by
  rw [simulateQ_bind, StateT.run_bind,
    show simulateQ (tabImpl D g) (fQ (Dg := Dg) x) = tabImpl D g (.inr (.inr x)) from
      simulateQ_spec_query _ _]
  rfl

/-- A call of `F` keeps the log's entries. -/
theorem log_mono_F (g : Tab Root Z n) (x : St) (s : SimSt Dg St Root n)
    (c : (GSpec Msg Dg Root Z n).QueryCache) (hc : GFree c) {z}
    (hz : z ∈ support ((tabImpl D g (.inr (.inr x))).run (s, c))) {e} (he : e ∈ s.log) :
    e ∈ z.2.1.log := by
  rcases tab_F D g x s c hc hz with ⟨-, h⟩ | ⟨-, h, -⟩
  · rw [h]; exact he
  · rw [h, log_record]; exact List.mem_cons_of_mem _ he

/-- **The branches of a root** are the table's challenges. -/
theorem branches_ok (g : Tab Root Z n) (iv : Dg) (r : Root) (e₀ : St × St × Option (Root × Fin n))
    (hl : e₀.2.2 = some (r, ⟨0, D.n_pos⟩)) :
    ∀ (js : List (Fin n)) (_ : ∀ j ∈ js, j.val ≠ 0) (s : SimSt Dg St Root n)
      (c : (GSpec Msg Dg Root Z n).QueryCache), Good D g iv (s, c) → e₀ ∈ s.log →
      ∀ z ∈ support ((simulateQ (tabImpl D g) (branchesP D e₀.2.1 js)).run (s, c)),
        z.2.1.bad = false → z.2.2 = c ∧ z.1 = js.map (g.at r) := by
  intro js
  induction js with
  | nil =>
    intro _ s c _ _ z hz _
    simp only [branchesP, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, rfl⟩
  | cons j js ih =>
    intro hjs s c hG he₀ z hz hb
    have hj := hjs j List.mem_cons_self
    rw [branchesP, run_fQ_bind] at hz
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hz
    have hb₁ : w₁.2.1.bad = false := by
      cases h : w₁.2.1.bad
      · rfl
      · exfalso
        have := tab_run_bad g _ w₁.2 (gfree_step g _ _ hG.gfree hw₁) h hw₂
        simp_all
    have hok := hG.inv.nxt e₀ he₀ r hl j hj
    obtain ⟨hG₁, hc₁, e₁, he₁, he₁y, he₁l⟩ := fstep_label g iv _ _ s c hG hok
      (fun ha ↦ progLbl_of (hok.1 ha) (fun hu ↦ hG.inv.used_branch he₀ hl hj hu ha)) hw₁ hb₁
    obtain ⟨hc₂, hz₂⟩ := ih (fun j' hj' ↦ hjs j' (List.mem_cons_of_mem _ hj')) w₁.2.1 w₁.2.2 hG₁
      (log_mono_F g _ s c hG.gfree hw₁ he₀) w₂ hw₂ hb
    refine ⟨hc₂.trans hc₁, ?_⟩
    simp only [List.map_cons, hz₂]
    rw [← he₁y, hG₁.inv.out e₁ he₁ r j he₁l]

theorem branchIdx_length : (branchIdx n).length = n - 1 := by
  simp [branchIdx]

theorem branchIdx_getElem (i : ℕ) (hi : i < (branchIdx n).length) :
    (branchIdx n)[i] = ⟨i + 1, by have := branchIdx_length (n := n); omega⟩ := by
  simp [branchIdx]

theorem branchIdx_ne_zero : ∀ j ∈ branchIdx n, j.val ≠ 0 := by
  intro j hj
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hj
  rw [branchIdx_getElem]
  exact Nat.succ_ne_zero i

theorem run_hQ_bind {β : Type} (g : Tab Root Z n) (m : Msg)
    (f : Dg → OracleComp (Rom2 Msg Dg St) β)
    (sc : SimSt Dg St Root n × (GSpec Msg Dg Root Z n).QueryCache) :
    (simulateQ (tabImpl D g) (hQ (St := St) m >>= f)).run sc =
      (tabImpl D g (.inr (.inl m))).run sc >>= fun w ↦ (simulateQ (tabImpl D g) (f w.1)).run w.2 := by
  rw [simulateQ_bind, StateT.run_bind,
    show simulateQ (tabImpl D g) (hQ (St := St) m) = tabImpl D g (.inr (.inl m)) from
      simulateQ_spec_query _ _]
  rfl

/-- **Without collision, the derived challenges of a root are the table's**, and the cache is
unchanged. -/
theorem chal_ok (g : Tab Root Z n) (iv : Dg) (r : Root) (s : SimSt Dg St Root n)
    (c : (GSpec Msg Dg Root Z n).QueryCache) (hG : Good D g iv (s, c))
    {z} (hz : z ∈ support ((simulateQ (tabImpl D g) (chalP D r)).run (s, c)))
    (hb : z.2.1.bad = false) :
    z.2.2 = c ∧ ∃ _ : z.1.length = n, ∀ i (hi : i < z.1.length), z.1[i] = g.at r ⟨i, by omega⟩ := by
  unfold chalP at hz
  rw [run_hQ_bind] at hz
  simp only [mem_support_bind_iff] at hz
  obtain ⟨w₀, hw₀, hz⟩ := hz
  obtain ⟨hv₀, hs₀⟩ := tab_H D g D.label s c hw₀
  rw [roStep_of_some hG.label] at hv₀
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hv₀
  obtain ⟨hiv, hc₀⟩ := hv₀
  rw [ite_pos' rfl, hiv, record_x0_self s hG.inv.x0 hG.inv.ivEq] at hs₀
  have hw₀2 : w₀.2 = (s, c) := Prod.ext hs₀ hc₀
  rw [hiv, hw₀2, run_fQ_bind] at hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨w₂, hw₂, w₃, hw₃, rfl⟩ := hz
  -- no collision along the way
  have hb₃ : w₃.2.1.bad = false := hb
  have hb₂ : w₂.2.1.bad = false := by
    cases h : w₂.2.1.bad
    · rfl
    · exfalso
      have := tab_run_bad g _ w₂.2 (gfree_step g _ _ hG.gfree hw₂) h hw₃
      simp_all
  -- the first state
  have hok := hG.inv.fst r
  obtain ⟨hG₂, hc₂, e₂, he₂, he₂y, he₂l⟩ := fstep_label g iv _ _ s c hG hok
    (fun ha ↦ progLbl_of (hok.1 ha) (fun hu ↦ hG.inv.used_zero r hu ha)) hw₂ hb₂
  rw [← he₂y] at hw₃
  obtain ⟨hc₃, hz₃⟩ := branches_ok g iv r e₂ he₂l (branchIdx n) branchIdx_ne_zero w₂.2.1 w₂.2.2
    hG₂ he₂ w₃ hw₃ hb₃
  refine ⟨hc₃.trans hc₂, by simp [hz₃, branchIdx_length]; have := D.n_pos; omega, fun i hi ↦ ?_⟩
  cases i with
  | zero =>
    simp only [List.getElem_cons_zero]
    rw [← he₂y, hG₂.inv.out e₂ he₂ r _ he₂l]
  | succ i =>
    simp only [List.getElem_cons_succ]
    have hi' : i < (branchIdx n).length := by simp [hz₃] at hi; simpa using hi
    simp only [hz₃, List.getElem_map, branchIdx_getElem]

end Common.SeedDuplex
