module

public import Common.Duplex.Inv

@[expose] public section

/-!
# Without collision, the derived challenges are the table's

From a good state of the table world, running the challenge derivation `chalP` over the
simulator ends, unless a collision occurs, with the table's challenges of the root, the cache
unchanged (`chal_ok`): every state of the chain is answered, or programmed, with its challenge.
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

/-- An entry of the log answering `y` with the challenge `L`. -/
def HasEntry (s : SimSt Dg St Root n) (y : St) (L : Root × Fin n) : Prop :=
  ∃ e ∈ s.log, e.2.1 = y ∧ e.2.2 = some L

theorem run_fQ_bind {β : Type} (g : Tab Root Z n) (x : St)
    (f : St → OracleComp (Rom2 Msg Dg St) β)
    (sc : SimSt Dg St Root n × (GSpec Msg Dg Root Z n).QueryCache) :
    (simulateQ (tabImpl D g) (fQ (Dg := Dg) x >>= f)).run sc =
      (tabImpl D g (.inr (.inr x))).run sc >>= fun w ↦ (simulateQ (tabImpl D g) (f w.1)).run w.2 := by
  rw [simulateQ_bind, StateT.run_bind,
    show simulateQ (tabImpl D g) (fQ (Dg := Dg) x) = tabImpl D g (.inr (.inr x)) from
      simulateQ_spec_query _ _]
  rfl

/-- **The rest of a chain** is the table's challenges. -/
theorem chain_ok (g : Tab Root Z n) (iv : Dg) (r : Root) (k : ℕ) :
    ∀ (y : St) (j : Fin n) (_ : j.val + k + 1 = n) (s : SimSt Dg St Root n)
      (c : (GSpec Msg Dg Root Z n).QueryCache), Good D g iv (s, c) → HasEntry s y (r, j) →
      ∀ z ∈ support ((simulateQ (tabImpl D g) (chainP D k y)).run (s, c)),
        z.2.1.bad = false → z.2.2 = c ∧ ∃ _ : z.1.length = k,
          ∀ i (hi : i < z.1.length), z.1[i] = g.at r ⟨j.val + 1 + i, by omega⟩ := by
  induction k with
  | zero =>
    intro y j hj s c hG hE z hz hb
    simp only [chainP, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, rfl, fun i hi ↦ absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro y j hj s c hG hE z hz hb
    obtain ⟨e, he, hey, hel⟩ := hE
    have h1 : j.val + 1 < n := by omega
    have hok := hG.inv.nxt e he r j h1 hel
    rw [chainP, run_fQ_bind] at hz
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hz
    have hb₁ : w₁.2.1.bad = false := by
      by_contra h
      have := tab_run_bad g _ w₁.2 (good_step g iv _ _ hG hw₁ (by
        cases hh : w₁.2.1.bad
        · rfl
        · exfalso
          have := tab_run_bad g (chainP D k w₁.1) w₁.2 (gfree_step g _ _ hG.gfree hw₁) hh hw₂
          simp_all)).gfree (by simpa using h) hw₂
      simp_all
    rw [hey] at hok
    obtain ⟨hG₁, hc₁, e₁, he₁, he₁y, he₁l⟩ := fstep_label g iv _ _ s c hG hok
      (fun ha ↦ progLbl_of (hok.1 ha) (fun hu ↦ hG.inv.used_succ he hel h1 hu (hey ▸ ha))) hw₁ hb₁
    obtain ⟨hc₂, hlen, hval⟩ := ih w₁.1 ⟨j.val + 1, h1⟩ (by simp; omega) w₁.2.1 w₁.2.2 hG₁
      ⟨e₁, he₁, he₁y, he₁l⟩ w₂ hw₂ hb
    refine ⟨hc₂.trans hc₁, by simp [hlen], fun i hi ↦ ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero]
      rw [← he₁y, hG₁.inv.out e₁ he₁ r _ he₁l]
    | succ i =>
      simp only [List.getElem_cons_succ]
      rw [hval i (by simp at hi; omega)]
      congr 2
      simp only
      omega

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
  -- the first state of the chain
  have hok := hG.inv.fst r
  obtain ⟨hG₂, hc₂, e₂, he₂, he₂y, he₂l⟩ := fstep_label g iv _ _ s c hG hok
    (fun ha ↦ progLbl_of (hok.1 ha) (fun hu ↦ hG.inv.used_zero r hu ha)) hw₂ hb₂
  obtain ⟨hc₃, hlen, hval⟩ := chain_ok g iv r (n - 1) (show St from w₂.1) ⟨0, D.n_pos⟩
    (by simp; have := D.n_pos; omega) w₂.2.1 w₂.2.2 hG₂ ⟨e₂, he₂, he₂y, he₂l⟩ w₃ hw₃ hb₃
  refine ⟨hc₃.trans hc₂, by simp [hlen]; have := D.n_pos; omega, fun i hi ↦ ?_⟩
  cases i with
  | zero =>
    simp only [List.getElem_cons_zero]
    rw [← he₂y, hG₂.inv.out e₂ he₂ r _ he₂l]
  | succ i =>
    simp only [List.getElem_cons_succ]
    rw [hval i (by simp at hi; omega)]
    congr 2
    simp only
    omega

end Common.SeedDuplex
