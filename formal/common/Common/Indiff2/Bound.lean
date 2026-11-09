module

public import Common.Indiff2.Bad
public import Common.Indiff.Bound

@[expose] public section

/-!
# The two-oracle model: the disagreement bound

Under the duplex discipline the violation flag stays down (`viol_false`); each fresh draw has a
uniform capacity, which collides with the at most `q` earlier capacities with probability at most
`q / |C|` (`prEvent_b0_le`). So the worlds disagree with probability at most `q² / |C|`
(`prEvent_disagree_le`).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Common

section Setting

variable {Dg E C Msg : Type}
  [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C)

/-! ## The violation flag -/

theorem bookUpd_hist_viol (NF : (Dg × E) → Prop) [DecidablePred NF]
    (t : (dSpec2 Msg Dg (SpState Dg E C)).Domain) (ht : ∀ x, t ≠ .inr (.inr (.inr x)))
    (s : FState Msg Dg E C) (a) (b : Book (SpState Dg E C)) :
    (bookUpd P iv NF t s a b).hist = b.hist ∧ (bookUpd P iv NF t s a b).viol = b.viol := by
  rcases t with n | m | (x | y) | x
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · simp only [bookUpd]; split_ifs <;> exact ⟨rfl, rfl⟩
  · simp only [bookUpd]; split_ifs <;> exact ⟨rfl, rfl⟩
  · exact absurd rfl (ht x)

/-- **Under the duplex discipline the violation flag stays down.** -/
theorem viol_false (NF : (Dg × E) → Prop) [DecidablePred NF] {α : Type}
    (D : OracleComp (dSpec2 Msg Dg (SpState Dg E C)) α) (hist : List (SpState Dg E C))
    (hD : DuplexOK iv NF D hist) (s : FState Msg Dg E C) (b : Book (SpState Dg E C))
    (hb : b.hist = hist) (hv : b.viol = false) :
    ∀ z ∈ support ((simulateQ (aug2 P iv NF) D).run (s, b)), z.2.2.viol = false := by
  induction D using OracleComp.inductionOn generalizing hist s b with
  | pure a =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hv
  | query_bind t k ih =>
    intro z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨us, hus, hz⟩ := hz
    rw [aug2, augImpl_run, support_map] at hus
    obtain ⟨w, -, rfl⟩ := hus
    by_cases ht : ∃ x, t = .inr (.inr (.inr x))
    · obtain ⟨x, rfl⟩ := ht
      obtain ⟨hadm, hk⟩ := (duplexOK_query_bind_F iv NF x k hist).mp hD
      refine ih w.1 (w.1 :: hist) (hk w.1) _ _ (by simp [bookUpd, hb]) ?_ z hz
      simp [bookUpd, hv, hb, hadm]
    · push Not at ht
      obtain ⟨h1, h2⟩ := bookUpd_hist_viol P iv NF t ht s w.1 b
      exact ih w.1 hist ((duplexOK_query_bind_other iv NF t ht k hist).mp hD w.1) _ _
        (h1.trans hb) (h2.trans hv) z hz

/-! ## Capacity collisions -/

/-- The number of fresh draws. -/
def bookSize (b : Book (SpState Dg E C)) : ℕ := b.dF.length + b.dI.length

theorem bookSize_bookUpd (NF : (Dg × E) → Prop) [DecidablePred NF]
    (t : (dSpec2 Msg Dg (SpState Dg E C)).Domain) (s : FState Msg Dg E C) (a)
    (b : Book (SpState Dg E C)) :
    bookSize (bookUpd P iv NF t s a b) ≤ bookSize b + queryCost2 (Dg := Dg) P t := by
  rcases t with n | m | (x | y) | x
  · simp [bookUpd]
  · simp [bookUpd]
  · simp only [bookUpd, queryCost2]
    split_ifs
    all_goals (simp only [bookSize, List.length_cons]; omega)
  · simp only [bookUpd, queryCost2]
    split_ifs
    all_goals (simp only [bookSize, List.length_cons]; omega)
  · simp only [bookUpd, queryCost2, bookSize]
    split_ifs
    all_goals (try simp only [List.length_cons])
    all_goals omega

theorem length_capsOf (b : Book (SpState Dg E C)) : (capsOf iv b).length = bookSize b + 1 := by
  simp [capsOf, bookSize]

theorem prEvent_cap_ec_le (L : List C) :
    Pr{let ec ← $ᵗ (E × C)}[ec.2 ∈ L] ≤ L.length / (Fintype.card C : ℝ≥0∞) :=
  SampleableType.prEvent_uniformSample_prod_le_of_forall_fst (fun ec : E × C ↦ ec.2 ∈ L)
    fun _ ↦ prEvent_uniform_mem_le L

/-- A direct call's event that needs a fresh `F` answer with a capacity in `L`. -/
theorem prEvent_fStep_le (x : SpState Dg E C) (s : FState Msg Dg E C) (L : List C)
    (g : SpState Dg E C × FState Msg Dg E C → Prop)
    (hg : ∀ z, g z → s.2 (.inr x) = none ∧ z.1.2 ∈ L) :
    Pr{let z ← fStep x s}[g z] ≤ L.length / (Fintype.card C : ℝ≥0∞) := by
  rcases hc : s.2 (.inr x) with _ | v
  · simp only [fStep, roStep_of_none hc, bind_pure_comp, prEvent_map]
    exact (prEvent_mono _ _ (fun u : SpState Dg E C ↦ u.2 ∈ L) fun u hu ↦ (hg _ hu).2).trans
      (prEvent_cap_mem_le L)
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z _ h ↦ absurd (hg z h).1 (by simp [hc])]
    exact zero_le

theorem b0_bookUpd_same {b b' : Book (SpState Dg E C)} (hF : b'.dF = b.dF) (hI : b'.dI = b.dI)
    (hb : ¬ B0 iv b) : ¬ B0 iv b' := by
  simp only [B0, capsOf, hF, hI] at hb ⊢
  exact hb

/-- **A step creates a capacity collision with probability at most its cost times `N / |C|`.** -/
theorem prEvent_b0_step (NF : (Dg × E) → Prop) [DecidablePred NF] (N : ℕ)
    (t : (dSpec2 Msg Dg (SpState Dg E C)).Domain) (s : FState Msg Dg E C × Book (SpState Dg E C))
    (hb : ¬ B0 iv s.2) (hN : bookSize s.2 + queryCost2 (Dg := Dg) P t ≤ N) :
    Pr{let z ← ((aug2 P iv NF) t).run s}[B0 iv z.2.2] ≤
      queryCost2 (Dg := Dg) P t * (N / (Fintype.card C : ℝ≥0∞)) := by
  obtain ⟨⟨σ, c⟩, b⟩ := s
  rw [aug2, augImpl_run, prEvent_map]
  have hL : bookSize b + 1 ≤ N →
      ((capsOf iv b).length : ℝ≥0∞) / (Fintype.card C) ≤ N / (Fintype.card C : ℝ≥0∞) :=
    fun h ↦ by
      gcongr
      rw [length_capsOf]
      exact_mod_cast h
  rcases t with n | m | (x | y) | x
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z _ h ↦ hb (by simpa [bookUpd] using h)]
    exact zero_le
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z _ h ↦ hb (by simpa [bookUpd] using h)]
    exact zero_le
  · simp only [queryCost2, Nat.cast_one, one_mul] at hN ⊢
    replace hL := hL hN
    rw [shadow_perm_run]
    simp only [fwdStep2]
    split
    · next y hy =>
      rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h ↦ ?_]
      · exact zero_le
      · simp only [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact hb (by simpa [bookUpd, hy] using h)
    · next hy =>
      split
      · next r β hch =>
        split
        · next m' hm =>
          have hrf : rootedFinal P σ x = true := by simp [rootedFinal, hch, hm]
          refine (prEvent_bind_le_of_forall_le _ _ _ fun w ↦ ?_).trans hL
          rw [bind_pure_comp, prEvent_map]
          refine (prEvent_mono _ _ _ fun ec h ↦ ?_).trans (prEvent_cap_ec_le _)
          simp only [bookUpd, hy, hrf, true_or, and_self, ite_true] at h
          exact cap_mem_of_b0_dF _ hb h
        · next hm =>
          have hrf : rootedFinal P σ x = false := by simp [rootedFinal, hch, hm]
          refine (prEvent_fStep_le x (σ, c) _ _ fun z h ↦ ?_).trans hL
          simp only [bookUpd, hy, hrf, Bool.false_eq_true, false_or, true_and] at h
          split_ifs at h with hc
          · exact ⟨hc, cap_mem_of_b0_dF _ hb h⟩
          · exact absurd h hb
      · next hch =>
        have hrf : rootedFinal P σ x = false := by simp [rootedFinal, hch]
        refine (prEvent_fStep_le x (σ, c) _ _ fun z h ↦ ?_).trans hL
        simp only [bookUpd, hy, hrf, Bool.false_eq_true, false_or, true_and] at h
        split_ifs at h with hc
        · exact ⟨hc, cap_mem_of_b0_dF _ hb h⟩
        · exact absurd h hb
  · simp only [queryCost2, Nat.cast_one, one_mul] at hN ⊢
    replace hL := hL hN
    rw [shadow_perm_run]
    simp only [invStep2]
    split
    · next x' hx =>
      rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h ↦ ?_]
      · exact zero_le
      · simp only [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact hb (by simpa [bookUpd, hx] using h)
    · next hx =>
      rw [prEvent_map]
      refine (prEvent_mono _ _ _ fun a h ↦ ?_).trans ((prEvent_cap_mem_le _).trans hL)
      simp only [bookUpd, hx, ite_true] at h
      exact cap_mem_of_b0_dI _ hb h
  · simp only [queryCost2, Nat.cast_one, one_mul] at hN ⊢
    replace hL := hL hN
    rw [shadow_F_run]
    refine (prEvent_fStep_le x (σ, c) _ _ fun z h ↦ ?_).trans hL
    simp only [bookUpd] at h
    split_ifs at h with hc
    · exact ⟨hc, cap_mem_of_b0_dF (b := b) _ hb
        (by simpa [B0, capsOf] using h)⟩
    · exact (hb (by simpa [B0, capsOf] using h)).elim

/-- **Capacity collisions are unlikely**: for a game of cost at most `q`, at most `q² / |C|`. -/
theorem prEvent_b0_le (NF : (Dg × E) → Prop) [DecidablePred NF] {α : Type}
    (D : OracleComp (dSpec2 Msg Dg (SpState Dg E C)) α) (q : ℕ)
    (hD : QueryCostAtMost D (queryCost2 (Dg := Dg) P) q) :
    Pr{let z ← ((simulateQ (aug2 P iv NF) D).run
      ((SimState.init iv, ∅), Book.init))}[B0 iv z.2.2] ≤ q * (q / (Fintype.card C : ℝ≥0∞)) := by
  have h := prEvent_run_bad_le (aug2 P iv NF) (fun s ↦ B0 iv s.2) (fun _ ↦ True)
    (queryCost2 (Dg := Dg) P) (fun s ↦ bookSize s.2) q (q / (Fintype.card C : ℝ≥0∞))
    (fun _ _ _ _ _ ↦ trivial)
    (fun t s _ z hz ↦ by
      rw [aug2, augImpl_run, support_map] at hz
      obtain ⟨w, -, rfl⟩ := hz
      exact bookSize_bookUpd P iv NF t _ _ _)
    (fun t s _ hb hN ↦ prEvent_b0_step P iv NF q t s hb hN) D q hD
    ((SimState.init iv, ∅), Book.init) trivial (by simp [bookSize, Book.init])
  have h0 : ¬ B0 iv (Book.init : Book (SpState Dg E C)) := by simp [B0, capsOf, Book.init]
  simpa [h0] using h

/-! ## The disagreement bound -/

theorem sInv_init (NF : (Dg × E) → Prop) :
    SInv iv NF (((SimState.init iv : SimState Dg E C), (∅ : HCache Msg Dg (SpState Dg E C))),
      Book.init) := by
  refine ⟨⟨fun x hx ↦ absurd rfl hx, fun x y h ↦ by simp at h, fun p hp ↦ ?_,
    fun p hp ↦ by simp [SimState.init] at hp⟩, fun y hy ↦ by simp [Book.init] at hy,
    fun h ↦ by simp [Book.init] at h⟩
  simp only [SimState.init, List.mem_singleton] at hp
  subst hp
  exact Or.inl rfl

/-- **The worlds disagree with probability at most `q² / |C|`** in a game of cost at most `q`
whose direct calls follow the duplex discipline. -/
theorem prEvent_disagree_le (NF : (Dg × E) → Prop) [DecidablePred NF]
    (hNF : ∀ m β B, P.pad m = β ++ [B] → ¬ NF B) {α : Type}
    (D : OracleComp (dSpec2 Msg Dg (SpState Dg E C)) α) (hD : DuplexOK iv NF D [])
    (q : ℕ) (hq : QueryCostAtMost D (queryCost2 (Dg := Dg) P) q) :
    Pr{let z ← ((simulateQ (aug2 P iv NF) D).run
      ((SimState.init iv, ∅), Book.init))}[z.2.2.flag = true] ≤
      q * (q / (Fintype.card C : ℝ≥0∞)) := by
  refine (prEvent_mono_of_support _ _ _ fun z hz hf ↦ ?_).trans (prEvent_b0_le P iv NF D q hq)
  have hI := inv_of_mem_support_run (aug2 P iv NF) (SInv iv NF)
    (fun t s hs z hz ↦ sInv_step P hNF t s hs hz) D (sInv_init iv NF) z hz
  rcases hI.flag hf with h | h
  · exact h
  · rw [viol_false P iv NF D [] hD _ _ rfl rfl z hz] at h
    exact absurd h Bool.false_ne_true

end Setting

end Common
