module

public import Common.Indiff2.Shadow

@[expose] public section

/-!
# The two-oracle model: disagreement needs a capacity collision

In the shadow world, the worlds disagree only at a direct call breaking the duplex discipline
(the violation flag) or after a **capacity collision** among the initial state and the fresh
draws (`B0`): an admissible direct call absorbs a non-final block into the initial state or into
an earlier answer of `F`, while a disagreement needs its input to be an inverse answer or to end
a sponge path from another rooted state of the same capacity (`flag_imp`). Under the duplex
discipline the violation flag stays down (`viol_false`), and each fresh draw collides with
probability at most `q / |C|` (`prEvent_b0_le`).
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

/-! ## The runs of the shadow world -/

theorem shadow_inl_run (n : ℕ) (s : FState Msg Dg E C) :
    ((foldRO (shadowImpl P)) (.inl n)).run s =
      (fun u ↦ (u, s)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  rw [shadow_eq_ideal1F P _ (by simp), foldRO_run, ideal1F_inl_run]
  simp [Functor.map_map]

theorem shadow_hash_run (m : Msg) (s : FState Msg Dg E C) :
    ((foldRO (shadowImpl P)) (.inr (.inl m))).run s =
      (fun w ↦ (w.1, (s.1, w.2))) <$>
        roStep (hs := hfSpec Msg Dg (SpState Dg E C)) (.inl m) s.2 := by
  rw [shadow_eq_ideal1F P _ (by simp), foldRO_run, ideal1F_hash_run]
  simp [Functor.map_map]

theorem shadow_perm_run (q : PermutationQuery (SpState Dg E C)) (s : FState Msg Dg E C) :
    ((foldRO (shadowImpl P)) (.inr (.inr (.inl q)))).run s =
      match q with
      | .forward x => fwdStep2 P x s
      | .inverse y => invStep2 y s := by
  rw [shadow_eq_ideal1F P _ (by simp)]
  exact ideal1F_fwd_run P q s

/-! ## Capacity collisions -/

/-- The capacities of the initial state and of the fresh draws. -/
def capsOf (b : Book (SpState Dg E C)) : List C := ((iv :: b.dF) ++ b.dI).map Prod.snd

/-- **A capacity collision** among the initial state and the fresh draws. -/
def B0 (b : Book (SpState Dg E C)) : Prop := ¬ (capsOf iv b).Nodup

instance (b : Book (SpState Dg E C)) : Decidable (B0 iv b) := by
  unfold B0; infer_instance

variable {iv}

theorem b0_mono {b b' : Book (SpState Dg E C)} (hF : b.dF.Sublist b'.dF)
    (hI : b.dI.Sublist b'.dI) (h : B0 iv b) : B0 iv b' := fun h' ↦
  h (h'.sublist (((hF.cons_cons iv).append hI).map Prod.snd))

theorem b0_of_cross {b : Book (SpState Dg E C)} {u v : SpState Dg E C}
    (hu : u = iv ∨ u ∈ b.dF) (hv : v ∈ b.dI) (h : u.2 = v.2) : B0 iv b := by
  intro hn
  simp only [capsOf, List.map_append] at hn
  have hdis := (List.nodup_append.mp hn).2.2
  have hu' : u.2 ∈ (iv :: b.dF).map Prod.snd := List.mem_map.mpr ⟨u, by
    rcases hu with rfl | hu
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ hu, rfl⟩
  exact hdis _ hu' _ (List.mem_map.mpr ⟨v, hv, rfl⟩) h

theorem b0_of_ne {b : Book (SpState Dg E C)} {u v : SpState Dg E C}
    (hu : u = iv ∨ u ∈ b.dF) (hv : v = iv ∨ v ∈ b.dF) (hne : u ≠ v) (h : u.2 = v.2) :
    B0 iv b := by
  intro hn
  simp only [capsOf, List.map_append] at hn
  have hn' := (List.nodup_append.mp hn).1
  have hmem : ∀ {w}, (w = iv ∨ w ∈ b.dF) → w ∈ iv :: b.dF := fun hw ↦ by
    rcases hw with rfl | hw
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ hw
  exact hne (List.inj_on_of_nodup_map hn' (hmem hu) (hmem hv) h)

theorem cap_mem_of_b0_dF {b : Book (SpState Dg E C)} (a : SpState Dg E C) (hb : ¬ B0 iv b)
    (h : B0 iv { b with dF := a :: b.dF }) : a.2 ∈ capsOf iv b := by
  by_contra ha
  apply h
  have hp : capsOf iv { b with dF := a :: b.dF } = iv.2 :: a.2 :: (b.dF ++ b.dI).map Prod.snd := by
    simp [capsOf]
  rw [hp]
  have hp2 : (iv.2 :: a.2 :: (b.dF ++ b.dI).map Prod.snd).Perm (a.2 :: capsOf iv b) := by
    simp only [capsOf, List.cons_append, List.map_cons]
    exact List.Perm.swap _ _ _
  exact hp2.nodup_iff.mpr (List.nodup_cons.mpr ⟨ha, not_not.mp hb⟩)

theorem cap_mem_of_b0_dI {b : Book (SpState Dg E C)} (a : SpState Dg E C) (hb : ¬ B0 iv b)
    (h : B0 iv { b with dI := a :: b.dI }) : a.2 ∈ capsOf iv b := by
  by_contra ha
  apply h
  have hp : (capsOf iv { b with dI := a :: b.dI }).Perm (a.2 :: capsOf iv b) := by
    simp only [capsOf, List.map_append, List.map_cons]
    exact List.perm_middle
  exact hp.nodup_iff.mpr (List.nodup_cons.mpr ⟨ha, not_not.mp hb⟩)

/-! ## The bookkeeping invariant -/

variable (iv) in
/-- The structure of the shadow world's state relative to the fresh draws `dF` (forward and `F`
answers) and `dI` (inverse answers). -/
structure SStruct (NF : (Dg × E) → Prop) (s : FState Msg Dg E C)
    (dF dI : List (SpState Dg E C)) : Prop where
  /-- `F` has been queried at recorded inputs only. -/
  fdom : FDom s.1 s.2
  /-- `F`'s answers are fresh draws. -/
  cv : ∀ x y, s.2 (.inr x) = some y → y ∈ dF
  /-- Rooted states are the initial state or fresh draws. -/
  chains : ∀ p ∈ s.1.chains, p.1 = iv ∨ p.1 ∈ dF
  /-- An edge is `F`'s, starts at an inverse answer, or ends a sponge path from a rooted state
  of the same capacity. -/
  edges : ∀ p ∈ s.1.edges, s.2 (.inr p.1) = some p.2 ∨ p.1 ∈ dI ∨
    ∃ r, (r = iv ∨ r ∈ dF) ∧ r.2 = p.1.2 ∧ ¬ NF (blockTo r p.1)

variable (iv) in
/-- **The bookkeeping invariant of the shadow world.** -/
structure SInv (NF : (Dg × E) → Prop) (s : FState Msg Dg E C × Book (SpState Dg E C)) :
    Prop where
  st : SStruct iv NF s.1 s.2.dF s.2.dI
  hist : ∀ y ∈ s.2.hist, y ∈ s.2.dF
  flag : s.2.flag = true → B0 iv s.2 ∨ s.2.viol = true

theorem SStruct.mono_lists {NF : (Dg × E) → Prop} {s : FState Msg Dg E C}
    {dF dI dF' dI' : List (SpState Dg E C)} (h : SStruct iv NF s dF dI) (hF : dF ⊆ dF')
    (hI : dI ⊆ dI') : SStruct iv NF s dF' dI' := by
  refine ⟨h.fdom, fun x y hxy ↦ hF (h.cv x y hxy), fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · rcases h.chains p hp with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (hF h1)
  · rcases h.edges p hp with h1 | h1 | ⟨r, hr, h2, h3⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl (hI h1))
    · refine Or.inr (Or.inr ⟨r, ?_, h2, h3⟩)
      rcases hr with hr | hr
      · exact Or.inl hr
      · exact Or.inr (hF hr)

theorem replayStep_fwd_cases (σ : SimState Dg E C) (x y : SpState Dg E C) :
    replayStep σ (.forward x, y) = σ ∨ (forwardLookup σ.edges x = none ∧
      (replayStep σ (.forward x, y)).edges = (x, y) :: σ.edges ∧
      ∀ p ∈ (replayStep σ (.forward x, y)).chains, p ∈ σ.chains ∨ p.1 = y) := by
  simp only [replayStep]
  split
  · exact Or.inl rfl
  · next hy =>
    right
    refine ⟨hy, ?_, ?_⟩
    · split <;> rfl
    · split
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact Or.inr rfl
        · exact Or.inl hp
      · exact fun p hp ↦ Or.inl hp

/-- A direct call to `F` keeps the structure, with its answer among the draws. -/
theorem SStruct.fStep {NF : (Dg × E) → Prop} {σ : SimState Dg E C}
    {c : HCache Msg Dg (SpState Dg E C)} {dF dI dF' dI' : List (SpState Dg E C)}
    (h : SStruct iv NF (σ, c) dF dI) (x : SpState Dg E C)
    {w} (hw : w ∈ support (roStep (hs := hfSpec Msg Dg (SpState Dg E C)) (.inr x) c))
    (hnew : c (.inr x) = none → w.1 ∈ dF') (hF : dF ⊆ dF') (hI : dI ⊆ dI') :
    w.1 ∈ dF' ∧ SStruct iv NF (replayStep σ (.forward x, w.1), w.2) dF' dI' := by
  obtain ⟨hle, hwx, hother⟩ := roStep_support _ _ hw
  have hw1 : w.1 ∈ dF' := by
    rcases hc : c (.inr x) with _ | v
    · exact hnew hc
    · have := hle hc
      rw [hwx] at this
      cases this
      exact hF (h.cv x _ hc)
  have h' := h.mono_lists hF hI
  refine ⟨hw1, fDom_replayStep h.fdom _ fun x' hx' ↦ ?_, fun x' y hxy ↦ ?_, ?_, ?_⟩
  · by_cases hx : x' = x
    · exact Or.inr (by rw [hx])
    · exact Or.inl (by rwa [← hother (.inr x') (by simpa using hx)])
  · by_cases hx : x' = x
    · subst hx
      rw [hwx] at hxy
      cases hxy
      exact hw1
    · rw [hother (.inr x') (by simpa using hx)] at hxy
      exact h'.cv x' y hxy
  · intro p hp
    rcases replayStep_fwd_cases σ x w.1 with hr | ⟨-, -, hch⟩
    · rw [hr] at hp; exact h'.chains p hp
    · rcases hch p hp with hp | hp
      · exact h'.chains p hp
      · exact Or.inr (hp ▸ hw1)
  · intro p hp
    rcases replayStep_fwd_cases σ x w.1 with hr | ⟨-, hed, -⟩
    · rw [hr] at hp
      rcases h'.edges p hp with h1 | h1
      · exact Or.inl (hle h1)
      · exact Or.inr h1
    · rw [hed] at hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Or.inl hwx
      · rcases h'.edges p hp with h1 | h1
        · exact Or.inl (hle h1)
        · exact Or.inr h1

/-- The last block of a padded message is final. -/
theorem not_nf_of_unpad {NF : (Dg × E) → Prop}
    (hNF : ∀ m β B, P.pad m = β ++ [B] → ¬ NF B) {β : List (Dg × E)} {B : Dg × E}
    (h : (P.unpad (β ++ [B])).isSome = true) : ¬ NF B := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h
  exact hNF m β B ((P.unpad_eq_some_iff _ _).mp hm)

/-- A forward step of the simulator ending a sponge path keeps the structure. -/
theorem SStruct.rootedFinal {NF : (Dg × E) → Prop}
    (hNF : ∀ m β B, P.pad m = β ++ [B] → ¬ NF B) {σ : SimState Dg E C}
    {c c' : HCache Msg Dg (SpState Dg E C)} {dF dI : List (SpState Dg E C)}
    (h : SStruct iv NF (σ, c) dF dI) {x r : SpState Dg E C} {β : List (Dg × E)}
    (hy : forwardLookup σ.edges x = none) (hch : chainOf σ.chains x = some (r, β))
    (hm : (P.unpad (β ++ [blockTo r x])).isSome = true)
    (hinr : ∀ x', c' (.inr x') = c (.inr x')) (a : SpState Dg E C) :
    SStruct iv NF (replayStep σ (.forward x, a), c') (a :: dF) dI := by
  have h' := h.mono_lists (List.subset_cons_self a dF) (fun _ h ↦ h)
  obtain ⟨hrβ, hrx⟩ := chainOf_some hch
  have hrep : replayStep σ (.forward x, a) =
      ⟨(x, a) :: σ.edges, (a, β ++ [blockTo r x]) :: σ.chains⟩ := by
    simp [replayStep, hy, hch]
  rw [hrep]
  refine ⟨fun x' hx' ↦ ?_, fun x' y hxy ↦ h'.cv x' y (by rwa [← hinr x']), fun p hp ↦ ?_,
    fun p hp ↦ ?_⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp (h.fdom x' (by rwa [← hinr x']))
    exact List.mem_map.mpr ⟨e, List.mem_cons_of_mem _ he, rfl⟩
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact Or.inr List.mem_cons_self
    · exact h'.chains p hp
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact Or.inr (Or.inr ⟨r, h'.chains _ hrβ, hrx, not_nf_of_unpad P hNF hm⟩)
    · rcases h'.edges p hp with h1 | h1
      · exact Or.inl (by rw [hinr]; exact h1)
      · exact Or.inr h1

/-- **A disagreement at an admissible direct call needs a capacity collision.** -/
theorem b0_of_disagree {NF : (Dg × E) → Prop}
    (hNF : ∀ m β B, P.pad m = β ++ [B] → ¬ NF B) {s : FState Msg Dg E C}
    {b : Book (SpState Dg E C)} (h : SStruct iv NF s b.dF b.dI) (hH : ∀ y ∈ b.hist, y ∈ b.dF)
    {x : SpState Dg E C} (hadm : Admissible iv NF b.hist x) (hd : disagree P s x = true) :
    B0 iv b := by
  obtain ⟨base, hbase, hcap, hnf⟩ : ∃ base, (base = iv ∨ base ∈ b.dF) ∧ base.2 = x.2 ∧
      NF (blockTo base x) := by
    rcases hadm with ⟨h1, h2⟩ | ⟨y, hy, h1, h2⟩
    · exact ⟨iv, Or.inl rfl, h1.symm, h2⟩
    · exact ⟨y, Or.inr (hH y hy), h1.symm, h2⟩
  have key : ∀ r, (r = iv ∨ r ∈ b.dF) → r.2 = x.2 → ¬ NF (blockTo r x) → B0 iv b :=
    fun r hr hrx hrnf ↦ b0_of_ne hr hbase (fun hrb ↦ hrnf (hrb ▸ hnf)) (hrx.trans hcap.symm)
  obtain ⟨σ, c⟩ := s
  simp only [disagree] at hd
  rcases hy : forwardLookup σ.edges x with _ | y
  · simp only [hy, Bool.or_eq_true, rootedFinal] at hd
    rcases hd with hd | hd
    · rcases hch : chainOf σ.chains x with _ | ⟨r, β⟩
      · simp [hch] at hd
      · simp only [hch] at hd
        obtain ⟨hrβ, hrx⟩ := chainOf_some hch
        exact key r (h.chains _ hrβ) hrx (not_nf_of_unpad P hNF hd)
    · exact absurd (h.fdom x (by simpa [Option.isSome_iff_ne_none] using hd))
        (fwdLookup_eq_none_iff.mp hy)
  · simp only [hy, decide_eq_true_eq] at hd
    rcases h.edges _ (mem_of_fwdLookup_eq_some hy) with h1 | h1 | ⟨r, hr, hrx, hrnf⟩
    · exact absurd h1 hd
    · exact b0_of_cross hbase h1 hcap
    · exact key r hr hrx hrnf

/-- **Every step of the shadow world keeps the bookkeeping invariant.** -/
theorem sInv_step {NF : (Dg × E) → Prop} [DecidablePred NF]
    (hNF : ∀ m β B, P.pad m = β ++ [B] → ¬ NF B)
    (t : (dSpec2 Msg Dg (SpState Dg E C)).Domain) (s : FState Msg Dg E C × Book (SpState Dg E C))
    (hs : SInv iv NF s) {z} (hz : z ∈ support (((aug2 P iv NF) t).run s)) :
    SInv iv NF z.2 := by
  obtain ⟨⟨σ, c⟩, b⟩ := s
  rw [aug2, augImpl_run, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rcases t with n | m | (x | y) | x
  · rw [shadow_inl_run] at hw
    simp only [support_map, Set.mem_image] at hw
    obtain ⟨u, -, rfl⟩ := hw
    exact hs
  · rw [shadow_hash_run] at hw
    simp only [support_map, Set.mem_image] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    obtain ⟨hle, -, hother⟩ := roStep_support _ _ hw'
    have hinr : ∀ x', w'.2 (.inr x') = c (.inr x') := fun x' ↦ hother _ (by simp)
    refine ⟨⟨fun x' hx' ↦ hs.st.fdom x' (by rwa [← hinr x']),
      fun x' y hxy ↦ hs.st.cv x' y (by rwa [← hinr x']), hs.st.chains, fun p hp ↦ ?_⟩,
      hs.hist, hs.flag⟩
    rcases hs.st.edges p hp with h1 | h1
    · exact Or.inl (by rw [hinr]; exact h1)
    · exact Or.inr h1
  · rw [shadow_perm_run] at hw
    simp only [fwdStep2] at hw
    split at hw
    · next y' hy =>
      simp only [support_pure, Set.mem_singleton_iff] at hw
      subst hw
      simpa [bookUpd, hy] using hs
    · next hy =>
      split at hw
      · next r β hch =>
        split at hw
        · next m' hm =>
          simp only [mem_support_bind_iff, support_uniformSample, Set.mem_univ, true_and,
            support_pure, Set.mem_singleton_iff] at hw
          obtain ⟨w', hw', ec, rfl⟩ := hw
          obtain ⟨hle, -, hother⟩ := roStep_support _ _ hw'
          have hrf : rootedFinal P σ x = true := by simp [rootedFinal, hch, hm]
          have hmS : (P.unpad (β ++ [blockTo r x])).isSome = true := by simp [hm]
          simp only [bookUpd, hy, hrf, true_or, and_self, ite_true]
          refine ⟨hs.st.rootedFinal P hNF hy hch hmS (fun x' ↦ hother _ (by simp)) _,
            fun y hy' ↦ List.mem_cons_of_mem _ (hs.hist y hy'), fun hf ↦ ?_⟩
          rcases hs.flag hf with h1 | h1
          · exact Or.inl (b0_mono (List.sublist_cons_self _ _) (List.Sublist.refl _) h1)
          · exact Or.inr h1
        · next hm =>
          simp only [fStep, support_map, Set.mem_image] at hw
          obtain ⟨w', hw', rfl⟩ := hw
          have hc : c (.inr x) = none := by
            by_contra hc
            exact fwdLookup_eq_none_iff.mp hy (hs.st.fdom x hc)
          have hrf : rootedFinal P σ x = false := by simp [rootedFinal, hch, hm]
          simp only [bookUpd, hy, hc, or_true, and_self, ite_true]
          obtain ⟨-, hst⟩ := hs.st.fStep x hw' (fun _ ↦ List.mem_cons_self)
            (List.subset_cons_self _ _) (fun _ h ↦ h)
          refine ⟨hst, fun y hy' ↦ List.mem_cons_of_mem _ (hs.hist y hy'), fun hf ↦ ?_⟩
          rcases hs.flag hf with h1 | h1
          · exact Or.inl (b0_mono (List.sublist_cons_self _ _) (List.Sublist.refl _) h1)
          · exact Or.inr h1
      · next hch =>
        simp only [fStep, support_map, Set.mem_image] at hw
        obtain ⟨w', hw', rfl⟩ := hw
        have hc : c (.inr x) = none := by
          by_contra hc
          exact fwdLookup_eq_none_iff.mp hy (hs.st.fdom x hc)
        simp only [bookUpd, hy, hc, or_true, and_self, ite_true]
        obtain ⟨-, hst⟩ := hs.st.fStep x hw' (fun _ ↦ List.mem_cons_self)
          (List.subset_cons_self _ _) (fun _ h ↦ h)
        refine ⟨hst, fun y hy' ↦ List.mem_cons_of_mem _ (hs.hist y hy'), fun hf ↦ ?_⟩
        rcases hs.flag hf with h1 | h1
        · exact Or.inl (b0_mono (List.sublist_cons_self _ _) (List.Sublist.refl _) h1)
        · exact Or.inr h1
  · rw [shadow_perm_run] at hw
    simp only [invStep2] at hw
    split at hw
    · next x' hx =>
      simp only [support_pure, Set.mem_singleton_iff] at hw
      subst hw
      simpa [bookUpd, hx] using hs
    · next hx =>
      simp only [support_map, Set.mem_image] at hw
      obtain ⟨a, -, rfl⟩ := hw
      simp only [bookUpd, hx, ite_true]
      have hrep : replayStep σ (.inverse y, a) = ⟨(a, y) :: σ.edges, σ.chains⟩ := by
        simp [replayStep, hx]
      have h' := hs.st.mono_lists (dF' := b.dF) (fun _ h ↦ h) (List.subset_cons_self a b.dI)
      refine ⟨?_, hs.hist, fun hf ↦ ?_⟩
      · simp only [hrep]
        refine ⟨fun x' hx' ↦ ?_, h'.cv, h'.chains, fun p hp ↦ ?_⟩
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp (hs.st.fdom x' hx')
          exact List.mem_map.mpr ⟨e, List.mem_cons_of_mem _ he, rfl⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · exact Or.inr (Or.inl List.mem_cons_self)
        · exact h'.edges p hp
      · rcases hs.flag hf with h1 | h1
        · exact Or.inl (b0_mono (b := b) (List.Sublist.refl _) (List.sublist_cons_self _ _) h1)
        · exact Or.inr h1
  · rw [shadow_F_run] at hw
    simp only [fStep, support_map, Set.mem_image] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    simp only [bookUpd]
    set dF' := if c (.inr x) = none then w'.1 :: b.dF else b.dF with hdF'
    have hsub : b.dF.Sublist dF' := by
      rw [hdF']; split_ifs
      · exact List.sublist_cons_self _ _
      · exact List.Sublist.refl _
    obtain ⟨hw1, hst⟩ := hs.st.fStep x hw' (fun hc ↦ by simp [hdF', hc]) hsub.subset
      (fun _ h ↦ h)
    refine ⟨hst, fun y hy' ↦ ?_, fun hf ↦ ?_⟩
    · rcases List.mem_cons.mp hy' with rfl | hy'
      · exact hw1
      · exact hsub.subset (hs.hist y hy')
    · simp only [Bool.or_eq_true] at hf ⊢
      rcases hf with hf | hd
      · rcases hs.flag hf with h1 | h1
        · exact Or.inl (b0_mono hsub (List.Sublist.refl _) h1)
        · exact Or.inr (Or.inl h1)
      · by_cases hadm : Admissible iv NF b.hist x
        · exact Or.inl (b0_mono hsub (List.Sublist.refl _)
            (b0_of_disagree P hNF hs.st hs.hist hadm hd))
        · exact Or.inr (Or.inr (by simpa using hadm))

end Setting

end Common
