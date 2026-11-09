module

public import Common.Indiff.InvFwd

@[expose] public section

/-!
# Indifferentiability: the hash step keeps the invariant

A hash query `H m` of the combined game keeps `Inv`, and while no collision happens, the full
view's walk along the padded message ends in the value of the padded path, whose digest part is
the random oracle's `H m` (`inv_combHash`). The walk is analysed through `detWalk_spec`: when the
target edge set is a partial function containing the walk's nodes, the walk follows exactly
these nodes.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec

namespace Common

section Setting

variable {Dg E C Msg : Type}
  [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  {P : Padding Msg (Dg × E)} [P.Lawful] {iv : SpState Dg E C}

/-- The state reached after `i` blocks of `bs` from `s`, reading path values from `vf`. -/
def walkState (vf : List (Dg × E) → SpState Dg E C) (pre : List (Dg × E)) (s : SpState Dg E C)
    (bs : List (Dg × E)) (i : ℕ) : SpState Dg E C :=
  if i = 0 then s else vf (pre ++ bs.take i)

/-- One block further along the walk. -/
theorem walkState_cons (vf : List (Dg × E) → SpState Dg E C) (pre : List (Dg × E))
    (s y : SpState Dg E C) (B : Dg × E) (bs : List (Dg × E)) (i : ℕ)
    (hy : y = vf (pre ++ [B])) :
    walkState vf (pre ++ [B]) y bs i = walkState vf pre s (B :: bs) (i + 1) := by
  rcases i with _ | i <;> simp [walkState, hy, List.take_succ_cons]

/-- **The walk follows the target edges.** If the target edge set `G` is a partial function,
holds every recorded edge and every node edge of the walk, and every used path's node edge is
recorded, the walk ends in the value of the whole path, records only target edges, keeps the
recorded edges, and records every node edge. -/
theorem detWalk_spec (used : List (Dg × E) → Bool) (vf : List (Dg × E) → SpState Dg E C)
    (G : SpState Dg E C × SpState Dg E C → Prop)
    (hfun : ∀ x y y', G (x, y) → G (x, y') → y = y') (A₀ : PermutationEdges (SpState Dg E C)) :
    ∀ (bs pre : List (Dg × E)) (s : SpState Dg E C) (A : PermutationEdges (SpState Dg E C))
      (us : List (SpState Dg E C)),
      (∀ e ∈ A, G e) → (∀ e ∈ A₀, e ∈ A) →
      (∀ i (h : i < bs.length),
        G (absorb (walkState vf pre s bs i) bs[i], vf (pre ++ bs.take (i + 1)))) →
      (∀ i (h : i < bs.length), used (pre ++ bs.take (i + 1)) = true →
        (absorb (walkState vf pre s bs i) bs[i], vf (pre ++ bs.take (i + 1))) ∈ A₀) →
      (detWalk used vf pre s A bs us).1 = (if bs = [] then s else vf (pre ++ bs)) ∧
      (∀ e ∈ (detWalk used vf pre s A bs us).2, G e) ∧
      (∀ e ∈ A, e ∈ (detWalk used vf pre s A bs us).2) ∧
      (∀ i (h : i < bs.length), (absorb (walkState vf pre s bs i) bs[i],
        vf (pre ++ bs.take (i + 1))) ∈ (detWalk used vf pre s A bs us).2) := by
  intro bs
  induction bs with
  | nil =>
    intro pre s A us hA _ _ _
    exact ⟨by simp [detWalk], fun e he ↦ hA e he, fun e he ↦ he, fun i h ↦ absurd h (by simp)⟩
  | cons B bs ih =>
    intro pre s A us hA hA₀ hpath hused
    have h0 := hpath 0 (by simp)
    simp only [walkState, ↓reduceIte, List.getElem_cons_zero, List.take_succ_cons,
      List.take_zero] at h0
    -- the hypotheses for the rest of the walk
    have hpath' : ∀ y, y = vf (pre ++ [B]) → ∀ i (h : i < bs.length),
        G (absorb (walkState vf (pre ++ [B]) y bs i) bs[i],
          vf (pre ++ [B] ++ bs.take (i + 1))) := by
      intro y hy i hi
      have := hpath (i + 1) (by simp; omega)
      rw [walkState_cons vf pre s y B bs i hy]
      simpa [List.take_succ_cons] using this
    have hused' : ∀ y, y = vf (pre ++ [B]) → ∀ i (h : i < bs.length),
        used (pre ++ [B] ++ bs.take (i + 1)) = true →
        (absorb (walkState vf (pre ++ [B]) y bs i) bs[i],
          vf (pre ++ [B] ++ bs.take (i + 1))) ∈ A₀ := by
      intro y hy i hi hu
      have := hused (i + 1) (by simp; omega) (by simpa [List.take_succ_cons] using hu)
      rw [walkState_cons vf pre s y B bs i hy]
      simpa [List.take_succ_cons] using this
    -- the lookup at the first node returns the target edge
    have hlook : ∀ y, forwardLookup A (absorb s B) = some y → y = vf (pre ++ [B]) := by
      intro y hy
      exact hfun _ _ _ (hA _ (mem_of_fwdLookup_eq_some hy)) h0
    -- the first node's edge is recorded after the walk
    have hfirst : ∀ (A' : PermutationEdges (SpState Dg E C)), (absorb s B, vf (pre ++ [B])) ∈ A' →
        ∀ (us' : List (SpState Dg E C)), (∀ e ∈ A', G e) →
        (∀ e ∈ A₀, e ∈ A') → (∀ e ∈ A, e ∈ A') →
        (detWalk used vf (pre ++ [B]) (vf (pre ++ [B])) A' bs us').1 =
            (if B :: bs = [] then s else vf (pre ++ B :: bs)) ∧
          (∀ e ∈ (detWalk used vf (pre ++ [B]) (vf (pre ++ [B])) A' bs us').2, G e) ∧
          (∀ e ∈ A, e ∈ (detWalk used vf (pre ++ [B]) (vf (pre ++ [B])) A' bs us').2) ∧
          (∀ i (h : i < (B :: bs).length), (absorb (walkState vf pre s (B :: bs) i) (B :: bs)[i],
            vf (pre ++ (B :: bs).take (i + 1))) ∈
              (detWalk used vf (pre ++ [B]) (vf (pre ++ [B])) A' bs us').2) := by
      intro A' hmem us' hA' hA₀' hAA'
      obtain ⟨h1, h2, h3, h4⟩ := ih (pre ++ [B]) (vf (pre ++ [B])) A' us' hA' hA₀'
        (hpath' _ rfl) (hused' _ rfl)
      refine ⟨?_, h2, fun e he ↦ h3 e (hAA' e he), fun i hi ↦ ?_⟩
      · rw [h1]
        rcases bs with _ | ⟨b, bs⟩ <;> simp
      · rcases i with _ | i
        · simp only [walkState, ↓reduceIte, List.getElem_cons_zero, List.take_succ_cons,
            List.take_zero]
          exact h3 _ hmem
        · have := h4 i (by simp at hi; omega)
          rw [walkState_cons vf pre s _ B bs i rfl] at this
          simpa [List.take_succ_cons] using this
    simp only [detWalk]
    split
    · next y hy =>
      obtain rfl := hlook y hy
      exact hfirst A (mem_of_fwdLookup_eq_some hy) us.tail hA hA₀ fun _ h ↦ h
    · next hy =>
      have hnu : used (pre ++ [B]) = false := by
        by_contra hu
        have hmem := hA₀ _ (by
          have := hused 0 (by simp) (by simpa using hu)
          simpa [walkState] using this)
        have := fwdLookup_eq_some_of_mem hmem fun e he hex ↦ hfun _ _ _
          (by rw [← hex]; exact hA e he) h0
        rw [hy] at this
        exact absurd this (by simp)
      simp only [hnu, Bool.false_eq_true, ↓reduceIte]
      exact hfirst _ List.mem_cons_self us.tail
        (fun e he ↦ by
          rcases List.mem_cons.mp he with rfl | he
          · exact h0
          · exact hA e he)
        (fun e he ↦ List.mem_cons_of_mem _ (hA₀ e he))
        (fun e he ↦ List.mem_cons_of_mem _ he)

/-- The prefixes of a hashed message's padding, as `take`s. -/
theorem take_succ_eq_append {bs : List (Dg × E)} {i : ℕ} (h : i < bs.length) :
    bs.take (i + 1) = bs.take i ++ [bs[i]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]; rfl

/-- The hashed prefixes after hashing `m`. -/
theorem mem_hPaths_cons {L : List Msg} {m : Msg} {β : List (Dg × E)} :
    β ∈ hPaths P (m :: L) ↔ β ∈ prefixesOf (P.pad m) ∨ β ∈ hPaths P L := by
  simp [hPaths]

/-- **The hash step keeps the invariant.** -/
theorem inv_combHash {cs : CState Dg E C Msg} {c : ACache Msg Dg E C} (hI : Inv P iv cs c)
    (m : Msg) {z : ((Dg × Dg) × CState Dg E C Msg) × ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (aSpec Msg Dg E C).romImpl
      ((combHash P iv m).run cs)).run c)) : Inv P iv z.1.2 z.2 := by
  obtain ⟨hS, hcond⟩ := hI
  obtain ⟨w, c₁, d, hw, hd, hz1⟩ := combHash_support P iv m cs c hz
  obtain ⟨hcc₁, hcached, -, us, hdet⟩ := allWalk_support P _ [] iv cs.all (P.pad m) c hw
  obtain ⟨hc₁c', hd', -⟩ := roStep_support (hs := aSpec Msg Dg E C) (.inl m) c₁ hd
  simp only [List.nil_append] at hcached hdet
  set c' := z.2 with hc'
  have hcc' : c ≤ c' := le_trans hcc₁ hc₁c'
  rw [hz1]
  set cs' := (hashOut cs m w d).2 with hcs'
  have hsim : cs'.sim = cs.sim := rfl
  have hhashed : cs'.hashed = m :: cs.hashed := rfl
  set pm := P.pad m with hpm
  have hpm0 : pm ≠ [] := P.pad_ne_nil m
  -- the path values along the padded message
  set vf : List (Dg × E) → SpState Dg E C := fun β ↦ (valC P c' β).getD iv with hvf
  have hvfc : ∀ i < pm.length, valC P c' (pm.take (i + 1)) = some (vf (pm.take (i + 1))) := by
    intro i hi
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hcached i hi)
    have h' := valC_mono P hc₁c' hv
    rw [h']
    simp [hvf, h']
  have hw_eq : w = detWalk (usedPath P cs.sim.chains cs.hashed) vf [] iv cs.all pm us :=
    hdet vf fun i hi ↦ by
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hcached i hi)
      rw [hv]
      have := hvfc i hi
      rw [valC_mono P hc₁c' hv] at this
      exact this
  have hsv : ∀ i ≤ pm.length, svC P iv c' (pm.take i) = some (walkState vf [] iv pm i) := by
    intro i hi
    rcases i with _ | i
    · simp [svC, walkState]
    · rw [svC_of_ne_nil (by simp [List.take_eq_nil_iff, hpm0]), hvfc i (by omega)]
      simp [walkState]
  -- the bookkeeping
  have hS' : Struct P iv cs' c' := by
    refine ⟨hS.root, fun p hp ↦ svC_mono hcc' (hS.chainVal p hp), hS.chainEdge, fun β hβ ↦ ?_⟩
    rcases mem_hPaths_cons.mp (hhashed ▸ hβ) with h | h
    · obtain ⟨i, hi, rfl⟩ := mem_prefixesOf.mp h
      rw [hvfc i hi]; simp
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hS.hCached β h)
      rw [valC_mono P hcc' hv]; simp
  refine ⟨hS', fun hbad hEC' ↦ ?_⟩
  have hHid : ∀ β, Hidden P cs.vis β → Hidden P cs'.vis β := fun β hβ ↦
    ⟨by rw [show cs'.vis.2.1 = m :: cs.hashed from rfl]; exact mem_hPaths_cons.mpr (Or.inr hβ.1),
      hβ.2⟩
  have hEC : ¬ EC P iv cs.vis c := by
    rintro ⟨β, v, hβ, hv, h⟩
    refine hEC' ⟨β, v, hHid β hβ, valC_mono P hcc' hv, ?_⟩
    rcases h with h | ⟨γ, w', hγ, hne, hw', hwv⟩
    · exact Or.inl h
    · exact Or.inr ⟨γ, w', hHid γ hγ, hne, valC_mono P hcc' hw', hwv⟩
  have hC := hcond hbad hEC
  have hV' : VisCons cs'.sim := hC.vis
  -- the target edges
  set G := GEdge P iv cs' c' with hG
  have hGmono : ∀ e, GEdge P iv cs c e → G e := by
    rintro e (h | h)
    · exact Or.inl h
    · exact Or.inr (hiddenEdge_mono hcc' hHid h)
  have hfun : ∀ x y y', G (x, y) → G (x, y') → y = y' := fun x y y' h h' ↦ by
    have := gEdge_fst_inj hS' hV' hEC' h h' rfl
    simp only [Prod.mk.injEq] at this
    exact this.2
  -- a visible prefix's node edge is a simulator edge
  have hvisEdge : ∀ i (hi : i < pm.length), pm.take (i + 1) ∈ vPaths cs.sim →
      (absorb (walkState vf [] iv pm i) pm[i], vf (pm.take (i + 1))) ∈ cs.sim.edges := by
    intro i hi hvis
    obtain ⟨v₀, hv₀⟩ := exists_chain_of_mem_vPaths hvis
    obtain ⟨q, hq, B, h1, h2⟩ := hS.chainEdge _ hv₀ (by simp [List.take_eq_nil_iff, hpm0])
    rw [take_succ_eq_append hi] at h1
    obtain ⟨h3, h4⟩ := List.append_inj' h1 rfl
    obtain rfl : pm[i] = B := List.singleton_inj.mp h4
    have hq1 := svC_mono hcc' (hS.chainVal q hq)
    rw [← h3, hsv i (by omega)] at hq1
    have hv1 := svC_mono hcc' (hS.chainVal _ hv₀)
    simp only at hv1
    rw [svC_of_ne_nil (by simp [List.take_eq_nil_iff, hpm0]), hvfc i hi] at hv1
    rw [Option.some.inj hq1, Option.some.inj hv1]
    exact h2
  -- a prefix's node edge
  have hpath : ∀ i (hi : i < pm.length),
      G (absorb (walkState vf [] iv pm i) pm[i], vf ([] ++ pm.take (i + 1))) := by
    intro i hi
    rw [List.nil_append]
    by_cases hvis : pm.take (i + 1) ∈ vPaths cs.sim
    · exact Or.inl (hvisEdge i hi hvis)
    · refine Or.inr ⟨pm.take i, pm[i], _, _,
        ⟨?_, by rw [← take_succ_eq_append hi]; exact hvis⟩, hsv i (by omega), ?_, rfl⟩
      · rw [show cs'.vis.2.1 = m :: cs.hashed from rfl, ← take_succ_eq_append hi]
        exact mem_hPaths_cons.mpr (Or.inl (mem_prefixesOf.mpr ⟨i, hi, rfl⟩))
      · rw [← take_succ_eq_append hi]; exact hvfc i hi
  -- a used prefix's node edge is already in the full view
  have hused : ∀ i (hi : i < pm.length),
      usedPath P cs.sim.chains cs.hashed ([] ++ pm.take (i + 1)) = true →
      (absorb (walkState vf [] iv pm i) pm[i], vf ([] ++ pm.take (i + 1))) ∈ cs.all := by
    intro i hi hu
    rw [List.nil_append] at hu ⊢
    by_cases hvis : pm.take (i + 1) ∈ vPaths cs.sim
    · exact (hC.allMem _).mpr (Or.inl (hvisEdge i hi hvis))
    · have hH : pm.take (i + 1) ∈ hPaths P cs.hashed := by
        simp only [usedPath, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hu
        rcases hu with hu | ⟨m', hm', hu⟩
        · exact absurd hu hvis
        · exact List.mem_flatMap.mpr ⟨m', hm', hu⟩
      have hhid : Hidden P cs.vis (pm.take i ++ [pm[i]]) := by
        rw [← take_succ_eq_append hi]; exact ⟨hH, hvis⟩
      obtain ⟨v₀, hv₀⟩ := Option.ne_none_iff_exists'.mp (hS.hCached _ hhid.1)
      obtain ⟨s₀, hs₀⟩ := svC_known hS (knownPath_init hS (Or.inr hhid))
      obtain rfl := svC_eq_of_le hcc' hs₀ (hsv i (by omega))
      have := hvfc i hi
      rw [take_succ_eq_append hi] at this
      obtain rfl := valC_eq_of_le hcc' hv₀ this
      refine (hC.allMem _).mpr (Or.inr ⟨pm.take i, pm[i], _, _, hhid, hs₀, hv₀, ?_⟩)
      rw [take_succ_eq_append hi]
  obtain ⟨hw1, hwG, hwA, hwN⟩ := detWalk_spec (usedPath P cs.sim.chains cs.hashed) vf G hfun
    cs.all pm [] iv cs.all us (fun e he ↦ hGmono e ((hC.allMem e).mp he)) (fun _ h ↦ h)
    hpath hused
  rw [← hw_eq] at hw1 hwG hwA hwN
  simp only [hpm0, ↓reduceIte, List.nil_append] at hw1
  -- the real answer is the random oracle's digest
  have hdig : w.1.1.1 = d := by
    have hlen : 0 < pm.length := List.length_pos_iff.mpr hpm0
    have hv := hvfc (pm.length - 1) (by omega)
    rw [Nat.sub_add_cancel (List.length_pos_iff.mpr hpm0), List.take_length] at hv
    rw [hw1]
    simp only [valC, hpm, P.unpad_pad, hd'] at hv
    simp only [Option.bind_some, Option.map_eq_some_iff] at hv
    obtain ⟨t, -, ht⟩ := hv
    rw [← ht]
  refine ⟨hV', fun e ↦ ⟨fun he ↦ hwG e he, fun he ↦ ?_⟩, ?_⟩
  · rcases he with he | ⟨γ, G', t, v, hδ, ht, hv, rfl⟩
    · exact hwA _ ((hC.allMem _).mpr (Or.inl he))
    · rcases mem_hPaths_cons.mp hδ.1 with h | h
      · obtain ⟨i, hi, hγ⟩ := mem_prefixesOf.mp h
        change i < pm.length at hi
        rw [take_succ_eq_append hi] at hγ
        obtain ⟨rfl, hGG⟩ := List.append_inj' hγ rfl
        obtain rfl : G' = pm[i] := List.singleton_inj.mp hGG
        rw [hsv i (by omega)] at ht
        obtain rfl := Option.some.inj ht
        have := hvfc i hi
        rw [take_succ_eq_append hi, hv] at this
        obtain rfl := Option.some.inj this
        have := hwN i hi
        rw [take_succ_eq_append hi] at this
        exact this
      · have hhid : Hidden P cs.vis (γ ++ [G']) := ⟨h, hδ.2⟩
        obtain ⟨v₀, hv₀⟩ := Option.ne_none_iff_exists'.mp (hS.hCached _ h)
        obtain ⟨s₀, hs₀⟩ := svC_known hS (knownPath_init hS (Or.inr hhid))
        obtain rfl := svC_eq_of_le hcc' hs₀ ht
        obtain rfl := valC_eq_of_le hcc' hv₀ hv
        exact hwA _ ((hC.allMem _).mpr (Or.inr ⟨γ, G', _, _, hhid, hs₀, hv₀, rfl⟩))
  · simp [hcs', hashOut, hdig, hC.noDiff]

end Setting

end Common
