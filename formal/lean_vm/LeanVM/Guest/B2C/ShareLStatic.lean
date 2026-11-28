/-
  LeanVM.Guest.B2C.ShareLStatic

  What the local sharing check says of a function's values and lists once: each value's cell in
  the frame, its temporaries and frame runs listed, its call sites' and table targets' cells free.
-/

module

public import LeanVM.Guest.B2C.ShareLSound
public import LeanVM.Guest.B2C.Static

/-!
# The local sharing check's static facts

`staticD_of_check`: every value a function's body names (or a parameter, or a temporary) is
`V.n` of its number and its cell is in the frame or a tail call's next frame, in no fixed frame
pointer cell, and in a temporary's cell only if it is that temporary; parameters are in the
frame; temporaries and frame runs are listed with their cells; no value is in a call site's or a
table target's cell; in `main` every value's cell is below the jump table.
-/

namespace LeanVM.Guest.B2C.ShareL

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Local
open LeanVM.Guest.Check LeanVM.Guest.Exec LeanVM.Guest.Memory

@[expose] public section

/-- **What the check gives statically** of core IR `cf`, certificate `C`, completeness data `P`,
frame size `fs`. -/
structure StaticD (cf : Core.Fn) (C : Cert) (P : Plumb) (fs : ℕ) (main : Bool) (mc : ℕ) : Prop where
  vals : ∀ v ∈ cf.params ++ Stmt.usesList cf.body ++ Stmt.tmpsList cf.body, v = V.n v.idx ∧
    (C.locs.getD v.idx 0 < fs ∨ C.locs.getD v.idx 0 ∈ nextCells C.locs fs (tailArgs cf)) ∧
    bitN (fpgCells P) (C.locs.getD v.idx 0) = false ∧
    (bitN (tmpCells P) (C.locs.getD v.idx 0) = false ∨ (v.idx, C.locs.getD v.idx 0) ∈ P.tmps)
  param : ∀ v ∈ cf.params, C.locs.getD v.idx 0 < fs
  tmp : ∀ t ∈ Stmt.tmpsList cf.body, t = V.n t.idx ∧ (t.idx, C.locs.getD t.idx 0) ∈ P.tmps
  run : ∀ p r rs, Atom.frameAddr p (r :: rs) ∈ lAtoms cf.body → ∀ (k : ℕ) (hk : k < (r :: rs).length),
    (r :: rs)[k] = V.n (r :: rs)[k].idx ∧ C.locs.getD (r :: rs)[k].idx 0 = C.locs.getD r.idx 0 + k ∧
      ((r :: rs)[k].idx, C.locs.getD r.idx 0 + k) ∈ P.runs
  sites : ∀ c ∈ siteCells P, c ∉ C.locs
  arms : ∀ a ∈ P.arms, a.2.1 ∉ C.locs
  mainBound : main = true → ∀ c ∈ C.locs, c < mc
  lists : listsOk P fs = true
  apartL : apartOkL C P main mc = true

mutual
/-- An atom of a block is at a position. -/
theorem atoms_at : ∀ (c : Ctx) (p : ℕ) (ss : List Stmt) {a : Core.Atom}, a ∈ lAtoms ss →
    ∃ q c', AtL c p ss q (.atom a) c'
  | _, _, [], _, h => by simp [lAtoms] at h
  | c, p, s :: ss, a, h => by
      simp only [lAtoms, List.mem_append] at h
      rcases h with h | h
      · rcases atomsS_at p s h with rfl | ⟨q, c', h1⟩
        · exact ⟨p, c, .head c p _ ss⟩
        · exact ⟨q, c', .inside h1⟩
      · obtain ⟨q, c', h1⟩ := atoms_at c (p + size s) ss h
        exact ⟨q, c', .tail h1⟩

theorem atomsS_at : ∀ (p : ℕ) (s : Stmt) {a : Core.Atom}, a ∈ sAtoms s →
    s = .atom a ∨ ∃ q c', AtS p s q (.atom a) c'
  | p, .ite x z n, a, h => by
      simp only [sAtoms, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨q, c', h1⟩ := atoms_at ⟨p + 1 + sizeL z, p, p + 1⟩ (p + 1) z h
        exact .inr ⟨q, c', .zero h1⟩
      · obtain ⟨q, c', h1⟩ := atoms_at ⟨p + 1 + sizeL z + sizeL n, p, p + 1 + sizeL z⟩ (p + 1 + sizeL z) n h
        exact .inr ⟨q, c', .nonzero h1⟩
  | p, .match_ x arms, a, h => by
      simp only [sAtoms] at h
      obtain ⟨q, c', h1⟩ := atomsA_at p (p + 1) arms h
      exact .inr ⟨q, c', .arm h1⟩
  | p, .atom a', a, h => .inl (by simp only [sAtoms, List.mem_singleton] at h; rw [h])
  | p, .call .., a, h => by simp [sAtoms] at h
  | p, .callIf .., a, h => by simp [sAtoms] at h
  | p, .dispatch .., a, h => by simp [sAtoms] at h
  | p, .ret _, a, h => by simp [sAtoms] at h

theorem atomsA_at : ∀ (t a : ℕ) (bs : List (List Stmt)) {at' : Core.Atom}, at' ∈ aAtoms bs →
    ∃ q c', AtA t a bs q (.atom at') c'
  | _, _, [], _, h => by simp [aAtoms] at h
  | t, a, b :: bs, at', h => by
      simp only [aAtoms, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨q, c', h1⟩ := atoms_at ⟨a + sizeL b, t, a⟩ a b h
        exact ⟨q, c', .here h1⟩
      · obtain ⟨q, c', h1⟩ := atomsA_at t (a + sizeL b) bs h
        exact ⟨q, c', .next h1⟩
end

section Static

variable {cf : Core.Fn} {C : Cert} {P : Plumb} {fs : ℕ} {main : Bool} {mc : ℕ} {T : Tabs}

local notation "Kf" => fnK cf C P fs main mc T

theorem cell_getD (H : CheckL cf C P fs main mc T) {u : ℕ} (hu : u < C.locs.length) :
    cellOf Kf u = C.locs.getD u 0 := by
  have := locsOk_spec (T := T) C.locs 0 H.locs u hu
  rw [Nat.zero_add] at this
  simp only [List.getD, List.getElem?_eq_getElem hu, Option.getD_some]; exact this

/-- A value's cell is owned, unless shared, when at least `2`. -/
theorem ot_ne_zero (H : CheckL cf C P fs main mc T) {u : ℕ} (hu : u < C.locs.length)
    (hc : 2 ≤ cellOf Kf u) : tget wO 8 5 T.ot (cellOf Kf u) ≠ 0 := by
  by_cases hs : vSh (vlane Kf u) = 0
  · rw [unshared_owner H hu hs hc]; omega
  · obtain ⟨q, i, st, cx, -, -, -, -, -, hsh⟩ := shared_home H hu hs
    have := (sharedOk_spec _ hsh).2.2.2.1
    intro h0; rw [h0] at this; simp at this

/-- A free cell holds no value. -/
theorem free_not_mem (H : CheckL cf C P fs main mc T) {cs : List ℕ} (hf : freeOk T cs = true) {c : ℕ}
    (hc : c ∈ cs) : c ∉ C.locs := by
  simp only [freeOk, allR_eq, List.all_eq_true, band, Nat.ble_eq, nbeq_iff'] at hf
  obtain ⟨h2, h0⟩ := hf c hc
  intro hm
  obtain ⟨u, hu, rfl⟩ := List.getElem_of_mem hm
  have := cell_getD H hu
  simp only [List.getD, List.getElem?_eq_getElem hu, Option.getD_some] at this
  rw [← this] at h0 h2
  exact ot_ne_zero H hu h2 h0

theorem tmpCells_bit {P : Plumb} {c : ℕ} (h : bitN (tmpCells P) c = true) : ∃ t, (t, c) ∈ P.tmps := by
  rw [bitN_eq, tmpCells, testBit_bitsOf] at h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  exact ⟨p.1, hp⟩

/-- **The static facts.** -/
theorem staticD_of_check (H : CheckL cf C P fs main mc T) : StaticD cf C P fs main mc := by
  obtain ⟨n0, f, hp, hf1, hfe, hst⟩ := H.run
  -- an operand's home facts
  have hhome : ∀ {q i v st cx}, Opd cf T q i v st cx → v = V.n v.idx ∧
      (C.locs.getD v.idx 0 < fs ∨ C.locs.getD v.idx 0 ∈ nextCells C.locs fs (tailArgs cf)) ∧
      bitN (fpgCells P) (C.locs.getD v.idx 0) = false ∧
      (bitN (tmpCells P) (C.locs.getD v.idx 0) = false ∨ (v.idx, C.locs.getD v.idx 0) ∈ P.tmps) ∧
      (main = true → C.locs.getD v.idx 0 < mc) := by
    intro q i v st cx ho
    have hlt := opd_lt H ho
    have hv := opd_vn H ho
    obtain ⟨q0, i0, st0, cx0, -, hh⟩ := home_at H hlt
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := homeOk_spec _ hh
    have hcg := cell_getD H hlt
    unfold cellOf at hcg
    rw [hcg] at h1 h2 h3 h4 h5 h6
    refine ⟨hv, h1, h2, ?_, fun hm ↦ ?_⟩
    · cases hb : bitN (tmpCells P) (C.locs.getD v.idx 0)
      · exact .inl rfl
      · right
        obtain ⟨t, ht⟩ := tmpCells_bit hb
        have hpairs : 2 ≤ C.locs.getD v.idx 0 := by
          have hl := H.lists
          simp only [listsOk, Exec.Trie.seq_eq, natSeq_eq, Bool.and_eq_true] at hl
          exact ((pairsOk_spec hl.1.1.1.1.2).1 _ ht).1
        have hot : tget wO 8 5 (fnK cf C P fs main mc T).T.ot (C.locs.getD v.idx 0) = 4 * t + 1 := by
          have := H.tmps
          simp only [tmpsOk, allR_eq, List.all_eq_true, nbeq_iff'] at this
          exact this _ ht
        by_cases hs : vSh (vlane Kf v.idx) = 0
        · have := h5 hpairs hs
          rw [hot] at this
          have e : v.idx = t := by omega
          rw [e] at ht ⊢; exact ht
        · have := (sharedOk_spec _ (h6 hpairs hs).2.2.2).2.2.2.1
          rw [hot] at this; omega
    · simp only [fnK, hm, Bool.cond_true] at h3; exact h3
  -- the step at a position
  have hstep : ∀ {q a cx}, AtL (c0 T) 1 cf.body q (.atom a) cx → listedOk Kf (.atom a) = true := by
    intro q a cx hat
    exact (step_spec _ (hst q _ cx hat)).1
  refine ⟨fun v hv ↦ ?_, fun v hv ↦ ?_, fun t ht ↦ ?_, fun p r rs ha k hk ↦ ?_, fun c hc ↦ free_not_mem H H.sites hc,
    fun a ha ↦ free_not_mem H H.arms (List.mem_map_of_mem ha), fun hm c hc ↦ ?_, H.lists, H.apart⟩
  · -- every value
    obtain ⟨q, i, st, cx, ho⟩ : ∃ q i st cx, Opd cf T q i v st cx := by
      rcases List.mem_append.mp hv with hv | hv
      · rcases List.mem_append.mp hv with hv | hv
        · obtain ⟨i, hi⟩ := mem_getElem? hv
          exact ⟨0, i, .ret cf.params, c0 T, .inl ⟨rfl, rfl, rfl⟩, by simpa [ownVals] using hi⟩
        · obtain ⟨q, s, c', hat, hn⟩ := uses_at (c0 T) 1 cf.body hv
          obtain ⟨i, hi⟩ := mem_getElem? (names_sub hn)
          exact ⟨q, i, s, c', .inr ⟨(atL_range hat).1, hat⟩, hi⟩
      · obtain ⟨q, a, c', hat, hn⟩ := tmps_at (c0 T) 1 cf.body hv
        obtain ⟨i, hi⟩ := mem_getElem? (tmps_sub hn)
        exact ⟨q, i, _, c', .inr ⟨(atL_range hat).1, hat⟩, hi⟩
    exact (hhome ho).1 |> fun h1 ↦ ⟨h1, (hhome ho).2.1, (hhome ho).2.2.1, (hhome ho).2.2.2.1⟩
  · -- parameters
    obtain ⟨i, hi⟩ := mem_getElem? hv
    have ho : Opd cf T 0 i v (.ret cf.params) (c0 T) := ⟨.inl ⟨rfl, rfl, rfl⟩, by simpa [ownVals] using hi⟩
    have hcg := cell_getD H (opd_lt H ho)
    unfold cellOf at hcg
    rw [← hcg]; exact H.params v hv
  · -- temporaries
    obtain ⟨q, a, c', hat, hn⟩ := tmps_at (c0 T) 1 cf.body ht
    obtain ⟨i, hi⟩ := mem_getElem? (tmps_sub hn)
    have ho : Opd cf T q i t (.atom a) c' := ⟨.inr ⟨(atL_range hat).1, hat⟩, hi⟩
    have hcg := cell_getD H (opd_lt H ho)
    have hl := hstep hat
    cases a with
    | rangeCheck x y t1 t2 k =>
      simp only [listedOk, band] at hl
      simp only [atomTmps, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl
      · have := listedT_spec hl.1; rw [hcg] at this; exact this
      · have := listedT_spec hl.2; rw [hcg] at this; exact this
    | touch t' p =>
      simp only [listedOk] at hl
      simp only [atomTmps, List.mem_cons, List.not_mem_nil, or_false] at hn
      subst hn
      have := listedT_spec hl; rw [hcg] at this; exact this
    | _ => simp [atomTmps] at hn
  · -- frame runs
    obtain ⟨q, c', hat⟩ := atoms_at (c0 T) 1 cf.body ha
    have hl := hstep hat
    simp only [listedOk] at hl
    have hrun : ∀ (base k : ℕ) (vs : List V), listedOk.runListedL Kf base k vs = true →
        ∀ (m : ℕ) (hm : m < vs.length), cellOf Kf vs[m].idx = base + k + m ∧
          listed (fnK cf C P fs main mc T).runs vs[m] (base + k + m) = true := by
      intro base k vs
      induction vs generalizing k with
      | nil => intro _ m hm; simp at hm
      | cons v vs ih =>
        intro h m hm
        simp only [listedOk.runListedL, band, nbeq_iff'] at h
        cases m with
        | zero => exact ⟨by simpa using h.1.1, by simpa using h.1.2⟩
        | succ m =>
          obtain ⟨e1, e2⟩ := ih (k + 1) h.2 m (by simpa using hm)
          refine ⟨by simpa [show base + k + (m + 1) = base + (k + 1) + m by omega] using e1, ?_⟩
          simpa [show base + k + (m + 1) = base + (k + 1) + m by omega] using e2
    obtain ⟨e1, e2⟩ := hrun _ 0 _ hl k hk
    obtain ⟨e3, e4⟩ := listed_spec e2
    have hmem : ∀ v ∈ r :: rs, ∃ i, Opd cf T q i v (.atom (.frameAddr p (r :: rs))) c' := fun v hv ↦ by
      obtain ⟨i, hi⟩ := mem_getElem? (show v ∈ ownVals (.atom (.frameAddr p (r :: rs))) by
        simp only [ownVals, atomVals]; exact List.mem_cons_of_mem _ hv)
      exact ⟨i, .inr ⟨(atL_range hat).1, hat⟩, hi⟩
    have hcg : ∀ v ∈ r :: rs, cellOf Kf v.idx = C.locs.getD v.idx 0 := fun v hv ↦ by
      obtain ⟨i, hoi⟩ := hmem v hv
      exact cell_getD H (opd_lt H hoi)
    rw [hcg _ (List.getElem_mem hk), hcg r List.mem_cons_self, Nat.add_zero] at e1
    rw [hcg r List.mem_cons_self, Nat.add_zero] at e4
    exact ⟨e3, e1, e4⟩
  · -- main
    obtain ⟨u, hu, rfl⟩ := List.getElem_of_mem hc
    have ho : ∃ q i st cx, Opd cf T q i (V.n u) st cx := by
      obtain ⟨q, i, st, cx, ho, -⟩ := home_at H hu; exact ⟨q, i, st, cx, ho⟩
    obtain ⟨q, i, st, cx, ho⟩ := ho
    have := (hhome ho).2.2.2.2 hm
    simpa [List.getD, List.getElem?_eq_getElem hu] using this

end Static

end
end LeanVM.Guest.B2C.ShareL
