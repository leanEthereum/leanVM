module

public import Common.Duplex.Table

@[expose] public section

/-!
# The simulator's invariant

Without collision, the simulator's records describe the derivations: every programmed answer
carries its challenge (`Inv`), and every branch of a programmed first answer is either answered
with its challenge or would be programmed with it (`NextOK`). A fresh step without collision keeps
this (`inv_record`).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open Common
open Common.Duplex (GSpec hP gaP VSpec toV)

namespace Common.SeedDuplex

variable {Msg Dg St Root Z W Cp : Type} {n : ℕ}
  [DecidableEq Msg] [DecidableEq St] [DecidableEq Root] [DecidableEq Cp]
  (D : DuplexSpec Msg Dg St Root Z W Cp n)

/-! ## The records after a step -/

theorem answer_record (s : SimSt Dg St Root n) (x y : St) (lbl : Option (Root × Fin n)) (x' : St) :
    (s.record D x y lbl).answer x' = if x' = x then some y else s.answer x' := by
  by_cases h : x' = x
  · subst h; simp [SimSt.answer, SimSt.record]
  · simp only [SimSt.answer, SimSt.record, h, ↓reduceIte]
    rw [List.find?_cons_of_neg (by simpa [eq_comm] using h)]

theorem log_record (s : SimSt Dg St Root n) (x y : St) (lbl : Option (Root × Fin n)) :
    (s.record D x y lbl).log = (x, y, lbl) :: s.log := rfl

theorem x0_record (s : SimSt Dg St Root n) (x y : St) (lbl : Option (Root × Fin n)) :
    (s.record D x y lbl).x0 = s.x0 := rfl

theorem iv_record (s : SimSt Dg St Root n) (x y : St) (lbl : Option (Root × Fin n)) :
    (s.record D x y lbl).iv = s.iv := rfl

theorem labOf_record_none (s : SimSt Dg St Root n) (x y : St) (x' : St) :
    (s.record D x y none).labOf x' = s.labOf x' := rfl

theorem mem_children {r : Root} {y : St} {p : St × (Root × Fin n)} :
    p ∈ children D r y ↔ ∃ k : Fin n, k.val ≠ 0 ∧ p = (D.next k y, (r, k)) := by
  simp only [children, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq]
  exact ⟨fun ⟨k, hk, h⟩ ↦ ⟨k, hk, h.symm⟩, fun ⟨k, hk, h⟩ ↦ ⟨k, hk, h.symm⟩⟩

theorem lab_record (s : SimSt Dg St Root n) (x y : St) (lbl : Option (Root × Fin n)) :
    (s.record D x y lbl).lab = s.lab ∨
      ∃ r j, lbl = some (r, j) ∧ j.val = 0 ∧ (s.record D x y lbl).lab = children D r y ++ s.lab := by
  rcases lbl with _ | ⟨r, j⟩
  · exact Or.inl rfl
  · by_cases hj : j.val = 0
    · exact Or.inr ⟨r, j, rfl, hj, by simp [SimSt.record, hj]⟩
    · exact Or.inl (by simp [SimSt.record, hj])

/-- A branch of a programmed first answer is registered with its challenge. -/
theorem labOf_record_branch (s : SimSt Dg St Root n) (x y : St) (r : Root) (j k : Fin n)
    (hj : j.val = 0) (hk : k.val ≠ 0) :
    (s.record D x y (some (r, j))).labOf (D.next k y) = some (r, k) := by
  have e : (s.record D x y (some (r, j))).lab = children D r y ++ s.lab := by
    simp [SimSt.record, hj]
  have hmem : (D.next k y, (r, k)) ∈ children D r y := (mem_children D).mpr ⟨k, hk, rfl⟩
  simp only [SimSt.labOf, e, List.find?_append]
  obtain ⟨p, hp⟩ : ∃ p, (children D r y).find? (fun p ↦ decide (p.1 = D.next k y)) = some p :=
    Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨_, hmem, by simp⟩)
  obtain ⟨k', -, rfl⟩ := (mem_children D).mp (List.mem_of_find?_eq_some hp)
  have h1 := List.find?_some hp
  simp only [decide_eq_true_eq] at h1
  rw [D.next_inj k' k y h1] at hp
  rw [hp]
  rfl

/-- Away from the branches of the answer `y`, a step keeps the registered challenges. -/
theorem labOf_record_ne (s : SimSt Dg St Root n) (x y : St) (P : Option (Root × Fin n)) {x' : St}
    (hne : ∀ k : Fin n, x' ≠ D.next k y) : (s.record D x y P).labOf x' = s.labOf x' := by
  rcases lab_record D s x y P with h | ⟨r, j, -, -, h⟩
  · simp only [SimSt.labOf, h]
  · simp only [SimSt.labOf, h, List.find?_append]
    have hnone : (children D r y).find? (fun p ↦ decide (p.1 = x')) = none := by
      rw [List.find?_eq_none]
      intro p hp hpx
      obtain ⟨k, -, rfl⟩ := (mem_children D).mp hp
      exact hne k (of_decide_eq_true hpx).symm
    rw [hnone]
    rfl

theorem mem_forb_of_key {s : SimSt Dg St Root n} {e} (he : e ∈ s.log) :
    D.cap e.1 ∈ forb D s := by
  simp only [forb, List.mem_toFinset, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl ⟨e, he, rfl⟩)

theorem mem_forb_of_val {s : SimSt Dg St Root n} {e} (he : e ∈ s.log) :
    D.cap e.2.1 ∈ forb D s := by
  simp only [forb, List.mem_toFinset, List.mem_append, List.mem_map]
  exact Or.inl (Or.inr ⟨e, he, rfl⟩)

theorem mem_forb_of_x0 {s : SimSt Dg St Root n} {x0} (h : s.x0 = some x0) :
    D.cap x0 ∈ forb D s := by
  simp [forb, h]

theorem answer_eq_some {s : SimSt Dg St Root n} {x y : St} (h : s.answer x = some y) :
    ∃ e ∈ s.log, e.1 = x ∧ e.2.1 = y := by
  simp only [SimSt.answer, Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  exact ⟨e, List.mem_of_find?_eq_some he, by simpa using List.find?_some he, rfl⟩

theorem answer_eq_none {s : SimSt Dg St Root n} {x : St} (h : s.answer x = none) :
    ∀ e ∈ s.log, e.1 ≠ x := by
  simp only [SimSt.answer, Option.map_eq_none_iff, List.find?_eq_none] at h
  exact fun e he hx ↦ h e he (by simpa using hx)

theorem cap_first' (r : Root) (d : Dg) : D.cap (D.first r d) = D.cap (D.init d) := D.cap_first r d

theorem cap_next' (j : Fin n) (y : St) : D.cap (D.next j y) = D.cap y := D.cap_next j y

theorem out_build (z : Z) (w : W) : D.out (D.build (z, w)) = z := by
  simp [DuplexSpec.out]

/-! ## The invariant -/

/-- A branch state is answered with its challenge, or would be programmed with it. -/
def NextOK (s : SimSt Dg St Root n) (x : St) (L : Root × Fin n) : Prop :=
  (s.answer x = none → efflab D s x = some L) ∧ ∀ e ∈ s.log, e.1 = x → e.2.2 = some L

/-- **The simulator's invariant** for the label's hash `iv` and the table `g`. -/
structure Inv (g : Tab Root Z n) (iv : Dg) (s : SimSt Dg St Root n) : Prop where
  x0 : s.x0 = some (D.init iv)
  nodup : (s.log.map (·.1)).Nodup
  ivEq : s.iv = some iv
  out : ∀ e ∈ s.log, ∀ r j, e.2.2 = some (r, j) → D.out e.2.1 = g.at r j
  place : ∀ e ∈ s.log, ∀ r (j : Fin n), e.2.2 = some (r, j) →
    (j.val = 0 → e.1 = D.first r iv) ∧
    (j.val ≠ 0 → ∃ e' ∈ s.log, e'.2.2 = some (r, ⟨0, D.n_pos⟩) ∧ e.1 = D.next j e'.2.1)
  lab : ∀ p ∈ s.lab, p.2.2.val ≠ 0 ∧
    ∃ e' ∈ s.log, e'.2.2 = some (p.2.1, ⟨0, D.n_pos⟩) ∧ p.1 = D.next p.2.2 e'.2.1
  nxt : ∀ e ∈ s.log, ∀ r, e.2.2 = some (r, ⟨0, D.n_pos⟩) → ∀ j : Fin n, j.val ≠ 0 →
    NextOK D s (D.next j e.2.1) (r, j)
  fst : ∀ r, NextOK D s (D.first r iv) (r, ⟨0, D.n_pos⟩)
  uniq : ∀ e ∈ s.log, ∀ e' ∈ s.log, e.2.2 = e'.2.2 → e.2.2 ≠ none → e = e'

variable {D}

theorem answer_ne_none_of_mem {s : SimSt Dg St Root n} {e} (he : e ∈ s.log) :
    s.answer e.1 ≠ none := fun h ↦ answer_eq_none h e he rfl

theorem mem_used_iff {s : SimSt Dg St Root n} {L : Root × Fin n} :
    L ∈ s.used ↔ ∃ e ∈ s.log, e.2.2 = some L := by
  simp [SimSt.used, List.mem_filterMap]

/-- A used first challenge: its state is answered. -/
theorem Inv.used_zero {g : Tab Root Z n} {iv : Dg} {s : SimSt Dg St Root n} (hI : Inv D g iv s)
    (r : Root) (hu : (r, ⟨0, D.n_pos⟩) ∈ s.used) :
    s.answer (D.first r iv) ≠ none := by
  obtain ⟨e, he, hl⟩ := mem_used_iff.mp hu
  have hx := (hI.place e he r _ hl).1 rfl
  rw [← hx]
  exact answer_ne_none_of_mem he

/-- A used branch challenge: its state is answered. -/
theorem Inv.used_branch {g : Tab Root Z n} {iv : Dg} {s : SimSt Dg St Root n} (hI : Inv D g iv s)
    {e} (he : e ∈ s.log) {r : Root} (hl : e.2.2 = some (r, ⟨0, D.n_pos⟩)) {j : Fin n}
    (hj : j.val ≠ 0) (hu : (r, j) ∈ s.used) : s.answer (D.next j e.2.1) ≠ none := by
  obtain ⟨e'', he'', hl''⟩ := mem_used_iff.mp hu
  obtain ⟨e', he', hl', hx⟩ := (hI.place e'' he'' r _ hl'').2 hj
  have : e' = e := hI.uniq e' he' e he (by rw [hl', hl]) (by simp [hl'])
  subst this
  rw [← hx]
  exact answer_ne_none_of_mem he''

theorem progLbl_of {s : SimSt Dg St Root n} {x : St} {L : Root × Fin n}
    (h : efflab D s x = some L) (hu : L ∉ s.used) : progLbl D s x = some L := by
  simp [progLbl, h, hu]

/-! ## A fresh step without collision keeps the invariant -/

section Step

variable {g : Tab Root Z n} {iv : Dg} {s : SimSt Dg St Root n} {x y : St}

theorem not_mem_insert_forb (hcol : D.cap y ∉ insert (D.cap x) (forb D s)) :
    D.cap y ≠ D.cap x ∧ (∀ e ∈ s.log, D.cap y ≠ D.cap e.1) ∧
      (∀ e ∈ s.log, D.cap y ≠ D.cap e.2.1) ∧ (∀ x0, s.x0 = some x0 → D.cap y ≠ D.cap x0) := by
  simp only [Finset.mem_insert, not_or] at hcol
  refine ⟨hcol.1, fun e he h ↦ hcol.2 (h ▸ mem_forb_of_key D he),
    fun e he h ↦ hcol.2 (h ▸ mem_forb_of_val D he), fun x0 h0 h ↦ hcol.2 (h ▸ mem_forb_of_x0 D h0)⟩

/-- A state whose capacity is that of the fresh answer is not answered. -/
theorem answer_of_cap (hk : ∀ e ∈ s.log, D.cap y ≠ D.cap e.1) {x' : St}
    (hx' : D.cap x' = D.cap y) : s.answer x' = none := by
  simp only [SimSt.answer, Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq]
  intro e he hex
  exact hk e he (hex ▸ hx').symm

/-- A state whose capacity is that of the fresh answer has no registered challenge. -/
theorem labOf_of_cap (hI : Inv D g iv s) (hv : ∀ e ∈ s.log, D.cap y ≠ D.cap e.2.1) {x' : St}
    (hx' : D.cap x' = D.cap y) : s.labOf x' = none := by
  simp only [SimSt.labOf, Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq]
  intro p hp hpx
  obtain ⟨-, e', he', -, hpe⟩ := hI.lab p hp
  apply hv e' he'
  rw [← hx', ← hpx, hpe, cap_next']

theorem efflab_record_of (P : Option (Root × Fin n)) {x' : St}
    (hl : (s.record D x y P).labOf x' = s.labOf x') :
    efflab D (s.record D x y P) x' = efflab D s x' := by
  simp only [efflab, iv_record, hl]

theorem efflab_spec {r : Root} {j : Fin n} (h : efflab D s x = some (r, j)) :
    (∃ d, s.iv = some d ∧ D.first r d = x ∧ j.val = 0) ∨
      (∃ p ∈ s.lab, p.1 = x ∧ p.2 = (r, j)) := by
  unfold efflab at h
  have hlab : s.labOf x = some (r, j) → ∃ p ∈ s.lab, p.1 = x ∧ p.2 = (r, j) := fun hl ↦ by
    simp only [SimSt.labOf, Option.map_eq_some_iff] at hl
    obtain ⟨p, hp, hpe⟩ := hl
    exact ⟨p, List.mem_of_find?_eq_some hp, by simpa using List.find?_some hp, hpe⟩
  rcases hiv : s.iv with _ | d
  · simp only [hiv] at h
    exact Or.inr (hlab h)
  · simp only [hiv] at h
    rcases hd : D.dec d x with _ | r'
    · simp only [hd] at h
      exact Or.inr (hlab h)
    · simp only [hd, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨d, rfl, (D.dec_iff d x r').mp hd, rfl⟩

theorem progLbl_not_used {L : Root × Fin n} (h : progLbl D s x = some L) : L ∉ s.used := by
  unfold progLbl at h
  split at h
  · split_ifs at h with hu
    cases h; exact hu
  · cases h

theorem progLbl_efflab {L : Root × Fin n} (h : progLbl D s x = some L) :
    efflab D s x = some L := by
  unfold progLbl at h
  split at h
  · next L' hL' => split_ifs at h; cases h; exact hL'
  · cases h

/-- The branch states stay described after a step elsewhere. -/
theorem nextOK_record (hx : s.answer x = none) {x' : St} {L : Root × Fin n}
    (hok : NextOK D s x' L) (hne : ∀ k : Fin n, x' ≠ D.next k y)
    (hprog : x' = x → progLbl D s x = some L) :
    NextOK D (s.record D x y (progLbl D s x)) x' L := by
  by_cases hxx : x' = x
  · subst hxx
    refine ⟨fun h ↦ by simp [answer_record] at h, fun e he hk ↦ ?_⟩
    rcases List.mem_cons.mp he with rfl | he
    · exact hprog rfl
    · exact absurd hk (answer_eq_none hx e he)
  · refine ⟨fun ha ↦ ?_, fun e he hk ↦ ?_⟩
    · rw [answer_record, ite_neg' hxx] at ha
      rw [efflab_record_of _ (labOf_record_ne D s x y _ hne)]
      exact hok.1 ha
    · rcases List.mem_cons.mp he with rfl | he
      · exact absurd hk.symm hxx
      · exact hok.2 e he hk

/-- **A step without collision** keeps the invariant. -/
theorem inv_record (hI : Inv D g iv s) (hx : s.answer x = none)
    (hy : ∀ r j, progLbl D s x = some (r, j) → D.out y = g.at r j)
    (hcol : D.cap y ∉ insert (D.cap x) (forb D s)) :
    Inv D g iv (s.record D x y (progLbl D s x)) := by
  obtain ⟨hcx, hck, hcv, hc0⟩ := not_mem_insert_forb hcol
  have hsx0 := hI.x0
  -- a state with another capacity than `y`'s is no branch of `y`
  have hbr : ∀ {x' : St}, D.cap x' ≠ D.cap y → ∀ k : Fin n, x' ≠ D.next k y :=
    fun h k h' ↦ h (by rw [h', cap_next'])
  constructor
  · exact hsx0
  · simp only [log_record, List.map_cons, List.nodup_cons]
    exact ⟨fun h ↦ by
      obtain ⟨e, he, hex⟩ := List.mem_map.mp h
      exact answer_eq_none hx e he hex, hI.nodup⟩
  · exact hI.ivEq
  · intro e he r j hl
    rcases List.mem_cons.mp he with rfl | he
    · exact hy r j hl
    · exact hI.out e he r j hl
  · intro e he r j hl
    rcases List.mem_cons.mp he with rfl | he
    · -- the new entry: its challenge came from `efflab`
      simp only at hl
      have hL : efflab D s x = some (r, j) := progLbl_efflab hl
      rcases efflab_spec hL with ⟨d, hd, hfd, hj⟩ | ⟨p, hp, hpx, hpl⟩
      · rw [hI.ivEq] at hd
        cases hd
        exact ⟨fun _ ↦ hfd.symm, fun hj' ↦ absurd hj hj'⟩
      · obtain ⟨hp0, e', he', hl', hx'⟩ := hI.lab p hp
        rw [hpl] at hp0 hl' hx'
        refine ⟨fun hj ↦ absurd hj hp0, fun _ ↦ ?_⟩
        exact ⟨e', List.mem_cons_of_mem _ he', hl', hpx ▸ hx'⟩
    · obtain ⟨h1, h2⟩ := hI.place e he r j hl
      exact ⟨h1, fun hj ↦ by
        obtain ⟨e', he', hl', hx'⟩ := h2 hj
        exact ⟨e', List.mem_cons_of_mem _ he', hl', hx'⟩⟩
  · intro p hp
    have hold : p ∈ s.lab → p.2.2.val ≠ 0 ∧ ∃ e' ∈ (s.record D x y (progLbl D s x)).log,
        e'.2.2 = some (p.2.1, ⟨0, D.n_pos⟩) ∧ p.1 = D.next p.2.2 e'.2.1 := fun hp ↦ by
      obtain ⟨h0, e', he', hl', hx'⟩ := hI.lab p hp
      exact ⟨h0, e', List.mem_cons_of_mem _ he', hl', hx'⟩
    rcases lab_record D s x y (progLbl D s x) with h | ⟨r0, j0, hP, hj0, h⟩
    · rw [h] at hp
      exact hold hp
    · rw [h] at hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨k, hk, rfl⟩ := (mem_children D).mp hp
        have hj0' : j0 = ⟨0, D.n_pos⟩ := Fin.ext hj0
        refine ⟨hk, (x, y, progLbl D s x), List.mem_cons_self, ?_, rfl⟩
        rw [hP, hj0']
      · exact hold hp
  · intro e he r hl j hj
    rcases List.mem_cons.mp he with rfl | he
    · simp only at hl ⊢
      have hny : D.next j y ≠ x := fun h' ↦ hcx (by rw [← cap_next' D j y, h'])
      have hans : s.answer (D.next j y) = none := answer_of_cap hck (cap_next' D j y)
      have hans' : (s.record D x y (progLbl D s x)).answer (D.next j y) = none := by
        rw [answer_record, ite_neg' hny, hans]
      refine ⟨fun _ ↦ ?_, fun e2 he2 hk ↦ absurd hans'
        (by rw [← hk]; exact answer_ne_none_of_mem he2)⟩
      have hd : D.dec iv (D.next j y) = none := by
        rcases hdd : D.dec iv (D.next j y) with _ | r'
        · rfl
        · have := (D.dec_iff _ _ _).mp hdd
          exact absurd (by rw [← cap_next' D j y, ← this, cap_first']) (hc0 _ hsx0)
      unfold efflab
      rw [iv_record, hI.ivEq]
      simp only [hd]
      rw [hl, labOf_record_branch D s x y r _ j rfl hj]
    · have hok := hI.nxt e he r hl j hj
      have hus : (r, j) ∈ s.used → s.answer (D.next j e.2.1) ≠ none := hI.used_branch he hl hj
      exact nextOK_record hx hok
        (hbr (fun h' ↦ hcv e he (by rw [← h', cap_next'])))
        (fun hxx ↦ by
          subst hxx
          exact progLbl_of (hok.1 hx) (fun hu ↦ hus hu hx))
  · intro r
    exact nextOK_record hx (hI.fst r)
      (hbr (fun h' ↦ hc0 _ hsx0 (by rw [← h', cap_first'])))
      (fun hxx ↦ by
        subst hxx
        exact progLbl_of ((hI.fst r).1 hx) (fun hu ↦ hI.used_zero r hu hx))
  · intro e he e' he' hll hn
    rcases List.mem_cons.mp he with rfl | he <;> rcases List.mem_cons.mp he' with rfl | he'
    · rfl
    · exfalso
      obtain ⟨L, hL⟩ := Option.ne_none_iff_exists'.mp hn
      exact progLbl_not_used (hL ▸ rfl : progLbl D s x = some L)
        (mem_used_iff.mpr ⟨e', he', hll ▸ hL⟩)
    · exfalso
      obtain ⟨L, hL⟩ := Option.ne_none_iff_exists'.mp hn
      exact progLbl_not_used (hll.symm.trans hL : progLbl D s x = some L)
        (mem_used_iff.mpr ⟨e, he, hL⟩)
    · exact hI.uniq e he e' he' hll hn

end Step

end Common.SeedDuplex

namespace Common.SeedDuplex

variable {Msg Dg St Root Z W Cp : Type} {n : ℕ}
  [DecidableEq Msg] [DecidableEq St] [DecidableEq Root] [DecidableEq Cp]
  [SampleableType Dg] [SampleableType St] [SampleableType Z] [SampleableType W]
  [Fintype St] [Fintype Z] [Fintype W] [Fintype Root] [Nonempty Z]
  {D : DuplexSpec Msg Dg St Root Z W Cp n}

/-! ## The steps of the table world -/

/-- The table world's state is good: the invariant, a cache without challenges, the label's
hash cached. -/
structure Good (D : DuplexSpec Msg Dg St Root Z W Cp n) (g : Tab Root Z n) (iv : Dg)
    (sc : SimSt Dg St Root n × (GSpec Msg Dg Root Z n).QueryCache) : Prop where
  inv : Inv D g iv sc.1
  gfree : GFree sc.2
  label : sc.2 (.inl D.label) = some iv

theorem bad_record (s : SimSt Dg St Root n) (x y : St) (lbl : Option (Root × Fin n)) :
    (s.record D x y lbl).bad = (s.bad || decide (D.cap y ∈ insert (D.cap x) (forb D s))) := rfl

theorem tab_bad_mono (g : Tab Root Z n) (t : (Rom2 Msg Dg St).Domain) (s : SimSt Dg St Root n)
    (c : (GSpec Msg Dg Root Z n).QueryCache) (hc : GFree c) (hs : s.bad = true) {z}
    (hz : z ∈ support ((tabImpl D g t).run (s, c))) : z.2.1.bad = true := by
  rcases t with k | m | x
  · rw [tab_coin D g k s c hz]; exact hs
  · obtain ⟨-, h⟩ := tab_H D g m s c hz
    rw [h]; split_ifs <;> exact hs
  · rcases tab_F D g x s c hc hz with ⟨-, h⟩ | ⟨-, h, -⟩
    · rw [h]; exact hs
    · rw [h]; simp [bad_record, hs]

theorem record_x0_self (s : SimSt Dg St Root n) {x0 : St} {d : Dg} (h : s.x0 = some x0)
    (h' : s.iv = some d) : ({ s with x0 := some x0, iv := some d } : SimSt Dg St Root n) = s := by
  cases s; simp_all

/-- **A step without collision keeps the table world good.** -/
theorem good_step (g : Tab Root Z n) (iv : Dg) (t : (Rom2 Msg Dg St).Domain)
    (sc : SimSt Dg St Root n × (GSpec Msg Dg Root Z n).QueryCache) (hG : Good D g iv sc)
    {z} (hz : z ∈ support ((tabImpl D g t).run sc)) (hb : z.2.1.bad = false) :
    Good D g iv z.2 := by
  obtain ⟨s, c⟩ := sc
  rcases t with k | m | x
  · rw [tab_coin D g k s c hz]; exact hG
  · obtain ⟨hv, h⟩ := tab_H D g m s c hz
    have hc : (z.1, z.2.2) ∈ support (roStep (hs := GSpec Msg Dg Root Z n) (.inl m) c) := hv
    have hz2 : z.2.2 = c ∨ ∃ u, z.2.2 = c.cacheQuery (.inl m) u ∧ c (.inl m) = none := by
      rcases hcm : c (.inl m) with _ | u
      · rw [roStep_of_none hcm] at hc
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hc
        obtain ⟨u, -, hu⟩ := hc
        exact Or.inr ⟨u, (Prod.mk.inj hu).2, rfl⟩
      · rw [roStep_of_some hcm] at hc
        simp only [support_pure, Set.mem_singleton_iff] at hc
        exact Or.inl (Prod.mk.inj hc).2
    have hs : z.2.1 = s := by
      rw [h]
      split_ifs with hm
      · subst hm
        rw [roStep_of_some hG.label] at hc
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hc
        rw [hc.1]
        exact record_x0_self s hG.inv.x0 hG.inv.ivEq
      · rfl
    refine ⟨hs ▸ hG.inv, ?_, ?_⟩
    · rcases hz2 with h2 | ⟨u, h2, -⟩
      · rw [h2]; exact hG.gfree
      · intro d; rw [h2, QueryCache.cacheQuery_of_ne _ _ (by simp)]; exact hG.gfree d
    · rcases hz2 with h2 | ⟨u, h2, hn⟩
      · rw [h2]; exact hG.label
      · rw [h2]
        by_cases hm : m = D.label
        · subst hm; rw [hG.label] at hn; cases hn
        · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa [eq_comm] using hm)]; exact hG.label
  · rcases tab_F D g x s c hG.gfree hz with ⟨-, h⟩ | ⟨hx, h, hy⟩
    · rw [h]; exact hG
    · rw [h] at hb ⊢
      have hcol : D.cap z.1 ∉ insert (D.cap x) (forb D s) := by
        intro hm
        simp [bad_record, hm] at hb
      refine ⟨inv_record hG.inv hx (fun r j hl ↦ ?_) hcol, hG.gfree, hG.label⟩
      obtain ⟨w, hw⟩ := hy r j hl
      rw [hw, out_build]

end Common.SeedDuplex
