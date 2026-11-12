/-
  LeanVM.Guest.B1.Selectors.SelectorTablesComplete

  `selector_tables`, completely: on the honest valuation (the body evaluated on the point's
  words, its buffer at any base), every statement holds on a memory holding the point and the
  buffer's words, and the buffer holds the opening point's tables.
-/

module

public import LeanVM.Guest.B1.Selectors.SelectorTables
public import LeanVM.Guest.B1.Selectors.LayoutBasic

/-!
# `selector_tables`, completely (TRIAGE G #69)

The point and its complements are the runs `(ept, p)`, `(ept1, p1)` (`stLin`); the buffer's base
is `ese` (`512` words). The honest valuation `stVal` is the body evaluated on `layRd` of the point
(`Fwd.ev`, the allocation answered by the base). The buffer's words (`stOwn`): at offset
`o = 64j + 16w + u`, `u` a multiple of `2^(3 - w)` (`stStored`), the value stored there
(`stD o`, level `w`'s entry `u / 2^(3 - w)` of nibble `j`); the words between the strided entries
are never written, `0`.

`st_holds`: on every memory holding `stOwn ++ stLin`, the relation holds with the buffer's pointer
as return; the buffer then holds the opening point's tables (by soundness).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The point's runs. -/
def stLin (ept ept1 : ℕ) (p p1 : List E) : TLay := [(ept, p), (ept1, p1)]

/-- The allocation's answer: the eq buffer at `ese`. -/
def stW (ese : ℕ) : ℕ → E := fun _ => ofK (addressOfIndex ese)

/-- **The honest valuation.** -/
noncomputable def stVal (ept ept1 ese : ℕ) (p p1 : List E) : Val :=
  B1.Val.ofArgs (ev (layRd (stLin ept ept1 p p1)) (stW ese)
    [ofK (addressOfIndex ept), ofK (addressOfIndex ept1)] stPre)

/-- The level of the buffer's offset `o`. -/
def stLvl (o : ℕ) : ℕ := o % 64 / 16

/-- The value stored at the buffer's offset `o`: nibble `o / 64`, level `stLvl o`, entry
`o % 16 / 2^(3 - stLvl o)`. -/
def stD (o : ℕ) : ℕ := stV (o / 64) (stLvl o) (o % 16 / 2 ^ (3 - stLvl o))

/-- The buffer's offset `o` is written: its entry a multiple of its level's stride. -/
def stStored (o : ℕ) : Bool := o % 16 % 2 ^ (3 - stLvl o) == 0

/-- The eq buffer's words: the stored values, `0` between them. -/
def stEqWords (σ : Val) : List E :=
  (List.range 512).map fun o => if stStored o then σ (.n (stD o)) else 0

/-- The buffer's run. -/
noncomputable def stOwn (ept ept1 ese : ℕ) (p p1 : List E) : TLay :=
  [(ese, stEqWords (stVal ept ept1 ese p p1))]

theorem st_chk : chk 2 stPre = some 292 := by decide +kernel

/-- What a statement of the body is: a pure atom, a hint, a load of the point, or a store. -/
def stKind : Stmt → Bool
  | .atom (.hint _) => true
  | .atom (.load (.n _) (.n 0) o) | .atom (.load (.n _) (.n 1) o) => decide (o < 32)
  | .atom (.load (.n d) (.n 2) o) => decide (o < 512) && decide (d = stD o) && stStored o
  | .atom a => pureB a
  | _ => false

theorem st_kinds : stPre.all stKind = true := by decide +kernel

/-- The stores of the body are the buffer's loads. -/
def stStoreOk : Atom → Bool
  | .load (.n _) (.n 2) _ => true
  | _ => false

theorem st_stores : (storesOf 2 stPre).all stStoreOk = true := by decide +kernel

theorem st_alloc_mem : Stmt.atom (.hint (.alloc (.n 2) 512)) ∈ stPre := by
  unfold stPre; simp

/-- The kinds of the body's statements. -/
theorem stKind_cases {s : Stmt} (h : stKind s = true) :
    (∃ hn, s = .atom (.hint hn)) ∨
    (∃ d o, (s = .atom (.load (.n d) (.n 0) o) ∨ s = .atom (.load (.n d) (.n 1) o)) ∧ o < 32) ∨
    (∃ o, s = .atom (.load (.n (stD o)) (.n 2) o) ∧ o < 512 ∧ stStored o = true) ∨
    (∃ a, s = .atom a ∧ pureB a = true) := by
  unfold stKind at h
  split at h
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr (Or.inl ⟨_, _, Or.inl rfl, by simpa using h⟩)
  · exact Or.inr (Or.inl ⟨_, _, Or.inr rfl, by simpa using h⟩)
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, rfl⟩, h2⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨_, rfl, h1, h2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨_, rfl, h⟩))
  · exact absurd h (by simp)

theorem pure_holds_rd {a : Atom} (ha : pureB a = true) {rd rd' : Reader} {σ : Val}
    (h : a.Holds rd σ) : a.Holds rd' σ := by
  cases a <;> simp_all [pureB, Atom.Holds]

theorem st_rdAt {rd : Reader} {L : TLay} (hm : MemLay rd L) {q : ℕ × List E} (hq : q ∈ L)
    {o : ℕ} (ho : o < q.2.length) :
    rdAt (layRd L) (ofK (addressOfIndex q.1)) o = q.2.getD o 0 ∧
      LoadHolds rd (ofK (addressOfIndex q.1)) o (q.2.getD o 0) := by
  have hr := memLay_read hm hq ho
  refine ⟨?_, tb_isInK_ofK _, by rw [tb_addr_ofK]; exact hr⟩
  rw [rdAt, tb_addr_ofK, layRd_agree hm ⟨q, hq, o, ho, rfl⟩, hr]
  rfl

theorem stVal_param (ept ept1 ese : ℕ) (p p1 : List E) :
    stVal ept ept1 ese p p1 (.n 0) = ofK (addressOfIndex ept) ∧
      stVal ept ept1 ese p p1 (.n 1) = ofK (addressOfIndex ept1) :=
  ⟨ev_params _ _ (l := [ofK (addressOfIndex ept), ofK (addressOfIndex ept1)]) st_chk (by norm_num),
    ev_params _ _ (l := [ofK (addressOfIndex ept), ofK (addressOfIndex ept1)]) st_chk (by norm_num)⟩

/-- The buffer's pointer, allocated and returned. -/
theorem stVal_bufs (ept ept1 ese : ℕ) (p p1 : List E) :
    stVal ept ept1 ese p p1 (.n 2) = ofK (addressOfIndex ese) ∧
      stVal ept ept1 ese p p1 (.n 291) = ofK (addressOfIndex ese) := by
  have hg : ∀ s ∈ stPre, GoodS (layRd (stLin ept ept1 p p1)) (storesOf 2 stPre) (stW ese)
      (stVal ept ept1 ese p p1) s :=
    (ev_spec (layRd (stLin ept ept1 p p1)) (stW ese) stPre
      [ofK (addressOfIndex ept), ofK (addressOfIndex ept1)] st_chk).2.2
  have e2 : stVal ept ept1 ese p p1 (.n 2) = ofK (addressOfIndex ese) := by
    simpa [GoodS, Good, stW] using hg _ st_alloc_mem
  have c1 := hg _ (show Stmt.atom (.copy (.n 291) (.n 2)) ∈ stPre by simp [stPre])
  simp only [GoodS, Good] at c1
  exact ⟨e2, by rw [c1, e2]⟩

set_option maxRecDepth 10000 in
/-- **Every statement holds** on the honest valuation, on every memory holding the buffer and the
point. -/
theorem st_sholds (ept ept1 ese : ℕ) (p p1 : List E) (hl : p.length = 32)
    (hl1 : p1.length = 32) (rd : Reader)
    (hm : MemLay rd (stOwn ept ept1 ese p p1 ++ stLin ept ept1 p p1)) :
    ∀ s ∈ stPre, SHolds (coreProgram.Rel rd) rd (stVal ept ept1 ese p p1) s := by
  have hg : ∀ s ∈ stPre, GoodS (layRd (stLin ept ept1 p p1)) (storesOf 2 stPre) (stW ese)
      (stVal ept ept1 ese p p1) s :=
    (ev_spec (layRd (stLin ept ept1 p p1)) (stW ese) stPre
      [ofK (addressOfIndex ept), ofK (addressOfIndex ept1)] st_chk).2.2
  obtain ⟨e0, e1⟩ := stVal_param ept ept1 ese p p1
  obtain ⟨e2, -⟩ := stVal_bufs ept ept1 ese p p1
  set σ := stVal ept ept1 ese p p1 with hσ
  obtain ⟨hmo, hmi⟩ := memLay_append.mp hm
  have hS : ∀ a ∈ storesOf 2 stPre, stStoreOk a = true := fun a ha =>
    List.all_eq_true.mp st_stores a ha
  intro s hs
  have hgs := hg s hs
  rcases stKind_cases (List.all_eq_true.mp st_kinds s hs) with
    ⟨hn, rfl⟩ | ⟨d, o, hld, ho⟩ | ⟨o, rfl, ho, hst⟩ | ⟨a, rfl, ha⟩
  · trivial
  · rcases hld with rfl | rfl
    · simp only [GoodS, Good] at hgs
      rcases hgs with hgs | hgs
      · exact absurd (hS _ hgs) (by simp [stStoreOk])
      · have := st_rdAt hmi (q := (ept, p)) (by simp [stLin]) (o := o) (by simp [hl, ho])
        show LoadHolds rd (σ (.n 0)) o (σ (.n d))
        rw [hgs, e0, this.1]; exact this.2
    · simp only [GoodS, Good] at hgs
      rcases hgs with hgs | hgs
      · exact absurd (hS _ hgs) (by simp [stStoreOk])
      · have := st_rdAt hmi (q := (ept1, p1)) (by simp [stLin]) (o := o) (by simp [hl1, ho])
        show LoadHolds rd (σ (.n 1)) o (σ (.n d))
        rw [hgs, e1, this.1]; exact this.2
  · show LoadHolds rd (σ (.n 2)) o (σ (.n (stD o)))
    have h := hmo (ese, stEqWords σ) (by unfold stOwn; exact List.mem_cons_self) o
      (by simp [stEqWords, ho])
    rw [e2]
    simpa [stEqWords, hst] using h
  · exact pure_holds_rd ha (holds_of_pure ha (by simpa only [GoodS] using hgs))

set_option maxRecDepth 10000 in
/-- **The relation holds** on a memory holding the buffer and the point, the buffer's pointer
returned. -/
theorem st_holds (ept ept1 ese : ℕ) (p p1 : List E) (hl : p.length = 32)
    (hl1 : p1.length = 32) (rd : Reader)
    (hm : MemLay rd (stOwn ept ept1 ese p p1 ++ stLin ept ept1 p p1)) :
    coreProgram.Rel rd "selector_tables" [ofK (addressOfIndex ept), ofK (addressOfIndex ept1)]
      [ofK (addressOfIndex ese)] := by
  obtain ⟨fn, hf, hp, hb⟩ := stFound
  obtain ⟨e0, e1⟩ := stVal_param ept ept1 ese p p1
  obtain ⟨-, e291⟩ := stVal_bufs ept ept1 ese p p1
  have hat := st_sholds ept ept1 ese p p1 hl hl1 rd hm
  refine (tb_rel_iff_sem hf _ _).mpr ⟨stVal ept ept1 ese p p1, by rw [hp]; simp [e0, e1], ?_⟩
  rw [hb]
  refine holdsList_straight stPre _ _ _ hat ?_
  simp [e291]

end
end LeanVM.Guest.B1.Tables
