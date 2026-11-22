module

public import LeanVM.Prover.ExecuteCompleteLog

/-!
# The executor's memory agrees with a reference

`Agree m M`: every written cell of `m` holds the reference's value `M`, the cells of a link class
have one reference value and are recorded as the class's members, every link's two cells are in one
class, and `used` stays below `maxCells`. A `put` of `M`'s value below `maxCells` succeeds and keeps
it (`Agree.put`), as do `putRun` (`Agree.putRun`) and the link of two unwritten cells with one
reference value (`Agree.link`), which merges or joins classes.
-/

namespace LeanVM.Prover.Exec

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

open scoped Classical

/-- Cells `x` and `y` are in one link class. -/
def SameCls (m : Mem) (x y : ℕ) : Prop := ∃ k, m.cellOf x = .cls k ∧ m.cellOf y = .cls k

/-- Class `k`'s recorded members. -/
def Mem.mems (m : Mem) (k : ℕ) : Array ℕ := m.members[k]?.getD #[]

/-- The memory agrees with `M` on written cells and within classes, records its classes and stays
below `maxCells`. -/
structure Core (m : Mem) (M : ℕ → E) : Prop where
  wf : m.WF
  get : ∀ c v, m.get c = some v → M c = v
  cls : ∀ c d k, m.cellOf c = .cls k → m.cellOf d = .cls k → M c = M d
  mem : ∀ c k, m.cellOf c = .cls k → c ∈ m.mems k
  size : m.members.size = m.vals.size
  used : m.used ≤ maxCells

/-- `Core`, and every link's cells have one reference value and are in one class. -/
structure Agree (m : Mem) (M : ℕ → E) : Prop extends Core m M where
  links : ∀ p ∈ m.links, M p.1 = M p.2 ∧ SameCls m p.1 p.2

theorem Agree.ensure {m : Mem} {M : ℕ → E} (h : Agree m M) {c : ℕ} (hc : c < maxCells) :
    Agree (m.ensure c) M :=
  ⟨⟨h.wf.ensure c, fun c v hv ↦ h.get c v hv, fun c d k ↦ h.cls c d k, fun c k ↦ h.mem c k,
    h.size, by simp only [Mem.ensure_used]; have := h.used; omega⟩, fun p hp ↦ h.links p hp⟩

theorem Agree.foldl_ensure {M : ℕ → E} :
    ∀ (l : List ℕ) (m : Mem), Agree m M → (∀ c ∈ l, c < maxCells) → Agree (l.foldl Mem.ensure m) M
  | [], _, h, _ => h
  | c :: l, _, h, hl => Agree.foldl_ensure l _ (h.ensure (hl c (List.mem_cons_self ..)))
    fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)

theorem Mem.get_none_of_free {m : Mem} {c : ℕ} (h : m.cellOf c = .free) : m.get c = none := by
  rw [Mem.get_eq, h]; rfl

theorem Mem.get_cls {m : Mem} {c k : ℕ} (h : m.cellOf c = .cls k) :
    m.get c = (m.vals[k]?).join := by
  rw [Mem.get_eq, h]; rfl

/-- `get` agrees across a class. -/
theorem SameCls.get_eq {m : Mem} {x y : ℕ} (h : SameCls m x y) : m.get x = m.get y := by
  obtain ⟨k, hx, hy⟩ := h
  rw [Mem.get_cls hx, Mem.get_cls hy]

/-! ## `put` -/

theorem Agree.setVal {m : Mem} {M : ℕ → E} (h : Agree m M) {c k : ℕ} {v : E}
    (hck : m.cellOf c = .cls k) (hv : M c = v) :
    Agree ⟨m.cells, m.vals.set! k (some v), m.members, m.links, m.used⟩ M := by
  have hcm : ∀ d, (⟨m.cells, m.vals.set! k (some v), m.members, m.links, m.used⟩ : Mem).cellOf d =
      m.cellOf d := fun _ ↦ rfl
  refine ⟨⟨⟨fun d k' hd ↦ ?_, fun d hd ↦ h.wf.used d hd⟩, fun d u hd ↦ ?_,
    fun d d' k' ↦ h.cls d d' k',
    fun d k' ↦ h.mem d k', by simpa using h.size, h.used⟩, fun p hp ↦ h.links p hp⟩
  · simpa using h.wf.cls d k' hd
  · rw [Mem.get_eq, hcm] at hd
    have hks := h.wf.cls c k hck
    generalize hx : m.cellOf d = x at hd
    cases x with
    | free => cases hd
    | lit w => exact h.get d u (by rw [Mem.get_eq, hx]; exact hd)
    | cls k' =>
      simp only [cval, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hd
      split_ifs at hd with hkk
      · subst hkk
        simp only [Option.join_some, Option.some.injEq] at hd
        rw [← hd, ← hv]
        exact h.cls d c k hx hck
      · exact h.get d u (by rw [Mem.get_eq, hx]; exact hd)

@[simp] theorem Mem.setCell_members (m : Mem) (c : ℕ) (x : Cell) :
    (m.setCell c x).members = m.members := by
  cases m; rfl

theorem Agree.setLit {m : Mem} {M : ℕ → E} (h : Agree m M) {c : ℕ} {v : E}
    (hc : m.cellOf c = .free) (hv : M c = v) (hu : c < m.used) :
    Agree (m.setCell c (.lit v)) M := by
  have hne : ∀ d k, m.cellOf d = .cls k → d ≠ c := fun d k hd hdc ↦ by
    subst hdc; rw [hc] at hd; cases hd
  have hcls : ∀ d k, (m.setCell c (.lit v)).cellOf d = .cls k → m.cellOf d = .cls k ∧ d ≠ c :=
    fun d k hd ↦ by
      rw [Mem.cellOf_setCell] at hd
      by_cases hdc : d = c
      · rw [ite_eq_left hdc] at hd; exact Cell.noConfusion hd
      · rw [ite_eq_right hdc] at hd; exact ⟨hd, hdc⟩
  refine ⟨⟨h.wf.setCell (fun _ h ↦ Cell.noConfusion h) hu, fun d u hd ↦ ?_, fun d d' k hd hd' ↦ ?_,
    fun d k hd ↦ ?_, by simpa using h.size, by simpa using h.used⟩, fun p hp ↦ ?_⟩
  · rw [Mem.get_eq, Mem.cellOf_setCell, Mem.setCell_vals] at hd
    split_ifs at hd with hdc
    · subst hdc; simp only [cval, Option.some.injEq] at hd; rw [hv, hd]
    · exact h.get d u (by rw [Mem.get_eq]; exact hd)
  · exact h.cls d d' k (hcls d k hd).1 (hcls d' k hd').1
  · unfold Mem.mems; rw [Mem.setCell_members]; exact h.mem d k (hcls d k hd).1
  · rw [Mem.setCell_links] at hp
    obtain ⟨hM, k, h1, h2⟩ := h.links p hp
    refine ⟨hM, k, ?_, ?_⟩
    · rw [Mem.cellOf_setCell, ite_eq_right (hne _ _ h1)]; exact h1
    · rw [Mem.cellOf_setCell, ite_eq_right (hne _ _ h2)]; exact h2

/-- A `put` of the reference's value succeeds and keeps the agreement. -/
theorem Agree.put {m : Mem} {M : ℕ → E} (h : Agree m M) {c : ℕ} {v : E} (hv : M c = v)
    (hc : c < maxCells) : ∃ m', m.put c v = .ok m' ∧ Agree m' M ∧ m ≤ m' ∧ m'.get c = some v := by
  suffices ∃ m', m.put c v = .ok m' ∧ Agree m' M by
    obtain ⟨m', e, h'⟩ := this
    obtain ⟨h1, -, h3⟩ := Mem.put_ok h.wf e
    exact ⟨m', e, h', h1, h3⟩
  have h1 := h.ensure hc
  have hcu : c < (m.ensure c).used := by simp
  simp only [Mem.put]
  generalize m.ensure c = m1 at h1 hcu
  obtain ⟨cells, vals, members, links, used⟩ := m1
  dsimp only at hcu ⊢
  split
  · rename_i w hw
    have := h1.get c w (by rw [Mem.get_eq, Mem.cellOf_mk, hw]; rfl)
    rw [← this, hv, ite_eq_left rfl]
    exact ⟨_, rfl, h1⟩
  · rename_i k hk
    have hkc : (⟨cells, vals, members, links, used⟩ : Mem).cellOf c = .cls k := by
      rw [Mem.cellOf_mk, hk]; rfl
    split
    · rename_i w hw'
      have := h1.get c w (by rw [Mem.get_cls hkc]; exact hw')
      rw [← this, hv, ite_eq_left rfl]
      exact ⟨_, rfl, h1⟩
    · exact ⟨_, rfl, h1.setVal hkc hv⟩
  · rename_i hx1 hx2
    have hfree : (⟨cells, vals, members, links, used⟩ : Mem).cellOf c = .free := by
      rw [Mem.cellOf_mk]
      cases h : cells[c]? with
      | none => rfl
      | some x => cases x with
        | free => rfl
        | lit w => exact absurd h (hx1 w)
        | cls k => exact absurd h (hx2 k)
    exact ⟨_, rfl, h1.setLit hfree hv hcu⟩

/-- The run `vs` from `b` lies below `maxCells` and is the reference's there. -/
def RunOk (M : ℕ → E) (b : ℕ) (vs : List E) : Prop :=
  ∀ k (h : k < vs.length), b + k < maxCells ∧ M (b + k) = vs[k]

/-- A run of the reference's values succeeds and keeps the agreement. -/
theorem Agree.putRun {m : Mem} {M : ℕ → E} (h : Agree m M) {b : ℕ} {vs : List E}
    (hr : RunOk M b vs) : ∃ m', putRun b vs m = .ok m' ∧ Agree m' M ∧ m ≤ m' := by
  have key : ∀ (l : List (E × ℕ)) (m : Mem), Agree m M →
      (∀ x ∈ l, b + x.2 < maxCells ∧ M (b + x.2) = x.1) →
      ∃ m', l.foldlM (fun m (v, k) ↦ m.put (b + k) v) m = .ok m' ∧ Agree m' M ∧ m ≤ m' := by
    intro l
    induction l with
    | nil => exact fun m h _ ↦ ⟨m, rfl, h, Mem.le_refl m⟩
    | cons x l ih =>
      intro m h hl
      obtain ⟨v, k⟩ := x
      obtain ⟨hk, hv⟩ := hl _ (List.mem_cons_self ..)
      obtain ⟨m1, e1, h1, le1, -⟩ := h.put hv hk
      obtain ⟨m2, e2, h2, le2⟩ := ih m1 h1 fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)
      exact ⟨m2, by rw [List.foldlM_cons, bind_ok]; exact ⟨m1, e1, e2⟩, h2, Mem.le_trans le1 le2⟩
  refine key _ m h fun x hx ↦ ?_
  have hx' := List.mem_zipIdx_iff_getElem?.mp hx
  obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp hx'
  rw [← he]
  exact hr _ hlt

/-! ## Classes -/

theorem mergeStep_get {i j : ℕ} (hij : i ≠ j) (cs : Array Cell) (x c : ℕ) :
    (mergeStep i j cs x)[c]?.getD .free =
      if c = x ∧ cs[c]?.getD .free = .cls j then .cls i else cs[c]?.getD .free := by
  unfold mergeStep
  split
  · rename_i k hk
    have hlt : x < cs.size := by
      by_contra hn; rw [Array.getElem?_eq_none (by omega)] at hk; cases hk
    split_ifs with hkj h1 h1
    · subst hkj
      rw [h1.1, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, ite_eq_left rfl,
        ite_eq_left hlt]
      rfl
    · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      by_cases hxc : x = c
      · subst hxc; subst hkj; rw [hk] at h1; exact absurd ⟨rfl, rfl⟩ h1
      · rw [ite_eq_right hxc]
    · rw [h1.1, hk] at *; simp only [Option.getD_some, Cell.cls.injEq] at h1; exact absurd h1.2 hkj
    · rfl
  · rename_i hn
    rw [ite_eq_right]
    rintro ⟨rfl, h2⟩
    cases h : cs[c]? with
    | none => rw [h] at h2; cases h2
    | some y => rw [h] at h2; cases h2; exact hn j h

theorem foldl_mergeStep_get {i j : ℕ} (hij : i ≠ j) :
    ∀ (l : List ℕ) (cs : Array Cell) (c : ℕ), (l.foldl (mergeStep i j) cs)[c]?.getD .free =
      if c ∈ l ∧ cs[c]?.getD .free = .cls j then .cls i else cs[c]?.getD .free
  | [], cs, c => by simp
  | x :: l, cs, c => by
    rw [List.foldl_cons, foldl_mergeStep_get hij l, mergeStep_get hij]
    generalize cs[c]?.getD .free = y
    by_cases hx : c = x <;> by_cases hl : c ∈ l <;> by_cases hy : y = .cls j <;>
      simp [hx, hl, hy, hij]

theorem Mem.merge_cellOf {m : Mem} {i j : ℕ} (hij : i ≠ j)
    (hacc : ∀ c, m.cellOf c = .cls j → c ∈ m.mems j) (c : ℕ) :
    (m.merge i j).cellOf c = if m.cellOf c = .cls j then .cls i else m.cellOf c := by
  rw [Mem.merge_eq]
  unfold Mem.cellOf
  dsimp only
  rw [← Array.foldl_toList, foldl_mergeStep_get hij]
  by_cases h : m.cells[c]?.getD .free = .cls j
  · rw [ite_eq_left ⟨Array.mem_toList_iff.mpr (hacc c h), h⟩, ite_eq_left h]
  · rw [ite_eq_right (fun h' ↦ h h'.2), ite_eq_right h]

theorem Mem.merge_members (m : Mem) (i j : ℕ) : (m.merge i j).members =
    (m.members.set! j #[]).modify i (fun a ↦ a ++ m.mems j) := by
  rw [Mem.merge_eq]; rfl

theorem Mem.merge_mems_of_ne {m : Mem} {i j k c : ℕ} (hk : k ≠ j) (hc : c ∈ m.mems k) :
    c ∈ (m.merge i j).mems k := by
  unfold Mem.mems at hc ⊢
  rw [Mem.merge_members, Array.getElem?_modify, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds, ite_eq_right (Ne.symm hk)]
  cases h : m.members[k]? with
  | none => rw [h] at hc; simp at hc
  | some a =>
    rw [h] at hc
    split_ifs <;> simp_all

theorem Mem.merge_mems_self {m : Mem} {i j c : ℕ} (hij : i ≠ j) (hi : i < m.members.size)
    (hc : c ∈ m.mems j) : c ∈ (m.merge i j).mems i := by
  unfold Mem.mems
  rw [Mem.merge_members, Array.getElem?_modify, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds, ite_eq_right (Ne.symm hij), ite_eq_left rfl,
    Array.getElem?_eq_getElem hi]
  simp [hc]

/-- Merging two classes of unwritten cells with one reference value. -/
theorem Core.merge {m : Mem} {M : ℕ → E} (h : Core m M) {i j : ℕ} (hij : i ≠ j)
    (hi : i < m.vals.size) (hvi : (m.vals[i]?).join = none) (hvj : (m.vals[j]?).join = none)
    {x y : ℕ} (hx : m.cellOf x = .cls i) (hy : m.cellOf y = .cls j) (hxy : M x = M y) :
    Core (m.merge i j) M ∧ (∀ c k, m.cellOf c = .cls k → k ≠ j → (m.merge i j).cellOf c = .cls k) ∧
      ∀ c, m.cellOf c = .cls j → (m.merge i j).cellOf c = .cls i := by
  have hmc := Mem.merge_cellOf hij (fun c hc ↦ h.mem c j hc)
  have hk : ∀ c k, m.cellOf c = .cls k → k ≠ j → (m.merge i j).cellOf c = .cls k :=
    fun c k hc hkj ↦ by rw [hmc, ite_eq_right (by rw [hc]; simpa using hkj), hc]
  have hj : ∀ c, m.cellOf c = .cls j → (m.merge i j).cellOf c = .cls i :=
    fun c hc ↦ by rw [hmc, ite_eq_left hc]
  have hback : ∀ c k, (m.merge i j).cellOf c = .cls k →
      (m.cellOf c = .cls j ∧ k = i) ∨ (m.cellOf c = .cls k ∧ k ≠ j) := fun c k hc ↦ by
    rw [hmc] at hc
    split_ifs at hc with h1
    · cases hc; exact Or.inl ⟨h1, rfl⟩
    · exact Or.inr ⟨hc, fun hkj ↦ h1 (hkj ▸ hc)⟩
  obtain ⟨-, hwf⟩ := Mem.merge_ok h.wf hi hvj
  refine ⟨⟨hwf, fun c v hc ↦ ?_, fun c d k hc hd ↦ ?_, fun c k hc ↦ ?_, ?_, by simpa using h.used⟩,
    hk, hj⟩
  · rw [Mem.get_eq, Mem.merge_vals, hmc] at hc
    split_ifs at hc with h1
    · simp only [cval] at hc; rw [hvi] at hc; cases hc
    · exact h.get c v (by rw [Mem.get_eq]; exact hc)
  · have hyx : M y = M x := hxy.symm
    rcases hback c k hc with ⟨hc1, rfl⟩ | ⟨hc1, -⟩ <;>
      rcases hback d k hd with ⟨hd1, hk1⟩ | ⟨hd1, -⟩
    · exact h.cls c d j hc1 hd1
    · rw [h.cls c y j hc1 hy, hyx, h.cls x d k hx hd1]
    · subst hk1; rw [h.cls c x k hc1 hx, hxy, h.cls y d j hy hd1]
    · exact h.cls c d k hc1 hd1
  · rcases hback c k hc with ⟨hc1, rfl⟩ | ⟨hc1, hkj⟩
    · exact Mem.merge_mems_self hij (by rw [h.size]; exact hi) (h.mem c j hc1)
    · exact Mem.merge_mems_of_ne hkj (h.mem c k hc1)
  · rw [Mem.merge_members, Mem.merge_vals]
    simpa [Array.size_modify] using h.size

theorem Mem.join_members (m : Mem) (c i : ℕ) :
    (m.join c i).members = m.members.modify i (·.push c) := by
  cases m; rfl

/-- Adding a cell, unwritten or already in the class, to a class without a value. -/
theorem Core.join {m : Mem} {M : ℕ → E} (h : Core m M) {c i : ℕ}
    (hc : m.cellOf c = .free ∨ m.cellOf c = .cls i) (hi : i < m.vals.size)
    (hv : (m.vals[i]?).join = none) (hcu : c < m.used) (hM : ∀ x, m.cellOf x = .cls i → M x = M c) :
    Core (m.join c i) M ∧ (∀ x k, m.cellOf x = .cls k → (m.join c i).cellOf x = .cls k) ∧
      (m.join c i).cellOf c = .cls i := by
  have hg : m.get c = none := by
    rcases hc with hc | hc
    · exact Mem.get_none_of_free hc
    · rw [Mem.get_cls hc, hv]
  obtain ⟨-, hwf⟩ := Mem.join_ok h.wf hi hg hcu
  have hkeep : ∀ x k, m.cellOf x = .cls k → (m.join c i).cellOf x = .cls k := fun x k hx ↦ by
    rw [Mem.join_cellOf]
    split_ifs with hxc
    · subst hxc; rcases hc with hc | hc <;> rw [hc] at hx <;> cases hx; rfl
    · exact hx
  have hback : ∀ x k, (m.join c i).cellOf x = .cls k → (x = c ∧ k = i) ∨ m.cellOf x = .cls k :=
    fun x k hx ↦ by
      rw [Mem.join_cellOf] at hx
      split_ifs at hx with hxc
      · cases hx; exact Or.inl ⟨hxc, rfl⟩
      · exact Or.inr hx
  have hpush : ∀ x k, x ∈ m.mems k → x ∈ (m.join c i).mems k := fun x k hx ↦ by
    unfold Mem.mems at hx ⊢
    rw [Mem.join_members, Array.getElem?_modify]
    cases h' : m.members[k]? with
    | none => rw [h'] at hx; simp at hx
    | some a => rw [h'] at hx; split_ifs <;> simp_all
  refine ⟨⟨hwf, fun d u hd ↦ ?_, fun d d' k hd hd' ↦ ?_, fun d k hd ↦ ?_, ?_,
    by simpa using h.used⟩, hkeep, by rw [Mem.join_cellOf, ite_eq_left rfl]⟩
  · rw [Mem.get_eq, Mem.join_vals, Mem.join_cellOf] at hd
    split_ifs at hd with hdc
    · simp only [cval] at hd; rw [hv] at hd; cases hd
    · exact h.get d u (by rw [Mem.get_eq]; exact hd)
  · rcases hback d k hd with ⟨rfl, rfl⟩ | hd1 <;> rcases hback d' k hd' with ⟨rfl, hk⟩ | hd2
    · rfl
    · exact (hM d' hd2).symm
    · subst hk; exact hM d hd1
    · exact h.cls d d' k hd1 hd2
  · rcases hback d k hd with ⟨rfl, rfl⟩ | hd1
    · unfold Mem.mems
      rw [Mem.join_members, Array.getElem?_modify, ite_eq_left rfl,
        Array.getElem?_eq_getElem (by rw [h.size]; exact hi)]
      simp
    · exact hpush d k (h.mem d k hd1)
  · rw [Mem.join_members, Mem.join_vals, Array.size_modify]; exact h.size

/-- A fresh class, without a value. -/
theorem Core.fresh {m : Mem} {M : ℕ → E} (h : Core m M) :
    Core ⟨m.cells, m.vals.push none, m.members.push #[], m.links, m.used⟩ M := by
  refine ⟨⟨fun c k hc ↦ ?_, fun c hc ↦ h.wf.used c hc⟩, fun c v hc ↦ ?_, fun c d k ↦ h.cls c d k,
    fun c k hc ↦ ?_, by simpa using h.size, h.used⟩
  · have := h.wf.cls c k hc; simp only [Array.size_push]; omega
  · rw [Mem.get_eq] at hc; dsimp only at hc; rw [Mem.cellOf_mk, cval_push_none] at hc
    exact h.get c v (by rw [Mem.get_eq]; exact hc)
  · have hk : k < m.members.size := by rw [h.size]; exact h.wf.cls c k hc
    have := h.mem c k hc
    unfold Mem.mems at this ⊢
    dsimp only
    rw [Array.getElem?_push, ite_eq_right (by omega)]
    exact this

theorem Mem.cellOf_free {m : Mem} {c : ℕ} (hg : m.get c = none)
    (hn : ∀ k, m.cells[c]? = some (.cls k) → False) : m.cellOf c = .free := by
  rw [Mem.get_eq] at hg
  unfold Mem.cellOf at hg ⊢
  cases h : m.cells[c]? with
  | none => rfl
  | some x =>
    rw [h] at hg
    cases x with
    | free => rfl
    | lit w => cases hg
    | cls k => exact absurd h (hn k)

/-- The link of two unwritten cells with one reference value keeps the agreement. -/
theorem Agree.link {m : Mem} {M : ℕ → E} (h : Agree m M) {a b : ℕ} (ha : m.get a = none)
    (hb : m.get b = none) (hab : M a = M b) (hau : a < maxCells) (hbu : b < maxCells) :
    Agree (m.link a b) M := by
  obtain ⟨cells, vals, members, links, used⟩ := m
  set m1 : Mem := ⟨cells, vals, members, links.push (a, b), max used (max a b + 1)⟩
  have hc1 : ∀ c, m1.cellOf c = (⟨cells, vals, members, links, used⟩ : Mem).cellOf c := fun _ ↦ rfl
  have h1 : Core m1 M := ⟨⟨fun c k hc ↦ h.wf.cls c k hc, fun c hc ↦ by
      have := h.wf.used c hc; dsimp only at this; simp only [m1]; omega⟩,
    fun c v hc ↦ h.get c v hc, fun c d k ↦ h.cls c d k, fun c k ↦ h.mem c k, h.size, by
      have := h.used; dsimp only at this; simp only [m1]; omega⟩
  have ha1 : m1.get a = none := ha
  have hb1 : m1.get b = none := hb
  have hau1 : a < m1.used := by simp only [m1]; omega
  have hbu1 : b < m1.used := by simp only [m1]; omega
  have fin : ∀ r : Mem, Core r M → r.links = m1.links →
      (∀ x y, SameCls m1 x y → SameCls r x y) → SameCls r a b → Agree r M := by
    intro r hr hl hs hab'
    refine ⟨hr, fun p hp ↦ ?_⟩
    rw [hl] at hp
    simp only [m1, Array.mem_push] at hp
    rcases hp with hp | rfl
    · obtain ⟨hM, hS⟩ := h.links p hp
      exact ⟨hM, hs _ _ hS⟩
    · exact ⟨hab, hab'⟩
  have hcls : ∀ c i, cells[c]? = some (.cls i) → m1.cellOf c = .cls i := fun c i hc ↦ by
    simp only [m1, Mem.cellOf_mk, hc]; rfl
  have hval : ∀ c i, m1.get c = none → cells[c]? = some (.cls i) → (vals[i]?).join = none :=
    fun c i hg hc ↦ by rw [Mem.get_cls (hcls c i hc)] at hg; exact hg
  simp only [Mem.link]
  split
  · rename_i i j hi hj
    have hai := hcls a i hi
    have hbj := hcls b j hj
    split_ifs with hij hsz
    · subst hij; exact fin m1 h1 rfl (fun _ _ h ↦ h) ⟨i, hai, hbj⟩
    · obtain ⟨c1, c2, c3⟩ := h1.merge hij (h1.wf.cls a i hai) (hval a i ha1 hi) (hval b j hb1 hj)
        hai hbj hab
      exact fin _ c1 (Mem.merge_links _ _ _) (fun x y ⟨k, hx, hy⟩ ↦ by
        by_cases hk : k = j
        · subst hk; exact ⟨i, c3 x hx, c3 y hy⟩
        · exact ⟨k, c2 x k hx hk, c2 y k hy hk⟩) ⟨i, c2 a i hai hij, c3 b hbj⟩
    · obtain ⟨c1, c2, c3⟩ := h1.merge (Ne.symm hij) (h1.wf.cls b j hbj) (hval b j hb1 hj)
        (hval a i ha1 hi) hbj hai hab.symm
      exact fin _ c1 (Mem.merge_links _ _ _) (fun x y ⟨k, hx, hy⟩ ↦ by
        by_cases hk : k = i
        · subst hk; exact ⟨j, c3 x hx, c3 y hy⟩
        · exact ⟨k, c2 x k hx hk, c2 y k hy hk⟩) ⟨j, c3 a hai, c2 b j hbj (Ne.symm hij)⟩
  · rename_i i hi hn
    have hai := hcls a i hi
    have hbf : m1.cellOf b = .free := Mem.cellOf_free hb1 fun j hj ↦ hn j hj
    obtain ⟨c1, c2, c3⟩ := h1.join (Or.inl hbf) (h1.wf.cls a i hai) (hval a i ha1 hi) hbu1
      fun x hx ↦ (h1.cls x a i hx hai).trans hab
    exact fin _ c1 (Mem.join_links _ _ _) (fun x y ⟨k, hx, hy⟩ ↦ ⟨k, c2 x k hx, c2 y k hy⟩)
      ⟨i, c2 a i hai, c3⟩
  · rename_i j hj hn
    have hbj := hcls b j hj
    have haf : m1.cellOf a = .free := Mem.cellOf_free ha1 fun i hi ↦ hn i hi
    obtain ⟨c1, c2, c3⟩ := h1.join (Or.inl haf) (h1.wf.cls b j hbj) (hval b j hb1 hj) hau1
      fun x hx ↦ (h1.cls x b j hx hbj).trans hab.symm
    exact fin _ c1 (Mem.join_links _ _ _) (fun x y ⟨k, hx, hy⟩ ↦ ⟨k, c2 x k hx, c2 y k hy⟩)
      ⟨j, c3, c2 b j hbj⟩
  · rename_i hna hnb _
    have haf : m1.cellOf a = .free := Mem.cellOf_free ha1 hna
    have hbf : m1.cellOf b = .free := Mem.cellOf_free hb1 hnb
    have h2 := h1.fresh
    set m2 : Mem :=
      ⟨cells, vals.push none, members.push #[], links.push (a, b), max used (max a b + 1)⟩
    have hc2 : ∀ c, m2.cellOf c = m1.cellOf c := fun _ ↦ rfl
    have hno : ∀ x, m2.cellOf x = .cls vals.size → False := fun x hx ↦ by
      have := h1.wf.cls x _ ((hc2 x).symm.trans hx); simp [m1] at this
    have hk2 : vals.size < m2.vals.size := by simp [m2]
    have hv2 : (m2.vals[vals.size]?).join = none := by simp [m2]
    obtain ⟨c1, c2, c3⟩ := h2.join (Or.inl ((hc2 a).trans haf)) hk2 hv2 hau1
      fun x hx ↦ (hno x hx).elim
    have hb3 : (m2.join a vals.size).cellOf b = .free ∨
        (m2.join a vals.size).cellOf b = .cls vals.size := by
      rw [Mem.join_cellOf]
      by_cases hba : b = a
      · rw [ite_eq_left hba]; exact Or.inr rfl
      · rw [ite_eq_right hba]; exact Or.inl ((hc2 b).trans hbf)
    obtain ⟨d1, d2, d3⟩ := c1.join hb3 (by simpa using hk2) (by simpa using hv2)
      (by simpa using hbu1) fun x hx ↦ by
        rw [Mem.join_cellOf] at hx
        by_cases hxa : x = a
        · rw [hxa]; exact hab
        · rw [ite_eq_right hxa] at hx; exact (hno x hx).elim
    exact fin _ d1 (by simp only [Mem.join_links]; rfl)
      (fun x y ⟨k, hx, hy⟩ ↦ ⟨k, d2 x k (c2 x k hx), d2 y k (c2 y k hy)⟩)
      ⟨vals.size, d2 a _ c3, d3⟩

end

end LeanVM.Prover.Exec
