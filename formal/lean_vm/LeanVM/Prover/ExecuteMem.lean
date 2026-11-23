module

public import Statement.Prover.Execute

/-!
# The executor's memory only grows

`Mem.Le m m'`: every written cell of `m` holds its value in `m'`, `used` grows and every link is
kept. `Mem.WF`: a class a cell is in has a value slot, and a cell in use lies below `used`. Every
successful `put`, `putRun`, `ensure` and `link` (of two unwritten cells) is monotone and keeps
`WF`; `put c v` writes `v` at `c`, and `link a b` records `(a, b)`.
-/

namespace LeanVM.Prover.Exec

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-! ## `Except` -/

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact ⟨fun h ↦ (by cases h), fun ⟨_, h, _⟩ ↦ (by cases h)⟩
  | ok a => exact ⟨fun h ↦ ⟨a, rfl, h⟩, fun ⟨_, h, h'⟩ ↦ by cases h; exact h'⟩

@[simp] theorem pure_ok {ε α : Type} {a b : α} : (pure a : Except ε α) = .ok b ↔ a = b :=
  ⟨fun h ↦ Except.ok.inj h, fun h ↦ h ▸ rfl⟩

@[simp] theorem throw_ok {ε α : Type} {e : ε} {b : α} : (throw e : Except ε α) = .ok b ↔ False :=
  ⟨fun h ↦ (by cases h), False.elim⟩

theorem mapError_ok {ε ε' α : Type} {f : ε → ε'} {x : Except ε α} {a : α} :
    x.mapError f = .ok a ↔ x = .ok a := by
  cases x <;> simp [Except.mapError]

/-! ## Cells -/

/-- The cell at `c`, `free` past the array. -/
def Mem.cellOf (m : Mem) (c : ℕ) : Cell := m.cells[c]?.getD .free

/-- A cell's value given the classes' values. -/
def cval (vals : Array (Option E)) : Cell → Option E
  | .lit v => some v
  | .cls k => (vals[k]?).join
  | .free => none

theorem Mem.get_eq (m : Mem) (c : ℕ) : m.get c = cval m.vals (m.cellOf c) := by
  unfold Mem.get Mem.cellOf
  cases m.cells[c]? with
  | none => rfl
  | some x => cases x <;> rfl

/-- `m'` extends `m`. -/
structure Mem.Le (m m' : Mem) : Prop where
  get : ∀ c v, m.get c = some v → m'.get c = some v
  used : m.used ≤ m'.used
  links : ∀ p, p ∈ m.links → p ∈ m'.links

instance : LE Mem := ⟨Mem.Le⟩

theorem Mem.le_refl (m : Mem) : m ≤ m := ⟨fun _ _ h ↦ h, le_rfl, fun _ h ↦ h⟩

theorem Mem.le_trans {a b c : Mem} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  ⟨fun x v h ↦ h2.get x v (h1.get x v h), h1.used.trans h2.used,
    fun p h ↦ h2.links p (h1.links p h)⟩

/-- The memory is well formed. -/
structure Mem.WF (m : Mem) : Prop where
  cls : ∀ c k, m.cellOf c = .cls k → k < m.vals.size
  used : ∀ c, m.cellOf c ≠ .free → c < m.used

theorem Mem.WF.get_lt {m : Mem} (hm : m.WF) {c : ℕ} {v : E} (h : m.get c = some v) :
    c < m.used := by
  refine hm.used c fun hc ↦ ?_
  rw [Mem.get_eq, hc] at h
  simp [cval] at h

/-- A step that keeps every written cell's value, `used` and the links. -/
theorem Mem.le_of {m m' : Mem}
    (hc : ∀ c v, cval m.vals (m.cellOf c) = some v → cval m'.vals (m'.cellOf c) = some v)
    (hu : m.used ≤ m'.used) (hl : ∀ p, p ∈ m.links → p ∈ m'.links) : m ≤ m' :=
  ⟨fun c v h ↦ by rw [Mem.get_eq] at h ⊢; exact hc c v h, hu, hl⟩

/-! ## `ensure` -/

@[simp] theorem Mem.ensure_cells (m : Mem) (c : ℕ) : (m.ensure c).cells = m.cells := rfl
@[simp] theorem Mem.ensure_vals (m : Mem) (c : ℕ) : (m.ensure c).vals = m.vals := rfl
@[simp] theorem Mem.ensure_links (m : Mem) (c : ℕ) : (m.ensure c).links = m.links := rfl
@[simp] theorem Mem.ensure_used (m : Mem) (c : ℕ) : (m.ensure c).used = max m.used (c + 1) := rfl
@[simp] theorem Mem.ensure_cellOf (m : Mem) (c c' : ℕ) : (m.ensure c).cellOf c' = m.cellOf c' := rfl

theorem Mem.le_ensure (m : Mem) (c : ℕ) : m ≤ m.ensure c :=
  Mem.le_of (fun _ _ h ↦ h) (by simp) (fun _ h ↦ h)

theorem Mem.WF.ensure {m : Mem} (hm : m.WF) (c : ℕ) : (m.ensure c).WF :=
  ⟨fun c' k h ↦ hm.cls c' k h, fun c' h ↦ by
    have := hm.used c' h; simp only [Mem.ensure_used]; omega⟩

theorem Mem.foldl_ensure (l : List ℕ) (m : Mem) (hm : m.WF) :
    m ≤ l.foldl Mem.ensure m ∧ (l.foldl Mem.ensure m).WF := by
  induction l generalizing m with
  | nil => exact ⟨Mem.le_refl m, hm⟩
  | cons c l ih =>
    obtain ⟨h1, h2⟩ := ih (m.ensure c) (hm.ensure c)
    exact ⟨Mem.le_trans (Mem.le_ensure m c) h1, h2⟩

/-! ## `setCell` -/

theorem Mem.setCell_eq (m : Mem) (c : ℕ) (x : Cell) : m.setCell c x =
    ⟨(if c < m.cells.size then m.cells
      else m.cells ++ Array.replicate (max (c + 1) (2 * m.cells.size) - m.cells.size) .free).set! c x,
      m.vals, m.members, m.links, m.used⟩ := by
  cases m; rfl

theorem Mem.cellOf_setCell (m : Mem) (c c' : ℕ) (x : Cell) :
    (m.setCell c x).cellOf c' = if c' = c then x else m.cellOf c' := by
  rw [Mem.setCell_eq]
  unfold Mem.cellOf
  dsimp only
  generalize hA : (if c < m.cells.size then m.cells
    else m.cells ++ Array.replicate (max (c + 1) (2 * m.cells.size) - m.cells.size) Cell.free) = A
  have hc : c < A.size := by
    subst hA; split_ifs with h
    · exact h
    · simp only [Array.size_append, Array.size_replicate]; omega
  have hA' : ∀ c' : ℕ, A[c']?.getD Cell.free = m.cells[c']?.getD Cell.free := by
    intro c'; subst hA; split_ifs with h
    · rfl
    · simp only [Array.getElem?_append, Array.getElem?_replicate]
      split_ifs with h1 h2
      · rfl
      · rw [Array.getElem?_eq_none (by omega)]; rfl
      · rw [Array.getElem?_eq_none (by omega)]
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases h : c' = c
  · subst h; simp [hc]
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h, hA']

@[simp] theorem Mem.setCell_vals (m : Mem) (c : ℕ) (x : Cell) : (m.setCell c x).vals = m.vals := by
  cases m; rfl
@[simp] theorem Mem.setCell_links (m : Mem) (c : ℕ) (x : Cell) :
    (m.setCell c x).links = m.links := by
  cases m; rfl
@[simp] theorem Mem.setCell_used (m : Mem) (c : ℕ) (x : Cell) : (m.setCell c x).used = m.used := by
  cases m; rfl

/-- Setting an unwritten cell is monotone. -/
theorem Mem.le_setCell {m : Mem} {c : ℕ} (x : Cell) (hc : m.get c = none) : m ≤ m.setCell c x := by
  refine Mem.le_of (fun c' v h ↦ ?_) (by simp) (fun _ h ↦ by simpa using h)
  rw [Mem.cellOf_setCell, Mem.setCell_vals]
  by_cases h' : c' = c
  · subst h'; rw [Mem.get_eq, h] at hc; simp at hc
  · rw [ite_eq_right h']; exact h

theorem Mem.WF.setCell {m : Mem} (hm : m.WF) {c : ℕ} {x : Cell}
    (hx : ∀ k, x = .cls k → k < m.vals.size) (hu : c < m.used) : (m.setCell c x).WF := by
  refine ⟨fun c' k h ↦ ?_, fun c' h ↦ ?_⟩
  · rw [Mem.cellOf_setCell] at h
    rw [Mem.setCell_vals]
    split_ifs at h
    · exact hx k h
    · exact hm.cls c' k h
  · rw [Mem.cellOf_setCell] at h
    rw [Mem.setCell_used]
    split_ifs at h with h'
    · exact h' ▸ hu
    · exact hm.used c' h

/-! ## `put` -/

theorem Mem.cellOf_mk (cells : Array Cell) (vals : Array (Option E)) (members : Array (Array ℕ))
    (links : Array (ℕ × ℕ)) (used c : ℕ) :
    (⟨cells, vals, members, links, used⟩ : Mem).cellOf c = cells[c]?.getD .free := rfl

/-- `put` writes `v` at `c`, monotonically. -/
theorem Mem.put_ok {m m' : Mem} {c : ℕ} {v : E} (hm : m.WF) (e : m.put c v = .ok m') :
    m ≤ m' ∧ m'.WF ∧ m'.get c = some v := by
  have hm1 := hm.ensure c
  have hle1 := Mem.le_ensure m c
  have hcu : c < (m.ensure c).used := by simp
  simp only [Mem.put] at e
  generalize m.ensure c = m1 at hm1 hle1 hcu e
  obtain ⟨cells, vals, members, links, used⟩ := m1
  simp only at e hcu
  split at e
  · rename_i w hw
    split_ifs at e with hwv
    · simp only [pure_ok] at e; subst e hwv
      refine ⟨hle1, hm1, ?_⟩
      rw [Mem.get_eq, Mem.cellOf_mk, hw]; rfl
  · rename_i k hk
    have hkc : (⟨cells, vals, members, links, used⟩ : Mem).cellOf c = .cls k := by
      rw [Mem.cellOf_mk, hk]; rfl
    split at e
    · rename_i w hw'
      split_ifs at e with hwv
      · simp only [pure_ok] at e; subst e hwv
        refine ⟨hle1, hm1, ?_⟩
        rw [Mem.get_eq, hkc]; exact hw'
    · rename_i hn
      simp only [pure_ok] at e; subst e
      have hks : k < vals.size := hm1.cls c k hkc
      refine ⟨Mem.le_trans hle1 (Mem.le_of (fun c' u h ↦ ?_) le_rfl fun _ h ↦ h), ⟨fun c' k' h ↦ ?_,
        fun c' h ↦ hm1.used c' h⟩, ?_⟩
      · rw [Mem.cellOf_mk] at h ⊢
        generalize cells[c']?.getD Cell.free = x at h ⊢
        cases x with
        | lit => exact h
        | free => exact h
        | cls k' =>
          have hne : k ≠ k' := by rintro rfl; simp only [cval] at h; rw [hn] at h; simp at h
          simp only [cval, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne hne]
          exact h
      · simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
        exact hm1.cls c' k' h
      · rw [Mem.get_eq, Mem.cellOf_mk, hk]
        simp [cval, hks]
  · rename_i hx1 hx2
    simp only [pure_ok] at e; subst e
    have hfree : (⟨cells, vals, members, links, used⟩ : Mem).cellOf c = .free := by
      rw [Mem.cellOf_mk]
      cases h : cells[c]? with
      | none => rfl
      | some x => cases x with
        | free => rfl
        | lit w => exact absurd h (hx1 w)
        | cls k => exact absurd h (hx2 k)
    have hg : (⟨cells, vals, members, links, used⟩ : Mem).get c = none := by
      rw [Mem.get_eq, hfree]; rfl
    refine ⟨Mem.le_trans hle1 (Mem.le_setCell _ hg), hm1.setCell (fun _ h ↦ Cell.noConfusion h) hcu,
      ?_⟩
    rw [Mem.get_eq, Mem.cellOf_setCell, ite_eq_left rfl]; rfl

/-- A fold of monotone writes. -/
theorem Mem.foldlM_ok {α : Type} (f : Mem → α → Except Fault Mem) (Q : α → Mem → Prop)
    (hQ : ∀ x m m', Q x m → m ≤ m' → Q x m')
    (hf : ∀ m x m', m.WF → f m x = .ok m' → m ≤ m' ∧ m'.WF ∧ Q x m') :
    ∀ (l : List α) (m m' : Mem), m.WF → l.foldlM f m = .ok m' →
      m ≤ m' ∧ m'.WF ∧ ∀ x ∈ l, Q x m'
  | [], m, m', hm, e => by
    simp only [List.foldlM_nil, pure_ok] at e; subst e
    exact ⟨Mem.le_refl m, hm, fun _ h ↦ nomatch h⟩
  | x :: l, m, m', hm, e => by
    rw [List.foldlM_cons, bind_ok] at e
    obtain ⟨m1, e1, e⟩ := e
    obtain ⟨h1, h2, h3⟩ := hf m x m1 hm e1
    obtain ⟨h4, h5, h6⟩ := Mem.foldlM_ok f Q hQ hf l m1 m' h2 e
    refine ⟨Mem.le_trans h1 h4, h5, fun y hy ↦ ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hQ _ _ _ h3 h4
    · exact h6 y hy

theorem putRun_ok {b : ℕ} {vs : List E} {m m' : Mem} (hm : m.WF) (e : putRun b vs m = .ok m') :
    m ≤ m' ∧ m'.WF := by
  unfold putRun at e
  obtain ⟨h1, h2, -⟩ := Mem.foldlM_ok _ (fun _ _ ↦ True) (fun _ _ _ _ _ ↦ trivial)
    (fun m x m' hm e ↦ by
      obtain ⟨v, k⟩ := x
      obtain ⟨h1, h2, -⟩ := Mem.put_ok hm e
      exact ⟨h1, h2, trivial⟩) _ m m' hm e
  exact ⟨h1, h2⟩

/-! ## `link` -/

/-- One move of `merge`'s fold. -/
def mergeStep (i j : ℕ) (cs : Array Cell) (c : ℕ) : Array Cell :=
  match cs[c]? with
  | some (.cls k) => if k = j then cs.set! c (.cls i) else cs
  | _ => cs

theorem Mem.merge_eq (m : Mem) (i j : ℕ) : m.merge i j =
    ⟨Array.foldl (mergeStep i j) m.cells (m.members[j]?.getD #[]), m.vals,
      (m.members.set! j #[]).modify i (fun a ↦ a ++ m.members[j]?.getD #[]), m.links, m.used⟩ := by
  cases m; rfl

/-- A cell `merge` leaves, or moves from class `j` to class `i`. -/
def Moved (i j : ℕ) (a b : Cell) : Prop := b = a ∨ (a = .cls j ∧ b = .cls i)

theorem mergeStep_moved {i j : ℕ} {cells cs : Array Cell}
    (h : ∀ c' : ℕ, Moved i j (cells[c']?.getD .free) (cs[c']?.getD .free)) (c : ℕ) :
    ∀ c' : ℕ, Moved i j (cells[c']?.getD .free) ((mergeStep i j cs c)[c']?.getD .free) := by
  intro c'
  unfold mergeStep
  split
  · rename_i k hk
    split_ifs with hkj
    · subst hkj
      simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      by_cases hc : c = c'
      · subst hc
        have hlt : c < cs.size := by
          by_contra hn; rw [Array.getElem?_eq_none (by omega)] at hk; simp at hk
        rw [ite_eq_left rfl, ite_eq_left hlt]
        have hcs : cs[c]?.getD .free = .cls k := by rw [hk]; rfl
        rcases h c with h' | ⟨h', -⟩
        · exact Or.inr ⟨h'.symm.trans hcs, rfl⟩
        · exact Or.inr ⟨h', rfl⟩
      · rw [ite_eq_right hc]; exact h c'
    · exact h c'
  · exact h c'

theorem foldl_mergeStep_moved (i j : ℕ) (cells : Array Cell) :
    ∀ (js : List ℕ) (cs : Array Cell),
      (∀ c' : ℕ, Moved i j (cells[c']?.getD .free) (cs[c']?.getD .free)) →
      ∀ c' : ℕ, Moved i j (cells[c']?.getD .free) ((js.foldl (mergeStep i j) cs)[c']?.getD .free)
  | [], _, h => h
  | c :: js, _, h => foldl_mergeStep_moved i j cells js _ (mergeStep_moved h c)

theorem Mem.merge_moved (m : Mem) (i j c : ℕ) :
    Moved i j (m.cellOf c) ((m.merge i j).cellOf c) := by
  rw [Mem.merge_eq]
  unfold Mem.cellOf
  dsimp only
  rw [← Array.foldl_toList]
  exact foldl_mergeStep_moved i j m.cells _ m.cells (fun _ ↦ Or.inl rfl) c

@[simp] theorem Mem.merge_vals (m : Mem) (i j : ℕ) : (m.merge i j).vals = m.vals := by
  rw [Mem.merge_eq]
@[simp] theorem Mem.merge_links (m : Mem) (i j : ℕ) : (m.merge i j).links = m.links := by
  rw [Mem.merge_eq]
@[simp] theorem Mem.merge_used (m : Mem) (i j : ℕ) : (m.merge i j).used = m.used := by
  rw [Mem.merge_eq]

theorem Mem.merge_ok {m : Mem} {i j : ℕ} (hm : m.WF) (hi : i < m.vals.size)
    (hj : (m.vals[j]?).join = none) : m ≤ m.merge i j ∧ (m.merge i j).WF := by
  refine ⟨Mem.le_of (fun c v h ↦ ?_) (by simp) (fun _ h ↦ by simpa using h), fun c k h ↦ ?_,
    fun c h ↦ ?_⟩
  · rw [Mem.merge_vals]
    rcases m.merge_moved i j c with h' | ⟨h', -⟩
    · rw [h']; exact h
    · rw [h'] at h; simp only [cval] at h; rw [hj] at h; simp at h
  · rw [Mem.merge_vals]
    rcases m.merge_moved i j c with h' | ⟨-, h'⟩
    · rw [h'] at h; exact hm.cls c k h
    · rw [h'] at h; cases h; exact hi
  · rw [Mem.merge_used]
    refine hm.used c fun hc ↦ h ?_
    rcases m.merge_moved i j c with h' | ⟨h', -⟩
    · rw [h', hc]
    · rw [hc] at h'; exact absurd h' (fun h ↦ Cell.noConfusion h)

@[simp] theorem Mem.join_vals (m : Mem) (c i : ℕ) : (m.join c i).vals = m.vals := by
  cases m; rfl
@[simp] theorem Mem.join_links (m : Mem) (c i : ℕ) : (m.join c i).links = m.links := by
  cases m; rfl
@[simp] theorem Mem.join_used (m : Mem) (c i : ℕ) : (m.join c i).used = m.used := by
  cases m; rfl
theorem Mem.join_cellOf (m : Mem) (c i c' : ℕ) :
    (m.join c i).cellOf c' = if c' = c then .cls i else m.cellOf c' := by
  rw [← Mem.cellOf_setCell]; cases m; rfl

theorem Mem.join_ok {m : Mem} {c i : ℕ} (hm : m.WF) (hi : i < m.vals.size) (hc : m.get c = none)
    (hu : c < m.used) : m ≤ m.join c i ∧ (m.join c i).WF := by
  have h1 := Mem.le_setCell (.cls i) hc
  have h2 := hm.setCell (x := .cls i) (fun k h ↦ by cases h; exact hi) hu
  refine ⟨Mem.le_of (fun c' v h ↦ ?_) (by simp) (fun _ h ↦ by simpa using h),
    ⟨fun c' k h ↦ ?_, fun c' h ↦ ?_⟩⟩
  · have := h1.get c' v (by rw [Mem.get_eq]; exact h)
    rw [Mem.get_eq, Mem.cellOf_setCell, Mem.setCell_vals] at this
    rw [Mem.join_cellOf, Mem.join_vals]; exact this
  · rw [Mem.join_cellOf] at h; rw [Mem.join_vals]
    have := h2.cls c' k; rw [Mem.cellOf_setCell, Mem.setCell_vals] at this; exact this h
  · rw [Mem.join_cellOf] at h; rw [Mem.join_used]
    have := h2.used c'; rw [Mem.cellOf_setCell, Mem.setCell_used] at this; exact this h

theorem cval_push_none (vals : Array (Option E)) (x : Cell) :
    cval (vals.push none) x = cval vals x := by
  cases x with
  | cls k =>
    simp only [cval, Array.getElem?_push]
    split_ifs with h
    · subst h; rw [Array.getElem?_eq_none le_rfl]; rfl
    · rfl
  | _ => rfl

/-- A fresh class for two unwritten cells. -/
theorem Mem.fresh_ok {m : Mem} {a b : ℕ} (hm : m.WF) (ha : m.get a = none) (hb : m.get b = none)
    (hau : a < m.used) (hbu : b < m.used) :
    m ≤ ((⟨m.cells, m.vals.push none, m.members.push #[], m.links, m.used⟩ : Mem).join a
        m.vals.size).join b m.vals.size ∧
      (((⟨m.cells, m.vals.push none, m.members.push #[], m.links, m.used⟩ : Mem).join a
        m.vals.size).join b m.vals.size).WF := by
  set m2 : Mem := ⟨m.cells, m.vals.push none, m.members.push #[], m.links, m.used⟩
  have hle : m ≤ m2 := Mem.le_of (fun c v h ↦ by
    simp only [m2]; rw [cval_push_none]; exact h) le_rfl (fun _ h ↦ h)
  have hwf : m2.WF := ⟨fun c k h ↦ by
    have := hm.cls c k h; simp only [m2, Array.size_push]; omega, fun c h ↦ hm.used c h⟩
  have hk : m.vals.size < m2.vals.size := by simp [m2]
  have ha2 : m2.get a = none := by
    rw [Mem.get_eq]; simp only [m2]; rw [cval_push_none]; rw [Mem.get_eq] at ha; exact ha
  obtain ⟨h1, h2⟩ := Mem.join_ok hwf hk ha2 hau
  have hb3 : (m2.join a m.vals.size).get b = none := by
    rw [Mem.get_eq, Mem.join_cellOf, Mem.join_vals]
    split_ifs
    · simp [cval, m2]
    · simp only [m2]; rw [cval_push_none]; rw [Mem.get_eq] at hb; exact hb
  obtain ⟨h3, h4⟩ := Mem.join_ok h2 (by simpa using hk) hb3 (by simpa using hbu)
  exact ⟨Mem.le_trans hle (Mem.le_trans h1 h3), h4⟩

/-- Linking two unwritten cells is monotone and records the link. -/
theorem Mem.link_ok {m : Mem} {a b : ℕ} (hm : m.WF) (ha : m.get a = none) (hb : m.get b = none) :
    m ≤ m.link a b ∧ (m.link a b).WF ∧ (a, b) ∈ (m.link a b).links ∧ a < (m.link a b).used ∧
      b < (m.link a b).used := by
  obtain ⟨cells, vals, members, links, used⟩ := m
  set m1 : Mem := ⟨cells, vals, members, links.push (a, b), max used (max a b + 1)⟩
  have hle1 : (⟨cells, vals, members, links, used⟩ : Mem) ≤ m1 :=
    Mem.le_of (fun _ _ h ↦ h) (by simp [m1]) (fun _ h ↦ by simp [m1, h])
  have hwf1 : m1.WF := ⟨fun c k h ↦ hm.cls c k h, fun c h ↦ by
    have := hm.used c h; dsimp only at this; simp only [m1]; omega⟩
  have ha1 : m1.get a = none := ha
  have hb1 : m1.get b = none := hb
  have hau : a < m1.used := by simp only [m1]; omega
  have hbu : b < m1.used := by simp only [m1]; omega
  have hab : (a, b) ∈ m1.links := by simp [m1]
  have key : ∀ r : Mem, m1 ≤ r → r.WF → r.links = m1.links → r.used = m1.used →
      (⟨cells, vals, members, links, used⟩ : Mem) ≤ r ∧ r.WF ∧ (a, b) ∈ r.links ∧ a < r.used ∧
        b < r.used :=
    fun r h1 h2 h3 h4 ↦ ⟨Mem.le_trans hle1 h1, h2, h3 ▸ hab, h4 ▸ hau, h4 ▸ hbu⟩
  have hcls : ∀ c i, cells[c]? = some (.cls i) → m1.cellOf c = .cls i := fun c i h ↦ by
    simp only [m1, Mem.cellOf_mk, h]; rfl
  have hnone : ∀ c j, m1.get c = none → cells[c]? = some (.cls j) → (vals[j]?).join = none :=
    fun c j h hc ↦ by rw [Mem.get_eq, hcls c j hc] at h; exact h
  simp only [Mem.link]
  split
  · rename_i i j hi hj
    split_ifs
    · exact key m1 (Mem.le_refl m1) hwf1 rfl rfl
    · obtain ⟨h1, h2⟩ := Mem.merge_ok hwf1 (hwf1.cls a i (hcls a i hi)) (hnone b j hb1 hj)
      exact key _ h1 h2 (Mem.merge_links _ _ _) (Mem.merge_used _ _ _)
    · obtain ⟨h1, h2⟩ := Mem.merge_ok hwf1 (hwf1.cls b j (hcls b j hj)) (hnone a i ha1 hi)
      exact key _ h1 h2 (Mem.merge_links _ _ _) (Mem.merge_used _ _ _)
  · rename_i i hi _
    obtain ⟨h1, h2⟩ := Mem.join_ok hwf1 (hwf1.cls a i (hcls a i hi)) hb1 hbu
    exact key _ h1 h2 (Mem.join_links _ _ _) (Mem.join_used _ _ _)
  · rename_i j hj _
    obtain ⟨h1, h2⟩ := Mem.join_ok hwf1 (hwf1.cls b j (hcls b j hj)) ha1 hau
    exact key _ h1 h2 (Mem.join_links _ _ _) (Mem.join_used _ _ _)
  · obtain ⟨h1, h2⟩ := Mem.fresh_ok hwf1 ha1 hb1 hau hbu
    exact key _ h1 h2 (by simp only [Mem.join_links]; rfl) (by simp only [Mem.join_used]; rfl)

end

end LeanVM.Prover.Exec
