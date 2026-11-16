/-
  LeanVM.Guest.Backend.Complete.Tmps

  What `TmpsApart` says, unpacked: each temporary has a cell, no other named value is placed at a
  temporary's cell, and the placed body's instructions name each temporary's cell exactly once.
-/

module

public import LeanVM.Guest.Backend.Complete.Cells

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

theorem fold_contains (locs : VMap Loc) (n : ℕ) (g : NMap Unit → V → NMap Unit)
    (hg : ∀ m t, (g m t).contains n = true ↔ m.contains n = true ∨ cellP locs t = some n) :
    ∀ (ts : List V) (m : NMap Unit),
      (ts.foldl g m).contains n = true ↔ m.contains n = true ∨ ∃ t ∈ ts, cellP locs t = some n
  | [], m => by simp
  | t :: ts, m => by
      rw [List.foldl_cons, fold_contains locs n g hg ts, hg]
      simp only [List.mem_cons, exists_eq_or_imp, or_assoc]

/-- **The set of the temporaries' cells.** -/
theorem tmpCellSet_contains (locs : VMap Loc) (ts : List V) (n : ℕ) :
    (tmpCellSet locs ts).contains n = true ↔ ∃ t ∈ ts, cellP locs t = some n := by
  unfold tmpCellSet
  rw [fold_contains locs n _ ?_ ts {}]
  · simp [NMap.contains]
  · intro m t
    split
    · next k e =>
      rw [e]
      simp only [NMap.contains, NMap.get?_insert, Option.some.injEq]
      by_cases h : n = k
      · subst h; simp
      · simp [h, Ne.symm h]
    · next e =>
      simp only [e, reduceCtorEq, or_false]

theorem cellCounts_cells (set : NMap Unit) (n : ℕ) : ∀ (cs : List ℕ) (m : NMap ℕ),
    ((cs.foldl (fun m c => if set.contains c then m.insert c ((m.get? c).getD 0 + 1) else m)
      m).get? n).getD 0 = (m.get? n).getD 0 + (if set.contains n then cs.count n else 0)
  | [], m => by simp
  | c :: cs, m => by
      rw [List.foldl_cons, cellCounts_cells set n cs, List.count_cons]
      split
      · next hc =>
        rw [NMap.get?_insert]
        by_cases h : n = c
        · subst h; simp [hc]; omega
        · simp only [h, ↓reduceIte, beq_iff_eq]
          split <;> simp [Ne.symm h]
      · next hc =>
        by_cases h : n = c
        · subst h; simp [hc]
        · simp [Ne.symm h]

theorem cellCounts_go (set : NMap Unit) (n : ℕ) : ∀ (ops : List LOp) (m : NMap ℕ),
    ((ops.foldl (fun m o => (opCells o).foldl (fun m c =>
      if set.contains c then m.insert c ((m.get? c).getD 0 + 1) else m) m) m).get? n).getD 0 =
      (m.get? n).getD 0 + (if set.contains n then (ops.flatMap opCells).count n else 0)
  | [], m => by simp
  | o :: os, m => by
      rw [List.foldl_cons, cellCounts_go set n os, cellCounts_cells, List.flatMap_cons,
        List.count_append]
      split <;> omega

/-- **How many times the instructions name a cell of the set.** -/
theorem cellCounts_get (set : NMap Unit) (ops : List LOp) (n : ℕ) :
    ((cellCounts set ops).get? n).getD 0 =
      if set.contains n then (ops.flatMap opCells).count n else 0 := by
  rw [cellCounts, cellCounts_go]
  simp

variable {tf : TracedFn} {pf : Placed}

theorem TmpsApart.parts (h : TmpsApart tf pf) :
    apartWith tf pf (Stmt.tmpsList tf.core.body) (tmpCellSet pf.locs (Stmt.tmpsList tf.core.body))
      (cellCounts (tmpCellSet pf.locs (Stmt.tmpsList tf.core.body)) (blockOps pf.fn.body 0)) =
      true ∧ distinctCells pf.locs (Stmt.tmpsList tf.core.body) {} = true ∧
    tmpOpsB (tmpCellSet pf.locs (Stmt.tmpsList tf.core.body)) (fpPtrs (blockOps pf.fn.body 0))
      (blockOps pf.fn.body 0) = true ∧
    (tmpCellSet pf.locs (Stmt.tmpsList tf.core.body)).contains
      (2 + tf.core.params.length + tf.rets) = false ∧ noShift0 pf.locs = true := by
  unfold TmpsApart tmpsApartB at h
  rw [nmapSeq_eq, nmapSeq_eq, nmapSeq_eq, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.2.1.1.1.1, h.2.1.1.1.2, h.2.2, h.2.1.1.2, h.2.1.2⟩

theorem trieVals_get {α : Type} : ∀ (t : Trie α) (n : ℕ) (a : α), t.get n = some a → a ∈ trieVals t
  | .nil, _, _, h => by simp at h
  | .node v l r, n, a, h => by
      rw [Trie.get_eq_getC] at h
      simp only [Trie.getC] at h
      simp only [trieVals, List.mem_append]
      split at h
      · subst h; simp
      · split at h
        · exact Or.inl (Or.inr (trieVals_get l _ a (by rw [Trie.get_eq_getC]; exact h)))
        · exact Or.inr (trieVals_get r _ a (by rw [Trie.get_eq_getC]; exact h))

/-- **No place is a shift by `g^0`.** -/
theorem TmpsApart.noShift0 (h : TmpsApart tf pf) (v : V) (n : ℕ) :
    pf.locs[v]? ≠ some (.shifted n 0) := fun he => by
  have hb := h.parts.2.2.2.2
  unfold Complete.noShift0 at hb
  rw [KMap.getElem?_eq] at he
  unfold KMap.get? at he
  cases hg : pf.locs.t.get (Keyed.key v) with
  | none => rw [hg] at he; simp at he
  | some bucket =>
    rw [hg, Option.getD_some] at he
    have hmb := trieVals_get _ _ _ hg
    have hp : (v, Loc.shifted n 0) ∈ bucket := by
      obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp he
      simp
    have := List.all_eq_true.mp (List.all_eq_true.mp hb bucket hmb) _ hp
    simp at this

theorem TmpsApart.with (h : TmpsApart tf pf) :
    apartWith tf pf (Stmt.tmpsList tf.core.body) (tmpCellSet pf.locs (Stmt.tmpsList tf.core.body))
      (cellCounts (tmpCellSet pf.locs (Stmt.tmpsList tf.core.body)) (blockOps pf.fn.body 0)) =
      true := h.parts.1

/-- **No temporary is placed at the cell past the argument and return cells** (a registered
loop helper's own frame pointer). -/
theorem TmpsApart.self (h : TmpsApart tf pf) {t : V} (ht : t ∈ Stmt.tmpsList tf.core.body) :
    cellP pf.locs t ≠ some (2 + tf.core.params.length + tf.rets) := fun he => by
  have := (tmpCellSet_contains pf.locs _ _).mpr ⟨t, ht, he⟩
  rw [h.parts.2.2.2.1] at this
  cases this

/-- **A temporary has a cell.** -/
theorem TmpsApart.cell (h : TmpsApart tf pf) {t : V} (ht : t ∈ Stmt.tmpsList tf.core.body) :
    ∃ n, cellP pf.locs t = some n := by
  have hw := h.with
  simp only [apartWith, Bool.and_eq_true, List.all_eq_true] at hw
  exact Option.isSome_iff_exists.mp (hw.1.1 t ht)

/-- **No value the body names or takes is placed at a temporary's cell.** -/
theorem TmpsApart.apart (h : TmpsApart tf pf) {v : V}
    (hv : v ∈ Stmt.usesList tf.core.body ++ tf.core.params) {l : Loc} (hl : pf.locs[v]? = some l)
    {t : V} (ht : t ∈ Stmt.tmpsList tf.core.body) : cellP pf.locs t ≠ some (locBase l) := by
  intro he
  have hw := h.with
  simp only [apartWith, Bool.and_eq_true, List.all_eq_true] at hw
  have := hw.1.2 v hv
  rw [hl] at this
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at this
  have hc := (tmpCellSet_contains pf.locs (Stmt.tmpsList tf.core.body) (locBase l)).mpr ⟨t, ht, he⟩
  rw [this] at hc
  exact Bool.false_ne_true hc

/-- **The placed body's instructions name a temporary's cell exactly once.** -/
theorem TmpsApart.count (h : TmpsApart tf pf) {t : V} (ht : t ∈ Stmt.tmpsList tf.core.body)
    {n : ℕ} (hn : cellP pf.locs t = some n) :
    ((blockOps pf.fn.body 0).flatMap opCells).count n = 1 := by
  have hw := h.with
  simp only [apartWith, Bool.and_eq_true, List.all_eq_true] at hw
  have := hw.2 t ht
  rw [hn] at this
  have hs := (tmpCellSet_contains pf.locs (Stmt.tmpsList tf.core.body) n).mpr ⟨t, ht, hn⟩
  have hg := cellCounts_get (tmpCellSet pf.locs (Stmt.tmpsList tf.core.body))
    (blockOps pf.fn.body 0) n
  rw [beq_iff_eq.mp this, hs] at hg
  simpa using hg.symm

theorem distinctCells_spec (locs : VMap Loc) : ∀ (ts : List V) (m : NMap Unit),
    distinctCells locs ts m = true →
      (∀ t ∈ ts, ∀ n, cellP locs t = some n → m.contains n = false) ∧
      ∀ t ∈ ts, ∀ t' ∈ ts, ∀ n, cellP locs t = some n → cellP locs t' = some n → t = t'
  | [], _, _ => ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
  | t :: ts, m, h => by
      unfold distinctCells at h
      split at h
      · next n hn =>
        rw [Bool.and_eq_true, Bool.not_eq_true'] at h
        obtain ⟨hm, hrest⟩ := h
        obtain ⟨ih1, ih2⟩ := distinctCells_spec locs ts _ hrest
        have hins : ∀ t'' ∈ ts, ∀ n'', cellP locs t'' = some n'' → n'' ≠ n ∧ m.contains n'' = false :=
          fun t'' ht'' n'' hn'' => by
            have := ih1 t'' ht'' n'' hn''
            simp only [NMap.contains, NMap.get?_insert] at this
            split at this
            · simp at this
            · next hne => exact ⟨hne, this⟩
        refine ⟨fun t' ht' n' hn' => ?_, fun a ha b hb k hka hkb => ?_⟩
        · rcases List.mem_cons.mp ht' with rfl | ht'
          · rw [hn] at hn'; cases hn'; exact hm
          · exact (hins t' ht' n' hn').2
        · rcases List.mem_cons.mp ha with hat | ha
          · rcases List.mem_cons.mp hb with hbt | hb
            · rw [hat, hbt]
            · rw [hat, hn] at hka
              exact absurd (Option.some.inj hka).symm (hins b hb k hkb).1
          · rcases List.mem_cons.mp hb with hbt | hb
            · rw [hbt, hn] at hkb
              exact absurd (Option.some.inj hkb).symm (hins a ha k hka).1
            · exact ih2 a ha b hb k hka hkb
      · next hn =>
        obtain ⟨ih1, ih2⟩ := distinctCells_spec locs ts m h
        refine ⟨fun t' ht' n' hn' => ?_, fun a ha b hb k hka hkb => ?_⟩
        · rcases List.mem_cons.mp ht' with rfl | ht'
          · rw [hn] at hn'; cases hn'
          · exact ih1 t' ht' n' hn'
        · rcases List.mem_cons.mp ha with hat | ha
          · rw [hat, hn] at hka; cases hka
          rcases List.mem_cons.mp hb with hbt | hb
          · rw [hbt, hn] at hkb; cases hkb
          exact ih2 a ha b hb k hka hkb

/-- **No two temporaries share a cell.** -/
theorem TmpsApart.inj (h : TmpsApart tf pf) :
    ∀ t ∈ Stmt.tmpsList tf.core.body, ∀ t' ∈ Stmt.tmpsList tf.core.body, ∀ n,
      cellP pf.locs t = some n → cellP pf.locs t' = some n → t = t' :=
  (distinctCells_spec pf.locs _ _ h.parts.2.1).2

theorem fold_contains_mono (g : NMap Unit → LOp → NMap Unit) (q : ℕ)
    (hkeep : ∀ m o, m.contains q = true → (g m o).contains q = true)
    (hadd : ∀ m off d, (g m (.deref q off d .fp)).contains q = true) :
    ∀ (ops : List LOp) (m : NMap Unit),
      (m.contains q = true ∨ ∃ off d, LOp.deref q off d .fp ∈ ops) →
        (ops.foldl g m).contains q = true
  | [], _, h => by
      rcases h with h | ⟨_, _, h⟩
      · exact h
      · exact nomatch h
  | o :: os, m, h => by
      rw [List.foldl_cons]
      refine fold_contains_mono g q hkeep hadd os _ ?_
      rcases h with h | ⟨off, d, h⟩
      · exact Or.inl (hkeep m o h)
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inl (hadd m off d)
        · exact Or.inr ⟨off, d, h⟩

/-- A pointer cell through which a `DEREF` stores the frame pointer is in `fpPtrs`. -/
theorem fpPtrs_contains {ops : List LOp} {q off d : ℕ} (h : LOp.deref q off d .fp ∈ ops) :
    (fpPtrs ops).contains q = true := by
  unfold fpPtrs
  refine fold_contains_mono _ q (fun m o hm => ?_) (fun m off d => ?_) ops {} (Or.inr ⟨off, d, h⟩)
  · split
    · simp only [NMap.contains, NMap.get?_insert] at hm ⊢
      split <;> simp_all
    · exact hm
  · simp [NMap.contains, NMap.get?_insert]

/-- **An instruction naming a temporary's cell is a `DEREF` into it at offset `0`, through a
cell that is no temporary's and through which no `DEREF` stores the frame pointer.** -/
theorem TmpsApart.ops (h : TmpsApart tf pf) {t : V} (ht : t ∈ Stmt.tmpsList tf.core.body)
    {c : ℕ} (hc : cellP pf.locs t = some c) {o : LOp} (ho : o ∈ blockOps pf.fn.body 0)
    (hco : c ∈ opCells o) :
    ∃ p, o = .deref p 0 c .cell ∧ (∀ t' ∈ Stmt.tmpsList tf.core.body, cellP pf.locs t' ≠ some p) ∧
      ∀ q off d, LOp.deref q off d .fp ∈ blockOps pf.fn.body 0 → q ≠ p := by
  have hb := h.parts.2.2.1
  simp only [tmpOpsB, List.all_eq_true] at hb
  have := hb o ho c hco
  have hs := (tmpCellSet_contains pf.locs (Stmt.tmpsList tf.core.body) c).mpr ⟨t, ht, hc⟩
  rw [hs, Bool.not_true, Bool.false_or] at this
  split at this
  · next p d =>
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at this
    obtain ⟨⟨rfl, hp⟩, hf⟩ := this
    refine ⟨p, rfl, fun t' ht' he => ?_, fun q off d hq he => ?_⟩
    · have := (tmpCellSet_contains pf.locs (Stmt.tmpsList tf.core.body) p).mpr ⟨t', ht', he⟩
      rw [hp] at this; cases this
    · subst he
      rw [fpPtrs_contains hq] at hf; cases hf
  · cases this

end
end LeanVM.Guest.Backend.Complete
