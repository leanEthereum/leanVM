/-
  LeanVM.Guest.Backend.Complete.ProgJt

  The cells of the honest memory at the back end's data, and the jump tables in it.
-/

module

public import LeanVM.Guest.Backend.Complete.ProgPlace

/-!
# The honest memory's cells and the jump tables

`cellsB_node`, `cellsB_phantom`, `hdrB_node`: the cells and headers `World.cellsB`, `World.hdrB`
give an instance by its tree. `mem_frameB`: a candidate in `[2, n)` whose offset no other
candidate has is a cell. `jt_honestB`: on the honest memory of a run of `main`, the jump tables are
written, `main`'s frame at word `0` holding them from `tablesBase` past its placed frame.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

theorem mem_dedupB : ∀ {L : List (ℕ × E)} {q : ℕ × E}, q ∈ L → (∀ q' ∈ L, q'.1 = q.1 → q' = q) →
    q ∈ dedupB L
  | [], _, h, _ => absurd h (List.not_mem_nil)
  | x :: xs, q, h, hu => by
    rw [dedupB]
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · by_cases hx : x.1 = q.1
      · rw [hu x List.mem_cons_self hx]; exact List.mem_cons_self
      · refine List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨mem_dedupB h fun q' hq' he =>
          hu q' (List.mem_cons_of_mem _ hq') he, ?_⟩)
        simp only [ne_eq, Bool.not_eq_true', beq_eq_false_iff_ne]
        exact fun he => hx he.symm

/-- A candidate in `[2, n)` whose offset no other candidate has is a cell of the frame. -/
theorem mem_frameB {n : ℕ} {L : List (ℕ × E)} {q : ℕ × E} (hq : q ∈ L) (h2 : 2 ≤ q.1) (hn : q.1 < n)
    (hu : ∀ q' ∈ L, q'.1 = q.1 → q' = q) : q ∈ frameB n L :=
  mem_dedupB (List.mem_filter.mpr ⟨hq, by simp [h2, hn]⟩) fun q' hq' he =>
    hu q' (List.mem_filter.mp hq').1 he

/-- Every cell of a frame is a candidate in `[2, n)`. -/
theorem frameB_sub {n : ℕ} {L : List (ℕ × E)} {q : ℕ × E} (hq : q ∈ frameB n L) :
    q ∈ L ∧ 2 ≤ q.1 ∧ q.1 < n := by
  have key : ∀ {M : List (ℕ × E)} {q : ℕ × E}, q ∈ dedupB M → q ∈ M := by
    intro M
    induction M with
    | nil => intro q h; simp [dedupB] at h
    | cons x xs ih =>
      intro q h
      rw [dedupB] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih (List.mem_filter.mp h).1)
  have := List.mem_filter.mp (key hq)
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at this
  exact ⟨this.1, this.2.1, this.2.2⟩

section Cells

variable {κ₀ : ℕ} {W : World κ₀}

theorem cellsB_node {I : Memory.Inst} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (ht : I.t = .node f σ bufs kids) {tf : TracedFn} {pf : Placed} (hf : W.fnOf f = some (tf, pf)) :
    W.cellsB I = frameB (W.fsB f) ((List.range pf.fn.frameSize).map
      (fun n => (n, (W.famB tf pf I.fp I.kidFps I.hdr σ).Ψ n)) ++
        (if f = "main" then W.tableB else [])) := by
  unfold World.cellsB
  rw [ht]
  simp only [hf]

theorem cellsB_phantom {I : Memory.Inst} {f : String} {σ : Val} (ht : I.t = .phantom f σ) {tf : TracedFn}
    {pf : Placed} (hf : W.fnOf f = some (tf, pf)) :
    W.cellsB I = frameB (W.fsB f) (tf.core.params.mapIdx (fun k v => (2 + k, σ v)) ++
      (if ((loopTable W.p)[f]?).any (·.registered) then
        [(2 + tf.core.params.length, ofK (addressOfIndex I.fp))] else [])) := by
  unfold World.cellsB
  rw [ht]
  simp only [hf]

theorem hdrB_node {I : Memory.Inst} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (ht : I.t = .node f σ bufs kids) {tf : TracedFn} {pf : Placed} (hf : W.fnOf f = some (tf, pf))
    (k : ℕ) (hK : IsInK ((W.famB tf pf I.fp I.kidFps I.hdr σ).kh k).1 ∧
      IsInK ((W.famB tf pf I.fp I.kidFps I.hdr σ).kh k).2) :
    W.hdrB I k = (W.famB tf pf I.fp I.kidFps I.hdr σ).kh k := by
  unfold World.hdrB World.wordsB
  rw [ht]
  simp only [hf, Option.map_some]
  simp only [hK.1, hK.2, and_self, ↓reduceIte]

theorem isInK_zeroB : IsInK (0 : E) := (isInK_iff _).mpr ⟨0, (map_zero (algebraMap K E)).symm⟩

/-- Every callee header is of `K`. -/
theorem hdrB_K (I : Memory.Inst) (k : ℕ) : IsInK (W.hdrB I k).1 ∧ IsInK (W.hdrB I k).2 := by
  unfold World.hdrB
  split
  · split
    · next h => exact h
    · exact ⟨isInK_zeroB, isInK_zeroB⟩
  · exact ⟨isInK_zeroB, isInK_zeroB⟩

end Cells

/-! ## The jump tables -/

section Jt

variable {κ₀ : ℕ} {W : World κ₀}

theorem mem_tableB {s : ℕ} {k : KVal} {w : E} (hs : W.slots[s]? = some k)
    (hw : SlotWord W.layout k = some w) : (W.layout.tablesBase + s, w) ∈ W.tableB := by
  unfold World.tableB
  refine List.mem_filterMap.mpr ⟨(k, s), ?_, by simp [hw]⟩
  obtain ⟨hlt, hk⟩ := Array.getElem?_eq_some_iff.mp hs
  refine List.mem_iff_getElem.mpr ⟨s, by simpa using hlt, ?_⟩
  simp [hk]

theorem tableB_off {q : ℕ × E} (hq : q ∈ W.tableB) :
    ∃ s < W.slots.size, q.1 = W.layout.tablesBase + s ∧ ∀ q' ∈ W.tableB, q'.1 = q.1 → q' = q := by
  have key : ∀ {q : ℕ × E}, q ∈ W.tableB → ∃ s k, W.slots[s]? = some k ∧
      SlotWord W.layout k = some q.2 ∧ q.1 = W.layout.tablesBase + s := by
    intro q hq
    unfold World.tableB at hq
    obtain ⟨⟨k, s⟩, hm, he⟩ := List.mem_filterMap.mp hq
    obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp hm
    simp only [List.getElem_zipIdx, Array.getElem_toList, Prod.mk.injEq] at hie
    obtain ⟨rfl, rfl⟩ := hie
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp he
    refine ⟨i, W.slots[i]'(by simpa using hi), by simp, hw, by simp⟩
  obtain ⟨s, k, hs, hw, he⟩ := key hq
  refine ⟨s, (Array.getElem?_eq_some_iff.mp hs).1, he, fun q' hq' he' => ?_⟩
  obtain ⟨s', k', hs', hw', he''⟩ := key hq'
  obtain rfl : s' = s := by omega
  obtain rfl : k' = k := Option.some.inj (hs'.symm.trans hs)
  have h2 : q'.2 = q.2 := Option.some.inj (hw'.symm.trans hw)
  exact Prod.ext (by omega) h2

/-- **The jump tables are written** on the honest memory of a run of `main`. -/
theorem jt_honestB (hW : W.Compiled) {hdr : E × E} {rd : Reader} {T : Tree} (hT : T.name = "main")
    (hH : HonestAt W.core W.fsB W.hdrB W.cellsB hdr T W.cellB rd [] []) :
    JTHolds (W.honestB hdr T) W.layout W.slots := by
  intro s k w hs hw
  obtain ⟨I, hI, hIt, hfp, -⟩ := root_inst (P := W.core) (fs := W.fsB) (H := W.hdrB) (hdr := hdr) (T := T)
  have hv := hH.toHonest.valid
  obtain ⟨σ, bufs, kids, hTn⟩ : ∃ σ bufs kids, T = .node "main" σ bufs kids := by
    cases T with
    | phantom f σ => exact hv.elim
    | node f σ bufs kids =>
      simp only [Tree.name] at hT
      subst hT
      exact ⟨σ, bufs, kids, rfl⟩
  rw [hTn] at hv
  obtain ⟨fn, hf, -⟩ := hv
  obtain ⟨tf, htf, rfl, hnm⟩ := core_find hf
  obtain ⟨pf, hfo, hpa⟩ := fnOf_of_mem hW htf
  rw [hnm] at hfo
  obtain ⟨hbase, hfs⟩ := fsB_main hW hpa hnm
  have hsz := (placed_size hW htf hpa).1
  have hslt := (Array.getElem?_eq_some_iff.mp hs).1
  have hq := mem_tableB hs hw
  have hc : (W.layout.tablesBase + s, w) ∈ W.cellsB I := by
    have he : (if "main" = "main" then W.tableB else ([] : List (ℕ × E))) = W.tableB := by simp
    rw [cellsB_node (hIt.trans hTn) hfo, he]
    refine mem_frameB (List.mem_append_right _ hq) (by simp only; omega) (by simp only; omega)
      fun q' hq' he => ?_
    rcases List.mem_append.mp hq' with hq' | hq'
    · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hq'
      simp only [List.mem_range] at hn
      simp only at he
      omega
    · obtain ⟨-, -, -, hu⟩ := tableB_off hq
      exact hu q' hq' he
  have := hH.toHonest.read_C hI hc
  rwa [hfp, show (addressOfIndex 0 : K) = 1 by rw [addressOfIndex, pow_zero], one_mul] at this

end Jt

end
end LeanVM.Guest.Backend.Complete
