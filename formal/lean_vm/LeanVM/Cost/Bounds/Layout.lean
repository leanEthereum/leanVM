module

public import LeanVM.Cost.Bounds.Replay
public import LeanVM.Cost.Bounds.Runner
import all Statement.LeanVmVerifier
import all LeanVM.Protocol.Extraction.Fast.AfterRoot

/-!
# Bounds: the layouts the replay returns

The runner's bounds (`Bounds/Runner.lean`) assume of the layout what
`buildLayoutLite`'s checks give: `κ = logMemory ≤ 30`, `logBytecode ≤ 30`, at most six tables of
log-height at most `30`, and every placement's offset a word. Here they are proved for every
layout `buildLayoutLite` returns:

* `stackOffsets_le`: blocks of log-size at most `s`: every offset at most `2^s·n`, `n` blocks
  (the running total, sharper than `stackOffsets_bounds`' `2^63`);
* `placementsOf_index_lt`: at most `165` columns of log-size at most `40` (`columnKappas`: `30`
  but `q_keccak`'s `36`): every placement's offset below `2^48`: a block's offset is at most
  `165·2^40`, a Keccak slot's `q_keccak`'s offset plus a slot (below `64`) of `2^κ` words;
* **`buildLayoutLite_facts`**: the layout's fields (`LayoutFacts`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters LeanVM.Semantics
open LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Protocol.Verifier

public section

/-! ## The offsets -/

/-- `stackOffsets`' fold: each offset at most the running total, the total grown by at most `2^s`
per block. -/
theorem offsetsFold_le (sizes : List ℕ) (s : ℕ) (hs : ∀ i, sizes.getD i 0 ≤ s) :
    ∀ (order : List ℕ) (acc : List ℕ × ℕ), (∀ x ∈ acc.1, x ≤ acc.2) →
      (∀ x ∈ (order.foldl (fun (acc : List ℕ × ℕ) i ↦
          (acc.1.set i acc.2, acc.2 + 2 ^ sizes.getD i 0)) acc).1,
        x ≤ (order.foldl (fun (acc : List ℕ × ℕ) i ↦
          (acc.1.set i acc.2, acc.2 + 2 ^ sizes.getD i 0)) acc).2) ∧
      (order.foldl (fun (acc : List ℕ × ℕ) i ↦
          (acc.1.set i acc.2, acc.2 + 2 ^ sizes.getD i 0)) acc).2 ≤ acc.2 + 2 ^ s * order.length := by
  intro order
  induction order with
  | nil => intro acc h; exact ⟨h, by simp⟩
  | cons i order ih =>
    intro acc h
    have hp : 2 ^ sizes.getD i 0 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (hs i)
    have hp0 : 0 < 2 ^ sizes.getD i 0 := Nat.two_pow_pos _
    obtain ⟨h1, h2⟩ := ih (acc.1.set i acc.2, acc.2 + 2 ^ sizes.getD i 0) (fun x hx ↦ by
      rcases List.mem_or_eq_of_mem_set hx with hx | rfl
      · have := h x hx; dsimp only; omega
      · dsimp only; omega)
    refine ⟨h1, ?_⟩
    simp only [List.foldl_cons, List.length_cons, Nat.mul_succ] at h2 ⊢
    omega

/-- **The stack's offsets**: blocks of log-size at most `s`: every offset at most `2^s·n`. -/
theorem stackOffsets_le (sizes : List ℕ) (s : ℕ) (hs : ∀ x ∈ sizes, x ≤ s) :
    ∀ x ∈ (stackOffsets sizes).1, x ≤ 2 ^ s * sizes.length := by
  have hs' : ∀ i, sizes.getD i 0 ≤ s := fun i ↦ by
    rcases getD_mem_or sizes i 0 with h | h
    · exact hs _ h
    · rw [h]; omega
  unfold stackOffsets
  dsimp only
  intro x hx
  obtain ⟨h1, h2⟩ := offsetsFold_le sizes s hs' ((List.range sizes.length).mergeSort fun i j ↦
      decide (sizes.getD j 0 < sizes.getD i 0) ||
        (decide (sizes.getD i 0 = sizes.getD j 0) && decide (i ≤ j)))
    (List.replicate sizes.length 0, 0) (fun y hy ↦ by simp [List.eq_of_mem_replicate hy])
  have := h1 x hx
  simp only [List.length_mergeSort, List.length_range, Nat.zero_add] at h2
  omega

/-- **The placements' offsets**: at most `165` columns of log-size at most `40`: every placement's
offset below `2^48`. -/
theorem placementsOf_index_lt (kappas : List ℕ) (hn : kappas.length ≤ 165)
    (hk : ∀ x ∈ kappas, x ≤ 40) :
    ∀ o ∈ (placementsOf kappas).1, ∀ p : Placement, o = some p → p.index < 2 ^ 48 := by
  unfold placementsOf
  dsimp only
  set cols := (List.range kappas.length).filter fun c ↦
    decide ((keccakSlot c).isNone = true ∧ c ∉ keccakOutputColumns)
  have hcl : cols.length ≤ 165 := (List.length_filter_le _ _).trans (by simp; omega)
  have hoff := stackOffsets_le (cols.map (kappas.getD · 0)) 40 (fun x hx ↦ by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    rcases getD_mem_or kappas i 0 with h | h
    · exact hk _ h
    · rw [h]; omega)
  generalize stackOffsets (cols.map (kappas.getD · 0)) = so at hoff
  obtain ⟨offs, tl⟩ := so
  simp only [List.length_map] at hoff
  have hT : 2 ^ 40 * cols.length ≤ 165 * 2 ^ 40 := by omega
  have hget : ∀ c, offs.getD (cols.idxOf c) 0 ≤ 165 * 2 ^ 40 := fun c ↦ by
    rcases getD_mem_or offs (cols.idxOf c) 0 with h | h
    · have := hoff _ h; omega
    · rw [h]; omega
  intro o ho p hp
  obtain ⟨⟨kappa, column⟩, hm, rfl⟩ := List.mem_map.1 ho
  have hkap : kappa ≤ 40 := hk _ (List.fst_mem_of_mem_zipIdx hm)
  dsimp only at hp
  generalize hks : keccakSlot column = ks at hp
  cases ks with
  | some slot =>
    obtain rfl := Option.some.inj hp.symm
    have hslot := keccakSlot_lt hks
    have h1 : slot * 2 ^ kappa ≤ 63 * 2 ^ 40 :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) hkap)
    have := hget qkeccak
    show offs.getD (cols.idxOf qkeccak) 0 + slot * 2 ^ kappa < 2 ^ 48
    omega
  | none =>
    dsimp only at hp
    split_ifs at hp
    obtain rfl := Option.some.inj hp.symm
    have := hget column
    show offs.getD (cols.idxOf column) 0 < 2 ^ 48
    omega

/-! ## The layouts -/

/-- What the runner's bound assumes of a layout. -/
structure LayoutFacts (L : LayoutLite) : Prop where
  logMemory_ge : 1 ≤ L.logMemory
  logMemory_le : L.logMemory ≤ 30
  logBytecode_le : L.logBytecode ≤ 30
  heights_length : L.tableLogHeights.length ≤ 6
  heights_le : ∀ h ∈ L.tableLogHeights, h ≤ 30
  index_lt : ∀ c, (L.placement c).index < 2 ^ 48

theorem LayoutFacts.index_lt_word {L : LayoutLite} (h : LayoutFacts L) (c : ℕ) :
    (L.placement c).index < 2 ^ 63 :=
  lt_trans (h.index_lt c) (by norm_num)

/-- **`buildLayoutLite`'s layouts** meet `LayoutFacts`, and the bytecode has `2^(ℓ + 4)` words. -/
theorem buildLayoutLite_facts {bytecode : List K} {logMemory : ℕ} {tableRows : List ℕ}
    {L : LayoutLite} (h : buildLayoutLite bytecode logMemory tableRows = some L) :
    LayoutFacts L ∧ log2Strict bytecode.length = some (L.logBytecode + busBits) := by
  unfold buildLayoutLite at h
  split at h
  · simp at h
  · rename_i val hval
    split_ifs at h with hc
    obtain rfl := Option.some.inj h
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hc
    have hr30 : ∀ r ∈ tableRows, r ≤ 2 ^ 30 := fun r hr' ↦ by
      have := List.all_eq_true.1 c4 r hr'; simpa using this
    obtain ⟨hhl, hhm⟩ := heights_facts tableRows hr30
    set heights := List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) tableRows
      tableLogFloors
    have hhD : ∀ i, heights.getD i 0 ≤ 30 := fun i ↦ by
      rcases getD_mem_or heights i 0 with h' | h'
      · exact hhm _ h'
      · rw [h']; omega
    obtain ⟨hkl, hkm⟩ := columnKappas_facts logMemory (val - busBits) heights c3
      (by simp only [busBits] at c5 ⊢; omega) hhD
    have hidx := placementsOf_index_lt (columnKappas logMemory (val - busBits) heights)
      (by omega) hkm
    refine ⟨⟨c2, c3, by simp only [busBits] at c5 ⊢; omega, hhl, hhm, fun c ↦ ?_⟩, ?_⟩
    · show (((placementsOf (columnKappas logMemory (val - busBits) heights)).1.getD c
        none).getD default).index < 2 ^ 48
      rcases getD_mem_or (placementsOf (columnKappas logMemory (val - busBits) heights)).1 c
        none with hm | hm
      · generalize hq : (placementsOf (columnKappas logMemory (val - busBits) heights)).1.getD c
          none = q at hm
        cases q with
        | none => show (0 : ℕ) < 2 ^ 48; norm_num
        | some p => exact hidx _ hm p rfl
      · rw [hm]; show (0 : ℕ) < 2 ^ 48; norm_num
    · show log2Strict bytecode.length = some (val - busBits + busBits)
      rw [Nat.sub_add_cancel c1]; exact hval

end

end LeanVM.Cost.Bounds
