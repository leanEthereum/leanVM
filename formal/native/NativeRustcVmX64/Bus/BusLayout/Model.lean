module

public import NativeRustcVmX64.Spec.Bus
public import NativeVm.Math.Layout

/-!
# `bus_layout`'s model side (x86-64; the AArch64 proof's, arch-independent)

`bus_layout` lays out the sizes `szs` (the framework's, then each block's owner's log-height) with
`stack_offsets` (`so`); placement `j` is `pl j`. `busLayout` of the framework sizes and the blocks is
then the depth and the placements split at the framework's count (`busLayout_depth`,
`busLayout_framework`, `busLayout_tables`). The sizes are at most `30`, at most `54` of them, so
`stack_offsets` succeeds (`offsetsFit`) and every offset and the depth fit a word.
-/

namespace NativeRustcVmX64.Bus.BusLayout

open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout LeanVM.Protocol.Verifier

@[expose] public section

/-- The sizes `bus_layout` lays out: the framework's, then each block's owner's log-height. -/
def szs (fw : Array Nat) (h : Array Nat) (bl : List NativeRustcVm.Data.Block) : List Nat :=
  fw.toList ++ bl.map fun b ↦ h.getD b.owner 0

/-- The offsets and the depth. -/
abbrev so (fw h : Array Nat) (bl : List NativeRustcVm.Data.Block) : Array Nat × Nat :=
  stackOffsets (szs fw h bl).toArray

/-- Placement `j`. -/
def pl (fw h : Array Nat) (bl : List NativeRustcVm.Data.Block) (j : Nat) : Placement :=
  ⟨(szs fw h bl).getD j 0, (so fw h bl).1.getD j 0⟩

theorem length_szs (fw h : Array Nat) (bl : List NativeRustcVm.Data.Block) :
    (szs fw h bl).length = fw.size + bl.length := by
  simp [szs]

theorem sizes_eq (fw h rows : Array Nat) (bl : List NativeRustcVm.Data.Block) :
    fw ++ (bl.map (blockW h rows)).toArray.map (·.logRows) = (szs fw h bl).toArray := by
  apply Array.ext'
  simp [szs, blockW]

theorem size_so (fw h : Array Nat) (bl : List NativeRustcVm.Data.Block) :
    (so fw h bl).1.size = fw.size + bl.length := by
  rw [(NativeVm.Math.Layout.stackOffsets_spec _).2.1]
  simp [length_szs]

theorem busLayout_depth (fw h rows : Array Nat) (bl : List NativeRustcVm.Data.Block) :
    (busLayout fw (bl.map (blockW h rows)).toArray).depth = (so fw h bl).2 := by
  simp only [NativeVm.Model.busLayout, sizes_eq]

theorem busLayout_framework (fw h rows : Array Nat) (bl : List NativeRustcVm.Data.Block) :
    (busLayout fw (bl.map (blockW h rows)).toArray).framework =
      ((List.range fw.size).map (pl fw h bl)).toArray := by
  simp only [NativeVm.Model.busLayout, sizes_eq]
  apply Array.ext
  · simp [size_so, length_szs]
  · intro i h1 h2
    simp only [List.size_toArray, List.length_map, List.length_range] at h2
    simp only [Array.getElem_extract, Array.getElem_zipWith, List.getElem_toArray,
      List.getElem_map, List.getElem_range, pl]
    simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]
    constructor
    · rw [List.getElem?_eq_getElem (by rw [length_szs]; omega)]; rfl
    · rw [Array.getElem?_eq_getElem (by rw [size_so]; omega)]; rfl

theorem busLayout_tables (fw h rows : Array Nat) (bl : List NativeRustcVm.Data.Block) :
    (busLayout fw (bl.map (blockW h rows)).toArray).tables =
      ((List.range bl.length).map fun j ↦ pl fw h bl (fw.size + j)).toArray := by
  simp only [NativeVm.Model.busLayout, sizes_eq]
  apply Array.ext
  · simp [size_so, length_szs]
  · intro i h1 h2
    simp only [List.size_toArray, List.length_map, List.length_range] at h2
    simp only [Array.getElem_extract, Array.getElem_zipWith, List.getElem_toArray,
      List.getElem_map, List.getElem_range, pl]
    simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]
    constructor
    · rw [List.getElem?_eq_getElem (by rw [length_szs]; omega)]; rfl
    · rw [Array.getElem?_eq_getElem (by rw [size_so]; omega)]; rfl

/-! ## Bounds -/

theorem szs_le {fw h : Array Nat} {bl : List NativeRustcVm.Data.Block} (hfw : ∀ s ∈ fw, s ≤ 30)
    (hh : ∀ s ∈ h, s ≤ 30) : ∀ s ∈ szs fw h bl, s ≤ 30 := by
  intro s hs
  simp only [szs, List.mem_append, Array.mem_toList_iff, List.mem_map] at hs
  rcases hs with hs | ⟨b, -, rfl⟩
  · exact hfw s hs
  · rw [Array.getD_eq_getD_getElem?]
    cases e : h[b.owner]? with
    | none => simp
    | some x => exact hh x (Array.mem_of_getElem? e)

theorem sum_pow_le {l : List Nat} (hl : ∀ s ∈ l, s ≤ 30) :
    (l.map (2 ^ ·)).sum ≤ l.length * 2 ^ 30 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := ih fun s hs ↦ hl s (List.mem_cons_of_mem _ hs)
    have h2 : 2 ^ x ≤ 2 ^ 30 := Nat.pow_le_pow_right (by omega) (hl x List.mem_cons_self)
    rw [Nat.succ_mul]
    omega

theorem offsetsFit {l : List Nat} (hl : ∀ s ∈ l, s ≤ 30) (hn : l.length ≤ 54) :
    OffsetsFit l.toArray := by
  refine ⟨fun s hs ↦ by have := hl s (by simpa using hs); omega, ?_⟩
  have := sum_pow_le hl
  have : l.length * 2 ^ 30 ≤ 54 * 2 ^ 30 := Nat.mul_le_mul_right _ hn
  rw [List.toList_toArray]
  omega

/-- The sizes' powers, in order of the indices. -/
theorem sum_range_pow {l : List Nat} :
    ((List.range l.toArray.size).map (2 ^ l.toArray.getD · 0)).sum = (l.map (2 ^ ·)).sum := by
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [Array.getD_eq_getD_getElem?, List.getElem?_eq_getElem (by simpa using h1)]

theorem offset_le {l : List Nat} (j : Nat) :
    (stackOffsets l.toArray).1.getD j 0 ≤ (l.map (2 ^ ·)).sum := by
  obtain ⟨-, hsz, hget⟩ := NativeVm.Math.Layout.stackOffsets_spec l.toArray
  by_cases hj : j < l.toArray.size
  · rw [hget j hj, ← sum_range_pow]
    apply List.Sublist.sum_le_sum (List.filter_sublist.map _) (fun _ _ ↦ Nat.zero_le _)
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    simp

theorem depth_le {l : List Nat} (hl : ∀ s ∈ l, s ≤ 30) (hn : l.length ≤ 54) :
    (stackOffsets l.toArray).2 ≤ 64 := by
  rw [(NativeVm.Math.Layout.stackOffsets_spec _).1, sum_range_pow]
  have := sum_pow_le hl
  have : l.length * 2 ^ 30 ≤ 54 * 2 ^ 30 := Nat.mul_le_mul_right _ hn
  exact NativeVm.Math.Layout.bitLength_le (by omega)

/-- `n &&& 62` for fewer than `64`: the even part. -/
theorem and62 : ∀ n < 64, n &&& 62 = 2 * (n / 2) := by decide

end

end NativeRustcVmX64.Bus.BusLayout
