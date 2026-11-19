module

public import NativeVm.Equiv.KeccakRmfe
public import NativeVm.Equiv.Field
public import NativeVm.Equiv.LayoutSpec

/-!
# Phase 6's pure steps: the model's words as the statement's values

The functions of `NativeVm/Model/KeccakGkr.lean` that read no transcript, each equal to the
statement's of the same name through `EW.toE` (an array of words read as the list of its elements'
values): `keccakLinearTranspose_eq`, `keccakInstanceWeights_eq`, `keccakSlotWeights_eq`,
`keccakFirstClaim_eq`, the fold of `keccakOpen`'s rows (`openRows_eq`), and the layer's
`projected` and `iota` sums (`projected_eq`, `iota_eq`). `KeccakClaimW.toSpec` reads a claim.

Every proof maps `EW.toE` through the loops (`List.foldl_hom`, `List.map_map`, the arrays' `toList`
lemmas) and never unfolds a loop bound: nothing here evaluates the constants `1600`, `25`, `64`.
-/

public section

namespace NativeVm.Equiv.Keccak

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol

/-- A claim as the statement's `KeccakClaim`. -/
@[expose] def _root_.NativeVm.Model.KeccakClaimW.toSpec (c : KeccakClaimW) : Verifier.KeccakClaim :=
  ⟨c.value.toE, c.mu.toList.map EW.toE, c.point.toList.map EW.toE, c.weights.toList.map EW.toE⟩

/-! ## Arrays of words -/

theorem toE_getD (a : Array EW) (i : ℕ) : (a.getD i 0).toE = (a.toList.map EW.toE).getD i 0 := by
  simp only [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_map,
    Array.getElem?_toList]
  cases a[i]? <;> simp [EW.toE_zero]

theorem getD_map_toE (a : Array EW) (i : ℕ) : (a.map EW.toE).getD i 0 = (a.getD i 0).toE := by
  rw [toE_getD]
  simp only [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_map,
    List.getElem?_map, Array.getElem?_toList]

theorem toList_extract_size {α : Type} (a : Array α) (i : ℕ) :
    (a.extract i a.size).toList = a.toList.drop i := by
  rw [Array.toList_extract, List.extract_eq_take_drop, List.take_of_length_le]
  simp

theorem toList_extract_zero {α : Type} (a : Array α) (n : ℕ) :
    (a.extract 0 n).toList = a.toList.take n := by
  rw [Array.toList_extract, List.extract_eq_take_drop]
  simp

theorem getD_toArray {α : Type} (l : List α) (i : ℕ) (d : α) : l.toArray.getD i d = l.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-! ## `keccakLinearTranspose` -/

theorem keccakRhoW_getD (lane : ℕ) : keccakRhoW.getD lane 0 = keccakRho.getD lane 0 :=
  getD_toArray _ _ _

theorem keccakLinearTranspose_eq (w : Array EW) :
    (Model.keccakLinearTranspose w).toList.map EW.toE =
      Verifier.keccakLinearTranspose (w.toList.map EW.toE) := by
  unfold Model.keccakLinearTranspose Verifier.keccakLinearTranspose
  dsimp only
  -- `g`: the statement's is the model's, read.
  have hw : (w.toList.map EW.toE).toArray = w.map EW.toE := by
    rw [← Array.toList_inj]; simp
  rw [hw]
  generalize hgW : (List.range 25).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
    g.setIfInBounds (64 * lane + z)
      (w.getD (64 * keccakPi lane + (z + keccakRhoW.getD lane 0) % 64) 0)) g)
    (Array.replicate Verifier.keccakBits 0) = gW
  have hinit : Array.replicate Verifier.keccakBits (0 : E) =
      (Array.replicate Verifier.keccakBits (0 : EW)).map EW.toE := by
    rw [Array.map_replicate, EW.toE_zero]
  have hg : (List.range 25).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
      g.setIfInBounds (64 * lane + z)
        ((w.map EW.toE).getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
      (Array.replicate Verifier.keccakBits (0 : E)) = gW.map EW.toE := by
    rw [hinit, ← hgW]
    refine List.foldl_hom (fun g : Array EW ↦ g.map EW.toE) fun g lane ↦
      List.foldl_hom (fun g : Array EW ↦ g.map EW.toE) fun g z ↦ ?_
    rw [Array.map_setIfInBounds, getD_map_toE, keccakRhoW_getD]
  rw [hg]
  generalize hcW : ((Array.range 5).flatMap fun x ↦ (Array.range 64).map fun z ↦
    sumE ((Array.range 5).map fun y ↦ gW.getD (64 * (x + 5 * y) + z) 0)) = cW
  have hc : ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
      Verifier.sumE ((List.range 5).map fun y ↦
        (gW.map EW.toE).getD (64 * (x + 5 * y) + z) 0)).toArray = cW.map EW.toE := by
    rw [← hcW, ← Array.toList_inj]
    simp only [Array.toList_map, Array.toList_flatMap, Array.toList_range,
      List.map_flatMap, List.map_map, Function.comp_def, toE_sumE, getD_map_toE]
  rw [hc]
  simp only [Array.toList_map, Array.toList_flatMap, Array.toList_range, List.map_flatMap,
    List.map_map, Function.comp_def, EW.toE_add, getD_map_toE]

/-! ## `keccakInstanceWeights` -/

theorem keccakInstanceWeights_eq (s : EW) :
    (Model.keccakInstanceWeights s).toList.map EW.toE = Verifier.keccakInstanceWeights s.toE := by
  unfold Model.keccakInstanceWeights Verifier.keccakInstanceWeights rmfeEmbedW
  simp only [Array.toList_map, List.map_map]
  refine List.map_congr_left fun e _ ↦ ?_
  simp only [Function.comp_apply, toE_sumE, Array.toList_filterMap, Array.toList_range,
    List.map_filterMap]
  congr 1
  refine List.filterMap_congr fun b hb ↦ ?_
  have hb : b < 64 := by
    have := List.mem_range.1 hb; simp only [Verifier.embedBits] at this; omega
  rw [testBitW_toUInt64 _ hb]
  split
  · rw [Option.map_some, toE_getD, toList_map_powers]
  · rfl

/-! ## `keccakSlotWeights` -/

theorem List.map_modify' {α β : Type} (g : α → β) {f : α → α} {f' : β → β}
    (h : ∀ x, g (f x) = f' (g x)) (l : List α) (i : ℕ) :
    (l.modify i f).map g = (l.map g).modify i f' := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_map, List.getElem_modify]
    split <;> simp [h]

theorem eqKernel_drop (point : Array EW) (n : ℕ) :
    Verifier.eqKernel ((point.toList.map EW.toE).drop n) =
      (Model.eqKernel (point.extract n point.size)).toList.map EW.toE := by
  rw [toList_map_eqKernel, toList_extract_size, List.map_drop]

theorem toArray_map_toE (a : Array EW) : (a.toList.map EW.toE).toArray = a.map EW.toE := by
  rw [← Array.toList_inj]; simp

theorem keccakSlotWeights_eq (logSteps : ℕ) (claim : KeccakClaimW) (first count : ℕ) :
    (Model.keccakSlotWeights logSteps claim first count).toList.map (fun r ↦ r.toList.map EW.toE) =
      Verifier.keccakSlotWeights logSteps claim.toSpec first count := by
  unfold Model.keccakSlotWeights Verifier.keccakSlotWeights KeccakClaimW.toSpec
  dsimp only
  rw [eqKernel_drop, toArray_map_toE]
  generalize Model.eqKernel (claim.point.extract (logSteps - 4) claim.point.size) = seg
  generalize hW : (List.range count).foldl (fun rows segment ↦
    (List.range Verifier.keccakBits).foldl (fun rows j ↦
      rows.modify (25 * (first + segment) + j / 64) fun row ↦
        row.setIfInBounds (j % 64) (seg.getD segment 0 * claim.weights.getD j 0)) rows)
    (Array.replicate (2 ^ Verifier.qkeccakSlotBits) (Array.replicate 64 0)) = rowsW
  have hinit : Array.replicate (2 ^ Verifier.qkeccakSlotBits) (Array.replicate 64 (0 : E)) =
      (Array.replicate (2 ^ Verifier.qkeccakSlotBits) (Array.replicate 64 (0 : EW))).map
        (·.map EW.toE) := by
    simp only [Array.map_replicate, EW.toE_zero]
  have hS : (List.range count).foldl (fun rows segment ↦
      (List.range Verifier.keccakBits).foldl (fun rows j ↦
        rows.modify (25 * (first + segment) + j / 64) fun row ↦
          row.setIfInBounds (j % 64)
            ((seg.toList.map EW.toE).getD segment 0 * (claim.weights.map EW.toE).getD j 0)) rows)
      (Array.replicate (2 ^ Verifier.qkeccakSlotBits) (Array.replicate 64 (0 : E))) =
      rowsW.map (·.map EW.toE) := by
    rw [hinit, ← hW]
    apply List.foldl_hom
    intro rows segment
    apply List.foldl_hom
    intro rows j
    rw [← Array.toList_inj, Array.toList_modify, Array.toList_map, Array.toList_map,
      Array.toList_modify, List.map_modify' (fun row : Array EW ↦ row.map EW.toE)]
    intro row
    rw [Array.map_setIfInBounds, EW.toE_mul, getD_map_toE, toE_getD]
  rw [hS]
  simp only [Array.toList_map, List.map_map, Function.comp_def]

/-! ## `keccakOpen`'s rows -/

theorem getD_rows (rows : Array (Array EW)) (k : ℕ) :
    (rows.toList.map fun r ↦ r.toList.map EW.toE).getD k [] =
      (rows.getD k #[]).toList.map EW.toE := by
  simp only [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_map,
    Array.getElem?_toList]
  cases rows[k]? <;> rfl

/-- The fold of `keccakOpen`'s rows by the slot's challenges. -/
theorem openRows_eq (slot : Array EW) (rows : Array (Array EW)) :
    (slot.foldl (fun rows challenge ↦ (Array.range (rows.size / 2)).map fun i ↦
      Array.zipWith (fun lo hi ↦ lo + challenge * (lo + hi)) (rows.getD (2 * i) #[])
        (rows.getD (2 * i + 1) #[])) rows).toList.map (fun r ↦ r.toList.map EW.toE) =
    (slot.toList.map EW.toE).foldl (fun rows challenge ↦
      (List.range (rows.length / 2)).map fun i ↦
        List.zipWith (fun lo hi ↦ lo + challenge * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) [])) (rows.toList.map fun r ↦ r.toList.map EW.toE) := by
  rw [← Array.foldl_toList, List.foldl_map]
  refine (List.foldl_hom (fun rows : Array (Array EW) ↦ rows.toList.map fun r ↦
    r.toList.map EW.toE) fun rows c ↦ ?_).symm
  simp only [List.length_map, Array.length_toList, getD_rows, Array.toList_map, Array.toList_range,
    List.map_map, Function.comp_def, Array.toList_zipWith, List.map_zipWith, List.zipWith_map,
    EW.toE_add, EW.toE_mul]

/-! ## `keccakFirstClaim` -/

theorem toE_ofK_shift {k : ℕ} (hk : k < 64) :
    (EW.ofK ((1 : UInt64) <<< k.toUInt64)).toE = Verifier.eOfNat (2 ^ k) := by
  have h : (1 : UInt64) <<< k.toUInt64 = (2 ^ k).toUInt64 := by
    rw [← UInt64.toNat_inj, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk]
    simp [Nat.shiftLeft_eq]
  rw [h, ← EW.toE_ofNat]
  rfl

theorem keccakFirstClaim_eq (inst segment lanePoint output : Array EW) (committed : EW) :
    (Model.keccakFirstClaim inst segment lanePoint output committed).toSpec =
      Verifier.keccakFirstClaim (inst.toList.map EW.toE) (segment.toList.map EW.toE)
        (lanePoint.toList.map EW.toE) (output.toList.map EW.toE) committed.toE := by
  unfold Model.keccakFirstClaim Verifier.keccakFirstClaim KeccakClaimW.toSpec
  dsimp only
  simp only [Verifier.KeccakClaim.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [EW.toE_add, EW.toE_mul, toE_getD, toList_map_eqKernel, toE_dot, toList_extract_zero,
      List.map_take, toList_map_eqKernel]
  · rw [toList_map_eqKernel, toList_extract_zero, List.map_take]
  · rw [Array.toList_append, List.map_append, toList_extract_size, List.map_drop]
  · rw [Array.toList_map, Array.toList_range, List.map_map]
    refine List.map_congr_left fun j _ ↦ ?_
    rw [Function.comp_apply, EW.toE_mul, toE_getD, toList_map_eqKernel,
      toE_ofK_shift (Nat.mod_lt _ (by decide))]

/-! ## The layer's sums -/

/-- The layer's `projected`, its pattern-matching lambdas read through the pair's projections (as
`dsimp` leaves them). -/
theorem projected_eq (mu product : Array EW) :
    (sumE ((Array.range Verifier.productBits).map fun c ↦
      sumE ((mu.zip rmfeProjectW).filterMap fun x ↦
        if testBitW x.2 c then some x.1 else none) * product.getD c 0)).toE =
    Verifier.sumE ((List.range Verifier.productBits).map fun c ↦
      Verifier.sumE ((List.zip (mu.toList.map EW.toE) Verifier.rmfeProject).filterMap
        fun x ↦ if x.2.testBit c then some x.1 else none) *
          (product.toList.map EW.toE).getD c 0) := by
  rw [toE_sumE, Array.toList_map, Array.toList_range, List.map_map]
  congr 1
  refine List.map_congr_left fun c hc ↦ ?_
  have hc : c < 64 := by
    have := List.mem_range.1 hc; simp only [Verifier.productBits, Verifier.embedBits] at this
    omega
  rw [Function.comp_apply, EW.toE_mul, toE_getD, toE_sumE, Array.toList_filterMap,
    Array.toList_zip, rmfeProjectW, Array.toList_map, List.zip_map_right, List.zip_map_left,
    List.map_filterMap, List.filterMap_map, List.filterMap_map]
  congr 2
  refine List.filterMap_congr fun ⟨m, mask⟩ _ ↦ ?_
  simp only [Function.comp_apply, Prod.map, id, testBitW_toUInt64 _ hc]
  split <;> rfl

theorem iota_eq (step : ℕ) (segments weights : Array EW) :
    (sumE ((Array.range Verifier.keccakSegments).map fun segment ↦
      segments.getD segment 0 * sumE ((Array.range 64).filterMap fun z ↦
        if testBitW (keccakRCW.getD (Verifier.keccakDepth * (segment + 1) - step - 1) 0) z then
          some (weights.getD z 0) else none))).toE =
    Verifier.sumE ((List.range Verifier.keccakSegments).map fun segment ↦
      (segments.toList.map EW.toE).getD segment 0 *
        Verifier.sumE ((List.range 64).filterMap fun z ↦
          if (keccakRC.getD (Verifier.keccakDepth * (segment + 1) - step - 1) 0).toNat.testBit z
          then some ((weights.toList.map EW.toE).getD z 0) else none)) := by
  rw [toE_sumE, Array.toList_map, Array.toList_range, List.map_map]
  congr 1
  refine List.map_congr_left fun segment _ ↦ ?_
  rw [Function.comp_apply, EW.toE_mul, toE_getD, toE_sumE, Array.toList_filterMap,
    Array.toList_range, List.map_filterMap, keccakRCW, getD_toArray]
  congr 2
  refine List.filterMap_congr fun z hz ↦ ?_
  rw [testBitW_eq _ (List.mem_range.1 hz)]
  split
  · rw [Option.map_some, toE_getD]
  · rfl

end NativeVm.Equiv.Keccak
