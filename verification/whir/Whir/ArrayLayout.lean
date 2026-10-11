import Whir.Concrete
import Whir.Layout

/-! Array/index refinement of the executable kernels. These results use no field
laws. Rotation is clamped by `Array.extract`, unlike unbounded list rotation;
the direct terminal-point bridge therefore records the protocol's length bound. -/
namespace Whir.ArrayLayout
open Concrete

variable {α : Type*}

@[simp] theorem size_tab (n : Nat) (f : Nat → α) : (tab n f).size = n := by
  simp [tab]

@[simp] theorem toList_tab (n : Nat) (f : Nat → α) :
    (tab n f).toList = (List.range n).map f := by
  simp [tab]

@[simp] theorem getElem_tab (n : Nat) (f : Nat → α) (i : Nat) (h : i < n) :
    (tab n f)[i]'(by simpa using h) = f i := by
  simp [tab]

@[simp] theorem getElem!_tab [Inhabited α] (n : Nat) (f : Nat → α)
    (i : Nat) (h : i < n) : (tab n f)[i]! = f i := by
  simp [getElem!_pos, h]

 theorem rotatePoint_slices (k : Nat) (point : Array α) :
    (rotatePoint k point).toList = point.toList.drop k ++ point.toList.take k := by
  simp [rotatePoint, List.extract]

 theorem rotatePoint_terminalPoint (k : Nat) (point : Array α) (h : k ≤ point.size) :
    (rotatePoint k point).toList = Layout.terminalPoint k point.toList := by
  rw [rotatePoint_slices, Layout.terminalPoint_slices k point.toList (by simpa using h)]

 theorem rotatePoint_terminalPoint_clamped (k : Nat) (point : Array α) :
    (rotatePoint k point).toList = Layout.terminalPoint (min k point.size) point.toList := by
  rw [rotatePoint_slices, Layout.terminalPoint_slices _ _ (by simp)]
  by_cases h : k ≤ point.size
  · simp [Nat.min_eq_left h]
  · have hs : point.size ≤ k := by omega
    have hs' : point.toList.length ≤ k := by simpa only [Array.length_toList] using hs
    simp only [Nat.min_eq_right hs, List.drop_eq_nil_of_le hs',
      List.take_of_length_le hs', List.nil_append]
    simp [← Array.length_toList]

@[simp] theorem size_rotatePoint (k : Nat) (point : Array α) :
    (rotatePoint k point).size = point.size := by
  simpa using congrArg List.length (rotatePoint_terminalPoint_clamped k point) |>.trans
    (Layout.terminalPoint_length _ _)

 theorem rotatePoint_permutation (k : Nat) (point : Array α) :
    (rotatePoint k point).toList.Perm point.toList := by
  rw [rotatePoint_terminalPoint_clamped]
  exact Layout.terminalPoint_permutation _ _

 theorem rotatePoint_inverse (k : Nat) (point : Array α) (h : k ≤ point.size) :
    rotatePoint (point.size - k) (rotatePoint k point) = point := by
  apply Array.toList_inj.mp
  rw [rotatePoint_terminalPoint _ _ (by simp), rotatePoint_terminalPoint k point h]
  exact Layout.terminalPoint_inverse k point.toList (by simpa using h)

 theorem padding_toList (zero : α) (width : Nat) (live : Array α)
    (h : live.size ≤ width) :
    (tab width fun i => live[i]?.getD zero).toList = Layout.padTail zero width live.toList := by
  apply List.ext_getElem
  · simp [Layout.padTail]; omega
  · intro i h₁ h₂
    simp only [toList_tab, List.getElem_map, List.getElem_range]
    by_cases hi : i < live.size
    · simp [Layout.padTail, List.getElem_append_left, hi, getElem?_pos]
    · have hs : live.size ≤ i := by omega
      simp [Layout.padTail, List.getElem_append_right, hi, hs, getElem?_neg]

 theorem reversed_tab_toList (n : Nat) (f : Nat → α) :
    (tab n fun i => f (n - 1 - i)).toList = Layout.prunedLeaf (tab n f).toList := by
  apply List.ext_getElem
  · simp [Layout.prunedLeaf]
  · intro i h₁ h₂
    simp [Layout.prunedLeaf, List.getElem_reverse, Nat.sub_sub]

 theorem restore_reversed_tab (zero : α) (width n : Nat) (f : Nat → α) :
    Layout.restoreLeaf zero width (tab n fun i => f (n - 1 - i)).toList =
      (Layout.padTail zero width (tab n f).toList).reverse := by
  rw [reversed_tab_toList, Layout.restoreLeaf_eq_full]

@[simp] theorem size_foldLow [Add α] [Mul α] [Inhabited α] (a : Array α) (r : α) :
    (foldLow a r).size = a.size / 2 := by simp [foldLow]

@[simp] theorem size_foldLane [Add α] [Mul α] [Inhabited α]
    (a : Array α) (block : Nat) (r : α) :
    (foldLane a block r).size = a.size / 2 := by simp [foldLane]

 theorem foldLow_indices {size i : Nat} (h : i < size / 2) :
    2 * i < size ∧ 2 * i + 1 < size := by omega

 theorem getElem_foldLow [Add α] [Mul α] [Inhabited α]
    (a : Array α) (r : α) (i : Nat) (h : i < a.size / 2) :
    (foldLow a r)[i]'(by simpa using h) =
      foldPair (a[2*i]'((foldLow_indices h).1)) (a[2*i+1]'((foldLow_indices h).2)) r := by
  simp [foldLow, tab, getElem!_pos, (foldLow_indices h).1, (foldLow_indices h).2]

/-- A top-lane step preserves the row and selects adjacent high-coordinate lanes. -/
 theorem foldLane_offset {block lane row : Nat} (hr : row < block) :
    ((lane * block + row) / block) * (2 * block) +
      (lane * block + row) % block = Layout.stackIndex block (2 * lane) row := by
  obtain ⟨hq, hm⟩ := Layout.stackIndex_partition (lane := lane) hr
  simp only [Layout.stackIndex] at hq hm ⊢
  rw [hq, hm]
  ring

 theorem foldLane_indices {block lanes i : Nat} (hb : 0 < block)
    (hi : i < lanes * block) :
    (i / block) * (2 * block) + i % block < (2 * lanes) * block ∧
    (i / block) * (2 * block) + i % block + block < (2 * lanes) * block := by
  have hq : i / block < lanes := (Nat.div_lt_iff_lt_mul hb).2 (by simpa [Nat.mul_comm] using hi)
  have hm : i % block < block := Nat.mod_lt _ hb
  constructor <;> nlinarith

 theorem getElem_foldLane [Add α] [Mul α] [Inhabited α]
    (a : Array α) (r : α) (block lanes lane row : Nat)
    (ha : a.size = (2 * lanes) * block) (hl : lane < lanes) (hr : row < block) :
    (foldLane a block r)[lane * block + row]'(by
      simp only [size_foldLane, ha, Nat.mul_assoc, Nat.mul_div_right _ (by decide : 0 < 2)]
      exact Layout.stackIndex_bound hl hr) =
      foldPair a[Layout.stackIndex block (2 * lane) row]!
        a[Layout.stackIndex block (2 * lane + 1) row]! r := by
  simp only [foldLane, tab, Array.getElem_map, List.getElem_toArray, List.getElem_range]
  rw [foldLane_offset hr]
  have he : Layout.stackIndex block (2 * lane) row + block =
      Layout.stackIndex block (2 * lane + 1) row := by
    simp only [Layout.stackIndex]
    ring
  rw [he]

/-- Both source accesses are in bounds; no panic/default value participates. -/
 theorem foldLane_stack_bounds {block lanes lane row : Nat}
    (hl : lane < lanes) (hr : row < block) :
    Layout.stackIndex block (2 * lane) row < (2 * lanes) * block ∧
    Layout.stackIndex block (2 * lane + 1) row < (2 * lanes) * block := by
  constructor <;> apply Layout.stackIndex_bound (by omega) hr

/-- The exact padding expression in `Protocol.prove`, including base embedding. -/
 theorem padding_map_toList {β : Type*} (zero : α) (embed : α → β)
    (width : Nat) (live : Array α) (h : live.size ≤ width) :
    (tab width fun i => embed (live[i]?.getD zero)).toList =
      Layout.padTail (embed zero) width (live.toList.map embed) := by
  have hm : (tab width fun i => embed (live[i]?.getD zero)).toList =
      ((tab width fun i => live[i]?.getD zero).toList.map embed) := by
    simp [List.map_map]
  rw [hm, padding_toList zero width live h]
  simp [Layout.padTail]

/-- Prefix restoration is the physical full leaf, not witness-order padding. -/
 theorem restore_array_toList (zero : α) (width : Nat) (stored : Array α) :
    ((tab (width - stored.size) fun _ => zero) ++ stored).toList =
      Layout.restoreLeaf zero width stored.toList := by
  simp [Layout.restoreLeaf, List.map_const', List.length_range]

 theorem encodeBase_size (message : Array K) (logN initialK rate : Nat) :
    (encodeBase message logN initialK rate).size = 2 ^ (logN - initialK + rate) := by
  simp [encodeBase]

/-- The actual encoder drops no occupied lane and reverses only the live lanes. -/
 theorem encodeBase_leaf (message : Array K) (logN initialK rate q : Nat)
    (hq : q < 2 ^ (logN - initialK + rate)) :
    ((encodeBase message logN initialK rate)[q]!).toList =
      Layout.prunedLeaf
        (tab (message.size / 2 ^ (logN - initialK)) fun lane =>
          (encode (logN - initialK) rate
            (tab (2 ^ (logN - initialK)) fun j =>
              E.ofK message[lane * 2 ^ (logN - initialK) + j]!))[q]!).toList := by
  simp only [encodeBase, getElem!_tab _ _ _ hq]
  rw [← reversed_tab_toList]
  congr 1
  apply Array.ext
  · simp
  · intro t ht ht'
    simp only [size_tab] at ht ht'
    have hr : message.size / 2 ^ (logN - initialK) - 1 - t <
        message.size / 2 ^ (logN - initialK) := by omega
    simp [tab, getElem!_pos, hr]

 theorem encodeBase_leaf_size (message : Array K) (logN initialK rate q : Nat)
    (hq : q < 2 ^ (logN - initialK + rate)) :
    ((encodeBase message logN initialK rate)[q]!).size =
      message.size / 2 ^ (logN - initialK) := by
  simpa [Layout.prunedLeaf] using congrArg List.length
    (encodeBase_leaf message logN initialK rate q hq)

/-- Every word read while constructing a live lane is inside the message,
even when its length is not a multiple of the block width. -/
 theorem encodeBase_word_bound {size block lane row : Nat}
    (hl : lane < size / block) (hr : row < block) :
    lane * block + row < size := by
  have hb : 0 < block := by omega
  have h : (lane + 1) * block ≤ size :=
    (Nat.le_div_iff_mul_le hb).1 (by omega)
  nlinarith

/-- The top-lane pairing is a permutation of all input coordinates, including
the empty case. Its second coordinate is the folded lane bit, not a row bit. -/
def foldLaneEquiv (lanes block : Nat) :
    (Fin (lanes * block) × Fin 2) ≃ Fin ((lanes * 2) * block) :=
  (Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl (Fin 2))).trans
    ((Equiv.prodAssoc (Fin lanes) (Fin block) (Fin 2)).trans
      ((Equiv.prodCongr (Equiv.refl (Fin lanes)) (Equiv.prodComm (Fin block) (Fin 2))).trans
        ((Equiv.prodAssoc (Fin lanes) (Fin 2) (Fin block)).symm.trans
          ((Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin block))).trans finProdFinEquiv))))

 theorem foldLaneEquiv_val (lanes block : Nat) (i : Fin (lanes * block)) (b : Fin 2) :
    (foldLaneEquiv lanes block (i, b)).val =
      (i.val / block) * (2 * block) + i.val % block + b.val * block := by
  simp [foldLaneEquiv, finProdFinEquiv]
  ring

 theorem sum_foldLane_pairs {β : Type*} [AddCommMonoid β]
    (lanes block : Nat) (g : Nat → β) :
    (∑ j : Fin ((lanes * 2) * block), g j.val) =
      ∑ i : Fin (lanes * block),
        (g ((i.val / block) * (2 * block) + i.val % block) +
         g ((i.val / block) * (2 * block) + i.val % block + block)) := by
  rw [← Equiv.sum_comp (foldLaneEquiv lanes block)]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, foldLaneEquiv_val]

 theorem foldLane_one [Add α] [Mul α] [Inhabited α] (a : Array α) (r : α) :
    foldLane a 1 r = foldLow a r := by
  simp [foldLane, foldLow, Nat.mul_comm, Nat.mod_one]

end Whir.ArrayLayout
