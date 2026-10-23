/-
  LeanVM.Protocol.EndToEnd.Complete.BusStack

  Tables stacked the way the Python verifier's `stack_offsets` places them: blocks laid end to
  end, largest first, padded with ones to a power of two. Their product is the product of the
  blocks, and their multilinear extension splits into the blocks' extensions weighted by their
  selectors, plus the padding.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.LayoutStack
public import LeanVM.Protocol.Whir.Complete.Tables

/-!
# Stacked leaves

The bus phase of the verifier program (`verifyBusBalance`, `python-verifier/verifier.py:482-593`
at leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`) reads each side of the bus as one grand
product over a cube of leaves: the side's blocks placed by `stack_offsets` (`bus_layout`), the
rest of the cube filled with ones. This module is that placement, for any block sizes and any
block tables:

* `stackOrder sizes`: `stack_offsets`' order, the stable sort of the indices by size, larger
  first (`Front.stackOffsets_eq`);
* `stackLeaves sizes tabs D`: the blocks' tables concatenated in that order, padded with ones to
  `2 ^ D` entries;
* `prod_stackLeaves`: the product of the leaves is the product of the blocks;
* `multilinearEval_stackLeaves`: the stacking identity. At a point `p` of `D` coordinates the
  leaves' extension is `Σ_b sel_b(p) · t̃_b(p_low) + (1 - Σ_b sel_b(p))`, where `sel_b` is the
  equality weight of the block's offset bits against the coordinates above the block
  (`blockSel`, the verifier's `Placement.eq_above`) and `p_low` the block's own coordinates.
  It holds because the order sorts the sizes decreasingly, so every offset is aligned to its
  block's size.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Complete Finset

@[expose] public section

/-! ## Sums over the cube -/

/-- Folding a constant table gives the constant table of half the length. -/
theorem foldPairs_replicate (r c : E) : ∀ n : ℕ,
    foldPairs r (List.replicate (2 * n) c) = List.replicate n c
  | 0 => rfl
  | n + 1 => by
    rw [show 2 * (n + 1) = (2 * n) + 1 + 1 by ring, List.replicate_succ, List.replicate_succ]
    simp only [foldPairs]
    rw [foldPairs_replicate r c n, List.replicate_succ]
    refine congrArg₂ List.cons ?_ rfl
    linear_combination (c * r) * two_eq_zero_E

/-- The extension of a constant table is the constant. -/
theorem multilinearEval_replicate (c : E) : ∀ p : List E,
    multilinearEval (List.replicate (2 ^ p.length) c) p = c
  | [] => rfl
  | r :: p => by
    rw [Whir.Complete.multilinearEval_cons, List.length_cons, pow_succ, mul_comm,
      foldPairs_replicate, multilinearEval_replicate c p]

/-- The equality weights of a point sum to one over the cube. -/
theorem sum_eqEval_boolPoint (m : ℕ) (p : List E) (hp : p.length = m) :
    ∑ x ∈ range (2 ^ m), eqEval (boolPoint m x) p = 1 := by
  have h := multilinearEval_eq_sum m (List.replicate (2 ^ m) 1) p (by simp) hp
  subst hp
  rw [multilinearEval_replicate] at h
  rw [h]
  refine sum_congr rfl fun x hx ↦ ?_
  rw [List.getD_eq_getElem _ _ (by simpa using mem_range.mp hx), List.getElem_replicate, one_mul]

/-- An entry of a table indexed by `y` below a block, at the point split at the block. -/
theorem eqEval_boolPoint_aligned {D v m y : ℕ} (hv : v ≤ D) (hy : y < 2 ^ v) (p : List E)
    (hp : p.length = D) :
    eqEval (boolPoint D (2 ^ v * m + y)) p =
      eqEval (boolPoint v y) (p.take v) * eqEval (boolPoint (D - v) m) (p.drop v) := by
  have hD : D = v + (D - v) := by omega
  rw [show 2 ^ v * m + y = y + 2 ^ v * m by ring, hD, boolPoint_add v (D - v) y m hy,
    ← List.take_append_drop v p, eqEval_append _ _ _ _ (by simp; omega)]
  simp only [List.take_append_drop]
  rw [show v + (D - v) - v = D - v by omega]

/-! ## The order and the leaves -/

/-- `stack_offsets`' order: the stable sort of the block indices by size, larger first. -/
def stackOrder (sizes : List ℕ) : List ℕ :=
  (List.range sizes.length).mergeSort fun i j ↦ decide (sizes.getD j 0 ≤ sizes.getD i 0)

theorem perm_stackOrder (sizes : List ℕ) : (stackOrder sizes).Perm (List.range sizes.length) :=
  List.mergeSort_perm _ _

theorem nodup_stackOrder (sizes : List ℕ) : (stackOrder sizes).Nodup :=
  (perm_stackOrder sizes).nodup_iff.mpr List.nodup_range

theorem mem_stackOrder {sizes : List ℕ} {b : ℕ} : b ∈ stackOrder sizes ↔ b < sizes.length := by
  rw [(perm_stackOrder sizes).mem_iff, List.mem_range]

/-- The order sorts the sizes decreasingly. -/
theorem pairwise_stackOrder (sizes : List ℕ) :
    (stackOrder sizes).Pairwise fun i j ↦ sizes.getD j 0 ≤ sizes.getD i 0 := by
  have h := List.pairwise_mergeSort (le := fun i j ↦ decide (sizes.getD j 0 ≤ sizes.getD i 0))
    (fun a b c h1 h2 ↦ by simp only [decide_eq_true_eq] at *; omega)
    (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (List.range sizes.length)
  exact h.imp fun h ↦ by simpa using h

/-- The total size of the blocks. -/
def blockTotal (sizes : List ℕ) : ℕ :=
  ((List.range sizes.length).map fun b ↦ 2 ^ sizes.getD b 0).sum

/-- The leaves: the blocks' tables concatenated in `stack_offsets`' order, padded with ones to
`2 ^ D` entries. -/
def stackLeaves (sizes : List ℕ) (tabs : ℕ → List E) (D : ℕ) : List E :=
  (stackOrder sizes).flatMap tabs ++
    List.replicate (2 ^ D - ((stackOrder sizes).flatMap tabs).length) 1

theorem prod_flatMap_E {α : Type} (f : α → List E) : ∀ l : List α,
    (l.flatMap f).prod = (l.map fun a ↦ (f a).prod).prod
  | [] => rfl
  | a :: l => by simp [List.flatMap_cons, List.prod_append, prod_flatMap_E f l]

/-- **The product of the leaves** is the product of the blocks. -/
theorem prod_stackLeaves (sizes : List ℕ) (tabs : ℕ → List E) (D : ℕ) :
    (stackLeaves sizes tabs D).prod =
      ((List.range sizes.length).map fun b ↦ (tabs b).prod).prod := by
  rw [stackLeaves, List.prod_append, List.prod_replicate, one_pow, mul_one, prod_flatMap_E]
  exact ((perm_stackOrder sizes).map _).prod_eq

theorem length_flatMap_stackOrder (sizes : List ℕ) (tabs : ℕ → List E)
    (htab : ∀ b < sizes.length, (tabs b).length = 2 ^ sizes.getD b 0) :
    ((stackOrder sizes).flatMap tabs).length = blockTotal sizes := by
  rw [List.length_flatMap, blockTotal]
  rw [List.map_congr_left fun b hb ↦ htab b (mem_stackOrder.mp hb)]
  exact ((perm_stackOrder sizes).map _).sum_eq

/-- The leaves fill the cube. -/
theorem length_stackLeaves (sizes : List ℕ) (tabs : ℕ → List E) (D : ℕ)
    (htab : ∀ b < sizes.length, (tabs b).length = 2 ^ sizes.getD b 0)
    (hD : blockTotal sizes ≤ 2 ^ D) : (stackLeaves sizes tabs D).length = 2 ^ D := by
  rw [stackLeaves, List.length_append, List.length_replicate,
    length_flatMap_stackOrder sizes tabs htab]
  omega

/-! ## Offsets -/

/-- The offset of block `b`, `stack_offsets(sizes)[b]`. -/
def blockOffset (sizes : List ℕ) (b : ℕ) : ℕ := (stackOffsets sizes).1.getD b 0

/-- The offset of the `k`-th block of the order is the size of the blocks before it. -/
theorem blockOffset_getElem (sizes : List ℕ) (k : ℕ) (hk : k < (stackOrder sizes).length) :
    blockOffset sizes (stackOrder sizes)[k] =
      (((stackOrder sizes).take k).map fun i ↦ 2 ^ sizes.getD i 0).sum := by
  have h := placeFold_getElem? (fun i ↦ 2 ^ sizes.getD i 0) (stackOrder sizes)
    (nodup_stackOrder sizes) (List.replicate sizes.length 0, 0)
    (fun i hi ↦ by simpa using mem_stackOrder.mp hi) k hk
  rw [blockOffset, stackOffsets_eq]
  simp only
  rw [List.getD_eq_getElem?_getD]
  exact (congrArg (Option.getD · 0) h).trans (by simp)

/-- Every offset is aligned to its block's size. -/
theorem dvd_blockOffset (sizes : List ℕ) (k : ℕ) (hk : k < (stackOrder sizes).length) :
    2 ^ sizes.getD (stackOrder sizes)[k] 0 ∣ blockOffset sizes (stackOrder sizes)[k] := by
  rw [blockOffset_getElem sizes k hk]
  refine List.dvd_sum fun d hd ↦ ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hi
  simp only [List.length_take] at hj
  have hp := List.pairwise_iff_getElem.mp (pairwise_stackOrder sizes) j k (by omega) hk
    (by omega)
  simp only [List.getElem_take]
  exact pow_dvd_pow 2 hp

/-! ## The stacking identity -/

/-- The selector of block `b` at `p`: the equality weight of its offset's bits above the block
against the coordinates above the block. -/
def blockSel (sizes : List ℕ) (D b : ℕ) (p : List E) : E :=
  eqEval (boolPoint (D - sizes.getD b 0) (blockOffset sizes b / 2 ^ sizes.getD b 0))
    (p.drop (sizes.getD b 0))

/-- A sum over a concatenation is the sum over its pieces, each at its running offset. -/
theorem sum_flatMap (tabs : ℕ → List E) (f : ℕ → E) : ∀ (ord : List ℕ) (off : ℕ),
    ∑ x ∈ range (ord.flatMap tabs).length, (ord.flatMap tabs).getD x 0 * f (off + x) =
      ((List.range ord.length).map fun k ↦
        ∑ y ∈ range (tabs ord[k]!).length, (tabs ord[k]!).getD y 0 *
          f (off + ((ord.take k).map fun i ↦ (tabs i).length).sum + y)).sum
  | [], _ => by simp
  | a :: ord, off => by
    rw [List.flatMap_cons, List.length_append, sum_range_add, List.length_cons,
      List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    refine congrArg₂ (· + ·) ?_ ?_
    · simp only [List.getElem!_cons_zero, List.take_zero, List.map_nil, List.sum_nil, add_zero]
      refine sum_congr rfl fun y hy ↦ ?_
      rw [List.getD_append _ _ _ _ (mem_range.mp hy)]
    · refine Eq.trans ?_ ((sum_flatMap tabs f ord (off + (tabs a).length)).trans ?_)
      · refine sum_congr rfl fun y _ ↦ ?_
        rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, add_assoc]
      · refine congrArg List.sum (List.map_congr_left fun k _ ↦ ?_)
        simp only [Function.comp_apply, List.getElem!_cons_succ, List.take_succ_cons,
          List.map_cons, List.sum_cons]
        refine sum_congr rfl fun y _ ↦ ?_
        rw [add_assoc off]

/-- A list read back through its indices. -/
theorem map_range_getElem! (l : List ℕ) : (List.range l.length).map (fun k ↦ l[k]!) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem!_eq_getElem?_getD, h2]

/-- A finite sum over the range is the list sum. -/
theorem sum_range_eq_list (n : ℕ) (H : ℕ → E) :
    ∑ b ∈ range n, H b = ((List.range n).map H).sum := by
  rw [← List.toFinset_range, List.sum_toFinset _ (List.nodup_range)]

/-- The pieces of the order, each at its offset: block `b`'s table against `f` at
`offset + y`. -/
theorem sum_flatMap_stackOrder (sizes : List ℕ) (tabs : ℕ → List E)
    (htab : ∀ b < sizes.length, (tabs b).length = 2 ^ sizes.getD b 0) (f : ℕ → E) :
    ∑ x ∈ range ((stackOrder sizes).flatMap tabs).length,
        ((stackOrder sizes).flatMap tabs).getD x 0 * f x =
      ∑ b ∈ range sizes.length, ∑ y ∈ range (2 ^ sizes.getD b 0),
        (tabs b).getD y 0 * f (blockOffset sizes b + y) := by
  have h := sum_flatMap tabs (fun x ↦ f x) (stackOrder sizes) 0
  simp only [zero_add] at h
  rw [h, sum_range_eq_list]
  set H : ℕ → E := fun b ↦ ∑ y ∈ range (2 ^ sizes.getD b 0),
    (tabs b).getD y 0 * f (blockOffset sizes b + y)
  have hk : ∀ k ∈ List.range (stackOrder sizes).length,
      (∑ y ∈ range (tabs (stackOrder sizes)[k]!).length, (tabs (stackOrder sizes)[k]!).getD y 0 *
        f ((((stackOrder sizes).take k).map fun i ↦ (tabs i).length).sum + y)) =
      H (stackOrder sizes)[k]! := by
    intro k hk
    have hk' := List.mem_range.mp hk
    have hmem : (stackOrder sizes)[k]! < sizes.length := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk']
      exact mem_stackOrder.mp (List.getElem_mem _)
    have hoff : (((stackOrder sizes).take k).map fun i ↦ (tabs i).length).sum =
        blockOffset sizes (stackOrder sizes)[k]! := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some,
        blockOffset_getElem sizes k hk']
      refine congrArg List.sum (List.map_congr_left fun i hi ↦ htab i ?_)
      exact mem_stackOrder.mp (List.mem_of_mem_take hi)
    simp only [H, htab _ hmem, hoff]
  rw [List.map_congr_left hk]
  have e : (List.range (stackOrder sizes).length).map (fun k ↦ H (stackOrder sizes)[k]!) =
      ((List.range (stackOrder sizes).length).map fun k ↦ (stackOrder sizes)[k]!).map H := by
    rw [List.map_map]; rfl
  rw [e, map_range_getElem!]
  exact ((perm_stackOrder sizes).map H).sum_eq

/-- **The stacking identity.** At a point of `D` coordinates, the leaves' extension is the sum of
the blocks' extensions at their own coordinates, each weighted by its selector, plus the padding's
weight `1 - Σ_b sel_b`. -/
theorem multilinearEval_stackLeaves (sizes : List ℕ) (tabs : ℕ → List E) (D : ℕ)
    (htab : ∀ b < sizes.length, (tabs b).length = 2 ^ sizes.getD b 0)
    (hD : blockTotal sizes ≤ 2 ^ D) (p : List E) (hp : p.length = D) :
    multilinearEval (stackLeaves sizes tabs D) p =
      ∑ b ∈ range sizes.length,
          blockSel sizes D b p * multilinearEval (tabs b) (p.take (sizes.getD b 0)) +
        (1 - ∑ b ∈ range sizes.length, blockSel sizes D b p) := by
  set f : ℕ → E := fun x ↦ eqEval (boolPoint D x) p
  -- each block's piece is its selector times its extension
  have hv : ∀ b < sizes.length, sizes.getD b 0 ≤ D := by
    intro b hb
    have h1 : 2 ^ sizes.getD b 0 ≤ blockTotal sizes := by
      rw [blockTotal]
      exact List.le_sum_of_mem (List.mem_map.mpr ⟨b, List.mem_range.mpr hb, rfl⟩)
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (h1.trans hD)
  have halign : ∀ b < sizes.length, 2 ^ sizes.getD b 0 ∣ blockOffset sizes b := by
    intro b hb
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (mem_stackOrder.mpr hb)
    exact dvd_blockOffset sizes k hk
  have hpiece : ∀ (g : ℕ → List E), (∀ b < sizes.length, (g b).length = 2 ^ sizes.getD b 0) →
      ∀ b < sizes.length, ∑ y ∈ range (2 ^ sizes.getD b 0),
        (g b).getD y 0 * f (blockOffset sizes b + y) =
          blockSel sizes D b p * multilinearEval (g b) (p.take (sizes.getD b 0)) := by
    intro g hg b hb
    obtain ⟨m, hm⟩ := halign b hb
    rw [multilinearEval_eq_sum (sizes.getD b 0) (g b) _ (hg b hb)
      (by rw [List.length_take]; have := hv b hb; omega), mul_sum]
    refine sum_congr rfl fun y hy ↦ ?_
    simp only [f, blockSel, hm, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
    rw [eqEval_boolPoint_aligned (hv b hb) (mem_range.mp hy) p hp]
    ring
  have hbody := length_flatMap_stackOrder sizes tabs htab
  rw [multilinearEval_eq_sum D _ p (length_stackLeaves sizes tabs D htab hD) hp]
  rw [show 2 ^ D = ((stackOrder sizes).flatMap tabs).length +
      (2 ^ D - ((stackOrder sizes).flatMap tabs).length) by omega, sum_range_add]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [← sum_congr rfl fun b hb ↦ hpiece tabs htab b (mem_range.mp hb),
      ← sum_flatMap_stackOrder sizes tabs htab f]
    refine sum_congr rfl fun x hx ↦ ?_
    rw [stackLeaves, List.getD_append _ _ _ _ (mem_range.mp hx)]
  · -- the padding: the cube's weight minus the blocks'
    set ones : ℕ → List E := fun b ↦ List.replicate (2 ^ sizes.getD b 0) 1
    have hones1 : ∀ b < sizes.length, (ones b).length = 2 ^ sizes.getD b 0 := fun b _ ↦ by
      simp [ones]
    have hlen1 := length_flatMap_stackOrder sizes ones hones1
    have hmem1 : ∀ a ∈ (stackOrder sizes).flatMap ones, a = 1 := by
      intro a ha
      obtain ⟨b, -, hb⟩ := List.mem_flatMap.mp ha
      exact List.eq_of_mem_replicate hb
    have hsel : ∑ x ∈ range (blockTotal sizes), f x =
        ∑ b ∈ range sizes.length, blockSel sizes D b p := by
      have h1 := sum_flatMap_stackOrder sizes ones hones1 f
      rw [hlen1] at h1
      rw [sum_congr rfl fun b hb ↦ hpiece ones hones1 b (mem_range.mp hb)] at h1
      rw [← h1.trans (sum_congr rfl fun b hb ↦ by
        rw [show ones b = List.replicate (2 ^ (p.take (sizes.getD b 0)).length) 1 by
          simp only [ones, List.length_take, hp, min_eq_left (hv b (mem_range.mp hb))],
          multilinearEval_replicate, mul_one])]
      refine sum_congr rfl fun x hx ↦ ?_
      rw [List.getD_eq_getElem _ _ (by rw [hlen1]; exact mem_range.mp hx),
        hmem1 _ (List.getElem_mem _), one_mul]
    have hall := sum_eqEval_boolPoint D p hp
    rw [show 2 ^ D = blockTotal sizes + (2 ^ D - blockTotal sizes) by omega, sum_range_add,
      hsel] at hall
    rw [← hall, hbody]
    simp only [add_sub_cancel_left]
    refine sum_congr rfl fun x hx ↦ ?_
    rw [stackLeaves, List.getD_append_right _ _ _ _ (by omega), hbody,
      Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ (by simpa using mem_range.mp hx),
      List.getElem_replicate, one_mul]

end
end LeanVM.Protocol.EndToEnd.Complete
