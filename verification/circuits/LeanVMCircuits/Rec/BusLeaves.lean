module

public import LeanVMCircuits.Rec.TableChain

@[expose] public section

/-!
The bus GKR's leaf layer on one side as Rust stacks it (`BusBlocks::new`), and its root as the product over the slots.

A side's leaf layer of `2^n` leaves stacks blocks: block `b` of `2^κ_b` rows at offset `2^κ_b q_b`, its leaves
`leaf_b`, every other leaf padding, `1` (`stackLeaf`). `stackLeaf_block` and `stackLeaf_pad` are the premises
`leaf_decompose` and `totals_eq_formSums` take of the layer; `prod_stackLeaf`: where the blocks fit in the layer and do
not overlap, the product of its leaves is the product of the blocks' leaves.

The recursion's blocks (`busSlots`) are the public table's one slot, then each owned table's slots in `Bind.ownedList`
order, every block of table `T` of `2^τ_T` rows, one per row. `prod_busSlots`: over them, the blocks' leaves multiply
to the product over `slots w` when every table's height is `2^τ_T`. `pullRoot_eq_slots` and `pushRoot_eq_slots`: the
bus's honest roots are such products, a slot's push leaf carrying its class-next slot's key (`pushKey`).
`root_eq_stack` and `level_stack`: the stacked layer's root is the product over the slots, so `pullRoot_eq_stack` and
`pushRoot_eq_stack` give the honest roots as the stacked layer's root.
-/

namespace LeanVMCircuits.Rec.AirLink

open LeanVMCircuits.Rec Model Finset

/-! A stacked layer. -/

section Stack

variable {m : ℕ} (κ q : Fin m → ℕ) (leaf : Fin m → ℕ → E)

open Classical in
/-- A side's stacked leaf layer: at `x` the leaf `leaf_b (x - 2^κ_b q_b)` of the block `b` holding `x`, else padding,
`1`. -/
noncomputable def stackLeaf (x : ℕ) : E :=
  if h : ∃ b, x ∈ Ico (2 ^ κ b * q b) (2 ^ κ b * q b + 2 ^ κ b) then
    leaf h.choose (x - 2 ^ κ h.choose * q h.choose)
  else 1

/-- Where no two blocks overlap, a block's rows carry its leaves. -/
theorem stackLeaf_block
    (hdisj : ∀ b b', b ≠ b' → Disjoint (Ico (2 ^ κ b * q b) (2 ^ κ b * q b + 2 ^ κ b))
      (Ico (2 ^ κ b' * q b') (2 ^ κ b' * q b' + 2 ^ κ b'))) :
    ∀ b, ∀ z < 2 ^ κ b, stackLeaf κ q leaf (2 ^ κ b * q b + z) = leaf b z := by
  intro b z hz
  have hmem : 2 ^ κ b * q b + z ∈ Ico (2 ^ κ b * q b) (2 ^ κ b * q b + 2 ^ κ b) := mem_Ico.mpr ⟨by omega, by omega⟩
  have hex : ∃ b', 2 ^ κ b * q b + z ∈ Ico (2 ^ κ b' * q b') (2 ^ κ b' * q b' + 2 ^ κ b') := ⟨b, hmem⟩
  have hb : hex.choose = b := by
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj _ _ hne) hex.choose_spec hmem
  rw [stackLeaf, dif_pos hex, hb, Nat.add_sub_cancel_left]

/-- Every leaf no block holds is padding. -/
theorem stackLeaf_pad {n : ℕ} :
    ∀ x < 2 ^ n, (∀ b, x ∉ Ico (2 ^ κ b * q b) (2 ^ κ b * q b + 2 ^ κ b)) → stackLeaf κ q leaf x = 1 := by
  intro x _ hx
  rw [stackLeaf, dif_neg fun ⟨b, hb⟩ => hx b hb]

/-- Where the blocks fit in the `2^n` leaves and do not overlap, the leaves multiply to the blocks' leaves. -/
theorem prod_stackLeaf {n : ℕ} (hin : ∀ b, 2 ^ κ b * q b + 2 ^ κ b ≤ 2 ^ n)
    (hdisj : ∀ b b', b ≠ b' → Disjoint (Ico (2 ^ κ b * q b) (2 ^ κ b * q b + 2 ^ κ b))
      (Ico (2 ^ κ b' * q b') (2 ^ κ b' * q b' + 2 ^ κ b'))) :
    ∏ x ∈ range (2 ^ n), stackLeaf κ q leaf x = ∏ b, ∏ z ∈ range (2 ^ κ b), leaf b z := by
  set blk := fun b : Fin m => Ico (2 ^ κ b * q b) (2 ^ κ b * q b + 2 ^ κ b)
  have hsub : univ.biUnion blk ⊆ range (2 ^ n) := fun x hx => by
    obtain ⟨b, -, hb⟩ := mem_biUnion.mp hx
    exact mem_range.mpr (lt_of_lt_of_le (mem_Ico.mp hb).2 (hin b))
  rw [← prod_subset hsub fun x hx hnx => stackLeaf_pad κ q leaf x (mem_range.mp hx)
      fun b hb => hnx (mem_biUnion.mpr ⟨b, mem_univ _, hb⟩),
    prod_biUnion fun b _ b' _ hbb' => hdisj b b' hbb']
  refine prod_congr rfl fun b _ => ?_
  rw [prod_Ico_eq_prod_range, Nat.add_sub_cancel_left]
  exact prod_congr rfl fun z hz => stackLeaf_block κ q leaf hdisj b z (mem_range.mp hz)

end Stack

/-- Non-vacuity: two blocks of one row each fill a layer of two leaves, whose product is theirs. -/
example (a c : E) :
    stackLeaf (fun _ : Fin 2 => 0) ![0, 1] (fun b _ => ![a, c] b) 1 = c ∧
      ∏ x ∈ range (2 ^ 1), stackLeaf (fun _ : Fin 2 => 0) ![0, 1] (fun b _ => ![a, c] b) x = a * c := by
  have hdisj : ∀ b b' : Fin 2, b ≠ b' →
      Disjoint (Ico (2 ^ 0 * (![0, 1] : Fin 2 → ℕ) b) (2 ^ 0 * (![0, 1] : Fin 2 → ℕ) b + 2 ^ 0))
        (Ico (2 ^ 0 * (![0, 1] : Fin 2 → ℕ) b') (2 ^ 0 * (![0, 1] : Fin 2 → ℕ) b' + 2 ^ 0)) := by
    decide
  refine ⟨?_, ?_⟩
  · simpa using stackLeaf_block (fun _ : Fin 2 => 0) ![0, 1] (fun b _ => ![a, c] b) hdisj 1 0 (by norm_num)
  · rw [prod_stackLeaf (fun _ : Fin 2 => 0) ![0, 1] (fun b _ => ![a, c] b) (fun b => by fin_cases b <;> simp) hdisj]
    simp

/-! The recursion's blocks. -/

/-- The bus's blocks on a side (`BusBlocks::new`): the public table's one slot, then each owned table's slots in
`Table::OWNED` order, as (table, slot). -/
def busSlots : List (Table × ℕ) :=
  (.pub, 0) :: Bind.ownedList.flatMap fun T => (List.range T.nSlots).map (T, ·)

theorem prod_range_list (n : ℕ) (h : ℕ → E) : ∏ i ∈ range n, h i = ((List.range n).map h).prod := by
  rw [Finset.prod_eq_multiset_prod, Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.prod_coe]

theorem prod_flatMap {α : Type} (l : List α) (h : α → List E) :
    (l.flatMap h).prod = (l.map fun a => (h a).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, List.prod_append, ih, List.map_cons, List.prod_cons]

/-- Over the bus's blocks, each block of table `T` the `2^τ_T` rows of its slot, the leaves multiply to the product
over every slot of every row, where every table's height is `2^τ_T`. -/
theorem prod_busSlots (g : Slot → E) (w : Witness) (taus : Table → ℕ) (hh : ∀ T, w.height T = 2 ^ taus T) :
    (busSlots.map fun p => ∏ z ∈ range (2 ^ taus p.1), g (p.1, z, p.2)).prod = ((slots w).map g).prod := by
  set F := fun T : Table => ∏ z ∈ range (2 ^ taus T), ∏ i ∈ range T.nSlots, g (T, z, i)
  have hT : ∀ T : Table, (((List.range (w.height T)).flatMap fun z =>
      (List.range T.nSlots).map fun i => ((T, z, i) : Slot)).map g).prod = F T := fun T => by
    rw [List.map_flatMap, prod_flatMap, hh]
    simp only [F, prod_range_list, List.map_map, Function.comp_def]
  have hB : ∀ T : Table, (((List.range T.nSlots).map fun i => ((T, i) : Table × ℕ)).map
      fun p => ∏ z ∈ range (2 ^ taus p.1), g (p.1, z, p.2)).prod = F T := fun T => by
    simp only [F, List.map_map, Function.comp_def, ← prod_range_list]
    exact prod_comm
  have hpub : F .pub = ∏ z ∈ range (2 ^ taus .pub), g (.pub, z, 0) := by
    simp [F, Table.nSlots]
  rw [slots, List.map_flatMap, prod_flatMap, busSlots, List.map_cons, List.prod_cons, List.map_flatMap,
    prod_flatMap]
  simp only [hT, hB]
  rw [← hpub]
  simp only [Table.all, Bind.ownedList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  ring

/-! The honest roots as products over the slots. -/

/-- A list's product over its positions. -/
theorem prod_fin_getElem {α : Type} (l : List α) (h : α → E) : ∏ i : Fin l.length, h l[i] = (l.map h).prod := by
  rw [← List.ofFn_getElem_eq_map, List.prod_ofFn]
  rfl

/-- The bus's honest root over the pulls: each slot's `β + fp_A` of its key and limbs. -/
theorem pullRoot_eq_slots (s : State) (w : Witness) (f : Fin 5 → E) :
    pullRoot s w f =
      ((slots w).map fun e => f 0 + UnionSound.fpAt (Fin.tail f) (busTuple (key e, carried w e))).prod := by
  rw [pullRoot, UnionSound.prodAt, pulls, Multiset.map_map, ← prod_fin_getElem, Finset.prod_eq_multiset_prod]
  rfl

/-- The bus's honest root over the pushes, by position: slot `i`'s `β + fp_A` of its class-next slot's key and its
limbs. -/
theorem pushRoot_eq_fin (s : State) (w : Witness) (f : Fin 5 → E) :
    pushRoot s w f = ∏ i : Fin (slots w).length, (f 0 + UnionSound.fpAt (Fin.tail f)
      (busTuple (key (slots w)[classNext (fun i : Fin (slots w).length => slotClass s (slots w)[i]) i],
        carried w (slots w)[i]))) := by
  rw [pushRoot, UnionSound.prodAt, pushes, Multiset.map_map, Finset.prod_eq_multiset_prod]
  rfl

/-- The key a slot pushes: its class-next slot's (`classNext` over the slots' classes), at its position in the slots. -/
noncomputable def pushKey (s : State) (w : Witness) (e : Slot) : ℕ :=
  if h : (slots w).idxOf e < (slots w).length then
    key (slots w)[classNext (fun i : Fin (slots w).length => slotClass s (slots w)[i]) ⟨_, h⟩]
  else key e

theorem pushKey_getElem (s : State) (w : Witness) (i : Fin (slots w).length) :
    pushKey s w (slots w)[i] =
      key (slots w)[classNext (fun i : Fin (slots w).length => slotClass s (slots w)[i]) i] := by
  have hi : (slots w).idxOf (slots w)[i] = i := (slots_nodup w).idxOf_getElem i i.isLt
  have hlt : (slots w).idxOf (slots w)[i] < (slots w).length := by rw [hi]; exact i.isLt
  rw [pushKey, dif_pos hlt]
  congr 3
  exact Fin.ext hi

/-- The bus's honest root over the pushes: each slot's `β + fp_A` of the key it pushes and its limbs. -/
theorem pushRoot_eq_slots (s : State) (w : Witness) (f : Fin 5 → E) :
    pushRoot s w f =
      ((slots w).map fun e => f 0 + UnionSound.fpAt (Fin.tail f) (busTuple (pushKey s w e, carried w e))).prod := by
  rw [pushRoot_eq_fin, ← prod_fin_getElem]
  exact prod_congr rfl fun i _ => by rw [pushKey_getElem]

/-! The stacked layer's root. -/

/-- The stacked layer over the bus's blocks, block `b` of table `T`'s slot `i` at `2^τ_T` rows carrying `g` of its
slots, multiplies to the product of `g` over every slot, where the blocks fit in the `2^n` leaves and do not overlap
and every table's height is `2^τ_T`. -/
theorem root_eq_stack (w : Witness) (taus : Table → ℕ) (hh : ∀ T, w.height T = 2 ^ taus T) (g : Slot → E) {n : ℕ}
    (κ q : Fin busSlots.length → ℕ) (leaf : Fin busSlots.length → ℕ → E) (hκ : ∀ b, κ b = taus busSlots[b].1)
    (hin : ∀ b, 2 ^ κ b * q b + 2 ^ κ b ≤ 2 ^ n)
    (hdisj : ∀ b b', b ≠ b' → Disjoint (Ico (2 ^ κ b * q b) (2 ^ κ b * q b + 2 ^ κ b))
      (Ico (2 ^ κ b' * q b') (2 ^ κ b' * q b' + 2 ^ κ b')))
    (hleaf : ∀ b z, leaf b z = g (busSlots[b].1, z, busSlots[b].2)) :
    ∏ x ∈ range (2 ^ n), stackLeaf κ q leaf x = ((slots w).map g).prod := by
  rw [prod_stackLeaf κ q leaf hin hdisj, ← prod_busSlots g w taus hh, ← prod_fin_getElem]
  exact prod_congr rfl fun b _ => by rw [hκ]; exact prod_congr rfl fun z _ => hleaf b z

/-- The stacked layer's tree's root, `n` levels up, is the product of `g` over every slot. -/
theorem level_stack (w : Witness) (taus : Table → ℕ) (hh : ∀ T, w.height T = 2 ^ taus T) (g : Slot → E) {n : ℕ}
    (κ q : Fin busSlots.length → ℕ) (leaf : Fin busSlots.length → ℕ → E) (hκ : ∀ b, κ b = taus busSlots[b].1)
    (hin : ∀ b, 2 ^ κ b * q b + 2 ^ κ b ≤ 2 ^ n)
    (hdisj : ∀ b b', b ≠ b' → Disjoint (Ico (2 ^ κ b * q b) (2 ^ κ b * q b + 2 ^ κ b))
      (Ico (2 ^ κ b' * q b') (2 ^ κ b' * q b' + 2 ^ κ b')))
    (hleaf : ∀ b z, leaf b z = g (busSlots[b].1, z, busSlots[b].2)) :
    level (stackLeaf κ q leaf) n 0 = ((slots w).map g).prod := by
  rw [level_root]
  exact root_eq_stack w taus hh g κ q leaf hκ hin hdisj hleaf

/-- The honest root over the pulls is the root of the stacked layer of the slots' pull leaves. -/
theorem pullRoot_eq_stack (s : State) (w : Witness) (f : Fin 5 → E) (taus : Table → ℕ)
    (hh : ∀ T, w.height T = 2 ^ taus T) {n : ℕ} (κ q : Fin busSlots.length → ℕ) (leaf : Fin busSlots.length → ℕ → E)
    (hκ : ∀ b, κ b = taus busSlots[b].1) (hin : ∀ b, 2 ^ κ b * q b + 2 ^ κ b ≤ 2 ^ n)
    (hdisj : ∀ b b', b ≠ b' → Disjoint (Ico (2 ^ κ b * q b) (2 ^ κ b * q b + 2 ^ κ b))
      (Ico (2 ^ κ b' * q b') (2 ^ κ b' * q b' + 2 ^ κ b')))
    (hleaf : ∀ b z, leaf b z = f 0 + UnionSound.fpAt (Fin.tail f)
      (busTuple (key (busSlots[b].1, z, busSlots[b].2), carried w (busSlots[b].1, z, busSlots[b].2)))) :
    pullRoot s w f = level (stackLeaf κ q leaf) n 0 := by
  rw [pullRoot_eq_slots]
  exact (level_stack w taus hh _ κ q leaf hκ hin hdisj hleaf).symm

/-- The honest root over the pushes is the root of the stacked layer of the slots' push leaves. -/
theorem pushRoot_eq_stack (s : State) (w : Witness) (f : Fin 5 → E) (taus : Table → ℕ)
    (hh : ∀ T, w.height T = 2 ^ taus T) {n : ℕ} (κ q : Fin busSlots.length → ℕ) (leaf : Fin busSlots.length → ℕ → E)
    (hκ : ∀ b, κ b = taus busSlots[b].1) (hin : ∀ b, 2 ^ κ b * q b + 2 ^ κ b ≤ 2 ^ n)
    (hdisj : ∀ b b', b ≠ b' → Disjoint (Ico (2 ^ κ b * q b) (2 ^ κ b * q b + 2 ^ κ b))
      (Ico (2 ^ κ b' * q b') (2 ^ κ b' * q b' + 2 ^ κ b')))
    (hleaf : ∀ b z, leaf b z = f 0 + UnionSound.fpAt (Fin.tail f)
      (busTuple (pushKey s w (busSlots[b].1, z, busSlots[b].2), carried w (busSlots[b].1, z, busSlots[b].2)))) :
    pushRoot s w f = level (stackLeaf κ q leaf) n 0 := by
  rw [pushRoot_eq_slots]
  exact (level_stack w taus hh _ κ q leaf hκ hin hdisj hleaf).symm

end LeanVMCircuits.Rec.AirLink
