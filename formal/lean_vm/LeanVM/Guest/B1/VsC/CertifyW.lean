/-
  LeanVM.Guest.B1.VsC.CertifyW

  `certify_stack`'s own words on a layout, and the stack they place.
-/

module

public import LeanVM.Guest.B1.VsC.CertifyF

/-!
# `certify_stack`'s own words

On a layout `buildLayout` returns with `stackLog ≤ 30` (so every group's `κ ≤ 30`,
`cs_layout`), the honest order `ρ` is a ranking, and the node's buffers hold (`csWords`): the
groups' keys, their sizes, the order `g^ρ(r)`, each group's offset `g^(csTot (rank gi))`, then per
block its offset and its `g^κ`. `csOuts_placed`: those outputs place the layout's stack.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Stack LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The stack's block sizes, as `stack` reads them. -/
def csSizes (layout : Layout) : List ℕ :=
  stackBlocks.map fun b ↦ (columnKappas tables layout.logMemory layout.tableLogHeights).getD b.column 0

theorem csSizes_length (layout : Layout) : (csSizes layout).length = 52 := by
  simp [csSizes, stackBlocks_length]

theorem csSizes_get (layout : Layout) {b : ℕ} (hb : b < 52) :
    (csSizes layout).getD b 0 = csKap (csKv layout) (grpOf b) := by
  rw [csSizes, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by rw [stackBlocks_length]; exact hb)]
  simp only [Option.map_some, Option.getD_some]
  rw [← blockKappa _ _ hb]
  simp [blockColumn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
    (show b < stackBlocks.length by rw [stackBlocks_length]; exact hb)]

/-- **A layout `buildLayout` returns, its stack within `2^30`**: every group's `κ ≤ 30`, its stack's
log `max 16 (log2Ceil T)`, `T` the blocks' total, at most `2^30`. -/
theorem cs_layout {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hbl : buildLayout bytecode lm rows = some layout) (hL : layout.stackLog ≤ 30) :
    (∀ gi < 8, csKap (csKv layout) gi ≤ 30) ∧
      layout.stackLog = max 16 (log2Ceil (∑ b ∈ Finset.range 52, 2 ^ csKap (csKv layout) (grpOf b))) ∧
      ∑ b ∈ Finset.range 52, 2 ^ csKap (csKv layout) (grpOf b) ≤ 2 ^ 30 := by
  obtain ⟨hlm, -, -, -, -, hsl, -⟩ := buildLayout_some hbl
  rw [← hlm] at hsl
  obtain ⟨-, hlog⟩ := stackOffsets_closed (csSizes layout)
  rw [csSizes_length] at hlog
  have hsum : ∑ j ∈ Finset.range 52, 2 ^ (csSizes layout).getD j 0 =
      ∑ b ∈ Finset.range 52, 2 ^ csKap (csKv layout) (grpOf b) :=
    Finset.sum_congr rfl fun j hj => by rw [csSizes_get layout (Finset.mem_range.1 hj)]
  have hst : layout.stackLog = max 16 (log2Ceil (∑ b ∈ Finset.range 52, 2 ^ csKap (csKv layout) (grpOf b))) := by
    rw [hsl, stack_eq]
    show max Whir.minLogStack (stackOffsets (csSizes layout)).2 = _
    rw [hlog, hsum]; rfl
  have hT : ∑ b ∈ Finset.range 52, 2 ^ csKap (csKv layout) (grpOf b) ≤ 2 ^ 30 := by
    have h1 := log2Ceil_le_iff.mp (le_trans (le_max_right 16 _) (hst ▸ hL))
    exact h1
  refine ⟨fun gi hgi => ?_, hst, hT⟩
  have hb := groups_b0_le gi hgi
  have hlen := (csGroups_facts gi hgi).2.2.1
  have hg := grpOf_block gi hgi 0 (by omega)
  rw [Nat.add_zero] at hg
  have h1 : 2 ^ csKap (csKv layout) gi ≤ ∑ b ∈ Finset.range 52, 2 ^ csKap (csKv layout) (grpOf b) := by
    have := Finset.single_le_sum (f := fun b => 2 ^ csKap (csKv layout) (grpOf b)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (show (csG gi).b0 < 52 by omega))
    simp only [hg] at this
    exact this
  by_contra hc
  have : 2 ^ 31 ≤ 2 ^ csKap (csKv layout) gi := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-! ## The words -/

section
variable (layout : Layout)

/-- The honest ranking. -/
abbrev csρ : ℕ → ℕ := csRho (stackKappas layout)

/-- Group `gi`'s offset: the total of the groups ranked before it. -/
def csAtW (gi : ℕ) : E := gen ^ csTot (csKv layout) (csρ layout) (csRk (stackKappas layout) gi)

/-- Block `b`'s offset. -/
def csOffW (b : ℕ) : E :=
  gen ^ (csTot (csKv layout) (csρ layout) (csRk (stackKappas layout) (grpOf b)) +
    (b - (csG (grpOf b)).b0) * 2 ^ csKap (csKv layout) (grpOf b))

/-- The outputs: the blocks' offsets, then their `g^κ`. -/
def csOutsW : List E :=
  (List.range 52).map (csOffW layout) ++ (List.range 52).map fun b => gen ^ csKap (csKv layout) (grpOf b)

/-- **`certify_stack`'s own words** from its cursor `c`: its five buffers. -/
def csWords (c : ℕ) : Words :=
  [(c, (List.range 8).map (csKeyW (csKv layout))), (c + 8, (List.range 8).map fun gi => gen ^ csSize (csKv layout) gi),
    (c + 16, (csOrd (stackKappas layout)).map Prover.count), (c + 24, (List.range 8).map (csAtW layout)),
    (c + 32, csOutsW layout)]

end

theorem csOutsW_length (layout : Layout) : (csOutsW layout).length = 104 := by simp [csOutsW]

theorem csOutsW_off (layout : Layout) {b : ℕ} (hb : b < 52) : (csOutsW layout)[b]'(by
    rw [csOutsW_length]; omega) = csOffW layout b := by
  simp [csOutsW, List.getElem_append_left (show b < ((List.range 52).map (csOffW layout)).length by simp; omega)]

theorem csOutsW_kap (layout : Layout) {b : ℕ} (hb : b < 52) : (csOutsW layout)[52 + b]'(by
    rw [csOutsW_length]; omega) = gen ^ csKap (csKv layout) (grpOf b) := by
  simp [csOutsW, List.getElem_append_right (show ((List.range 52).map (csOffW layout)).length ≤ 52 + b by simp)]

/-- **The outputs place the stack.** -/
theorem csOuts_placed {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hbl : buildLayout bytecode lm rows = some layout) (hL : layout.stackLog ≤ 30) {rd : Reader} {out : E}
    (hr : ReadsAt rd out (csOutsW layout)) :
    StackPlaced rd layout (gen ^ layout.stackLog) out (out * gen ^ 52) := by
  obtain ⟨hk30, -, -⟩ := cs_layout hbl hL
  obtain ⟨hperm, hR, -⟩ := csOrd_facts layout fun g hg => by have := hk30 g hg; omega
  obtain ⟨hrk, -⟩ := csRk_facts hperm
  obtain ⟨hlm, -, -, -, -, hsl, hpl⟩ := buildLayout_some hbl
  rw [← hlm] at hsl hpl
  set kv := csKv layout with hkv
  set kappas := columnKappas tables layout.logMemory layout.tableLogHeights with hkappas
  set sizes := csSizes layout with hsizes
  obtain ⟨hoff, -⟩ := stackOffsets_closed sizes
  rw [hsizes, csSizes_length] at hoff
  refine ⟨rfl, fun b hb => ?_⟩
  change b < stackBlocks.length at hb
  rw [stackBlocks_length] at hb
  obtain ⟨hcl, -⟩ := colSrc_block b hb
  have hkl : blockColumn b < kappas.length := by
    rw [hkappas, columnKappas_eq, List.length_map]; exact hcl
  obtain ⟨hg8, hb0, hblen⟩ := grpOf_facts b hb
  obtain ⟨hr8, hρr⟩ := hrk (grpOf b) hg8
  set r := csRk (stackKappas layout) (grpOf b)
  set j := b - (csG (grpOf b)).b0
  have hjl : j < (csG (csρ layout r)).len := by show j < (csG (csRho _ r)).len; rw [hρr]; omega
  have hbj : (csG (csρ layout r)).b0 + j = b := by show (csG (csRho _ r)).b0 + j = b; rw [hρr]; omega
  have hlook : ((stackBlocks.map (·.column)).zip (stackOffsets sizes).1).lookup (blockColumn b) =
      some ((stackOffsets sizes).1.getD b 0) := by
    have := lookup_zip (stackBlocks.map (·.column)) (stackOffsets sizes).1 blockColumns_nodup
      (by rw [stackOffsets_length, List.length_map, hsizes, csSizes_length, stackBlocks_length]) b
      (by rw [List.length_map, stackBlocks_length]; exact hb)
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (show b < stackBlocks.length by rw [stackBlocks_length]; exact hb)] at this
    simpa [blockColumn, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show b < stackBlocks.length by rw [stackBlocks_length]; exact hb)] using this
  refine ⟨⟨kappas.getD (blockColumn b) 0, (stackOffsets sizes).1.getD b 0⟩, ?_, ?_, ?_⟩
  · rw [hpl, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx,
      List.getElem?_eq_getElem hkl]
    simp only [Option.map_some, Option.getD_some, Nat.zero_add, block_noSlot b hb]
    rw [stack_eq, show (stackBlocks.map fun b => kappas.getD b.column 0) = sizes from rfl, hlook]
    simp [List.getElem?_eq_getElem hkl]
  · show LoadHolds rd out b (gen ^ (stackOffsets sizes).1.getD b 0)
    have hw := hr b (by rw [csOutsW_length]; omega)
    rw [csOutsW_off layout hb] at hw
    convert hw using 2
    rw [hoff b hb]
    have hro := rank_offset hR hr8 hjl
    rw [hbj] at hro
    have hf : (Finset.range 52).filter (fun x ↦ StkBefore (fun j ↦ sizes.getD j 0) x b) =
        (Finset.range 52).filter (fun x ↦ StkBefore (fun b ↦ csKap kv (grpOf b)) x b) :=
      Finset.filter_congr fun x hx ↦ by
        simp only [StkBefore]; rw [hsizes, csSizes_get layout (Finset.mem_range.1 hx), csSizes_get layout hb]
    unfold stkBeforeSum
    rw [hf]
    have : ∑ x ∈ (Finset.range 52).filter (fun x ↦ StkBefore (fun b ↦ csKap kv (grpOf b)) x b), 2 ^ sizes.getD x 0 =
        stkBeforeSum (fun b ↦ csKap kv (grpOf b)) 52 b :=
      Finset.sum_congr rfl fun x hx => by
        rw [hsizes, csSizes_get layout (Finset.mem_range.1 (Finset.mem_filter.1 hx).1)]
    rw [this, hro, csOffW, show csRho (stackKappas layout) r = grpOf b from hρr]
  · rw [loadHolds_mul_gen_pow]
    show LoadHolds rd out (52 + b) (gen ^ (kappas.getD (blockColumn b) 0))
    rw [hkappas, blockKappa _ _ hb]
    have hw := hr (52 + b) (by rw [csOutsW_length]; omega)
    rw [csOutsW_kap layout hb] at hw
    exact hw

end
end LeanVM.Guest.B1.VsC
