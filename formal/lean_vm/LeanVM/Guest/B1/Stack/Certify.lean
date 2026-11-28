/-
  LeanVM.Guest.B1.Stack.Certify

  `certify_stack` is sound: it places the stack `buildLayout` lays out.
-/

module

public import LeanVM.Guest.B1.Stack.Ranks
public import LeanVM.Guest.B1.Stack.Interface

/-!
# `certify_stack`, sound

`certify_stack_sound`: on a memory image of `2^κ` words, `11 ≤ κ ≤ 32`, a call of
`certify_stack` gives `MeaningCertifyStack`: for every layout `buildLayout` returns, from its kappa
sources at `kappa_base`, the call returns `g^stackLog` and, per stack block, its column's placement
(`StackPlaced`). The kappas: `columnKappas` is the kappa sources' exponents plus the adjustments
(`columnKappas_eq`), each block's that of its group (`colSrc_block`); the offsets: `stack`'s are
`stackOffsets`' (`stackOffsets_closed`), which the ranks match (`rank_offset`).
-/

namespace LeanVM.Guest.B1.Stack

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Guest.Value

@[expose] public section

/-! ## The kappas -/

/-- The kappa sources' exponents: `0`, the memory's log, the heights. -/
def kvOf (lm : ℕ) (hs : List ℕ) (i : ℕ) : ℕ := if i = 0 then 0 else if i = 1 then lm else hs.getD (i - 2) 0

/-- Each column's kappa source and adjustment. -/
def colSrc : List (ℕ × ℕ) :=
  [(1, 0), (1, 0), (7, qkeccakSlotBits)] ++ tables.flatMap fun t ↦ List.replicate t.width (2 + t.opcode, 0)

theorem columnKappas_eq (lm : ℕ) (hs : List ℕ) :
    columnKappas tables lm hs = colSrc.map fun p ↦ kvOf lm hs p.1 + p.2 := by
  unfold columnKappas colSrc
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_flatMap, List.map_replicate, kvOf]
  simp [opKeccak, show ∀ x : ℕ, ¬ (2 + x = 1) from fun x ↦ by omega]

set_option maxRecDepth 100000 in
theorem colSrc_block : ∀ b < 52, blockColumn b < colSrc.length ∧
    colSrc.getD (blockColumn b) (0, 0) = ((csG (grpOf b)).src, (csG (grpOf b)).adj) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem stackBlocks_length : stackBlocks.length = 52 := by decide +kernel

set_option maxRecDepth 100000 in
theorem blockColumns_nodup : (stackBlocks.map (·.column)).Nodup := by decide +kernel

set_option maxRecDepth 100000 in
theorem block_noSlot : ∀ b < 52, qkeccakSlot (blockColumn b) = none := by decide +kernel

/-- A block's kappa is its group's. -/
theorem blockKappa (lm : ℕ) (hs : List ℕ) {b : ℕ} (hb : b < 52) :
    (columnKappas tables lm hs).getD (blockColumn b) 0 = csKap (kvOf lm hs) (grpOf b) := by
  obtain ⟨hl, he⟩ := colSrc_block b hb
  rw [columnKappas_eq, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hl]
  simp only [Option.map_some, Option.getD_some]
  rw [List.getD_eq_getElem _ _ hl] at he
  rw [he]; rfl

/-! ## The lookup -/

theorem lookup_zip : ∀ (cs vs : List ℕ), cs.Nodup → cs.length = vs.length → ∀ b < cs.length,
    (cs.zip vs).lookup (cs.getD b 0) = some (vs.getD b 0)
  | [], _, _, _, b, hb => absurd hb (by simp)
  | c :: cs, [], _, h, _, _ => by simp at h
  | c :: cs, v :: vs, hnd, hl, b, hb => by
    rcases b with _ | b
    · simp
    · have hnd' := List.nodup_cons.1 hnd
      have hb' : b < cs.length := by simpa using hb
      have hne : cs.getD b 0 ≠ c := fun h ↦ hnd'.1 (by
        rw [← h, List.getD_eq_getElem _ _ hb']; exact List.getElem_mem hb')
      simp only [List.zip_cons_cons, List.lookup, List.getD_cons_succ]
      rw [show (cs.getD b 0 == c) = false from beq_false_of_ne hne]
      exact lookup_zip cs vs hnd'.2 (by simpa using hl) b hb'

/-! ## The layout -/

/-- What `buildLayout` returns, field by field. -/
theorem buildLayout_some {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (h : buildLayout bytecode lm rows = some layout) :
    layout.logMemory = lm ∧ lm ≤ 30 ∧ layout.tables = tables ∧
    layout.tableLogHeights = List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) rows tableLogFloors ∧
    (∀ t < nTables, layout.tableLogHeights.getD t 0 ≤ 30) ∧
    layout.stackLog = (stack (columnKappas tables lm layout.tableLogHeights)).2 ∧
    layout.placements = (columnKappas tables lm layout.tableLogHeights).zipIdx.map fun (kappa, column) ↦
      (match qkeccakSlot column with
        | some slot => ((stack (columnKappas tables lm layout.tableLogHeights)).1.lookup qkeccak).map
            (· + (slot <<< kappa))
        | none => (stack (columnKappas tables lm layout.tableLogHeights)).1.lookup column).map
        fun index ↦ ({ variableCount := kappa, index := index } : Placement) := by
  unfold buildLayout at h
  split at h
  · cases h
  · split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨-, hlm, hrows, -, -, hlen⟩ := hc
    refine ⟨rfl, by simpa [maxLogMemory] using hlm, rfl, rfl, fun t ht ↦ ?_, rfl, rfl⟩
    simp only [List.getD_eq_getElem?_getD, List.getElem?_zipWith]
    rcases hr : rows[t]? with _ | r
    · simp
    · have hrle := List.all_eq_true.1 hrows r (List.mem_of_getElem? hr)
      simp only [decide_eq_true_eq] at hrle
      have hlog : log2Ceil r ≤ 30 := log2Ceil_le_iff.mpr (by simpa [maxTableLog] using hrle)
      have hfl : ∀ t < nTables, (tableLogFloors[t]?).getD 0 ≤ 30 := by decide
      have hft := hfl t ht
      rcases hf : tableLogFloors[t]? with _ | f
      · simp
      · rw [hf] at hft
        simp only [Option.getD_some] at hft
        simp [hlog, hft]

/-! ## The theorem -/

theorem ranks_total {kv : ℕ → ℕ} {ρ : ℕ → ℕ} (h : Ranking kv ρ) :
    ∑ b ∈ Finset.range 52, 2 ^ csKap kv (grpOf b) = csTot kv ρ 8 := by
  rw [sum_blocks, h.sum_groups]
  unfold csTot csSize
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  have hg := h.lt r (Finset.mem_range.1 hr)
  rw [Finset.sum_congr rfl fun j hj ↦ by rw [grpOf_block _ hg j (Finset.mem_range.1 hj)]]
  simp

theorem stackOffsets_length (sizes : List ℕ) : (stackOffsets sizes).1.length = sizes.length := by
  simp only [stackOffsets]
  exact (stkFold_length (fun i ↦ 2 ^ sizes.getD i 0) _ _).trans (by simp)

theorem stack_eq (kappas : List ℕ) :
    stack kappas = ((stackBlocks.map (·.column)).zip
        (stackOffsets (stackBlocks.map fun b ↦ kappas.getD b.column 0)).1,
      max Whir.minLogStack (stackOffsets (stackBlocks.map fun b ↦ kappas.getD b.column 0)).2) := rfl

theorem kappaSources_get {kb : E} {rd : Reader} {lm : ℕ} {hs : List ℕ}
    (h : ReadsAt rd kb (kappaSources lm hs)) : ∀ i < 8, LoadHolds rd kb i (gen ^ kvOf lm hs i) := by
  intro i hi
  have hl : i < (kappaSources lm hs).length := by simp [kappaSources, nTables]; omega
  have := h i hl
  convert this using 1
  rcases i with _ | _ | i
  · simp [kappaSources, kvOf]
  · simp [kappaSources, kvOf]
  · simp [kappaSources, kvOf]

/-- **`certify_stack` is sound**: it places the stack of every layout `buildLayout` returns. -/
theorem certify_stack_sound {κ : ℕ} (hκ11 : 11 ≤ κ) (hκ : κ ≤ 32) (L : MemoryImage κ)
    (args rets : List E) (h : coreProgram.Rel L.read "certify_stack" args rets) :
    MeaningCertifyStack L.read args rets := by
  obtain ⟨σ, hp, -⟩ := (rel_iff_sem find_certify_stack _ _).mp h
  rw [certify_stack_params] at hp
  simp only [List.map_cons, List.map_nil] at hp
  subst hp
  intro bytecode lm rows layout hbl ht hkbR
  obtain ⟨hlm, hlm30, -, -, hh30, hsl, hpl⟩ := buildLayout_some hbl
  rw [← hlm] at hsl hpl hlm30
  set kv := kvOf layout.logMemory layout.tableLogHeights with hkvdef
  have hkv : ∀ i < 8, kv i ≤ 30 := fun i hi ↦ by
    rw [hkvdef]
    unfold kvOf
    by_cases h0 : i = 0
    · simp [h0]
    · by_cases h1 : i = 1
      · simp [h1, hlm30]
      · simp only [h0, h1, ↓reduceIte]
        exact hh30 _ (by simp only [nTables]; omega)
  obtain ⟨ρ, hρlt, hdes, hkap, out, hrets, houts⟩ :=
    certify_stack_guest hκ11 hκ L kv hkv _ _ rets h (kappaSources_get hkbR) ht
  have hR : Ranking kv ρ := ⟨hρlt, hdes⟩
  set kappas := columnKappas tables layout.logMemory layout.tableLogHeights with hkappas
  set sizes := stackBlocks.map fun b ↦ kappas.getD b.column 0 with hsizes
  have hszl : sizes.length = 52 := by simp [hsizes, stackBlocks_length]
  have hsz : ∀ b < 52, sizes.getD b 0 = csKap kv (grpOf b) := fun b hb ↦ by
    rw [hsizes, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (by rw [stackBlocks_length]; exact hb)]
    simp only [Option.map_some, Option.getD_some]
    rw [← blockKappa _ _ hb]
    simp [blockColumn, hkappas, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
      (show b < stackBlocks.length by rw [stackBlocks_length]; exact hb)]
  obtain ⟨hoff, hlog⟩ := stackOffsets_closed sizes
  rw [hszl] at hoff hlog
  have hsum : ∑ j ∈ Finset.range 52, 2 ^ sizes.getD j 0 = csTot kv ρ 8 := by
    rw [← ranks_total hR]
    exact Finset.sum_congr rfl fun j hj ↦ by rw [hsz j (Finset.mem_range.1 hj)]
  refine ⟨_, out, out * gen ^ 52, hrets, ?_, fun b hb ↦ ?_⟩
  · rw [hsl, stack_eq, ← hsizes, hlog, hsum]
    rfl
  · change b < stackBlocks.length at hb
    rw [stackBlocks_length] at hb
    obtain ⟨hcl, -⟩ := colSrc_block b hb
    have hkl : blockColumn b < kappas.length := by
      rw [hkappas, columnKappas_eq, List.length_map]; exact hcl
    obtain ⟨r, hr, hρr⟩ := hR.surj (grpOf b) (grpOf_facts b hb).1
    obtain ⟨-, hb0, hblen⟩ := grpOf_facts b hb
    set j := b - (csG (grpOf b)).b0
    have hbj : b = (csG (ρ r)).b0 + j := by rw [hρr]; omega
    have hjl : j < (csG (ρ r)).len := by rw [hρr]; omega
    obtain ⟨ho, hk⟩ := houts r hr j hjl
    rw [← hbj] at ho
    rw [show 52 + (csG (ρ r)).b0 + j = 52 + b by omega] at hk
    -- the placement
    have hlook : ((stackBlocks.map (·.column)).zip (stackOffsets sizes).1).lookup (blockColumn b) =
        some ((stackOffsets sizes).1.getD b 0) := by
      have := lookup_zip (stackBlocks.map (·.column)) (stackOffsets sizes).1 blockColumns_nodup
        (by rw [stackOffsets_length, List.length_map, hszl, stackBlocks_length]) b
        (by rw [List.length_map, stackBlocks_length]; exact hb)
      rw [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem (show b < stackBlocks.length by rw [stackBlocks_length]; exact hb)] at this
      simpa [blockColumn, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show b < stackBlocks.length by rw [stackBlocks_length]; exact hb)] using this
    refine ⟨⟨kappas.getD (blockColumn b) 0, (stackOffsets sizes).1.getD b 0⟩, ?_, ?_, ?_⟩
    · rw [hpl, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx,
        List.getElem?_eq_getElem hkl]
      simp only [Option.map_some, Option.getD_some, Nat.zero_add, block_noSlot b hb]
      rw [stack_eq, ← hsizes, hlook]
      simp [List.getElem?_eq_getElem hkl]
    · show LoadHolds L.read out b (gen ^ (stackOffsets sizes).1.getD b 0)
      rw [hoff b hb]
      convert ho using 2
      rw [← rank_offset hR hr hjl, ← hbj]
      unfold stkBeforeSum
      have hf : (Finset.range 52).filter (fun x ↦ StkBefore (fun j ↦ sizes.getD j 0) x b) =
          (Finset.range 52).filter (fun x ↦ StkBefore (fun b ↦ csKap kv (grpOf b)) x b) :=
        Finset.filter_congr fun x hx ↦ by
          simp only [StkBefore]; rw [hsz x (Finset.mem_range.1 hx), hsz b hb]
      rw [hf]
      exact Finset.sum_congr rfl fun x hx ↦ by
        show 2 ^ sizes.getD x 0 = 2 ^ csKap kv (grpOf x)
        rw [hsz x (Finset.mem_range.1 (Finset.mem_filter.1 hx).1)]
    · rw [loadHolds_mul_gen_pow]
      show LoadHolds L.read out (52 + b) (gen ^ (kappas.getD (blockColumn b) 0))
      rw [hkappas, blockKappa _ _ hb, ← hρr]
      exact hk

end
end LeanVM.Guest.B1.Stack
