/-
  LeanVM.Protocol.Relation.Placement

  The whole-column stack's placements: every block starts at a multiple of its size and ends
  within the stack, so a claim's stack point reads exactly its column's rows.
-/

module

public import Statement.Verifier.Lib
import LeanVM.Facts.Stack

/-!
# Placements

`stack_offsets` (`multilinear.rs`) lays the blocks end to end largest first, so each block starts
after blocks no smaller than itself, at a multiple of its size, and ends within the total
(`stackOffsets_aligned`). `buildLayout` places a column with a block of its own at its block, and a
column `q_keccak` carries at `q_keccak`'s block plus its slot times its height
(`placement_aligned`): every placement of a layout `buildLayout` gives starts at a multiple of
`2^variableCount` and ends within `2^stackLog`.
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters

@[expose] public section

/-! ## `stack_offsets` -/

section Offsets

variable (size : ℕ → ℕ)

/-- One block laid: its offset written, the total advanced. -/
def offsetStep (acc : List ℕ × ℕ) (i : ℕ) : List ℕ × ℕ := (acc.1.set i acc.2, acc.2 + 2 ^ size i)

theorem foldl_offsetStep_snd : ∀ (o : List ℕ) (acc : List ℕ × ℕ),
    (o.foldl (offsetStep size) acc).2 = acc.2 + (o.map fun i ↦ 2 ^ size i).sum
  | [], acc => by simp
  | i :: o, acc => by
    simp only [List.foldl_cons, foldl_offsetStep_snd o, offsetStep, List.map_cons, List.sum_cons]
    omega

theorem foldl_offsetStep_length : ∀ (o : List ℕ) (acc : List ℕ × ℕ),
    (o.foldl (offsetStep size) acc).1.length = acc.1.length
  | [], _ => rfl
  | i :: o, acc => by
    simp only [List.foldl_cons, foldl_offsetStep_length o, offsetStep, List.length_set]

theorem foldl_offsetStep_getD_of_not_mem : ∀ (o : List ℕ) (acc : List ℕ × ℕ) (i : ℕ), i ∉ o →
    (o.foldl (offsetStep size) acc).1.getD i 0 = acc.1.getD i 0
  | [], _, _, _ => rfl
  | j :: o, acc, i, hi => by
    simp only [List.mem_cons, not_or] at hi
    simp only [List.foldl_cons]
    rw [foldl_offsetStep_getD_of_not_mem o _ i hi.2]
    simp only [offsetStep, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hi.1)]

/-- **Each block laid after blocks no smaller is aligned and within the total.** -/
theorem foldl_offsetStep_spec : ∀ (o : List ℕ) (acc : List ℕ × ℕ),
    o.Pairwise (fun i j ↦ size j ≤ size i) → o.Nodup → (∀ i ∈ o, i < acc.1.length) →
    (∀ j ∈ o, 2 ^ size j ∣ acc.2) → ∀ i ∈ o,
      2 ^ size i ∣ (o.foldl (offsetStep size) acc).1.getD i 0 ∧
        (o.foldl (offsetStep size) acc).1.getD i 0 + 2 ^ size i ≤
          (o.foldl (offsetStep size) acc).2
  | [], _, _, _, _, _, i, hi => absurd hi List.not_mem_nil
  | a :: o, acc, hp, hn, hl, hd, i, hi => by
    rw [List.pairwise_cons] at hp
    rw [List.nodup_cons] at hn
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [foldl_offsetStep_getD_of_not_mem size o _ i hn.1, foldl_offsetStep_snd]
      have hil : i < acc.1.length := hl i List.mem_cons_self
      simp only [offsetStep, List.getD_eq_getElem?_getD, List.getElem?_set_self hil,
        Option.getD_some]
      exact ⟨hd i List.mem_cons_self, by omega⟩
    · refine foldl_offsetStep_spec o _ hp.2 hn.2 (fun j hj ↦ ?_) (fun j hj ↦ ?_) i hi
      · simp only [offsetStep, List.length_set]; exact hl j (List.mem_cons_of_mem _ hj)
      · simp only [offsetStep]
        refine Nat.dvd_add (hd j (List.mem_cons_of_mem _ hj)) ?_
        exact Nat.pow_dvd_pow 2 (hp.1 j hj)

end Offsets

/-- **`stack_offsets` aligns every block and keeps it within the total**: block `i` starts at a
multiple of `2^sizes[i]` and ends within `2^totalLog`. -/
theorem stackOffsets_aligned (sizes : List ℕ) {i : ℕ} (hi : i < sizes.length) :
    2 ^ sizes.getD i 0 ∣ (stackOffsets sizes).1.getD i 0 ∧
      (stackOffsets sizes).1.getD i 0 + 2 ^ sizes.getD i 0 ≤ 2 ^ (stackOffsets sizes).2 := by
  let size := fun i ↦ sizes.getD i 0
  let le := fun i j ↦ decide (size j < size i) || (decide (size i = size j) && decide (i ≤ j))
  let order := (List.range sizes.length).mergeSort le
  have hperm : order.Perm (List.range sizes.length) := List.mergeSort_perm _ _
  have hsorted : order.Pairwise (fun i j ↦ size j ≤ size i) := by
    refine (List.pairwise_mergeSort (le := le) ?_ ?_ _).imp fun {a b} h ↦ ?_
    · intro a b c hab hbc
      simp only [le, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hab hbc ⊢
      omega
    · intro a b
      simp only [le, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
      omega
    · simp only [le, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
      omega
  have hspec := foldl_offsetStep_spec size order (List.replicate sizes.length 0, 0) hsorted
    (hperm.nodup_iff.mpr List.nodup_range)
    (fun j hj ↦ by simpa using hperm.subset hj)
    (fun j _ ↦ dvd_zero _) i (hperm.symm.subset (List.mem_range.mpr hi))
  have htot : (order.foldl (offsetStep size) (List.replicate sizes.length 0, 0)).2 ≤
      2 ^ (stackOffsets sizes).2 := by
    rw [foldl_offsetStep_snd, stackOffsets_snd]
    have hsum : (order.map fun i ↦ 2 ^ size i).sum = (sizes.map fun k ↦ 2 ^ k).sum := by
      rw [(hperm.map _).sum_eq, ← range_map_getD sizes 0 (fun k ↦ 2 ^ k)]
    rw [zero_add, hsum]
    exact (log2Ceil_le_iff _ _).mp le_rfl
  exact ⟨hspec.1, hspec.2.trans htot⟩

/-! ## The layout's placements -/

/-- The tables' widths and opcodes. -/
theorem tables_widths_opcodes :
    tables.map (fun t ↦ (t.width, t.opcode)) = [(7, 0), (9, 1), (5, 2), (10, 3), (14, 4), (68, 5)] := by
  decide +kernel

/-- `KECCAK`'s first global column. -/
theorem keccakBase_eq : globalColumnBases.getD opKeccak 0 = 48 := by decide +kernel

/-- Every column's log-size: the memory's, `q_keccak`'s, then each table's height over its width. -/
theorem columnKappas_eq (lm : ℕ) (hs : List ℕ) :
    columnKappas tables lm hs = [lm, lm, hs.getD opKeccak 0 + qkeccakSlotBits] ++
      (List.replicate 7 (hs.getD 0 0) ++ List.replicate 9 (hs.getD 1 0) ++
        List.replicate 5 (hs.getD 2 0) ++ List.replicate 10 (hs.getD 3 0) ++
        List.replicate 14 (hs.getD 4 0)) ++ List.replicate 68 (hs.getD 5 0) := by
  have h : tables.flatMap (fun t ↦ List.replicate t.width (hs.getD t.opcode 0)) =
      (tables.map fun t ↦ (t.width, t.opcode)).flatMap fun x ↦ List.replicate x.1 (hs.getD x.2 0) := by
    rw [List.flatMap_map]
  simp only [columnKappas, h, tables_widths_opcodes, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc]

/-- A column `q_keccak` carries is a `KECCAK` column, at a slot below `2^slot_bits`. -/
theorem qkeccakSlot_facts {c s : ℕ} (h : qkeccakSlot c = some s) :
    48 ≤ c ∧ c < 48 + 68 ∧ s < 2 ^ qkeccakSlotBits := by
  have hspare : ∀ k < qkeccakSpare, spareLocal k < 68 ∧ qkeccakSlots + k < 64 := by decide
  have h64 : 2 ^ qkeccakSlotBits = 64 := by decide
  have h8 : keccakIn = 8 := by decide
  have h33 : keccakOut = 33 := by decide
  unfold qkeccakSlot at h
  simp only [keccakBase_eq] at h
  rw [h64]
  split at h
  · next hc =>
    split at h
    · next k hk =>
      have hkm := List.mem_of_find?_eq_some hk
      have hke := List.find?_some hk
      simp only [decide_eq_true_eq] at hke
      have := hspare k (List.mem_range.mp hkm)
      simp only [Option.some.injEq] at h
      subst h
      omega
    · split at h
      · next hl =>
        simp only [Option.some.injEq] at h
        subst h
        rw [h8, h33] at hl
        rw [h8]
        omega
      · cases h
  · cases h

theorem lookup_zip_some {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l₁ : List α} {l₂ : List β} {a : α} {b : β}, (l₁.zip l₂).lookup a = some b →
      ∃ i : ℕ, l₁[i]? = some a ∧ l₂[i]? = some b
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: xs, y :: ys, a, b, h => by
    simp only [List.zip_cons_cons, List.lookup_cons] at h
    split at h
    · next hx =>
      simp only [Option.some.injEq] at h
      exact ⟨0, by simp [beq_iff_eq.mp hx], by simp [h]⟩
    · obtain ⟨i, h1, h2⟩ := lookup_zip_some h
      exact ⟨i + 1, by simpa using h1, by simpa using h2⟩

/-- **Every placement of a layout `buildLayout` gives is aligned and within the stack**: it starts
at a multiple of `2^variableCount` and ends within `2^stackLog`. -/
theorem placement_aligned {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (h : buildLayout bytecode lm rows = some layout) {c : ℕ} {p : Placement}
    (hp : layout.placements.getD c none = some p) :
    2 ^ p.variableCount ∣ p.index ∧ p.index + 2 ^ p.variableCount ≤ 2 ^ layout.stackLog := by
  unfold buildLayout at h
  split at h
  · cases h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      dsimp only at hp ⊢
      generalize hk : columnKappas tables lm _ = kappas at hp ⊢
      generalize hsz : stackOffsets (stackBlocks.map fun b ↦ kappas.getD b.column 0) = so at hp ⊢
      have hst : stack kappas = ((stackBlocks.map (·.column)).zip so.1, max Whir.minLogStack so.2) := by
        simp only [stack, hsz]
      simp only [hst] at hp ⊢
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx, zero_add] at hp
      rcases hkc : kappas[c]? with _ | kappa
      · simp [hkc] at hp
      simp only [hkc, Option.map_some, Option.getD_some] at hp
      have hsizes : ∀ {i : ℕ} {b : StackBlock}, stackBlocks[i]? = some b →
          i < (stackBlocks.map fun b ↦ kappas.getD b.column 0).length ∧
            (stackBlocks.map fun b ↦ kappas.getD b.column 0).getD i 0 = kappas.getD b.column 0 := by
        intro i b hb
        have hi : i < stackBlocks.length := (List.getElem?_eq_some_iff.mp hb).1
        refine ⟨by simpa using hi, ?_⟩
        simp [List.getD_eq_getElem?_getD, hb]
      have hmax : 2 ^ so.2 ≤ 2 ^ max Whir.minLogStack so.2 :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      split at hp
      · next slot hslot =>
        obtain ⟨o, ho, hp⟩ := Option.map_eq_some_iff.mp hp
        obtain ⟨o', ho', rfl⟩ := Option.map_eq_some_iff.mp ho
        obtain ⟨i, hi1, hi2⟩ := lookup_zip_some ho'
        rw [List.getElem?_map] at hi1
        obtain ⟨b, hb, hbc⟩ := Option.map_eq_some_iff.mp hi1
        obtain ⟨hil, hgi⟩ := hsizes hb
        have hal := stackOffsets_aligned _ hil
        rw [hsz, hgi, hbc] at hal
        have hog : so.1.getD i 0 = o' := by simp [List.getD_eq_getElem?_getD, hi2]
        rw [hog] at hal
        obtain ⟨hc1, hc2, hs⟩ := qkeccakSlot_facts hslot
        have hkq : kappas.getD qkeccak 0 = kappa + qkeccakSlotBits := by
          have hkc' : kappas.getD c 0 = kappa := by simp [List.getD_eq_getElem?_getD, hkc]
          rw [← hk, columnKappas_eq] at hkc' ⊢
          have hc' : c = 48 + (c - 48) := by omega
          rw [hc'] at hkc'
          simp only [List.getD_eq_getElem?_getD] at hkc' ⊢
          rw [List.getElem?_append_right (by simp)] at hkc'
          simp only [List.length_append, List.length_cons, List.length_replicate,
            List.length_nil] at hkc'
          rw [List.getElem?_replicate, ite_eq_left (by omega)] at hkc'
          simp only [Option.getD_some] at hkc'
          simp [qkeccak, opKeccak, ← hkc']
        rw [hkq] at hal
        subst hp
        refine ⟨?_, ?_⟩
        · simp only [Nat.shiftLeft_eq]
          refine Nat.dvd_add ((Nat.pow_dvd_pow 2 (by omega)).trans hal.1) (dvd_mul_left _ _)
        · simp only [Nat.shiftLeft_eq]
          have h6 : (slot + 1) * 2 ^ kappa ≤ 2 ^ (kappa + qkeccakSlotBits) := by
            rw [pow_add, mul_comm (2 ^ kappa)]
            exact Nat.mul_le_mul_right _ (by omega)
          have := hal.2
          calc o' + slot * 2 ^ kappa + 2 ^ kappa = o' + (slot + 1) * 2 ^ kappa := by ring
            _ ≤ o' + 2 ^ (kappa + qkeccakSlotBits) := by omega
            _ ≤ 2 ^ so.2 := this
            _ ≤ _ := hmax
      · obtain ⟨o, ho, hp⟩ := Option.map_eq_some_iff.mp hp
        obtain ⟨i, hi1, hi2⟩ := lookup_zip_some ho
        rw [List.getElem?_map] at hi1
        obtain ⟨b, hb, hbc⟩ := Option.map_eq_some_iff.mp hi1
        obtain ⟨hil, hgi⟩ := hsizes hb
        have hal := stackOffsets_aligned _ hil
        rw [hsz, hgi, hbc] at hal
        have hog : so.1.getD i 0 = o := by simp [List.getD_eq_getElem?_getD, hi2]
        have hkc' : kappas.getD c 0 = kappa := by simp [List.getD_eq_getElem?_getD, hkc]
        rw [hog, hkc'] at hal
        subst hp
        exact ⟨hal.1, hal.2.trans hmax⟩
    · cases h

/-- `GLOBAL_COLUMN_BASES` and `TABLE_WIDTHS`. -/
theorem globalColumnBases_eq : globalColumnBases = [3, 10, 19, 24, 34, 48] := by decide +kernel

theorem tableWidths_eq : tableWidths = [7, 9, 5, 10, 14, 68] := by decide +kernel

/-- **A table column's log-size is its table's height.** -/
theorem columnKappas_table (lm : ℕ) (hs : List ℕ) {t j : ℕ} (ht : t < nTables)
    (hj : j < tableWidths.getD t 0) :
    (columnKappas tables lm hs).getD (globalColumnBases.getD t 0 + j) 0 = hs.getD t 0 := by
  rw [columnKappas_eq, globalColumnBases_eq]
  rw [tableWidths_eq] at hj
  simp only [nTables] at ht
  simp only [List.getD_eq_getElem?_getD]
  interval_cases t <;> simp at hj <;> simp [opKeccak] <;> interval_cases j <;> rfl

/-- The memory's columns' log-size is the memory's. -/
theorem columnKappas_memory (lm : ℕ) (hs : List ℕ) :
    (columnKappas tables lm hs).getD memory0 0 = lm ∧ (columnKappas tables lm hs).getD memory1 0 = lm ∧
      (columnKappas tables lm hs).getD qkeccak 0 = hs.getD opKeccak 0 + qkeccakSlotBits := by
  rw [columnKappas_eq]
  simp [memory0, memory1, qkeccak]

/-- **A placement's variables are its column's log-size.** -/
theorem placement_variableCount {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (h : buildLayout bytecode lm rows = some layout) {c : ℕ} {p : Placement}
    (hp : layout.placements.getD c none = some p) :
    p.variableCount = (columnKappas tables layout.logMemory layout.tableLogHeights).getD c 0 := by
  unfold buildLayout at h
  split at h
  · cases h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      dsimp only at hp ⊢
      generalize columnKappas tables lm _ = kappas at hp ⊢
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx,
        zero_add] at hp ⊢
      rcases hkc : kappas[c]? with _ | kappa
      · simp [hkc] at hp
      simp only [hkc, Option.map_some, Option.getD_some] at hp ⊢
      obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hp
      rfl
    · cases h

theorem stackOffsets_length (sizes : List ℕ) : (stackOffsets sizes).1.length = sizes.length := by
  have := foldl_offsetStep_length (fun i ↦ sizes.getD i 0)
    ((List.range sizes.length).mergeSort fun i j ↦
      decide (sizes.getD j 0 < sizes.getD i 0) ||
        (decide (sizes.getD i 0 = sizes.getD j 0) && decide (i ≤ j)))
    (List.replicate sizes.length 0, 0)
  rw [List.length_replicate] at this
  exact this

theorem lookup_zip_isSome {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l₁ : List α} {l₂ : List β} {a : α}, l₁.length ≤ l₂.length → a ∈ l₁ →
      ((l₁.zip l₂).lookup a).isSome
  | [], _, _, _, h => absurd h List.not_mem_nil
  | _ :: _, [], _, hl, _ => by simp at hl
  | x :: xs, y :: ys, a, hl, ha => by
    simp only [List.zip_cons_cons, List.lookup_cons]
    split
    · rfl
    · next hx =>
      have : a ∈ xs := by
        rcases List.mem_cons.mp ha with rfl | h
        · simp at hx
        · exact h
      exact lookup_zip_isSome (by simpa using hl) this

/-- Every column but the `KECCAK` output lanes has a block of its own or a slot of `q_keccak`. -/
theorem column_placed : ∀ c < 116, ¬ (81 ≤ c ∧ c < 106) →
    (qkeccakSlot c).isSome ∨ c ∈ stackBlocks.map (·.column) := by
  decide +kernel

theorem qkeccak_mem_stackBlocks : qkeccak ∈ stackBlocks.map (·.column) := by decide +kernel

/-- **Every column but the `KECCAK` output lanes is placed**: a layout `buildLayout` gives has a
placement for it. -/
theorem placement_isSome {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (h : buildLayout bytecode lm rows = some layout) {c : ℕ} (hc : c < 116)
    (hk : ¬ (globalColumnBases.getD opKeccak 0 + keccakOut ≤ c ∧
      c < globalColumnBases.getD opKeccak 0 + keccakOut + keccakStateLanes)) :
    (layout.placements.getD c none).isSome := by
  have h33 : keccakOut = 33 := by decide
  rw [keccakBase_eq, h33] at hk
  have hcol := column_placed c hc (by simpa [keccakStateLanes] using hk)
  unfold buildLayout at h
  split at h
  · cases h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      dsimp only
      generalize hk' : columnKappas tables lm _ = kappas
      have hlen : kappas.length = 116 := by rw [← hk', columnKappas_eq]; simp
      generalize hsz : stackOffsets (stackBlocks.map fun b ↦ kappas.getD b.column 0) = so
      have hst : stack kappas = ((stackBlocks.map (·.column)).zip so.1, max Whir.minLogStack so.2) := by
        simp only [stack, hsz]
      have hsl : (stackBlocks.map (·.column)).length ≤ so.1.length := by
        rw [← hsz, stackOffsets_length]; simp
      simp only [hst]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx, zero_add,
        List.getElem?_eq_getElem (show c < kappas.length by omega), Option.map_some,
        Option.getD_some]
      split
      · simp only [Option.isSome_map]
        exact lookup_zip_isSome hsl qkeccak_mem_stackBlocks
      · next hn =>
        simp only [Option.isSome_map]
        rcases hcol with h1 | h1
        · simp [hn] at h1
        · exact lookup_zip_isSome hsl h1
    · cases h

end

end LeanVM.Protocol.Verifier
