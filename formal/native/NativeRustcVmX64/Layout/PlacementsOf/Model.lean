module

public import NativeVm.Math.Layout
public import NativeRustcVm.Rodata
public import NativeRustcVm.Layout.Values

/-!
# `placements_of`'s model facts

- The stacked columns `blockList` (`94` of them), those below `c` (`below c`).
- `KECCAK_SLOT` and `KECCAK_OUTPUT`'s bytes at column `c` (`slot_byte`, `out_byte`): `255` for no
  slot (`slotF`), `1` for an output lane (`outF`).
- The offsets `stack_offsets` gives the stacked columns' sizes (`ow_getD`, `ow_snd`) and their
  bounds (`sumF_le`, `fit`).
-/

namespace NativeRustcVmX64.Layout.PlacementsOf

open NativeVm.Model NativeVm.Math.Layout LeanVM.Protocol.Verifier NativeRustcVm.Layout

public section

/-! ## The stacked columns -/

theorem blockList_length : blockList.length = 94 := by decide

theorem blockList_nodup : blockList.Nodup := List.nodup_range.filter _

theorem mem_blockList_iff {c : Nat} (hc : c < 158) : c ∈ blockList ↔ isBlockF c = true := by
  simp [blockList, List.mem_filter, hc]

theorem blockList_get4 : blockList[4]'(by rw [blockList_length]; omega) = 4 := by decide

/-- The stacked columns below `c`. -/
@[expose] def below (c : Nat) : List Nat := (List.range c).filter isBlockF

theorem below_succ (c : Nat) :
    below (c + 1) = below c ++ (if isBlockF c then [c] else []) := by
  unfold below
  rw [List.range_succ, List.filter_append]
  cases h : isBlockF c <;> simp [h]

theorem below_158 : below 158 = blockList := rfl

theorem below_length_le {c : Nat} (hc : c ≤ 158) : (below c).length ≤ 94 := by
  rw [← blockList_length, ← below_158]
  unfold below
  have : List.range 158 = List.range c ++ (List.range' c (158 - c)) := by
    rw [List.range_eq_range', List.range_eq_range']
    have := List.range'_append_1 (s := 0) (m := c) (n := 158 - c)
    rw [Nat.zero_add, show c + (158 - c) = 158 by omega] at this
    exact this.symm
  rw [this, List.filter_append, List.length_append]
  omega

theorem below_lt {c q : Nat} (hq : q ∈ below c) : q < c := by
  simp only [below, List.mem_filter, List.mem_range] at hq; exact hq.1

theorem below_prefix {c : Nat} (hc : c ≤ 158) : below c <+: blockList := by
  rw [← below_158]
  unfold below
  have : List.range 158 = List.range c ++ (List.range' c (158 - c)) := by
    rw [List.range_eq_range', List.range_eq_range']
    have := List.range'_append_1 (s := 0) (m := c) (n := 158 - c)
    rw [Nat.zero_add, show c + (158 - c) = 158 by omega] at this
    exact this.symm
  rw [this, List.filter_append]
  exact List.prefix_append _ _

theorem below_getElem {c q : Nat} (hc : c ≤ 158) (hq : q < (below c).length) :
    (below c)[q] = blockList[q]'(by
      have := (below_prefix hc).length_le; omega) :=
  (List.IsPrefix.getElem (below_prefix hc) hq)

/-! ## The bytes -/

theorem slot_byte {c : Nat} (hc : c < 158) :
    NativeRustcVm.Data.keccakSlot[c]'(by
      simp [NativeRustcVm.Data.keccakSlot, columnCount_158, hc]) =
      NativeRustcVm.Data.slotByte (slotF c) := by
  simp only [NativeRustcVm.Data.keccakSlot, List.getElem_map, List.getElem_range]
  rw [keccakSlot_eq c hc]

theorem out_byte {c : Nat} (hc : c < 158) :
    (NativeRustcVm.Data.keccakOutput.map fun b ↦ if b then (1 : UInt8) else 0)[c]'(by
      simp [NativeRustcVm.Data.keccakOutput, columnCount_158, hc]) =
      if outF c then 1 else 0 := by
  simp only [NativeRustcVm.Data.keccakOutput, List.getElem_map, List.getElem_range]
  rw [keccakOutput_eq c hc]

theorem slotF_lt {c s : Nat} (h : slotF c = some s) : s < 64 := by
  unfold slotF at h; split_ifs at h <;> simp at h <;> omega

theorem slotByte_none {c : Nat} : NativeRustcVm.Data.slotByte (slotF c) = 255 ↔ slotF c = none := by
  constructor
  · intro h
    cases hs : slotF c with
    | none => rfl
    | some s =>
      rw [hs] at h
      have := slotF_lt hs
      simp only [NativeRustcVm.Data.slotByte] at h
      have := congrArg UInt8.toNat h
      simp [Nat.toUInt8, UInt8.toNat_ofNat] at this
      omega
  · intro h; rw [h]; rfl

theorem slotByte_toNat {c s : Nat} (h : slotF c = some s) :
    (NativeRustcVm.Data.slotByte (slotF c)).toNat = s := by
  rw [h]
  have := slotF_lt h
  simp [NativeRustcVm.Data.slotByte, Nat.toUInt8]
  omega

/-! ## The offsets -/

/-- The stacked columns' sizes. -/
@[expose] def sizesOf (κ : Nat → Nat) : Array Nat := (blockList.map κ).toArray

theorem sizesOf_size (κ : Nat → Nat) : (sizesOf κ).size = blockList.length := by simp [sizesOf]

theorem sizesOf_getD (κ : Nat → Nat) {q : Nat} (hq : q < blockList.length) :
    (sizesOf κ).getD q 0 = κ (blockList.getD q 0) := by
  simp [sizesOf, Array.getD, hq, List.getD_eq_getElem?_getD]

/-- **The offset of stacked column `q`.** -/
theorem ow_getD (κ : Nat → Nat) {q : Nat} (hq : q < blockList.length) :
    (stackOffsets (sizesOf κ)).1.getD q 0 = sumF κ (keyF κ (blockList.getD q 0)) := by
  rw [(stackOffsets_spec _).2.2 q (by rw [sizesOf_size]; exact hq)]
  exact sum_before κ _ (sizesOf_size κ) (fun q hq ↦ sizesOf_getD κ hq) hq

theorem ow_snd (κ : Nat → Nat) : (stackOffsets (sizesOf κ)).2 = log2Ceil (sumF κ 0) := by
  rw [(stackOffsets_spec _).1, sum_all κ _ (sizesOf_size κ) (fun q hq ↦ sizesOf_getD κ hq)]

theorem ow_size (κ : Nat → Nat) : (stackOffsets (sizesOf κ)).1.size = blockList.length := by
  rw [(stackOffsets_spec _).2.1, sizesOf_size]

theorem foldl_sumStep_le (κ : Nat → Nat) (kr : Nat) (hk : ∀ c < 158, κ c ≤ 36) :
    ∀ (l : List Nat) (a : Nat), (∀ c ∈ l, c < 158) →
      l.foldl (sumStep κ kr) a ≤ a + l.length * 2 ^ 36
  | [], a, _ => by simp
  | c :: l, a, h => by
    simp only [List.foldl_cons, List.length_cons]
    have ih := foldl_sumStep_le κ kr hk l (sumStep κ kr a c) fun x hx ↦ h x (by simp [hx])
    have hs : sumStep κ kr a c ≤ a + 2 ^ 36 := by
      unfold sumStep
      split
      · have := Nat.pow_le_pow_right (by decide : 0 < 2) (hk c (h c (by simp)))
        omega
      · omega
    have := Nat.succ_mul l.length (2 ^ 36)
    omega

/-- The sizes of stacked columns at most `2 ^ 36` each. -/
theorem sumF_le (κ : Nat → Nat) (kr : Nat) (hk : ∀ c < 158, κ c ≤ 36) :
    sumF κ kr ≤ 158 * 2 ^ 36 := by
  have := foldl_sumStep_le κ kr hk (List.range 158) 0 (fun c hc ↦ List.mem_range.mp hc)
  simpa [sumF] using this

/-- **The stacked columns fit a `u64`.** -/
theorem fit (κ : Nat → Nat) (hk : ∀ c < 158, κ c ≤ 36) : OffsetsFit (sizesOf κ) := by
  refine ⟨fun s hs ↦ ?_, ?_⟩
  · simp only [sizesOf, List.mem_toArray, List.mem_map] at hs
    obtain ⟨c, hc, rfl⟩ := hs
    have := hk c (lt_of_mem_blockList hc)
    omega
  · have h := sum_all κ _ (sizesOf_size κ) (fun q hq ↦ sizesOf_getD κ hq)
    have hb := sumF_le κ 0 hk
    have e : ((sizesOf κ).toList.map (2 ^ ·)).sum =
        ((List.range (sizesOf κ).size).map (2 ^ (sizesOf κ).getD · 0)).sum := by
      congr 1
    rw [e, h]
    omega

end

end NativeRustcVmX64.Layout.PlacementsOf
