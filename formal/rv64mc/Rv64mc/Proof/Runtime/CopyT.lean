/-
  Rv64mc.Proof.Runtime.CopyT

  What the total proofs of `compiler_builtins`' `memcpy` and `memmove` share: memory as bytes (`bat`), a store or load
  of any width as the bytes it writes or reads (`bat_storeMem`, `extractByte_loadVal`), the reassembly of a doubleword
  from two (`extractByte_shr_or_shl`), and the copy's invariant (`Inv`): the bytes copied so far, every other byte
  apart from the stack below `top` kept, and the memory frame, with its lemmas for a byte, a doubleword and a store
  into the stack slot (`Inv.byte`, `Inv.word`, `Inv.slot`, `slot_copy`).

  ## Main definitions

  * `bat`, `Inv`

  ## Main results

  * `bat_storeMem`, `extractByte_loadVal`, `extractByte_load`, `extractByte_shr_or_shl`, `shamt`, `or_eq_add`
  * `Inv.start`, `Inv.byte`, `Inv.word`, `Inv.slot`, `Inv.src`, `slot_copy`, `slot_copy_from`
-/

import Rv64mc.Proof.Runtime.MemsetT
import Rv64mc.Spec.Runtime.MemT
import Rv64mc.Tactic.StepsT
import RiscvZkvm.Rv64.Logic.MemRegionWriteWide

namespace Rv64mc.Proof.Runtime.CopyT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Tactic Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin Kept)

/-- The byte at address `x`, a number. -/
abbrev bat (M : MachineState) (x : Nat) : BitVec 8 := M.getByte (BitVec.ofNat 64 x)

theorem toNat_align_ofNat {b : Nat} (hb : b < 2 ^ 64) : (alignToDword (BitVec.ofNat 64 b)).toNat = b - b % 8 := by
  rw [toNat_alignToDword, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]

theorem byteOffset_ofNat {b : Nat} (hb : b < 2 ^ 64) : byteOffset (BitVec.ofNat 64 b) = b % 8 := by
  rw [byteOffset_eq_toNat_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]

theorem getByte_setMem' (M : MachineState) (a v y : Word) :
    (M.setMem a v).getByte y = if alignToDword y = a then extractByte v (byteOffset y) else M.getByte y := by
  unfold MachineState.getByte
  split
  · subst_vars; rw [MachineState.getMem_setMem_eq]
  · rw [MachineState.getMem_setMem_ne ‹_›]

theorem align_eq_iff {b : Nat} (hb : b < 2 ^ 64) (x : Word) :
    alignToDword (BitVec.ofNat 64 b) = alignToDword x ↔ b / 8 = x.toNat / 8 := by
  rw [← BitVec.toNat_inj, toNat_align_ofNat hb, toNat_alignToDword]; omega

theorem extractByte_trunc8 (v : Word) : v.truncate 8 = extractByte v 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [extractByte]
theorem extractByte_trunc16_0 (v : Word) : (v.truncate 16).truncate 8 = extractByte v 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [extractByte]
theorem extractByte_trunc16_1 (v : Word) : ((v.truncate 16) >>> 8).truncate 8 = extractByte v 1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [extractByte, show 8 + i < 16 by omega]
theorem extractByte_trunc32 (v : Word) (k : Nat) (hk : k < 4) :
    ((v.truncate 32) >>> (8 * k)).truncate 8 = extractByte v k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have : k * 8 + i < 32 := by omega
  simp [extractByte, this, Nat.mul_comm]

/-- A byte in the doubleword at `x`'s aligned address. -/
theorem getByte_same_dword {M : MachineState} {x : Word} {b : Nat} (hb : b < 2 ^ 64) (hA : b / 8 = x.toNat / 8) :
    M.getByte (BitVec.ofNat 64 b) = extractByte (M.getMem (alignToDword x)) (b % 8) := by
  rw [MachineState.getByte, (align_eq_iff hb x).2 hA, byteOffset_ofNat hb]

theorem iteT {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by simp [h]
theorem iteF {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by simp [h]

/-- **A store's bytes**: a store of width `w` at `x`, aligned for its width, writes `v`'s low bytes at
    `[x, x + w)` and keeps every other byte. -/
theorem bat_storeMem {w : Width} {M : MachineState} {x v : Word} {b : Nat} (hx : x.toNat % w.bytes = 0)
    (hb : b < 2 ^ 64) : bat (storeMem w M x v) b =
      if x.toNat ≤ b ∧ b < x.toNat + w.bytes then extractByte v (b - x.toNat) else bat M b := by
  have hxl := x.isLt
  have hal := align_eq_iff hb x
  have hbo := byteOffset_ofNat hb
  have hw1 : Width.b1.bytes = 1 := rfl
  have hw2 : Width.b2.bytes = 2 := rfl
  have hw4 : Width.b4.bytes = 4 := rfl
  have hw8 : Width.b8.bytes = 8 := rfl
  cases w <;> simp only [hw1, hw2, hw4, hw8] at hx <;> unfold bat storeMem <;> dsimp only
  · rw [MachineState.setByte, getByte_setMem', hbo, byteOffset_eq_toNat_mod]
    by_cases hA : b / 8 = x.toNat / 8
    · rw [iteT (hal.2 hA)]
      by_cases hE : b % 8 = x.toNat % 8
      · have := extractByte_replaceByte_same (M.getMem (alignToDword x)) ⟨x.toNat % 8, by omega⟩ (v.truncate 8)
        simp only at this
        rw [hE, this, iteT (by omega), extractByte_trunc8, show b - x.toNat = 0 by omega]
      · rw [extractByte_replaceByte_diff _ _ (by omega) (by omega) hE, iteF (by omega), getByte_same_dword hb hA]
    · rw [iteF (mt hal.1 hA), iteF (by omega)]
  · rw [MachineState.setHalfword, getByte_setMem', hbo, byteOffset_eq_toNat_mod]
    by_cases hA : b / 8 = x.toNat / 8
    · rw [iteT (hal.2 hA), extractByte_replaceHalfword _ _ (by omega) (by omega)]
      by_cases h0 : b % 8 = 2 * (x.toNat % 8 / 2)
      · rw [iteT h0, iteT (by omega), extractByte_trunc16_0, show b - x.toNat = 0 by omega]
      by_cases h1 : b % 8 = 2 * (x.toNat % 8 / 2) + 1
      · rw [iteF h0, iteT h1, iteT (by omega), extractByte_trunc16_1, show b - x.toNat = 1 by omega]
      rw [iteF h0, iteF h1, iteF (by omega), getByte_same_dword hb hA]
    · rw [iteF (mt hal.1 hA), iteF (by omega)]
  · rw [MachineState.setWord32, getByte_setMem', hbo, byteOffset_eq_toNat_mod]
    by_cases hA : b / 8 = x.toNat / 8
    · rw [iteT (hal.2 hA), extractByte_replaceWord32 _ _ (by omega) (by omega)]
      have e := fun k (hk : k < 4) => extractByte_trunc32 v k hk
      by_cases h0 : b % 8 = 4 * (x.toNat % 8 / 4)
      · rw [iteT h0, iteT (by omega), show b - x.toNat = 0 by omega]; simpa using e 0 (by omega)
      by_cases h1 : b % 8 = 4 * (x.toNat % 8 / 4) + 1
      · rw [iteF h0, iteT h1, iteT (by omega), show b - x.toNat = 1 by omega]; exact e 1 (by omega)
      by_cases h2 : b % 8 = 4 * (x.toNat % 8 / 4) + 2
      · rw [iteF h0, iteF h1, iteT h2, iteT (by omega), show b - x.toNat = 2 by omega]; exact e 2 (by omega)
      by_cases h3 : b % 8 = 4 * (x.toNat % 8 / 4) + 3
      · rw [iteF h0, iteF h1, iteF h2, iteT h3, iteT (by omega), show b - x.toNat = 3 by omega]
        exact e 3 (by omega)
      rw [iteF h0, iteF h1, iteF h2, iteF h3, iteF (by omega), getByte_same_dword hb hA]
    · rw [iteF (mt hal.1 hA), iteF (by omega)]
  · have hx' : alignToDword x = x := by
      apply BitVec.eq_of_toNat_eq; rw [toNat_alignToDword]; omega
    rw [getByte_setMem', hbo]
    by_cases hA : b / 8 = x.toNat / 8
    · rw [iteT ((hal.2 hA).trans hx'), iteT (by omega)]; congr 1; omega
    · rw [iteF (fun h => hA (hal.1 (h.trans hx'.symm))), iteF (by omega)]

theorem extractByte_window (W : Word) (o n t : Nat) (ht : 8 * t + 8 ≤ n) (hn : n ≤ 64) :
    extractByte (((W >>> (8 * o)).setWidth n).setWidth 64) t = extractByte W (o + t) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [extractByte, hi, show t * 8 + i < n by omega, show t * 8 + i < 64 by omega]
  congr 1; omega

theorem ofNat_toNat' (x : Word) : BitVec.ofNat 64 x.toNat = x := by simp

/-- **A load's bytes**: a load of width `w` at `x`, aligned for its width, reads byte `t` from `x + t`. -/
theorem extractByte_loadVal {w : Width} {M : MachineState} {x : Word} {t : Nat} (hx : x.toNat % w.bytes = 0)
    (ht : t < w.bytes) : extractByte (loadVal w M x) t = bat M (x.toNat + t) := by
  have hxl := x.isLt
  have hw1 : Width.b1.bytes = 1 := rfl
  have hw2 : Width.b2.bytes = 2 := rfl
  have hw4 : Width.b4.bytes = 4 := rfl
  have hw8 : Width.b8.bytes = 8 := rfl
  have hb : x.toNat + t < 2 ^ 64 := by cases w <;> simp only [hw1, hw2, hw4, hw8] at hx ht <;> omega
  have hA : (x.toNat + t) / 8 = x.toNat / 8 := by cases w <;> simp only [hw1, hw2, hw4, hw8] at hx ht <;> omega
  unfold bat
  rw [getByte_same_dword hb hA]
  have hx' : alignToDword x = x ∨ x.toNat % 8 ≠ 0 := by
    by_cases h : x.toNat % 8 = 0
    · exact .inl (BitVec.eq_of_toNat_eq (by rw [toNat_alignToDword]; omega))
    · exact .inr h
  cases w <;> simp only [hw1, hw2, hw4, hw8] at hx ht <;> unfold loadVal <;> dsimp only <;>
    rw [show (x.toNat + t) % 8 = x.toNat % 8 + t by omega] <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · rw [show t = 0 by omega]
    simp [MachineState.getByte, extractByte, byteOffset_eq_toNat_mod, hi]
  · simp [MachineState.getHalfword, extractByte, extractHalfword, byteOffset_eq_toNat_mod, hi,
      show t * 8 + i < 64 by omega, show t * 8 + i < 16 by omega]
    congr 1; omega
  · simp [MachineState.getWord32, extractByte, extractWord32, byteOffset_eq_toNat_mod, hi,
      show t * 8 + i < 64 by omega, show t * 8 + i < 32 by omega]
    congr 1; omega
  · rw [hx'.resolve_right (by omega), show x.toNat % 8 + t = t by omega]

/-- A sign extension keeps the bytes of the width it extends from. -/
theorem extractByte_sext {w : Width} {v : Word} {t : Nat} (ht : t < w.bytes) :
    extractByte ((UnOp.sext w).eval v) t = extractByte v t := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  cases w <;> simp [Width.bytes] at ht <;>
    simp [UnOp.eval, Width.bits, extractByte, hi, show t * 8 + i < 64 by omega, BitVec.getElem_signExtend] <;>
    omega

/-- **Two doublewords reassembled**: the bytes from `o` on of `p`, then the first `o` of `c`. -/
theorem extractByte_shr_or_shl (p c : Word) (o t : Nat) (ho : 0 < o) (ho8 : o < 8) (ht : t < 8) :
    extractByte ((p >>> (8 * o)) ||| (c <<< (64 - 8 * o))) t =
      if t + o < 8 then extractByte p (t + o) else extractByte c (t + o - 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  split
  · have h1 : t * 8 + i < 64 - 8 * o := by omega
    simp [extractByte, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, hi, h1]
    congr 1; omega
  · have h1 : 64 ≤ 8 * o + (t * 8 + i) := by omega
    have h2 : ¬ t * 8 + i < 64 - 8 * o := by omega
    have h3 : t * 8 + i < 64 := by omega
    simp [extractByte, BitVec.getLsbD_ushiftRight, hi, h2, h3, BitVec.getLsbD_of_ge p _ h1]
    congr 1; omega

/-! ## Stores as doubleword stores -/

/-- A store of any width, aligned for it, is a doubleword store at its aligned address. -/
theorem storeMem_eq_setMem (w : Width) (M : MachineState) {x : Word} (v : Word) (hx : x.toNat % w.bytes = 0) :
    ∃ v', storeMem w M x v = M.setMem (alignToDword x) v' := by
  cases w
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · refine ⟨v, ?_⟩
    have : alignToDword x = x := BitVec.eq_of_toNat_eq (by rw [toNat_alignToDword]; simp [Width.bytes] at hx; omega)
    simp only [storeMem, this]

variable {env : Env}

/-- A store into the stack slot below `top` keeps `Kept`. -/
theorem Kept.slot {top dst x v : Word} {n : Nat} {w : Width} {m M : MachineState} (h : Kept env top dst n m M)
    (hroom : env.stackLimit.toNat + 16 ≤ top.toNat) (hx1 : top.toNat - 16 ≤ x.toNat) (hx2 : x.toNat < top.toNat)
    (hal : x.toNat % w.bytes = 0) (htop : top.toNat % 8 = 0) : Kept env top dst n m (storeMem w M x v) := by
  obtain ⟨v', hv⟩ := storeMem_eq_setMem w M v hal
  rw [hv]
  have ha := toNat_alignToDword x
  have hl := env.layout
  exact ⟨frame_slot h.1 (by omega) (by omega), static_store h.2.1 (by omega), by simp [h.2.2]⟩

/-! ## The copy's invariant -/

/-- **The copy so far**: `j` bytes of `[src, src + n)` copied to `[dst, dst + n)`, every byte outside the copied
    ones and apart from the stack below `top` kept, and `Kept`. -/
def Inv (env : Env) (top dst src : Word) (n : Nat) (m M : MachineState) (j : Nat) : Prop :=
  Kept env top dst n m M ∧ (∀ k, k < j → bat M (dst.toNat + k) = bat m (src.toNat + k)) ∧
    ∀ b, b < 2 ^ 64 → ¬ (dst.toNat ≤ b ∧ b < dst.toNat + j) → (b < env.stackLimit.toNat ∨ top.toNat ≤ b) →
      bat M b = bat m b

theorem Inv.start {top dst src : Word} {n : Nat} {m : MachineState} (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) : Inv env top dst src n m m 0 :=
  ⟨⟨Env.Frame.refl hnx, hst, rfl⟩, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩

/-- A store into the stack slot keeps `Inv`. -/
theorem Inv.slot {top dst src x v : Word} {n j : Nat} {w : Width} {m M : MachineState}
    (h : Inv env top dst src n m M j) (hdoff : OffStack env top dst n) (hj : j ≤ n) (hdn : dst.toNat + n < 2 ^ 64)
    (hroom : env.stackLimit.toNat + 16 ≤ top.toNat) (htop : top.toNat % 8 = 0)
    (hx1 : top.toNat - 16 ≤ x.toNat) (hx2 : x.toNat + w.bytes ≤ top.toNat) (hal : x.toNat % w.bytes = 0) :
    Inv env top dst src n m (storeMem w M x v) j := by
  have hw : 0 < w.bytes := by cases w <;> decide
  refine ⟨Kept.slot h.1 hroom hx1 (by omega) hal htop, fun k hk => ?_, fun b hb h1 h2 => ?_⟩
  · unfold OffStack at hdoff
    rw [bat_storeMem hal (by omega), iteF (by omega)]
    exact h.2.1 k hk
  · rw [bat_storeMem hal hb, iteF (by omega)]
    exact h.2.2 b hb h1 h2

/-- A byte store of the next byte keeps `Inv`, one byte further. -/
theorem Inv.byte {top dst src x v : Word} {n j : Nat} {m M : MachineState} (h : Inv env top dst src n m M j)
    (hw : InWin env dst n) (hx : x.toNat = dst.toNat + j) (hjn : j < n)
    (hv : extractByte v 0 = bat m (src.toNat + j)) : Inv env top dst src n m (storeMem .b1 M x v) (j + 1) := by
  have h1 : x.toNat % Width.b1.bytes = 0 := Nat.mod_one _
  have hwb : Width.b1.bytes = 1 := rfl
  have hdn : dst.toNat + n < 2 ^ 64 := by have := env.heapEnd.isLt; unfold InWin at hw; omega
  refine ⟨Kept.setByte h.1 hw (by omega) (by omega) _, fun k hk => ?_, fun b hb hn hs => ?_⟩
  · rw [bat_storeMem h1 (by omega)]
    by_cases hkj : k = j
    · rw [iteT (by omega), show dst.toNat + k - x.toNat = 0 by omega, hv, hkj]
    · rw [iteF (by omega)]; exact h.2.1 k (by omega)
  · rw [bat_storeMem h1 hb, iteF (by omega)]
    exact h.2.2 b hb (by omega) hs

/-- An aligned doubleword store of the next eight bytes keeps `Inv`, eight bytes further. -/
theorem Inv.word {top dst src x v : Word} {n j : Nat} {m M : MachineState} (h : Inv env top dst src n m M j)
    (hw : InWin env dst n) (hx : x.toNat = dst.toNat + j) (hal : x.toNat % 8 = 0) (hjn : j + 8 ≤ n)
    (hv : ∀ t, t < 8 → extractByte v t = bat m (src.toNat + j + t)) :
    Inv env top dst src n m (storeMem .b8 M x v) (j + 8) := by
  have h1 : x.toNat % Width.b8.bytes = 0 := hal
  have hwb : Width.b8.bytes = 8 := rfl
  have hdn : dst.toNat + n < 2 ^ 64 := by have := env.heapEnd.isLt; unfold InWin at hw; omega
  refine ⟨Kept.setMem h.1 hw hal (by omega) (by omega) _, fun k hk => ?_, fun b hb hn hs => ?_⟩
  · rw [bat_storeMem h1 (by omega)]
    by_cases hkj : j ≤ k
    · rw [iteT (by omega), hv _ (by omega)]; congr 1; omega
    · rw [iteF (by omega)]; exact h.2.1 k (by omega)
  · rw [bat_storeMem h1 hb, iteF (by omega)]
    exact h.2.2 b hb (by omega) hs

/-- A source byte apart from the copied ones and from the stack below `top` reads as at entry. -/
theorem Inv.src {top dst src : Word} {n j k : Nat} {m M : MachineState} (h : Inv env top dst src n m M j)
    (hk : src.toNat + k < 2 ^ 64) (hn : ¬ (dst.toNat ≤ src.toNat + k ∧ src.toNat + k < dst.toNat + j))
    (hs : src.toNat + k < env.stackLimit.toNat ∨ top.toNat ≤ src.toNat + k) :
    bat M (src.toNat + k) = bat m (src.toNat + k) :=
  h.2.2 _ hk hn hs

/-- The shift amounts of a reassembly by `o` bytes, as the code masks them. -/
theorem shamt {x : Word} {o : Nat} (hx : x.toNat = 8 * o) (h1 : 0 < o) (h8 : o < 8) :
    (x &&& 63#64).toNat = 8 * o ∧ (0#64 - x &&& 56#64 &&& 63#64).toNat = 64 - 8 * o := by
  have : x = BitVec.ofNat 64 (8 * o) := by
    apply BitVec.eq_of_toNat_eq; rw [hx, BitVec.toNat_ofNat]; omega
  subst this
  rcases (by omega : o = 1 ∨ o = 2 ∨ o = 3 ∨ o = 4 ∨ o = 5 ∨ o = 6 ∨ o = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- An or into the low bits of an 8-byte aligned address is an addition. -/
theorem or_eq_add {a b : Word} (ha : a.toNat % 8 = 0) (hb : b.toNat < 8) : a ||| b = a + b := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero, Bool.and_eq_false_imp]
  intro h1
  by_cases hi3 : i < 3
  · have := Nat.testBit_mod_two_pow a.toNat 3 i
    rw [show 2 ^ 3 = 8 from rfl, ha] at this
    simp [BitVec.getLsbD, hi3] at this h1
    exact absurd h1 (by simp [← this])
  · simp only [BitVec.getLsbD]
    exact Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hb
      ((Nat.pow_le_pow_right (by decide : 2 > 0) (by omega : 3 ≤ i)).trans_eq' rfl))

/-- An and with a mask of the low three bits reads only `x`'s low three bits. -/
theorem and_low {x c : Word} {o : Nat} (h : x.toNat % 8 = o) (hc : c &&& 7#64 = c) :
    x &&& c = BitVec.ofNat 64 o &&& c := by
  have h7 : x &&& 7#64 = BitVec.ofNat 64 o := by
    apply BitVec.eq_of_toNat_eq
    rw [Proof.Runtime.Alloc.and7, BitVec.toNat_ofNat]; omega
  calc x &&& c = x &&& (7#64 &&& c) := by rw [BitVec.and_comm 7#64, hc]
    _ = BitVec.ofNat 64 o &&& c := by rw [← BitVec.and_assoc, h7]

/-- **A narrow copy into the stack slot**: `w` bytes of the source at `i` into byte `i` of the slot at `top - 8`, the
    first `i` already copied, keeps `Inv` and copies the first `i + w`. -/
theorem slot_copy {top dst src X v : Word} {n j i B : Nat} {w : Width} {m M : MachineState}
    (hI : Inv env top dst src n m M j) (hdoff : OffStack env top dst n) (hj : j ≤ n) (hdn : dst.toNat + n < 2 ^ 64)
    (hroom : env.stackLimit.toNat + 16 ≤ top.toNat) (htop : top.toNat % 8 = 0)
    (hS : ∀ t, t < i → bat M (top.toNat - 8 + t) = bat m (B + t)) (hX : X.toNat = top.toNat - 8 + i)
    (hal : X.toNat % w.bytes = 0) (hiw : i + w.bytes ≤ 8)
    (hv : ∀ u, u < w.bytes → extractByte v u = bat m (B + i + u)) :
    Inv env top dst src n m (storeMem w M X v) j ∧
      ∀ t, t < i + w.bytes → bat (storeMem w M X v) (top.toNat - 8 + t) = bat m (B + t) := by
  have htl := top.isLt
  refine ⟨hI.slot hdoff hj hdn hroom htop (by omega) (by omega) hal, fun t ht => ?_⟩
  rw [bat_storeMem hal (by omega)]
  by_cases hti : i ≤ t
  · rw [iteT (by omega), hv _ (by omega)]; congr 1; omega
  · rw [iteF (by omega)]; exact hS t (by omega)

/-- A load of width `w`, sign-extended or not, reads byte `u` of it from `x + u`. -/
theorem extractByte_load {w : Width} {M : MachineState} {x : Word} {u : Nat} (sg : Bool)
    (hx : x.toNat % w.bytes = 0) (hu : u < w.bytes) :
    extractByte (if sg then (UnOp.sext w).eval (loadVal w M x) else loadVal w M x) u = bat M (x.toNat + u) := by
  cases sg
  · exact extractByte_loadVal hx hu
  · simp only [↓reduceIte]; rw [extractByte_sext hu]; exact extractByte_loadVal hx hu

theorem and1_zero (x : Word) : x &&& 1#64 = 0#64 ↔ x.toNat % 2 = 0 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_and, show (1#64 : Word).toNat = 2 ^ 1 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  simp

theorem and2_zero (x : Word) : x &&& 2#64 = 0#64 ↔ x.toNat % 4 < 2 := by
  have h3 : x &&& 3#64 = BitVec.ofNat 64 (x.toNat % 4) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (3#64 : Word).toNat = 2 ^ 2 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
      BitVec.toNat_ofNat]
    omega
  have : x &&& 2#64 = BitVec.ofNat 64 (x.toNat % 4) &&& 2#64 := by
    rw [← h3, BitVec.and_assoc]; rfl
  rw [this]
  have hl : x.toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize x.toNat % 4 = k at hl ⊢
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> decide

theorem toNat_shl3 {x : Word} (h : x.toNat < 8) : (x <<< 3).toNat = 8 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

/-- `slot_copy` from byte `lo` of the slot on. -/
theorem slot_copy_from {top dst src X v : Word} {n j lo i B : Nat} {w : Width} {m M : MachineState}
    (hI : Inv env top dst src n m M j) (hdoff : OffStack env top dst n) (hj : j ≤ n) (hdn : dst.toNat + n < 2 ^ 64)
    (hroom : env.stackLimit.toNat + 16 ≤ top.toNat) (htop : top.toNat % 8 = 0)
    (hS : ∀ t, lo ≤ t → t < i → bat M (top.toNat - 8 + t) = bat m (B + t)) (hX : X.toNat = top.toNat - 8 + i)
    (hal : X.toNat % w.bytes = 0) (hiw : i + w.bytes ≤ 8)
    (hv : ∀ u, u < w.bytes → extractByte v u = bat m (B + i + u)) :
    Inv env top dst src n m (storeMem w M X v) j ∧
      ∀ t, lo ≤ t → t < i + w.bytes → bat (storeMem w M X v) (top.toNat - 8 + t) = bat m (B + t) := by
  have htl := top.isLt
  refine ⟨hI.slot hdoff hj hdn hroom htop (by omega) (by omega) hal, fun t ht0 ht => ?_⟩
  rw [bat_storeMem hal (by omega)]
  by_cases hti : i ≤ t
  · rw [iteT (by omega), hv _ (by omega)]; congr 1; omega
  · rw [iteF (by omega)]; exact hS t ht0 (by omega)

theorem and4_zero (x : Word) : x &&& 4#64 = 0#64 ↔ x.toNat % 8 < 4 := by
  have h7 : x &&& 7#64 = BitVec.ofNat 64 (x.toNat % 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [Proof.Runtime.Alloc.and7, BitVec.toNat_ofNat]; omega
  have : x &&& 4#64 = BitVec.ofNat 64 (x.toNat % 8) &&& 4#64 := by
    rw [← h7, BitVec.and_assoc]; rfl
  rw [this]
  have hl : x.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize x.toNat % 8 = k at hl ⊢
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `y` rounded down to a multiple of 8, as the code computes it. -/
theorem toNat_and_not7 (y : Word) : (y &&& 18446744073709551608#64).toNat = y.toNat - y.toNat % 8 := by
  rw [show (18446744073709551608#64 : Word) = ~~~7#64 by decide]
  exact toNat_alignToDword y

/-- The bytes from `x` to the next multiple of 8, as the code computes them. -/
theorem toNat_neg_and7 (x : Word) : (0#64 - x &&& 7#64).toNat = (8 - x.toNat % 8) % 8 := by
  rw [Proof.Runtime.Alloc.and7, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, Nat.add_zero]
  omega
