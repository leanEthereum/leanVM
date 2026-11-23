module

public import NativeRustcVmX64.Keccak.WordsHash.Tail

/-!
# `keccak256_words::<hash_words's closure>` (x86-64): the padding and the last permutation

`pad_run`: from the padding block (`b82`, lane 16's word in RAX), the machine inevitably reaches
the epilogue (`EpiAt`) with the lanes `keccakF1600 (lastB m0)`, `lastB` the whole blocks' state
with the last block's words and the padding XORed into the rate (`finalState`'s argument). The
block runs in three parts: `padA` XORs lane 16's word and computes the padding word
`1 << 8 (r % 8)` (`padWord_val`) and the padded lane's offset `8 t`, `t = r / 8`
(`and8_val`), `r = len % 136`; `padB t` XORs the padding word into lane `t` (`padB_exec`);
`padC` XORs `0x80` into byte 135, lane 16's top byte (`wordAt_xorb`), and calls `keccak_f`
(`call_kf`).
-/

namespace NativeRustcVmX64.WordsHash

open NativeRustcX64 NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcX64.KeccakF (WordAt wordAt_of_eq load_of_wordAt)
open NativeRustcVm.Keccak (padLane)
open Vm.Keccak256WordsOfHashWords

@[expose] public section

/-- The lanes before the last permutation. -/
def lastB (m0 : MachineData) : KeccakState :=
  Native.Keccak.Proof.xorRate (stA m0) fun k =>
    word m0 (17 * nb m0 + k) ^^^ padLane (m0.regs.get64 .rdx).toNat k

/-- **At the epilogue**: the lanes `keccakF1600 (lastB m0)`. -/
def EpiAt [Host] (m0 : MachineData) (k : Nat) (st : MachineState) : Prop :=
  Ctx m0 (slotsH m0) [] 8 st.data ∧ Lanes m0 st.data.dmem (Keccak.lane (keccakF1600 (lastB m0))) ∧
    st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b83Offset)

end

public section

/-- The padding word's XOR into lane `t`. -/
theorem padB_exec (t : Nat) (ht : t < 17) : ∃ S, exec padBCode (startPad t) = some (S, .fall) ∧
    S.mem = [⟨0, 40 + 8 * t, 8, .bin .xor .W64 (.load 0 (40 + 8 * t) 8) (.reg .rax)⟩] ∧
    S.reg .rsp = some (.ptr 0 8) := by
  match t, ht with
  | 0, _ => exact ⟨_, padB0, rfl, rfl⟩
  | 1, _ => exact ⟨_, padB1, rfl, rfl⟩
  | 2, _ => exact ⟨_, padB2, rfl, rfl⟩
  | 3, _ => exact ⟨_, padB3, rfl, rfl⟩
  | 4, _ => exact ⟨_, padB4, rfl, rfl⟩
  | 5, _ => exact ⟨_, padB5, rfl, rfl⟩
  | 6, _ => exact ⟨_, padB6, rfl, rfl⟩
  | 7, _ => exact ⟨_, padB7, rfl, rfl⟩
  | 8, _ => exact ⟨_, padB8, rfl, rfl⟩
  | 9, _ => exact ⟨_, padB9, rfl, rfl⟩
  | 10, _ => exact ⟨_, padB10, rfl, rfl⟩
  | 11, _ => exact ⟨_, padB11, rfl, rfl⟩
  | 12, _ => exact ⟨_, padB12, rfl, rfl⟩
  | 13, _ => exact ⟨_, padB13, rfl, rfl⟩
  | 14, _ => exact ⟨_, padB14, rfl, rfl⟩
  | 15, _ => exact ⟨_, padB15, rfl, rfl⟩
  | 16, _ => exact ⟨_, padB16, rfl, rfl⟩
  | _ + 17, h => exact absurd h (by omega)

/-- Byte 0 of an 8-bit XOR. -/
theorem byteOf_xorW8 (x y : BitVec 64) :
    byteOf (BinOp.apply .xor .W8 x y) 0 = byteOf x 0 ^^^ byteOf y 0 := by
  apply UInt8.toNat_inj.mp
  simp only [BinOp.apply, ext, low, byteOf, UInt8.toNat_ofNat', UInt8.toNat_xor, Nat.mul_zero,
    Nat.pow_zero, Nat.div_one]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, BitVec.toNat_setWidth, BitVec.toNat_xor, Nat.testBit_xor]
  by_cases hj : j < 8
  · simp [hj, show j < 64 by omega]
  · simp [hj]

theorem byteOf_hi {i : Nat} (hi : i < 8) :
    byteOf (0x8000000000000000#64) i = if i = 7 then 128 else 0 := by
  interval_cases i <;> rfl

variable [Labels] {env : Env} {S : SState} {m : MachineData}

/-- **`PAD_LAST`'s XOR into byte 135**: lane 16's top bit flipped. -/
theorem wordAt_xorb {m0 : MachineData} (hm : Match env S m)
    (hb : env.regions[0]? = some (frame m0, 296))
    (hmem : S.mem = [⟨0, 0, 8, .retAddr⟩,
      ⟨0, 175, 1, .bin .xor .W8 (.load 0 175 1) (.lit 18446744073709551488)⟩])
    {x : BitVec 64} (h0 : WordAt env.mem0 (frame m0 + BitVec.ofNat 64 168) x) :
    WordAt m.dmem (frame m0 + BitVec.ofNat 64 168) (x ^^^ 0x8000000000000000#64) := by
  intro i hi
  simp only [List.length_map, List.length_range] at hi
  rw [addr_add, hm.mem 0 _ 296 hb (168 + i) (by omega)]
  unfold memByte
  simp only [List.getElem_map, List.getElem_range, Hasher.byteOf_xor, byteOf_hi hi]
  have h0i := h0 i (by simp [hi])
  simp only [List.getElem_map, List.getElem_range, addr_add] at h0i
  have hf : findWrite 0 (168 + i) S.mem = if i = 7 then
      some (.bin .xor .W8 (.load 0 175 1) (.lit 18446744073709551488), 0) else none := by
    rw [hmem]
    interval_cases i <;> rfl
  rw [hf]
  by_cases h7 : i = 7
  · subst h7
    simp only [↓reduceIte, Sym.eval, byteOf_xorW8]
    rw [byteOf_load (t := 0) (by omega) (by omega), Env.base_eq hb,
      show 175 + 0 = 168 + 7 from rfl, h0i]
    rfl
  · simp only [h7, ↓reduceIte]
    rw [h0i, UInt8.xor_zero]

/-- The lanes after `padC`: lane 16's top bit flipped, the others kept. -/
theorem lanes_xorb {m0 : MachineData} (hm : Match env S m)
    (hb : env.regions[0]? = some (frame m0, 296))
    (hmem : S.mem = [⟨0, 0, 8, .retAddr⟩,
      ⟨0, 175, 1, .bin .xor .W8 (.load 0 175 1) (.lit 18446744073709551488)⟩])
    {f : Nat → UInt64} (hl : Lanes m0 env.mem0 f) :
    Lanes m0 m.dmem (fun i => if i = 16 then f 16 ^^^ 0x8000000000000000 else f i) := by
  intro i hi
  by_cases h16 : i = 16
  · subst h16
    simp only [↓reduceIte]
    exact wordAt_of_eq (wordAt_xorb hm hb hmem (hl 16 (by omega))) (by rw [UInt64.toBitVec_xor]; rfl)
  · simp only [h16, ↓reduceIte]
    refine KeccakF.wordAt_keep hm hb (by omega) ?_ (hl i hi)
    rw [hmem]
    simp only [firstOverlap]
    split
    · omega
    · split
      · omega
      · rfl

end

end NativeRustcVmX64.WordsHash
