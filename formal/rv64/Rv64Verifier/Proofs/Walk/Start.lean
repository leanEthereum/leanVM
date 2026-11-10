import Rv64Verifier.Proofs.Walk.Bytes
import Rv64Verifier.Proofs.Runtime.Contracts
import Rv64Verifier.Proofs.Transcript.Duplex
import Rv64Verifier.Blocks.F4

/-!
# `walk` from its entry to `keccak_f`

`0x80000ef8` saves the registers, reads the public input a byte at a time into four words (kept
in `s3`..`s6` and stored at `S - 1312`), stores the IV's four words at `S - 1344`, and zeroes
the other 17 lanes (`memset(S - 1280, 0, 136)`): the 25 lanes `Sponge::new` permutes, `seedWord`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model
  Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The lanes `Sponge::new` permutes, from the entry's memory: the IV's words, the public input's,
zeros. -/
def seedWord (s : MachineState) (j : Nat) : Word :=
  if j < 4 then s.getMem (s.getReg .x11 + 104 + BitVec.ofNat 64 (8 * j))
  else if j < 8 then s.getMem (s.getReg .x12 + BitVec.ofNat 64 (8 * (j - 4))) else 0

/-- At `keccak_f`'s call: the seed at `S - 1344`, the public input's words in `s3`..`s6`. -/
structure Seed (s u : MachineState) : Prop where
  inv : Inv s u
  x9 : u.getReg .x9 = s.getReg .x13
  x19 : u.getReg .x19 = s.getMem (s.getReg .x12 + 8)
  x20 : u.getReg .x20 = s.getMem (s.getReg .x12 + 24)
  x21 : u.getReg .x21 = s.getMem (s.getReg .x12)
  x22 : u.getReg .x22 = s.getMem (s.getReg .x12 + 16)
  x23 : u.getReg .x23 = s.getReg .x10
  x24 : u.getReg .x24 = s.getReg .x11
  seed : ∀ j < 25, u.getMem (s.getReg .x2 - BitVec.ofNat 64 (1344 - 8 * j)) = seedWord s j

theorem seedWord_iv (s : MachineState) {j : Nat} (hj : j < 4) :
    seedWord s j = s.getMem (s.getReg .x11 + BitVec.ofNat 64 (104 + 8 * j)) := by
  simp only [seedWord, hj, ↓reduceIte, BitVec.add_assoc, BitVec.ofNat_add]
  rfl

theorem seedWord_pi (s : MachineState) {j : Nat} (h1 : 4 ≤ j) (h2 : j < 8) :
    seedWord s j = s.getMem (s.getReg .x12 + BitVec.ofNat 64 (8 * (j - 4))) := by
  simp only [seedWord, show ¬ j < 4 by omega, h2, ↓reduceIte]

theorem seedWord_zero (s : MachineState) {j : Nat} (h1 : 8 ≤ j) : seedWord s j = 0 := by
  simp only [seedWord, show ¬ j < 4 by omega, show ¬ j < 8 by omega, ↓reduceIte]

theorem sub_add_ofNat {S : Word} {k j : Nat} (hS : k ≤ S.toNat) (hj : j ≤ k) :
    S - BitVec.ofNat 64 k + BitVec.ofNat 64 j = S - BitVec.ofNat 64 (k - j) := by
  apply BitVec.eq_of_toNat_eq
  have hk : k < 2 ^ 64 := Nat.lt_of_le_of_lt hS S.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by omega : j < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : k - j < 2 ^ 64)]
  omega

set_option maxRecDepth 8192 in
/-- The prologue's block, to `memset`'s call. -/
theorem prologueBlock {s : MachineState} (hpc : s.pc = 0x80000ef8) (hpre : WalkPre s) :
    ∃ u, Reaches Image.code s u ∧ b80000ef8.Holds s u := by
  obtain ⟨hb1, hb2, hb3, hlo⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hin := hpre.input
  have hinS := hpre.inputRO.2.1
  have hbc := hpre.bytecode.mem.self
  have hbcA := hpre.bytecode.mem.align
  have hbcS := hpre.bytecode.self.2.1
  rw [stackLo_eq] at hinS hbcS
  have v0 : Sym.validAccess 1 (s.getReg .x12) = true := by
    simpa using valid1 hin.1 0 (by decide)
  exact Sym.BlockSpec.reaches b80000ef8_spec hpc (by
    rv_eval []
    and_intros
    all_goals first
      | valid_access hval [hb1]
      | exact valid1 hin.1 _ (by decide)
      | exact v0
      | exact hin.2
      | exact Mapped.valid8 hbc (by addr_omega [hbc]) (by addr_omega [hbc]) (by addr_omega [hbc, hbcA])
      | addr_omega [hinS, hbcS, hb1, hin, hbc])

theorem prologue (hMS : MemsetSpec 0x800126f4) {s : MachineState} (hpc : s.pc = 0x80000ef8)
    (hpre : WalkPre s) :
    ∃ u, Reaches Image.code s u ∧ ((u.pc = 0x800010e4 ∧ Seed s u) ∨ Dead Image.code u) := by
  obtain ⟨hb1, hb2, hb3, hlo⟩ := bounds hpre
  obtain ⟨u₁, hr₁, h₁⟩ := prologueBlock hpc hpre
  have hx := hpre.stack.next
  rw [stackLo_eq] at hx
  have hm₁ := DFrame.of_memFrame (b80000ef8_frame h₁ (by omega))
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 2656 := b80000ef8_x2 h₁
  have hn₁ : heapNext u₁ = heapNext s := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (hm₁ nextAddr fun i hi hw ↦ by addr_omega [hx, hw, hi, hb1])
  have I₁ : Inv s u₁ := {
    sp := sp₁
    heap := ⟨hn₁ ▸ hpre.heap.lo, hn₁ ▸ hpre.heap.hi⟩
    mono := hn₁.ge
    frame := hm₁.mono fun a ha ↦ Or.inr (Or.inl (by rw [stackLo_eq]; addr_omega [ha, hb1]))
    saved := fun i hi ↦ by
      interval_cases i
      exacts [b80000ef8_m_x2_n8 h₁, b80000ef8_m_x2_n16 h₁, b80000ef8_m_x2_n24 h₁,
        b80000ef8_m_x2_n32 h₁, b80000ef8_m_x2_n40 h₁, b80000ef8_m_x2_n48 h₁,
        b80000ef8_m_x2_n56 h₁, b80000ef8_m_x2_n64 h₁, b80000ef8_m_x2_n72 h₁,
        b80000ef8_m_x2_n80 h₁, b80000ef8_m_x2_n88 h₁, b80000ef8_m_x2_n96 h₁,
        b80000ef8_m_x2_n104 h₁] }
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 1280 := b80000ef8_x10 h₁
  have x12₁ : u₁.getReg .x12 = 136 := b80000ef8_x12 h₁
  obtain ⟨u₂, hr₂, ⟨hpc₂, hp₂, post₂⟩ | hd⟩ := hMS.call hr₁ (b80000ef8_pc h₁)
    (show Mapped _ _ by rw [x10₁, x12₁]; addr_omega [hb1, hb2])
  swap
  · exact ⟨u₂, hr₂, Or.inr hd⟩
  have by₂ := post₂.bytes
  have fr₂ := post₂.frame
  rw [x10₁, x12₁] at by₂ fr₂
  have st₂ : Step s u₁ u₂ (s.getReg .x2 - 1280) 136 := by
    have fr := DFrame.of_byteFrame fr₂
    have he : heapNext u₂ = heapNext u₁ := by
      simp only [heapNext]
      exact congrArg BitVec.toNat (fr nextAddr fun i hi hw ↦ by addr_omega [hx, hw, hi, hb1])
    exact ⟨fr.mono fun a ha ↦ Or.inl (by simpa using ha), ⟨he ▸ I₁.heap.lo, he ▸ I₁.heap.hi⟩,
      he.ge, hp₂.reg .x2⟩
  have I₂ := I₁.after hpre (inFrame hpre (k := 1280) (n := 136) (by omega) (by omega)) st₂
  have keep (r : Reg) (hr : r ∈ calleeSaved := by decide) : u₂.getReg r = u₁.getReg r := hp₂.reg r hr
  have w₂ (k : Nat) (hk : 1288 ≤ k) (hk2 : k ≤ 1344) :
      u₂.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = u₁.getMem (s.getReg .x2 - BitVec.ofNat 64 k) :=
    st₂.word hpre (by addr_omega [hb1, hk, hk2]) (by addr_omega [hb1, hk, hk2])
  have p0 : u₁.getMem (s.getReg .x2 - 1312) = s.getMem (s.getReg .x12) :=
    h₁.mem_eq 3 (by decide) (by rv_eval []) (by rv_eval []; exact assemble_eq _)
  have p1 : u₁.getMem (s.getReg .x2 - 1304) = s.getMem (s.getReg .x12 + 8) :=
    h₁.mem_eq 2 (by decide) (by rv_eval []) (by rv_eval []; exact assemble_eq _)
  have p2 : u₁.getMem (s.getReg .x2 - 1296) = s.getMem (s.getReg .x12 + 16) :=
    h₁.mem_eq 1 (by decide) (by rv_eval []) (by rv_eval []; exact assemble_eq _)
  have p3 : u₁.getMem (s.getReg .x2 - 1288) = s.getMem (s.getReg .x12 + 24) :=
    h₁.mem_eq 0 (by decide) (by rv_eval []) (by rv_eval []; exact assemble_eq _)
  rw [b80000ef8_x11 h₁, show (136 : Word).toNat = 136 from rfl] at by₂
  refine ⟨u₂, hr₂, Or.inl ⟨?_, {
    inv := I₂
    x9 := (keep .x9).trans (b80000ef8_x9 h₁)
    x19 := ?_
    x20 := ?_
    x21 := ?_
    x22 := ?_
    x23 := (keep .x23).trans (b80000ef8_x23 h₁)
    x24 := (keep .x24).trans (b80000ef8_x24 h₁)
    seed := ?_ }⟩⟩
  · rw [hpc₂, returnAddress_eq, b80000ef8_x1 h₁]; decide
  · rw [keep .x19]
    exact h₁.reg_eq .x19 rfl (by rv_eval []; exact assemble_eq _)
  · rw [keep .x20]
    exact h₁.reg_eq .x20 rfl (by rv_eval []; exact assemble_eq _)
  · rw [keep .x21]
    exact h₁.reg_eq .x21 rfl (by rv_eval []; exact assemble_eq _)
  · rw [keep .x22]
    exact h₁.reg_eq .x22 rfl (by rv_eval []; exact assemble_eq _)
  · intro j hj
    by_cases hj8 : 8 ≤ j
    · rw [seedWord_zero s hj8, show s.getReg .x2 - BitVec.ofNat 64 (1344 - 8 * j) =
        s.getReg .x2 - 1280 + BitVec.ofNat 64 (8 * (j - 8)) by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj, hj8]]
      exact Transcript.Duplex.getMem_zero_of_bytesAt (by decide) by₂ (by addr_omega [hb1, hb3])
        (by omega) (by omega)
    rw [w₂ _ (by omega) (by omega)]
    by_cases hj4 : 4 ≤ j
    · rw [seedWord_pi s hj4 (by omega)]
      interval_cases j
      · exact p0.trans (by simp)
      · exact p1
      · exact p2
      · exact p3
    · rw [seedWord_iv s (by omega)]
      interval_cases j
      · exact b80000ef8_m_x2_n1344 h₁
      · exact b80000ef8_m_x2_n1336 h₁
      · exact b80000ef8_m_x2_n1328 h₁
      · exact b80000ef8_m_x2_n1320 h₁

end Rv64Verifier.Proofs.Walk
