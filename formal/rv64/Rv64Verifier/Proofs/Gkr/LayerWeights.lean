import Rv64Verifier.Proofs.Gkr.LayerSample

/-!
# `keccak::verify_layer`: the instance weights

`keccak.rs:109-113`, inlined at `0x8000f420..0x8000f4f8`: per mask `RMFE_EMBED[e]` (a `u32`,
`.rodata` at `0xa0000ea8`), the powers of `s` at its bits, pushed into a new `Vec`.

The mask's load `lw` reads at `0xa0000ea8 + 4 e`, a doubleword's upper half for odd `e`; the
generated block at `0x8000f4a0` asks for an aligned address, so it is checked again here by the
symbolic executor with sub-doubleword loads at any address (`cfgA`).
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

def cfgA : Sym.Config := { noAlias := true, anyAlign := true }

/-- The mask's address `x12 + 4 x10`. -/
def maskE : Sym.E := .bin .add (.reg .x12) (.bin .sll (.reg .x10) (.c 2))

/-- `0x8000f4a0` with the mask loaded at any address. -/
def f4a0A : Sym.Expect :=
  { b8000f4a0 with
    regs := b8000f4a0.regs.map fun p ↦ (p.1, if p.1 == .x5 then
      .bin (.ldx .w) (.ld (.bin .and maskE (.c 0xfffffffffffffff8))) (.bin .and maskE (.c 7))
      else p.2)
    obl := [.valid ⟨some maskE, 0⟩ 4] }

theorem f4a0A_spec : Sym.BlockSpec Image.code 0x8000f4a0 9 (fun s ↦ Sym.Oblig.all s f4a0A.obl)
    f4a0A.Holds :=
  Sym.BlockSpec.of_expect (cfg := cfgA) (fuel := 9) (x := f4a0A)
    (words := (Image.code.words.drop 15656).take 9) (by decide +kernel)
    (Sym.CodeAt.slice Image.code 15656 9 0x8000f4a0 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

theorem f4a0A_x5 {s t : MachineState} (h : f4a0A.Holds s t) :
    t.getReg .x5 = BitVec.signExtend 64 (extractWord32
      (s.getMem ((s.getReg .x12 + s.getReg .x10 * 4) &&& 0xfffffffffffffff8))
      (((s.getReg .x12 + s.getReg .x10 * 4) &&& 7).toNat / 4)) :=
  h.reg_eq .x5 rfl (by rv_eval [maskE])

theorem embed_dword {u : MachineState} (h : RodataOk u) {k : Nat} (hk : k < 8) :
    u.getMem (0xa0000ea8 + BitVec.ofNat 64 (8 * k)) =
      rmfeEmbedRust.getD (2 * k + 1) 0 ++ rmfeEmbedRust.getD (2 * k) 0 := by
  interval_cases k <;> exact h.word

/-- The mask `lw` loads: `RMFE_EMBED[e]`, sign-extended. -/
theorem mask_word {u : MachineState} (h : RodataOk u) {e : Nat} (he : e < 16) :
    BitVec.signExtend 64 (extractWord32
      (u.getMem ((0xa0000ea8 + BitVec.ofNat 64 e * 4) &&& 0xfffffffffffffff8))
      (((0xa0000ea8 + BitVec.ofNat 64 e * 4) &&& 7).toNat / 4)) =
      BitVec.signExtend 64 (rmfeEmbedRust.getD e 0) := by
  have ha : (0xa0000ea8 + BitVec.ofNat 64 e * 4) &&& 0xfffffffffffffff8 =
      0xa0000ea8 + BitVec.ofNat 64 (8 * (e / 2)) := by interval_cases e <;> decide
  have ho : ((0xa0000ea8 + BitVec.ofNat 64 e * 4) &&& 7).toNat / 4 = e % 2 := by
    interval_cases e <;> decide
  rw [ha, ho, embed_dword h (by omega)]
  interval_cases e <;> decide

/-- `srlw` by `b` and `andi 1` test the mask's bit `b`. -/
theorem srlw_bit (m : BitVec 32) {b : Nat} (hb : b < 32) :
    BitVec.signExtend 64 (wordResult .srl (BitVec.truncate 32 (BitVec.signExtend 64 m))
      (BitVec.truncate 32 (BitVec.ofNat 64 b))) &&& 1 = 0 ↔ bit32 m b = false := by
  have h1 : BitVec.truncate 32 (BitVec.signExtend 64 m) = m := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [BitVec.getLsbD_signExtend, hi]; omega
  have h2 : (BitVec.truncate 32 (BitVec.ofNat 64 b)).toNat % 32 = b := by
    simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  simp only [wordResult, h1, h2]
  unfold bit32
  have e1 : ((BitVec.signExtend 64 (m >>> b) &&& 1) = 0) ↔ m.getLsbD b = false := by
    constructor
    · intro h
      have := congrArg (fun x : BitVec 64 ↦ x.getLsbD 0) h
      simpa [BitVec.getElem_signExtend, BitVec.getElem_ushiftRight] using this
    · intro h
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rcases i with _ | i
      · simp [BitVec.getElem_signExtend, BitVec.getElem_ushiftRight, h]
      · simp
  have e2 : ((m >>> b &&& 1#32) == 1#32) = m.getLsbD b := by
    cases hz : m.getLsbD b
    · simp only [beq_eq_false_iff_ne, ne_eq]
      intro hc
      have := congrArg (fun x : BitVec 32 ↦ x.getLsbD 0) hc
      simp [hz] at this
    · simp only [beq_iff_eq]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rcases i with _ | i
      · simp [hz]
      · simp
  rw [e1, e2]

end Rv64Verifier.Gkr.Layer
