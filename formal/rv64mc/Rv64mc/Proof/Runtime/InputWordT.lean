/-
  Rv64mc.Proof.Runtime.InputWordT

  `Input::word` is total: it returns the reader's next word as `InputWordSpec` says, or, on an
  empty slice, ends the run with the guest's abort (`halt(2)`). The total counterpart of
  `InputWord.lean`, over the same template, from `halt`'s `Aborts` (`HaltT.lean`).

  The reader and the words it points to are the caller's, so their windows and alignment are in
  the precondition (`WordPreT`): the reader 8-byte aligned and below the stack window's end, its
  slice from an 8-byte aligned pointer at or above the input window's start, its `8 * len` bytes
  ending within the heap. `main`'s reader over the input satisfies it (`inputBase`, at most
  `inputCapacity` words), and a return keeps it: the pointer moves up by 8 as the length drops by
  one.

  ## Main definitions

  * `WordPreT`, `WordStop`, `InputWordSpecT`

  ## Main results

  * `total`
  * `wordPreT_input`: `main`'s reader over the input satisfies `WordPreT`
-/

import Rv64mc.Proof.Runtime.InputWord
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Tactic.TStep

namespace Rv64mc.Proof.Runtime.InputWordT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Proof.Runtime
open Rv64mc.Gen.VerifierRv64.Input.Word (Link tmpl)
open Rv64mc.Proof.Runtime.InputWord (inputPtrAt_eq inputLenAt_eq ne_add8)

/-- `Input::word`'s total precondition: `WordPre`, the reader 8-byte aligned and below the stack window's end, and
    its slice's `8 * len` bytes from an 8-byte aligned pointer at or above the input window's start to at most the
    heap's end. -/
def WordPreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  WordPre env regs m ∧ (regs .x10).toNat % 8 = 0 ∧ (regs .x10).toNat + Layouts.Input.byteSize ≤ 0xc0000000 ∧
    0x10000000 ≤ (m.getMem (inputPtrAt (regs .x10))).toNat ∧ (m.getMem (inputPtrAt (regs .x10))).toNat % 8 = 0 ∧
    (m.getMem (inputPtrAt (regs .x10))).toNat + 8 * (m.getMem (inputLenAt (regs .x10))).toNat ≤ env.heapEnd.toNat

/-- Where `Input::word` may end the run: `a0 = 2`, and the reader's slice was empty. -/
def WordStop (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = 2 ∧ m.getMem (inputLenAt (regs .x10)) = 0

/-- **The total contract of `Input::word`**: `InputWordSpec`'s, or the abort on an empty slice. -/
def InputWordSpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (WordPreT env) WordPost WordOut (Stop := WordStop)

variable {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat}

/-- **`main`'s reader satisfies `WordPreT`**: 8-byte aligned in the stack, over at most `inputCapacity` words at
    `inputBase`, below a heap end at or above the heap's start. -/
theorem wordPreT_input {regs : Reg → Word} {m : MachineState} {n : Nat}
    (hlo : env.stackLimit.toNat ≤ (regs .x10).toNat) (hal : (regs .x10).toNat % 8 = 0)
    (hhi : (regs .x10).toNat + 16 ≤ 0xc0000000) (hq : m.getMem (regs .x10) = inputBase)
    (hl : m.getMem (regs .x10 + 8#64) = BitVec.ofNat 64 n) (hn : n ≤ inputCapacity)
    (hheap : 0x20000000 ≤ env.heapEnd.toNat) : WordPreT env regs m := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by unfold inputCapacity at hn; omega)
  simp only [WordPreT, WordPre, inputPtrAt_eq, inputLenAt_eq, hq, hl, hn', Layouts.Input.byteSize,
    show inputBase.toNat = 0x10000000 by decide]
  unfold inputCapacity at hn
  exact ⟨⟨hlo, by omega⟩, hal, hhi, le_rfl, trivial, by omega⟩

/-- **`Input::word` is total**, with no stack, from `halt`'s `Aborts`. -/
theorem total (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p) (hhalt : Aborts env p L.halt.idx 0) :
    InputWordSpecT env p i 0 := by
  intro Q ret top rest regs m hpre hstop hk
  have ⟨⟨⟨hra, hsp⟩, hstk, hst, hnx, ⟨⟨hlo, hhi⟩, hal8, hrd, hqlo, hqal, hqhi⟩, hal⟩, hwin⟩ := hpre
  simp only [inputPtrAt_eq, inputLenAt_eq] at hqlo hqal hqhi
  have hlay := env.layout
  simp only [Layouts.Input.byteSize] at hhi hrd
  have h8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
  have hw0 : inWindow (regs .x10) 8 = true := hwin.stackObj hlo (by omega)
  have hw8 : inWindow (regs .x10 + 8#64) 8 = true := hwin.stackObj (by omega) (by omega)
  tsteps hp
  refine TotalRv.ld8 hp rfl (by simpa [Expr.eval, BinOp.eval] using hw8)
    (by simp only [Expr.eval, BinOp.eval]; omega) ?_
  tsteps hp
  tcond hp as hc
  -- an empty slice: `halt`
  · tsteps hp
    refine Aborts.call hhalt hpre hp rfl (callee_site hL.halt hL.s0 (by simp [updReg_apply]))
      (by simp [updReg_apply, hsp]) fun fr st r' m' h2 ha => hstop fr st r' m' ⟨h2, ?_⟩ ha
    simpa [condEval, operandVal, cmpEval, updReg_apply, inputLenAt_eq] using hc
  -- the next word: `q` the slice's pointer, `l ≠ 0` its length
  · have hl0 : m.getMem (regs .x10 + 8#64) ≠ 0 := by simpa [condEval, operandVal, cmpEval] using hc
    have hl1 : 1 ≤ (m.getMem (regs .x10 + 8#64)).toNat :=
      Nat.one_le_iff_ne_zero.2 fun h => hl0 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    have hwq : inWindow (m.getMem (regs .x10)) 8 = true := hwin.heapObj hqlo (by omega)
    tsteps hp
    refine TotalRv.ld8 hp rfl (by tnorm; exact hw0) (by tnorm; omega) ?_
    tnorm
    tsteps hp
    refine TotalRv.ld8 hp rfl (by tnorm; exact hwq) (by tnorm; omega) ?_
    tnorm
    tsteps hp
    refine TotalRv.sd8 hp rfl (by tnorm; exact hw0) (by tnorm; omega) (by tnorm; exact hwin.noCodeAt hw0 (by decide)) ?_
    tnorm
    tsteps hp
    refine TotalRv.sd8 hp rfl (by tnorm; exact hw8) (by tnorm; omega) (by tnorm; exact hwin.noCodeAt hw8 (by decide)) ?_
    tnorm
    tsteps hp
    refine TotalRv.ret hp rfl (by tnorm; exact hra) (by tnorm; exact hsp) ?_
    have hn0 : regs .x10 ≠ env.nextAddr := fun h => by rw [h] at hlo; omega
    have hn8 : regs .x10 + 8#64 ≠ env.nextAddr := fun h => by rw [← BitVec.toNat_inj, h8] at h; omega
    have hs0 : (regs .x10).toNat < env.staticLo.toNat ∨ env.staticHi.toNat ≤ (regs .x10).toNat := by omega
    have hs8 : (regs .x10 + 8#64).toNat < env.staticLo.toNat ∨ env.staticHi.toNat ≤ (regs .x10 + 8#64).toNat := by
      omega
    have hf1 := Env.Frame.setMem_out (top := top) (out := WordOut regs m)
      (v := m.getMem (regs .x10) + 8#64) hnx (Or.inl (inputPtrAt_eq _).symm) hn0
    have hf2 := Env.Frame.setMem_out (top := top) (out := WordOut regs m)
      (v := m.getMem (regs .x10 + 8#64) + 18446744073709551615#64) hf1.2.1 (Or.inr (inputLenAt_eq _).symm) hn8
    refine hk _ _ ⟨⟨by simp (disch := decide) only [AbiRegs.updReg_iff]; exact AbiRegs.refl hsp,
      hf1.trans hf2 (Nat.le_refl _) fun a h => Or.inr (Or.inr (Or.inr h)),
      Env.static_setMem (Env.static_setMem hst hs0) hs8, ?_, ?_, ?_, ?_⟩, rfl⟩
    · show m.getMem (inputLenAt (regs .x10)) ≠ 0
      rw [inputLenAt_eq]
      exact hl0
    · show m.getMem (m.getMem (regs .x10)) = m.getMem (m.getMem (inputPtrAt (regs .x10)))
      rw [inputPtrAt_eq]
    · rw [inputPtrAt_eq]
      simp [MachineState.getMem, MachineState.setMem, ne_add8 (regs .x10)]
    · rw [inputLenAt_eq, BitVec.sub_eq_add_neg]
      simp [MachineState.getMem, MachineState.setMem]

end Rv64mc.Proof.Runtime.InputWordT

/-- info: 'Rv64mc.Proof.Runtime.InputWordT.wordPreT_input' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.InputWordT.wordPreT_input

/-- info: 'Rv64mc.Proof.Runtime.InputWordT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.InputWordT.total
