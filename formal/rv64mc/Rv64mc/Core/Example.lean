/-
  Rv64mc.Core.Example

  `Holds` at work on two hand-written templates: a leaf that adds one to `a0` (`inc`), and a function that saves
  `ra` on its stack, calls it through a site and returns (`caller`). The caller's proof uses the leaf's contract at
  the call (`lsym … using [hinc.contract]`), its frame (`Env.Frame.trans`) to find `ra` again, and the stack lemmas
  for its own store. Nothing here names an address of the image.
-/

import Rv64mc.Core.Holds
import Rv64mc.Link.Basic

namespace Rv64mc.Example

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- `addi a0, a0, 1; ret`. -/
def incTmpl (base : Word) : Lfundef (Op Reg) Reg :=
  { name := "inc", addr := base, depth := 0, body :=
    [.Llabel .internal 0, .Lopn (.set .x10 (.bin .add (.reg .x10) (.imm 1#64))), .Llabel .internal 1, .Lret] }

/-- What `caller` knows of the program: its entry, its callee, its call site. -/
structure Link where
  base : Word
  inc : Callee
  site : Site

/-- The link's facts, proved of the concrete program (`Callee.WF`, `Site.WF`), as equations for `simp`. -/
structure Link.WF (p : Lprog (Op Reg) Reg) (L : Link) : Prop where
  inc : (p[L.inc.idx]?).map (·.addr) = some L.inc.entry
  site : (L.site.hi + L.site.lo) &&& 0xfffffffffffffffe#64 = L.inc.entry

/-- `addi sp, sp, -16; sd ra, 8(sp); auipc ra, hi; jalr ra, lo(ra); ld ra, 8(sp); addi sp, sp, 16; ret`. -/
def callerTmpl (L : Link) : Lfundef (Op Reg) Reg :=
  { name := "caller", addr := L.base, depth := 0, body :=
    [.Llabel .internal 0, .Lopn (.set .x2 (.bin .add (.reg .x2) (.imm 0xfffffffffffffff0#64))),
     .Llabel .internal 1, .Lopn (.store .b8 (.bin .add (.reg .x2) (.imm 8#64)) (.reg .x1)),
     .Llabel .internal 2, .Lopn (.set .x1 (.imm L.site.hi)),
     .Llabel .internal 3, .Lcall (L.base + 16#64)
       (.indirect (.bin .and (.bin .add (.reg .x1) (.imm L.site.lo)) (.imm 0xfffffffffffffffe#64)) [L.inc.idx]),
     .Llabel .internal 4, .Lopn (.load .x1 .b8 false (.bin .add (.reg .x2) (.imm 8#64))),
     .Llabel .internal 5, .Lopn (.set .x2 (.bin .add (.reg .x2) (.imm 16#64))),
     .Llabel .internal 6, .Lret] }

/-- Both add one to `a0`. -/
def Post (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = regs .x10 + 1

variable (env : Env) (p : Lprog (Op Reg) Reg)

/-- The leaf's contract, with no stack. -/
theorem inc_ok (i : Nat) (base : Word) (hp : p[i]? = some (incTmpl base)) :
    Holds env p i 0 (fun _ _ => True) Post := by
  intro G n Q ret top rest regs m ⟨⟨hra, hsp⟩, _, hst, hnx, _⟩ hk
  lsym hp with [hra, hsp]
  exact hk _ _ ⟨⟨by simp [updReg_apply, hsp], by simp [updReg_apply], by simp [updReg_apply],
    by simp [updReg_apply], by simp [updReg_apply], by simp [updReg_apply], by simp [updReg_apply],
    by simp [updReg_apply], by simp [updReg_apply], by simp [updReg_apply], by simp [updReg_apply],
    by simp [updReg_apply], by simp [updReg_apply]⟩, Env.Frame.refl hnx, hst, by simp [Post, updReg_apply]⟩

/-- The caller's contract, from the leaf's: 16 bytes of its own stack. -/
theorem caller_ok (j : Nat) (L : Link) (hp : p[j]? = some (callerTmpl L)) (hL : L.WF p)
    (hinc : Holds env p L.inc.idx 0 (fun _ _ => True) Post) :
    Holds env p j 16 (fun _ _ => True) Post := by
  intro G n Q ret top rest regs m ⟨⟨hra, hsp⟩, hstk, hst, hnx, _⟩ hk
  have hlay := env.layout
  -- the slot `ra` is saved in, and the callee's stack top
  have hslot : (top + 0xfffffffffffffff8#64).toNat = top.toNat - 8 := by bv_omega
  have hsp' : (top + 0xfffffffffffffff0#64).toNat = top.toNat - 16 := by bv_omega
  have hlo : env.stackLimit.toNat ≤ (top + 0xfffffffffffffff8#64).toNat := by omega
  lsym hp with [hra, hsp, Lprog.Isa.addrAt, hL.inc, hL.site, Holds.post, AbiRegs]
    using [hinc.contract]
  -- the callee's precondition
  · refine ⟨⟨by simp [updReg_apply], by simp [updReg_apply]⟩, by simp only [lsym_simp, hsp']; omega,
      Env.static_setMem_stack hst hlo, by rw [Env.next_setMem_stack hlo]; exact hnx, trivial⟩
  -- `ra` read back from the slot the callee keeps
  · have := hret.2.1.getMem_above (by omega) (a := top + 0xfffffffffffffff8#64) (by omega) id
    simp [updReg_apply, this]
  · simp [updReg_apply]
  · apply hk
    obtain ⟨hr, hfr, hs, hpo⟩ := hret
    refine ⟨?_, (Env.Frame.setMem_stack hnx hlo (by omega)).trans hfr (by omega) nofun, hs, ?_⟩
    · simp only [AbiRegs, updReg_apply] at hr ⊢
      simp [hr]
    · simp only [Post, updReg_apply] at hpo ⊢
      simp [hpo]

end Rv64mc.Example
