import Rv64Verifier.Proofs.Bytecode.EvalCredit

/-!
# `Bytecode::evaluate`: the side conditions of `0x80011408`

Its accesses are frame slots and the eight bit sums of the bucket's byte: valid, and distinct
where the executor assumed so. Kept apart, being slow.
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts
  Rv64Verifier.Model Rv64Verifier.Blocks.F84
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

variable {e : Env}

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 20000 in
theorem credit_obl (he : EnvOk e) {u : MachineState} (hsp : u.getReg .x2 = e.s.getReg .x2 - 1968)
    {c : BitVec 16} (h16 : u.getReg .x16 = c.setWidth 64) (hc : c.toNat < 2048) :
    Sym.Oblig.all u b80011408.obl := by
  have hsp' := he.sp
  have hst := he.pre.stack.valid
  have hcb : (c.setWidth 64 : Word).toNat = c.toNat := by
    rw [BitVec.toNat_setWidth]; have := c.isLt; omega
  have hbyte := bucketByte (c.setWidth 64) (by rw [hcb]; exact hc)
  rw [hcb] at hbyte
  rv_eval [hsp, h16, mul24, hbyte]
  and_intros <;> first
    | valid_access hst [hsp', hc]
    | addr_omega [hsp', hc]

end Rv64Verifier.Proofs.Bytecode.Eval
