import Rv64Verifier.Proofs.Bytecode.Basic
import Rv64Verifier.Blocks.F1

/-!
# `Input::digest`: the side conditions of its main block

`0x800000f4` (`Blocks/F1.lean`) saves twelve registers, loads four words of the input, stores
their 32 bytes one by one and advances the `Input`; its side conditions (valid accesses, and
addresses the executor assumed distinct) follow from the ranges being mapped and apart. Kept
apart from `Digest.lean`, which it would slow down.
-/

namespace Rv64Verifier.Proofs.Bytecode
open RiscvZkvm.Rv64 Rv64Verifier.Blocks.F1 Rv64Verifier.Runtime
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `digest`'s 96-byte frame. -/
@[rv_addr] def digestStack : Nat := 96

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem digest_obl {u : MachineState} (ho : Mapped (u.getReg .x10) 32)
    (hoa : (u.getReg .x10).toNat % 8 = 0) (hi : Mapped (u.getReg .x11) 16)
    (hia : (u.getReg .x11).toNat % 8 = 0) (hp : Mapped (u.getMem (u.getReg .x11)) 32)
    (hpa : (u.getMem (u.getReg .x11)).toNat % 8 = 0) (hst : StackOk u digestStack)
    (hoi : Apart (u.getReg .x10) 32 (u.getReg .x11) 16)
    (hos : Apart (u.getReg .x10) 32 (stackLo u digestStack) digestStack)
    (his : Apart (u.getReg .x11) 16 (stackLo u digestStack) digestStack)
    (hps : Apart (u.getMem (u.getReg .x11)) 32 (stackLo u digestStack) digestStack) :
    Sym.Oblig.all u b800000f4.obl := by
  have hsp := hst.bounds (by decide) (by decide)
  rv_eval []
  and_intros <;> first
    | exact hoa
    | valid_in ho [ho, hoa]
    | valid_in hi [hi, hia]
    | valid_in hp [hp, hpa]
    | valid_access hst.valid [hsp]
    | addr_omega [hsp, ho, hoa, hi, hia, hp, hpa, hos, his, hps, hoi]

end Rv64Verifier.Proofs.Bytecode
