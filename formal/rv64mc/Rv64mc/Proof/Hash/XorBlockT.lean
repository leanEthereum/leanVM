/-
  Rv64mc.Proof.Hash.XorBlockT

  `verifier::hash::xor_block(state, block)` is total (`XorBlockSafeT`): from a state of `25` lanes at `a0`,
  8-byte aligned, in a window apart from the static data and `NEXT` and from the stack below the stack pointer, and a
  block of `136` bytes at `a1` in a window, it returns, writing at most the state's doublewords (`XorBlock.Out`). It
  does not state the lanes it leaves, which is `Spec.Hash.XorBlock`'s partial contract, not yet proved; no caller's
  safety reads them.

  ## Main definitions

  * `XorPreT`, `XorBlockSafeT`

  ## Main results

  * `total`
-/

import Rv64mc.Spec.Hash.Keccak
import Rv64mc.Spec.Runtime.MemT
import Rv64mc.Tactic.SymT
import Rv64mc.Gen.Tmpl.Verifier.Hash.XorBlock

namespace Rv64mc.Proof.Hash.XorBlockT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Spec.Hash
open Rv64mc.Gen.Verifier.Hash.XorBlock (Link tmpl)

/-- `xor_block`'s total precondition: the state's `200` bytes 8-byte aligned, in the heap window up to the heap's end
    or the stack window, apart from the stack below the stack pointer; the block's `136` bytes in a window. -/
def XorPreT (env : Env) (regs : Reg → Word) (_m : MachineState) : Prop :=
  (regs .x10).toNat % 8 = 0 ∧
    ((0x10000000 ≤ (regs .x10).toNat ∧ (regs .x10).toNat + stateBytes ≤ env.heapEnd.toNat) ∨
      (env.stackLimit.toNat ≤ (regs .x10).toNat ∧ (regs .x10).toNat + stateBytes ≤ 0xc0000000)) ∧
    OffStack env (regs .x2) (regs .x10) stateBytes ∧
    ((0x10000000 ≤ (regs .x11).toNat ∧ (regs .x11).toNat + rate ≤ 0x78000000) ∨
      (0xa0000000 ≤ (regs .x11).toNat ∧ (regs .x11).toNat + rate ≤ 0xc0000000))

/-- **The total contract of `xor_block`**: it returns, writing at most the state. It does not say what it writes. -/
def XorBlockSafeT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (XorPreT env) (fun _ _ _ _ => True) XorBlock.Out

variable {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link}

set_option rv_sym.heap true in
/-- **`xor_block` is total**, with its 16-byte frame. -/
theorem total (hp : p[i]? = some (tmpl L)) : XorBlockSafeT env p i 16 := by
  rv_autoT hp

end Rv64mc.Proof.Hash.XorBlockT

/-- info: 'Rv64mc.Proof.Hash.XorBlockT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Hash.XorBlockT.total
