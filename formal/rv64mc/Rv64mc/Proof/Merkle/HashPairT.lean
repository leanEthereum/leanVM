/-
  Rv64mc.Proof.Merkle.HashPairT

  `hash_pair` is total (`specT`): from the digest's slot (`out`, `a0`) in a window apart from the stack below the
  stack pointer, the left digest's bytes (`a1`) in a window and the right one's (`a2`) in a window apart from that
  stack, it returns, writing at most the slot's doublewords (`DigestOut`). Safety only: the digest written is
  `keccak_hash`'s, whose functional contract (`Spec.Hash.Keccak`) is not total (`KeccakHashSafeT`).

  ## Main definitions

  * `PreT`, `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Hash.KeccakHashT
import Rv64mc.Proof.Runtime.MemcpyT
import Rv64mc.Proof.Runtime.WinT
import Rv64mc.Spec.Merkle.Merkle
import Rv64mc.Tactic.SymT
import Rv64mc.Gen.Tmpl.Verifier.Merkle.HashPair

namespace Rv64mc.Proof.Merkle.HashPairT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Gen.Verifier.Merkle.HashPair (Link tmpl)

/-- The total precondition: the slot in a window and apart from the stack below the stack pointer, the left digest
    in a window, the right one in a window and apart from that stack. -/
def PreT (env : Env) (regs : Reg → Word) (_m : MachineState) : Prop :=
  InWin env (regs .x10) Layouts.Digest.byteSize ∧ OffStack env (regs .x2) (regs .x10) Layouts.Digest.byteSize ∧
    InWin env (regs .x11) Layouts.Digest.byteSize ∧
    inWindow (regs .x12) Layouts.Digest.byteSize = true ∧ OffStack env (regs .x2) (regs .x12) Layouts.Digest.byteSize

/-- **The total contract of `hash_pair`**: it returns, writing at most the slot's doublewords. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (fun _ _ _ _ => True) fun regs _ => Spec.Hash.DigestOut (regs .x10)

set_option rv_sym.heap true in
/-- **`hash_pair` is total.** -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needC needK : Nat} (hnC : 80 + needC ≤ need) (hnK : 80 + needK ≤ need)
    (hcp : Runtime.MemcpyT.MemcpySpecT env p L.memcpy.idx needC)
    (hkh : Hash.KeccakHashT.KeccakHashSafeT env p L.keccakHash.idx needK) : specT env p i need := by
  rv_autoT hp with [hL, (by omega : env.stackLimit.toNat + 80 ≤ top.toNat)] using [hcp, hkh]
  all_goals
    have h80 : (top + 18446744073709551536#64).toNat = top.toNat - 80 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h48 : (top + 18446744073709551568#64).toNat = top.toNat - 48 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have := hpre_12.top_le
    have := hpre_12.nextAddr_ge
    have := env.layout
    have hx12 := inWindow_iff.1 hpre_9
    have hoff := hpre_2 ▸ hpre_10
    simp only [Layouts.Digest.byteSize, OffStack, inWindow_iff, h80, h48, show (32#64).toNat = 32 from rfl,
      show (64#64).toNat = 64 from rfl] at hx12 hoff ⊢
  · omega
  · exact Or.inr ⟨Or.inr ⟨by omega, by omega⟩, by omega, hx12, by omega⟩
  · exact Or.inr ⟨Or.inr ⟨by omega, by omega⟩, by omega⟩

end Rv64mc.Proof.Merkle.HashPairT

/-- info: 'Rv64mc.Proof.Merkle.HashPairT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Merkle.HashPairT.total
