/-
  Rv64mc.Proof.Transcript.GrindingBitsT

  `grinding_bits` is total: it returns `GrindingBits.Post`'s bit count (`Spec.Transcript.GrindingBits`), over any
  program holding its template. A leaf with no memory access: the partial proof (`GrindingBits.lean`) ported by
  `rv_autoT`, with its lemmas.

  ## Main definitions

  * `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Transcript.GrindingBits
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Transcript.GrindingBitsT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Transcript Rv64mc.Proof.Transcript.GrindingBits
open Rv64mc.Gen.Verifier.Transcript.GrindingBits (Link tmpl)

/-- **The total contract of `grinding_bits`**: `GrindingBits.spec`'s, as a `HoldsT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun _ _ => True) GrindingBits.Post

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (_hL : L.WF p)
    {need : Nat} : specT env p i need := by
  rv_autoT hp
  · have hN := (small_iff _ _).1 hc_1
    have hp := pred_split hN
    obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.1 hc
    rw [h1, h2] at hp
    simp at hp
    omega
  · change 0#64 - BinOp.ult.eval (125#64 - Model.popc (Model.smear (regs .x11 - BinOp.ult.eval (regs .x10) 1#64) ^^^
      18446744073709551615#64)) 126#64 &&& (125#64 - Model.popc (Model.smear (regs .x11 -
      BinOp.ult.eval (regs .x10) 1#64) ^^^ 18446744073709551615#64)) = _
    have hN := (small_iff _ _).1 hc_1
    have hne : (regs .x11 - BinOp.ult.eval (regs .x10) 1#64).toNat ≠ 0 := fun h =>
      hc (BitVec.eq_of_toNat_eq (by simpa using h))
    have hB := Model.bitLength_le_64 (regs .x11 - BinOp.ult.eval (regs .x10) 1#64)
    rw [Model.smear_eq, Model.popc_eq hB, fin_eq (by omega), grinding_eq, ite_eq_right hN, ← pred_split hN,
      bitLength_hi hne (BitVec.isLt _)]
    congr 1
    omega
  · change 0#64 - BinOp.ult.eval (125#64 - (Model.popc (Model.smear (regs .x10 + 18446744073709551615#64) ^^^
      18446744073709551615#64) + 64#64)) 126#64 &&& (125#64 - (Model.popc (Model.smear (regs .x10 +
      18446744073709551615#64) ^^^ 18446744073709551615#64) + 64#64)) = _
    have hN := (small_iff _ _).1 hc_1
    have hB := Model.bitLength_le_64 (regs .x10 + 18446744073709551615#64)
    rw [Model.smear_eq, Model.popc_eq hB, ← BitVec.ofNat_add, fin_eq (by omega), grinding_eq, ite_eq_right hN,
      ← pred_split hN, hc]
    rw [show (0#64 : Word).toNat * 2 ^ 64 = 0 from rfl, Nat.zero_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · rw [grinding_eq, ite_eq_left (Decidable.of_not_not fun h => hc ((small_iff _ _).2 h))]

end Rv64mc.Proof.Transcript.GrindingBitsT

/-- info: 'Rv64mc.Proof.Transcript.GrindingBitsT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Transcript.GrindingBitsT.total
