/-
  Rv64mc.Proof.Field.ReduceT

  `reduce` is total: it returns `Reduce.Post`'s value (`Spec.Field.Reduce`), over any program holding its template. A
  leaf with no memory access, so `rv_autoT` leaves only the value, as `rv_auto` does for `Reduce.lean`.

  ## Main definitions

  * `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Spec.Field.Reduce
import Rv64mc.Proof.Field.U128
import Rv64mc.Gen.Tmpl.Verifier.Field.Reduce
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Field.ReduceT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Field

/-- **The total contract of `reduce`**: `Reduce.spec`'s, as a `HoldsT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun _ _ => True) Reduce.Post

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Gen.Verifier.Field.Reduce.Link)
    (hp : p[i]? = some (Gen.Verifier.Field.Reduce.tmpl L)) (need : Nat) : specT env p i need := by
  rv_autoT hp
  simp only [Model.reduce, setWidth_append, setWidth_shift_append, BitVec.xor_assoc, BitVec.xor_comm,
    xor_left_comm]

end Rv64mc.Proof.Field.ReduceT

/-- info: 'Rv64mc.Proof.Field.ReduceT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Field.ReduceT.total
