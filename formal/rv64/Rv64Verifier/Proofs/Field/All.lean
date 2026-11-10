import Rv64Verifier.Proofs.Field.Clmul
import Rv64Verifier.Proofs.Field.BaseMulFun
import Rv64Verifier.Proofs.Field.Mul
import Rv64Verifier.Proofs.Field.MulK
import Rv64Verifier.Proofs.Field.Square
import Rv64Verifier.Proofs.Field.Sum
import Rv64Verifier.Proofs.Field.KInv
import Rv64Verifier.Proofs.Field.Pow

/-!
# The field functions' contracts, with no hypotheses

Each `Proofs/Field` contract, its callees' contracts discharged by their own proofs, and
`Contracts.MulSpec`, `M3` from `.rodata`.
-/

namespace Rv64Verifier.Proofs.Field
open Rv64Verifier.FieldContracts Rv64Verifier.Contracts

theorem clmul : ClmulSpec := Clmul.clmul_spec
theorem baseMul : BaseMulSpec := BaseMulFun.base_mul_fun
theorem eMul : EMulSpec := Mul.mul_spec
theorem mulK : MulKSpec := MulK.mul_k_spec
theorem kSquare : KSquareSpec := Square.k_square_spec
theorem eSquare : ESquareSpec := Square.e_square_spec
theorem kInv : KInvSpec := KInv.k_inv_spec kSquare baseMul
theorem ePow : PowSpec := Pow.pow_spec eMul eSquare
theorem eSum : SumSpec := Sum.sum_spec

/-- **`mul` multiplies in `E`**, from `.rodata` in place. -/
theorem mul : MulSpec := fun s hpc hpre ↦
  eMul s hpc ⟨hpre.toMulArgs, poolOk_of_rodata hpre.rodata hpre.stackRodata⟩

/-! Lean's three axioms, nothing native. -/

/-- info: 'Rv64Verifier.Proofs.Field.clmul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms clmul

/-- info: 'Rv64Verifier.Proofs.Field.baseMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms baseMul

/-- info: 'Rv64Verifier.Proofs.Field.eMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms eMul

/-- info: 'Rv64Verifier.Proofs.Field.mulK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mulK

/-- info: 'Rv64Verifier.Proofs.Field.kSquare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms kSquare

/-- info: 'Rv64Verifier.Proofs.Field.eSquare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms eSquare

/-- info: 'Rv64Verifier.Proofs.Field.kInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms kInv

/-- info: 'Rv64Verifier.Proofs.Field.ePow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ePow

/-- info: 'Rv64Verifier.Proofs.Field.eSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms eSum

/-- info: 'Rv64Verifier.Proofs.Field.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mul

end Rv64Verifier.Proofs.Field
