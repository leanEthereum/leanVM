import Rv64Verifier.Proofs.Multilinear.Dot
import Rv64Verifier.Proofs.Multilinear.PolyEval
import Rv64Verifier.Proofs.Multilinear.IndexMle
import Rv64Verifier.Proofs.Multilinear.Clone
import Rv64Verifier.Proofs.Multilinear.SelectorPoint
import Rv64Verifier.Proofs.Multilinear.EqAbove
import Rv64Verifier.Proofs.Multilinear.FromElem
import Rv64Verifier.Proofs.Multilinear.Powers
import Rv64Verifier.Proofs.Multilinear.ScalerNew
import Rv64Verifier.Proofs.Multilinear.Frames
import Rv64Verifier.Proofs.Multilinear.SpecExtend
import Rv64Verifier.Proofs.Multilinear.EqKernel
import Rv64Verifier.Proofs.Multilinear.Concat
import Rv64Verifier.Proofs.Multilinear.SliceConcat
import Rv64Verifier.Proofs.Field.All
import Rv64Verifier.Proofs.Runtime.All

/-!
# The multilinear helpers' contracts, their callees' discharged

Each `Proofs/Multilinear` contract with its callees' contracts proved.
-/

namespace Rv64Verifier.Proofs.Multilinear
open Rv64Verifier.MultilinearContracts Rv64Verifier.Runtime

theorem dot : DotSpec := Dot.dot_spec Field.mul
theorem polyEval : PolyEvalSpec := PolyEval.poly_eval_spec Field.mul
theorem indexMle : IndexMleSpec := IndexMle.index_mle_spec Field.mul Field.eSquare
theorem selectorPoint : SelectorSpec := SelectorPoint.selector_point_spec tryAllocZeroed
theorem eqAbove : EqAboveSpec := EqAbove.eq_above_spec selectorPoint EqEval.eq_eval_proved
theorem fromElem : FromElemSpec := FromElem.from_elem_spec tryAllocZeroed
theorem powers : PowersSpec := Powers.powers_spec tryAllocZeroed Field.mul
theorem scalerNew : ScalerSpec := ScalerNew.scaler_new_spec fromElem

theorem clone : CloneSpec := Clone.clone_spec tryAllocZeroed Runtime.memcpy

/-- `spec_extend` with room enough. -/
theorem specExtend : ExtendSpec := SpecExtend.extend_spec Runtime.memcpy

theorem eqKernel : EqKernelSpec := EqKernel.eq_kernel_spec fromElem scalerNew Field.mul

/-- `[Vec<E>; 2]::concat`, as `Proofs/Transcript/Contracts.lean` states it. -/
theorem concat : Transcript.ConcatSpec := Concat.concat_spec tryAllocZeroed specExtend

theorem sliceConcat : SliceConcatSpec := SliceConcat.slice_concat_spec tryAllocZeroed specExtend

end Rv64Verifier.Proofs.Multilinear

/-! Lean's three axioms, nothing native. -/

/-- info: 'Rv64Verifier.Proofs.Multilinear.dot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Multilinear.dot

/-- info: 'Rv64Verifier.Proofs.Multilinear.polyEval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Multilinear.polyEval

/-- info: 'Rv64Verifier.Proofs.Multilinear.indexMle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Multilinear.indexMle

/-- info: 'Rv64Verifier.Proofs.Multilinear.selectorPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Multilinear.selectorPoint

/-- info: 'Rv64Verifier.Proofs.Multilinear.eqAbove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Multilinear.eqAbove

/-- info: 'Rv64Verifier.Proofs.Multilinear.fromElem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Multilinear.fromElem

/-- info: 'Rv64Verifier.Proofs.Multilinear.powers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Multilinear.powers

/-- info: 'Rv64Verifier.Proofs.Multilinear.scalerNew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Multilinear.scalerNew

/-- info: 'Rv64Verifier.Proofs.Multilinear.clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Multilinear.clone

/-- info: 'Rv64Verifier.Proofs.Multilinear.specExtend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Multilinear.specExtend

/-- info: 'Rv64Verifier.Proofs.Multilinear.eqKernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Multilinear.eqKernel

/-- info: 'Rv64Verifier.Proofs.Multilinear.concat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Multilinear.concat

/-- info: 'Rv64Verifier.Proofs.Multilinear.sliceConcat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Multilinear.sliceConcat
