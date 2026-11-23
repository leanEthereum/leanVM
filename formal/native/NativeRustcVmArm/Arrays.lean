module

public import NativeRustcVmArm.Arrays.Dot
public import NativeRustcVmArm.Arrays.EqEval
public import NativeRustcVmArm.Arrays.EqKernel
public import NativeRustcVmArm.Arrays.EqEvalFn
public import NativeRustcVmArm.Arrays.PolyEval
public import NativeRustcVmArm.Arrays.IndexMleFrom
public import NativeRustcVmArm.Arrays.PaddingWeight
public import NativeRustcVmArm.Arrays.Powers
public import NativeRustcVmArm.Arrays.ProdE
public import NativeRustcVmArm.Arrays.SumE
public import NativeRustcVmArm.Arrays.SelectorPoint
public import NativeRustcVmArm.Arrays.BufEW30Extend
public import NativeRustcVmArm.Arrays.BufEW36Extend
public import NativeRustcVmArm.Arrays.BufEW63Extend
public import NativeRustcVmArm.Arrays.BufEW230Extend
public import NativeRustcVmArm.Arrays.BufU64x230Extend
public import NativeRustcVmArm.Arrays.MultilinearEvalByOfMultilinearEval
public import NativeRustcVmArm.Arrays.MultilinearEvalByOfComputedBytecodeValue

/-!
# `field.rs`'s array functions and `Buf::extend` on AArch64

The contracts (`NativeRustcVmArm.Spec.Arrays`) met, each given `EW::mul`'s contract where it calls
it; their axioms checked below.
-/

/-- info: 'NativeRustcVmArm.Arrays.Dot.dot_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Arrays.Dot.dot_spec

/-- info: 'NativeRustcVmArm.Arrays.EqEval.eqEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Arrays.EqEval.eqEval_spec

/-- info: 'NativeRustcVmArm.Arrays.EqEvalFn.eqEvalFn_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Arrays.EqEvalFn.eqEvalFn_spec

/-- info: 'NativeRustcVmArm.Arrays.PolyEval.polyEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Arrays.PolyEval.polyEval_spec

/-- info: 'NativeRustcVmArm.Arrays.IndexMleFrom.indexMleFrom_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Arrays.IndexMleFrom.indexMleFrom_spec

/-- info: 'NativeRustcVmArm.Arrays.PaddingWeight.paddingWeight_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Arrays.PaddingWeight.paddingWeight_spec

/-- info: 'NativeRustcVmArm.Arrays.Powers.powers_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Arrays.Powers.powers_spec

/-- info: 'NativeRustcVmArm.Arrays.ProdE.prodE_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Arrays.ProdE.prodE_spec

/-- info: 'NativeRustcVmArm.Arrays.SumE.sumE_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Arrays.SumE.sumE_spec

/-- info: 'NativeRustcVmArm.Arrays.BufEW30Extend.bufEW30Extend_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Arrays.BufEW30Extend.bufEW30Extend_spec

/-- info: 'NativeRustcVmArm.Arrays.BufEW36Extend.bufEW36Extend_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Arrays.BufEW36Extend.bufEW36Extend_spec

/-- info: 'NativeRustcVmArm.Arrays.BufEW63Extend.bufEW63Extend_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Arrays.BufEW63Extend.bufEW63Extend_spec

/-- info: 'NativeRustcVmArm.Arrays.BufEW230Extend.bufEW230Extend_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Arrays.BufEW230Extend.bufEW230Extend_spec

/-- info: 'NativeRustcVmArm.Arrays.BufU64x230Extend.bufU64x230Extend_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Arrays.BufU64x230Extend.bufU64x230Extend_spec

/-- info: 'NativeRustcVmArm.Arrays.SelectorPoint.selectorPoint_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Arrays.SelectorPoint.selectorPoint_spec

/-- info: 'NativeRustcVmArm.Arrays.EqKernel.eqKernel_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Arrays.EqKernel.eqKernel_spec

/-- info: 'NativeRustcVmArm.Arrays.MleOfMultilinearEval.mleOfMultilinearEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Arrays.MleOfMultilinearEval.mleOfMultilinearEval_spec

/-- info: 'NativeRustcVmArm.Arrays.MleOfComputedBytecodeValue.mleOfComputedBytecodeValue_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Arrays.MleOfComputedBytecodeValue.mleOfComputedBytecodeValue_spec
