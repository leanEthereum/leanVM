module

public import NativeRustcVmX64.Arrays.MultilinearEvalByOfMultilinearEval.Spec
public import NativeRustcVmX64.Arrays.MultilinearEvalByOfComputedBytecodeValue.Spec

/-!
# `multilinear_eval_by` on x86-64

Both instances of `field.rs`'s `multilinear_eval_by` meet their contracts
(`NativeRustcVmX64.Spec.Arrays`) given `EW::mul`'s:
`Arrays.MleOfMultilinearEval.mleOfMultilinearEval_spec` (`multilinear_eval`'s closure) and
`Arrays.MleOfComputedBytecodeValue.mleOfComputedBytecodeValue_spec` (`computed_bytecode_value`'s).
Their shared frame, steps and loops: `Arrays/MultilinearEvalBy/*` (`MleFrame`). The build fails if
an axiom footprint grows beyond Lean's three standard axioms.
-/

/-- info: 'NativeRustcVmX64.Arrays.MleOfMultilinearEval.mleOfMultilinearEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Arrays.MleOfMultilinearEval.mleOfMultilinearEval_spec

/-- info: 'NativeRustcVmX64.Arrays.MleOfComputedBytecodeValue.mleOfComputedBytecodeValue_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Arrays.MleOfComputedBytecodeValue.mleOfComputedBytecodeValue_spec
