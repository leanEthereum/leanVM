module

public import NativeArm.Xmss
public import NativeArm.Sphincs
public import NativeArm.Vm

/-!
# The verifiers on AArch64

The end theorems: the machine code of each verifier, in any layout, returns `verifyWithKeccak` of
its input. The build fails if their axiom footprint grows beyond Lean's three standard axioms.

The leanVM verifier's (`NativeArm.VmVerifier.verify_correct_of`) still takes its seven phases'
contracts as hypotheses.
-/

/-- info: 'NativeArm.XmssVerifier.verify_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeArm.XmssVerifier.verify_correct

/-- info: 'NativeArm.SphincsVerifier.verify_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeArm.SphincsVerifier.verify_correct
