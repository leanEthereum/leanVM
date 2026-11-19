module

public import NativeArm.Xmss
public import NativeArm.Sphincs
public import NativeArm.Vm

/-!
# The verifiers on AArch64

The end theorems: the machine code of each verifier, in any layout, returns its statement's verdict
on its input (`verifyWithKeccak`; for leanVM, `verifyWith` of the decoded wire bytes). The build
fails if their axiom footprint grows beyond Lean's three standard axioms.
-/

/-- info: 'NativeArm.XmssVerifier.verify_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeArm.XmssVerifier.verify_correct

/-- info: 'NativeArm.SphincsVerifier.verify_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeArm.SphincsVerifier.verify_correct

/-- info: 'NativeArm.VmVerifier.verify_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeArm.VmVerifier.verify_correct
