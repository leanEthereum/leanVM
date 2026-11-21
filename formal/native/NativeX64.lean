module

public import NativeX64.Xmss
public import NativeX64.Sphincs
public import NativeX64.Vm

/-!
# The verifiers on x86-64

The end theorems: the machine code of each verifier, in any layout, returns its statement's verdict
on its input (`verifyWithKeccak`; for leanVM, `verifyWith` of the decoded wire bytes). The build
fails if their axiom footprint grows beyond Lean's three standard axioms.
-/

/-- info: 'NativeX64.XmssVerifier.verify_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeX64.XmssVerifier.verify_correct

/-- info: 'NativeX64.SphincsVerifier.verify_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeX64.SphincsVerifier.verify_correct

/-- info: 'NativeX64.VmVerifier.verify_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeX64.VmVerifier.verify_correct
