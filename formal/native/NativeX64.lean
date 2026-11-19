module

public import NativeX64.Xmss
public import NativeX64.Sphincs
public import NativeX64.Vm

/-!
# The verifiers on x86-64

The end theorems: the machine code of each verifier, in any layout, returns `verifyWithKeccak` of
its input. The build fails if their axiom footprint grows beyond Lean's three standard axioms.

The leanVM verifier's (`NativeX64.VmVerifier.verify_correct_of`) still takes its seven phases'
contracts as hypotheses.
-/

/-- info: 'NativeX64.XmssVerifier.verify_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeX64.XmssVerifier.verify_correct

/-- info: 'NativeX64.SphincsVerifier.verify_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeX64.SphincsVerifier.verify_correct
