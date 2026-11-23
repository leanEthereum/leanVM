module

public import NativeRustcX64.SphincsVerify.Encode.Spec

/-!
# Region 5a's axioms

`encode_spec` depends on Lean's three axioms only.
-/

namespace NativeRustcX64.SphincsVerifyProof.EncodeTest

/-- info: 'NativeRustcX64.SphincsVerifyProof.encode_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NativeRustcX64.SphincsVerifyProof.encode_spec

end NativeRustcX64.SphincsVerifyProof.EncodeTest
