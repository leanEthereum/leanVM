module

public import NativeRustcArm.SphincsVerify.Encode.Spec

/-!
# Region 5a's axioms

`encode_spec` depends on Lean's three axioms only.
-/

namespace NativeRustcArm.SphincsVerifyProof.EncodeTest

/--
info: 'NativeRustcArm.SphincsVerifyProof.encode_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcArm.SphincsVerifyProof.encode_spec

end NativeRustcArm.SphincsVerifyProof.EncodeTest
