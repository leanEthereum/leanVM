module

public import NativeRustcArm.Rodata.Names

public import NativeRustcArm.Data
public import NativeRustcArm.Code.Sphincs
public import NativeRustcArm.Spec.Keccak
public import NativeRustcArm.SphincsVerify.Basic

/-!
# The read-only data the leanSPHINCS verifier's end theorems assume

`SphincsVerifier.verify_correct` assumes the round constants `rcBytes` at
`NativeRustcArm.roundConstantsLabel` (`RcAt`) and `LAYER_HEIGHTS`' `lhBytes` at
`NativeRustcArm.layerHeightsLabel`. These are the bytes the ingested program's data hold at those
labels, so a loader placing the program's data there meets the assumption.
-/

namespace NativeRustcArm

set_option Elab.async false

public theorem Sphincs.rc_data : dataAt NativeRustcArm.roundConstantsLabel Sphincs.rodata = some rcBytes := by
  decide +kernel

public theorem Sphincs.lh_data :
    dataAt NativeRustcArm.layerHeightsLabel Sphincs.rodata = some SphincsVerifyProof.lhBytes := by
  decide +kernel

end NativeRustcArm
