module

public import NativeRustcX64.Rodata.Names

public import NativeRustcX64.Data
public import NativeRustcX64.Code.Xmss
public import NativeRustcX64.Code.Sphincs
public import NativeRustcX64.Spec.Keccak
public import NativeRustcX64.SphincsVerify.Basic

/-!
# The read-only data the signature verifiers' end theorems assume

`XmssVerifier.verify_correct` assumes the round constants `rcBytes` at `NativeRustcX64.roundConstantsLabel` (`RcAt`), and
`SphincsVerifier.verify_correct` those and `LAYER_HEIGHTS`' `lhBytes` at `NativeRustcX64.layerHeightsLabel`. These are the
bytes the ingested programs' data hold at those labels, so a loader placing the program's data
there meets those assumptions. The separate `GotAt` loader hypothesis supplies the reached
symbols' addresses in ordinary-memory GOT slots, disjoint from one another, the stack and the
protected areas; these dynamically relocated slots are not part of the static data below.
-/

namespace NativeRustcX64

set_option Elab.async false

public theorem Xmss.rc_data : dataAt NativeRustcX64.roundConstantsLabel Xmss.rodata = some rcBytes := by
  decide +kernel

public theorem Sphincs.rc_data : dataAt NativeRustcX64.roundConstantsLabel Sphincs.rodata = some rcBytes := by
  decide +kernel

public theorem Sphincs.lh_data :
    dataAt NativeRustcX64.layerHeightsLabel Sphincs.rodata = some SphincsVerifyProof.lhBytes := by
  decide +kernel

end NativeRustcX64
