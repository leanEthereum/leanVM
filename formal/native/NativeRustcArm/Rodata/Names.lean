module

public import NativeRustcArm.Code.Xmss.Names
public import NativeRustcArm.Code.Sphincs.Names

namespace NativeRustcArm

/-- The Keccak round constants, identified by `Xmss.rc_data` and `Sphincs.rc_data`. -/
@[expose] public def roundConstantsLabel : String := Xmss.Symbols.rodata0Label

/-- The layer heights, identified by `Sphincs.lh_data`. -/
@[expose] public def layerHeightsLabel : String := Sphincs.Symbols.rodata7Label

end NativeRustcArm
