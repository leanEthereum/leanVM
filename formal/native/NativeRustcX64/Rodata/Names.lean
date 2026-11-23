module

public import NativeRustcX64.Code.Xmss.Names
public import NativeRustcX64.Code.Sphincs.Names

namespace NativeRustcX64

/-- The Keccak round constants, identified by `Xmss.rc_data` and `Sphincs.rc_data`. -/
@[expose] public def roundConstantsLabel : String := Xmss.Symbols.rodata0Label

/-- The layer heights, identified by `Sphincs.lh_data`. -/
@[expose] public def layerHeightsLabel : String := Sphincs.Symbols.rodata1Label

end NativeRustcX64
