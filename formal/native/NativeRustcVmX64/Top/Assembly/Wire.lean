module

public import NativeRustcVmX64.Top.Assembly.Base
public import NativeRustcVmX64.Wire.ReaderLe
public import NativeRustcVmX64.Wire.ReaderDigest
public import NativeRustcVmX64.Wire.ReaderWords
public import NativeRustcVmX64.Wire.InsD
public import NativeRustcVmX64.Wire.Find
public import NativeRustcVmX64.Wire.WriteOpenings
public import NativeRustcVmX64.Wire.RdRows
public import NativeRustcVmX64.Wire.ClimbLevel
public import NativeRustcVmX64.Wire.PhaseM
public import NativeRustcVmX64.Wire.Decode
public import NativeRustcVmX64.Code.Vm.ClimbLevel.Names
public import NativeRustcVmX64.Code.Vm.Decode.Names
public import NativeRustcVmX64.Code.Vm.Find.Names
public import NativeRustcVmX64.Code.Vm.InsD.Names
public import NativeRustcVmX64.Code.Vm.PhaseM.Names
public import NativeRustcVmX64.Code.Vm.RdRows.Names
public import NativeRustcVmX64.Code.Vm.ReaderDigest.Names
public import NativeRustcVmX64.Code.Vm.ReaderLe.Names
public import NativeRustcVmX64.Code.Vm.ReaderWords.Names
public import NativeRustcVmX64.Code.Vm.WriteOpenings.Names

/-!
# The wire decoder's functions, placed in `leanvm_verify`'s program

`Reader::{le, digest, words}`, `ins_d`, `find` and `write_openings` proved so far, instantiated at
their places in `Vm.code` with their callees' instantiated contracts.
-/

namespace NativeRustcVmX64.Assembly

open NativeRustcX64 NativeRustcVmX64.Placement

public section

variable [Host] (hP : Host.prog = Vm.code)
include hP

theorem readerLe : Spec (label NativeRustcVmX64.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost :=
  Wire.ReaderLe.readerLe_spec (placed_ReaderLe hP)

theorem readerDigest : Spec (label NativeRustcVmX64.Vm.ReaderDigest.entryLabel) ReaderDigestPre ReaderDigestPost :=
  Wire.ReaderDigest.readerDigest_spec (placed_ReaderDigest hP) (readerLe hP)

theorem readerWords : Spec (label NativeRustcVmX64.Vm.ReaderWords.entryLabel) ReaderWordsPre ReaderWordsPost :=
  Wire.ReaderWords.readerWords_spec (placed_ReaderWords hP) (readerLe hP)

theorem insD : Spec (label NativeRustcVmX64.Vm.InsD.entryLabel) InsDPre InsDPost :=
  Wire.InsD.insD_spec (placed_InsD hP)

theorem find : Spec (label NativeRustcVmX64.Vm.Find.entryLabel) FindPre FindPost :=
  Wire.Find.find_spec (placed_Find hP)

theorem writeOpenings : Spec (label NativeRustcVmX64.Vm.WriteOpenings.entryLabel) WriteOpeningsPre WriteOpeningsPost :=
  Wire.WriteOpenings.writeOpenings_spec (placed_WriteOpenings hP) (find hP)

theorem rdRows : Spec (label NativeRustcVmX64.Vm.RdRows.entryLabel) RdRowsPre RdRowsPost :=
  Wire.RdRows.rdRows_spec (placed_RdRows hP) (readerWords hP)

theorem climbLevel : Spec (label NativeRustcVmX64.Vm.ClimbLevel.entryLabel) ClimbLevelPre ClimbLevelPost :=
  Wire.ClimbLevel.climbLevel_spec (placed_ClimbLevel hP) (hashPair hP) (readerDigest hP)

theorem phaseM : Spec (label NativeRustcVmX64.Vm.PhaseM.entryLabel) PhaseMPre PhaseMPost :=
  Wire.PhaseM.phaseM_spec (placed_PhaseM hP) (readerLe hP) (insD hP) (rdRows hP)
    (keccak256WordsHash hP) (climbLevel hP) (writeOpenings hP)

theorem decode : Spec (label NativeRustcVmX64.Vm.Decode.entryLabel) DecodePre DecodePost :=
  Wire.Decode.decode_spec (placed_Decode hP) (readerLe hP) (readerWords hP) (phaseM hP)

end

end NativeRustcVmX64.Assembly
