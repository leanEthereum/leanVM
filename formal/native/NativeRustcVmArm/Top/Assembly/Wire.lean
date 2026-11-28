module

public import NativeRustcVmArm.Code.Vm.ClimbLevel.Names
public import NativeRustcVmArm.Code.Vm.Decode.Names
public import NativeRustcVmArm.Code.Vm.Find.Names
public import NativeRustcVmArm.Code.Vm.InsD.Names
public import NativeRustcVmArm.Code.Vm.PhaseM.Names
public import NativeRustcVmArm.Code.Vm.RdRows.Names
public import NativeRustcVmArm.Code.Vm.ReaderDigest.Names
public import NativeRustcVmArm.Code.Vm.ReaderLe.Names
public import NativeRustcVmArm.Code.Vm.ReaderWords.Names
public import NativeRustcVmArm.Code.Vm.WriteOpenings.Names
public import NativeRustcVmArm.Top.Assembly.Base
public import NativeRustcVmArm.Wire.ReaderLe
public import NativeRustcVmArm.Wire.ReaderDigest
public import NativeRustcVmArm.Wire.ReaderWords
public import NativeRustcVmArm.Wire.InsD
public import NativeRustcVmArm.Wire.Find
public import NativeRustcVmArm.Wire.RdRows
public import NativeRustcVmArm.Wire.ClimbLevel
public import NativeRustcVmArm.Wire.PhaseM
public import NativeRustcVmArm.Wire.WriteOpenings
public import NativeRustcVmArm.Wire.Decode

/-!
# The wire decoder's functions, placed in `leanvm_verify`'s program

`Reader::{le, digest, words}`, `ins_d`, `find`, `rd_rows`, `climb_level`, instantiated at their
places in `Vm.code` with their callees' instantiated contracts.
-/

namespace NativeRustcVmArm.Assembly

open NativeRustcArm NativeRustcVmArm.Placement

public section

variable [NativeRustcArm.Host] (hP : NativeRustcArm.Host.prog = Vm.code)
include hP

theorem readerLe : Spec (label NativeRustcVmArm.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost :=
  Wire.ReaderLe.readerLe_spec (placed_ReaderLe hP)

theorem readerDigest : Spec (label NativeRustcVmArm.Vm.ReaderDigest.entryLabel) ReaderDigestPre ReaderDigestPost :=
  Wire.ReaderDigest.readerDigest_spec (placed_ReaderDigest hP) (readerLe hP)

theorem readerWords : Spec (label NativeRustcVmArm.Vm.ReaderWords.entryLabel) ReaderWordsPre ReaderWordsPost :=
  Wire.ReaderWords.readerWords_spec (placed_ReaderWords hP) (readerLe hP)

theorem insD : Spec (label NativeRustcVmArm.Vm.InsD.entryLabel) InsDPre InsDPost :=
  Wire.InsD.insD_spec (placed_InsD hP)

theorem find : Spec (label NativeRustcVmArm.Vm.Find.entryLabel) FindPre FindPost :=
  Wire.Find.find_spec (placed_Find hP)

theorem rdRows : Spec (label NativeRustcVmArm.Vm.RdRows.entryLabel) RdRowsPre RdRowsPost :=
  Wire.RdRows.rdRows_spec (placed_RdRows hP) (readerWords hP)

theorem climbLevel : Spec (label NativeRustcVmArm.Vm.ClimbLevel.entryLabel) ClimbLevelPre ClimbLevelPost :=
  Wire.ClimbLevel.climbLevel_spec (placed_ClimbLevel hP) (hashPair hP) (readerDigest hP)

theorem writeOpenings : Spec (label NativeRustcVmArm.Vm.WriteOpenings.entryLabel) WriteOpeningsPre WriteOpeningsPost :=
  Wire.WriteOpenings.writeOpenings_spec (placed_WriteOpenings hP) (find hP)

theorem phaseM : Spec (label NativeRustcVmArm.Vm.PhaseM.entryLabel) PhaseMPre PhaseMPost :=
  Wire.PhaseM.phaseM_spec (placed_PhaseM hP) (climbLevel hP) (insD hP) (keccak256WordsHash hP)
    (rdRows hP) (readerLe hP) (writeOpenings hP)

theorem decode : Spec (label NativeRustcVmArm.Vm.Decode.entryLabel) DecodePre DecodePost :=
  Wire.Decode.decode_spec (placed_Decode hP) (readerLe hP) (readerWords hP) (phaseM hP)

end

end NativeRustcVmArm.Assembly
