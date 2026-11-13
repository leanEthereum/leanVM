import LeanVM.Guest.B1.Whir.Config
import LeanVM.Guest.B1.Whir.Template

/-!
# The proofs' copies of the guest's constants

A template mirrors a guest constant where the compiler unrolls by it. Each copy equals the constant
`guest-export` writes from the guest (`Data.const_*`, `Guest/Data/Source.lean`), so a guest change that
moves one fails here, by name, before the templates it shapes fail their kernel checks.
-/

namespace LeanVMTests.Guest.Mirrors

open LeanVM.Guest LeanVM.Guest.B1.Whir

example : resBatch = Data.const_RES_BATCH := rfl
example : ligMaxLevels = Data.const_LIG_MAX_LEVELS := rfl
example : ligNSizes = Data.const_LIG_N_LOG_SIZES := rfl
example : ligNRates = Data.const_LIG_N_RATES := rfl
example : ligPosCap = Data.const_LIG_LEVEL_POSITIONS_CAP := rfl
example : ligColsCap = Data.const_LIG_LOG_MSG_COLS_CAP := rfl
example : yrLogCap = Data.const_YR_LOG_CAP := rfl
example : hsStride = 2 ^ Data.const_HIGH_BITS_CAP := rfl
example : queryGrind = Data.const_QUERY_GRIND_BITS := rfl
example : levelOodGrind = Data.const_OOD_GRIND_BITS := rfl

end LeanVMTests.Guest.Mirrors
