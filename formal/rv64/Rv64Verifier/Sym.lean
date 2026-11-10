import Rv64Verifier.Sym.Api
import Rv64Verifier.Sym.Code

/-!
# A reflective symbolic executor for RV64IM straight-line code

Ported from sig.golf's `SigGolfCandidate.Rv`: `symRun` (`Sym/Exec.lean`) runs straight-line
code over symbolic expressions of the initial state, `symRun_sound` (`Sym/Sound.lean`) proves
that the machine of `Rv64Verifier/Machine.lean` follows it, and `BlockSpec.of_expect`
(`Sym/Api.lean`) turns one kernel-checked run into a block specification.
-/
