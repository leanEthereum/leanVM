import LeanVM.Guest.B2C.Cpl
import LeanVM.Guest.B2C.ShareStatic
import LeanVM.Guest.CheckWinC
import LeanVM.Guest.Memory.StaticSplit

/-! **The guest's certificates do not read the verifier's statement.** The certificates of
`B2C/Cplw`, `B2C/Shared`, `Checked` and the memory layer (`Memory/GuestCnt*`), about 8.5 CPU-h of
kernel evaluation, read the guest's code, the ISA and the field (`Statement.Field`, with `eOfNat`
and `gen`; the field's bit facts in `Value/FieldBits.lean`), not the verifier
(`Statement.LeanVmVerifier`), so that an edit of the verifier's statement rebuilds none of them
(`CertFirewall.lean` guards the rest of their imports). This module, which imports their four
bases, fails to build if their imports reach the verifier or `Value.Tower`. -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let forbidden := [`Statement.LeanVmVerifier, `LeanVM.Guest.Value.Tower]
  let reached := (← getEnv).header.moduleNames.filter fun m ↦ forbidden.any (·.isPrefixOf m)
  unless reached.isEmpty do
    throwError m!"the guest's certificates import {reached.toList}: keep the \
      functions they evaluate in modules that do not (see \
      `LeanVM/Guest/B2C/CertFirewallVerifier.lean`)"
