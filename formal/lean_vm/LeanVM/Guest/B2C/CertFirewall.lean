import LeanVM.Guest.B2C.Cpl
import LeanVM.Guest.B2C.ShareStatic
import LeanVM.Guest.CheckWinC
import LeanVM.Guest.Memory.Family

/-! **The kernel-checked certificates of the guest program read its code and the checks alone.**
The generated certificates (`B2C/Cplw`, `B2C/Shared`, `Checked`, `Memory/GuestCnt`) are most of
`lean_vm`'s kernel evaluation, and a module is rebuilt whenever what a module it
imports exports changes. Each imports its family's base (`B2C.Cpl`, `B2C.ShareStatic`,
`CheckWinC`, `Memory.Family`), and those import the guest program's code, its compiled form
and the functions the checks evaluate (of the statement: the ISA, the field, the verifier's
definitions and the bytecode), not the guest's statement, the program logic, B1's proofs, the
protocol's, the verifier's facts, the schemes, LeanDA or `common`: an edit there rebuilds no
certificate. This module, which imports the
four bases, fails to build if their imports reach any of those. -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let forbidden := [`LeanVM.Guest.B1, `LeanVM.Protocol, `LeanVM.Facts.Verifier, `LeanVM.Guest.Logic,
    `LeanVM.Guest.Bytecode, `LeanXmss, `Sphincs, `LeanDa, `Common, `Statement.LeanVm,
    `Statement.LeanVmGuest, `Statement.Prover, `Statement.LeanXmss,
    `Statement.LeanSphincs, `Statement.LeanDa, `Statement.Fast.Schemes, `Statement.CostMachine,
    `Statement.Theorems, `Statement.Corollaries]
  let reached := (← getEnv).header.moduleNames.filter fun m ↦ forbidden.any (·.isPrefixOf m)
  unless reached.isEmpty do
    throwError m!"the guest's certificates import {reached.toList}: keep the functions they \
      evaluate in modules that do not (see `LeanVM/Guest/B2C/CertFirewall.lean`)"
