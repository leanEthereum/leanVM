import LeanVM.Parameters.PohligHellman

/-! **The kernel-checked Pohlig–Hellman constants read the field alone.** `PohligHellman` checks
nine exponentiations in the kernel; it imports `Statement.Field` and nothing of `lean_vm`, so
an edit of the discrete logarithm or its proofs (`Fast/DiscreteLog.lean`) rebuilds no check. This
module fails to build if its imports reach any other module of `lean_vm`. -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let reached := (← getEnv).header.moduleNames.filter fun m ↦
    (`LeanVM).isPrefixOf m && m != `LeanVM.Parameters.PohligHellman
  unless reached.isEmpty do
    throwError m!"the Pohlig–Hellman constants import {reached.toList}: keep them on the field \
      alone (see `LeanVM/Parameters/PohligHellmanFirewall.lean`)"
