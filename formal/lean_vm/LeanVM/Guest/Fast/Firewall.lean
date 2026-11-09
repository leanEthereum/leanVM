import LeanVM.Guest.Fast.GLanesCheck
import LeanVM.Guest.Fast.XmssTablesCheck
import LeanVM.Guest.Fast.SpWotsTablesCheck
import LeanVM.Guest.Fast.WhirTablesCheck
import LeanVM.Guest.Fast.PreTable

/-! **The kernel-checked tables of the decoder's readers read the templates alone.** The checks
of `Fast/*TablesCheck.lean` evaluate the template generators in the kernel (`WhirTablesCheck` most
of a minute), and a module is rebuilt whenever what a module it imports exports changes. So they
import the literal tables, the numbers they are checked against (`Fast/Numbers.lean`), the
templates (`B1/Sig/XmssT`, `B1/Sig/SpWotsT` with its layout `SpWotsLayout`, which reads the arms'
starts off the shared codeword's `WotsSound`, `B1/Whir/InterfaceW`), the functions' names
(`Fast/FunctionNames`, over `Guest/NameIndex`) and their preconditions (`Fast/PreTable`, over
`Fast/PreSig` and the certificates' data), not the readers (`Fast/Xmss`, `Sphincs`, `Whir`) or the
precondition's test (`Fast/PreTest`), the lemmas proving the numbers equal to the generators
(`Fast/Wots`, `SpWots`, `LogG`), the certificates and the checker (`CertName`, `CheckSound`), the
replay (`Located/`), the schemes' soundness, `verify_sub`'s, `main`'s, the cost compiler or the
statement's end: an edit there rebuilds no table. This module, which imports the five checks, fails
to build if their imports reach any of those. -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let forbidden := [`LeanVM.Guest.Fast.Xmss, `LeanVM.Guest.Fast.Sphincs, `LeanVM.Guest.Fast.Whir,
    `LeanVM.Guest.Fast.Wots, `LeanVM.Guest.Fast.SpWots, `LeanVM.Guest.Fast.LogG,
    `LeanVM.Guest.Fast.Common, `LeanVM.Guest.Fast.PreTest, `LeanVM.Guest.CertName,
    `LeanVM.Guest.CheckSound,
    `LeanVM.Guest.Located, `LeanVM.Guest.B1.Sig.XmssSegSound, `LeanVM.Guest.B1.Sig.XmssLoop2,
    `LeanVM.Guest.B1.Sig.SphincsSound,
    `LeanVM.Guest.B1.VerifySub, `LeanVM.Guest.B1.Main.SoundV, `LeanVM.Guest.B1.Main.Interface,
    `LeanVM.Cost, `LeanVM.Guest.End, `LeanVM.Guest.EndFinal, `Statement.Theorems,
    `Statement.Corollaries]
  let reached := (← getEnv).header.moduleNames.filter fun m ↦ forbidden.any (·.isPrefixOf m)
  unless reached.isEmpty do
    throwError m!"the decoder's table checks import {reached.toList}: keep the functions they \
      evaluate in modules that do not (see `LeanVM/Guest/Fast/Firewall.lean`)"
