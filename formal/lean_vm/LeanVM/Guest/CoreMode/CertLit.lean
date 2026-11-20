/-
  LeanVM.Guest.CoreMode.CertLit

  `core_cert%`, `cert_in%` and `sig_in%`: the declarations `scripts/core-mode/certs.py` writes for
  each routed function, written once here so that the generated modules state them in one line.
-/

module

public meta import Lean.Elab.Command
public import LeanVM.Guest.KernelLit
public import LeanVM.Guest.CoreMode.ListLit

/-!
# A routed function's certificate in one line

`core_cert% «k» «p» i [«m₀», …]` (`nz` before the list when its residuals are its walk's) is

* `noncomputable def «k».modeCert : Mode.Cert := ⟨envC, funC, code.chunks.flatten⟩`;
* `kernel_rfl «k».modeSigs : «k».modeCert.E.sigs = CoreMode.sigTrie [«m₀».csig, …]`;
* `noncomputable def «k».ce`, the certificate with its facts (`EndExec.CertE`), its core data the
  `i`-th of pack `p`'s.

`cert_in% «k» j i` is `theorem «k».modeCert_in`: the certificate is the `i`-th of the `j`-th pack's
among `CoreMode.coreCerts`. `sig_in% «k»` is `⟨_, Fn.«k».modeCert_in, rfl, rfl, rfl⟩`: a
callee's signature is a certificate's among them. Unhygienic: each expands to the text the generator
wrote before, its names resolved where it is written, so its elaboration is the same.
-/

public section

open Lean in
/-- `k`'s declaration named `k.s`. -/
meta def LeanVM.Guest.CertLit.dot (k : TSyntax `ident) (s : Name) : TSyntax `ident :=
  mkIdent (k.getId ++ s)

open LeanVM.Guest.CertLit in
set_option hygiene false in
/-- `core_cert% «k» «p» i [nz] [«m₀», …]`: `k`'s certificate, its callees' signatures and its facts. -/
macro "core_cert% " k:ident p:ident i:num nz:("nz")? "[" ms:ident,* "]" : command => do
  let sigs := ms.getElems.map (dot · `csig)
  let ok := Lean.mkIdent (`ModePack ++ p.getId ++ `coreFns_ok)
  let nzT ← if nz.isSome then `(nzOnly_of (j := idx) (by decide +kernel)) else `(nzOnly_nil rfl)
  `(noncomputable def $(dot k `modeCert) : Mode.Cert := ⟨envC, funC, code.chunks.flatten⟩
    kernel_rfl $(dot k `modeSigs) : $(dot k `modeCert).E.sigs = CoreMode.sigTrie [$sigs,*]
    noncomputable def $(dot k `ce) : EndExec.CertE CoreMode.hcTab CoreMode.coreNzs :=
      ⟨modeCert, cfun, $ok _ (list_mem% $i), ⟨by decide +kernel, rfl, rfl⟩, rfl, fnSpecC, by decide +kernel,
        Mode.fnLink_of code_mem rfl rfl rfl, termOk_of (j := idx) (by decide +kernel), $nzT⟩)

open LeanVM.Guest.CertLit in
set_option hygiene false in
/-- `cert_in% «k» j i`: `k`'s certificate is among the core route's. -/
macro "cert_in% " k:ident j:num i:num : command =>
  `(theorem $(dot k `modeCert_in) : $(dot k `modeCert) ∈ CoreMode.coreCerts :=
      EndExec.CertE.mem (ls := CoreMode.corePacks) $(dot k `ce) (list_mem% $j) (list_mem% $i))

set_option hygiene false in
/-- `sig_in% «k»`: `k`'s signature is a certificate's among the core route's. -/
macro "sig_in% " k:ident : term =>
  `(⟨_, $(Lean.mkIdent (`Fn ++ k.getId ++ `modeCert_in)), rfl, rfl, rfl⟩)

end
