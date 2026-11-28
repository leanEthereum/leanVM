/-
  LeanVM.Guest.CoreMode.CertLit

  `core_cert%`, `cert_in%`, `sig_in%` and `off_in%`: the declarations `scripts/core-mode/certs.py`
  writes for each routed function, written once here so that the generated modules state them in
  one line.
-/

module

public meta import Lean.Elab.Command
public import LeanVM.Guest.KernelLit
public import LeanVM.Guest.CoreMode.ListLit

/-!
# A routed function's certificate in one line

`core_cert% «k» [«m₀», …]` is

* `noncomputable def «k».modeCert : Mode.Cert := ⟨envC, funC, code.chunks.flatten⟩`;
* `kernel_rfl «k».modeSigs : «k».modeCert.E.sigs = CoreMode.sigTrie [«m₀».csig, …]`;
* `noncomputable def «k».ce`, the certificate with its facts (`EndExec.CertE`), its termination
  facts and its residuals decided at its compiled index `«k».idx` (`EndExec.termOk_of`,
  `Res.nzOnly_of`).

`cert_in% «k» j i` is `theorem «k».modeCert_in`: for any certificates of the functions off the
route, the certificate is the `i`-th of the `j`-th pack's among `EndExec.certsOf`. In a term,
`sig_in% «k»` is a routed callee's signature among them, `off_in% c j` an off function's (from the
hypothesis `hoff`), the `j`-th of the off functions' `c`-th chunk. Unhygienic: each expands to
text whose names resolve where it is written.
-/

public section

open Lean in
/-- `k`'s declaration named `k.s`. -/
meta def LeanVM.Guest.CertLit.dot (k : TSyntax `ident) (s : Name) : TSyntax `ident :=
  mkIdent (k.getId ++ s)

open LeanVM.Guest.CertLit in
set_option hygiene false in
/-- `core_cert% «k» [«m₀», …]`: `k`'s certificate, its callees' signatures and its facts. -/
macro "core_cert% " k:ident "[" ms:ident,* "]" : command => do
  let sigs := ms.getElems.map (dot · `csig)
  `(noncomputable def $(dot k `modeCert) : Mode.Cert := ⟨envC, funC, code.chunks.flatten⟩
    kernel_rfl $(dot k `modeSigs) : $(dot k `modeCert).E.sigs = CoreMode.sigTrie [$sigs,*]
    noncomputable def $(dot k `ce) : EndExec.CertE CoreMode.hcTab :=
      ⟨modeCert, cfun, ⟨by decide +kernel, rfl, rfl⟩, rfl, fnSpecC, by decide +kernel,
        Mode.fnLink_of code_mem rfl rfl rfl, termOk_of (j := idx) (by decide +kernel),
        Res.nzOnly_of (j := idx) (by decide +kernel)⟩)

open LeanVM.Guest.CertLit in
set_option hygiene false in
/-- `cert_in% «k» j i`: `k`'s certificate is among the core route's. -/
macro "cert_in% " k:ident j:num i:num : command =>
  `(theorem $(dot k `modeCert_in) (offK : Mode.Sig → Mode.Cert) :
      $(dot k `modeCert) ∈ EndExec.certsOf CoreMode.corePacks CoreMode.offSigs offK :=
    EndExec.CertE.mem $(dot k `ce) (list_mem% $j) (list_mem% $i))

set_option hygiene false in
/-- `sig_in% «k»`: a routed callee's signature is a certificate's. -/
macro "sig_in% " k:ident : term =>
  `(⟨_, $(Lean.mkIdent (`Fn ++ k.getId ++ `modeCert_in)) offK, rfl, rfl, rfl⟩)

set_option hygiene false in
/-- `off_in% c j`: the `j`-th signature of the `c`-th chunk of the off functions' (`offSigs`, the
chunks appended, then `[]`) is a certificate's, by `hoff`. -/
macro "off_in% " c:num j:num : term => do
  let mut t ← `(List.mem_append_left _ (list_mem% $j))
  for _ in [0:c.getNat] do t ← `(List.mem_append_right _ $t)
  `(EndExec.sigIn_off hoff $t)

end
