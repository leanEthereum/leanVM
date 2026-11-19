/-
  LeanVM.Guest.Res.Off

  What the functions off the core route give of the end theorem's assembly (`EndExec.OffFacts`):
  the mode walk's certificates, their residuals and termination facts.
-/

module

public import LeanVM.Guest.Mode.Certs
public import LeanVM.Guest.Res.SubCerts
public import LeanVM.Guest.Res.TermCerts
public import LeanVM.Guest.CoreMode.Gen.Certs

/-!
# The functions off the core route

`Mode.offCerts` are the certificates of the functions the core route does not check: the mode
walk's (`scripts/mode-cert/gen.py`), their residuals by family (`Res/SubCerts`, given the listed
certificates' `resExc`) and termination facts (`Res/TermCerts`). With none left, `OffFacts.nil`
replaces `offFacts` and this module, the mode walk's certificates and the residual families go.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Guest LeanVM.Guest.Res

public section

/-- **What the functions off the core route give**, given the frame interfaces the kernel does not check and the
listed certificates' residuals. -/
theorem offFacts {A : String → Bridge.FnAl} (h : Mode.ModeHyps) (hexc : ∀ K ∈ resExc, ResCert A K) :
    OffFacts CoreMode.hcTab CoreMode.coreCerts Mode.offCerts CoreMode.coreTable CoreMode.offSigs A where
  st := Mode.offCerts_st
  spec := Mode.offCerts_spec h
  fn := Mode.offCerts_fn
  sigs := Mode.offCerts_sigs
  off := Mode.offSigs_in
  nodup := Mode.offCerts_nodup
  res := resTop_guestF hexc
  term := termNode_guest

end

end LeanVM.Guest.EndExec
