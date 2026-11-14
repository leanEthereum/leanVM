module

public import LeanVM.Guest.Mode.CertDefs
public import LeanVM.Guest.Mode.ResInst

/-!
# Nonzero residuals from a frame's constants

`NzStatOk K`: `K` is function `j`'s certificate (its entry `fnOf j`'s), and each nonzero residual's
product cell is a fixed nonzero constant of `j`'s frame (`nzStat`, which `num_stat` reads on the
reference). Generated per certificate where it holds (`Mode/Certs/Sig*.lean`, `modeNzStat`).
-/

namespace LeanVM.Guest.Mode

open LeanVM.Guest LeanVM.Guest.B2C

@[expose] public section

/-- **`K` is function `j`'s, its nonzero residuals' products fixed nonzero constants.** -/
def NzStatOk (K : Cert) : Prop :=
  ∃ j < nFns, (fnOf j).entryPc = K.F.entry ∧ nzStat (plumbOf j).stat (fsN j) K.F K.code = true

end

end LeanVM.Guest.Mode
