import FORS.Certificates.H26

/-! **Proof of the proved lifetime**: `ForsPotential.det_bitsFH` applied to the configuration's
certificates (`Certificates/H26.lean`). `Main.lean` states it again, independently of this file, and
proves it with the theorem here. Small budgets use the linear potential, the one-coin cover potential
at baseline `ρ / 2^128` and the contact bound A4 of the FORS leaves; large budgets use the one-coin
covers at the survival-weighted baseline. -/

namespace FORS.Lifetimes

open Security ForsPotential

/-- Height 26, layered (10 + 8 + 8), 1,182,000,000 signatures (98.2% of the cover attack's 1.203e+09). -/
theorem h26_layered_bits : SecurityBits (.layered 26 3 8 24 10 1182000000) 127 :=
  @det_bitsFH (.layered 26 3 8 24 10 1182000000) (by decide) 26 26 24 10 264193 1182000000
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 512487451133699472151040029945233408
    H0.rho_h26_b26 H0.tab_h26_b26 H0.small_h26_b26 H0.near_h26_b26 H0.tab_h26_b26_ok H0.rate_h26_b26_ok H0.small_h26_b26_ok
    H0.near_h26_b26_ok H0.check_h26_b26_ok [H0.cover_h26_b26_0] [] H0.covers_h26_L_ok

end FORS.Lifetimes
