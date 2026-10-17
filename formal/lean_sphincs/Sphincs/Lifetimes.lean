import Sphincs.LifetimeCertificates

/-! **Proved lifetimes of the forest variant** for the deterministic signer (seed-derived
randomizers): 127 classical bits against any adversary. Small budgets use the linear potential, the
one-coin cover potential at baseline `ρ / 2^128` and the contact bound A4 of the forest; large
budgets use the one-coin covers at the survival-weighted baseline. Every lifetime is at least the
proved lifetime of the FORS variant (`LeanSphincs.Lifetimes.requestedSecurity` in
leanXMSS-leanSPHINCS-candidates). -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Lifetimes

open Security ForsPotential

/-- Subtree height 26, 1383000000 signatures (96.1% of the cover attack's 1.44e+09; the FORS variant: 1156000000). -/
abbrev full : Params := ⟨26, 1383000000, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 26 and 1383000000 signatures. -/
theorem full_bits : @Det.HasClassicalSecurityBitsDet full 127 :=
  @det_bitsFH full (by decide) 26 1383000000 rfl rfl 250752950924986904089568310569467904 H0.rho_b26 H0.tab_b26 H0.small_b26 H0.near_b26 H0.tab_b26_ok
    H0.rate_b26_ok H0.small_b26_ok H0.near_b26_ok H0.check_b26_ok [H0.cover_b26_0] [] H0.covers_b26_ok

/-- Subtree height 20, 26030000 signatures (91.3% of the cover attack's 2.851e+07; the FORS variant: 22380000). -/
abbrev pruned20 : Params := ⟨20, 26030000, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 20 and 26030000 signatures. -/
theorem pruned20_bits : @Det.HasClassicalSecurityBitsDet pruned20 127 :=
  @det_bitsFH pruned20 (by decide) 20 26030000 rfl rfl 558871528355207643822193711415033856 H0.rho_b20 H0.tab_b20 H0.small_b20 H0.near_b20 H0.tab_b20_ok
    H0.rate_b20_ok H0.small_b20_ok H0.near_b20_ok H0.check_b20_ok [H0.cover_b20_0, H0.cover_b20_1] [H0.coverh_b20_0] H0.covers_b20_ok

/-- Subtree height 14, 480900 signatures (86.3% of the cover attack's 5.575e+05; the FORS variant: 412500). -/
abbrev pruned14 : Params := ⟨14, 480900, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 14 and 480900 signatures. -/
theorem pruned14_bits : @Det.HasClassicalSecurityBitsDet pruned14 127 :=
  @det_bitsFH pruned14 (by decide) 14 480900 rfl rfl 1179940068462340716375613534384422912 H0.rho_b14 H0.tab_b14 H0.small_b14 H0.near_b14 H0.tab_b14_ok
    H0.rate_b14_ok H0.small_b14_ok H0.near_b14_ok H0.check_b14_ok [H0.cover_b14_0, H0.cover_b14_1] [H0.coverh_b14_0] H0.covers_b14_ok

/-- Subtree height 13, 247000 signatures (85.5% of the cover attack's 2.89e+05; the FORS variant: 211900). -/
abbrev pruned13 : Params := ⟨13, 247000, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 13 and 247000 signatures. -/
theorem pruned13_bits : @Det.HasClassicalSecurityBitsDet pruned13 127 :=
  @det_bitsFH pruned13 (by decide) 13 247000 rfl rfl 1314909569352122321482228451418046464 H0.rho_b13 H0.tab_b13 H0.small_b13 H0.near_b13 H0.tab_b13_ok
    H0.rate_b13_ok H0.small_b13_ok H0.near_b13_ok H0.check_b13_ok [H0.cover_b13_0, H0.cover_b13_1] [H0.coverh_b13_0] H0.covers_b13_ok

/-- Subtree height 12, 126900 signatures (84.7% of the cover attack's 1.498e+05; the FORS variant: 108700). -/
abbrev pruned12 : Params := ⟨12, 126900, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 12 and 126900 signatures. -/
theorem pruned12_bits : @Det.HasClassicalSecurityBitsDet pruned12 127 :=
  @det_bitsFH pruned12 (by decide) 12 126900 rfl rfl 1449533407878593313898110627080044544 H0.rho_b12 H0.tab_b12 H0.small_b12 H0.near_b12 H0.tab_b12_ok
    H0.rate_b12_ok H0.small_b12_ok H0.near_b12_ok H0.check_b12_ok [H0.cover_b12_0, H0.cover_b12_1] [H0.coverh_b12_0] H0.covers_b12_ok

/-- Subtree height 10, 33490 signatures (83.3% of the cover attack's 4.022e+04; the FORS variant: 28600). -/
abbrev pruned10 : Params := ⟨10, 33490, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 10 and 33490 signatures. -/
theorem pruned10_bits : @Det.HasClassicalSecurityBitsDet pruned10 127 :=
  @det_bitsFH pruned10 (by decide) 10 33490 rfl rfl 1742566343746827758207774509045383168 H0.rho_b10 H0.tab_b10 H0.small_b10 H0.near_b10 H0.tab_b10_ok
    H0.rate_b10_ok H0.small_b10_ok H0.near_b10_ok H0.check_b10_ok [H0.cover_b10_0, H0.cover_b10_1] [H0.coverh_b10_0] H0.covers_b10_ok

/-- Subtree height 8, 8830 signatures (81.9% of the cover attack's 1.078e+04; the FORS variant: 7530). -/
abbrev pruned8 : Params := ⟨8, 8830, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 8 and 8830 signatures. -/
theorem pruned8_bits : @Det.HasClassicalSecurityBitsDet pruned8 127 :=
  @det_bitsFH pruned8 (by decide) 8 8830 rfl rfl 2027867772287336761555281578532274176 H0.rho_b8 H0.tab_b8 H0.small_b8 H0.near_b8 H0.tab_b8_ok
    H0.rate_b8_ok H0.small_b8_ok H0.near_b8_ok H0.check_b8_ok [H0.cover_b8_0, H0.cover_b8_1] [H0.coverh_b8_0] H0.covers_b8_ok

/-- **The forest lifetimes**: 127 bits at every subtree height. -/
theorem requestedSecurity :
    @Det.HasClassicalSecurityBitsDet full 127 ∧
    @Det.HasClassicalSecurityBitsDet pruned20 127 ∧
    @Det.HasClassicalSecurityBitsDet pruned14 127 ∧
    @Det.HasClassicalSecurityBitsDet pruned13 127 ∧
    @Det.HasClassicalSecurityBitsDet pruned12 127 ∧
    @Det.HasClassicalSecurityBitsDet pruned10 127 ∧
    @Det.HasClassicalSecurityBitsDet pruned8 127 :=
  ⟨full_bits, pruned20_bits, pruned14_bits, pruned13_bits, pruned12_bits, pruned10_bits, pruned8_bits⟩

end Sphincs.Lifetimes
