module

public import Quantum.Sphincs.Assembly.ChgRevStatic
public import Quantum.Sphincs.Assembly.HmsgCoversMass
public import Quantum.Sphincs.Hybrid.Masked

@[expose] public section

/-!
# leanSPHINCS's good tables

The masked hybrid (`Quantum.Sphincs.Hybrid.Masked`) masks the masses by ReparamFull's good set
`FullG (SrcS S₀)` and pays its bad fraction `stageFrac (SrcS S₀)` once, for a static condition
`S₀` on the template data `(p, v)`.

* **The static condition of the masses** (`SphStatic`): HmsgCovers' `HStatic` (HmsgCoversMass'
  `hSt`), `TrialsOff` (`hOff`) and ChgRevStatic's `ChgStatic` (the digest blocks' capacities) at
  the template data. GoodES's conditions stay on the event side.
* **The bad fraction** (`stageFrac_sphStatic_le`): `stageFrac (SrcS SphStatic) ≤ 2^-197 + 2^-400 +
  2^-277 + staticFrac` (MassSources' `goodT_posM_bad_frac_le_keccak`: ReparamFull's
  `2^-197 + 2^-400`, SrcBad's `2^-277`), with `staticFrac` the fraction of the coordinates whose
  template data are off `SphStatic`.
-/

open scoped ENNReal

namespace Quantum.Sphincs.Assembly

/-- **The static condition of the masses** at the template data: HmsgCovers' `HStatic` (the
`H_msg` rates injective, at most five `H_msg` inputs per capacity), `TrialsOff` and
ChgRevStatic's `ChgStatic`. -/
def SphStatic (p : PP) (v : (s : HPos) → XD s) : Prop :=
  HStatic (pubP p) (rootV v) ∧ TrialsOff (pubP p).xw (pubP p).keys.1 (valsOf v) ∧
    ChgStatic (pubP p) (rootV v)

open scoped Classical in
/-- **The static fraction**: the coordinates of the reparametrization whose template data are off
`SphStatic`. -/
noncomputable def staticFrac : ℝ≥0∞ :=
  (Fintype.card YS : ℝ≥0∞)⁻¹ *
    (Finset.univ.filter fun y : YS ↦ ¬SphStatic (psiE y).1 (psiE y).2.1).card

open scoped Classical in
/-- **The masked hybrid's bad fraction** at the good set `FullG (SrcS SphStatic)`: ReparamFull's
`2^-197 + 2^-400`, SrcBad's `2^-277` and the static fraction. -/
theorem stageFrac_sphStatic_le :
    stageFrac (SrcS SphStatic) ≤ ENNReal.ofReal (1 / 2 ^ 197) + ENNReal.ofReal (1 / 2 ^ 400) +
      ENNReal.ofReal (1 / 2 ^ 277) + staticFrac :=
  goodT_posM_bad_frac_le_keccak SphStatic

end Quantum.Sphincs.Assembly

end
