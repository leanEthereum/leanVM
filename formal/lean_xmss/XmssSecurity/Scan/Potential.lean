module

public import XmssSecurity.Scan.Reach
public import XmssSecurity.Proof.CappedEncodingRejection

@[expose] public section

/-!
# The partner potential

For one leaf index, the cached encoding inputs `(message, randomness)` and the scan walk on each
message's line of randomizers. A cached input is a hit when its digest is valid; it is partnered when
another cached input of the same leaf index has the same digest. `W y` is the start mass the scan
carries to `y`, `Φ` the mass of the partnered hits and `H` the mass of all hits.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Partner

open LoopWalk

/-- The probability that a fresh uniform output truncates to a valid digest. -/
noncomputable def landing : ℝ≥0∞ :=
  (TargetSum.validDigests.card : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹

/-- The successor of a randomizer. -/
def nextRand : Equiv.Perm Randomness := Equiv.addRight 1

abbrev Position := Message × Randomness

variable (cache : QueryCache HashSpec) (parameter : PublicParameter) (leafIndex : LeafIndex)

def input (y : Position) : HashInput :=
  Concrete.CacheView.encodingInput parameter leafIndex y

noncomputable def status (y : Position) : St :=
  match cache (input parameter leafIndex y) with
  | none => .fresh
  | some output => if TargetSum.ValidDigest (truncateHash output) then .hit else .miss

def IsHit (y : Position) : Prop :=
  ∃ output, cache (input parameter leafIndex y) = some output ∧
    TargetSum.ValidDigest (truncateHash output)

def IsPartnered (y : Position) : Prop :=
  ∃ output, cache (input parameter leafIndex y) = some output ∧
    TargetSum.ValidDigest (truncateHash output) ∧
    ∃ z ≠ y, ∃ other, cache (input parameter leafIndex z) = some other ∧
      truncateHash other = truncateHash output

/-- The start mass the scan on `y`'s message carries to `y`. -/
noncomputable def W (y : Position) : ℝ≥0∞ :=
  ∑ r, reach nextRand landing (fun ρ => status cache parameter leafIndex (y.1, ρ)) y.2
    signingAttemptLimit r

open Classical in
noncomputable def Φ : ℝ≥0∞ :=
  ∑ y, if IsPartnered cache parameter leafIndex y then W cache parameter leafIndex y else 0

open Classical in
noncomputable def H : ℝ≥0∞ :=
  ∑ y, if IsHit cache parameter leafIndex y then W cache parameter leafIndex y else 0

open Classical in
/-- The cached inputs of the leaf index. -/
noncomputable def C : Nat :=
  (Finset.univ.filter fun y : Position => (cache (input parameter leafIndex y)).isSome).card

open Classical in
/-- The cached hits of the leaf index. -/
noncomputable def V : Nat :=
  (Finset.univ.filter fun y : Position => IsHit cache parameter leafIndex y).card

end XmssSecurity.Partner
