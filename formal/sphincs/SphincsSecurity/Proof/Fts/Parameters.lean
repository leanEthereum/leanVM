import SphincsSecurity.Scheme
import Mathlib.Tactic.IrreducibleDef

/-!
# Few-time signature parameters

The oracle calls of an honest few-time key and opening, and the constants the few-time analysis hands to the rest of the proof. They are sealed: the rest of the proof carries them symbolically, and only the few-time closers and the closing arithmetic use their values.
-/

namespace SphincsSecurity.Concrete

open ENNReal

/-- Opening one leaf in every few-time tree recomputes each authentication path node. -/
irreducible_def ftsOpenHashCost : Nat := ∑ _tree : FtsTree, ∑ level : Fin ftsTreeHeight, (2 ^ (level.val + 1) - 1)

/-- A few-time public key: every tree root, then the hash of the roots. -/
irreducible_def ftsKeyHashCost : Nat := ∑ _tree : FtsTree, (2 ^ (ftsTreeHeight + 1) - 1) + 1

theorem two_pow_ftsTreeHeight_le_ftsOpenHashCost : 2 ^ ftsTreeHeight ≤ ftsOpenHashCost := by
  rw [ftsOpenHashCost_def]
  decide

theorem ftsOpenHashCost_le_digestAttemptLimit : ftsOpenHashCost ≤ digestAttemptLimit := by
  rw [ftsOpenHashCost_def]
  decide

/-- The length of the uniform proposal word that both budget routes price certificates against. -/
irreducible_def fixedProposalLength : Nat := 1537 * 2 ^ 22 + 2 ^ 25 + 13

/-- How far a proposal-word prefix may run ahead of its expected length before the monitor stops. -/
irreducible_def proposalPrefixSlack : Nat := 2 ^ 25

/-- Per query, the expected excess of the full certificate price over the price of one fresh digest. -/
noncomputable irreducible_def fullCertificateExcessRate : ENNReal := 11 / 2 ^ 152

/-- Per query, the average price of a near certificate that omits one given tree. -/
noncomputable irreducible_def nearCertificatePrice : ENNReal := ((557 : ENNReal) / 14) / (2 ^ 128 : Nat)

/-- The probability that a proposal-word prefix ever runs past its slack. -/
noncomputable irreducible_def proposalPrefixExceptionBound : ENNReal := (2 ^ 700 : ENNReal)⁻¹

end SphincsSecurity.Concrete
