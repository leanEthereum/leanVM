import LeanDa.Commitment
import LeanDa.Security
import PqDas

/-!
# LeanDA's security

Wagner's theorems for his erasure code commitment from a vector commitment, a code checker and
an argument of knowledge (`PqDas`), instantiated with LeanDA as `crates/lean_da` computes it, for
any number `r ≥ 1` of rows and any hash `H` (the crate's is BLAKE2s): completeness, position
binding by reduction to a collision of `H`, and code binding with the membership test's
soundness `δ = 14 / 2^192` over `|E^14| = 2^2688` challenges. The argument `ps` and its extractor `ext` are parameters: knowledge soundness enters
as the probability that the explicit reduction `ksReduction` breaks it.
-/

open PqDas PqDas.CommittedSoundness OracleComp OracleSpec ENNReal

namespace LeanDa

variable (r : ℕ) (H : List UInt8 → Digest) {Crs Proof : Type} (ps : Argument r H Crs Proof)

/-- **Completeness**: with a perfectly complete argument, every cell of an honest commitment
opens and verifies. -/
theorem leanDa_perfectlyComplete (hps : ps.PerfectlyComplete) :
    (leanDa r H ps).PerfectlyComplete (code r) (roRuntime Digest Challenges) :=
  scheme_perfectlyComplete (code r) (merkleVC r H) (checker r) ps
    (merkleVC_perfectlyComplete r H) (checker_complete r) hps

/-- **Position binding**: an adversary opening a commitment at one cell to two different cells
gives, through the explicit reduction, a collision of `H`. -/
theorem leanDa_positionBinding
    (A : ErasureCodeCommitment.PosBindingAdv (OracleComp (unifSpec + (Digest →ₒ Challenges))) Cell
      (r * 128) (Unit × Crs) (Digest × Proof) Opening) :
    (leanDa r H ps).posBindingExp (roRuntime Digest Challenges) A {true} ≤
      Pr{let b ← hashCollisionExp H
          (merkleCollider r H (posBindingReduction ps A))}[b = true] :=
  (scheme_positionBinding (code r) (merkleVC r H) (checker r) ps A).trans
    (posBindingExp_le_hashCollisionExp r H _)

/-- **Code binding**: for an adversary making at most `Q` random-oracle queries,
`(Pr[code-bind] - (ε_ks + ε₁))² ≤ (Q + 2) (ε₂ + 14 / 2^192 + 2^-2688)`, with `ε_ks` the success of
the reduction against the argument's knowledge soundness and `ε₁`, `ε₂` those of two explicit
reductions finding collisions of `H`. -/
theorem leanDa_codeBinding [NeZero r]
    (ext : Nark.Extractor (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof)
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (Digest →ₒ Challenges))) Cell
      (r * 128) (Unit × Crs) (Digest × Proof) Opening) {Q : ℕ} (hA : ∀ ck, HashQueryBound (A ck) Q) :
    ((leanDa r H ps).codeBindingExp (code r) (roRuntime Digest Challenges) A {true} -
        (Pr{let b ← ps.knowledgeSoundnessExp ext (ksReduction (merkleVC r H) A)}[b = true] +
          Pr{let b ← hashCollisionExp H (merkleCollider r H
            ((wpbReduction ps ext A).toPosBindingAdv (merkleVC r H)))}[b = true])) ^ 2 ≤
      ((Q : ℝ≥0∞) + 2) *
        (Pr{let b ← hashCollisionExp H (merkleCollider r H
            ((forkCollisionReduction (code r) (merkleVC r H) (checker r)
              (csReduction ps ext A) (Q + 1)).toPosBindingAdv (merkleVC r H)))}[b = true] +
          14 / 2 ^ 192 + (2 ^ 2688)⁻¹) := by
  have h := scheme_codeBinding_concrete_posBinding (code r) (merkleVC r H) (checker r) ps
    ext A (merkleVC_perfectlyComplete r H) (checker_sound r) hA
  have hcard : (Fintype.card Challenges : ℝ≥0∞)⁻¹ = (2 ^ 2688)⁻¹ := by
    rw [card_challenges, Nat.cast_pow, Nat.cast_ofNat, show 192 * 14 = 2688 from rfl]
  rw [hcard] at h
  unfold leanDa
  have h₁ := posBindingExp_le_hashCollisionExp r H
    ((wpbReduction ps ext A).toPosBindingAdv (merkleVC r H))
  have h₂ := posBindingExp_le_hashCollisionExp r H
    ((forkCollisionReduction (code r) (merkleVC r H) (checker r)
      (csReduction ps ext A) (Q + 1)).toPosBindingAdv (merkleVC r H))
  refine le_trans ?_ (h.trans ?_)
  · exact pow_le_pow_left₀ zero_le (tsub_le_tsub_left (add_le_add le_rfl h₁) _) 2
  · exact mul_le_mul' le_rfl (add_le_add (add_le_add h₂ le_rfl) le_rfl)

end LeanDa

/-! The build fails if a front-page theorem's axiom footprint ever grows beyond Lean's three
standard axioms. -/

/-- info: 'LeanDa.leanDa_perfectlyComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.leanDa_perfectlyComplete

/-- info: 'LeanDa.leanDa_positionBinding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.leanDa_positionBinding

/-- info: 'LeanDa.leanDa_codeBinding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.leanDa_codeBinding

/-- info: 'LeanDa.checker_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.checker_sound

/-- info: 'LeanDa.commitCodewords_eq_commitCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.commitCodewords_eq_commitCells
