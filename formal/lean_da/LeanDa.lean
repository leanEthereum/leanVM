import LeanDa.Commitment
import LeanDa.Subspace
import LeanDa.Security
import LeanDa.RpmSecurity
import LeanDa.RpmWagner
import LeanDa.RpmComplete
import LeanDa.KsRpm
import LeanDa.Arith
import LeanDa.StraightBound
import LeanDa.RpmArg
import LeanDa.PiOnly
import PqDas
import LeanDa.WithHash
import LeanDa.WithHashBridge

/-!
# LeanDA's security

Benedikt Wagner's theorems for his erasure code commitment from a vector commitment, a code
checker and an argument of knowledge (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da;
his post: https://ethresear.ch/t/formally-verified-security-for-pq-das-leanda/25746),
instantiated with LeanDA as `crates/lean_da` computes it, for any number `r ≥ 1` of rows and any
hash `H` (the crate's is Keccak-256): position binding by reduction to a collision of `H`, and
code binding with the membership test's soundness `δ = (2^13 - 1) / 2^128` over the
draws. The argument `ps` and its extractor `ext` are parameters: knowledge soundness enters
as the probability that the explicit reduction `ksReduction` breaks it.

In the random-permutation model (`H` Keccak-256 over a random permutation `π`, the challenges the
deployed duplex over `π`, the adversary and the argument's prover and verifier querying the
model's oracles, the argument's extractor reading the adversary's transcript), LeanDA is perfectly
complete for every permutation `π`, by Wagner's completeness proof
(`leanDa_perfectlyComplete_rpm`, `LeanDa.RpmComplete`); position binding holds with the bound
`(Q + 1)² · 2^-256` for every number `Q` of permutation calls (`leanDa_positionBinding_rpm`, from
`Q² / 2^256 + Q² / 2^508`, `LeanDa.RpmArg`); and code binding holds for an argument knowledge
sound there (`leanDa_codeBinding_rpm_bound`, `LeanDa.RpmArg`) by a straight-line argument built
on Wagner's framework and games (`LeanDa.StraightBound`): a code-binding win is a break of the
argument's knowledge soundness or a bad event of `H` and the draws, lazily sampled per root and
nonce. The grind discounts the membership test's soundness: a draw the adversary's call makes is
selected and accepting with probability at most `2^-10 · (2^13 - 1) / 2^128`, and the verifier's
own nonce search for the root is one fresh try, `(2^13 - 1) / 2^128` (`LeanDa.StraightBad`). The
argument's verification runs with the adversary, so the proof takes the argument as a virtual
oracle-free one that reads the verification's verdict (`psV`), and its knowledge-soundness game
reads the challenge as the nonce search does (`ksIdealG_le_rpmG`).

Wagner's forking route needs an oracle-free argument: for one, code binding moves to the
two-oracle random-oracle model within `Q² / 2^508` (`leanDa_codeBinding_rpm`), where the duplex
lemma (`Common.SeedDuplex`) and sampling `H` in advance give his bound, averaged over `H`, plus
`2 (Q + 2^64 + 2)² / 2^576` (`leanDa_codeBinding_avg`); his two collision terms are birthday bounds
(`wpbColl_le`, `forkColl_le`) and his knowledge-soundness term is the argument's knowledge
soundness in the random-permutation model (`leanDa_codeBinding_core`), so LeanDA is code binding
with explicit terms in `Q` (`leanDa_codeBinding_fork`), a weaker bound than the end statement's,
which implies it (`codeBindingRpmFork_of_codeBindingRpm`).
-/

/-! ## The end theorems

Each proves a proposition of `Statement/LeanDa.lean`, all three in `LeanDa/PiOnly.lean`:
`leanDa_perfectlyComplete_rpm : LeanDaPerfectlyComplete`, `leanDa_positionBinding_rpm :
PositionBindingRpm` and `leanDa_codeBinding_rpm_bound : CodeBindingRpm`; the axioms are pinned at
the end of this file. -/

example : LeanDa.LeanDaPerfectlyComplete := LeanDa.leanDa_perfectlyComplete_rpm

example : LeanDa.LeanDaPositionBinding := LeanDa.leanDa_positionBinding_rpm

example : LeanDa.LeanDaCodeBinding := LeanDa.leanDa_codeBinding_rpm_bound

open PqDas PqDas.CommittedSoundness OracleComp OracleSpec ENNReal

namespace LeanDa

variable (r : ℕ) (H : List UInt8 → Common.DigestBytes) {Crs Proof : Type} (ps : WArgument r H Crs Proof)

/-- **Position binding**: an adversary opening a commitment at one cell to two different cells
gives, through the explicit reduction, a collision of `H`. -/
theorem leanDa_positionBinding
    (A : ErasureCodeCommitment.PosBindingAdv (OracleComp (unifSpec + (Common.DigestBytes →ₒ MembershipChallenge))) Cell
      (r * 128) (Unit × Crs) (Common.DigestBytes × Proof) CellOpening) :
    (leanDa r H ps).posBindingExp (roRuntime Common.DigestBytes MembershipChallenge) A {true} ≤
      Pr{let b ← hashCollisionExp H
          (merkleCollider r H (posBindingReduction ps A))}[b = true] :=
  (scheme_positionBinding (leanDaErasureCode r) (merkleVC r H) (checker r) ps A).trans
    (posBindingExp_le_hashCollisionExp r H _)

/-- **Code binding**: for an adversary making at most `Q` random-oracle queries,
`(Pr[code-bind] - (ε_ks + ε₁))² ≤ (Q + 2) (ε₂ + (2^13 - 1) / 2^128 + 2^-192)`, with `ε_ks` the success of
the reduction against the argument's knowledge soundness and `ε₁`, `ε₂` those of two explicit
reductions finding collisions of `H`. -/
theorem leanDa_codeBinding [NeZero r]
    (ext : Nark.Extractor (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell)
        Crs Proof)
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (Common.DigestBytes →ₒ MembershipChallenge))) Cell
      (r * 128) (Unit × Crs) (Common.DigestBytes × Proof) CellOpening) {Q : ℕ} (hA : ∀ ck, HashQueryBound (A ck) Q) :
    ((leanDa r H ps).codeBindingExp (leanDaErasureCode r) (roRuntime Common.DigestBytes
        MembershipChallenge) A {true} -
        (Pr{let b ← ps.knowledgeSoundnessExp ext (ksReduction (merkleVC r H) A)}[b = true] +
          Pr{let b ← hashCollisionExp H (merkleCollider r H
            ((wpbReduction ps ext A).toPosBindingAdv (merkleVC r H)))}[b = true])) ^ 2 ≤
      ((Q : ℝ≥0∞) + 2) *
        (Pr{let b ← hashCollisionExp H (merkleCollider r H
            ((forkCollisionReduction (leanDaErasureCode r) (merkleVC r H) (checker r)
              (csReduction ps ext A) (Q + 1)).toPosBindingAdv (merkleVC r H)))}[b = true] +
          (2 ^ 13 - 1) / 2 ^ 128 + (2 ^ 192)⁻¹) := by
  have h := scheme_codeBinding_concrete_posBinding (leanDaErasureCode r) (merkleVC r H)
      (checker r) ps
    ext A (merkleVC_perfectlyComplete r H) (checker_sound r) hA
  have hcard : (Fintype.card MembershipChallenge : ℝ≥0∞)⁻¹ ≤ (2 ^ 192)⁻¹ := by
    refine ENNReal.inv_le_inv.mpr ?_
    have hc : (2 ^ 192 : ℕ) ≤ Fintype.card MembershipChallenge := by
      have h1 : Fintype.card Draw = 2 ^ 192 := by rw [Fintype.card_prod, card_E, card_K]; norm_num
      rw [← h1]
      exact Fintype.card_le_of_injective (fun d (_ : Fin nLabels) ↦ d)
        fun a b h ↦ congrFun h ⟨0, by simp⟩
    exact_mod_cast hc
  unfold leanDa
  have h₁ := posBindingExp_le_hashCollisionExp r H
    ((wpbReduction ps ext A).toPosBindingAdv (merkleVC r H))
  have h₂ := posBindingExp_le_hashCollisionExp r H
    ((forkCollisionReduction (leanDaErasureCode r) (merkleVC r H) (checker r)
      (csReduction ps ext A) (Q + 1)).toPosBindingAdv (merkleVC r H))
  refine le_trans ?_ (h.trans ?_)
  · exact pow_le_pow_left₀ zero_le (tsub_le_tsub_left (add_le_add le_rfl h₁) _) 2
  · exact mul_le_mul' le_rfl (add_le_add (add_le_add h₂ le_rfl) hcard)

section CodeBindingRpm

open Common

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
      Proof rel)

/-- **Wagner's code-binding bound for LeanDA, averaged over a uniformly random table of `H`.** For
every argument `ps` and extractor `ext`, and every adversary whose game, verifications included,
makes at most `Q` permutation calls (`permCalls2`),

`(Pr[code-bind] − (Q²/2^508 + 2(Q+2^64+2)²/2^576 + ε_ks + ε₁))² ≤ (Q + 2)(ε₂ + (2^13-1)/2^128 + 2^-192)`,

where, for a uniformly random table `h` of `H` on the strings of at most `2048` bytes (`Hh h`
its hash) and Wagner's adversary `advH h` built from the RPM adversary, `ε_ks` is the success of
Wagner's reduction against the knowledge soundness of `ps` for the relation with the hash `Hh h`
(`ksExpH`), and `ε₁`, `ε₂` those of his two reductions finding a collision of `Hh h`
(`wpbCollExpH`, `forkCollExpH`).

`Q²/2^508` is the two-oracle transfer, `2(Q+2^64+2)²/2^576` the duplex lemma (the challenges' sponge
is a random oracle of the roots unless two of at most `Q + 2^64 + 2` states share their 576-bit
capacity), and the rest is Wagner's bound for each `h`, averaged over `h`. -/
theorem leanDa_codeBinding_avg [NeZero r]
    (ext : Nark.Extractor (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell)
        Crs Proof)
    (A : CodeBindingAdvB r Crs Proof) (Q : ℕ)
    (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) :
    (Pr{let b ← codeBindingExpRpm r ps A}[b = true] -
        ((Q ^ 2 : ℝ≥0∞) / 2 ^ 508 + 2 * ((Q + nLabels + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 576 +
          (Pr{let b ← ($ᵗ HTab : ProbComp HTab) >>= ksExpH r ps ext A}[b = true] +
            Pr{let b ← ($ᵗ HTab : ProbComp HTab) >>= wpbCollExpH r ps ext A}[b = true]))) ^ 2 ≤
      ((Q : ℝ≥0∞) + 2) *
        (Pr{let b ← ($ᵗ HTab : ProbComp HTab) >>= forkCollExpH r ps ext A Q}[b = true] +
          (2 ^ 13 - 1) / 2 ^ 128 + (2 ^ 192)⁻¹) := by
  set εks := Pr{let b ← ($ᵗ HTab : ProbComp HTab) >>= ksExpH r ps ext A}[b = true]
  set ε₁ := Pr{let b ← ($ᵗ HTab : ProbComp HTab) >>= wpbCollExpH r ps ext A}[b = true]
  set ε₂ := Pr{let b ← ($ᵗ HTab : ProbComp HTab) >>= forkCollExpH r ps ext A Q}[b = true]
  set cb : ProbComp Bool := ($ᵗ HTab : ProbComp HTab) >>= fun h ↦ ps.setup >>= fun crs ↦
    (simulateQ (Common.DigestBytes →ₒ MembershipChallenge).romImpl (gameW r ps A h crs)).run' ∅
  -- Wagner's bound, averaged over `H`
  have hW : (prT cb - (εks + ε₁)) ^ 2 ≤ ((Q : ℝ≥0∞) + 2) * (ε₂ + ((2 ^ 13 - 1) / 2 ^ 128 + (2 ^ 192)⁻¹)) := by
    refine sq_tsub_avg_le _ _ _ _ _ _ _ fun h ↦ ?_
    rw [prT_gameW r ps A h, ← add_assoc]
    exact leanDa_codeBinding r (Hh h) (argH r ps (Hh h)) ext (advH r ps A h)
      (hashQueryBound_advH r ps A Q hQ h)
  -- the RPM game against the simulated world
  have hG := codeBindingExpRpm_le_G r ps A Q hQ
  rw [show Pr{let b ← codeBindingExpG r ps A}[b = true] = prT cb from prT_codeBindingExpG r ps A]
    at hG
  have hdup : ((Q + nLabels + 1 : ℕ) : ℝ≥0∞) * (2 * ((Q + nLabels + 1 : ℕ) : ℝ≥0∞) * (2 ^ 576 : ℝ≥0∞)⁻¹) =
      2 * ((Q + nLabels + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 576 := by
    rw [div_eq_mul_inv]; ring
  rw [hdup, add_assoc] at hG
  rw [← add_assoc ε₂] at hW
  refine le_trans (pow_le_pow_left₀ zero_le ?_ 2) hW
  rw [tsub_le_iff_right]
  calc Pr{let b ← codeBindingExpRpm r ps A}[b = true]
      ≤ prT cb + ((Q ^ 2 : ℝ≥0∞) / 2 ^ 508 + 2 * ((Q + nLabels + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 576) := hG
    _ ≤ (prT cb - (εks + ε₁) + (εks + ε₁)) +
          ((Q ^ 2 : ℝ≥0∞) / 2 ^ 508 + 2 * ((Q + nLabels + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 576) := by
        gcongr; exact le_tsub_add
    _ = _ := by ring

end CodeBindingRpm

section Core

open Common

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
      Proof rel)

/-- **Code binding with Wagner's three terms bounded**: the knowledge-soundness term by the RPM
knowledge-soundness experiment of `ksAdv A` and the transfer and duplex terms of its game, and the
two collision terms by birthday bounds. -/
theorem leanDa_codeBinding_core [NeZero r]
    (ext : Nark.Extractor (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell)
        Crs Proof)
    (A : CodeBindingAdvB r Crs Proof) (Q : ℕ)
    (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) :
    (Pr{let b ← codeBindingExpRpm r ps A}[b = true] -
        ((Q ^ 2 : ℝ≥0∞) / 2 ^ 508 + 2 * ((Q + nLabels + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 576 +
          ((Pr{let b ← ksExpRpm r ps ext (ksAdv r A)}[b = true] +
              ((ksCalls r Q) ^ 2 : ℝ≥0∞) / 2 ^ 508 + 2 * ((Q + nLabels + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 576) +
            ((wpbCalls r Q + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256))) ^ 2 ≤
      ((Q : ℝ≥0∞) + 2) *
        (((forkCalls r Q + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 + (2 ^ 13 - 1) / 2 ^ 128 + (2 ^ 192)⁻¹) := by
  have h := leanDa_codeBinding_avg r ps ext A Q hQ
  have hks : Pr{let b ← ($ᵗ HTab : ProbComp HTab) >>= ksExpH r ps ext A}[b = true] ≤
      Pr{let b ← ksExpRpm r ps ext (ksAdv r A)}[b = true] + ((ksCalls r Q) ^ 2 : ℝ≥0∞) / 2 ^ 508 +
        2 * ((Q + nLabels + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 576 := by
    have hdup : ((Q + nLabels + 1 : ℕ) : ℝ≥0∞) * (2 * ((Q + nLabels + 1 : ℕ) : ℝ≥0∞) * (2 ^ 576 : ℝ≥0∞)⁻¹) =
        2 * ((Q + nLabels + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 576 := by
      rw [div_eq_mul_inv]; ring
    rw [prT_ksExpH, ← hdup]
    exact (ksIdealG_le r ps ext A Q hQ).trans
      (add_le_add (rom2_le_ksExpRpm r ps ext A Q hQ) le_rfl)
  have h₁ := wpbColl_le r ps ext A Q hQ
  have h₂ := forkColl_le r ps ext A Q hQ
  refine le_trans (pow_le_pow_left₀ zero_le (tsub_le_tsub_left ?_ _) 2) (h.trans ?_)
  · gcongr
  · gcongr

/-- **Code binding by Wagner's forking route**, for an oracle-free argument (proof side, not an
end statement: the end statements' arguments query the oracles, and the fork needs one that does
not): in the random-permutation model, the code-binding game of `ps` (its two-oracle form,
`codeBindingExpRpm`, the verifier deriving the challenges for each opening) is broken with
probability at most `(Q + c + 2^65) · 2^-k + (Q + 2^20) · 2^-56 + (Q + 2^22)² · 2^-158` if the
argument's knowledge-soundness game (`ksExpRpm`) is at most `(q + c) · 2^-k`: his bound with its
knowledge-soundness term read back in the random-permutation model (`ksExpRpm_ksAdv`, through
`rom2_le_ksExpRpm` and `ksIdealG_le`), its collision terms birthday bounds (`wpbColl_le`,
`forkColl_le`), and the forking lemma's square root bounded (`fork_sq_le`). -/
theorem leanDa_codeBinding_fork (r : ℕ) {Crs Proof : Type}
    {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
    (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
        Proof rel)
    (ext : Nark.Extractor (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs Proof) (c k : ℕ)
    (hks : ∀ (B : KsAdvB Crs Proof) (q : ℕ), QueryCostAtMost (ksGame2 r ps ext B) permCalls2 q →
      q ≤ 2 ^ 128 → Pr{let b ← ksExpRpm r ps ext B}[b = true] ≤ ((q : ℝ≥0∞) + c) * (2 : ℝ≥0∞)⁻¹ ^ k)
    (hr1 : 1 ≤ r) (hrM : r ≤ maxRows) (A : CodeBindingAdvB r Crs Proof) (Q : ℕ)
    (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) (hQcap : Q ≤ 2 ^ 127) :
    Pr{let b ← codeBindingExpRpm r ps A}[b = true] ≤
      ((Q : ℝ≥0∞) + c + 2 ^ 65) * (2 : ℝ≥0∞)⁻¹ ^ k + ((Q : ℝ≥0∞) + 2 ^ 20) * (2 : ℝ≥0∞)⁻¹ ^ 56 +
        ((Q : ℝ≥0∞) + 2 ^ 22) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 158 := by
  have : NeZero r := ⟨by omega⟩
  have hL := logPaddedRowCount_le_logMaxRows hrM
  have hN := paddedRowCount_le_maxRows hrM
  norm_num [maxRows, logMaxRows] at hL hN
  have hK : ksCalls r Q ≤ Q + 2 ^ 65 := by unfold ksCalls relCalls nLabels nonceCount; omega
  have hK' : ksCalls r Q ≤ 2 ^ 43 * (Q + 2 ^ 22) := hK.trans (by omega)
  have hD : Q + nLabels + 1 ≤ 2 ^ 43 * (Q + 2 ^ 22) := by unfold nLabels nonceCount; omega
  have hW : wpbCalls r Q + 2 ≤ Q + 2 ^ 22 := by unfold wpbCalls openCalls; omega
  have hF : forkCalls r Q + 2 ≤ 2 * (Q + 2 ^ 20) := by
    unfold forkCalls commitCalls openCalls; omega
  have hε : Pr{let b ← ksExpRpm r ps ext (ksAdv r A)}[b = true] ≤
      ((Q + c + 2 ^ 65 : ℕ) : ℝ≥0∞) / 2 ^ k := by
    refine (hks (ksAdv r A) (ksCalls r Q) (isWeightBound_ksGame r ps ext A Q hQ)
      (hK.trans (by omega))).trans ?_
    rw [div_eq_mul_inv, ENNReal.inv_pow]
    refine mul_le_mul_left ?_ _
    have hK2 : ksCalls r Q + c ≤ Q + c + 2 ^ 65 := by
      have := hK
      generalize ksCalls r Q = K at this ⊢
      omega
    exact_mod_cast hK2
  have hP := le_of_sq_tsub_le (leanDa_codeBinding_core r ps ext A Q hQ)
    (fork_sq_le Q (forkCalls r Q + 2) hF)
  refine hP.trans ?_
  have hR := rest_le Q (ksCalls r Q) (wpbCalls r Q + 2) (Q + nLabels + 1) (Q + 2 ^ 20) (Q + 2 ^ 22)
    hK' hW (by omega) hD (by omega) (by omega)
  calc _ = Pr{let b ← ksExpRpm r ps ext (ksAdv r A)}[b = true] +
        ((Q ^ 2 : ℝ≥0∞) / 2 ^ 508 + 2 * ((Q + nLabels + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 576 +
          (((ksCalls r Q : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 + 2 * ((Q + nLabels + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 576) +
          ((wpbCalls r Q + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 +
          (((Q + 2 ^ 20 : ℕ) : ℝ≥0∞) / 2 ^ 95 + ((Q + 2 ^ 20 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 159 +
            ((Q + 2 : ℕ) : ℝ≥0∞) / 2 ^ 57)) := by ring
    _ ≤ ((Q + c + 2 ^ 65 : ℕ) : ℝ≥0∞) / 2 ^ k +
        (((Q + 2 ^ 20 : ℕ) : ℝ≥0∞) / 2 ^ 56 + ((Q + 2 ^ 22 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 158) :=
        add_le_add hε hR
    _ = _ := by
        simp only [div_eq_mul_inv, ENNReal.inv_pow]
        push_cast
        ring

/-- **The forking route's bound for the end statement's games** (proof side, not an end
statement): `LeanDaCodeBinding` with the bound the forking route gives,
`(Q + c + 2^65) · 2^-k + (Q + 2^20) · 2^-56 + (Q + 2^22)² · 2^-158`, the end statement's bound
before the straight-line proof. -/
abbrev CodeBindingRpmFork : Prop :=
  ∀ (r : ℕ) {Crs Proof : Type} (ps : LeanDaArgument r Crs Proof)
    (ext : StraightLineExtractor Common.DigestBytes (Fin (r * 128) → Cell) Crs Proof) (c k : ℕ),
    (∀ (B : KnowledgeSoundnessAdversary Crs Proof) (q : ℕ), QueryCostAtMost (knowledgeSoundnessGameWithHash r ps ext B) permutationCallCost q →
      q ≤ 2 ^ 128 → Pr{let b ← runWithRandomPermutation (knowledgeSoundnessGameWithHash r ps ext B)}[b = true] ≤
        ((q : ℝ≥0∞) + c) * (2 : ℝ≥0∞)⁻¹ ^ k) →
    1 ≤ r → r ≤ maxRows →
    ∀ (A : CodeBindingAdversary r Crs Proof) (Q : ℕ),
      QueryCostAtMost (codeBindingGameWithHash r ps A) permutationCallCost Q → Q ≤ 2 ^ 127 →
        Pr{let b ← runWithRandomPermutation (codeBindingGameWithHash r ps A)}[b = true] ≤
          ((Q : ℝ≥0∞) + c + 2 ^ 65) * (2 : ℝ≥0∞)⁻¹ ^ k + ((Q : ℝ≥0∞) + 2 ^ 20) * (2 : ℝ≥0∞)⁻¹ ^ 56 +
            ((Q : ℝ≥0∞) + 2 ^ 22) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 158

/-- **The forking route's bound follows from the straight-line one**, which is below it for every
`Q` (`straight_le_fork`). -/
theorem codeBindingRpmFork_of_codeBindingRpm (h : CodeBindingRpmWithHash) : CodeBindingRpmFork := by
  intro r Crs Proof ps ext c k hks hr1 hrM A Q hQ _
  exact (h r ps ext c k hks hr1 hrM A Q hQ).trans (straight_le_fork Q c k)

end Core

end LeanDa

/-! The build fails if a front-page theorem's axiom footprint ever grows beyond Lean's three
standard axioms. -/

/-- info: 'LeanDa.leanDa_perfectlyComplete_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.leanDa_perfectlyComplete_rpm

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

/-- info: 'LeanDa.dualCodeword_eq_dualCodewordAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.dualCodeword_eq_dualCodewordAt

/-- info: 'LeanDa.leanDa_positionBinding_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.leanDa_positionBinding_rpm

/-- info: 'LeanDa.leanDa_codeBinding_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.leanDa_codeBinding_rpm

/-- info: 'LeanDa.leanDa_codeBinding_rpm_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.leanDa_codeBinding_rpm_bound

/-- info: 'LeanDa.leanDa_codeBinding_fork' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.leanDa_codeBinding_fork

/-- info: 'LeanDa.codeBindingRpmFork_of_codeBindingRpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.codeBindingRpmFork_of_codeBindingRpm

/-- info: 'LeanDa.membershipChallengeM_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.membershipChallengeM_id

/-- info: 'LeanDa.verifyCellM_id' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.verifyCellM_id
