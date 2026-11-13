/-
  LeanVM.Guest.Batch.Rpm

  The batching in the random-permutation model: an adversary querying `π` and `π⁻¹` outputs a
  proof, and the batching program, with Keccak-256 the sponge over `π` and Keccak-f[1600] `π`,
  accepts children with a false claim with probability at most the random-oracle bound of
  `batch_rom` plus `q² / 2^508` for `q` permutation calls.
-/

module

public import LeanVM.Guest.Batch.Rom
public import LeanVM.Protocol.Rpm.Generic
public import Common.Linear
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.ExperimentBridge
public import LeanVM.Guest.WithHash
public import LeanVM.Guest.AcceptableChild
public import Common.ByteArray

@[expose] public section

/-!
# The batching in the random-permutation model

`batch_rom` bounds the batching with Keccak-256 and Keccak-f[1600] independent random oracles.
Here both are built from one random permutation `π`, which the adversary queries forward and
inverse (`Rpm.runAdversaryThen`; `Rpm.detRun` for a deterministic adversary): `batch_rpm` bounds the probability that the batching program
(`boundedBatchingProgram M bytecode`, from its seeding `batchSeedOf`) accepts a proof that begins with fewer than
`M` children of the bytecode's shapes one of whose claims is false (`SomeChildClaimFalse`) by
`batch_rom`'s bound at the adversary's `QA` queries, plus `rpmError (QA + QV · 2^32)`, `QV` the
program's query bound, each query at most `2^32` permutation calls. `batch_rpm_bits`: for
`QA + QV ≤ 2^64`, at most `(QA + QV) · max(2M - 3, 8) · 2^-128`. `batch_bound_le`: for `QA ≤ 2^128`
and `QV ≤ 2^96`, at most `(QA + QV + 1) · max(2M - 3, 8) · 2^-130 + 5 (QA + QV)² · 2^-256`, the
per-query `max(2M - 3, 8) · 2^-130` being `batchε M`: a round's `2/|E|`, or `λ`'s `(2M - 3)/|E|`
through its proof of work of `2` bits (`RomSpec.lean`); `batch_sound_holds` is it as
the end statement `BatchingSound` of `Statement/LeanVmGuestCompleteness.lean` states it: the verifier written out
(`runBatching`, the seeding `F(H(label) ‖ 0)` then the program).

The proof is `Rpm.detRun_le_rom` with `batch_rom` (and, for an adversary with coins, first
`Rpm.rpmRun_le_det`, `Coins.lean`): the program follows the duplex discipline (its
seed is the permutation of `seedInput`, zero from lane `8` on, then the duplex sponge,
`duplexVm_batch`), it hashes only its label (`31` bytes) and commits nothing, so each of its
queries costs at most `2^32` permutation calls (`isWeightBound_batch`).
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Sound LeanVM.Node LeanVM.Rpm OracleComp OracleSpec
open scoped ENNReal

/-! ## The program commits nothing -/

theorem movesOK_readCount (M : ℕ) : BMoves (readChildCount M) := by
  unfold readChildCount
  exact Moves.seq' (Moves.readN _) fun _ _ ↦ Moves.seq' (movesOK_require _ _) fun _ _ ↦
    (Moves.liftOption _).mono (fun _ h ↦ h) id (fun _ _ ↦ trivial) fun _ h ↦ h

theorem movesOK_readChild (nB : ℕ) : BMoves (readChild nB) := by
  unfold readChild
  exact Moves.seq' (Moves.readN _) fun _ _ ↦ Moves.seq' (movesOK_require _ _) fun _ _ ↦
    (Moves.liftOption _).mono (fun _ h ↦ h) id (fun _ _ ↦ trivial) fun _ h ↦ h

theorem movesOK_readChildren (nB : ℕ) : ∀ n, BMoves (readChildren nB n)
  | 0 => trivial
  | n + 1 => Moves.seq' (movesOK_readChild nB) fun _ _ ↦
      Moves.seq' (movesOK_readChildren nB n) fun _ _ ↦ trivial

theorem movesOK_batchAny (M : ℕ) (bytecode : List K) : BMoves (boundedBatchingProgram M bytecode) := by
  unfold boundedBatchingProgram batchingProgram
  exact Moves.seq' (movesOK_readCount M) fun n _ ↦
    Moves.seq' (movesOK_readChildren _ n) fun cs _ ↦ movesOK_batchRest bytecode cs

/-! ## The duplex discipline -/

theorem hOnly_hsRun : ∀ (fs : List (List Digest → Bytes)) (ds : List Digest),
    HOnly (Seed.hsRun callKeccak256 fs ds)
  | [], _ => hOnly_pure _
  | f :: fs, ds => by
    simp only [Seed.hsRun]
    exact (hOnly_queryH _).bind fun _ ↦ hOnly_hsRun fs _

theorem duplexP_batchSeed (h : List KeccakState) :
    DuplexP (batchSeedOf.run callKeccak256 callKeccakF1600) h fun seed h' ↦ seed ∈ h' := by
  simp only [Seed.run, batchSeedOf]
  refine ((hOnly_hsRun _ _).duplexP h).bind fun ds h' hh ↦ ?_
  subst hh
  exact (duplexP_queryF_bind _ _ _ _).mpr
    ⟨admissibleVm_seedInput _ _ _, fun y ↦ List.mem_cons_self⟩

/-- **The batching program follows the duplex discipline.** -/
theorem duplexVm_batch (M : ℕ) (bytecode : List K) (z : Unit × Proof) :
    DuplexVm (verifierFam batchSeeds (boundedBatchingProgram M bytecode) z) [] := by
  rw [duplexVm_iff_duplexP, verifierFam_batch]
  change DuplexP (do
    let seed ← batchSeedOf.run callKeccak256 callKeccakF1600
    runProofWithHash callKeccak256 callKeccakF1600 (boundedBatchingProgram M bytecode) seed z.2) [] _
  exact (duplexP_batchSeed []).bind fun seed h' hs ↦ duplexP_runProof _ hs _

/-! ## The permutation calls -/

theorem batchLabel_length : batchingLabel.length ≤ 2 ^ 37 := by
  rw [batchingLabel, String.length_toList_toUTF8]
  decide

theorem allQ_batchSeed : AllQueriesSatisfy (batchSeedOf.run callKeccak256 callKeccakF1600) Short := by
  refine allQueriesSatisfy_bind (allQ_hsRun _ _ fun f hf ds ↦ ?_) fun _ ↦ allQ_queryF _
  simp only [batchSeedOf, List.mem_cons, List.not_mem_nil, or_false] at hf
  subst hf
  exact batchLabel_length.trans (Nat.le_add_right _ _)

theorem allQ_batch (M : ℕ) (bytecode : List K) (z : Unit × Proof) :
    AllQueriesSatisfy (verifierFam batchSeeds (boundedBatchingProgram M bytecode) z) Short := by
  rw [verifierFam_batch]
  exact allQueriesSatisfy_bind allQ_batchSeed fun seed ↦
    allQ_runProof _ seed z.2 (WidthsLE.of_moves (movesOK_batchAny M bytecode))

/-- **The batching program makes at most `QV · 2^32` permutation calls**, `QV` its query
bound. -/
theorem isWeightBound_batch (M : ℕ) (bytecode : List K) (z : Unit × Proof) :
    Common.QueryCostAtMost (verifierFam batchSeeds (boundedBatchingProgram M bytecode) z) hashBlocks
      (batchingQueryBound bytecode M * 2 ^ 32) :=
  isWeightBound_of_isTotalQueryBound hashBlocks (2 ^ 32) (isTotalQueryBound_batchFam M bytecode z)
    ((allQ_batch M bytecode z).mono fun _ h ↦ (hashBlocks_le_of_short h).trans (by norm_num))

/-! ## The batching in the random-permutation model -/

variable {M : ℕ} {bytecode : List K}

/-- **The batching in the random-permutation model.** An adversary of `QA` queries to `π` and
`π⁻¹` outputs a proof; the probability that the batching program, Keccak-256 the sponge over `π`
and Keccak-f[1600] `π`, accepts it while it begins with fewer than `M` children of the bytecode's
shapes one of whose claims is false is at most `batch_rom`'s bound,
`(QA + QV) · (batchε M + failBound (QA + QV))`, plus `rpmError (QA + QV · 2^32)`, `QV` the
program's query bound. -/
theorem batch_rpm (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length) (hM : M ≤ 2 ^ 64 - 1)
    (A : OracleComp (Common.permutationOracleSpec KeccakState) (Unit × Proof)) (QA : ℕ) (hA : A.IsTotalQueryBound QA) :
    Pr{let z ← detRun A (verifierFam batchSeeds (boundedBatchingProgram M bytecode))}[
      z.2 = true ∧ SomeChildClaimFalse bytecode M z.1.2] ≤
      ((QA + batchingQueryBound bytecode M : ℕ) : ℝ≥0∞) *
          (batchε M + failBound batchSeeds (QA + batchingQueryBound bytecode M)) +
        rpmError (QA + batchingQueryBound bytecode M * 2 ^ 32) := by
  obtain ⟨A', hA', hle⟩ := detRun_le_rom A (verifierFam batchSeeds (boundedBatchingProgram M bytecode))
    (duplexVm_batch M bytecode) hA (isWeightBound_batch M bytecode)
    (fun z ↦ z.2 = true ∧ SomeChildClaimFalse bytecode M z.1.2)
  refine hle.trans (add_le_add (le_of_eq_of_le ?_ (batch_rom hb hM A' QA hA')) le_rfl)
  rw [romStep_eq, prEvent_map]

/-- `batchε M + failBound` at `N ≤ 2^64` queries is at most `max(2M - 3, 8) · 2^-129`. -/
theorem batchε_add_failBound_le {N : ℕ} (M : ℕ) (hN : N ≤ 2 ^ 64) :
    batchε M + failBound batchSeeds N ≤ (max (2 * M - 3) 8 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ 129 := by
  rw [batchε, failBound_batchSeeds]
  exact bits_129 (by omega) hN

/-- `(QA + QV · 2^32)² ≤ (QA + QV) · c` for `QA + QV ≤ 2^64` and `c ≥ 2^128`. -/
theorem sq_batch_le {QA QV c : ℕ} (hN : QA + QV ≤ 2 ^ 64) (hc : 2 ^ 128 ≤ c) :
    (QA + QV * 2 ^ 32) ^ 2 ≤ (QA + QV) * c := by
  have h1 : QA + QV * 2 ^ 32 ≤ (QA + QV) * 2 ^ 32 := by omega
  have h2 : (QA + QV) * 2 ^ 32 ≤ 2 ^ 96 :=
    calc (QA + QV) * 2 ^ 32 ≤ 2 ^ 64 * 2 ^ 32 := Nat.mul_le_mul_right _ hN
      _ = 2 ^ 96 := by norm_num
  calc (QA + QV * 2 ^ 32) ^ 2 = (QA + QV * 2 ^ 32) * (QA + QV * 2 ^ 32) := Nat.pow_two _
    _ ≤ ((QA + QV) * 2 ^ 32) * 2 ^ 96 := Nat.mul_le_mul h1 (h1.trans h2)
    _ = (QA + QV) * 2 ^ 128 := by ring
    _ ≤ (QA + QV) * c := Nat.mul_le_mul_left _ hc

/-- `rpmError (QA + QV · 2^32)` is at most `(QA + QV) · 2^-189` for `QA + QV ≤ 2^64`. -/
theorem rpmError_batch_le {QA QV : ℕ} (hN : QA + QV ≤ 2 ^ 64) :
    rpmError (QA + QV * 2 ^ 32) ≤ ((QA + QV : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 189 := by
  rw [rpmError_eq, inv_pow_eq_div 189 508 (by norm_num), ← mul_div_assoc, ← Nat.cast_mul]
  refine ENNReal.div_le_div_right (Nat.cast_le.2 ?_) _
  rw [show 508 - 189 = 128 + 191 from rfl, pow_add]
  exact sq_batch_le hN (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))

theorem two_mul_inv_pow_129 : 2 * (2 : ℝ≥0∞)⁻¹ ^ 129 = (2 : ℝ≥0∞)⁻¹ ^ 128 := by
  rw [pow_succ, ← mul_assoc, mul_comm 2, mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

/-- **The batching in the random-permutation model, in bits**: for `QA + QV ≤ 2^64` (the
adversary's queries to `π` and `π⁻¹` and the program's query bound), the program accepts fewer
than `M` children with a false claim with probability at most
`(QA + QV) · max(2M - 3, 8) · 2^-128`. -/
theorem batch_rpm_bits (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)
    (hM : M ≤ 2 ^ 64 - 1) (A : OracleComp (Common.permutationOracleSpec KeccakState) (Unit × Proof)) (QA : ℕ)
    (hA : A.IsTotalQueryBound QA) (hQ : QA + batchingQueryBound bytecode M ≤ 2 ^ 64) :
    Pr{let z ← detRun A (verifierFam batchSeeds (boundedBatchingProgram M bytecode))}[
      z.2 = true ∧ SomeChildClaimFalse bytecode M z.1.2] ≤
      ((QA + batchingQueryBound bytecode M : ℕ) : ℝ≥0∞) *
        ((max (2 * M - 3) 8 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ 128) := by
  refine (batch_rpm hb hM A QA hA).trans ?_
  have hm : (1 : ℝ≥0∞) ≤ (max (2 * M - 3) 8 : ℕ) := by
    exact_mod_cast (show 1 ≤ max (2 * M - 3) 8 by omega)
  calc ((QA + batchingQueryBound bytecode M : ℕ) : ℝ≥0∞) *
          (batchε M + failBound batchSeeds (QA + batchingQueryBound bytecode M)) +
        rpmError (QA + batchingQueryBound bytecode M * 2 ^ 32)
      ≤ ((QA + batchingQueryBound bytecode M : ℕ) : ℝ≥0∞) *
            ((max (2 * M - 3) 8 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ 129) +
          ((QA + batchingQueryBound bytecode M : ℕ) : ℝ≥0∞) *
            ((max (2 * M - 3) 8 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ 129) :=
        add_le_add (by gcongr; exact batchε_add_failBound_le M hQ)
          ((rpmError_batch_le hQ).trans (by
            gcongr
            exact (Common.inv_two_pow_le_of_le (by norm_num)).trans (le_mul_of_one_le_left zero_le hm)))
    _ = ((QA + batchingQueryBound bytecode M : ℕ) : ℝ≥0∞) *
          ((max (2 * M - 3) 8 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ 128) := by
        rw [← mul_add, ← two_mul, ← two_mul_inv_pow_129]
        ring

/-- **The batching's bound up to `2^128` queries of the adversary**: for `QA ≤ 2^128` and a program
bound `QV ≤ 2^96`, `batch_rpm`'s bound is at most
`(QA + QV + 1) · max(2M - 3, 8) · 2^-130 + 5 (QA + QV)² · 2^-256`: `batchε M` per query, the
failure term `5 (QA + QV) / 2^256` per query, and the transfer's
`(QA + QV · 2^32)² / 2^508 ≤ 2^-250`, within one more `batchε M`. -/
theorem batch_bound_le {QA QV M : ℕ} (hQA : QA ≤ 2 ^ 128) (hQV : QV ≤ 2 ^ 96) :
    ((QA + QV : ℕ) : ℝ≥0∞) * (batchε M + failBound batchSeeds (QA + QV)) +
        rpmError (QA + QV * 2 ^ 32) ≤
      (((QA + QV : ℕ) : ℝ≥0∞) + 1) * (max (2 * M - 3) 8 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ 130 +
        5 * ((QA + QV : ℕ) : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
  have hq : QA + QV * 2 ^ 32 ≤ 2 ^ 129 :=
    calc QA + QV * 2 ^ 32 ≤ 2 ^ 128 + 2 ^ 96 * 2 ^ 32 :=
          Nat.add_le_add hQA (Nat.mul_le_mul_right _ hQV)
      _ = 2 ^ 129 := by norm_num
  have hm : (1 : ℝ≥0∞) ≤ (max (2 * M - 3) 8 : ℕ) := by
    exact_mod_cast (show 1 ≤ max (2 * M - 3) 8 by omega)
  have hr : rpmError (QA + QV * 2 ^ 32) ≤ (max (2 * M - 3) 8 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ 130 :=
    calc rpmError (QA + QV * 2 ^ 32) ≤ ((QA + QV * 2 ^ 32 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 379 :=
          Common.sq_div_le_mul_inv_pow (k := 129) 379 hq
      _ ≤ (2 : ℝ≥0∞) ^ 129 * (2 : ℝ≥0∞)⁻¹ ^ 379 := by
          gcongr
          exact_mod_cast hq
      _ = (2 : ℝ≥0∞)⁻¹ ^ 250 := Common.two_pow_mul_inv_pow 129 250
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 130 := Common.inv_two_pow_le_of_le (by norm_num)
      _ ≤ (max (2 * M - 3) 8 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ 130 := le_mul_of_one_le_left zero_le hm
  have hf : ((QA + QV : ℕ) : ℝ≥0∞) * failBound batchSeeds (QA + QV) =
      5 * ((QA + QV : ℕ) : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
    rw [failBound_batchSeeds, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv, ENNReal.inv_pow]
    ring
  rw [batchε, mul_add, hf]
  calc ((QA + QV : ℕ) : ℝ≥0∞) * ((max (2 * M - 3) 8 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ 130) +
        5 * ((QA + QV : ℕ) : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 + rpmError (QA + QV * 2 ^ 32)
      ≤ ((QA + QV : ℕ) : ℝ≥0∞) * ((max (2 * M - 3) 8 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ 130) +
        5 * ((QA + QV : ℕ) : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 +
          (max (2 * M - 3) 8 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ 130 :=
        add_le_add le_rfl hr
    _ = (((QA + QV : ℕ) : ℝ≥0∞) + 1) * (max (2 * M - 3) 8 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ 130 +
        5 * ((QA + QV : ℕ) : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 := by ring

/-! ## The end statements -/

/-- The batching's statement family run on a proof is the batching's verifier
(`Statement/LeanVmGuest.lean`) with the oracle calls. -/
theorem verifierFam_eq_batchRun (M : ℕ) (bytecode : List K) :
    verifierFam batchSeeds (boundedBatchingProgram M bytecode) =
      fun z ↦ runBatchingWithHash callKeccak256 callKeccakF1600 (boundedBatchingProgram M bytecode) z.2 := by
  funext z
  rw [verifierFam_batch]
  simp only [verifierComp, Rom.verify, Seed.run, batchSeedOf, Seed.hsRun, runBatchingWithHash,
    bind_assoc, pure_bind, List.nil_append, List.getD_cons_zero]

/-- **`BatchingSound`** (`Statement/LeanVmGuestCompleteness.lean`): the adversary's coins do not
help (`rpmRun_le_det`), then `batch_rpm` and `batch_bound_le`. -/
theorem batchingSoundWithHash_holds : BatchingSoundWithHash := by
  intro M bytecode hb hM B QA hB hQA hQV
  rw [← verifierFam_eq_batchRun]
  obtain ⟨A, hA, hle⟩ := rpmRun_le_det hB (verifierFam batchSeeds (boundedBatchingProgram M bytecode))
    (fun z ↦ z.2 = true ∧ SomeChildClaimFalse bytecode M z.1.2)
  exact hle.trans ((batch_rpm hb hM A QA hA).trans (batch_bound_le hQA hQV))

/-- **`BatchingSound`** (`Statement/LeanVmGuestCompleteness.lean`): the game over `π` is the experiment with
the two calls (`batchingSound_of_withHash`). -/
theorem batch_sound_holds : BatchingSound :=
  batchingSound_of_withHash batchingSoundWithHash_holds

end LeanVM.Guest.Batch

end
