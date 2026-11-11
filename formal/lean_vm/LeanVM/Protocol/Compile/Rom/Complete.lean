/-
  LeanVM.Protocol.Compile.Rom.Complete

  Completeness of the compiled verifier in the random-oracle model: the honest prover, run
  against the random oracles, produces a proof the compiled verifier rejects with negligible
  probability; its only failure is a proof-of-work search that runs out of fuel.
-/

module

public import LeanVM.Protocol.Compile.Rom.Prover
public import LeanVM.Protocol.Compile.Rom.Step
public import LeanVM.Protocol.Compile.Rom.Final
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds
public import LeanVM.Protocol.WithHash

/-!
# Completeness in the random-oracle model

Let `P : VerifierProgram Bool` be a verifier program, `S` a strategy that wins every interactive run
of `P` with well-shaped words, and `σ` the seeding. The honest prover of the random-oracle model
(`honestComp σ P S fuel`) seeds the sponge and runs `proveM callKeccak256 callKeccakF1600`; when a proof-of-work
search finds no nonce below `fuel`, it outputs the empty proof. In the experiment
`romExperiment` the honest prover and then the compiled verifier run against the same lazily
sampled random oracles.

`romComplete`: if every proof of work of `P` asks for at most `bits ≤ 64` bits (and is followed at
once by a challenge, `GrindThenSample`), the verifier rejects with probability at most

  `Q · (1 - 2^-bits)^fuel`,

`Q` the queries of the prover and the verifier together.

## The proof

On every outcome in which the honest prover returns a proof, the verifier accepts: both runs read
their queries from the oracles' final log, so they are the runs of the pure prover and verifier
at a hash function and a permutation that agree with the log (`simulateQ_id_of_look`), and the
pure verifier accepts the pure prover's proof for all of them (`runProof_prove`).

The prover fails only at a proof-of-work search, at a sponge whose capacity `c` and waiting
scalars `ps` (all of tag `1`, at most three) fix the inputs of the nonces, `nonceInput c ps n`,
and whose `fuel` nonces all fail. A potential on the log (`powPot`) sums, over the positions
`(c, ps)` some of whose nonce inputs below `fuel` the log holds (`keys`), the probability
`(1 - 2^-bits)^(untried)` that the nonces not yet in the log all fail a `bits`-bit proof of work, or
`0` once one passed (`powTerm`); a nonce that fails a narrower grind fails it too (`powOk_mono`). It is `1` on a log in which the prover failed (`one_le_powPot`). A fresh permutation
query keeps a position's term a martingale (a nonce fails with probability exactly
`1 - 2^-bits`, `avg_miss_eq`), and a position new to the log starts with its first nonce, its
term averaging to `(1 - 2^-bits)^fuel` (`powPot_stepF`); hash queries change nothing. The
potential engine of `LeanVM.Protocol.ToVCVio.Rom` turns this into the bound. No collision term
is needed: a position's term counts the nonce inputs in the log, whoever queried them.
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash LeanVM.Protocol
open LeanVM.Protocol.Rom OracleComp OracleSpec
open LeanVM.Prover (Tree buildTreeWithHash searchM findNonceM)
open scoped ENNReal

@[expose] public section

/- The enumerations of `Digest` and `KState` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest instFintypeKState

/-! ## The proof-of-work predicate, exactly -/

/-- The probability that one nonce fails a proof of work of `b` bits: `1 - 2^-b`. -/
noncomputable def missProb (b : ℕ) : ℝ≥0∞ := 1 - 2⁻¹ ^ b

/-- **A nonce fails with probability exactly `1 - 2^-b`.** -/
theorem avg_miss_eq {b : ℕ} (hb : b ≤ 64) :
    (∑ u : KeccakState, ind (powOk b (Keccak.lane u 2) = false)) / Fintype.card KeccakState =
      missProb b := by
  have hc : (Fintype.card KeccakState : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hct : (Fintype.card KeccakState : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hadd : (∑ u : KeccakState, ind (powOk b (Keccak.lane u 2) = false)) +
      (∑ u : KeccakState, ind (powOk b (Keccak.lane u 2) = true)) = Fintype.card KeccakState := by
    rw [← Finset.sum_add_distrib]
    calc ∑ u : KeccakState, (ind (powOk b (Keccak.lane u 2) = false) +
          ind (powOk b (Keccak.lane u 2) = true))
        = ∑ _u : KeccakState, (1 : ℝ≥0∞) := Finset.sum_congr rfl fun u _ ↦ by
          cases powOk b (Keccak.lane u 2) <;> simp [ind]
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hdiv := congrArg (· / (Fintype.card KeccakState : ℝ≥0∞)) hadd
  simp only [ENNReal.add_div, ENNReal.div_self hc hct, sum_powOk_div_eq hb] at hdiv
  exact ENNReal.eq_sub_of_add_eq (by simp) hdiv

theorem missProb_eq_ofReal (b : ℕ) : missProb b = ENNReal.ofReal (1 - (1 / 2 : ℝ) ^ b) := by
  rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one, ENNReal.ofReal_pow (by norm_num)]
  rw [missProb, one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- `(1 - 2^-b)^(2^b) ≤ e^-1 < 3/8`, over the reals. -/
theorem one_sub_pow_le_three_eighths (b : ℕ) : (1 - (1 / 2 : ℝ) ^ b) ^ (2 ^ b) ≤ 3 / 8 := by
  have hy0 : 0 ≤ 1 - (1 / 2 : ℝ) ^ b := by
    have : (1 / 2 : ℝ) ^ b ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have he : Real.exp (-1) < 3 / 8 := by
    have h := Real.exp_one_gt_d9
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  calc (1 - (1 / 2 : ℝ) ^ b) ^ (2 ^ b) ≤ (Real.exp (-(1 / 2 : ℝ) ^ b)) ^ (2 ^ b) :=
        pow_le_pow_left₀ hy0 (by have := Real.add_one_le_exp (-(1 / 2 : ℝ) ^ b); linarith) _
    _ = Real.exp (-1) := by
        rw [← Real.exp_nat_mul]; congr 1
        push_cast
        rw [mul_neg, ← mul_pow]; norm_num
    _ ≤ 3 / 8 := he.le

/-- **`2^b · 4k` failed nonces are as unlikely as `5k` fair coins all landing tails**:
`(1 - 2^-b)^(2^b · 4k) ≤ e^-4k < 2^-5k`, as `(3/8)^4 < 2^-5`. -/
theorem missProb_pow_four_le (b k : ℕ) : missProb b ^ (2 ^ b * 4 * k) ≤ 2⁻¹ ^ (5 * k) := by
  rw [pow_mul, pow_mul, pow_mul]
  refine pow_le_pow_left₀ bot_le ?_ k
  have hy : 0 ≤ 1 - (1 / 2 : ℝ) ^ b := by
    have : (1 / 2 : ℝ) ^ b ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  rw [missProb_eq_ofReal, ← ENNReal.ofReal_pow hy, ← ENNReal.ofReal_pow (pow_nonneg hy _)]
  calc ENNReal.ofReal (((1 - (1 / 2 : ℝ) ^ b) ^ (2 ^ b)) ^ 4) ≤ ENNReal.ofReal ((1 / 2) ^ 5) :=
        ENNReal.ofReal_le_ofReal ((pow_le_pow_left₀ (pow_nonneg hy _)
          (one_sub_pow_le_three_eighths b) 4).trans (by norm_num))
    _ = 2⁻¹ ^ 5 := by
        rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
        norm_num

/-- A proof of work of `B` bits passes one of `b ≤ B` bits. -/
theorem powOk_mono {b B : ℕ} (hbB : b ≤ B) {w : UInt64} (h : powOk B w = true) :
    powOk b w = true := by
  simp only [powOk, decide_eq_true_eq] at h ⊢
  exact Nat.mod_eq_zero_of_dvd ((Nat.pow_dvd_pow 2 hbB).trans (Nat.dvd_of_mod_eq_zero h))

/-! ## Proof-of-work positions -/

/-- The permutation input of the nonce `n` at the capacity `c` with the waiting scalars `ps`: the
nonce absorbed with tag `4` after them, then the permutation (`absorbNonce`). -/
def nonceInput (c : Fin 9 → UInt64) (ps : List (E × ℕ)) (n : ℕ) : KeccakState :=
  duplexOf c (ps ++ [(nonceOf n, dsPowNonce)])

/-- A position of a proof-of-work search: the capacity and the waiting scalars. -/
abbrev PowKey : Type := (Fin 9 → UInt64) × List (E × ℕ)

/-- A position as the honest prover reaches it: at most three scalars waiting, each of tag `1`. -/
def KeyOk (κ : PowKey) : Prop := κ.2.length ≤ 3 ∧ ∀ e ∈ κ.2, e.2 = 1

theorem nonceOf_inj {n n' : ℕ} (hn : n < 2 ^ 64) (hn' : n' < 2 ^ 64)
    (h : nonceOf n = nonceOf n') : n = n' := by
  have h0 := congrArg (fun x : E ↦ (x.limb 0).toBitVec.toNat) h
  simp only [nonceOf, limb_ofLimbs, K.ofBits] at h0
  change (BitVec.ofNat 64 n).toNat = (BitVec.ofNat 64 n').toNat at h0
  simp only [BitVec.toNat_ofNat] at h0
  rwa [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hn'] at h0

theorem validPending_key {κ : PowKey} (hκ : KeyOk κ) (n : ℕ) :
    ValidPending (κ.2 ++ [(nonceOf n, dsPowNonce)]) := by
  refine ⟨by simp; have := hκ.1; omega, fun e he ↦ ?_⟩
  rcases List.mem_append.mp he with he | he
  · exact Or.inl (hκ.2 e he)
  · rw [List.mem_singleton] at he; subst he; exact Or.inr rfl

/-- Nonce inputs name their position and nonce. -/
theorem nonceInput_inj {κ κ' : PowKey} (hκ : KeyOk κ) (hκ' : KeyOk κ') {n n' : ℕ}
    (hn : n < 2 ^ 64) (hn' : n' < 2 ^ 64)
    (h : nonceInput κ.1 κ.2 n = nonceInput κ'.1 κ'.2 n') : κ = κ' ∧ n = n' := by
  have hc := congrArg capOf h
  simp only [nonceInput, capOf_duplexOf] at hc
  have hp := congrArg parsePending h
  simp only [nonceInput, parsePending_duplexOf _ (validPending_key hκ n),
    parsePending_duplexOf _ (validPending_key hκ' n')] at hp
  obtain ⟨hps, hlast⟩ := List.append_inj' hp rfl
  simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hlast
  exact ⟨Prod.ext hc hps, nonceOf_inj hn hn' hlast⟩

section Pot

variable (bits fuel : ℕ)

open Classical in
/-- The position of a nonce input below `fuel`, if the input is one. -/
noncomputable def keyOf (t : KeccakState) : Option PowKey :=
  if h : ∃ κ : PowKey, ∃ n, KeyOk κ ∧ n < fuel ∧ t = nonceInput κ.1 κ.2 n then some h.choose
  else none

open Classical in
/-- The positions some of whose nonce inputs below `fuel` the log holds. -/
noncomputable def keys (ℓ : Log) : Finset PowKey := ((fIns ℓ).filterMap (keyOf fuel)).toFinset

open Classical in
/-- The nonces below `fuel` the log has tried at a position. -/
noncomputable def tried (ℓ : Log) (κ : PowKey) : Finset ℕ :=
  (Finset.range fuel).filter fun n ↦ lookF ℓ (nonceInput κ.1 κ.2 n) ≠ none

/-- Some nonce below `fuel` passes at a position, in the log. -/
def Solved (ℓ : Log) (κ : PowKey) : Prop :=
  ∃ n < fuel, ∃ v, lookF ℓ (nonceInput κ.1 κ.2 n) = some v ∧
    powOk bits (Keccak.lane v 2) = true

open Classical in
/-- The term of a position: `0` once a nonce below `fuel` passed, otherwise the probability that
the nonces below `fuel` not yet tried all fail. -/
noncomputable def powTerm (ℓ : Log) (κ : PowKey) : ℝ≥0∞ :=
  if Solved bits fuel ℓ κ then 0 else missProb bits ^ (fuel - (tried fuel ℓ κ).card)

/-- **The proof-of-work potential**: the terms of the positions the log holds. -/
noncomputable def powPot (ℓ : Log) : ℝ≥0∞ := ∑ κ ∈ keys fuel ℓ, powTerm bits fuel ℓ κ

theorem powPot_nil : powPot bits fuel [] = 0 := by
  simp [powPot, keys, fIns]

end Pot

/-! ## The step -/

section Step

variable {bits fuel : ℕ}

theorem keyOf_spec {t : KeccakState} {κ : PowKey} (h : keyOf fuel t = some κ) :
    ∃ n, KeyOk κ ∧ n < fuel ∧ t = nonceInput κ.1 κ.2 n := by
  unfold keyOf at h
  split at h
  · rename_i hex
    cases h
    exact hex.choose_spec
  · cases h

theorem keyOf_nonceInput (hfuel : fuel ≤ 2 ^ 64) {κ : PowKey} (hκ : KeyOk κ) {n : ℕ}
    (hn : n < fuel) : keyOf fuel (nonceInput κ.1 κ.2 n) = some κ := by
  have hex : ∃ κ' : PowKey, ∃ n', KeyOk κ' ∧ n' < fuel ∧
      nonceInput κ.1 κ.2 n = nonceInput κ'.1 κ'.2 n' := ⟨κ, n, hκ, hn, rfl⟩
  unfold keyOf
  split
  · rename_i hex'
    obtain ⟨n', hκ', hn', he⟩ := hex'.choose_spec
    exact congrArg some (nonceInput_inj hκ hκ' (by omega) (by omega) he).1.symm
  · exact absurd hex ‹_›

/-- The terms of a position whose nonce inputs below `fuel` all differ from `t` do not move. -/
theorem powTerm_append_of_ne {ℓ : Log} {e : Entry} {κ : PowKey}
    (hne : ∀ n < fuel, lookF (ℓ ++ [e]) (nonceInput κ.1 κ.2 n) = lookF ℓ (nonceInput κ.1 κ.2 n)) :
    powTerm bits fuel (ℓ ++ [e]) κ = powTerm bits fuel ℓ κ := by
  have hS : Solved bits fuel (ℓ ++ [e]) κ ↔ Solved bits fuel ℓ κ := by
    unfold Solved
    constructor
    · rintro ⟨n, hn, d, hd, hp⟩; exact ⟨n, hn, d, (hne n hn) ▸ hd, hp⟩
    · rintro ⟨n, hn, d, hd, hp⟩; exact ⟨n, hn, d, (hne n hn).symm ▸ hd, hp⟩
  have hT : tried fuel (ℓ ++ [e]) κ = tried fuel ℓ κ := by
    unfold tried
    refine Finset.filter_congr fun n hn ↦ ?_
    rw [hne n (Finset.mem_range.mp hn)]
  have hS' := propext hS
  unfold powTerm
  rw [hT, hS']

/-- **A position's term is a martingale** at a fresh nonce input of it. -/
theorem powTerm_step (hb : bits ≤ 64) (hfuel : fuel ≤ 2 ^ 64) {ℓ : Log}
    {κ : PowKey} (hκ : KeyOk κ) {n0 : ℕ} (hn0 : n0 < fuel)
    (ht : lookF ℓ (nonceInput κ.1 κ.2 n0) = none) :
    (∑ u, powTerm bits fuel (ℓ ++ [.inr (nonceInput κ.1 κ.2 n0, u)]) κ) / Fintype.card KeccakState ≤
      powTerm bits fuel ℓ κ := by
  set t := nonceInput κ.1 κ.2 n0
  by_cases hs : Solved bits fuel ℓ κ
  · refine avg_le_of_le fun u ↦ ?_
    have hs' : Solved bits fuel (ℓ ++ [.inr (t, u)]) κ := by
      obtain ⟨n, hn, d, hd, hp⟩ := hs
      exact ⟨n, hn, d, lookF_append_of_some hd _, hp⟩
    simp [powTerm, hs']
  · have hl : ∀ u, ∀ n < fuel, n ≠ n0 →
        lookF (ℓ ++ [.inr (t, u)]) (nonceInput κ.1 κ.2 n) = lookF ℓ (nonceInput κ.1 κ.2 n) :=
      fun u n hn hne ↦ lookF_append_inr_of_ne (fun h ↦ hne (nonceInput_inj hκ hκ
        (by omega) (by omega) h).2) u
    have hT : ∀ u, tried fuel (ℓ ++ [.inr (t, u)]) κ = insert n0 (tried fuel ℓ κ) := by
      intro u
      ext n
      simp only [tried, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
      by_cases hnn : n = n0
      · subst hnn
        simp [t, lookF_append_inr_self ht, hn0]
      · simp only [hnn, false_or]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [hl u n h1 hnn] at h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [hl u n h1 hnn]⟩
    have hn0T : n0 ∉ tried fuel ℓ κ := by
      simp only [tried, Finset.mem_filter, not_and, not_not]
      intro _
      exact ht
    have hcard : (tried fuel ℓ κ).card < fuel := by
      have hsub : insert n0 (tried fuel ℓ κ) ⊆ Finset.range fuel := by
        intro n hn
        rcases Finset.mem_insert.mp hn with rfl | hn
        · exact Finset.mem_range.mpr hn0
        · exact (Finset.mem_filter.mp hn).1
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hn0T, Finset.card_range] at this
      omega
    have hpt : ∀ u, powTerm bits fuel (ℓ ++ [.inr (t, u)]) κ =
        ind (powOk bits (Keccak.lane u 2) = false) *
          missProb bits ^ (fuel - ((tried fuel ℓ κ).card + 1)) := by
      intro u
      have hS : Solved bits fuel (ℓ ++ [.inr (t, u)]) κ ↔
          powOk bits (Keccak.lane u 2) = true := by
        constructor
        · rintro ⟨n, hn, d, hd, hp⟩
          by_cases hnn : n = n0
          · subst hnn
            rw [lookF_append_inr_self ht] at hd
            cases hd; exact hp
          · exact absurd ⟨n, hn, d, by rwa [hl u n hn hnn] at hd, hp⟩ hs
        · intro hp
          exact ⟨n0, hn0, u, lookF_append_inr_self ht u, hp⟩
      unfold powTerm
      rw [hT u, Finset.card_insert_of_notMem hn0T]
      by_cases hp : powOk bits (Keccak.lane u 2) = true
      · simp [hS.mpr hp, hp, ind]
      · have hf : powOk bits (Keccak.lane u 2) = false := by simpa using hp
        simp [mt hS.mp hp, hf, ind]
    simp only [hpt]
    rw [← Finset.sum_mul, ENNReal.div_eq_inv_mul, ← mul_assoc, ← ENNReal.div_eq_inv_mul,
      avg_miss_eq hb]
    unfold powTerm
    simp only [hs, ↓reduceIte]
    rw [← pow_succ']
    exact le_of_eq (by congr 1; omega)

/-- **The potential's step at the permutation**: a fresh query raises it by at most
`(1 - 2^-bits)^fuel` in expectation. -/
theorem powPot_stepF (hb : bits ≤ 64) (hfuel : fuel ≤ 2 ^ 64) {ℓ : Log}
    {t : KeccakState} (ht : lookF ℓ t = none) :
    (∑ u, powPot bits fuel (ℓ ++ [.inr (t, u)])) / Fintype.card KeccakState ≤
      powPot bits fuel ℓ + missProb bits ^ fuel := by
  classical
  -- the terms of the positions other than `t`'s do not move
  have hother : ∀ u κ, (∀ n < fuel, nonceInput κ.1 κ.2 n ≠ t) →
      powTerm bits fuel (ℓ ++ [.inr (t, u)]) κ = powTerm bits fuel ℓ κ := fun u κ hne ↦
    powTerm_append_of_ne fun n hn ↦ lookF_append_inr_of_ne (hne n hn) u
  have havg : ∀ (K : Finset PowKey), (∀ κ ∈ K, ∀ n < fuel, nonceInput κ.1 κ.2 n ≠ t) →
      (∑ u, ∑ κ ∈ K, powTerm bits fuel (ℓ ++ [.inr (t, u)]) κ) / Fintype.card KeccakState =
        ∑ κ ∈ K, powTerm bits fuel ℓ κ := by
    intro K hK
    rw [Finset.sum_comm, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun κ hκ ↦ ?_
    simp only [hother _ κ (hK κ hκ)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm, ← mul_assoc,
      ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
      one_mul]
  rcases hk : keyOf fuel t with _ | κ0
  · -- `t` is no nonce input below `fuel`
    have hkeys : ∀ u, keys fuel (ℓ ++ [.inr (t, u)]) = keys fuel ℓ := by
      intro u; ext κ; simp [keys, fIns_append_inr, hk]
    have hne : ∀ κ ∈ keys fuel ℓ, ∀ n < fuel, nonceInput κ.1 κ.2 n ≠ t := by
      intro κ hκ n hn he
      obtain ⟨κ', -, hκ'⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hκ)
      obtain ⟨-, hκok, -, -⟩ := keyOf_spec hκ'
      rw [← he, keyOf_nonceInput hfuel hκok hn] at hk
      cases hk
    simp only [powPot, hkeys]
    rw [havg _ hne]
    exact le_self_add
  · obtain ⟨n0, hκ0, hn0, rfl⟩ := keyOf_spec hk
    have hkeys : ∀ u, keys fuel (ℓ ++ [.inr (nonceInput κ0.1 κ0.2 n0, u)]) =
        insert κ0 (keys fuel ℓ) := by
      intro u; ext κ; simp [keys, fIns_append_inr, hk, eq_comm]
    have hne : ∀ κ ∈ keys fuel ℓ, κ ≠ κ0 → ∀ n < fuel, nonceInput κ.1 κ.2 n ≠
        nonceInput κ0.1 κ0.2 n0 := by
      intro κ hκ hκne n hn he
      obtain ⟨t', -, hκ'⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hκ)
      obtain ⟨-, hκok, -, -⟩ := keyOf_spec hκ'
      exact hκne (nonceInput_inj hκok hκ0 (by omega) (by omega) he).1
    set T := nonceInput κ0.1 κ0.2 n0
    simp only [powPot, hkeys]
    have hstep0 := powTerm_step hb hfuel hκ0 hn0 ht
    by_cases hmem : κ0 ∈ keys fuel ℓ
    · simp only [Finset.insert_eq_of_mem hmem]
      have e1 : (∑ u, ∑ κ ∈ keys fuel ℓ, powTerm bits fuel (ℓ ++ [.inr (T, u)]) κ) =
          (∑ u, powTerm bits fuel (ℓ ++ [.inr (T, u)]) κ0) +
            ∑ u, ∑ κ ∈ (keys fuel ℓ).erase κ0, powTerm bits fuel (ℓ ++ [.inr (T, u)]) κ := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun u _ ↦ (Finset.add_sum_erase _ _ hmem).symm
      rw [e1, ENNReal.add_div,
        havg _ fun κ hκ ↦ hne κ (Finset.mem_of_mem_erase hκ) (Finset.ne_of_mem_erase hκ)]
      refine (add_le_add hstep0 le_rfl).trans ?_
      rw [Finset.add_sum_erase _ _ hmem]
      exact le_self_add
    · have e1 : (∑ u, ∑ κ ∈ insert κ0 (keys fuel ℓ), powTerm bits fuel (ℓ ++ [.inr (T, u)]) κ) =
          (∑ u, powTerm bits fuel (ℓ ++ [.inr (T, u)]) κ0) +
            ∑ u, ∑ κ ∈ keys fuel ℓ, powTerm bits fuel (ℓ ++ [.inr (T, u)]) κ := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun u _ ↦ Finset.sum_insert hmem
      rw [e1, ENNReal.add_div, havg _ fun κ hκ ↦ hne κ hκ fun h ↦ hmem (h ▸ hκ)]
      have hnew : powTerm bits fuel ℓ κ0 ≤ missProb bits ^ fuel := by
        have hT : tried fuel ℓ κ0 = ∅ := by
          refine Finset.filter_false_of_mem fun n hn hl ↦ hmem ?_
          obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hl
          refine List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨nonceInput κ0.1 κ0.2 n, ?_,
            keyOf_nonceInput hfuel hκ0 (Finset.mem_range.mp hn)⟩)
          obtain ⟨i, hi, hei, -⟩ := (lookF_eq_some_iff ℓ _ v).mp hv
          exact mem_fIns_of_getElem hi hei
        unfold powTerm
        split
        · exact bot_le
        · rw [hT, Finset.card_empty, Nat.sub_zero]
      rw [add_comm]
      exact add_le_add le_rfl (hstep0.trans hnew)

/-- A hash query changes the potential not at all. -/
theorem powPot_append_inl (ℓ : Log) (e : Bytes × Digest) :
    powPot bits fuel (ℓ ++ [.inl e]) = powPot bits fuel ℓ := by
  have hk : keys fuel (ℓ ++ [.inl e]) = keys fuel ℓ := by
    simp [keys, fIns_append_inl]
  simp only [powPot, hk]
  refine Finset.sum_congr rfl fun κ _ ↦ powTerm_append_of_ne fun n _ ↦ lookF_append_inl ℓ e _

end Step

/-! ## Failure of the honest prover -/

section Failure

variable {F : KeccakState → Option KeccakState}

/-- A proof-of-work step's third lane, in `Option`, is the answer's at the position's nonce
input. -/
theorem absorbNonce_option' {sp : Sponge} {n : ℕ} {r : UInt64 × Sponge}
    (h : absorbNonce F sp (nonceOf n) = some r) :
    ∃ c ps u, F (nonceInput c ps n) = some u ∧ r.1 = Keccak.lane u 2 ∧ r.2.pending = [] ∧
      (if sp.pending.length = 4 then ps = [] ∧ ∃ v, F (duplexInput sp) = some v ∧ c = capOf v
        else ps = sp.pending ∧ c = capOf sp.state) := by
  obtain ⟨sp', ha, u, hu, rfl⟩ := (absorbNonce_option _ _ _ _).mp h
  rw [absorb_option] at ha
  split at ha
  · rename_i h4
    obtain ⟨v, hv, rfl⟩ := ha
    refine ⟨capOf v, [], u, ?_, rfl, rfl, by simp [h4, hv]⟩
    rw [duplexInput_eq] at hu
    exact hu
  · rename_i h4
    subst ha
    refine ⟨capOf sp.state, sp.pending, u, ?_, rfl, rfl, by simp [h4]⟩
    rw [duplexInput_eq] at hu
    exact hu

theorem searchM_eq_some_none {bits : ℕ} {sp : Sponge} :
    ∀ (count n : ℕ), searchM F bits sp n count = some none →
      ∀ j, n ≤ j → j < n + count →
        ∃ r, absorbNonce F sp (nonceOf j) = some r ∧ powOk bits r.1 = false
  | 0, _, _ => fun _ h1 h2 ↦ by omega
  | count + 1, n, h => by
    change (absorbNonce F sp (LeanVM.Prover.nonceOf n)).bind _ = _ at h
    obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · rename_i hp
      intro j hj1 hj2
      rcases Nat.eq_or_lt_of_le hj1 with rfl | hlt
      · exact ⟨r, hr, by simpa using hp⟩
      · exact searchM_eq_some_none count (n + 1) h j hlt (by omega)

theorem findNonceM_eq_some_none {bits : ℕ} {sp : Sponge} {fuel : ℕ}
    (h : findNonceM F bits sp fuel = some none) :
    ∀ n < fuel, ∃ r, absorbNonce F sp (nonceOf n) = some r ∧ powOk bits r.1 = false := by
  unfold findNonceM at h
  exact fun n hn ↦ searchM_eq_some_none fuel 0 h n (Nat.zero_le n) (by omega)

/-- The honest prover's sponge between its moves: at most four scalars waiting, each of tag
`1`. -/
def ProverSp (sp : Sponge) : Prop := sp.pending.length ≤ 4 ∧ ∀ e ∈ sp.pending, e.2 = 1

/-- A squeeze keeps the honest prover's sponge. -/
theorem proverSp_squeeze {sp : Sponge} (hsp : ProverSp sp) {r : E × Sponge}
    (hr : squeeze F sp = some r) : ProverSp r.2 := by
  rcases hg : sp.ground with _ | c
  · obtain ⟨u, -, rfl⟩ := (squeeze_option _ hg _).mp hr
    exact ⟨by simp, by simp⟩
  · rw [squeeze_ground _ hg] at hr
    cases hr
    exact hsp

theorem proverSp_absorb {sp sp' : Sponge} (hsp : ProverSp sp) {x : E}
    (ha : Compile.absorb (m := Option) F sp x dsObserve = some sp') : ProverSp sp' := by
  rw [absorb_option] at ha
  split at ha
  · obtain ⟨v, -, rfl⟩ := ha
    exact ⟨by simp, by simp [dsObserve]⟩
  · rename_i h4
    subst ha
    refine ⟨by simp; have := hsp.1; omega, fun e he ↦ ?_⟩
    rcases List.mem_append.mp he with he | he
    · exact hsp.2 e he
    · rw [List.mem_singleton] at he; subst he; rfl

/-- The honest strategy's moves along a history: every scalar the history reads is the one `S`
sends at the history before it, and every word it commits the one `S` commits there. The
challenges and the openings' rows are anything. -/
def _root_.LeanVM.Protocol.Compile.Strategy.Follows (S : Strategy) (h : List Ev) : Prop :=
  ∀ l e, l ++ [e] <+: h → (∀ x, e = .read x → x = S.msg l) ∧
    (∀ ht w W, e = .commit ht w W → W = S.word l)

theorem _root_.LeanVM.Protocol.Compile.Strategy.follows_nil (S : Strategy) : S.Follows [] := by
  intro l e he
  have := he.length_le
  simp at this

/-- One more event that is `S`'s move at the history, or no move of the prover's. -/
theorem _root_.LeanVM.Protocol.Compile.Strategy.Follows.snoc {S : Strategy} {h : List Ev}
    (hf : S.Follows h) {e : Ev}
    (hread : ∀ x, e = .read x → x = S.msg h)
    (hcommit : ∀ ht w W, e = .commit ht w W → W = S.word h) : S.Follows (h ++ [e]) := by
  intro l e' he'
  rcases List.prefix_concat_iff.mp he' with heq | hp
  · obtain ⟨rfl, he⟩ := List.append_inj' heq rfl
    obtain rfl : e' = e := by simpa using he
    exact ⟨hread, hcommit⟩
  · exact hf l e' hp

/-- **The prover fails only at a proof of work.** If the honest prover, run with the queries
answered in `Option`, fails, then some proof-of-work search along the program fails, at a sponge
the honest prover keeps, at a history on which the prover made its strategy's moves. -/
theorem proveFromM_eq_some_none {H : Bytes → Option Digest} (S : Strategy) (fuel : ℕ)
    {P : VerifierProgram Bool} :
    ∀ (p : VerifierProgram Bool) (sp : Sponge) (h : List Ev) (cs : List Tree), P.after h = some p →
      ProverSp sp → S.Follows h → proveFromM H F S fuel p sp h cs = some none →
      ∃ h' bits k sp', P.after h' = some (.grind bits k) ∧ S.Follows h' ∧ ProverSp sp' ∧
        findNonceM F bits sp' fuel = some none
  | .ret _, _, _, _, _, _, _, hp => by cases hp
  | .fail, _, _, _, _, _, _, hp => by cases hp
  | .read k, sp, h, cs, ha, hsp, hfo, hp => by
    have ha' := after_read_step ha (S.msg h)
    change (Compile.absorb F sp _ _).bind _ = _ at hp
    obtain ⟨sp', hsp', hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
    rcases r with _ | _
    · exact proveFromM_eq_some_none S fuel _ sp' _ _ ha' (proverSp_absorb hsp hsp')
        (hfo.snoc (fun x hx ↦ by cases hx; rfl) (fun _ _ _ hx ↦ by cases hx)) hr
    · cases hp
  | .sample k, sp, h, cs, ha, hsp, hfo, hp => by
    change (squeeze F sp).bind _ = _ at hp
    obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
    exact proveFromM_eq_some_none S fuel _ _ _ _ (after_sample_step ha _)
      (proverSp_squeeze hsp hr) (hfo.snoc (fun _ hx ↦ by cases hx) (fun _ _ _ hx ↦ by cases hx)) hp
  | .grind bits k, sp, h, cs, ha, hsp, hfo, hp => by
    have ha' := after_grind_step ha
    change (findNonceM F bits sp fuel).bind _ = _ at hp
    obtain ⟨o, ho, hp⟩ := Option.bind_eq_some_iff.mp hp
    rcases o with _ | n
    · exact ⟨h, bits, k, sp, ha, hfo, hsp, ho⟩
    · change (absorbNonce F sp n).bind _ = _ at hp
      obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
      obtain ⟨t, ht, hp⟩ := Option.bind_eq_some_iff.mp hp
      have hsp' : ProverSp r.2 := by
        obtain ⟨sp', -, u, -, rfl⟩ := (absorbNonce_option _ _ _ _).mp hr
        exact ⟨by simp, by simp⟩
      rcases t with _ | _
      · exact proveFromM_eq_some_none S fuel _ _ _ _ ha' hsp'
          (hfo.snoc (fun _ hx ↦ by cases hx) (fun _ _ _ hx ↦ by cases hx)) ht
      · cases hp
  | .commit ht w k, sp, h, cs, ha, hsp, hfo, hp => by
    have ha' := after_commit_step ha (S.word h)
    change (buildTreeWithHash H ht (S.word h)).bind _ = _ at hp
    obtain ⟨tree, -, hp⟩ := Option.bind_eq_some_iff.mp hp
    change (Compile.absorb F sp _ _).bind _ = _ at hp
    obtain ⟨sp0, h0, hp⟩ := Option.bind_eq_some_iff.mp hp
    change (Compile.absorb F sp0 _ _).bind _ = _ at hp
    obtain ⟨sp1, h1, hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
    rcases r with _ | _
    · exact proveFromM_eq_some_none S fuel _ sp1 _ _ ha'
        (proverSp_absorb (proverSp_absorb hsp h0) h1)
        (hfo.snoc (fun _ hx ↦ by cases hx) (fun _ _ _ hx ↦ by cases hx; rfl)) hr
    · cases hp
  | .query i ps k, sp, h, cs, ha, hsp, hfo, hp => by
    simp only [proveFromM] at hp
    split at hp
    · cases hp
    · rename_i tree hc
      have ha' := after_query_step ha (ps.map fun q ↦ tree.word (q % 2 ^ tree.height))
      obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
      rcases r with _ | _
      · exact proveFromM_eq_some_none S fuel _ sp _ _ ha' hsp
          (hfo.snoc (fun _ hx ↦ by cases hx) (fun _ _ _ hx ↦ by cases hx)) hr
      · cases hp

end Failure

/-! ## The honest prover against the random oracles -/

/-- **The honest prover of the random-oracle model**: seed the sponge by `σ`, then run the honest
prover with every hash and permutation a query; the empty proof if a proof-of-work search
fails. -/
def honestComp (σ : Seed) (P : VerifierProgram Bool) (S : Strategy) (fuel : ℕ) :
    OracleComp KeccakCalls Proof := do
  let seed ← σ.run callKeccak256 callKeccakF1600
  let r ← proveM callKeccak256 callKeccakF1600 P S seed fuel
  pure (r.getD ⟨[], []⟩)

/-- The honest prover makes at most `|σ.hs| + 1 + n · proverFactor height fuel` queries. -/
theorem isTotalQueryBound_honestComp {σ : Seed} {P : VerifierProgram Bool} {height n : ℕ}
    (hP : P.CostLE height n) (S : Strategy) (fuel : ℕ) :
    IsTotalQueryBound (honestComp σ P S fuel) (σ.hs.length + 1 + n * proverFactor height fuel) :=
  isTotalQueryBound_bind (isTotalQueryBound_seedRun σ) fun seed ↦ by
    rw [← Nat.add_zero (n * _)]
    exact isTotalQueryBound_bind (isTotalQueryBound_proveM hP S seed fuel) fun _ ↦
      isTotalQueryBound_pure' _ 0

/-- A challenge that fails a proof of work of `b` bits fails one of `B ≥ b` bits. -/
theorem powOk_false_mono {b B : ℕ} {c : E} (hbB : b ≤ B) (h : powOk b c = false) :
    powOk B c = false := by
  unfold powOk at h ⊢
  simp only [decide_eq_false_iff_not] at h ⊢
  intro hc
  exact h (Nat.mod_eq_zero_of_dvd
    (Nat.dvd_trans (Nat.pow_dvd_pow 2 hbB) (Nat.dvd_of_mod_eq_zero hc)))

/-- **The final inequality.** On every reachable outcome of the logged experiment in which the
verifier rejects the honest prover's proof, the potential of the final log is at least `1`. -/
theorem one_le_powPot {σ : Seed} {P : VerifierProgram Bool} {S : Strategy} {bits fuel : ℕ}
    (hfuel : fuel ≤ 2 ^ 64) (hfuel0 : fuel ≠ 0)
    (hP : GrindThenSample P)
    (hc : ∀ chal, runI P S chal = some true) (hs : ∀ chal, shapedI P S chal)
    (hg : ∀ h b k, P.after h = some (.grind b k) → S.Follows h → b ≤ bits)
    {z : (Proof × Bool) × Log} (hz : z ∈ support (logExperiment (honestComp σ P S fuel)
      (verifierComp σ P))) (hrej : z.1.2 = false) :
    1 ≤ powPot bits fuel z.2 := by
  set ℓ := z.2
  have h := (simulateQ_look_of_mem_support _ [] z hz).2 ℓ (List.prefix_refl _)
  rw [simulateQ_bind] at h
  obtain ⟨π, hA, h⟩ := Option.bind_eq_some_iff.mp h
  rw [simulateQ_map] at h
  obtain ⟨b, hb, hπb⟩ := Option.map_eq_some_iff.mp h
  have hzb : b = false := by rw [← hrej, ← hπb]
  subst hzb
  -- The prover's run against the log.
  simp only [honestComp, simulateQ_bind, simulateQ_seedRun, simulateQ_proveM,
    simulateQ_pure] at hA
  change (σ.run (lookH ℓ) (lookF ℓ)).bind (fun seed ↦ (proveM (lookH ℓ) (lookF ℓ) P S seed
    fuel).bind fun r ↦ some (r.getD ⟨[], []⟩)) = some π at hA
  obtain ⟨seed, hseed, hA⟩ := Option.bind_eq_some_iff.mp hA
  obtain ⟨r, hr, hA⟩ := Option.bind_eq_some_iff.mp hA
  cases r with
  | some π' =>
    -- The prover succeeded: the verifier accepts, a contradiction.
    exfalso
    cases hA
    let Ht : Bytes → Digest := fun x ↦ (lookH ℓ x).getD default
    let Ft : KeccakState → KeccakState := fun s ↦ (lookF ℓ s).getD default
    have hH : ∀ x u, lookH ℓ x = some u → Ht x = u := fun x u hx ↦ by simp [Ht, hx]
    have hF : ∀ s u, lookF ℓ s = some u → Ft s = u := fun s u hs ↦ by simp [Ft, hs]
    have hseed' : σ.run (m := Id) Ht Ft = seed := by
      have := simulateQ_id_of_look ℓ Ht Ft hH hF (σ.run callKeccak256 callKeccakF1600) seed
        (by rw [simulateQ_seedRun]; exact hseed)
      rwa [simulateQ_seedRun] at this
    have hπ : prove Ht Ft P S seed fuel = some π' := by
      have := simulateQ_id_of_look ℓ Ht Ft hH hF (proveM callKeccak256 callKeccakF1600 P S seed fuel) (some π')
        (by rw [simulateQ_proveM]; exact hr)
      rw [simulateQ_proveM] at this
      rw [← proveM_id]
      exact this
    have hb' : simulateQ (lookImpl ℓ) (verifierComp σ P π') = some false := hb
    have hv := simulateQ_id_of_look ℓ Ht Ft hH hF (verifierComp σ P π') false hb'
    rw [simulateQ_verify] at hv
    have hacc := runProof_prove Ht Ft P S seed fuel hP hc hs hπ
    have hv' : runProofWithHash (m := Id) Ht Ft P (σ.run (m := Id) Ht Ft) π' = false := hv
    rw [hseed', hacc] at hv'
    cases hv'
  | none =>
    -- The prover failed: some proof-of-work search failed.
    have hr' : proveFromM (lookH ℓ) (lookF ℓ) S fuel P ⟨seed, [], none⟩ [] [] = some none := by
      change (proveFromM (lookH ℓ) (lookF ℓ) S fuel P ⟨seed, [], none⟩ [] []).bind _ = _ at hr
      obtain ⟨t, ht, hr⟩ := Option.bind_eq_some_iff.mp hr
      cases t with
      | none => exact ht
      | some _ => cases hr
    obtain ⟨h', b', k, sp, ha, hfo, hsp, hf⟩ :=
      proveFromM_eq_some_none S fuel P ⟨seed, [], none⟩ [] [] (VerifierProgram.after.eq_1 P)
          ⟨by simp, by simp⟩ S.follows_nil hr'
    have hbB := hg h' b' k ha hfo
    have hall' := findNonceM_eq_some_none hf
    have hall : ∀ n < fuel, ∃ r, absorbNonce (lookF ℓ) sp (nonceOf n) = some r ∧
        powOk bits r.1 = false := fun n hn ↦ by
      obtain ⟨r, hr, hp⟩ := hall' n hn
      refine ⟨r, hr, ?_⟩
      by_contra hB
      have := powOk_mono hbB (by simpa using hB)
      rw [hp] at this
      cases this
    -- The position of the search, the same for every nonce.
    obtain ⟨κ, hκ, hnon⟩ : ∃ κ : PowKey, KeyOk κ ∧ ∀ n < fuel, ∃ u,
        lookF ℓ (nonceInput κ.1 κ.2 n) = some u ∧ powOk bits (Keccak.lane u 2) = false := by
      by_cases h4 : sp.pending.length = 4
      · obtain ⟨r0, hr0, -⟩ := hall 0 (Nat.pos_of_ne_zero hfuel0)
        obtain ⟨c0, ps0, u0, -, -, -, hif⟩ := absorbNonce_option' hr0
        simp only [h4, ↓reduceIte] at hif
        obtain ⟨-, v, hv, -⟩ := hif
        refine ⟨(capOf v, []), ⟨by simp, by simp⟩, fun n hn ↦ ?_⟩
        obtain ⟨r, hr, hp⟩ := hall n hn
        obtain ⟨c, ps, u, hu, hru, -, hif⟩ := absorbNonce_option' hr
        simp only [h4, ↓reduceIte] at hif
        obtain ⟨rfl, v', hv', rfl⟩ := hif
        rw [hv] at hv'
        cases hv'
        exact ⟨u, hu, by rw [← hru]; exact powOk_false_mono hb'le hp⟩
      · refine ⟨(capOf sp.state, sp.pending), ⟨by dsimp only; have := hsp.1; omega, hsp.2⟩,
          fun n hn ↦ ?_⟩
        obtain ⟨r, hr, hp⟩ := hall n hn
        obtain ⟨c, ps, u, hu, hru, -, hif⟩ := absorbNonce_option' hr
        simp only [h4, ↓reduceIte] at hif
        obtain ⟨rfl, rfl⟩ := hif
        exact ⟨u, hu, by rw [← hru]; exact powOk_false_mono hb'le hp⟩
    -- Its term is `1`.
    have hS : ¬ Solved bits fuel ℓ κ := by
      rintro ⟨n, hn, d, hd, hp⟩
      obtain ⟨d', hd', hp'⟩ := hnon n hn
      rw [hd'] at hd
      cases hd
      rw [hp'] at hp
      cases hp
    have hT : (tried fuel ℓ κ).card = fuel := by
      have : tried fuel ℓ κ = Finset.range fuel := by
        refine Finset.filter_true_of_mem fun n hn ↦ ?_
        obtain ⟨d, hd, -⟩ := hnon n (Finset.mem_range.mp hn)
        simp [hd]
      rw [this, Finset.card_range]
    have hterm : powTerm bits fuel ℓ κ = 1 := by
      simp [powTerm, hS, hT]
    have hmem : κ ∈ keys fuel ℓ := by
      obtain ⟨u, hu, -⟩ := hnon 0 (Nat.pos_of_ne_zero hfuel0)
      obtain ⟨i, hi, hei, -⟩ := (lookF_eq_some_iff ℓ _ u).mp hu
      exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨_, mem_fIns_of_getElem hi hei,
        keyOf_nonceInput hfuel hκ (Nat.pos_of_ne_zero hfuel0)⟩)
    rw [← hterm]
    exact Finset.single_le_sum (fun _ _ ↦ bot_le) hmem

/-- **Completeness in the random-oracle model.** For a verifier program `P` whose proofs of work
are each followed at once by a challenge and ask for at most `bits ≤ 64` bits wherever the prover
has made the strategy's moves (`Strategy.Follows`), a strategy `S` that wins every interactive run of `P` with
well-shaped words, the seeding `σ`, and a fuel of at most `2^64` nonces: with `Q` the queries of
the honest prover and the verifier together, the verifier rejects the honest prover's proof with
probability at most `Q · (1 - 2^-bits)^fuel`. -/
theorem romComplete (P : VerifierProgram Bool) (S : Strategy) (σ : Seed) {bits fuel height n : ℕ}
    (hb : bits ≤ 64) (hfuel : fuel ≤ 2 ^ 64) (hPg : GrindThenSample P)
    (hg : ∀ h b k, P.after h = some (.grind b k) → S.Follows h → b ≤ bits)
    (hc : ∀ chal, runI P S chal = some true) (hs : ∀ chal, shapedI P S chal)
    (hP : P.CostLE height n) :
    Pr{let z ← romExperiment (honestComp σ P S fuel) (verifierComp σ P)}[z.1.2 = false] ≤
      ((σ.hs.length + 1 + n * proverFactor height fuel + (σ.hs.length + 1 + n / 4) : ℕ) :
        ℝ≥0∞) * missProb bits ^ fuel := by
  set QA := σ.hs.length + 1 + n * proverFactor height fuel
  set QV := σ.hs.length + 1 + n / 4
  by_cases hfuel0 : fuel = 0
  · -- no fuel: the bound is at least one
    subst hfuel0
    refine (prEvent_le_one _).trans ?_
    rw [pow_zero, mul_one]
    exact_mod_cast (show 1 ≤ QA + QV by omega)
  have hA := isTotalQueryBound_honestComp (σ := σ) hP S fuel
  have hV : ∀ π, IsTotalQueryBound (verifierComp σ P π) QV :=
    isTotalQueryBound_verifierComp hP σ
  rw [prEvent_romExperiment_eq_logExperiment _ _ fun r _ ↦ r.2 = false]
  have hstep : LogFreshStepBound (powPot bits fuel) (missProb bits ^ fuel) := by
    rw [logFreshStepBound_iff]
    refine ⟨fun ℓ x _ ↦ ?_, fun ℓ s hs' ↦ ?_⟩
    · simp only [powPot_append_inl]
      exact (avg_le_of_le fun _ ↦ le_rfl).trans le_self_add
    · exact powPot_stepF hb hfuel ((lookR_eq_none_iff ℓ s).mpr hs')
  have h := prEvent_run_loggedRO_le_of_freshStepBound hstep _ (QA + QV)
    (isTotalQueryBound_bind hA fun a ↦ (isQueryBound_map_iff (verifierComp σ P a) _ QV _ _).mpr
      (hV a)) [] (fun r _ ↦ r.2 = false)
    (fun z hz hrej ↦ one_le_powPot hfuel hfuel0 hPg hc hs hg hz hrej)
  rw [powPot_nil, zero_add] at h
  exact h

end
end LeanVM.Protocol.Compile.Rom
