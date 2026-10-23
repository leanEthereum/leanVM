/-
  LeanVM.Protocol.Compile.Rom.Complete

  Completeness of the compiled verifier in the random-oracle model: the honest prover, run
  against the random oracle, produces a proof the compiled verifier rejects with negligible
  probability; its only failure is a proof-of-work search that runs out of fuel.
-/

module

public import LeanVM.Protocol.Compile.Rom.Prover
public import LeanVM.Protocol.Compile.Rom.Step
public import Mathlib.Analysis.Complex.Exponential

/-!
# Completeness in the random-oracle model

Let `P : Prog Bool` be a verifier program, `S` a strategy that wins every interactive run of `P`
with well-shaped words, and `σ` the seeding. The honest prover of the random-oracle model
(`honestComp σ P S fuel`) seeds the chain and runs `proveM queryH`; when a proof-of-work search
finds no nonce below `fuel`, it outputs the empty proof. In the experiment `romExperiment` the
honest prover and then the compiled verifier run against one lazily sampled random oracle.

`romComplete`: if every proof of work of `P` asks for `bits ∈ [1, 64]` bits, the verifier rejects
with probability at most

  `Q · ((1 - 2^-bits)^fuel + Q / 2^256)`,

`Q` the queries of the prover and the verifier together.

## The proof

On every outcome in which the honest prover returns a proof, the verifier accepts: both runs read
their hashes from the oracle's final log, so they are the runs of the pure prover and verifier at
a hash function that agrees with the log (`simulateQ_id_of_look`), and the pure verifier accepts
the pure prover's proof for every hash function (`runProof_prove`).

The prover fails only at a proof-of-work search, at some chain state `cv`, whose base
`H(cv ‖ (0, 3))` the log answers and whose `fuel` nonces all fail. A potential on the log
(`powPot`) sums, over the entries whose input is a proof-of-work base `u`, the probability
`(1 - 2^-bits)^(untried)` that the nonces of `u` below `fuel` not yet in the log all fail, or `0`
once one passes (`powTerm`). It is `1` on a log in which the prover failed (`one_le_powPot`). A
fresh query keeps an old term a supermartingale (a nonce of `u` fails with probability exactly
`1 - 2^-bits`, `avg_miss_eq`), and a fresh base `u` adds at most `(1 - 2^-bits)^fuel`, plus the
probability `|ℓ| / 2^256` that the log already holds a nonce input of `u`. The potential engine
of `LeanVM.Protocol.ToVCVio.Rom` turns this into the bound.
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Blake2sHash LeanVM.Protocol
open LeanVM.Protocol.Rom OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/-! ## The proof-of-work predicate, exactly -/

/-- Exactly `2^(64 - b)` 64-bit numbers are divisible by `2^b`, for `b ≤ 64`. -/
theorem card_filter_mod_pow_eq_zero {b : ℕ} (hb : b ≤ 64) :
    (Finset.univ.filter fun i : Fin (2 ^ 64) ↦ i.val % 2 ^ b = 0).card = 2 ^ (64 - b) := by
  refine le_antisymm ((card_filter_mod_pow_eq_zero_le b).trans_eq (by rw [min_eq_left hb])) ?_
  have h64 : 2 ^ 64 = 2 ^ (64 - b) * 2 ^ b := by rw [← pow_add, Nat.sub_add_cancel hb]
  let f : Fin (2 ^ (64 - b)) → Fin (2 ^ 64) := fun j ↦ ⟨j.val * 2 ^ b, by
    rw [h64]; exact (Nat.mul_lt_mul_right (Nat.two_pow_pos b)).mpr j.isLt⟩
  have hf : Function.Injective f := fun i j h ↦
    Fin.ext (Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos b) (congrArg Fin.val h))
  calc 2 ^ (64 - b) = (Finset.univ.map ⟨f, hf⟩).card := by simp
    _ ≤ _ := Finset.card_le_card fun x hx ↦ by
        simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk] at hx
        obtain ⟨j, rfl⟩ := hx
        simp [f]

/-- **The proof of work of a uniform digest succeeds with probability exactly `2^-b`**, for
`1 ≤ b ≤ 64`. -/
theorem sum_powOk_div_eq {b : ℕ} (hb0 : b ≠ 0) (hb : b ≤ 64) (n : E) :
    (∑ d : Digest, if powOk b n d then (1 : ℝ≥0∞) else 0) / Fintype.card Digest = 2⁻¹ ^ b := by
  have hpow : ∀ d : Digest, powOk b n d =
      decide (((challengeOf d).limb 0).toBitVec.toNat % 2 ^ b = 0) := by
    intro d
    have h0 : (challengeOf d).limb 0 = ofWords d[0] d[1] := by
      rw [challengeOf, limb_ofLimbs]; rfl
    simp only [powOk, hb0, ↓reduceIte]
    rw [h0, ← toNat_lowWord_add_highWord, lowWord_ofWords, highWord_ofWords]
  let g : K → ℝ≥0∞ := fun a ↦ if a.toBitVec.toNat % 2 ^ b = 0 then 1 else 0
  have hsum : (∑ d : Digest, if powOk b n d then (1 : ℝ≥0∞) else 0) =
      ∑ d : Digest, g ((challengeOf d).limb 0) := by
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    simp only [hpow, decide_eq_true_eq, g]
  rw [hsum, sum_challengeOf_div (fun c ↦ g (c.limb 0))]
  have hE : (∑ c : E, g (c.limb 0)) =
      (Fintype.card (K × K) : ℝ≥0∞) * ∑ a : K, g a := by
    rw [Fintype.sum_equiv limbEquiv (fun c ↦ g (c.limb 0)) (fun p ↦ g p.1) (fun _ ↦ rfl),
      Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  have hcE : (Fintype.card E : ℝ≥0∞) = (Fintype.card (K × K) : ℝ≥0∞) * Fintype.card K := by
    rw [Fintype.card_congr limbEquiv, Fintype.card_prod, Nat.cast_mul, mul_comm]
  rw [hE, hcE, ENNReal.mul_div_mul_left _ _ (by exact_mod_cast Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _), card_K]
  have hK : (∑ a : K, g a) =
      ((Finset.univ.filter fun i : Fin (2 ^ 64) ↦ i.val % 2 ^ b = 0).card : ℝ≥0∞) := by
    rw [Fintype.sum_equiv LeanVM.Protocol.finEquivK.symm g
      (fun i : Fin (2 ^ 64) ↦ if i.val % 2 ^ b = 0 then 1 else 0) (fun _ ↦ rfl)]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hK, card_filter_mod_pow_eq_zero hb]
  have h64 : (2 : ℝ≥0∞) ^ 64 = 2 ^ (64 - b) * 2 ^ b := by
    rw [← pow_add, Nat.sub_add_cancel hb]
  rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, h64, ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (by simp) (by simp), mul_comm (2 ^ (64 - b))⁻¹, mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one, ENNReal.inv_pow]

/-- The probability that one nonce fails a proof of work of `b` bits: `1 - 2^-b`. -/
noncomputable def missProb (b : ℕ) : ℝ≥0∞ := 1 - 2⁻¹ ^ b

theorem missProb_le_one (b : ℕ) : missProb b ≤ 1 := tsub_le_self

/-- **A nonce fails with probability exactly `1 - 2^-b`.** -/
theorem avg_miss_eq {b : ℕ} (hb0 : b ≠ 0) (hb : b ≤ 64) (n : E) :
    (∑ d : Digest, ind (powOk b n d = false)) / Fintype.card Digest = missProb b := by
  have hc : (Fintype.card Digest : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hct : (Fintype.card Digest : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hadd : (∑ d : Digest, ind (powOk b n d = false)) +
      (∑ d : Digest, if powOk b n d then (1 : ℝ≥0∞) else 0) = Fintype.card Digest := by
    rw [← Finset.sum_add_distrib]
    calc ∑ d : Digest, (ind (powOk b n d = false) + if powOk b n d then (1 : ℝ≥0∞) else 0)
        = ∑ _d : Digest, (1 : ℝ≥0∞) := Finset.sum_congr rfl fun d _ ↦ by
          cases powOk b n d <;> simp [ind]
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hdiv := congrArg (· / (Fintype.card Digest : ℝ≥0∞)) hadd
  simp only [ENNReal.add_div, ENNReal.div_self hc hct, sum_powOk_div_eq hb0 hb n] at hdiv
  exact ENNReal.eq_sub_of_add_eq (by simp) hdiv

/-- `(1 - 2^-b)^(2^b) ≤ e^-1 < 1/2`, over the reals. -/
theorem one_sub_pow_le_half (b : ℕ) : (1 - (1 / 2 : ℝ) ^ b) ^ (2 ^ b) ≤ 1 / 2 := by
  have hy0 : 0 ≤ 1 - (1 / 2 : ℝ) ^ b := by
    have : (1 / 2 : ℝ) ^ b ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have he : Real.exp (-1) < 1 / 2 := by
    have h2 : 1 + 1 < Real.exp 1 := Real.add_one_lt_exp one_ne_zero
    rw [Real.exp_neg, one_div]
    exact inv_strictAnti₀ (by norm_num) (by linarith)
  calc (1 - (1 / 2 : ℝ) ^ b) ^ (2 ^ b) ≤ (Real.exp (-(1 / 2 : ℝ) ^ b)) ^ (2 ^ b) :=
        pow_le_pow_left₀ hy0 (by have := Real.add_one_le_exp (-(1 / 2 : ℝ) ^ b); linarith) _
    _ = Real.exp (-1) := by
        rw [← Real.exp_nat_mul]; congr 1
        push_cast
        rw [mul_neg, ← mul_pow]; norm_num
    _ ≤ 1 / 2 := he.le

theorem missProb_eq_ofReal (b : ℕ) : missProb b = ENNReal.ofReal (1 - (1 / 2 : ℝ) ^ b) := by
  rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one, ENNReal.ofReal_pow (by norm_num)]
  rw [missProb, one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- **`2^b · k` failed nonces are as unlikely as `k` fair coins all landing tails**:
`(1 - 2^-b)^(2^b · k) ≤ 2^-k`. -/
theorem missProb_pow_le (b k : ℕ) : missProb b ^ (2 ^ b * k) ≤ 2⁻¹ ^ k := by
  rw [pow_mul]
  refine pow_le_pow_left₀ bot_le ?_ k
  rw [missProb_eq_ofReal, ← ENNReal.ofReal_pow (by
    have : (1 / 2 : ℝ) ^ b ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith)]
  calc ENNReal.ofReal ((1 - (1 / 2 : ℝ) ^ b) ^ (2 ^ b)) ≤ ENNReal.ofReal (1 / 2) :=
        ENNReal.ofReal_le_ofReal (one_sub_pow_le_half b)
    _ = 2⁻¹ := by rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num

/-! ## The proof-of-work potential -/

/-- The input of a proof-of-work base at chain state `cv`: `cv ‖ (0, 3)`. -/
def baseInput (cv : Digest) : Bytes := digestBytes cv ++ blockOf 0 3

/-- The input of the nonce `n` at the base `u`: `u ‖ (n, 4)`. -/
def nonceInput (u : Digest) (n : ℕ) : Bytes := digestBytes u ++ blockOf (nonceOf n) 4

section Pot

variable (bits fuel : ℕ)

open Classical in
/-- The nonces below `fuel` the log has tried at the base `u`. -/
noncomputable def tried (ℓ : Log) (u : Digest) : Finset ℕ :=
  (Finset.range fuel).filter fun n ↦ look ℓ (nonceInput u n) ≠ none

/-- Some nonce below `fuel` passes at the base `u`, in the log. -/
def Solved (ℓ : Log) (u : Digest) : Prop :=
  ∃ n < fuel, ∃ d, look ℓ (nonceInput u n) = some d ∧ powOk bits (nonceOf n) d = true

open Classical in
/-- The term of a base `u`: `0` once a nonce below `fuel` passed, otherwise the probability that
the nonces below `fuel` not yet tried all fail. -/
noncomputable def powTerm (ℓ : Log) (u : Digest) : ℝ≥0∞ :=
  if Solved bits fuel ℓ u then 0 else missProb bits ^ (fuel - (tried fuel ℓ u).card)

/-- **The proof-of-work potential**: the terms of the bases the log holds. -/
noncomputable def powPot (ℓ : Log) : ℝ≥0∞ :=
  (ℓ.map fun e ↦ ind (∃ cv, e.1 = baseInput cv) * powTerm bits fuel ℓ e.2).sum

theorem powTerm_le_one (ℓ : Log) (u : Digest) : powTerm bits fuel ℓ u ≤ 1 := by
  unfold powTerm
  split
  · exact zero_le_one
  · exact pow_le_one₀ bot_le (missProb_le_one bits)

theorem powPot_nil : powPot bits fuel [] = 0 := rfl

end Pot

/-! ## Encodings -/

theorem nonceOf_inj {n n' : ℕ} (hn : n < 2 ^ 64) (hn' : n' < 2 ^ 64)
    (h : nonceOf n = nonceOf n') : n = n' := by
  have h0 := congrArg (fun x : E ↦ (x.limb 0).toBitVec.toNat) h
  simp only [nonceOf, limb_ofLimbs, K.ofBits] at h0
  change (BitVec.ofNat 64 n).toNat = (BitVec.ofNat 64 n').toNat at h0
  simp only [BitVec.toNat_ofNat] at h0
  rwa [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hn'] at h0

theorem nonceInput_inj {u u' : Digest} {n n' : ℕ} (hn : n < 2 ^ 64) (hn' : n' < 2 ^ 64)
    (h : nonceInput u n = nonceInput u' n') : u = u' ∧ n = n' := by
  obtain ⟨hu, hx, -⟩ := chainInput_inj h
  exact ⟨hu, nonceOf_inj hn hn' hx⟩

theorem baseInput_ne_nonceInput (cv u : Digest) (n : ℕ) : baseInput cv ≠ nonceInput u n :=
  chain_ne_of_tag (by norm_num) (by norm_num) (by norm_num)

theorem chunk0_nonceInput (u : Digest) (n : ℕ) : chunk0 (nonceInput u n) = digestBytes u :=
  chunk0_append u _

/-! ## The step -/

section Step

variable {bits fuel : ℕ}

/-- The term of a base whose nonce inputs below `fuel` all differ from `t` does not move. -/
theorem powTerm_append_of_ne {ℓ : Log} {t : Bytes} {w : Digest}
    (hne : ∀ n < fuel, nonceInput w n ≠ t) (u : Digest) :
    powTerm bits fuel (ℓ ++ [(t, u)]) w = powTerm bits fuel ℓ w := by
  have hl : ∀ n < fuel, look (ℓ ++ [(t, u)]) (nonceInput w n) = look ℓ (nonceInput w n) :=
    fun n hn ↦ look_append_single_of_ne (hne n hn) u
  have hS : Solved bits fuel (ℓ ++ [(t, u)]) w ↔ Solved bits fuel ℓ w := by
    unfold Solved
    constructor
    · rintro ⟨n, hn, d, hd, hp⟩; exact ⟨n, hn, d, (hl n hn) ▸ hd, hp⟩
    · rintro ⟨n, hn, d, hd, hp⟩; exact ⟨n, hn, d, (hl n hn).symm ▸ hd, hp⟩
  have hT : tried fuel (ℓ ++ [(t, u)]) w = tried fuel ℓ w := by
    unfold tried
    refine Finset.filter_congr fun n hn ↦ ?_
    rw [hl n (Finset.mem_range.mp hn)]
  have hS' := propext hS
  unfold powTerm
  rw [hT, hS']

/-- **An old term is a supermartingale.** -/
theorem powTerm_step_old (hb0 : bits ≠ 0) (hb : bits ≤ 64) (hfuel : fuel ≤ 2 ^ 64) {ℓ : Log}
    {t : Bytes} (ht : look ℓ t = none) (w : Digest) :
    (∑ u, powTerm bits fuel (ℓ ++ [(t, u)]) w) / Fintype.card Digest ≤ powTerm bits fuel ℓ w := by
  by_cases hn : ∃ n0 < fuel, nonceInput w n0 = t
  · obtain ⟨n0, hn0, rfl⟩ := hn
    by_cases hs : Solved bits fuel ℓ w
    · -- Solved stays solved.
      refine avg_le_of_le fun u ↦ ?_
      have hs' : Solved bits fuel (ℓ ++ [(nonceInput w n0, u)]) w := by
        obtain ⟨n, hn, d, hd, hp⟩ := hs
        exact ⟨n, hn, d, look_append_single_of_some hd _ _, hp⟩
      have h0 : powTerm bits fuel (ℓ ++ [(nonceInput w n0, u)]) w = 0 := by
        simp [powTerm, hs']
      rw [h0]
      exact bot_le
    · have hl : ∀ u, ∀ n < fuel, n ≠ n0 →
          look (ℓ ++ [(nonceInput w n0, u)]) (nonceInput w n) = look ℓ (nonceInput w n) :=
        fun u n hn hne ↦ look_append_single_of_ne (fun h ↦ hne (nonceInput_inj
          (by omega) (by omega) h).2) u
      have hT : ∀ u, tried fuel (ℓ ++ [(nonceInput w n0, u)]) w = insert n0 (tried fuel ℓ w) := by
        intro u
        ext n
        simp only [tried, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
        by_cases hnn : n = n0
        · subst hnn
          simp [look_append_single_self ht, hn0]
        · simp only [hnn, false_or]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [hl u n h1 hnn] at h2⟩
          · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [hl u n h1 hnn]⟩
      have hn0T : n0 ∉ tried fuel ℓ w := by simp [tried, ht]
      have hcard : (tried fuel ℓ w).card < fuel := by
        have hsub : insert n0 (tried fuel ℓ w) ⊆ Finset.range fuel := by
          intro n hn
          rcases Finset.mem_insert.mp hn with rfl | hn
          · exact Finset.mem_range.mpr hn0
          · exact (Finset.mem_filter.mp hn).1
        have := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem hn0T, Finset.card_range] at this
        omega
      have hpt : ∀ u, powTerm bits fuel (ℓ ++ [(nonceInput w n0, u)]) w =
          ind (powOk bits (nonceOf n0) u = false) *
            missProb bits ^ (fuel - ((tried fuel ℓ w).card + 1)) := by
        intro u
        have hS : Solved bits fuel (ℓ ++ [(nonceInput w n0, u)]) w ↔
            powOk bits (nonceOf n0) u = true := by
          constructor
          · rintro ⟨n, hn, d, hd, hp⟩
            by_cases hnn : n = n0
            · subst hnn
              rw [look_append_single_self ht] at hd
              cases hd; exact hp
            · exact absurd ⟨n, hn, d, by rwa [hl u n hn hnn] at hd, hp⟩ hs
          · intro hp
            exact ⟨n0, hn0, u, look_append_single_self ht u, hp⟩
        unfold powTerm
        rw [hT u, Finset.card_insert_of_notMem hn0T]
        by_cases hp : powOk bits (nonceOf n0) u = true
        · simp [hS.mpr hp, hp, ind]
        · have hf : powOk bits (nonceOf n0) u = false := by simpa using hp
          simp [mt hS.mp hp, hf, ind]
      simp only [hpt]
      rw [← Finset.sum_mul, ENNReal.div_eq_inv_mul, ← mul_assoc, ← ENNReal.div_eq_inv_mul,
        avg_miss_eq hb0 hb]
      unfold powTerm
      simp only [hs, ↓reduceIte]
      rw [← pow_succ']
      exact le_of_eq (by congr 1; omega)
  · push Not at hn
    refine avg_le_of_le fun u ↦ le_of_eq ?_
    exact powTerm_append_of_ne hn u

/-- **A new base adds at most `(1 - 2^-bits)^fuel`**, plus the chance that the log already
holds one of its nonce inputs. -/
theorem powTerm_step_new {ℓ : Log} {t : Bytes} (hbase : ∃ cv, t = baseInput cv) :
    (∑ u, powTerm bits fuel (ℓ ++ [(t, u)]) u) / Fintype.card Digest ≤
      missProb bits ^ fuel + ℓ.length / Fintype.card Digest := by
  obtain ⟨cv, rfl⟩ := hbase
  have hpt : ∀ u, powTerm bits fuel (ℓ ++ [(baseInput cv, u)]) u ≤
      ind (∃ e ∈ ℓ, chunk0 e.1 = digestBytes u) + missProb bits ^ fuel := by
    intro u
    rw [powTerm_append_of_ne (fun n _ h ↦ baseInput_ne_nonceInput cv u n h.symm) u]
    by_cases hx : ∃ e ∈ ℓ, chunk0 e.1 = digestBytes u
    · rw [ind_of hx]
      exact (powTerm_le_one bits fuel ℓ u).trans le_self_add
    · rw [ind_of_not hx, zero_add]
      have hT : tried fuel ℓ u = ∅ := by
        refine Finset.filter_false_of_mem fun n _ hn ↦ hx ?_
        obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hn
        obtain ⟨i, hi, he, -⟩ := (look_eq_some_iff ℓ _ v).mp hv
        exact ⟨ℓ[i], List.getElem_mem hi, by rw [he]; exact chunk0_nonceInput u n⟩
      have hS : ¬ Solved bits fuel ℓ u := by
        rintro ⟨n, hn, d, hd, -⟩
        have : n ∈ tried fuel ℓ u := by simp [tried, hn, hd]
        rw [hT] at this
        exact absurd this (Finset.notMem_empty n)
      simp [powTerm, hS, hT]
  have hc : (Fintype.card Digest : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hct : (Fintype.card Digest : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcount : ∑ u, ind (∃ e ∈ ℓ, chunk0 e.1 = digestBytes u) ≤ ℓ.length := by
    calc ∑ u, ind (∃ e ∈ ℓ, chunk0 e.1 = digestBytes u)
        ≤ ∑ u, (ℓ.map fun e ↦ ind (chunk0 e.1 = digestBytes u)).sum :=
          Finset.sum_le_sum fun u _ ↦ ind_exists_le _ _
      _ = (ℓ.map fun e ↦ ∑ u, ind (chunk0 e.1 = digestBytes u)).sum := sum_list_sum_comm _ _
      _ ≤ ℓ.length * 1 := list_sum_le _ _ _ fun e _ ↦
          sum_ind_le_one fun u u' hu hu' ↦ digestBytes_injective (hu.symm.trans hu')
      _ = ℓ.length := mul_one _
  calc (∑ u, powTerm bits fuel (ℓ ++ [(baseInput cv, u)]) u) / Fintype.card Digest
      ≤ (∑ u, (ind (∃ e ∈ ℓ, chunk0 e.1 = digestBytes u) + missProb bits ^ fuel)) /
          Fintype.card Digest := by gcongr with u; exact hpt u
    _ = (∑ u, ind (∃ e ∈ ℓ, chunk0 e.1 = digestBytes u)) / Fintype.card Digest +
          missProb bits ^ fuel := sum_add_const_div_card (spec := HashSpec) ([] : Bytes) _ _
    _ ≤ ℓ.length / Fintype.card Digest + missProb bits ^ fuel := by gcongr
    _ = _ := add_comm _ _

/-- **The potential's step**: a fresh query raises it by at most
`(1 - 2^-bits)^fuel + |ℓ| / 2^256` in expectation. -/
theorem powPot_step (hb0 : bits ≠ 0) (hb : bits ≤ 64) (hfuel : fuel ≤ 2 ^ 64) {ℓ : Log}
    {t : Bytes} (ht : look ℓ t = none) :
    (∑ u, powPot bits fuel (ℓ ++ [(t, u)])) / Fintype.card Digest ≤
      powPot bits fuel ℓ + (missProb bits ^ fuel + ℓ.length / Fintype.card Digest) := by
  set c := (Fintype.card Digest : ℝ≥0∞)
  have hsplit : ∀ u, powPot bits fuel (ℓ ++ [(t, u)]) =
      (ℓ.map fun e ↦ ind (∃ cv, e.1 = baseInput cv) * powTerm bits fuel (ℓ ++ [(t, u)]) e.2).sum +
        ind (∃ cv, t = baseInput cv) * powTerm bits fuel (ℓ ++ [(t, u)]) u := by
    intro u
    simp [powPot, List.map_append, List.sum_append]
  simp only [hsplit, Finset.sum_add_distrib, ENNReal.add_div]
  refine add_le_add ?_ ?_
  · rw [sum_list_sum_comm, ENNReal.div_eq_inv_mul, ← List.sum_map_mul_left]
    refine List.sum_le_sum fun e _ ↦ ?_
    rw [← Finset.mul_sum, ← mul_assoc, mul_comm c⁻¹, mul_assoc, ← ENNReal.div_eq_inv_mul]
    exact mul_le_mul' le_rfl (powTerm_step_old hb0 hb hfuel ht e.2)
  · rw [← Finset.mul_sum, ENNReal.div_eq_inv_mul, ← mul_assoc, mul_comm c⁻¹, mul_assoc,
      ← ENNReal.div_eq_inv_mul]
    by_cases hbase : ∃ cv, t = baseInput cv
    · rw [ind_of hbase, one_mul]
      exact powTerm_step_new hbase
    · rw [ind_of_not hbase, zero_mul]
      exact bot_le

end Step

/-! ## Failure of the honest prover -/

section Failure

variable {H : Bytes → Option Digest}

theorem searchM_eq_some_none {bits : ℕ} {base : Digest} :
    ∀ ns : List ℕ, searchM H bits base ns = some none →
      ∀ n ∈ ns, ∃ d, H (nonceInput base n) = some d ∧ powOk bits (nonceOf n) d = false
  | [], _ => by simp
  | n :: ns, h => by
    change (H _).bind _ = _ at h
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · rename_i hp
      intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨d, hd, by simpa using hp⟩
      · exact searchM_eq_some_none ns h m hm

theorem findNonceM_eq_some_none {bits : ℕ} {cv : Digest} {fuel : ℕ}
    (h : findNonceM H bits cv fuel = some none) :
    bits ≠ 0 ∧ ∃ base, H (baseInput cv) = some base ∧
      ∀ n < fuel, ∃ d, H (nonceInput base n) = some d ∧ powOk bits (nonceOf n) d = false := by
  unfold findNonceM at h
  split at h
  · cases h
  · rename_i hb
    change (H _).bind _ = _ at h
    obtain ⟨base, hbase, h⟩ := Option.bind_eq_some_iff.mp h
    exact ⟨hb, base, hbase, fun n hn ↦ searchM_eq_some_none _ h n (List.mem_range.mpr hn)⟩

/-- **The prover fails only at a proof of work.** If the honest prover, run with the hash
answered in `Option`, fails, then some proof-of-work search along the program fails. -/
theorem proveFromM_eq_some_none (S : Strategy) (fuel : ℕ) {P : Prog Bool} :
    ∀ (p : Prog Bool) (cv : Digest) (h : List Ev), P.after h = some p →
      proveFromM H S fuel p cv h = some none →
      ∃ h' bits k cv', P.after h' = some (.grind bits k) ∧
        findNonceM H bits cv' fuel = some none
  | .ret _, _, _, _, hp => by cases hp
  | .fail, _, _, _, hp => by cases hp
  | .read k, cv, h, ha, hp => by
    have ha' : P.after (h ++ [Ev.read (S.msg h)]) = some (k (S.msg h)) := by
      rw [Prog.after_append_single _ ha]; simp [Prog.after]
    change (H _).bind _ = _ at hp
    obtain ⟨cv', -, hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
    rcases r with _ | _
    · exact proveFromM_eq_some_none S fuel _ cv' _ ha' hr
    · cases hp
  | .sample k, cv, h, ha, hp => by
    change (H _).bind _ = _ at hp
    obtain ⟨cv', -, hp⟩ := Option.bind_eq_some_iff.mp hp
    have ha' : P.after (h ++ [Ev.sample (challengeOf cv')]) = some (k (challengeOf cv')) := by
      rw [Prog.after_append_single _ ha]; simp [Prog.after]
    exact proveFromM_eq_some_none S fuel _ cv' _ ha' hp
  | .grind bits k, cv, h, ha, hp => by
    have ha' : P.after (h ++ [Ev.grind bits]) = some k := by
      rw [Prog.after_append_single _ ha]; simp [Prog.after]
    change (findNonceM H bits cv fuel).bind _ = _ at hp
    obtain ⟨o, ho, hp⟩ := Option.bind_eq_some_iff.mp hp
    rcases o with _ | n
    · exact ⟨h, bits, k, cv, ha, ho⟩
    · change (H _).bind _ = _ at hp
      obtain ⟨cv', -, hp⟩ := Option.bind_eq_some_iff.mp hp
      obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
      rcases r with _ | _
      · exact proveFromM_eq_some_none S fuel _ cv' _ ha' hr
      · cases hp
  | .commit ht w k, cv, h, ha, hp => by
    have ha' : P.after (h ++ [Ev.commit ht w (S.word h)]) = some k := by
      rw [Prog.after_append_single _ ha]; simp [Prog.after]
    change (treeRootM H ht (S.word h)).bind _ = _ at hp
    obtain ⟨root, -, hp⟩ := Option.bind_eq_some_iff.mp hp
    change (H _).bind _ = _ at hp
    obtain ⟨cv0, -, hp⟩ := Option.bind_eq_some_iff.mp hp
    change (H _).bind _ = _ at hp
    obtain ⟨cv1, -, hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
    rcases r with _ | _
    · exact proveFromM_eq_some_none S fuel _ cv1 _ ha' hr
    · cases hp
  | .query i ps k, cv, h, ha, hp => by
    simp only [proveFromM] at hp
    split at hp
    · cases hp
    · rename_i ht w word hc
      have ha' : P.after (h ++ [Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))]) =
          some (k (ps.map fun q ↦ word (q % 2 ^ ht))) := by
        rw [Prog.after_append_single _ ha]; simp [Prog.after]
      change Option.bind (ps.mapM (openingAtM H ht word)) _ = _ at hp
      obtain ⟨os, -, hp⟩ := Option.bind_eq_some_iff.mp hp
      obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
      rcases r with _ | _
      · exact proveFromM_eq_some_none S fuel _ cv _ ha' hr
      · cases hp

end Failure

/-! ## The honest prover against the random oracle -/

/-- **The honest prover of the random-oracle model**: seed the chain by `σ`, then run the honest
prover with every hash a query; the empty proof if a proof-of-work search fails. -/
def honestComp (σ : Seed) (P : Prog Bool) (S : Strategy) (fuel : ℕ) :
    OracleComp HashSpec Proof := do
  let seed ← σ.run queryH
  let r ← proveM queryH P S seed fuel
  pure (r.getD ⟨[], []⟩)

/-- The honest prover makes at most `1 + |σ.steps| + n · proverFactor height fuel` queries. -/
theorem isTotalQueryBound_honestComp {σ : Seed} {P : Prog Bool} {height n : ℕ}
    (hP : P.CostLE height n) (S : Strategy) (fuel : ℕ) :
    IsTotalQueryBound (honestComp σ P S fuel) (1 + σ.steps.length + n * proverFactor height fuel) :=
  isTotalQueryBound_bind (isTotalQueryBound_seedRun σ) fun seed ↦ by
    rw [← Nat.add_zero (n * _)]
    exact isTotalQueryBound_bind (isTotalQueryBound_proveM hP S seed fuel) fun _ ↦
      isTotalQueryBound_pure' _ 0

/-- **The final inequality.** On every reachable outcome of the logged experiment in which the
verifier rejects the honest prover's proof, the potential of the final log is at least `1`. -/
theorem one_le_powPot {σ : Seed} {P : Prog Bool} {S : Strategy} {bits fuel : ℕ}
    (hc : ∀ chal, runI P S chal = some true) (hs : ∀ chal, shapedI P S chal)
    (hg : ∀ h b k, P.after h = some (.grind b k) → b = bits)
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
  change (σ.run (look ℓ)).bind (fun seed ↦ (proveM (look ℓ) P S seed fuel).bind
    fun r ↦ some (r.getD ⟨[], []⟩)) = some π at hA
  obtain ⟨seed, hseed, hA⟩ := Option.bind_eq_some_iff.mp hA
  obtain ⟨r, hr, hA⟩ := Option.bind_eq_some_iff.mp hA
  cases r with
  | some π' =>
    -- The prover succeeded: the verifier accepts, a contradiction.
    exfalso
    cases hA
    let Ht : Bytes → Digest := fun x ↦ (look ℓ x).getD default
    have hH : ∀ x u, look ℓ x = some u → Ht x = u := fun x u hx ↦ by simp [Ht, hx]
    have hseed' : σ.run (m := Id) Ht = seed := by
      have := simulateQ_id_of_look ℓ Ht hH (σ.run queryH) seed
        (by rw [simulateQ_seedRun]; exact hseed)
      rwa [simulateQ_seedRun] at this
    have hπ : prove Ht P S seed fuel = some π' := by
      have := simulateQ_id_of_look ℓ Ht hH (proveM queryH P S seed fuel) (some π')
        (by rw [simulateQ_proveM]; exact hr)
      rw [simulateQ_proveM] at this
      rw [← proveM_id]
      exact this
    have hb' : simulateQ (lookImpl ℓ) (verifierComp σ P π') = some false := hb
    have hv := simulateQ_id_of_look ℓ Ht hH (verifierComp σ P π') false hb'
    rw [simulateQ_verify] at hv
    have hacc := runProof_prove Ht P S seed fuel hc hs hπ
    have hv' : runProof (m := Id) Ht P (σ.run (m := Id) Ht) π' = false := hv
    rw [hseed', hacc] at hv'
    cases hv'
  | none =>
    -- The prover failed: some proof-of-work search failed.
    have hr' : proveFromM (look ℓ) S fuel P seed [] = some none := by
      change (proveFromM (look ℓ) S fuel P seed []).bind _ = _ at hr
      obtain ⟨t, ht, hr⟩ := Option.bind_eq_some_iff.mp hr
      cases t with
      | none => exact ht
      | some _ => cases hr
    obtain ⟨h', b', k, cv, ha, hf⟩ :=
      proveFromM_eq_some_none S fuel P seed [] (Prog.after.eq_1 P) hr'
    rw [hg h' b' k ha] at hf
    obtain ⟨-, base, hbase, hall⟩ := findNonceM_eq_some_none hf
    -- The base's term is `1`.
    have hS : ¬ Solved bits fuel ℓ base := by
      rintro ⟨n, hn, d, hd, hp⟩
      obtain ⟨d', hd', hp'⟩ := hall n hn
      rw [hd'] at hd
      cases hd
      rw [hp'] at hp
      cases hp
    have hT : (tried fuel ℓ base).card = fuel := by
      have : tried fuel ℓ base = Finset.range fuel := by
        refine Finset.filter_true_of_mem fun n hn ↦ ?_
        obtain ⟨d, hd, -⟩ := hall n (Finset.mem_range.mp hn)
        simp [hd]
      rw [this, Finset.card_range]
    have hterm : powTerm bits fuel ℓ base = 1 := by
      simp [powTerm, hS, hT]
    obtain ⟨i, hi, he, -⟩ := (look_eq_some_iff ℓ _ base).mp hbase
    calc (1 : ℝ≥0∞) = ind (∃ cv', (ℓ[i]).1 = baseInput cv') * powTerm bits fuel ℓ (ℓ[i]).2 := by
          rw [he, ind_of ⟨cv, rfl⟩, one_mul, hterm]
      _ ≤ powPot bits fuel ℓ := List.single_le_sum (fun _ _ ↦ bot_le) _
          (List.mem_map.mpr ⟨ℓ[i], List.getElem_mem hi, rfl⟩)

/-- **Completeness in the random-oracle model.** For a verifier program `P` whose proofs of work
all ask for `bits ∈ [1, 64]` bits, a strategy `S` that wins every interactive run of `P` with
well-shaped words, the seeding `σ`, and a fuel of at most `2^64` nonces: with `Q` the queries of
the honest prover and the verifier together, the verifier rejects the honest prover's proof with
probability at most `Q · ((1 - 2^-bits)^fuel + Q / 2^256)`. -/
theorem romComplete (P : Prog Bool) (S : Strategy) (σ : Seed) {bits fuel height n : ℕ}
    (hb0 : bits ≠ 0) (hb : bits ≤ 64) (hfuel : fuel ≤ 2 ^ 64)
    (hg : ∀ h b k, P.after h = some (.grind b k) → b = bits)
    (hc : ∀ chal, runI P S chal = some true) (hs : ∀ chal, shapedI P S chal)
    (hP : P.CostLE height n) :
    Pr{let z ← romExperiment (honestComp σ P S fuel) (verifierComp σ P)}[z.1.2 = false] ≤
      ((1 + σ.steps.length + n * proverFactor height fuel + (1 + σ.steps.length + n) : ℕ) :
        ℝ≥0∞) * (missProb bits ^ fuel +
          ((1 + σ.steps.length + n * proverFactor height fuel + (1 + σ.steps.length + n) : ℕ) :
            ℝ≥0∞) / 2 ^ 256) := by
  set QA := 1 + σ.steps.length + n * proverFactor height fuel
  set QV := 1 + σ.steps.length + n
  have hA := isTotalQueryBound_honestComp (σ := σ) hP S fuel
  have hV : ∀ π, IsTotalQueryBound (verifierComp σ P π) QV :=
    isTotalQueryBound_verifierComp hP σ
  rw [prEvent_romExperiment_eq_logExperiment _ _ fun r _ ↦ r.2 = false]
  have h := prEvent_run_loggedRO_le_of_freshStepBelow (Φ := powPot bits fuel)
    (δ := missProb bits ^ fuel + ((QA + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) (QA + QV)
    (fun ℓ t hN ht ↦ by
      have := powPot_step hb0 hb hfuel ((logLookup_eq_none_iff ℓ t).mpr ht)
      refine this.trans (add_le_add le_rfl (add_le_add le_rfl ?_))
      rw [card_digest, Nat.cast_pow, Nat.cast_ofNat]
      gcongr)
    _ (QA + QV)
    (isTotalQueryBound_bind hA fun a ↦ (isQueryBound_map_iff (verifierComp σ P a) _ QV _ _).mpr
      (hV a)) [] (by simp) (fun r _ ↦ r.2 = false)
    (fun z hz hrej ↦ one_le_powPot hc hs hg hz hrej)
  rw [powPot_nil, zero_add] at h
  exact h

end
end LeanVM.Protocol.Compile.Rom
