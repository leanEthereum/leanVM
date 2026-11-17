module

public import Common.MultiKey.Defs

@[expose] public section

/-!
# The multi-key game: from the random-oracle model to the permutation

The multi-key game of a hash-query scheme is the single-key game of its `k` keys as one scheme
(`SchemeWithHash.multiKey`), so the transfer of `Common.AdvBudget` applies to it: the statement's
adversary read as a ROM adversary (`romAdvOf`) makes the same own calls and, through every layer,
the same requests to each key (`romAdvOf_reqWeight`); the game's permutation calls are `k` key
generations, the signer's per request and one verification, at most `2^161` for `k ≤ 2^32` keys
when one key's key generation, `maxRequests` signatures and one verification cost at most
`2^128`, and `q ≤ 2^128`; so the sponge's indifferentiability term `Q² / 2^509` is below one unit
`2^-bits` (`multiKey_of_romBoundMulti`).

`RomBoundMulti` is the random-oracle bound of the multi-key game at the adversary's own count,
`k · (q + slack + (k - 1)) / 2^bits`, each key answering at most `maxRequests` requests.
-/

open OracleComp OracleSpec MeasureTheory
open LeanVM.Rpm
open scoped ENNReal
open HashSig.OverPermutation (sequenceFin)

namespace Common.SufCma

variable {Seed PK SK Req Resp F : Type}

/-! ## Request weights through the readings -/

/-- **A weight on signing requests**, `wr` on a request, nothing on the other oracles. -/
def reqWeight {α : Type} (wr : Req → ℕ) : α ⊕ Req → ℕ
  | .inl _ => 0
  | .inr r => wr r

/-- An adversary's requests to key `j` in the random-oracle model. -/
abbrev requestToKeyCalls {k : ℕ} (j : Fin k) : World.Domain ⊕ (Fin k × Req) → ℕ :=
  reqWeight fun r ↦ if r.1 = j then 1 else 0

theorem signingRequestToKeyCost_eq {k : ℕ} (j : Fin k) :
    signingRequestToKeyCost (Req := Req) j = reqWeight fun r ↦ if r.1 = j then 1 else 0 := by
  funext t
  rcases t with _ | _ <;> rfl

theorem embedS_reqWeight (wr : Req → ℕ) (t : RandomPermutationOracles.Domain ⊕ Req) :
    QueryCostAtMost (embedS (Resp := Resp) t) (reqWeight wr) (reqWeight wr t) := by
  rcases t with (n | q) | r <;> simp only [embedS, embed, simulateQ_spec_query] <;>
    exact (isWeightBound_query _ _).mono (by simp [reqWeight])

theorem relabelS_reqWeight (wr : Req → ℕ) (t : KSpecH.Domain ⊕ Req) :
    QueryCostAtMost (relabelS (Resp := Resp) t) (reqWeight wr) (reqWeight wr t) := by
  rcases t with (n | m | q) | r
  · simp only [relabelS, relabel, simulateQ_spec_query]
    exact (isWeightBound_query _ _).mono (by simp [reqWeight])
  · simp only [relabelS, relabel, simulateQ_spec_query]
    exact (isWeightBound_query _ _).mono (by simp [reqWeight])
  · simp only [relabelS, relabel, simulateQ_map, simulateQ_spec_query]
    exact isWeightBound_map _ ((isWeightBound_query _ _).mono (by simp [reqWeight]))
  · simp only [relabelS]
    exact (isWeightBound_query _ _).mono (by simp [reqWeight])

variable (e : DigestBytes ≃ BitVec 256)

theorem ofKS_reqWeight (wr : Req → ℕ) (t : KRom.Domain) :
    QueryCostAtMost (ofKS (Req := Req) (Resp := Resp) e t) (reqWeight wr) 0 := by
  rcases t with n | m
  · simp only [ofKS]
    exact (isWeightBound_query _ _).mono (by simp [reqWeight])
  · simp only [ofKS]
    exact isWeightBound_map _ ((isWeightBound_query _ _).mono (by simp [reqWeight]))

theorem simAdv_reqWeight (wr : Req → ℕ) (t : KSpecB.Domain ⊕ Req)
    (s : SimState DigestBytes KRest KCap) :
    QueryCostAtMost ((simAdv (Req := Req) (Resp := Resp) e t).run s) (reqWeight wr)
      (reqWeight wr t) := by
  rcases t with t | r
  · exact isWeightBound_simulateQ _ (fun _ ↦ 0) _ (ofKS_reqWeight e wr)
      (QueryCostAtMost.zero_weight _)
  · show QueryCostAtMost ((fun a ↦ (a, s)) <$>
      (liftM ((World + (Req →ₒ Resp)).query (.inr r)) : OracleComp _ _)) _ _
    exact isWeightBound_map _ ((isWeightBound_query _ _).mono (by simp [reqWeight]))

/-- **The ROM adversary makes the statement adversary's requests, weighed by any request
weight.** -/
theorem romAdvOf_reqWeight (wr : Req → ℕ)
    (main : PK → OracleComp (RandomPermutationOracles + (Req →ₒ Resp)) F) (n : ℕ) (pk : PK)
    (h : QueryCostAtMost (main pk) (reqWeight wr) n) :
    QueryCostAtMost (romAdvOf e main pk) (reqWeight wr) n := by
  have h1 := isWeightBound_simulateQ _ _ _ (embedS_reqWeight wr) h
  have h2 := isWeightBound_simulateQ _ _ _ (relabelS_reqWeight wr) h1
  exact isWeightBound_map _ (isWeightBound_run_simulateQ _ _ _ (simAdv_reqWeight e wr) h2 _)

/-! ## The bounds of `k` keys -/

/-- **The multi-key random-oracle bound at the adversary's own count**: every ROM adversary
against `k` keys that itself makes at most `q` hash calls and at most `maxRequests` requests to
each key, on every path, wins with probability at most `k · (q + slack + (k - 1)) / 2^bits`. -/
def RomBoundMulti (S : SchemeWithHash Seed PK SK Req Resp F) (k bits slack maxRequests : ℕ) :
    Prop :=
  ∀ q (main : (Fin k → PK) → OracleComp (World + (Fin k × Req →ₒ Resp)) (Fin k × F)),
    (∀ pks, QueryCostAtMost (main pks) advHashCalls q) →
    (∀ pks j, QueryCostAtMost (main pks) (requestToKeyCalls j) maxRequests) →
      Pr{let r ← romExperiment (S.multiKey k) main}[r.1 = true] ≤
        (k : ℝ≥0∞) * ((q : ℝ≥0∞) + slack + ((k - 1 : ℕ) : ℝ≥0∞)) / ((2 ^ bits : ℕ) : ℝ≥0∞)

section Weight

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}

/-- **Bounds on a family of weights add**: over a finite index set. -/
theorem QueryCostAtMost.sum_weight {β : Type} (s : Finset β) {oa : OracleComp spec α}
    {w : β → ι → ℕ} {n : β → ℕ} (h : ∀ b ∈ s, QueryCostAtMost oa (w b) (n b)) :
    QueryCostAtMost oa (fun t ↦ ∑ b ∈ s, w b t) (∑ b ∈ s, n b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using QueryCostAtMost.zero_weight oa
  | insert b s hb ih =>
    simp only [Finset.sum_insert hb]
    exact (h b (Finset.mem_insert_self b s)).add_weight
      (ih fun b' hb' ↦ h b' (Finset.mem_insert_of_mem hb'))

/-- `n` computations in sequence, each of weight at most `K`, weigh at most `n · K`. -/
theorem sequenceFin_cost {w : ι → ℕ} {K : ℕ} :
    ∀ {n : ℕ} (c : Fin n → OracleComp spec α), (∀ j, QueryCostAtMost (c j) w K) →
      QueryCostAtMost (sequenceFin c) w (n * K)
  | 0, _, _ => trivial
  | n + 1, c, h => by
    simp only [sequenceFin]
    refine ((h 0).bind fun _ ↦ (sequenceFin_cost (fun i ↦ c i.succ) fun i ↦ h i.succ).bind
      fun _ ↦ isWeightBound_pure _ _ 0).mono ?_
    rw [Nat.add_zero, Nat.succ_mul]
    omega

end Weight

/-- The requests to the `k` keys are all the requests. -/
theorem sum_signingRequestToKeyCost {k : ℕ} (t : RandomPermutationOracles.Domain ⊕ (Fin k × Req)) :
    ∑ j : Fin k, signingRequestToKeyCost j t = signingRequestCost t := by
  rcases t with t | r
  · simp [signingRequestToKeyCost, signingRequestCost]
  · simp [signingRequestToKeyCost, signingRequestCost]

/-- `(k (q + c + (k - 1))) / 2^bits + Q² / 2^509 ≤ k (q + (c + 1) + k) 2^-bits` for `Q ≤ 2^161`,
`1 ≤ k`, `bits ≤ 128`. -/
theorem multi_add_sq_le {k q c Q bits : ℕ} (hk : 1 ≤ k) (hQ : Q ≤ 2 ^ 161) (hb : bits ≤ 128) :
    (k : ℝ≥0∞) * ((q : ℝ≥0∞) + c + ((k - 1 : ℕ) : ℝ≥0∞)) / ((2 ^ bits : ℕ) : ℝ≥0∞) +
        (Q : ℝ≥0∞) ^ 2 / 2 ^ 509 ≤
      (k : ℝ≥0∞) * ((q : ℝ≥0∞) + ((c + 1 : ℕ) : ℝ≥0∞) + k) * (2 : ℝ≥0∞)⁻¹ ^ bits := by
  have h1 : (k : ℝ≥0∞) * ((q : ℝ≥0∞) + c + ((k - 1 : ℕ) : ℝ≥0∞)) / ((2 ^ bits : ℕ) : ℝ≥0∞) =
      (k : ℝ≥0∞) * ((q : ℝ≥0∞) + c + ((k - 1 : ℕ) : ℝ≥0∞)) * (2 : ℝ≥0∞)⁻¹ ^ bits := by
    rw [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, ENNReal.inv_pow]
  have h2 : (Q : ℝ≥0∞) ^ 2 / 2 ^ 509 ≤ (2 : ℝ≥0∞)⁻¹ ^ bits :=
    calc (Q : ℝ≥0∞) ^ 2 / 2 ^ 509 ≤ (Q : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 348 :=
          sq_div_le_mul_inv_pow (k := 161) 348 hQ
      _ ≤ (2 : ℝ≥0∞) ^ 161 * (2 : ℝ≥0∞)⁻¹ ^ 348 := by
          gcongr
          exact_mod_cast hQ
      _ = (2 : ℝ≥0∞)⁻¹ ^ 187 := two_pow_mul_inv_pow 161 187
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ bits := inv_two_pow_le_of_le (by omega)
  have hkk : ((k - 1 : ℕ) : ℝ≥0∞) + 1 = k := by
    exact_mod_cast Nat.sub_add_cancel hk
  have hk1 : (1 : ℝ≥0∞) ≤ k := by exact_mod_cast hk
  rw [h1]
  calc (k : ℝ≥0∞) * ((q : ℝ≥0∞) + c + ((k - 1 : ℕ) : ℝ≥0∞)) * (2 : ℝ≥0∞)⁻¹ ^ bits +
        (Q : ℝ≥0∞) ^ 2 / 2 ^ 509
      ≤ (k : ℝ≥0∞) * ((q : ℝ≥0∞) + c + ((k - 1 : ℕ) : ℝ≥0∞)) * (2 : ℝ≥0∞)⁻¹ ^ bits +
          (k : ℝ≥0∞) * 2 * (2 : ℝ≥0∞)⁻¹ ^ bits := by
        gcongr
        calc (Q : ℝ≥0∞) ^ 2 / 2 ^ 509 ≤ (2 : ℝ≥0∞)⁻¹ ^ bits := h2
          _ = 1 * 1 * (2 : ℝ≥0∞)⁻¹ ^ bits := by ring
          _ ≤ (k : ℝ≥0∞) * 2 * (2 : ℝ≥0∞)⁻¹ ^ bits := by gcongr; norm_num
    _ = (k : ℝ≥0∞) * ((q : ℝ≥0∞) + ((c + 1 : ℕ) : ℝ≥0∞) + (((k - 1 : ℕ) : ℝ≥0∞) + 1)) *
          (2 : ℝ≥0∞)⁻¹ ^ bits := by push_cast; ring
    _ = _ := by rw [hkk]

/-- **The multi-key game over `π`, from the multi-key ROM bound.** For a hash-query scheme whose
key generation, signer and verifier over `π` make at most `K`, `s` per request and `V`
permutation calls on every path, with `K + maxRequests · s + V ≤ 2^128`, a ROM bound
`k · (q + slack + (k - 1)) / 2^bits` against `k ≤ 2^32` keys gives the statement's game of the `k`
keys over `π` the bound `k · (q + (slack + 1) + k) · 2^-bits`, the adversary itself making `q` calls
of `π` and `π⁻¹` and at most `maxRequests` requests to each key: the sponge's indifferentiability
costs less than one unit `2^-bits`. -/
theorem multiKey_of_romBoundMulti (S : SchemeWithHash Seed PK SK Req Resp F)
    {k bits slack maxRequests K s V : ℕ} (hbits : bits ≤ 128) (hk1 : 1 ≤ k) (hk : k ≤ 2 ^ 32)
    (hrom : RomBoundMulti S k bits slack maxRequests)
    (hK : ∀ seed, QueryCostAtMost (S.overPermutation.generateKeys seed) permutationCallCost K)
    (hs : ∀ sk r, QueryCostAtMost (S.overPermutation.sign sk r) permutationCallCost s)
    (hV : ∀ pk f, QueryCostAtMost (S.overPermutation.verify pk f) permutationCallCost V)
    (hsmall : K + maxRequests * s + V ≤ 2 ^ 128) (q : ℕ)
    (main : (Fin k → PK) →
      OracleComp (RandomPermutationOracles + (Fin k × Req →ₒ Resp)) (Fin k × F))
    (hq : ∀ pks, QueryCostAtMost (main pks) adversaryPermutationCost q)
    (hn : ∀ pks j, QueryCostAtMost (main pks) (signingRequestToKeyCost j) maxRequests) :
    Pr{let b ← runWithRandomPermutation (forgeryGame (S.overPermutation.multiKey k) main)}[
        b = true] ≤
      (k : ℝ≥0∞) * ((q : ℝ≥0∞) + ((slack + 1 : ℕ) : ℝ≥0∞) + k) * (2 : ℝ≥0∞)⁻¹ ^ bits := by
  rw [← multiKey_overPermutation]
  set M := S.multiKey k with hM
  rcases le_or_gt q (2 ^ 128) with hcap | hcap
  · -- the costs of the `k` keys as one scheme
    have hK' : ∀ seeds, QueryCostAtMost (M.overPermutation.generateKeys seeds)
        permutationCallCost (k * K) := by
      intro seeds
      rw [hM, multiKey_overPermutation]
      simp only [Scheme.multiKey]
      exact ((sequenceFin_cost _ fun j ↦ hK (seeds j)).bind fun _ ↦
        isWeightBound_pure _ _ 0).mono (by omega)
    have hs' : ∀ sks r, QueryCostAtMost (M.overPermutation.sign sks r) permutationCallCost s := by
      intro sks r
      rw [hM, multiKey_overPermutation]
      exact hs _ _
    have hV' : ∀ pks f, QueryCostAtMost (M.overPermutation.verify pks f) permutationCallCost V := by
      intro pks f
      rw [hM, multiKey_overPermutation]
      exact hV _ _
    have hnt : ∀ pks, QueryCostAtMost (main pks) signingRequestCost (k * maxRequests) := by
      intro pks
      have h := QueryCostAtMost.sum_weight Finset.univ (fun j _ ↦ hn pks j)
      simp only [sum_signingRequestToKeyCost, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul] at h
      exact h
    set Q := k * K + (q + s * (k * maxRequests)) + V with hQdef
    have hQ : QueryCostAtMost (forgeryGame M.overPermutation main) permutationCallCost Q :=
      forgeryGame_cost _ main hK' hs' hV' hq hnt
    have hQle : Q ≤ 2 ^ 161 := by
      have h1 : k * K + s * (k * maxRequests) + V ≤ k * (K + maxRequests * s + V) := by
        have : s * (k * maxRequests) = k * (maxRequests * s) := by ring
        rw [this, Nat.mul_add, Nat.mul_add]
        have : V ≤ k * V := Nat.le_mul_of_pos_left V hk1
        omega
      have h2 : k * (K + maxRequests * s + V) ≤ 2 ^ 32 * 2 ^ 128 := Nat.mul_le_mul hk hsmall
      have h3 : (2 : ℕ) ^ 32 * 2 ^ 128 + 2 ^ 128 ≤ 2 ^ 161 := by norm_num
      omega
    let mainH : (Fin k → PK) → OracleComp (KSpecH + (Fin k × Req →ₒ Resp)) (Fin k × F) :=
      fun pk ↦ simulateQ embedS (main pk)
    let mainB : (Fin k → PK) → OracleComp (KSpecB + (Fin k × Req →ₒ Resp)) (Fin k × F) :=
      fun pk ↦ simulateQ relabelS (mainH pk)
    have hQH : QueryCostAtMost (rpmGameH M mainH) permCallsH Q := by
      have h := hQ
      rw [forgeryGame_overPermutation, rpmGame_eq_expand, isWeightBound_expand_iff] at h
      exact h
    have hQB : QueryCostAtMost (rpmGameB digestBytesEquivBitVec M mainB) permCallsB Q := by
      have h := isWeightBound_relabel hQH
      rwa [rpmGame_relabel] at h
    have hprob : Pr{let b ← runWithRandomPermutation (forgeryGame M.overPermutation main)}[
        b = true] = Pr{let b ← rpmExperimentB digestBytesEquivBitVec M mainB}[b = true] := by
      rw [forgeryGame_overPermutation, rpmGame_eq_expand, runK_expand]
      exact (rpmExperiment_relabel M mainH).prEvent_eq _
    obtain ⟨h1, -⟩ := rpm_le_romB digestBytesEquivBitVec M mainB Q Q
      (hQB.mono_weight oracleCallsB_le_permCallsB) hQB
    have hrom' := hrom q (romAdvOf digestBytesEquivBitVec main)
      (fun pk ↦ romAdvOf_advHashCalls _ main q pk (hq pk))
      (fun pk j ↦ romAdvOf_reqWeight _ _ main maxRequests pk
        (signingRequestToKeyCost_eq j ▸ hn pk j))
    rw [hprob]
    refine (h1.trans (add_le_add hrom' le_rfl)).trans ?_
    exact multi_add_sq_le hk1 hQle hbits
  · refine (prEvent_le_one _).trans (one_le_mul_inv_two_pow ?_)
    calc (2 : ℝ≥0∞) ^ bits ≤ 2 ^ 128 := pow_le_pow_right₀ one_le_two hbits
      _ ≤ (q : ℝ≥0∞) := by exact_mod_cast hcap.le
      _ ≤ (k : ℝ≥0∞) * ((q : ℝ≥0∞) + ((slack + 1 : ℕ) : ℝ≥0∞) + k) := by
          calc (q : ℝ≥0∞) = 1 * q := (one_mul _).symm
            _ ≤ (k : ℝ≥0∞) * ((q : ℝ≥0∞) + ((slack + 1 : ℕ) : ℝ≥0∞) + k) := by
                gcongr
                · exact_mod_cast hk1
                · rw [add_assoc]; exact le_self_add

end Common.SufCma
