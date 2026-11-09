module

public import Common.PiOnly
public import Common.Linear
public import Common.SeedKey
public import Common.StaticSwap
public import Common.WithHashBridge

@[expose] public section

/-!
# SUF-CMA security at the adversary's own count

The statement's `StronglyUnforgeable` charges an adversary for its own calls of `π` and `π⁻¹`
only: key generation, the signer's answers and the forgery's verification are the game's. This
file moves a random-oracle bound of the same shape (`RomBoundAdv`: at most `q` hash calls of the
adversary itself and at most `maxRequests` signing requests, success at most
`(q + slack) / 2^bits`) to the statement's model:

* the kept-key and static-swap forms of a scheme win as often as the scheme against
  every adversary (`KeptKey.prob_romExperiment_eq`, `StaticSwap.success_eq`), so the bound passes
  to them unchanged (`KeptKey.romBoundAdv`, `StaticSwap.romBoundAdv`);
* `stronglyUnforgeable_of_romBoundAdv`: the statement's adversary, read with the Keccak-256 oracle
  (`embedS`), on bytes (`relabelS`) and with its permutation queries answered by the
  indifferentiability simulator (`romAdv`), is a ROM adversary with the same own calls and the
  same requests (`romAdv_advHashCalls`, `romAdv_requestCalls`); the sponge's indifferentiability
  costs `Q² / 2^509` for the game's total `Q` of permutation calls, which worst-case bounds on key
  generation, the signer and the verifier (`forgeryGame_cost`) keep below `2^129`, so that term is
  less than one unit `2^-bits`.
-/

open OracleComp OracleSpec MeasureTheory
open LeanVM.Rpm
open scoped ENNReal

namespace Common

section Weight

variable {ι ι' : Type} {spec : OracleSpec.{0, 0} ι} {spec' : OracleSpec.{0, 0} ι'} {α : Type}

/-- Nothing weighs nothing. -/
theorem QueryCostAtMost.zero_weight (oa : OracleComp spec α) :
    QueryCostAtMost oa (fun _ ↦ 0) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff]
    exact ⟨le_rfl, fun u ↦ ih u⟩

/-- **Two weights' bounds add.** -/
theorem QueryCostAtMost.add_weight {oa : OracleComp spec α} {w₁ w₂ : ι → ℕ} {a b : ℕ}
    (h₁ : QueryCostAtMost oa w₁ a) (h₂ : QueryCostAtMost oa w₂ b) :
    QueryCostAtMost oa (fun t ↦ w₁ t + w₂ t) (a + b) := by
  induction oa using OracleComp.inductionOn generalizing a b with
  | pure x => trivial
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at h₁ h₂ ⊢
    exact ⟨by omega, fun u ↦ (ih u (h₁.2 u) (h₂.2 u)).mono (by omega)⟩

/-- **A weight's bound scales.** -/
theorem QueryCostAtMost.mul_weight {oa : OracleComp spec α} {w : ι → ℕ} {a : ℕ} (k : ℕ)
    (h : QueryCostAtMost oa w a) : QueryCostAtMost oa (fun t ↦ k * w t) (k * a) := by
  induction oa using OracleComp.inductionOn generalizing a with
  | pure x => trivial
  | query_bind t k' ih =>
    rw [isWeightBound_query_bind_iff] at h ⊢
    refine ⟨Nat.mul_le_mul_left k h.1, fun u ↦ ?_⟩
    rw [← Nat.mul_sub]
    exact ih u (h.2 u)

/-- **Weight bounds through a writer simulation.** -/
theorem isWeightBound_run_simulateQ_writer {L : Type} [EmptyCollection L] [Append L]
    [LawfulAppend L] (impl : QueryImpl spec (WriterT L (OracleComp spec'))) (w : ι → ℕ)
    (w' : ι' → ℕ) (hstep : ∀ t, QueryCostAtMost (impl t).run w' (w t))
    {oa : OracleComp spec α} {Q : ℕ} (h : QueryCostAtMost oa w Q) :
    QueryCostAtMost (simulateQ impl oa).run w' Q := by
  induction oa using OracleComp.inductionOn generalizing Q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, WriterT.run_bind']
    exact ((hstep t).bind fun z ↦ isWeightBound_map _ (ih z.1 (h.2 z.1))).mono (by omega)

end Weight

namespace SufCma

variable {Seed PK SK Req Resp F : Type}

/-! ## The bound at the adversary's own count, in the random-oracle model -/

/-- An adversary's own hash calls: a call of `H` one; a coin and a signing request nothing. -/
def advHashCalls : World.Domain ⊕ Req → ℕ
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => 0

/-- An adversary's signing requests: one each. -/
def requestCalls : World.Domain ⊕ Req → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- **A random-oracle bound at the adversary's own count**: every ROM adversary that itself makes
at most `q` hash calls and at most `maxRequests` signing requests on every path, whatever the
answers, wins with probability at most `(q + slack) / 2^bits`. Key generation, the signer's
answers and the forgery's verification are not charged to `q`. -/
def RomBoundAdv (S : SchemeWithHash Seed PK SK Req Resp F) (bits slack maxRequests : ℕ) : Prop :=
  ∀ q (main : PK → OracleComp (World + (Req →ₒ Resp)) F),
    (∀ pk, QueryCostAtMost (main pk) advHashCalls q) →
    (∀ pk, QueryCostAtMost (main pk) requestCalls maxRequests) →
      Pr{let r ← romExperiment S main}[r.1 = true] ≤
        ((q : ℝ≥0∞) + slack) / ((2 ^ bits : ℕ) : ℝ≥0∞)

/-- **The bound passes to the kept-key scheme**, which wins as often against every adversary. -/
theorem KeptKey.romBoundAdv {D SK' : Type} {S : SchemeWithHash Seed PK SK Req Resp F}
    (K : KeptKey S D SK') (hK : K.Reruns) {bits slack maxRequests : ℕ}
    (h : RomBoundAdv S bits slack maxRequests) : RomBoundAdv K.scheme bits slack maxRequests := by
  intro q main hq hr
  rw [K.prob_romExperiment_eq hK main]
  exact h q main hq hr

/-- **The bound passes through a static swap**, whose two schemes win as often against every
adversary. -/
theorem StaticSwap.romBoundAdv {SK₁ SK₂ : Type} {S₁ : SchemeWithHash Seed PK SK₁ Req Resp F}
    {S₂ : SchemeWithHash Seed PK SK₂ Req Resp F} (K : StaticSwap S₁ S₂) (P : List UInt8 → Prop)
    [DecidablePred P] [Fintype {d // P d}] (hk₁ : ∀ seed, QueriesIn P (S₁.keygen seed))
    (hk₂ : ∀ seed, QueriesIn P (S₂.keygen seed)) (hs₁ : ∀ sk r, QueriesIn P (S₁.sign sk r))
    (hs₂ : ∀ seed r, QueriesIn P (S₂.sign (K.keep seed) r)) {bits slack maxRequests : ℕ}
    (h : RomBoundAdv S₁ bits slack maxRequests) : RomBoundAdv S₂ bits slack maxRequests := by
  intro q main hq hr
  rw [K.success_eq P hk₁ hk₂ hs₁ hs₂ main]
  exact h q main hq hr

/-! ## The adversary's calls through its readings -/

/-- The adversary's own calls with the hash oracle: `H`, `π` and `π⁻¹` one each. -/
def advCallsH : KSpecH.Domain ⊕ Req → ℕ
  | .inl t => oracleCalls t
  | .inr _ => 0

/-- Its signing requests with the hash oracle. -/
def requestCallsH : KSpecH.Domain ⊕ Req → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- The adversary's own calls on bytes. -/
def advCallsB : KSpecB.Domain ⊕ Req → ℕ
  | .inl t => oracleCallsB t
  | .inr _ => 0

/-- Its signing requests on bytes. -/
def requestCallsB : KSpecB.Domain ⊕ Req → ℕ
  | .inl _ => 0
  | .inr _ => 1

theorem embedS_advCalls (t : RandomPermutationOracles.Domain ⊕ Req) :
    QueryCostAtMost (embedS (Resp := Resp) t) advCallsH (adversaryPermutationCost t) := by
  rcases t with (n | q) | r <;> simp only [embedS, embed, simulateQ_spec_query] <;>
    exact (isWeightBound_query _ _).mono (by
      simp [advCallsH, oracleCalls, adversaryPermutationCost, permutationCallCost])

theorem embedS_requests (t : RandomPermutationOracles.Domain ⊕ Req) :
    QueryCostAtMost (embedS (Resp := Resp) t) requestCallsH (signingRequestCost t) := by
  rcases t with (n | q) | r <;> simp only [embedS, embed, simulateQ_spec_query] <;>
    exact (isWeightBound_query _ _).mono (by simp [requestCallsH, signingRequestCost])

theorem relabelS_advCalls (t : KSpecH.Domain ⊕ Req) :
    QueryCostAtMost (relabelS (Resp := Resp) t) advCallsB (advCallsH t) := by
  rcases t with (n | m | q) | r
  · simp only [relabelS, relabel, simulateQ_spec_query]
    exact (isWeightBound_query _ _).mono (by simp [advCallsB, oracleCallsB, advCallsH, oracleCalls])
  · simp only [relabelS, relabel, simulateQ_spec_query]
    exact (isWeightBound_query _ _).mono (by simp [advCallsB, oracleCallsB, advCallsH, oracleCalls])
  · simp only [relabelS, relabel, simulateQ_map, simulateQ_spec_query]
    exact isWeightBound_map _ ((isWeightBound_query _ _).mono (by
      simp [advCallsB, oracleCallsB, advCallsH, oracleCalls]))
  · simp only [relabelS]
    exact (isWeightBound_query _ _).mono (by simp [advCallsB, advCallsH])

theorem relabelS_requests (t : KSpecH.Domain ⊕ Req) :
    QueryCostAtMost (relabelS (Resp := Resp) t) requestCallsB (requestCallsH t) := by
  rcases t with (n | m | q) | r
  · simp only [relabelS, relabel, simulateQ_spec_query]
    exact (isWeightBound_query _ _).mono (by simp [requestCallsB, requestCallsH])
  · simp only [relabelS, relabel, simulateQ_spec_query]
    exact (isWeightBound_query _ _).mono (by simp [requestCallsB, requestCallsH])
  · simp only [relabelS, relabel, simulateQ_map, simulateQ_spec_query]
    exact isWeightBound_map _ ((isWeightBound_query _ _).mono (by
      simp [requestCallsB, requestCallsH]))
  · simp only [relabelS]
    exact (isWeightBound_query _ _).mono (by simp [requestCallsB, requestCallsH])

variable (e : DigestBytes ≃ BitVec 256)

/-- The transfer's oracles read in the scheme's: a hash call is an own hash call. -/
theorem ofKS_advHashCalls (t : KRom.Domain) :
    QueryCostAtMost (ofKS (Req := Req) (Resp := Resp) e t) advHashCalls (romCalls t) := by
  rcases t with n | m
  · simp only [ofKS]
    exact (isWeightBound_query _ _).mono (by simp [advHashCalls, romCalls])
  · simp only [ofKS]
    exact isWeightBound_map _ ((isWeightBound_query _ _).mono (by simp [advHashCalls, romCalls]))

/-- The transfer's oracles make no signing request. -/
theorem ofKS_requestCalls (t : KRom.Domain) :
    QueryCostAtMost (ofKS (Req := Req) (Resp := Resp) e t) requestCalls 0 := by
  rcases t with n | m
  · simp only [ofKS]
    exact (isWeightBound_query _ _).mono (by simp [requestCalls])
  · simp only [ofKS]
    exact isWeightBound_map _ ((isWeightBound_query _ _).mono (by simp [requestCalls]))

theorem simAdv_advHashCalls (t : KSpecB.Domain ⊕ Req) (s : SimState DigestBytes KRest KCap) :
    QueryCostAtMost ((simAdv (Req := Req) (Resp := Resp) e t).run s) advHashCalls (advCallsB t) := by
  rcases t with t | r
  · exact isWeightBound_simulateQ _ _ _ (ofKS_advHashCalls e) (isWeightBound_idealImpl t s)
  · show QueryCostAtMost ((fun a ↦ (a, s)) <$>
      (liftM ((World + (Req →ₒ Resp)).query (.inr r)) : OracleComp _ _)) _ _
    exact isWeightBound_map _ ((isWeightBound_query _ _).mono (by simp [advHashCalls, advCallsB]))

theorem simAdv_requestCalls (t : KSpecB.Domain ⊕ Req) (s : SimState DigestBytes KRest KCap) :
    QueryCostAtMost ((simAdv (Req := Req) (Resp := Resp) e t).run s) requestCalls
      (requestCallsB t) := by
  rcases t with t | r
  · exact isWeightBound_simulateQ _ (fun _ ↦ 0) _ (ofKS_requestCalls e)
      (QueryCostAtMost.zero_weight _)
  · show QueryCostAtMost ((fun a ↦ (a, s)) <$>
      (liftM ((World + (Req →ₒ Resp)).query (.inr r)) : OracleComp _ _)) _ _
    exact isWeightBound_map _ ((isWeightBound_query _ _).mono (by
      simp [requestCalls, requestCallsB]))

/-- The statement's adversary read as a ROM adversary. -/
noncomputable def romAdvOf (main : PK → OracleComp (RandomPermutationOracles + (Req →ₒ Resp)) F) :
    PK → OracleComp (World + (Req →ₒ Resp)) F :=
  romAdv e fun pk ↦ simulateQ relabelS (simulateQ embedS (main pk))

/-- **The ROM adversary makes the statement adversary's own calls.** -/
theorem romAdvOf_advHashCalls
    (main : PK → OracleComp (RandomPermutationOracles + (Req →ₒ Resp)) F) (q : ℕ) (pk : PK)
    (h : QueryCostAtMost (main pk) adversaryPermutationCost q) :
    QueryCostAtMost (romAdvOf e main pk) advHashCalls q := by
  have h1 := isWeightBound_simulateQ _ _ _ embedS_advCalls h
  have h2 := isWeightBound_simulateQ _ _ _ relabelS_advCalls h1
  exact isWeightBound_map _ (isWeightBound_run_simulateQ _ _ _ (simAdv_advHashCalls e) h2 _)

/-- **The ROM adversary makes the statement adversary's signing requests.** -/
theorem romAdvOf_requestCalls
    (main : PK → OracleComp (RandomPermutationOracles + (Req →ₒ Resp)) F) (n : ℕ) (pk : PK)
    (h : QueryCostAtMost (main pk) signingRequestCost n) :
    QueryCostAtMost (romAdvOf e main pk) requestCalls n := by
  have h1 := isWeightBound_simulateQ _ _ _ embedS_requests h
  have h2 := isWeightBound_simulateQ _ _ _ relabelS_requests h1
  exact isWeightBound_map _ (isWeightBound_run_simulateQ _ _ _ (simAdv_requestCalls e) h2 _)

/-! ## The game's total permutation calls -/

/-- **The game's permutation calls**: key generation's, the adversary's own, its requests' and the
verification's, from worst-case bounds on each. -/
theorem forgeryGame_cost (scheme : Scheme Seed PK SK Req Resp F)
    (main : PK → OracleComp (RandomPermutationOracles + (Req →ₒ Resp)) F) {K s V q n : ℕ}
    (hK : ∀ seed, QueryCostAtMost (scheme.generateKeys seed) permutationCallCost K)
    (hs : ∀ sk r, QueryCostAtMost (scheme.sign sk r) permutationCallCost s)
    (hV : ∀ pk f, QueryCostAtMost (scheme.verify pk f) permutationCallCost V)
    (hq : ∀ pk, QueryCostAtMost (main pk) adversaryPermutationCost q)
    (hn : ∀ pk, QueryCostAtMost (main pk) signingRequestCost n) :
    QueryCostAtMost (forgeryGame scheme main) permutationCallCost (K + (q + s * n) + V) := by
  unfold forgeryGame
  have h0 := isWeightBound_liftM_probComp permutationCallCost (fun _ ↦ rfl) scheme.sampleSeed
  have hrest : ∀ keys : PK × SK, QueryCostAtMost (do
      let ((forgery, log) : F × QueryLog (Req →ₒ Resp)) ←
        (simulateQ
          (QueryImpl.ofLift RandomPermutationOracles
            (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp RandomPermutationOracles)) +
          QueryImpl.withLogging (spec := Req →ₒ Resp) (scheme.sign keys.2)) (main keys.1)).run
      let verified ← scheme.verify keys.1 forgery
      return scheme.winningCondition log forgery && verified) permutationCallCost
        ((q + s * n) + V) := by
    rintro ⟨pk, sk⟩
    have hw : QueryCostAtMost (main pk)
        (fun t ↦ adversaryPermutationCost t + s * signingRequestCost t) (q + s * n) :=
      (hq pk).add_weight ((hn pk).mul_weight s)
    have hphase := isWeightBound_run_simulateQ_writer
      (QueryImpl.ofLift RandomPermutationOracles
        (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp RandomPermutationOracles)) +
        QueryImpl.withLogging (spec := Req →ₒ Resp) (scheme.sign sk))
      (fun t ↦ adversaryPermutationCost t + s * signingRequestCost t) permutationCallCost
      (fun t ↦ by
        rcases t with t | r
        · show QueryCostAtMost ((fun u ↦ (u, (∅ : QueryLog (Req →ₒ Resp)))) <$>
            (liftM (RandomPermutationOracles.query t) : OracleComp _ _)) _ _
          exact isWeightBound_map _ ((isWeightBound_query _ _).mono (by
            simp [adversaryPermutationCost, signingRequestCost]))
        · have h := isWeightBound_map (fun u ↦ (u, [(⟨r, u⟩ : (_ : Req) × Resp)])) (hs sk r)
          simpa [adversaryPermutationCost, signingRequestCost] using h) hw
    exact hphase.bind fun z ↦ (hV pk z.1).bind fun _ ↦ isWeightBound_pure _ _ 0
  have := h0.bind fun seed ↦ (hK seed).bind hrest
  refine this.mono (by omega)

/-! ## The end theorem -/

/-- `(q + slack) / 2^bits + Q² / 2^509 ≤ (q + slack + 1) · 2^-bits` for `Q ≤ 2^129`,
`bits ≤ 128`. -/
theorem add_sq_le_succ {q slack Q bits : ℕ} (hQ : Q ≤ 2 ^ 129) (hb : bits ≤ 128) :
    ((q : ℝ≥0∞) + slack) / ((2 ^ bits : ℕ) : ℝ≥0∞) + (Q : ℝ≥0∞) ^ 2 / 2 ^ 509 ≤
      ((q : ℝ≥0∞) + ((slack + 1 : ℕ) : ℝ≥0∞)) * (2 : ℝ≥0∞)⁻¹ ^ bits := by
  have h1 : ((q : ℝ≥0∞) + slack) / ((2 ^ bits : ℕ) : ℝ≥0∞) =
      ((q : ℝ≥0∞) + slack) * (2 : ℝ≥0∞)⁻¹ ^ bits := by
    rw [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, ENNReal.inv_pow]
  have h2 : (Q : ℝ≥0∞) ^ 2 / 2 ^ 509 ≤ (2 : ℝ≥0∞)⁻¹ ^ bits :=
    calc (Q : ℝ≥0∞) ^ 2 / 2 ^ 509 ≤ (Q : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 380 :=
          sq_div_le_mul_inv_pow (k := 129) 380 hQ
      _ ≤ (2 : ℝ≥0∞) ^ 129 * (2 : ℝ≥0∞)⁻¹ ^ 380 := by
          gcongr
          exact_mod_cast hQ
      _ = (2 : ℝ≥0∞)⁻¹ ^ 251 := two_pow_mul_inv_pow 129 251
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ bits := inv_two_pow_le_of_le (by omega)
  rw [h1]
  calc ((q : ℝ≥0∞) + slack) * (2 : ℝ≥0∞)⁻¹ ^ bits + (Q : ℝ≥0∞) ^ 2 / 2 ^ 509
      ≤ ((q : ℝ≥0∞) + slack) * (2 : ℝ≥0∞)⁻¹ ^ bits + (2 : ℝ≥0∞)⁻¹ ^ bits := by gcongr
    _ = ((q : ℝ≥0∞) + ((slack + 1 : ℕ) : ℝ≥0∞)) * (2 : ℝ≥0∞)⁻¹ ^ bits := by
        push_cast
        ring

/-- **SUF-CMA security at the adversary's own count, from the random-oracle bound.** A scheme with
the hash a query whose ROM experiment is won with probability at most `(q + slack) / 2^bits` by
every adversary making `q` hash calls itself and `maxRequests` signing requests, and whose key
generation, signer and verifier over `π` make at most `K`, `s` per request and `V` permutation
calls on every path, with `K + maxRequests · s + V ≤ 2^128`, is strongly unforgeable over `π` at
`bits ≤ 128` bits with the constant `slack + 1`: the adversary itself makes `q` calls of `π` and
`π⁻¹`. -/
theorem stronglyUnforgeable_of_romBoundAdv (S : SchemeWithHash Seed PK SK Req Resp F)
    {bits slack maxRequests K s V : ℕ} (hbits : bits ≤ 128)
    (hrom : RomBoundAdv S bits slack maxRequests)
    (hK : ∀ seed, QueryCostAtMost (S.overPermutation.generateKeys seed) permutationCallCost K)
    (hs : ∀ sk r, QueryCostAtMost (S.overPermutation.sign sk r) permutationCallCost s)
    (hV : ∀ pk f, QueryCostAtMost (S.overPermutation.verify pk f) permutationCallCost V)
    (hsmall : K + maxRequests * s + V ≤ 2 ^ 128) :
    StronglyUnforgeable S.overPermutation maxRequests (slack + 1) bits := by
  intro q main hq hn
  rcases le_or_gt q (2 ^ 128) with hcap | hcap
  · set Q := K + (q + s * maxRequests) + V with hQdef
    have hQ : QueryCostAtMost (forgeryGame S.overPermutation main) permutationCallCost Q :=
      forgeryGame_cost _ main hK hs hV hq hn
    have hQle : Q ≤ 2 ^ 129 := by
      have : s * maxRequests = maxRequests * s := Nat.mul_comm _ _
      omega
    -- the game with the hash oracle, then on bytes
    let mainH : PK → OracleComp (KSpecH + (Req →ₒ Resp)) F := fun pk ↦ simulateQ embedS (main pk)
    let mainB : PK → OracleComp (KSpecB + (Req →ₒ Resp)) F :=
      fun pk ↦ simulateQ relabelS (mainH pk)
    have hQH : QueryCostAtMost (rpmGameH S mainH) permCallsH Q := by
      have h := hQ
      rw [forgeryGame_overPermutation, rpmGame_eq_expand, isWeightBound_expand_iff] at h
      exact h
    have hQB : QueryCostAtMost (rpmGameB digestBytesEquivBitVec S mainB) permCallsB Q := by
      have h := isWeightBound_relabel hQH
      rwa [rpmGame_relabel] at h
    have hprob : Pr{let b ← runWithRandomPermutation (forgeryGame S.overPermutation main)}[b = true]
        = Pr{let b ← rpmExperimentB digestBytesEquivBitVec S mainB}[b = true] := by
      rw [forgeryGame_overPermutation, rpmGame_eq_expand, runK_expand]
      exact (rpmExperiment_relabel S mainH).prEvent_eq _
    obtain ⟨h1, -⟩ := rpm_le_romB digestBytesEquivBitVec S mainB Q Q
      (hQB.mono_weight oracleCallsB_le_permCallsB) hQB
    have hrom' := hrom q (romAdvOf digestBytesEquivBitVec main)
      (fun pk ↦ romAdvOf_advHashCalls _ main q pk (hq pk))
      (fun pk ↦ romAdvOf_requestCalls _ main maxRequests pk (hn pk))
    rw [hprob]
    refine (h1.trans (add_le_add hrom' le_rfl)).trans ?_
    exact add_sq_le_succ hQle hbits
  · have := Common.le_succ_mul_inv_two_pow_of_lt (p :=
      Pr{let b ← runWithRandomPermutation (forgeryGame S.overPermutation main)}[b = true])
      (prEvent_le_one _) hbits (Q := q + slack) (by omega)
    refine this.trans (le_of_eq ?_)
    push_cast
    ring

end SufCma

end Common
