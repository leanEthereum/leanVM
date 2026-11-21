module

public import Common.MultiKey.Bad

@[expose] public section

/-!
# The multi-key random-oracle bound from the single-key one

`romBoundMulti_of_romBoundAdv`: a scheme with the single-key random-oracle bound
`(q + slack) / 2^bits` at the adversary's own count (`RomBoundAdv`), the reduction's separation
facts (`Separation`) and a clash bound `ε ≤ 2^-bits` of a fresh key against any fixed key has the
multi-key bound `k · (q + slack + (k - 1)) / 2^bits` (`RomBoundMulti`).

The forgery names its key, so the multi-key win is the union over `i` of "the forgery is under key
`i` and wins" (the factor `k`). For each `i` that event is, with one oracle, the tagged game's
(`prob_multiGame_eq_untag`); with two oracles it is the single-key game against the reduction for
key `i` (`prob_taggedGame_eq`), which makes the adversary's own `q` hash calls and its requests to
key `i` alone (`reduction_advHashCalls`, `reduction_requestCalls`), so `RomBoundAdv` bounds it by
`(q + slack) / 2^bits`: the other keys' hashing is answered by the reduction's private oracle and
costs nothing. The two worlds differ only when an input is asked of both oracles
(`prEvent_untag_le`), which needs key `i` to clash with one of the `k - 1` others
(`prob_bad_le`, `(k - 1) ε`, the term `k (k - 1) / 2^bits` in all).
-/

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Common.SufCma.MultiKey

variable {Seed PK SK Req Resp F : Type}

/-- **The multi-key random-oracle bound.** -/
theorem romBoundMulti_of_romBoundAdv (S : SchemeWithHash Seed PK SK Req Resp F)
    (ownedPub : PK → List UInt8 → Prop) [∀ pk, DecidablePred (ownedPub pk)] (k : ℕ)
    {bits slack maxRequests : ℕ} (hS : RomBoundAdv S bits slack maxRequests)
    (sep : Separation S ownedPub) {ε : ℝ≥0∞}
    (hclash : ∀ zb, IsKey S zb → Pr{let z ← romRun (freshRec S) ∅}[Clash ownedPub z.1 zb] ≤ ε)
    (hε : ε ≤ ((2 ^ bits : ℕ) : ℝ≥0∞)⁻¹) :
    RomBoundMulti S k bits slack maxRequests := by
  intro q main hq hn
  set D : ℝ≥0∞ := ((2 ^ bits : ℕ) : ℝ≥0∞)
  -- the forgery under each key `i`
  have hi : ∀ i : Fin k, Pr{let z ← romRun (multiGameIdx S main) ∅}[z.1 = (i, true)] ≤
      ((q : ℝ≥0∞) + slack + ((k - 1 : ℕ) : ℝ≥0∞)) / D := by
    intro i
    rw [prob_multiGame_eq_untag S ownedPub i main]
    refine (prEvent_untag_le (taggedGame S ownedPub i main) fun y ↦ y.1 = (i, true)).trans ?_
    have h1 : Pr{let z ← (simulateQ TagSpec.romImpl (taggedGame S ownedPub i main)).run ∅}[
        z.1.1 = (i, true)] ≤ ((q : ℝ≥0∞) + slack) / D := by
      refine (prEvent_mono_of_support _ _ (fun z ↦ z.1.1.2 = true) fun z _ h ↦ by
        rw [h]).trans ?_
      rw [prob_taggedGame_eq S ownedPub i main]
      exact hS q _ (reduction_advHashCalls S ownedPub i main q hq)
        (reduction_requestCalls S ownedPub i main maxRequests fun pks ↦ hn pks i)
    have h2 := prob_bad_le S ownedPub sep i main hclash
    calc _ ≤ ((q : ℝ≥0∞) + slack) / D + ((k - 1 : ℕ) : ℝ≥0∞) * ε := add_le_add h1 h2
      _ ≤ ((q : ℝ≥0∞) + slack) / D + ((k - 1 : ℕ) : ℝ≥0∞) / D := by
        gcongr
        rw [div_eq_mul_inv]
        gcongr
      _ = _ := ENNReal.div_add_div_same
  rw [prob_romExperiment, romGame_multiKey, simulateQ_map, StateT.run'_eq, StateT.run_map,
    Functor.map_map, prEvent_map]
  calc _ ≤ Pr{let z ← romRun (multiGameIdx S main) ∅}[∃ i, z.1 = (i, true)] :=
        prEvent_mono_of_support _ _ _ fun z _ h ↦ ⟨z.1.1, Prod.ext rfl h⟩
    _ ≤ ∑ i : Fin k, Pr{let z ← romRun (multiGameIdx S main) ∅}[z.1 = (i, true)] :=
        prEvent_exists_le _ _
    _ ≤ ∑ _i : Fin k, ((q : ℝ≥0∞) + slack + ((k - 1 : ℕ) : ℝ≥0∞)) / D :=
        Finset.sum_le_sum fun i _ ↦ hi i
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_assoc]

/-- **Multi-key strong unforgeability over `π`, from the single-key random-oracle bound.** A
hash-query scheme with the single-key bound `(q + slack) / 2^bits` (`RomBoundAdv`), the
separation facts for a public ownership `ownedPub`, a clash bound `ε ≤ 2^-bits` of a fresh key
against any fixed one, and key generation, signer and verifier over `π` of at most `K`, `s` per
request and `V` permutation calls with `K + maxRequests · s + V ≤ 2^128`, is multi-key strongly
unforgeable for up to `2^32` keys: `k · (q + (slack + 1) + k) · 2^-bits`. The factor `k` is the
union over the key the forgery names; `k (k - 1)` is a clash of the forged key with another
(`prob_bad_le`); the other keys' hashing is answered by the reduction's private random oracle and
costs nothing (`reduction_advHashCalls`); the `1` beside `slack` is the sponge's
indifferentiability over the whole `k`-key game (`multiKey_of_romBoundMulti`). -/
theorem multiKeyStronglyUnforgeable_of_romBoundAdv (S : SchemeWithHash Seed PK SK Req Resp F)
    (ownedPub : PK → List UInt8 → Prop) [∀ pk, DecidablePred (ownedPub pk)]
    {bits slack maxRequests K s V : ℕ} (hbits : bits ≤ 128)
    (hS : RomBoundAdv S bits slack maxRequests) (sep : Separation S ownedPub) {ε : ℝ≥0∞}
    (hclash : ∀ zb, IsKey S zb → Pr{let z ← romRun (freshRec S) ∅}[Clash ownedPub z.1 zb] ≤ ε)
    (hε : ε ≤ ((2 ^ bits : ℕ) : ℝ≥0∞)⁻¹)
    (hK : ∀ seed, QueryCostAtMost (S.overPermutation.generateKeys seed) permutationCallCost K)
    (hs : ∀ sk r, QueryCostAtMost (S.overPermutation.sign sk r) permutationCallCost s)
    (hV : ∀ pk f, QueryCostAtMost (S.overPermutation.verify pk f) permutationCallCost V)
    (hsmall : K + maxRequests * s + V ≤ 2 ^ 128) :
    MultiKeyStronglyUnforgeable S.overPermutation (2 ^ 32) maxRequests (slack + 1) bits :=
  fun k hk1 hk q main hq hn ↦ multiKey_of_romBoundMulti S hbits hk1 hk
    (romBoundMulti_of_romBoundAdv S ownedPub k hS sep hclash hε) hK hs hV hsmall q main hq hn

end Common.SufCma.MultiKey
