import SphincsFors.Scheme

/-!
# Exhausting a search

Both of the signer's searches walk a sequence of distinct hash inputs and stop at the first answer
that is accepted: the randomizer search over trial numbers, the counter search over counters. This
file bounds the probability that one such search exhausts every trial.

The argument is the lazy random oracle's defining property. An input the cache has never seen is
answered by a uniform draw, so one trial rejects with exactly the share of answers the acceptance
test rejects, and the answer it caches is at an input no later trial visits. Stepping the induction
therefore preserves the freshness hypothesis and multiplies one rejection factor per trial.
-/

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 10000

namespace SphincsFors.Completeness

variable {β γ : Type}

/-- A search: query `inputs t`, and stop at the first answer the decoder accepts, running `success` on what it decoded. Both of the signer's searches have this shape. -/
def searchLoop (inputs : Nat → HashInput) (decode : HashOutput → Option β)
    (success : Nat → β → OracleComp HashSpec γ) : Nat → Nat → OracleComp HashSpec (Option γ)
  | 0, _ => pure none
  | n + 1, t => do
      let answer ← Concrete.oracleHash (inputs t)
      match decode answer with
      | some value => some <$> success t value
      | none => searchLoop inputs decode success n (t + 1)

/-- The share of answers one trial rejects. -/
noncomputable def failMass (decode : HashOutput → Option β) : ℝ≥0∞ :=
  ((Finset.univ.filter fun u => decode u = none).card : ℝ≥0∞) / (Fintype.card HashOutput : ℝ≥0∞)

/-- The rejection share is the probability that one uniform answer is rejected. -/
theorem failMass_eq_probEvent (decode : HashOutput → Option β) :
    failMass decode = Pr[fun u => decode u = none | ($ᵗ HashOutput : ProbComp HashOutput)] :=
  (probEvent_uniformSample HashOutput _).symm

/-- A query on an uncached input samples its answer uniformly. -/
theorem fresh_run (input : HashInput) (cache : QueryCache HashSpec) (hfresh : cache input = none)
    {δ : Type} (next : HashOutput × QueryCache HashSpec → ProbComp δ) (p : δ → Prop) :
    Pr[p | (randomOracle (spec := HashSpec) input).run cache >>= next]
      = ∑' u : HashOutput, (Fintype.card HashOutput : ℝ≥0∞)⁻¹
          * Pr[p | next (u, cache.cacheQuery input u)] := by
  rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, map_eq_bind_pure_comp, bind_assoc]
  simp only [Function.comp_def, pure_bind]
  rw [show (uniformSampleImpl (spec := HashSpec) input) = ($ᵗ HashOutput : ProbComp HashOutput)
    from rfl, probEvent_bind_eq_tsum]
  exact tsum_congr fun u => by rw [probOutput_uniformSample]

/-- A search over fresh inputs, distinct below `bound`, exhausts all `n` trials with probability at most the per-trial rejection share to the `n`. The bound is what the counter search needs: its inputs carry a 32-bit counter, so they repeat only after `2 ^ 32` trials, which is exactly its trial budget. -/
theorem probEvent_searchLoop (inputs : Nat → HashInput) (decode : HashOutput → Option β)
    (success : Nat → β → OracleComp HashSpec γ) (bound : Nat)
    (hinj : ∀ s s', s < bound → s' < bound → inputs s = inputs s' → s = s') :
    ∀ (n t : Nat), t + n ≤ bound → ∀ cache : QueryCache HashSpec,
      (∀ s, t ≤ s → s < bound → cache (inputs s) = none) →
      Pr[fun r => r.1 = none |
          (simulateQ randomOracle (searchLoop inputs decode success n t)).run cache]
        ≤ failMass decode ^ n := by
  intro n
  induction n with
  | zero => intro t _ cache _; simp [searchLoop]
  | succ n ih =>
      intro t hbound cache hfresh
      rw [searchLoop]
      simp only [Concrete.oracleHash, HasQuery.query, simulateQ_bind, simulateQ_spec_query,
        StateT.run_bind]
      rw [fresh_run (inputs t) cache (hfresh t (Nat.le_refl t) (by omega))]
      have hterm : ∀ u : HashOutput,
          Pr[fun r => r.1 = none | (simulateQ randomOracle
              (match decode u with
                | some value => some <$> success t value
                | none => searchLoop inputs decode success n (t + 1))).run
              (cache.cacheQuery (inputs t) u)]
            ≤ (if decode u = none then failMass decode ^ n else 0) := by
        intro u
        cases hu : decode u with
        | some value =>
            simp only [reduceCtorEq, if_false, simulateQ_map, StateT.run_map, probEvent_map]
            simp
        | none =>
            simp only [if_true]
            refine ih (t + 1) (by omega) _ (fun s hs hsb => ?_)
            have hne : inputs s ≠ inputs t := fun hcon => by
              have hst := hinj s t hsb (by omega) hcon
              omega
            exact (QueryCache.cacheQuery_of_ne cache u hne).trans
              (hfresh s (Nat.le_of_succ_le hs) hsb)
      refine le_trans (ENNReal.tsum_le_tsum (fun u => mul_le_mul_right (hterm u) _)) ?_
      rw [tsum_fintype, Finset.sum_congr rfl (fun u _ => by rw [mul_ite, mul_zero]),
        Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
        pow_succ', failMass, div_eq_mul_inv, ← mul_assoc]

/-- A bound that holds from every reachable state holds for the whole run. -/
theorem probEvent_bind_le {α δ : Type} (x : OracleComp HashSpec α) (k : α → OracleComp HashSpec δ)
    (p : δ × QueryCache HashSpec → Prop) (cache : QueryCache HashSpec) (b : ℝ≥0∞)
    (hk : ∀ r ∈ support ((simulateQ randomOracle x).run cache),
      Pr[p | (simulateQ randomOracle (k r.1)).run r.2] ≤ b) :
    Pr[p | (simulateQ randomOracle (x >>= k)).run cache] ≤ b := by
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  calc ∑' r : α × QueryCache HashSpec,
        Pr[= r | (simulateQ randomOracle x).run cache]
          * Pr[p | (simulateQ randomOracle (k r.1)).run r.2]
      ≤ ∑' r : α × QueryCache HashSpec, Pr[= r | (simulateQ randomOracle x).run cache] * b := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        by_cases hr : r ∈ support ((simulateQ randomOracle x).run cache)
        · exact mul_le_mul_right (hk r hr) _
        · simp [probOutput_eq_zero_of_not_mem_support hr]
    _ ≤ b := by
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left' tsum_probOutput_le_one

/-- A run fails only if its first part lands in `p`, or its continuation fails from a reachable state outside `p`. -/
theorem probEvent_bind_le_add {α δ : Type} (x : OracleComp HashSpec α)
    (k : α → OracleComp HashSpec δ) (p : α × QueryCache HashSpec → Prop)
    (q : δ × QueryCache HashSpec → Prop) (cache : QueryCache HashSpec) (b : ℝ≥0∞)
    (hk : ∀ r ∈ support ((simulateQ randomOracle x).run cache), ¬ p r →
      Pr[q | (simulateQ randomOracle (k r.1)).run r.2] ≤ b) :
    Pr[q | (simulateQ randomOracle (x >>= k)).run cache]
      ≤ Pr[p | (simulateQ randomOracle x).run cache] + b := by
  classical
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum,
    probEvent_eq_tsum_ite (mx := (simulateQ randomOracle x).run cache) (p := p)]
  calc ∑' r : α × QueryCache HashSpec,
        Pr[= r | (simulateQ randomOracle x).run cache]
          * Pr[q | (simulateQ randomOracle (k r.1)).run r.2]
      ≤ ∑' r : α × QueryCache HashSpec,
          ((if p r then Pr[= r | (simulateQ randomOracle x).run cache] else 0)
            + Pr[= r | (simulateQ randomOracle x).run cache] * b) := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        by_cases hr : r ∈ support ((simulateQ randomOracle x).run cache)
        · by_cases hp : p r
          · simp only [hp, if_true]
            have hone : Pr[q | (simulateQ randomOracle (k r.1)).run r.2] ≤ 1 := probEvent_le_one
            exact le_add_right (mul_le_of_le_one_right' hone)
          · simp only [hp, if_false, zero_add]
            exact mul_le_mul_right (hk r hr hp) _
        · simp [probOutput_eq_zero_of_not_mem_support hr]
    _ ≤ (∑' r : α × QueryCache HashSpec,
          if p r then Pr[= r | (simulateQ randomOracle x).run cache] else 0) + b := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
        have hmass : ∑' r : α × QueryCache HashSpec,
            Pr[= r | (simulateQ randomOracle x).run cache] ≤ 1 := tsum_probOutput_le_one
        exact add_le_add le_rfl (mul_le_of_le_one_left' hmass)

/-! ## Distinct inputs

The counter rides in the hashed bytes, so trials below the wrap hash distinct inputs. -/
theorem bytesLE_inj {n : Nat} {x y : BitVec (8 * n)} (h : bytesLE n x = bytesLE n y) : x = y := by
  have hfun := List.ofFn_inj.mp h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : i / 8 < n := by omega
  have hbyte := congrFun hfun ⟨i / 8, hj⟩
  have hbits : (x.extractLsb' (8 * (i / 8)) 8) = (y.extractLsb' (8 * (i / 8)) 8) := by
    simpa using congrArg UInt8.toBitVec hbyte
  have hlsb := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8)) hbits
  simp only [BitVec.getLsbD_extractLsb'] at hlsb
  have hmod : i % 8 < 8 := by omega
  have hsum : 8 * (i / 8) + i % 8 = i := by omega
  simpa [hmod, hsum] using hlsb

/-- Counter inputs below the wrap are distinct. -/
theorem counter_bytes_inj {c c' : Nat} (hc : c < 2 ^ 32) (hc' : c' < 2 ^ 32)
    (h : (bytesLE 4 (BitVec.ofNat counterBits c) : HashInput)
        = bytesLE 4 (BitVec.ofNat counterBits c')) : c = c' := by
  have hv := congrArg BitVec.toNat (bytesLE_inj h)
  simp only [BitVec.toNat_ofNat, counterBits] at hv
  rwa [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] at hv

/-! ## The counter search

`otsSignFrom` walks counters from its starting value, hashing the layer message with each under the
leaf's encoding tweak and stopping at the first digest the target-sum code accepts. That is a search
over the encoding inputs. -/

open Concrete Seeded in
/-- The counter search, as a search over its encoding inputs. -/
theorem otsSignFrom_eq_searchLoop (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) (message : Digest) :
    ∀ (n t : Nat),
      (otsSignFrom parameter lay tree leaf seed message n t
        : OracleComp HashSpec (Option (Counter × (ChainIndex → Digest))))
        = searchLoop
            (fun c => tweakableHashInput parameter (.encoding lay tree leaf)
              (bytesLE 16 message ++ bytesLE 4 (BitVec.ofNat counterBits c)))
            (fun out => TargetSum.decodeDigest (truncateHash out))
            (fun c encoding => do
              let values ← otsValues parameter lay tree leaf seed fun chainIdx => (encoding chainIdx).val
              pure (BitVec.ofNat counterBits c, values))
            n t := by
  intro n
  induction n with
  | zero => intro t; rfl
  | succ n ih =>
      intro t
      rw [otsSignFrom, searchLoop]
      simp only [encode, tweakableHash, oracleHash, bind_assoc, pure_bind,
        map_eq_bind_pure_comp, Function.comp_def, ih]
      refine bind_congr fun answer => ?_
      cases TargetSum.decodeDigest (truncateHash answer) <;> rfl

end SphincsFors.Completeness
