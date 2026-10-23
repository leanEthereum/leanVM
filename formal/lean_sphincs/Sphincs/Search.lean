import Sphincs.Scheme
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.EvalDist.Sum
import VCVio.EvalDist.ProbabilityBounds

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

namespace Sphincs.Completeness

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
    failMass decode = Pr{let u ← ($ᵗ HashOutput : ProbComp HashOutput)}[decode u = none] :=
  (SampleableType.prEvent_uniformSample _).symm

/-- A query on an uncached input samples its answer uniformly. -/
theorem fresh_run (input : HashInput) (cache : QueryCache HashSpec) (hfresh : cache input = none)
    {δ : Type} (next : HashOutput × QueryCache HashSpec → ProbComp δ) (p : δ → Prop) :
    Pr{let x ← (randomOracle (spec := HashSpec) input).run cache >>= next}[p x]
      = ∑' u : HashOutput, (Fintype.card HashOutput : ℝ≥0∞)⁻¹
          * Pr{let x ← next (u, cache.cacheQuery input u)}[p x] := by
  rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, bind_map_left,
    show (uniformSampleImpl (spec := HashSpec) input) = ($ᵗ HashOutput : ProbComp HashOutput)
      from rfl, OracleComp.prEvent_bind_eq_tsum]
  exact tsum_congr fun u => by rw [SampleableType.prEvent_uniformSample_eq_singleton]

/-- A search over fresh inputs, distinct below `bound`, exhausts all `n` trials with probability at most the per-trial rejection share to the `n`. The bound is what the counter search needs: its inputs carry a 32-bit counter, so they repeat only after `2 ^ 32` trials, which is exactly its trial budget. -/
theorem probEvent_searchLoop (inputs : Nat → HashInput) (decode : HashOutput → Option β)
    (success : Nat → β → OracleComp HashSpec γ) (bound : Nat)
    (hinj : ∀ s s', s < bound → s' < bound → inputs s = inputs s' → s = s') :
    ∀ (n t : Nat), t + n ≤ bound → ∀ cache : QueryCache HashSpec,
      (∀ s, t ≤ s → s < bound → cache (inputs s) = none) →
      Pr{let r ← (simulateQ randomOracle (searchLoop inputs decode success n t)).run cache}[r.1 = none]
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
          Pr{let r ← ((simulateQ randomOracle
              (match decode u with
                | some value => some <$> success t value
                | none => searchLoop inputs decode success n (t + 1))).run
              (cache.cacheQuery (inputs t) u))}[r.1 = none]
            ≤ (if decode u = none then failMass decode ^ n else 0) := by
        intro u
        cases hu : decode u with
        | some value =>
            simp only [reduceCtorEq, ite_false, simulateQ_map, StateT.run_map, prEvent_map]
            simp
        | none =>
            simp only [ite_true]
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
      Pr{let x ← (simulateQ randomOracle (k r.1)).run r.2}[p x] ≤ b) :
    Pr{let y ← (simulateQ randomOracle (x >>= k)).run cache}[p y] ≤ b := by
  rw [simulateQ_bind, StateT.run_bind, OracleComp.prEvent_bind_eq_tsum]
  calc ∑' r : α × QueryCache HashSpec,
        Pr{let y ← (simulateQ randomOracle x).run cache}[y = r]
          * Pr{let x ← (simulateQ randomOracle (k r.1)).run r.2}[p x]
      ≤ ∑' r : α × QueryCache HashSpec, Pr{let y ← (simulateQ randomOracle x).run cache}[y = r] * b := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        by_cases hr : r ∈ support ((simulateQ randomOracle x).run cache)
        · exact mul_le_mul_right (hk r hr) _
        · simp [(prEvent_eq_zero_of_not_mem_support _) hr]
    _ ≤ b := by
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)

/-- A run fails only if its first part lands in `p`, or its continuation fails from a reachable state outside `p`. -/
theorem probEvent_bind_le_add {α δ : Type} (x : OracleComp HashSpec α)
    (k : α → OracleComp HashSpec δ) (p : α × QueryCache HashSpec → Prop)
    (q : δ × QueryCache HashSpec → Prop) (cache : QueryCache HashSpec) (b : ℝ≥0∞)
    (hk : ∀ r ∈ support ((simulateQ randomOracle x).run cache), ¬ p r →
      Pr{let x ← (simulateQ randomOracle (k r.1)).run r.2}[q x] ≤ b) :
    Pr{let y ← (simulateQ randomOracle (x >>= k)).run cache}[q y]
      ≤ Pr{let y ← (simulateQ randomOracle x).run cache}[p y] + b := by
  classical
  rw [simulateQ_bind, StateT.run_bind, OracleComp.prEvent_bind_eq_tsum,
    OracleComp.prEvent_eq_tsum_ite (oa := (simulateQ randomOracle x).run cache) (p := p)]
  calc ∑' r : α × QueryCache HashSpec,
        Pr{let y ← (simulateQ randomOracle x).run cache}[y = r]
          * Pr{let x ← (simulateQ randomOracle (k r.1)).run r.2}[q x]
      ≤ ∑' r : α × QueryCache HashSpec,
          ((if p r then Pr{let y ← (simulateQ randomOracle x).run cache}[y = r] else 0)
            + Pr{let y ← (simulateQ randomOracle x).run cache}[y = r] * b) := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        by_cases hr : r ∈ support ((simulateQ randomOracle x).run cache)
        · by_cases hp : p r
          · simp only [hp, ite_true]
            have hone : Pr{let x ← (simulateQ randomOracle (k r.1)).run r.2}[q x] ≤ 1 := (prEvent_le_one _)
            exact le_add_right (mul_le_of_le_one_right' hone)
          · simp only [hp, ite_false, zero_add]
            exact mul_le_mul_right (hk r hr hp) _
        · simp [(prEvent_eq_zero_of_not_mem_support _) hr]
    _ ≤ (∑' r : α × QueryCache HashSpec,
          if p r then Pr{let y ← (simulateQ randomOracle x).run cache}[y = r] else 0) + b := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
        have hmass : ∑' r : α × QueryCache HashSpec,
            Pr{let y ← (simulateQ randomOracle x).run cache}[y = r] ≤ 1 := (OracleComp.tsum_prEvent_le_one _)
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
              let secrets ← otsSecrets parameter lay tree leaf seed
              let values ← sequenceFin fun chainIdx =>
                chainWalk parameter lay tree leaf chainIdx 0 (encoding chainIdx).val (secrets chainIdx)
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

end Sphincs.Completeness
