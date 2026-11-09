module

public import XmssSecurity.Scan.Leaves
public import XmssSecurity.Scan.Selection

@[expose] public section

/-!
# A signing request at an unsigned leaf index

The signer selects a cached hit `y` with probability at most `W y / 2^128`, so it selects a partnered one with
probability at most `Φ / 2^128`.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Ghost

open Partner

set_option maxRecDepth 100000

theorem scan_landing_eq : Scan.landing = Partner.landing := by
  rw [Scan.landing, Partner.landing, div_eq_mul_inv]
  push_cast
  rfl

variable (secretKey : SecretKey)

theorem scanStatus_eq (leafIndex : LeafIndex) (message : Message) (cache : QueryCache HashSpec) :
    Scan.scanStatus secretKey leafIndex message cache =
      fun ρ => status cache secretKey.parameter leafIndex (message, ρ) := by
  funext ρ
  unfold Scan.scanStatus status input
  cases cache (Concrete.CacheView.encodingInput secretKey.parameter leafIndex (message, ρ)) with
  | none => rfl
  | some o => by_cases hv : TargetSum.ValidDigest (truncateHash o) <;> simp [hv]

theorem sign_select_le (leafIndex : LeafIndex) (message : Message) (cache : QueryCache HashSpec)
    (ρ : Randomness) (hy : IsHit cache secretKey.parameter leafIndex (message, ρ)) :
    Pr{let r ← (simulateQ romImpl (Concrete.scheme.sign secretKey leafIndex message)).run cache}[∃ s, r.1 = some s ∧ s.randomness = ρ] ≤
      W cache secretKey.parameter leafIndex (message, ρ) * ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ := by
  have hsample :
      (simulateQ romImpl (liftM Concrete.signingRandomness)).run cache =
        (fun base => (base, cache)) <$> Concrete.signingRandomness := by
    change (simulateQ (unifFwdImpl HashSpec +
        (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)))
      (liftM Concrete.signingRandomness)).run cache = _
    exact roSim.run_liftM (hashSpec := HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      Concrete.signingRandomness cache
  have hstatus : Scan.scanStatus secretKey leafIndex message cache ρ = .hit := by
    rw [scanStatus_eq]; exact (isHit_iff (message, ρ)).mp hy
  change Pr{let x ← ((simulateQ romImpl (Concrete.precomputedCappedSign secretKey leafIndex message)).run
    cache)}[∃ s, x.1 = some s ∧ s.randomness = ρ] ≤ _
  rw [Concrete.precomputedCappedSign, simulateQ_bind, StateT.run_bind, hsample,
    Concrete.signingRandomness_eq, bind_map_left]
  refine le_trans ?_ (Scan.selection_uniform_eq secretKey leafIndex message cache ρ hstatus).le |>.trans
    (le_of_eq ?_)
  · rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
    refine ENNReal.tsum_le_tsum fun base => mul_le_mul' le_rfl ?_
    rw [simulateQ_bind, StateT.run_bind]
    simp only [simulateQ_pure, StateT.run_pure]
    rw [bind_pure_comp, prEvent_map]
    refine prEvent_mono_of_support _ _ _ fun z _ h => ?_
    obtain ⟨s, hs, hρ⟩ := h
    refine ⟨s, ?_, hρ⟩
    split_ifs at hs
    exact hs
  · rw [scanStatus_eq, W, ← scan_landing_eq]
    congr 1

open Classical in
/-- **The signer selects a partnered input with probability at most `Φ / 2^128`.** -/
theorem sign_collision_le (leafIndex : LeafIndex) (message : Message) (cache : QueryCache HashSpec) :
    Pr{let r ← (simulateQ romImpl (Concrete.scheme.sign secretKey leafIndex message)).run cache}[(⟨⟨leafIndex, message⟩, r.1, cache, r.2⟩ : SigningCacheEntry).CachedSelectionCollision
          secretKey cache] ≤
      Φ cache secretKey.parameter leafIndex * ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ := by
  set S : Finset Randomness :=
    Finset.univ.filter fun ρ => IsPartnered cache secretKey.parameter leafIndex (message, ρ)
  calc _ ≤ Pr{let r ← (simulateQ romImpl (Concrete.scheme.sign secretKey leafIndex message)).run cache}[∃ ρ ∈ S, ∃ s, r.1 = some s ∧ s.randomness = ρ] := by
        refine prEvent_mono_of_support _ _ _ fun r hr hcol => ?_
        obtain ⟨sig, so, z, oo, hsig, hso, hoo, hz, htrunc⟩ := hcol
        refine ⟨sig.randomness, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, sig, hsig, rfl⟩
        exact ⟨so, hso, sign_selected_valid secretKey hr hsig hso, z, hz, oo, hoo, htrunc.symm⟩
    _ ≤ ∑ ρ ∈ S, Pr{let r ← (simulateQ romImpl (Concrete.scheme.sign secretKey leafIndex message)).run cache}[∃ s, r.1 = some s ∧ s.randomness = ρ] :=
        prEvent_exists_finset_le S _ _
    _ ≤ ∑ ρ ∈ S, W cache secretKey.parameter leafIndex (message, ρ) * ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ := by
        refine Finset.sum_le_sum fun ρ hρ => sign_select_le secretKey leafIndex message cache ρ ?_
        obtain ⟨o, ho, hv, -⟩ := (Finset.mem_filter.mp hρ).2
        exact ⟨o, ho, hv⟩
    _ ≤ _ := by
        rw [← Finset.sum_mul]
        refine mul_le_mul' ?_ le_rfl
        rw [Φ, Fintype.sum_prod_type, Finset.sum_filter]
        exact Finset.single_le_sum (f := fun m => ∑ ρ : Randomness,
          if IsPartnered cache secretKey.parameter leafIndex (m, ρ) then
            W cache secretKey.parameter leafIndex (m, ρ) else 0)
          (fun _ _ => zero_le) (Finset.mem_univ message)

end XmssSecurity.Ghost
