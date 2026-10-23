import XmssSecurity.Proof.CappedGlobalChainOutputSimulation

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

noncomputable def globalChainTableHighViewOfMaterial
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial) :
    (GlobalChainValueIndex → Digest) × (GlobalChainEdgeIndex → Digest) :=
  let table := globalChainTrajectoryMaterialTable material
  (table, globalChainEdgeHighTableOfCache material.2.2 parameter table)

noncomputable def globalChainRandomnessOfMaterial
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial) :
    (ChainKey → ChainIndex → Digest) × GlobalChainEdgeOutputTable :=
  globalChainKeygenRandomnessOfView
    (globalChainTableHighViewOfMaterial parameter material)

theorem globalChainRandomnessOfMaterial_secret
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (hmaterial : material ∈ support
      (outputGlobalChainTrajectoryMaterial parameter)) :
    (globalChainRandomnessOfMaterial parameter material).1 = material.1 := by
  have hseeds := outputGlobalChainTrajectoryMaterial_seedsMatch parameter
    material hmaterial (fun _ => none)
  change (globalChainTableMaterialEquiv
    (globalChainTrajectoryMaterialTable material)).1 = material.1
  funext key chain
  have h := (hseeds key chain).symm
  rw [startSecretKey_keyChainStart_apply] at h
  exact h

theorem globalChainRandomnessOfMaterial_output_cached
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (hmaterial : material ∈ support
      (outputGlobalChainTrajectoryMaterial parameter))
    (edge : GlobalChainEdgeIndex) :
    material.2.2
        (globalChainTableEdgeInput parameter
          (globalChainTrajectoryMaterialTable material) edge) =
      some ((globalChainRandomnessOfMaterial parameter material).2 edge) := by
  have hmatches := outputGlobalChainTrajectoryMaterial_edgesMatch parameter
    material hmaterial
  obtain ⟨output, hcached, htarget⟩ := hmatches edge
  have houtput : (globalChainRandomnessOfMaterial parameter material).2 edge =
      output := by
    change globalChainEdgeOutputFromHigh
        (globalChainEdgeHighTableOfCache material.2.2 parameter
          (globalChainTrajectoryMaterialTable material))
        (globalChainTrajectoryMaterialTable material) edge = output
    exact globalChainEdgeOutputFromHigh_eq_cached material.2.2 parameter
      (globalChainTrajectoryMaterialTable material) edge output hcached htarget
  rw [houtput]
  exact hcached

theorem globalChainRandomnessOfMaterial_eq_outputTraceRandomness
    (parameter : PublicParameter)
    (trace : OutputTrace GlobalChainTrajectoryMaterial)
    (htrace : trace ∈ support
      (outputGlobalChainTrajectoryMaterialTrace parameter)) :
    globalChainRandomnessOfMaterial parameter trace.1 =
      outputTraceRandomness trace := by
  have hmaterial :=
    outputGlobalChainTrajectoryMaterialTrace_material_support parameter trace
      htrace
  apply Prod.ext
  · exact globalChainRandomnessOfMaterial_secret parameter trace.1 hmaterial
  · change (globalChainRandomnessOfMaterial parameter trace.1).2 =
      globalChainEdgeOutputTableOfOutputTape trace.2
    rw [globalChainEdgeOutputTableOfOutputTrace_eq_cached parameter trace
      htrace]
    funext edge
    unfold globalCachedOutputOfTrajectories
    symm
    change (trace.1.2.2 (globalChainTableEdgeInput parameter
      (globalChainTrajectoryMaterialTable trace.1) edge)).getD 0 = _
    rw [globalChainRandomnessOfMaterial_output_cached parameter trace.1
      hmaterial edge]
    simp

theorem evalDist_outputGlobalChainRandomness_eq_uniform
    (parameter : PublicParameter) :
    (globalChainRandomnessOfMaterial parameter <$>
      outputGlobalChainTrajectoryMaterial parameter) =ᵈ
    uniformGlobalChainKeygenRandomness := by
  calc
    _ =ᵈ ((globalChainRandomnessOfMaterial parameter ∘ Prod.fst) <$>
        outputGlobalChainTrajectoryMaterialTrace parameter) := by
      rw [← outputGlobalChainTrajectoryMaterialTrace_fst parameter,
        Functor.map_map]
      rfl
    _ =ᵈ (outputTraceRandomness <$>
        outputGlobalChainTrajectoryMaterialTrace parameter) := by
      refine EvalDistEq.of_eq ?_
      simp only [map_eq_bind_pure_comp]
      apply OracleComp.bind_congr_of_forall_mem_support
      intro trace htrace
      change pure (globalChainRandomnessOfMaterial parameter trace.1) =
        pure (outputTraceRandomness trace)
      rw [globalChainRandomnessOfMaterial_eq_outputTraceRandomness parameter
        trace htrace]
    _ =ᵈ uniformGlobalChainKeygenRandomness :=
      evalDist_outputTraceRandomness_eq_uniform parameter

end XmssSecurity.CappedChain
