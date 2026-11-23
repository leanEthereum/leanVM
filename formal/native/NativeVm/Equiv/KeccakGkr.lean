module

public import NativeVm.Equiv.KeccakPure
public import NativeVm.Equiv.Transcript

/-!
# Phase 6: the model simulates `keccakPhase`

`Sim` for each transcript-reading function of `NativeVm/Model/KeccakGkr.lean` against the
statement's of the same name (`Statement/LeanVmVerifier.lean`): `sim_keccakOpen`,
`sim_verifyKeccakLayer`, `sim_keccakLayers`, `sim_verifyKeccak` and `sim_keccakPhase`. Each is
the composition of its steps' simulations (`Sim.bind` over `Sim.readScalars`, `Sim.grind`,
`Sim.sampleChallenge(s)`, `Sim.sumcheck`, `Sim.require`), its pure steps by
`NativeVm/Equiv/KeccakPure.lean`. A claim is related to the statement's by `KeccakClaimW.toSpec`,
the phase's result by `KeccakRel` (the column claims by `ColumnClaimW.toSpec`, the point and the
slices through `EW.toE`).
-/

public section

namespace NativeVm.Equiv.Keccak

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol

/-- `keccakOpen`'s results: the slot point, the weights and the value left, through `EW.toE`. -/
@[expose] def OpenRel (a : Array EW × Array EW × EW) (b : List E × List E × E) : Prop :=
  a.1.toList.map EW.toE = b.1 ∧ a.2.1.toList.map EW.toE = b.2.1 ∧ a.2.2.toE = b.2.2

/-- Phase 6's results: the column claims, the point and the slices of `q_keccak`. -/
@[expose] def KeccakRel (a : Array ColumnClaimW × Array EW × Array EW)
    (b : List Verifier.ColumnClaim × List E × List E) : Prop :=
  a.1.toList.map ColumnClaimW.toSpec = b.1 ∧ a.2.1.toList.map EW.toE = b.2.1 ∧
    a.2.2.toList.map EW.toE = b.2.2

theorem replicate_none_map (n : ℕ) :
    (Array.replicate n (none : Option EW)).toList.map (Option.map EW.toE) =
      List.replicate n none := by
  simp

theorem sim_keccakOpen (logSteps : ℕ) (claim : KeccakClaimW) (first count : ℕ) {value : EW}
    {value' : E} (hv : value.toE = value') :
    Sim (Model.keccakOpen logSteps claim first count value)
      (Verifier.keccakOpen logSteps claim.toSpec first count value') OpenRel := by
  unfold Model.keccakOpen Verifier.keccakOpen Model.sumcheckPlain
  refine Sim.bind (Sim.sumcheck hv _ (replicate_none_map _)) fun a b h ↦ ?_
  obtain ⟨slot, v⟩ := a
  obtain ⟨slot', v'⟩ := b
  obtain ⟨h1, h2⟩ := h
  dsimp only at h1 h2 ⊢
  refine Sim.pure ⟨h1, ?_, h2⟩
  rw [List.headD_eq_getD, ← h1, ← keccakSlotWeights_eq, ← openRows_eq, getD_rows]

theorem sim_verifyKeccakLayer (logSteps step : ℕ) (claim : KeccakClaimW) :
    Sim (Model.verifyKeccakLayer logSteps step claim)
      (Verifier.verifyKeccakLayer logSteps step claim.toSpec) (fun a b ↦ a.toSpec = b) := by
  unfold Model.verifyKeccakLayer Verifier.verifyKeccakLayer Model.sumcheckPlain
  dsimp only [KeccakClaimW.toSpec]
  refine Sim.bind (Sim.readScalars _) fun product product' hp ↦ ?_
  obtain ⟨rfl, -⟩ := hp
  refine Sim.bind (Sim.require ?_) fun _ _ _ ↦ ?_
  · rw [EW.beq_iff_toE, EW.toE_add, EW.toE_mul, projected_eq, eqKernel_drop, iota_eq, toE_sumE]
  refine Sim.bind (Sim.grind _) fun _ _ _ ↦ ?_
  refine Sim.bind Sim.sampleChallenge fun s s' hs ↦ ?_
  subst hs
  refine Sim.bind (Sim.sumcheck (toE_polyEval _ _) _ (by simp)) fun a b h ↦ ?_
  obtain ⟨point, v⟩ := a
  obtain ⟨point', v'⟩ := b
  obtain ⟨hpoint, hv⟩ := h
  dsimp only at hpoint hv ⊢
  refine Sim.bind (Sim.sumcheck hv _ (replicate_none_map _)) fun a b h ↦ ?_
  obtain ⟨localPoint, v⟩ := a
  obtain ⟨localPoint', v'⟩ := b
  obtain ⟨hlocal, hv⟩ := h
  dsimp only at hlocal hv ⊢
  subst hlocal hv
  refine Sim.bind (Sim.readScalars _) fun t t' ht ↦ ?_
  obtain ⟨rfl, -⟩ := ht
  refine Sim.bind (Sim.require ?_) fun _ _ _ ↦ ?_
  · simp only [EW.beq_iff_toE, EW.toE_add, EW.toE_mul, toE_dot, toList_extract_zero, List.map_take,
      toList_map_eqKernel, toE_sumE, keccakInstanceWeights_eq, toE_getD]
  refine Sim.bind (Sim.grind _) fun _ _ _ ↦ ?_
  refine Sim.bind Sim.sampleChallenge fun beta beta' hbeta ↦ ?_
  subst hbeta
  refine Sim.pure ?_
  simp only [Verifier.KeccakClaim.mk.injEq]
  refine ⟨?_, keccakInstanceWeights_eq _, hpoint, ?_⟩
  · simp only [EW.toE_add, EW.toE_mul, toE_getD]
  · rw [keccakLinearTranspose_eq]
    simp only [Array.toList_map, Array.toList_range, List.map_map, Function.comp_def, EW.toE_add,
      EW.toE_mul, toE_getD, toList_map_eqKernel]

theorem sim_keccakLayers (logSteps : ℕ) : ∀ (steps : List ℕ) (claim : KeccakClaimW),
    Sim (steps.foldlM (fun claim step ↦ Model.verifyKeccakLayer logSteps step claim) claim)
      (Verifier.keccakLayers logSteps steps claim.toSpec) (fun a b ↦ a.toSpec = b)
  | [], _ => Sim.pure rfl
  | step :: steps, claim => by
    rw [List.foldlM_cons, Verifier.keccakLayers]
    refine Sim.bind (sim_verifyKeccakLayer _ _ _) fun a b h ↦ ?_
    subst h
    exact sim_keccakLayers logSteps steps a

theorem sim_verifyKeccak (logSteps : ℕ) (inst output : Array EW) :
    Sim (Model.verifyKeccak logSteps inst output)
      (Verifier.verifyKeccak logSteps (inst.toList.map EW.toE) (output.toList.map EW.toE))
      KeccakRel := by
  have hseg : 1 < Verifier.keccakSegments := by decide
  unfold Model.verifyKeccak Verifier.verifyKeccak Model.keccakLayers Model.sumcheckPlain
  dsimp only
  simp only [hseg, ↓reduceIte]
  refine Sim.bind (Sim.grind _) fun _ _ _ ↦ ?_
  refine Sim.bind (Sim.sampleChallenges _) fun segment segment' hs ↦ ?_
  obtain ⟨rfl, -⟩ := hs
  refine Sim.bind (Sim.sampleChallenges _) fun lanePoint lanePoint' hl ↦ ?_
  obtain ⟨rfl, -⟩ := hl
  refine Sim.bind Sim.readScalar fun committed committed' hc ↦ ?_
  subst hc
  rw [← keccakFirstClaim_eq]
  refine Sim.bind (sim_keccakLayers _ _ _) fun claim claim' hclaim ↦ ?_
  subst hclaim
  refine Sim.bind (sim_keccakOpen _ _ _ _ rfl) fun a b h ↦ ?_
  obtain ⟨slot, weights, v⟩ := a
  obtain ⟨slot', weights', v'⟩ := b
  obtain ⟨h1, h2, h3⟩ := h
  dsimp only at h1 h2 h3 ⊢
  subst h1 h2 h3
  refine Sim.bind Sim.readScalar fun word word' hw ↦ ?_
  subst hw
  refine Sim.bind (Sim.require ?_) fun _ _ _ ↦ ?_
  · simp only [EW.beq_iff_toE, EW.toE_mul, toE_getD, List.headD_eq_getD]
  refine Sim.bind (R := fun o o' ↦ o.toList.map ColumnClaimW.toSpec = o') (Sim.pure ?_)
    fun outputs outputs' houtputs ↦ ?_
  · simp only [List.map_cons, List.map_nil, ColumnClaimW.toSpec,
      Array.toList_append, List.map_append, toList_extract_zero, toList_extract_size,
      List.map_take, List.map_drop]
  refine Sim.bind (Sim.sumcheck rfl _ (replicate_none_map _)) fun a b h ↦ ?_
  obtain ⟨low, v⟩ := a
  obtain ⟨low', v'⟩ := b
  obtain ⟨hlow, hv⟩ := h
  dsimp only at hlow hv ⊢
  subst hlow
  refine Sim.bind (sim_keccakOpen _ _ _ _ hv) fun a b h ↦ ?_
  obtain ⟨slot, weights, v⟩ := a
  obtain ⟨slot', weights', v'⟩ := b
  obtain ⟨h1, h2, h3⟩ := h
  dsimp only at h1 h2 h3 ⊢
  subst h1 h2 h3
  refine Sim.bind (Sim.readScalars _) fun slices slices' hsl ↦ ?_
  obtain ⟨rfl, -⟩ := hsl
  refine Sim.bind (Sim.require ?_) fun _ _ _ ↦ ?_
  · simp only [EW.beq_iff_toE, EW.toE_mul, toE_multilinearEval, toE_dot, KeccakClaimW.toSpec]
  refine Sim.pure ⟨houtputs, ?_, rfl⟩
  simp only [Array.toList_append, List.map_append, toList_extract_zero, List.map_take,
    KeccakClaimW.toSpec]

/-- **Phase 6**: the model's `keccakPhase` simulates the statement's, the layout read by
`LayoutW.toSpec` and the tables' evaluations through `EW.toE`. -/
theorem sim_keccakPhase (layout : LayoutW) (evaluations : Array (Array EW × Array EW))
    (evaluations' : List (List E × List E))
    (hev : evaluations.toList.map (fun (p, v) ↦ (p.toList.map EW.toE, v.toList.map EW.toE)) =
      evaluations') :
    Sim (Model.keccakPhase layout evaluations) (Verifier.keccakPhase layout.toSpec evaluations')
      KeccakRel := by
  unfold Model.keccakPhase Verifier.keccakPhase
  have hget : evaluations'.getD Verifier.opKeccak ([], []) =
      (fun (pv : Array EW × Array EW) ↦ (pv.1.toList.map EW.toE, pv.2.toList.map EW.toE))
        (evaluations.getD Verifier.opKeccak (#[], #[])) := by
    subst hev
    simp only [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_map,
      Array.getElem?_toList]
    cases evaluations[Verifier.opKeccak]? <;> rfl
  have hlog : layout.toSpec.tableLogHeights.getD Verifier.opKeccak 0 =
      layout.tableLogHeights.getD Verifier.opKeccak 0 := by
    simp [LayoutW.toSpec, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  rw [hget, hlog]
  obtain ⟨p, v⟩ := evaluations.getD Verifier.opKeccak (#[], #[])
  dsimp only
  have hout : (List.range 25).map
        (fun lane ↦ (v.toList.map EW.toE).getD (Verifier.keccakOut + lane) 0) =
      ((Array.range 25).map fun lane ↦ v.getD (Verifier.keccakOut + lane) 0).toList.map
        EW.toE := by
    simp only [Array.toList_map, Array.toList_range, List.map_map, Function.comp_def, toE_getD]
  rw [hout]
  exact sim_verifyKeccak _ _ _

end NativeVm.Equiv.Keccak
