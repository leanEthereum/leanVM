module

public import NativeVm.Equiv.Gkr
public import NativeVm.Equiv.BusPure

/-!
# Phase 3: the bus simulates the statement's

`verifyBusBalance` (`NativeVm/Model/Bus.lean`) against the statement's
`verifyBusBalance computedBytecodeValue` on the layout's `LayoutW.toSpec`, the result related
through `BusResultW.toSpec`. The transcript's steps compose their simulations, the GKR walk is
`Sim.verifyGkrGrandProducts`, the bytecode's share `Sim.bytecodeShare` and its value
`Sim.computedBytecodeValue`; the leaf decomposition is pure (`NativeVm/Equiv/BusPure.lean`).
-/

@[expose] public section

namespace NativeVm.Equiv

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

theorem Sim.bytecodeShare (ws bl : Array EW) :
    Sim (Model.bytecodeShare ws bl)
      (Verifier.bytecodeShare (ws.toList.map EW.toE) (bl.toList.map EW.toE))
      fun a b ↦ a.1.toE = b.1 ∧ a.2.1.toList.map EW.toE = b.2.1 ∧ a.2.2.toE = b.2.2 := by
  unfold Model.bytecodeShare Verifier.bytecodeShare Model.sumcheckPlain
  refine Sim.bind Sim.readScalar fun sh sh' hsh ↦ ?_
  refine Sim.bind (Sim.sumcheck hsh _ (by simp)) ?_
  rintro ⟨x, cl⟩ ⟨x', cl'⟩ ⟨hx, hcl⟩
  refine Sim.bind Sim.readScalar fun v v' hv ↦ ?_
  refine Sim.bind (Sim.require ?_) fun _ _ _ ↦ Sim.pure ⟨hsh, by simp [hx], hv⟩
  rw [EW.beq_iff_toE, EW.toE_mul, toE_dot, toList_map_eqKernel]
  simp only at hx hcl ⊢
  rw [hx, hcl, hv]

theorem Sim.computedBytecodeValue (words : Array UInt64) (pt : Array EW) (v : EW) :
    Sim (Model.computedBytecodeValue words pt v)
      (Verifier.computedBytecodeValue (words.toList.map K.ofLane) (pt.toList.map EW.toE) v.toE)
      fun _ _ ↦ True := by
  unfold Model.computedBytecodeValue Verifier.computedBytecodeValue
  refine Sim.require ?_
  rw [EW.beq_iff_toE, toE_multilinearEval]
  simp [Function.comp_def]

/-- **Phase 3** (`verifyBusBalance computedBytecodeValue`). -/
theorem Sim.verifyBusBalance (layout : LayoutW) :
    Sim (Model.verifyBusBalance layout)
      (Verifier.verifyBusBalance Verifier.computedBytecodeValue layout.toSpec)
      fun a b ↦ a.toSpec = b := by
  have hpush := busLayout_toSpec #[0, layout.logMemory, layout.logBytecode] layout.push
  have hpull := busLayout_toSpec #[0, layout.logMemory, layout.logBytecode] layout.pull
  have hcount := busLayout_toSpec #[] layout.count
  unfold Model.verifyBusBalance Verifier.verifyBusBalance
  simp only [LayoutW.toSpec, ← hpush, ← hpull, ← hcount]
  refine Sim.bind (Sim.require decide_eq_true_iff) fun _ _ _ ↦ ?_
  refine Sim.bind (Sim.grind _) fun _ _ _ ↦ ?_
  refine Sim.bind (Sim.sampleChallenges _) fun w w' ⟨hw, _⟩ ↦ ?_
  refine Sim.bind Sim.sampleChallenge fun b b' hb ↦ ?_
  refine Sim.bind (Sim.verifyGkrGrandProducts _) ?_
  rintro ⟨cr, pt, tv⟩ ⟨cr', pt', tv'⟩ ⟨hcr, hpt, htv⟩
  simp only at hcr hpt htv ⊢
  subst hw hb hcr hpt htv
  refine Sim.bind (Sim.require ?_) fun _ _ _ ↦ ?_
  · rw [bne_iff_ne, ne_eq, ne_eq, ← EW.toE_zero, EW.toE_inj]
  refine Sim.bind (Sim.readScalars 2) fun m m' ⟨hm, hml⟩ ↦ ?_
  refine Sim.bind Sim.readScalar fun mf mf' hmf ↦ ?_
  refine Sim.bind Sim.readScalar fun bf bf' hbf ↦ ?_
  subst hm hmf hbf
  have hlow : ∀ n, List.take n (pt.toList.map EW.toE) = (pt.extract 0 n).toList.map EW.toE := by
    intro n; simp [Array.toList_extract, List.extract_eq_take_drop, List.map_take]
  simp only [hlow]
  refine Sim.bind (Sim.bytecodeShare _ _) ?_
  rintro ⟨sh, bp, v⟩ ⟨sh', bp', v'⟩ ⟨hsh, hbp, hv⟩
  simp only at hsh hbp hv ⊢
  subst hsh hbp hv
  refine Sim.bind (Sim.computedBytecodeValue _ _ _) fun _ _ _ ↦ ?_
  refine Sim.pure ?_
  have hf0 : formsToSpec (tablesW.map fun _ ↦ #[#[], #[], #[]]) =
      Verifier.tables.map fun _ ↦ [{}, {}, {}] := by
    simp [formsToSpec, tablesW, Function.comp_def]
    exact Or.inr rfl
  have hfp0 := fingerprints_toSpec w m (pt.extract 0 layout.logMemory)
    (pt.extract 0 layout.logBytecode) sh (Model.gpow 0) 1 1
  have hfp1 := fingerprints_toSpec w m (pt.extract 0 layout.logMemory)
    (pt.extract 0 layout.logBytecode) sh (Model.gpow (2 ^ layout.logBytecode - 1)) mf bf
  simp only [toE_gpow, EW.toE_one] at hfp0 hfp1
  rw [accumulateSide_eq hf0 rfl rfl hfp0 rfl rfl rfl (getD_toE tv 0).symm,
    accumulateSide_eq rfl rfl rfl hfp1 rfl rfl rfl (getD_toE tv 1).symm,
    accumulateSide_eq (ffp := #[]) (ffp' := []) (ws := #[1]) (ws' := [1]) rfl rfl rfl rfl
      (by simp) EW.toE_zero rfl (getD_toE tv 2).symm]
  obtain ⟨_ | ⟨m0, _ | ⟨m1, _ | ⟨_, _⟩⟩⟩⟩ := m <;> simp at hml
  simp [BusResultW.toSpec, ColumnClaimW.toSpec]

end NativeVm.Equiv
