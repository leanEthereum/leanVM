module

public import NativeVm.Equiv.LayoutBuild
public import NativeVm.Equiv.Transcript

/-!
# Phase 1: the announced sizes and the layout

`Sim.readAnnouncedSizes`: the model's `readAnnouncedSizes` simulates the statement's on the
bytecode's lanes read as `K`, its layout the statement's through `LayoutW.toSpec`
(`buildLayout_toSpec`, `NativeVm/Equiv/LayoutBuild.lean`) and its rate exponent the statement's. An
announced size is the integer of a scalar's low limb (`getD_c0_toNat`), its high limb checked zero.
-/

@[expose] public section

namespace NativeVm.Equiv

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-- A lane's integer value. -/
theorem kToNat_ofLane (w : UInt64) : Verifier.kToNat (K.ofLane w) = w.toNat := rfl

/-- An announced size: an entry's low limb as an integer, a missing one `0`. -/
theorem getD_c0_toNat (a : Array EW) (l : List E) (h : a.toList.map EW.toE = l) (i : ℕ) :
    (a.getD i 0).c0.toNat = Verifier.kToNat ((l.getD i 0).limb 0) := by
  subst h
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_map,
    Array.getElem?_toList]
  rcases a[i]? with _ | x <;> simp [kToNat_ofLane]
  rfl

/-- **Phase 1** (`readAnnouncedSizes`): the layout read as the statement's, and the rate. -/
theorem Sim.readAnnouncedSizes (bytecode : Array UInt64) :
    Sim (Model.readAnnouncedSizes bytecode)
      (Verifier.readAnnouncedSizes (bytecode.toList.map K.ofLane))
      (fun a b ↦ a.1.toSpec = b.1 ∧ a.2 = b.2) := by
  unfold Model.readAnnouncedSizes Verifier.readAnnouncedSizes
  refine Sim.bind (Sim.readScalars _) fun a l ⟨hal, hlen⟩ ↦ ?_
  refine Sim.bind (Sim.require ?_) fun _ _ _ ↦ ?_
  · subst hal
    simp [Array.all_toList, K_ofLane_injective.eq_iff' K_ofLane_zero]
  have hm : (a.getD 0 0).c0.toNat = Verifier.kToNat ((l.headD 0).limb 0) := by
    rw [getD_c0_toNat a l hal 0]; cases l <;> rfl
  have hi : (a.back?.getD 0).c0.toNat = Verifier.kToNat ((l.getLastD 0).limb 0) := by
    subst hal
    rw [Array.back?_eq_getElem?, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
    simp only [List.length_map, Array.length_toList, List.getElem?_map, Array.getElem?_toList]
    rcases a[a.size - 1]? with _ | x <;> simp [kToNat_ofLane]
    rfl
  have hr : (Array.map (fun x ↦ x.c0.toNat) (a.extract 1 (1 + nTables))).toList =
      List.map (fun value ↦ Verifier.kToNat (value.limb 0))
        (List.take Verifier.tables.length (List.drop 1 l)) := by
    subst hal
    simp [Array.toList_extract, List.take_drop, nTables_eq, kToNat_ofLane, Function.comp_def]
    rw [Nat.add_comm]
    cases List.map (fun x ↦ x.c0.toNat) a.toList <;> simp
  simp only []
  rw [hm, hi, ← hr]
  refine Sim.bind (Sim.require (by simp)) fun _ _ _ ↦ ?_
  refine Sim.bind (Sim.liftOpt (R := fun lw L ↦ lw.toSpec = L) ?_) fun lw L hL ↦ ?_
  · rw [← buildLayout_toSpec]
    rcases buildLayout bytecode _ _ with _ | lw
    · exact .none
    · exact .some rfl
  subst hL
  exact Sim.bind (Sim.require (by simp [LayoutW.toSpec])) fun _ _ _ ↦ Sim.pure ⟨rfl, rfl⟩

end NativeVm.Equiv
