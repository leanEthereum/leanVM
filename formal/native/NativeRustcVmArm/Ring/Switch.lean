module

public import NativeRustcVmArm.Code.Vm.RingCoefficients.Names
public import NativeRustcVmArm.Code.Vm.RingSwitch.Names
public import NativeRustcVmArm.Code.Vm.RingTarget.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TStateSampleChallenges.Names
public import NativeRustcVmArm.Ring.Switch.Tail

/-!
# `ring_switch`'s contract

The prologue and `grind(13)` (`b0`), the branch on its result (`b1`): on `None` the epilogue
(`b6`); on `Some`, the 16 challenges (`b2`), the coefficients from `f`, `g` (`b3`), the target
(`b4`), its store and `Some(())` (`b5`), the epilogue (`b6`).
-/

namespace NativeRustcVmArm.Ring.Switch

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.RingSwitch

public section

variable {m0 : MachineData} {a : DecArea} {s : TState}

/-- What changed since the entry: the `RingW`, the `TState`, the stack. -/
theorem post_same [Labels] {m : MachineData} (hfr : SFr m0 m) :
    SameOutside m0.dmem m.dmem (fun q ↦ InRange (oA m0) ringWBytes q ∨
      InRange (tA m0) tstateBytes q ∨
      InRange (stackBelow m0 ringSwitchStack) ringSwitchStack q) := fun q hq ↦
  hfr.same q fun hh ↦ hq (by
    rcases hh with hh | hh | hh
    · exact .inr (.inr hh)
    · exact .inl hh
    · exact .inr (.inl hh))

variable [Host] {k : Nat}

/-- **`ring_switch`'s contract.** -/
theorem ringSwitch_spec (hp : Placed code k)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    (hrc : Spec (Labels.label NativeRustcVmArm.Vm.RingCoefficients.entryLabel) RingCoefficientsPre RingCoefficientsPost)
    (hrt : Spec (Labels.label NativeRustcVmArm.Vm.RingTarget.entryLabel) RingTargetPre RingTargetPost)
    (a : DecArea) (s : TState) (point : Array EW) :
    Spec (Labels.label NativeRustcVmArm.Vm.RingSwitch.entryLabel) (RingSwitchPre a s) (RingSwitchPost a s point) := by
  intro m0 h
  rw [show Labels.label NativeRustcVmArm.Vm.RingSwitch.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.RingSwitch.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.RingSwitch.entryOffset) NativeRustcVmArm.Vm.RingSwitch.entry_at]
  have hb6 : b6.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.RingSwitch.b6Offset) := hb b6_in_code (by simp [b6]) hp
  refine stepEntry hp h hgr fun m2 hfr2 h19 h20 h21 hx0 hnext ↦ ?_
  cases hg : (grind LeanVM.Parameters.Whir.batchGrindingBits).run s with
  | none =>
    rw [hg] at hx0
    refine stepBranch hp h hfr2 h19 h20 h21 (s1 := s) (b := false) (fun hf ↦ nomatch hf) hx0
      (fun m' hfr' _ hx' _ ↦ ?_) (fun _ _ _ hf ↦ nomatch hf)
    refine (stepExit h hb6 hfr').mono fun st ⟨hpc, hS, hd, hx⟩ ↦ ⟨hpc, ?_, ?_, ?_, hS⟩
    · rw [hx, hx', ringSwitch_none hg]
      rfl
    · intro x s' hr
      rw [ringSwitch_none hg] at hr
      cases hr
    · intro q hq
      rw [hd]
      exact post_same hfr' q hq
  | some p =>
    obtain ⟨⟨⟩, t1⟩ := p
    rw [hg] at hx0
    have hts1 := hnext () t1 hg
    refine stepBranch hp h hfr2 h19 h20 h21 (s1 := t1) (b := true) (fun _ ↦ hts1) hx0
      (fun _ _ _ _ hf ↦ nomatch hf) fun m3 hG hx3 _ ↦ ?_
    refine stepSample hp h hsc hG hx3 fun m4 xs t2 hrun hG2 ↦ ?_
    refine stepCoeff hp h hrc hG2 fun m5 hG3 ↦ ?_
    refine stepTarget hp h hrt hG3 fun m6 hG4 ↦ ?_
    refine stepStore hp h hG4 hG2.sz fun m7 hG5 ↦ ?_
    have hr := ringSwitch_some (point := point) (s := arr m0 m0.regs.X1 coeffCount) hg hrun
    refine (stepExit h hb6 hG5.fr).mono fun st ⟨hpc, hS, hd, hx⟩ ↦ ⟨hpc, ?_, ?_, ?_, hS⟩
    · rw [hx, hG5.x0, hr]
      rfl
    · intro x s' hx'
      rw [hr] at hx'
      cases hx'
      exact ⟨by rw [hd]; exact hG5.ring, by rw [hd]; exact hG5.ts⟩
    · intro q hq
      rw [hd]
      exact post_same hG5.fr q hq

end

end NativeRustcVmArm.Ring.Switch
