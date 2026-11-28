module

public import NativeRustcVmX64.Sumcheck.Layer.Tail
public import NativeRustcVmX64.Code.Vm.PolyEval.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfVerifyLayer.Names
public import NativeRustcVmX64.Code.Vm.TStateSumcheckRoundPoly.Names

/-!
# `TState::sumcheck` with `verify_layer`'s closure on x86-64

**`sumcheckLayer_spec`**: the entry, the loop over the slots (a round each: `head_spec`,
`tail_spec`), the exit; the output holds `sumcheckFn claim count (pt[·]?) n`'s claim, the slots
its challenges, the `TState` its state (`SumcheckLayerPost`).
-/

namespace NativeRustcVmX64.Sumcheck.Layer

open NativeRustcX64 NativeRustcVmX64.Vm.SumcheckOfVerifyLayer
open NativeVm.Model NativeRustcVm.Transcript

public section

variable [Host] {k : Nat}

/-- **The loop**: from the head, the exit on a rejection or `.L8` after the last round. -/
theorem loop_spec (hp : Placed code k)
    (hrp : ∀ a s e, Spec (Labels.label NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.entryLabel) (RoundPolyPre a s e) (RoundPolyPost a s e))
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hpe : Spec (Labels.label NativeRustcVmX64.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    {a : DecArea} {s : TState} {pt : Array EW} {n : Nat} {m0 : MachineData}
    (hpre : LPre a s pt n m0) {i : Nat} {m : MachineData} (hi : Inv a s pt n m0 i m) :
    Eventually (step1 Host.exe) (Goal a s pt n m0 k) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b2Offset)⟩ := by
  refine Sym.loop (fun c st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b2Offset) ∧
      ∃ i, n - i = c ∧ Inv a s pt n m0 i st.data) (fun c st ⟨hpc, i, hc, hi⟩ ↦ ?_)
    ⟨rfl, i, rfl, hi⟩
  obtain ⟨d, pc⟩ := st
  simp only at hpc
  subst hpc hc
  have hl := hi.lt
  refine Eventually.bind (head_spec hp hrp hpre hi) fun st h ↦ ?_
  rcases h with h | ⟨hpc, xs, msg, s1, hmid⟩
  · exact Eventually.done _ (.inl h)
  obtain ⟨d', pc'⟩ := st
  simp only at hpc
  subst hpc
  refine Eventually.mono (tail_spec hp hsq hpe hpre hmid) fun st h ↦ ?_
  rcases h with h | ⟨hpc, hinv⟩
  · exact .inl h
  · exact .inr ⟨n - (i + 1), by omega, hpc, i + 1, rfl, hinv⟩

/-- **`sumcheck` with `verify_layer`'s closure: its contract.** -/
theorem sumcheckLayer_spec (hp : Placed code k)
    (hrp : ∀ a s e, Spec (Labels.label NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.entryLabel) (RoundPolyPre a s e) (RoundPolyPost a s e))
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hpe : Spec (Labels.label NativeRustcVmX64.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    (a : DecArea) (s : TState) (pt : Array EW) :
    Spec (Labels.label NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.entryLabel) (SumcheckLayerPre a s pt) (SumcheckLayerPost a s pt) := by
  intro m0 hpre0
  have hpre : LPre a s pt (stackArg m0 1).toNat m0 := ⟨hpre0, rfl⟩
  generalize (stackArg m0 1).toNat = n at hpre
  rw [show Labels.label NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b0Offset) from hp.label NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.entry_at]
  have fin : ∀ st : MachineState, Goal a s pt n m0 k st →
      Eventually (step1 Host.exe)
        (fun st' ↦ st'.pc = retOf m0 ∧ rspOf st'.data = rspOf m0 + 8#64 ∧
          LPost a s pt n m0 st'.data) st := by
    intro st h
    rcases h with h | ⟨hpc, hd⟩
    · exact Eventually.done _ h
    · obtain ⟨d, pc⟩ := st
      simp only at hpc
      subst hpc
      exact exit_done hp hpre hd
  refine Eventually.bind (entry_spec hp hpre) fun st h ↦ ?_
  rcases h with ⟨hpc, hd⟩ | ⟨hpc, hinv⟩
  · exact fin st (.inr ⟨hpc, hd⟩)
  · obtain ⟨d, pc⟩ := st
    simp only at hpc
    subst hpc
    exact Eventually.bind (loop_spec hp hrp hsq hpe hpre hinv) fin

end

end NativeRustcVmX64.Sumcheck.Layer
