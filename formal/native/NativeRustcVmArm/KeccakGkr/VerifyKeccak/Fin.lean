module

public import NativeRustcVmArm.Code.Vm.VerifyKeccak.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Entry

/-!
# `verify_keccak`'s postcondition from a state of the frame

`post_of`: from a state of the frame, X0 the model's verdict and, on `some`, its outputs in
memory, the postcondition. `goal_fail`: at `.LVerifyKeccak_31` with the model's `none`;
`goal_exit`: at the epilogue (`b73`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.KeccakGkr (scratchBytes outBytes KeccakOutAt)

public section

variable {a : DecArea} {s : TState} {cs : Array ColumnClaimW} {inst output : Array EW}
  {m0 : MachineData}

/-- The model's run. -/
abbrev run0 (s : TState) (inst output : Array EW) (m0 : MachineData) :=
  (NativeVm.Model.verifyKeccak m0.regs.X1.toNat inst output).run s

/-- **The postcondition** from a state of the frame. -/
theorem post_of [Labels] {m m' : MachineData} (hfr : VFr m0 m) (hd : m'.dmem = m.dmem)
    (hsv : Saved m0 m') (hx : m'.regs.X0 = okWord (run0 s inst output m0).isSome)
    (hok : ∀ outs pt sl s', run0 s inst output m0 = some ((outs, pt, sl), s') →
      TStateAt m.dmem (tA m0) a s' ∧
        NativeRustcVm.Layout.ClaimsWAt m.dmem (clA m0) (cs ++ outs) ∧
        KeccakOutAt m.dmem (oA m0) pt sl) :
    VerifyKeccakPost a s cs inst output m0 m' := by
  refine ⟨hx, fun outs pt sl s' hr ↦ ?_, fun q hq ↦ ?_, hsv⟩
  · rw [hd]; exact hok outs pt sl s' hr
  · rw [hd]
    refine hfr.same q fun h ↦ hq ?_
    rcases h with h | h
    · exact ⟨stackRegion m0 verifyKeccakStack, List.mem_cons_self, h⟩
    · rcases h with h | h | h | h
      · exact ⟨⟨tA m0, tstateBytes⟩, .tail _ (.head _), h⟩
      · exact ⟨⟨scA m0, scratchBytes⟩, .tail _ (.tail _ (.head _)), h⟩
      · exact ⟨⟨clA m0, NativeRustcVm.Layout.claimsBytes⟩, .tail _ (.tail _ (.tail _ (.head _))), h⟩
      · exact ⟨⟨oA m0, outBytes⟩, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), h⟩

variable [Host] {k : Nat}

/-- **The failure exit** with the model's `none`. -/
theorem goal_fail (hp : Placed code k) (hn : Nums a inst m0) {m : MachineData} (hfr : VFr m0 m)
    (hr : run0 s inst output m0 = none) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0)
      ⟨m, Labels.label NativeRustcVmArm.Vm.VerifyKeccak.label_31⟩ :=
  exitFail (Q := VerifyKeccakPost a s cs inst output m0) hp hn hfr fun m' _ hsv hx hd ↦
    post_of hfr hd hsv (by rw [hx, hr]; rfl) (fun _ _ _ _ h ↦ by rw [hr] at h; cases h)

/-- **The epilogue** (`b73`), X0 the model's verdict. -/
theorem goal_exit (hp : Placed code k) (hn : Nums a inst m0) {m : MachineData} (hfr : VFr m0 m)
    (hx : m.regs.X0 = okWord (run0 s inst output m0).isSome)
    (hok : ∀ outs pt sl s', run0 s inst output m0 = some ((outs, pt, sl), s') →
      TStateAt m.dmem (tA m0) a s' ∧
        NativeRustcVm.Layout.ClaimsWAt m.dmem (clA m0) (cs ++ outs) ∧
        KeccakOutAt m.dmem (oA m0) pt sl) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b73Offset)⟩ :=
  exitAt (Q := VerifyKeccakPost a s cs inst output m0) hp hn hfr fun _ _ hsv hx' hd ↦
    post_of hfr hd hsv (hx'.trans hx) hok

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
