module

public import NativeRustcVmArm.Sumcheck.RoundPoly.Frame

/-!
# `sumcheck_round_poly`'s postcondition from its exits

A rejection (`post_none`: the model's `none`, X0 = `0`) and a success (`post_some`: the model's
`some`, X0 = `1`, the message and the `TState` its).
-/

namespace NativeRustcVmArm.Sumcheck.RoundPoly

open NativeRustcArm NativeRustcArm.Sym
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Sumcheck

public section

variable {a : DecArea} {s : TState} {e : Option EW} {m0 m : MachineData}

/-- The model's run. -/
abbrev runR (m0 : MachineData) (s : TState) (e : Option EW) : Option (Array EW × TState) :=
  (sumcheckRoundPoly m0.regs.X1.toNat ⟨m0.regs.X2, m0.regs.X3⟩ e).run s

/-- **A rejection.** -/
theorem post_none (hr : runR m0 s e = none) (hx0 : m.regs.X0 = 0)
    (hs : SameOutside m0.dmem m.dmem (Chg m0)) (hsv : Saved m0 m) :
    RoundPolyPost a s e m0 m := by
  refine ⟨?_, fun xs s' h ↦ ?_, fun xs s' h ↦ ?_, hs, hsv⟩
  · rw [hx0]; simp only [hr, Option.isSome_none, okWord]; rfl
  · simp [runR] at hr; simp [hr] at h
  · simp [runR] at hr; simp [hr] at h

/-- **A success.** -/
theorem post_some {msg : Array EW} {s' : TState} (hr : runR m0 s e = some (msg, s'))
    (hx0 : m.regs.X0 = 1) (hm : NativeRustcVm.EWsAt m.dmem (msgAt m0) msg.toList)
    (ht : TStateAt m.dmem (tAt m0) a s')
    (hs : SameOutside m0.dmem m.dmem (Chg m0)) (hsv : Saved m0 m) :
    RoundPolyPost a s e m0 m := by
  refine ⟨?_, fun xs s'' h ↦ ?_, fun xs s'' h ↦ ?_, hs, hsv⟩
  · rw [hx0]; simp only [hr, Option.isSome_some, okWord]; rfl
  · simp only [runR] at hr
    rw [hr, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact hm
  · simp only [runR] at hr
    rw [hr, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact ht

end

end NativeRustcVmArm.Sumcheck.RoundPoly
