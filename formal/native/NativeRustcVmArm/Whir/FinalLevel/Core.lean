module

public import NativeRustcVmArm.Whir.FinalLevel.End

/-!
# `final_level`: what lives after the rows' check

`Core`: `Base` and the folded scalars at the frame's byte `40`; kept by a block keeping
`coreRegs` and those bytes, or a call (`Core.saved`). Frame ranges apart (`Ctx.apart_locs`), a
frame's bytes across a call (`Ctx.keep_call`) or a block (`keep_block`).
-/

namespace NativeRustcVmArm.Whir.FinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters

public section

/-- **After the rows' check**: `Base`, the folded scalars. -/
structure Core (level : Whir.Level) (m0 st : MachineData) (folded : Array EW) : Prop where
  base : Base m0 st
  size : folded.size = 2 ^ mu m0 + level.fold
  fold : NativeRustcVm.EWsAt st.dmem (loc m0 40) folded.toList

/-- The registers `Core` reads. -/
@[expose] def coreRegs : List XReg := [.X19, .X20, .X21, .X27, .X28]

theorem Live.core {level : Whir.Level} {m0 st : MachineData} {folded : Array EW}
    (h : Live level m0 st folded) : Core level m0 st folded := ⟨h.base, h.size, h.fold⟩

theorem Core.fr {level : Whir.Level} {m0 st : MachineData} {folded : Array EW}
    (h : Core level m0 st folded) : FFr m0 st := h.base.fr

/-- `Core` kept. -/
theorem Core.saved {level : Whir.Level} {m0 st st' : MachineData} {folded : Array EW}
    (h : Core level m0 st folded) (hf : FFr m0 st')
    (hk : ∀ r ∈ coreRegs, st'.regs.getXReg r = st.regs.getXReg r)
    (hs : NativeRustcVm.Layout.Same st.dmem st'.dmem (loc m0 40) 1024)
    (h64 : 2 ^ mu m0 + level.fold ≤ 64) : Core level m0 st' folded where
  base := ⟨hf, (by rw [show st'.regs.X19 = st.regs.X19 from hk .X19 (by simp [coreRegs])]
                   exact h.base.x19),
    (hk .X20 (by simp [coreRegs])).trans h.base.x20,
    (hk .X21 (by simp [coreRegs])).trans h.base.x21,
    (hk .X27 (by simp [coreRegs])).trans h.base.x27,
    (hk .X28 (by simp [coreRegs])).trans h.base.x28⟩
  size := h.size
  fold := NativeRustcVm.Layout.BytesAt.of_same h.fold hs (by
    rw [NativeRustcVm.length_ewsBytes, Array.length_toList, h.size]; omega)

theorem coreRegs_cs : ∀ r ∈ coreRegs, calleeSaved r = true := by decide

/-- Callee-saved registers kept keep `coreRegs`. -/
theorem core_cs {st st' : MachineData}
    (hcs : ∀ r, calleeSaved r = true → st'.regs.getXReg r = st.regs.getXReg r) :
    ∀ r ∈ coreRegs, st'.regs.getXReg r = st.regs.getXReg r :=
  fun r hr ↦ hcs r (coreRegs_cs r hr)

/-- Bytes kept carry `EWsAt`. -/
theorem ewsAt_same {d d' : Mem 64} {x : BitVec 64} {xs : List EW} {n : Nat}
    (h : NativeRustcVm.EWsAt d x xs) (hs : NativeRustcVm.Layout.Same d d' x n)
    (hn : 16 * xs.length ≤ n) : NativeRustcVm.EWsAt d' x xs :=
  NativeRustcVm.Layout.BytesAt.of_same h hs (by rw [NativeRustcVm.length_ewsBytes]; exact hn)

/-- Bytes kept carry `EWAt`. -/
theorem ewAt_same {d d' : Mem 64} {x : BitVec 64} {e : EW} {n : Nat}
    (h : NativeRustcVm.EWAt d x e) (hs : NativeRustcVm.Layout.Same d d' x n) (hn : 16 ≤ n) :
    NativeRustcVm.EWAt d' x e :=
  NativeRustcVm.Layout.BytesAt.of_same h hs (by rw [NativeRustcVm.length_ewBytes]; exact hn)

section
variable [Labels] {a : DecArea} {s0 : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData}

namespace Ctx

variable (c : Ctx a s0 level ba b w rounds m0)
include c

/-- Frame ranges one below the other are apart. -/
theorem apart_locs {o n o' n' : Nat} (h : o + n ≤ o') (h' : o' + n' ≤ 2672) :
    Apart (loc m0 o) n (loc m0 o') n' := by
  unfold Apart
  rw [c.loc_nat (by omega), c.loc_nat (by omega)]
  omega

/-- A frame's bytes `[o, o + len)` across a call writing its stack and `[lo, lo + n)`. -/
theorem keep_call {st : MachineData} (hf : FFr m0 st) {N' : Nat}
    (hle : 2672 + N' ≤ finalLevelStack) {d' : Mem 64} {lo n : Nat}
    (hs : SameOutside st.dmem d' fun q ↦
      InRange (stackBelow st N') N' q ∨ InRange (loc m0 lo) n q ∨ outs m0 q)
    {o len : Nat} (hol : o + len ≤ lo ∨ lo + n ≤ o) (hln : lo + n ≤ 2672)
    (ho : o + len ≤ 2672) : NativeRustcVm.Layout.Same st.dmem d' (loc m0 o) len :=
  c.same_call hf hle hs ho hol hln

end Ctx

end

end

end NativeRustcVmArm.Whir.FinalLevel
