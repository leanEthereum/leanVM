module

public import NativeRustcVmArm.Tables.PublicInputPhase.Calls

/-!
# `public_input_phase`: the two limbs' claims

At a limb's start (`LimbAt`, the frame from there on with no output): the registers, the frame's
point words, the claims so far, the public input, the `TState` after the challenge, the changes
since the entry. The second limb (`b6`, `multilinear_eval_by`, `b7`, `push_claim`, the exit `b8`:
`limb1`); the first (`b3`, `multilinear_eval_by`, `b4`, `push_claim`, `b5`: `limb0`), a failed
push straight to the exit.
-/

namespace NativeRustcVmArm.Tables.PublicInputPhase

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PublicInputPhase
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVm.Layout (claimsBytes ClaimsWAt claimCap pointCap)
open LeanVM.Protocol.Verifier (memory0 memory1)

@[expose] public section

/-- The memory placement's variable count. -/
abbrev vcOf (L : LayoutW) : Nat := (L.placement memory0).variableCount

/-- Where the phase writes: its stack, the `TState`, the claims. -/
def Out (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (base m0 publicInputPhaseStack) publicInputPhaseStack q ∨
    InRange m0.regs.X0.toBitVec tstateBytes q ∨ InRange m0.regs.X3.toBitVec claimsBytes q

/-- The first claim. -/
def claim0 (s : TState) (L : LayoutW) (pub : Vector UInt64 4) : ColumnClaimW :=
  ⟨memory0, pt s.sponge.squeeze.1 (vcOf L),
    multilinearEval #[EW.ofK pub[0], EW.ofK pub[2]] #[s.sponge.squeeze.1]⟩

/-- **At a limb's start**: the frame from here on with no output, the registers, the frame's
words `ws`, the claims `cs'`, the public input, the `TState` after the challenge, the changes since
the entry. -/
structure LimbAt [Labels] (a : DecArea) (s : TState) (L : LayoutW) (pub : Vector UInt64 4)
    (cs' : Array ColumnClaimW) (ws : List (Nat × UInt64)) (m0 m : MachineData) : Prop where
  fr : Fr (reb m0 m.dmem) 608 publicInputPhaseStack slots keep (fun _ ↦ False) m
  x19 : m.regs.getXReg .X19 = m0.regs.X3
  x20 : m.regs.getXReg .X20 = m0.regs.X2
  x21 : m.regs.getXReg .X21 = s.sponge.squeeze.1.c0
  x22 : m.regs.getXReg .X22 = s.sponge.squeeze.1.c1
  x23 : (m.regs.getXReg .X23).toNat = max (vcOf L) 1
  words : Bus.FrameWords m.dmem (base m0 608) ws
  claims : ClaimsWAt m.dmem m0.regs.X3.toBitVec cs'
  pub : NativeRustcVm.WordsAt m.dmem m0.regs.X2.toBitVec pub.toList
  ts : TStateAt m.dmem m0.regs.X0.toBitVec a { s with sponge := s.sponge.squeeze.2 }
  kept : Kept m0.dmem m.dmem
  same : SameOutside m0.dmem m.dmem (Out m0)

/-- What `public_input_phase` reaches. -/
abbrev Goal [Labels] (a : DecArea) (s : TState) (L : LayoutW) (pub : Vector UInt64 4)
    (cs : Array ColumnClaimW) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ PublicInputPhasePost a s L pub cs m0 st.data

end

public section

theorem pt_max (ch : EW) (v : Nat) : pt ch (max v 1) = pt ch v := by
  unfold pt
  congr 2
  omega

theorem push_push (cs : Array ColumnClaimW) (x y : ColumnClaimW) :
    (cs.push x).push y = cs ++ #[x, y] := by
  apply Array.toList_inj.mp
  simp

section
variable [Host] {k : Nat} {a : DecArea} {s : TState} {L : LayoutW} {pub : Vector UInt64 4}
  {cs : Array ColumnClaimW} {m0 : MachineData}

/-- **The exit** (`b8`): the registers restored, X0 kept, `ret`. -/
theorem exit8 (hp : Placed code k) (hS : StackOk m0 publicInputPhaseStack) {m : MachineData}
    {d : DataMem}
    (hfr : Fr (reb m0 d) 608 publicInputPhaseStack slots keep
      (fun q ↦ InRange m0.regs.X3.toBitVec claimsBytes q) m)
    (hk : Kept m0.dmem d) (hsame : SameOutside m0.dmem d (Out m0))
    (hpost : ∀ m' : MachineData, m'.dmem = m.dmem → m'.regs.X0 = m.regs.X0 →
      m'.regs.X0 = okWord (((publicInputPhase L pub).run s).isSome &&
        decide (cs.size + 2 ≤ claimCap)) ∧
      (∀ x s', (publicInputPhase L pub).run s = some (x, s') → cs.size + 2 ≤ claimCap →
        ClaimsWAt m'.dmem m0.regs.X3.toBitVec (cs ++ x)) ∧
      NextAt m'.dmem m0.regs.X0.toBitVec a ((publicInputPhase L pub).run s)) :
    Eventually (step1 Host.exe) (Goal a s L pub cs m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.PublicInputPhase.b8Offset)⟩ := by
  have hS1 := StackOk.rebase hS hk
  have hwf := Bus.wf_frame hS1 le_N hfr.kept
  have hm := Bus.match_frame hS1 le_N rfl hfr.sp
  refine exec_then (b8_in_code.trans hp.1 (by simp [b8])) run_b8 hwf hm fun st hm' hpc ↦ ?_
  have hm'' : Match (Env.ofMachine m [(base (reb m0 d) 608, 608)]) (Bus.after b8 sF) st.data := by
    rw [Bus.after_eq run_b8]; exact hm'
  obtain ⟨hok, hmem, h0⟩ := ok_b8
  obtain ⟨hret, hsv⟩ := hfr.exit hm'' hwf hok
  have hd : st.data.dmem = m.dmem := hm''.dmem_eq hwf hmem
  have e0 : st.data.regs.X0 = m.regs.X0 := Bus.Gkr.reg_of hm'' h0
  obtain ⟨p1, p2, p3⟩ := hpost st.data hd e0
  refine .done _ ⟨by simp only [PcOk] at hpc; rw [hpc, hret]; rfl, p1, p2, p3, ?_,
    Saved.rebase hk hsv⟩
  rw [hd]
  refine (NativeRustcVm.SameOutside.trans hsame hfr.same).mono fun q hq ↦ ?_
  rcases hq with (hq | hq | hq) | (hq | hq)
  · exact .inr (.inr hq)
  · exact .inl hq
  · exact .inr (.inl hq)
  · exact .inr (.inr hq)
  · exact .inr (.inl hq)

end

end

end NativeRustcVmArm.Tables.PublicInputPhase
