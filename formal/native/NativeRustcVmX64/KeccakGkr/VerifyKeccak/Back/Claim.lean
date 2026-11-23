module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.Push
public import NativeRustcVmX64.Code.Vm.BufEW36Extend.Names
public import NativeRustcVmX64.Code.Vm.PushClaim.Names

/-! # Constructing and pushing the committed output claim (blocks 47–54) -/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.KeccakGkr.SeqZ NativeVm.Model
open NativeRustcVm.Transcript (DecArea TStateAt)
open NativeRustcVm.KeccakGkr (off ClaimAt WeightsAt)

public section

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

theorem At.widen {p : Nat} {T : SState} {vals : Nat → BitVec 64} {st : MachineState}
    {wr wr' : Nat → Bool} (hat : At m0 k p wr T vals st)
    (hw : ∀ i, wr i = true → wr' i = true) : At m0 k p wr' T vals st :=
  ⟨hat.1, ⟨hat.2.mt, same_mono hw hat.2.same, hat.2.kept⟩⟩

theorem claims_bound (hpre : VerifyKeccakPre a s cs inst output m0)
    {p : Nat} {T : SState} {vals : Nat → BitVec 64} {st : MachineState}
    (hat : At m0 k p wrA T vals st) :
    NativeRustcVm.Layout.ClaimsWAt st.data.dmem (keccakClaims m0) cs := by
  have c := ctx_of hpre
  apply NativeRustcVm.Tables.ClaimsWAt.of_same hpre.2.2.2.2.2.2.1
  exact same_ro c hat.2.same c.cW c.cS (fun _ ↦ c.tc.symm) (fun _ ↦ c.sc.symm)
    (fun h ↦ by cases h) (fun h ↦ by cases h)

theorem claimStep (hp : Placed NativeRustcVmX64.Vm.VerifyKeccak.code k)
    (hpre : VerifyKeccakPre a s cs inst output m0)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36))
    (hpush : ∀ cs, Spec (Labels.label NativeRustcVmX64.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    {st : MachineState} {V : Vs} {slot : Array EW} {w : EW} {s1 : TState} {cl : KeccakClaimW}
    (hat : At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b47Offset wrA t45 (vv m0 V) st)
    (hw0 : V.w0 = w.c0.toBitVec) (hw1 : V.w1 = w.c1.toBitVec)
    (hslot : NativeRustcVm.EWsAt st.data.dmem (off (fb m0) 232) slot.toList)
    (h6 : slot.size = 6)
    (hts : TStateAt st.data.dmem (reg m0 .rdi) a s1)
    (hcl : ClaimAt st.data.dmem (off (fb m0) 992) cl)
    (hcw : WeightsAt st.data.dmem (off (reg m0 .r9) 25600) cl)
    {R : MachineState → Prop}
    (cont : ∀ st', At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b55Offset wrB t52 (vv m0 V) st' →
      TStateAt st'.data.dmem (reg m0 .rdi) a s1 →
      ClaimAt st'.data.dmem (off (fb m0) 992) cl →
      WeightsAt st'.data.dmem (off (reg m0 .r9) 25600) cl →
      NativeRustcVm.Layout.ClaimsWAt st'.data.dmem (keccakClaims m0) (cs.push (outClaim inst slot w)) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have c := ctx_of hpre
  refine extFirstStep hp hpre hext hat fun st1 hat1 hb1 hc1 hk1 ↦ ?_
  refine extHighStep hp hpre hext hat1 hb1 fun st2 hat2 hb2 hc2 hk2 ↦ ?_
  have hc12 := hc1.trans hc2
  have hslot2 := Chg.ewsF c hc12 (by decide) rfl
    (by rw [Array.length_toList, h6]; decide) (by rw [Array.length_toList, h6]; decide) hslot
  refine extSlotStep hp hpre hext hat2 hb2 hslot2 h6 fun st3 hat3 hb3 hc3 hk3 ↦ ?_
  have hc123 := hc12.trans hc3
  have hcls3 := claims_bound hpre hat3
  have hat3' : At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b53Offset wrB t52 (vv m0 V) st3 := At.widen hat3 (by
    intro i hi
    simp only [wrA, wrB, Bool.or_eq_true] at hi ⊢
    exact Or.inl hi)
  refine pushStep hp hpre hpush hat3' hw0 hw1 hb3 hcls3 fun st4 hat4 hcls4 hc4 hk4 ↦ ?_
  have hc := hc123.trans hc4
  have hk := NativeRustcVmX64.Transcript.kept_trans hk1 (NativeRustcVmX64.Transcript.kept_trans hk2
    (NativeRustcVmX64.Transcript.kept_trans hk3 hk4))
  exact cont st4 hat4 (Chg.ts c hc (by decide) (by decide) (by decide) hk hts)
    (Chg.claimF c hc (by decide) (by decide) (by decide) (by decide) hcl)
    (Chg.wtsR c hc (by decide) (by decide) (by decide) (by decide) hcw) hcls4

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
