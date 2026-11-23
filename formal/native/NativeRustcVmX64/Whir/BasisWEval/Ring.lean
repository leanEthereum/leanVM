module

public import NativeRustcVmX64.Whir.BasisWEval.Vals
public import NativeRustcVmX64.Code.Vm.RingClaimWeight.Names

/-!
# `BasisW::eval`: the ring-switched claim (x86-64)

From `NativeRustcVmX64.Vm.BasisWEval.label_3` (`A4`): `b4` pushes the point as `ring_claim_weight`'s two stack arguments
and calls it on the placement of `QKECCAK` (RAX, RDX), the Keccak output's point (at most 36
coordinates) and the ring switch's coefficients, its `Option<EW>` at the frame's `80`: `Some` of
the ring-switched claim's weight, the rest as `A4` (`A5`, `ring_call`).
-/

namespace NativeRustcVmX64.Whir.BasisWEval

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model LeanVM.Parameters
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVm.Layout NativeRustcVm.Ring
open NativeRustcVmX64.Vm.BasisWEval
open NativeRustcVm.KeccakGkr (KeccakOutAt outBytes outPointCap)
open NativeRustcVm.Transcript (off off_add off_zero toNat_off OptEWAt)
open LeanVM.Protocol.Verifier (qkeccak Placement)

@[expose] public section

/-- **After `ring_claim_weight`** (`b5`, RSP at the frame's `8`): `A4`'s registers and words, the
weight at the frame's `80`. -/
structure A5 (m0 : MachineData) (ba : BasisAddrs) (b : BasisW) (v : Vals) (d : MachineData) :
    Prop where
  base : Base m0 ba 8 d
  rbx : reg d .rbx = reg m0 .rsi
  rbp : reg d .rbp = ba.scales
  r15 : reg d .r15 = ba.count.toUInt64.toBitVec
  r13 : reg d .r13 = sA ba (min 1 ba.count)
  r14 : reg d .r14 = (sAt b.scales 0).c0.toBitVec
  w24 : FW m0 d 24 (sAt b.scales 0).c1.toBitVec
  out : OptEWAt d.dmem (off (fb m0) 80) (some (ringW v (xpt m0)))

end

public section

variable {m0 : MachineData} {ba : BasisAddrs} {b : BasisW} {v : Vals}

theorem In.kpLen (h : In m0 ba b v) : v.kp.toList.length ≤ 36 := h.keccak.1.1

theorem In.keccakAt (h : In m0 ba b v) {o : Nat} {d : MachineData} (hf : Fb m0 o d) :
    KeccakOutAt d.dmem ba.keccak v.kp v.slices :=
  ⟨NativeRustcVm.Layout.BufEWAt.of_same h.keccak.1 (h.same_of hf h.keccakIn) (by decide),
    h.keccak.2.1, NativeRustcVm.Tables.EWsAt.of_same h.keccak.2.2
      ((h.same_of hf h.keccakIn).sub (o := 584) (k := 1024) (by decide))
      (by rw [Array.length_toList, h.keccak.2.1])⟩

theorem In.coeffsLen (h : In m0 ba b v) : v.coeffs.toList.length = 64 := by
  simpa [coeffCount] using h.ring.2.1

variable [Host] {k : Nat}

/-- **The ring-switched claim's weight**, from `NativeRustcVmX64.Vm.BasisWEval.label_3` to `b5`. -/
theorem ring_call (hp : Placed code k) (h : In m0 ba b v)
    (hrcw : Spec (Labels.label NativeRustcVmX64.Vm.RingClaimWeight.entryLabel) RingClaimWeightPre RingClaimWeightPost)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b4Offset)) (ha : A4 m0 ba b v st.data)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b5Offset) → A5 m0 ba b v st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hS := h.stackOk
  have hN := h.hN
  have hf := ha.base.fr
  let ret := (Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b4Offset + b4.length)).toBitVec
  have hkin := h.keccakIn
  have hk8 : WhirIn m0 ba.keccak 8 basisWEvalStack := WhirIn.mono' hkin (by decide)
  have hbk : NativeRustcVm.Apart (reg m0 .rsi) 56 ba.keccak 8 :=
    NativeRustcVm.Apart.mono h.aparts.1 (Nat.le_refl _) (by unfold basisBytes; omega)
      (Nat.le_refl _) (by unfold outBytes; omega)
  have hwf : (envB m0 st.data [(reg m0 .rsi, 56), (ba.keccak, 8)] ret).WF :=
    h.wf2 hf.frame.kept h.basis hk8 hbk
  have hK := h.keccakAt hf
  have hlen := h.kpLen
  have l32 : (envB m0 st.data [(reg m0 .rsi, 56), (ba.keccak, 8)] ret).load 1 32 8 = ba.keccak :=
    load_ofMachine (r := 1) rfl (h.word hf 4 (by decide))
  have l24 : (envB m0 st.data [(reg m0 .rsi, 56), (ba.keccak, 8)] ret).load 1 24 8 = ba.ring :=
    load_ofMachine (r := 1) rfl (h.word hf 3 (by decide))
  have l20 : (envB m0 st.data [(reg m0 .rsi, 56), (ba.keccak, 8)] ret).load 2 0 8 =
      v.kp.toList.length.toUInt64.toBitVec :=
    load_ofMachine (r := 2) (o := 0) rfl (by rw [off_zero]; exact hK.1.2.1)
  have hm : Match (envB m0 st.data [(reg m0 .rsi, 56), (ba.keccak, 8)] ret) ringS st.data := by
    refine match_ofMachine ⟨rfl, rfl, rfl, trivial⟩
      ⟨hf.frame.rsp_eval, known_ptr rfl ha.rbx, trivial⟩ trivial trivial ⟨?_, trivial⟩
    exact l32.trans (eval_ptr (i := 2) rfl).symm
  obtain ⟨hmid, h0, hmiss, w8, w16, hrcx, hr8, hrsi, hrdi, hr9, -, hrbx, hk⟩ := ok_b4
  refine at_pc hpc (h.block hf hwf (inf hp b4_in_code (by simp [b4])) exit_b4 (fun _ _ ↦ rfl) hm
    hmid h0 fun st1 hm1 hpc1 hf1 ↦ ?_)
  have hlt : (v.kp.toList.length.toUInt64.toBitVec).toNat < 37 := by
    rw [toNat_bv_toUInt64 (by omega)]; omega
  have e8 : reg st1.data .r8 = v.kp.toList.length.toUInt64.toBitVec :=
    (reg_eval hm1 hr8).trans (r84_eval l20 hlt)
  have ercx : reg st1.data .rcx = off ba.keccak 8 :=
    (reg_eval hm1 hrcx).trans (rcx4_eval l20 l32 hlt)
  have er9 : reg st1.data .r9 = off ba.ring 16 := by
    rw [reg_eval hm1 hr9]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, l24, off]
    exact BitVec.add_comm _ _
  have ersi : reg st1.data .rsi = (v.L.placement qkeccak).variableCount.toUInt64.toBitVec :=
    (reg_eval hm1 hrsi).trans ha.rax
  have erdx : reg st1.data .rdx = (v.L.placement qkeccak).index.toUInt64.toBitVec :=
    (keeps_reg hm1 hk (by simp)).trans ha.rdx
  have erdi : reg st1.data .rdi = off (fb m0) 80 := (reg_eval hm1 hrdi).trans (eval_ptr0 80)
  have hb1 : Base m0 ba 0 st1.data := ha.base.block hf1 hwf hm1 hmid (by
    simp only [missWs, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hmiss ⊢
    exact ⟨hmiss.2.1, hmiss.2.2.1, hmiss.2.2.2.1, hmiss.2.2.2.2⟩)
  have ha0 : stackArg st1.data 0 = reg m0 .rdx :=
    stackArg_of hf1 (FW.wrote hm1 (by omega) w8 ha.base.w40.load)
  have ha1 : stackArg st1.data 1 = reg m0 .rcx :=
    stackArg_of hf1 (FW.wrote hm1 (by omega) w16 ha.base.w48.load)
  have hle : 160 - 0 + ringClaimWeightStack ≤ basisWEvalStack := stack_le.2.1
  have hpre : RingClaimWeightPre st1.data := by
    refine ⟨h.stackOk_at hf1 (by omega) hle, h.argsOk hf1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e8]; exact Nat.le_of_lt_succ hlt
    · rw [ha1]; exact h.pre.2.2.2.1
    · unfold SliceOk
      rw [ercx, e8, toNat_bv_toUInt64 (by omega)]
      exact h.argIn hf1 (by omega) hle (WhirIn.sub hkin (by unfold outBytes; omega))
    · rw [er9]
      exact h.argIn hf1 (by omega) hle (WhirIn.sub h.ringIn (by unfold ringWBytes; omega))
    · rw [ha0, ha1]; exact h.argIn hf1 (by omega) hle h.point
    · rw [erdi]; exact h.optOut hf1 hle
  obtain ⟨hpcc, hretc⟩ := hpc1
  refine Fr.call (c := 0) (Nc := ringClaimWeightStack) (lo := 80) (len := 24)
    (X := NativeRustcVm.InRange (off (fb m0) 80) 24) hS N_ge (by omega) hle slots_c0 (by omega)
    (fun _ h ↦ h.elim) (fun _ h ↦ .inr h) hrcw hf1 ⟨hpcc, hretc⟩ hpre
    (fun m' hq ↦ ⟨?_, hq.2.2⟩) fun m2 hf2 hq2 hk2 hcs2 ↦ ?_
  · refine NativeRustcVm.SameOutside.mono hq.2.1 fun q hq ↦ ?_
    rcases hq with hq | hq
    · rw [erdi] at hq; exact .inr hq
    · exact .inl hq
  -- the weight
  have epl : placementArg st1.data = v.L.placement qkeccak :=
    placementArg_eq (placement_lt h.layout qkeccak) ersi erdx
  have ekp : slice st1.data (reg st1.data .rcx) (reg st1.data .r8) = v.kp := by
    unfold slice
    rw [ercx, e8, toNat_bv_toUInt64 (by omega),
      h.ewsOf_eq hf1 (WhirIn.sub hkin (o := 8) (by unfold outBytes; omega)) le_rfl]
    have := NativeRustcVm.ewsOf_of_ewsAt h.keccak.1.2.2
    rw [this, Array.toArray_toList]
  have ecf : arr st1.data (reg st1.data .r9) coeffCount = v.coeffs := by
    unfold arr
    have hcl := h.coeffsLen
    rw [er9, show coeffCount = v.coeffs.toList.length by rw [hcl]; rfl,
      h.ewsOf_eq hf1 (WhirIn.sub h.ringIn (o := 16) (by
        rw [hcl]; unfold ringWBytes coeffCount; omega)) le_rfl]
    have := NativeRustcVm.ewsOf_of_ewsAt h.ring.2.2
    rw [this, Array.toArray_toList]
  have ex : slice st1.data (stackArg st1.data 0) (stackArg st1.data 1) = xpt m0 :=
    h.xpt_eq hf1 ha0 ha1
  have hout := hq2.1
  rw [epl, ekp, ecf, ex, erdi] at hout
  rw [show k + NativeRustcVmX64.Vm.BasisWEval.b4Offset + b4.length = k + NativeRustcVmX64.Vm.BasisWEval.b5Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.BasisWEval.b4_next]]
  refine cont _ rfl {
    base := hb1.call hf2 hk2 (by omega) (.inl (by omega))
    rbx := (hcs2 .rbx rfl).trans ((reg_eval hm1 hrbx).trans (eval_ptr rfl))
    rbp := (hcs2 .rbp rfl).trans ((keeps_reg hm1 hk (by simp)).trans ha.rbp)
    r15 := (hcs2 .r15 rfl).trans ((keeps_reg hm1 hk (by simp)).trans ha.r15)
    r13 := (hcs2 .r13 rfl).trans ((keeps_reg hm1 hk (by simp)).trans ha.r13)
    r14 := (hcs2 .r14 rfl).trans ((keeps_reg hm1 hk (by simp)).trans ha.r14)
    w24 := (ha.w24.block hwf hm1 hmid (by omega) (by
        simp only [missWs, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hmiss
        exact hmiss.1)).call hk2 (by omega) (by omega) (.inl (by omega))
    out := hout }

end

end NativeRustcVmX64.Whir.BasisWEval
