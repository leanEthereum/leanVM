module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.Grind
public import NativeVm.Math.Keccak.Facts
public import NativeRustcVmX64.Code.Vm.InstanceWeights.Names
public import NativeRustcVmX64.Code.Vm.PolyEval.Names
public import NativeRustcVmX64.Code.Vm.SumE.Names

/-!
# `verify_layer` on x86-64: the instance weights, `κ`, the product at `s`

From `C1` (`b48`, code index `383`): `instance_weights(frame + 1704, s)` (`b48`), their sum `κ`
(`sum_e`, `b49`), `κ` spilled at the frame's `32`, `48`, the product at `s` (`poly_eval`, `b50`):
at `b51` (`470`) with `C2`: `inst`.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVmX64.Sumcheck (Ctx At)
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)
open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- `κ`, the instance weights' sum. -/
abbrev kap (ch : EW) : EW := sumE (keccakInstanceWeights ch)

/-- **At the equality-mode sumcheck** (`b51`, code index `470`): the product at `s` in RAX, RDX,
`κ` at the frame's `32`, `48`, the instance weights at `1704`, the point's address in RBP, its
size in R15, the `TState` in R12, R14. -/
structure C2 (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW) (ch : EW)
    (s2 : TState) (d : MachineData) : Prop where
  body : Body m0 (wFront m0) 24 d
  ts : TStateAt d.dmem (tA m0) a s2
  fw : FWs m0 d.dmem (backWords m0)
  k32 : NativeRustcVm.WordAt d.dmem (off (stackBelow m0 2016) 32) (kap ch).c0
  k48 : NativeRustcVm.WordAt d.dmem (off (stackBelow m0 2016) 48) (kap ch).c1
  mu : NativeRustcVm.BufEWAt d.dmem (off (stackBelow m0 2016) 1704) 16
    (keccakInstanceWeights ch).toList
  pe : ewArg (reg d .rax) (reg d .rdx) = polyEval p ch
  rbp : reg d .rbp = cA m0 + 288#64
  r15 : reg d .r15 = BitVec.ofNat 64 c.point.size
  r14 : reg d .r14 = tA m0
  r12 : reg d .r12 = tA m0

end

public section

theorem iw_len (ch : EW) : (keccakInstanceWeights ch).toList.length = 16 := by
  rw [Array.length_toList, NativeVm.Math.Keccak.instanceWeights_size]

theorem ite16 (y : BitVec 64) :
    (if (!CmpOp.apply .ult .W64 (16#64) (BitVec.ofNat 64 17)) = true then y else 16#64) =
      16#64 := by
  rw [ult64]; rfl

theorem ite16' (y z : BitVec 64) :
    (if (!CmpOp.apply .ult .W64 (16#64) (BitVec.ofNat 64 17)) = true then y else z) = z := by
  rw [ult64]; rfl

end

public section

variable [Host] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData} {k : Nat}
  {p : Array EW}

/-- **The instance weights, `κ`, the product at `s`**, from `b48` to `b51`. -/
theorem inst (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    (hiw : Spec (Labels.label NativeRustcVmX64.Vm.InstanceWeights.entryLabel) InstanceWeightsPre InstanceWeightsPost)
    (hsum : Spec (Labels.label NativeRustcVmX64.Vm.SumE.entryLabel) SumEPre SumEPost)
    (hpe : Spec (Labels.label NativeRustcVmX64.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    {ch : EW} {s2 : TState} {d : MachineData} (h : C1 m0 a c p ch s2 d)
    {R : MachineState → Prop}
    (cont : ∀ d', C2 m0 a c p ch s2 d' → Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b51Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b48Offset)⟩ := by
  have g := geo_of hpre
  have hWo := wFront_outs hpre
  have hS := pre_stack hpre
  have cx := ctx hpre (F := 2000) (by decide)
  -- `b48`: `instance_weights(frame + 1704, s)`.
  have hwf := wf0 hS h.body (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b48Offset + b48.length)).toBitVec)
  have hm : Match (envB m0 d [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b48Offset + b48.length)).toBitVec)
      (fr 24) d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨h.body.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 16) g h.body hwf (blk hp b48_in_code (by simp [b48])) e48
    (fun _ _ ↦ rfl) hm (by decide +kernel) (hex0 (by decide +kernel)) fun st hm1 hpc1 hb1 _ ↦ ?_
  have hfr1 := frSame_blk (o := 24) (n := 2000) hwf hm1 (by decide +kernel) (by decide)
    (by decide +kernel)
  have hts1 := ts_blk0 hpre hwf hm1 (by decide +kernel) (by decide +kernel) h.ts
  have hrdi1 : reg st.data .rdi = off (stackBelow m0 2016) 1704 :=
    (hm1.regs .rdi _ rfl).trans (eval_ptr0 1704)
  have hrsi1 : reg st.data .rsi = ch.c0.toBitVec := (hm1.regs .rsi _ rfl).trans h.rax
  have hrdx1 : reg st.data .rdx = ch.c1.toBitVec := (hm1.regs .rdx _ rfl).trans h.rdx
  have hk1 : ∀ r ∈ [Reg64.r14], reg st.data r = reg d r :=
    keepR_regs hm1 (by decide +kernel) fun _ ↦ rfl
  have hA := frArea hpre hWo hb1 (Sk := instanceWeightsStack) (by decide) (o := 1704) (n := 264)
    (by decide) (by decide)
  have hat1 := hb1.at_ hpre hWo (by decide)
  have hiwP : InstanceWeightsPre st.data := by
    refine ⟨cx.stackOk hat1 (by decide), ?_, ?_⟩
    · show Areas st.data instanceWeightsStack [⟨reg st.data .rdi, 264⟩] []
      rw [hrdi1]
      refine ⟨fun r hr ↦ ?_, NativeRustcVm.disjoint_cons_iff.mpr ⟨fun r hr ↦ ?_,
        List.pairwise_singleton _ _⟩, fun _ _ _ hr ↦ by simp at hr⟩
      · simp only [List.append_nil, List.mem_singleton] at hr
        subst hr
        exact ⟨hA.1, hA.2.1⟩
      · simp only [List.mem_singleton] at hr
        subst hr
        exact Apart.symm' hA.2.2.2.2.1
    · rw [hrdi1]
      apply hb1.got hpre hWo (by decide) (by decide)
      intro p hp
      simp only [List.mem_singleton] at hp
      subst p
      refine ⟨(stackBelow m0 verifyLayerStack, verifyLayerStack + 8), by simp, ?_, ?_⟩
      all_goals
        rw [stack_eq, g.sbN, g.fa (by decide)]
        have := g.hN
        omega
  refine call_then hpc1 hiw hiwP fun st2 hpc2 hrsp2 hq2 ↦ ?_
  obtain ⟨hbuf, hwr, hsv⟩ := hq2
  rw [hrdi1, hrsi1, hrdx1, ewArg_ew] at hbuf
  have hso := writes1 hwr
  rw [hrdi1] at hso
  have hb2 : Body m0 (wFront m0) 24 st2.data :=
    Body.callX hpre hWo hb1 hsv hrsp2 (by decide) hso fun q hq ↦
      .inr (fr_sub g (by decide) (by decide) (by decide) hq)
  have hfr2 : FrSame m0 st.data.dmem st2.data.dmem 24 1680 :=
    frSame_call g hb1 (by decide) hso (by decide) (by decide) fun q hq ↦
      fr_miss g (o := 1704) (n := 264) (by decide) (by decide) (by decide) hq
  have hts2 := ts_callX hpre hWo hb1 hsv.2 (by decide) hso
    (fun q hq ↦ frame_not_t hpre (fr_in g (by decide) hq)) hts1
  have hcs2 := hsv.1
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2 hb2 hfr2 hts2 hcs2 hbuf
  subst hpc2
  have hfw2 : FWs m0 d2.dmem (backWords m0) :=
    (hfr1.bw h.fw).keepIn hfr2 fun q hq ↦ by have := backWords_in q hq; omega
  -- `b49`: `κ`.
  rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b48Offset + b48.length = k + NativeRustcVmX64.Vm.VerifyLayer.b49Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b48_next]]
  have hwf3 := wf0 hS hb2 (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b49Offset + b49.length)).toBitVec)
  have hm3 : Match (envB m0 d2 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b49Offset + b49.length)).toBitVec)
      (fr 24) d2 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hb2.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 16) g hb2 hwf3 (blk hp b49_in_code (by simp [b49])) e49
    (fun _ _ ↦ rfl) hm3 (by decide +kernel) (hex0 (by decide +kernel)) fun st3 hm4 hpc4 hb4 _ ↦ ?_
  have hl : (envB m0 d2 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b49Offset + b49.length)).toBitVec).load 0 1704 8 =
      16#64 := by
    have := hbuf.2.1
    rw [iw_len] at this
    exact fload8 this
  have hfr4 := frSame_blk (o := 24) (n := 2000) hwf3 hm4 (by decide +kernel) (by decide)
    (by decide +kernel)
  have hts4 := ts_blk0 hpre hwf3 hm4 (by decide +kernel) (by decide +kernel) hts2
  have hrsi4 : reg st3.data .rsi = 16#64 := by
    rw [show reg st3.data .rsi = _ from hm4.regs .rsi _ rfl, bk_ite, bk_not]
    simp only [SBool.eval, Sym.eval, hl]
    exact ite16 _
  have hrdi4 : reg st3.data .rdi = off (stackBelow m0 2016) 1712 := by
    rw [show reg st3.data .rdi = _ from hm4.regs .rdi _ rfl, bk_ite, bk_not]
    rw [show (SBool.cmp .ult .W64 (.load 0 1704 8) (.lit 17)).eval
      (envB m0 d2 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b49Offset + b49.length)).toBitVec) = true by
        simp only [SBool.eval, Sym.eval, hl]; decide]
    exact eval_ptr0 1712
  have hk4 : ∀ r ∈ [Reg64.r12, .r13, .r14], reg st3.data r = reg d2 r :=
    keepR_regs hm4 (by decide +kernel) fun _ ↦ rfl
  have hA4 := frArea hpre hWo hb4 (Sk := sumEStack) (by decide) (o := 1712) (n := 256)
    (by decide) (by decide)
  have hat4 := hb4.at_ hpre hWo (by decide)
  have hews : NativeRustcVm.EWsAt st3.data.dmem (off (stackBelow m0 2016) 1712)
      (keccakInstanceWeights ch).toList := by
    have hb3 := hbuf.2.2
    rw [show off (stackBelow m0 2016) 1704 + 8#64 = off (stackBelow m0 2016) 1712 by
      unfold off; bv_omega] at hb3
    exact (hfr4.sub (o' := 1712) (n' := 256) (by decide) (by decide)).ews hb3
      (by rw [iw_len])
  refine leafX hpre hWo (Sk := sumEStack) (by decide) hsum
    (fun _ _ hq ↦ ⟨changes_stk hq.2.1, hq.2.2⟩) hpc4 hb4
    ⟨cx.stackOk hat4 (by decide), by rw [hrsi4]; decide,
      by rw [hrdi4, hrsi4]; exact ⟨hA4.1, hA4.2.1⟩⟩
    fun d5 hq5 hb5 hfr5 hts5 hcs5 _ ↦ ?_
  have hk5 : ewArg (reg d5 .rax) (reg d5 .rdx) = kap ch := by
    have := hq5.1
    rw [hrdi4, slice_of hews (by rw [hrsi4, NativeVm.Math.Keccak.instanceWeights_size]; rfl)] at this
    exact this
  -- `b50`: `κ` spilled, the point's slots cleared, `poly_eval(product, 47, s)`.
  rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b49Offset + b49.length = k + NativeRustcVmX64.Vm.VerifyLayer.b50Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b49_next]]
  have hfrA : FrSame m0 d.dmem d5.dmem 24 1680 :=
    ((hfr1.sub (by decide) (by decide)).trans hfr2).trans
      ((hfr4.trans hfr5).sub (by decide) (by decide))
  have hfw5 : FWs m0 d5.dmem (backWords m0) :=
    h.fw.keepIn hfrA fun q hq ↦ by have := backWords_in q hq; omega
  have hprod5 : NativeRustcVm.EWsAt d5.dmem (off (stackBelow m0 2016) 472) p.toList :=
    (hfrA.sub (o' := 472) (n' := 752) (by decide) (by decide)).ews h.prod
      (by rw [Array.length_toList, h.psize])
  have hmu5 : NativeRustcVm.BufEWAt d5.dmem (off (stackBelow m0 2016) 1704) 16
      (keccakInstanceWeights ch).toList :=
    ((hfr4.trans hfr5).sub (o' := 1704) (n' := 8 + 16 * 16) (by decide) (by decide)).buf hbuf
  have hr12 : reg d5 .r12 = ch.c0.toBitVec := by
    exact (hcs5 .r12 rfl).trans ((hk4 .r12 (by simp)).trans ((hcs2 .r12 rfl).trans
      ((hm1.regs .r12 _ rfl).trans h.rax)))
  have hr13 : reg d5 .r13 = ch.c1.toBitVec := by
    exact (hcs5 .r13 rfl).trans ((hk4 .r13 (by simp)).trans ((hcs2 .r13 rfl).trans
      ((hm1.regs .r13 _ rfl).trans h.rdx)))
  have hr14 : reg d5 .r14 = tA m0 := by
    exact (hcs5 .r14 rfl).trans ((hk4 .r14 (by simp)).trans ((hcs2 .r14 rfl).trans
      ((hk1 .r14 (by simp)).trans h.r14)))
  have hts5' := hts5 _ hts4
  obtain ⟨-, -, hplen, hpw, -⟩ := hb5.claim hpre (fun _ h ↦ h)
  have hsz : c.point.size ≤ 30 := by
    simpa [NativeRustcVm.KeccakGkr.claimPointCap] using hplen
  have hlt : (BitVec.ofNat 64 c.point.size).toNat < (BitVec.ofNat 64 31).toNat := by
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hwf6 := wfC hpre hb5 (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b50Offset + b50.length)).toBitVec)
  have hm6 : Match (envB m0 d5 [(cA m0, 768)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b50Offset + b50.length)).toBitVec)
      (fr 24 [768] [] [] [(.load 0 128 8, 1, 280)]) d5 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb5.rsp, trivial⟩ trivial trivial
      ⟨by show Env.load _ 0 128 8 = cA m0 + BitVec.ofInt 64 280
          rw [fload8 (bw128 hfw5)]; rfl, trivial⟩
  have hl280 : (envB m0 d5 [(cA m0, 768)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b50Offset + b50.length)).toBitVec).load 1 280 8 =
      BitVec.ofNat 64 c.point.size := by
    rw [cload (o := 280) hpw]; simp only [Array.length_toList, Nat.toUInt64]; rfl
  have hl64 : (envB m0 d5 [(cA m0, 768)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b50Offset + b50.length)).toBitVec).load 0 64 8 = cA m0 + 288#64 :=
    fload8 (bw64 hfw5)
  refine Body.blk (o' := 16) g hb5 hwf6 (blk hp b50_in_code (by simp [b50])) e50
    (fun _ _ ↦ rfl) hm6 (by decide +kernel) (hex0 (by decide +kernel)) fun st6 hm7 hpc7 hb6 _ ↦ ?_
  have h40 := frSame_blk (o := 40) (n := 8) hwf6 hm7 (by decide +kernel) (by decide)
    (by decide +kernel)
  have h56 := frSame_blk (o := 56) (n := 1168) hwf6 hm7 (by decide +kernel) (by decide)
    (by decide +kernel)
  have h1704 := frSame_blk (o := 1704) (n := 8 + 16 * 16) hwf6 hm7 (by decide +kernel)
    (by decide) (by decide +kernel)
  have hts6 := ts_blk0 hpre hwf6 hm7 (by decide +kernel) (by decide +kernel) hts5'
  have hk32 : NativeRustcVm.WordAt st6.data.dmem (off (stackBelow m0 2016) 32) (kap ch).c0 :=
    fwW hm7 rfl rfl (by decide) (by decide +kernel) (by exact ewArg_c0 hk5)
  have hk48 : NativeRustcVm.WordAt st6.data.dmem (off (stackBelow m0 2016) 48) (kap ch).c1 :=
    fwW hm7 rfl rfl (by decide) (by decide +kernel) (by exact ewArg_c1 hk5)
  have hrdi6 : reg st6.data .rdi = off (stackBelow m0 2016) 472 :=
    (hm7.regs .rdi _ rfl).trans (eval_ptr0 472)
  have hrsi6 : reg st6.data .rsi = 47#64 := hm7.regs .rsi _ rfl
  have hrdx6 : reg st6.data .rdx = ch.c0.toBitVec := (hm7.regs .rdx _ rfl).trans hr12
  have hrcx6 : reg st6.data .rcx = ch.c1.toBitVec := (hm7.regs .rcx _ rfl).trans hr13
  have hr12' : reg st6.data .r12 = tA m0 := (hm7.regs .r12 _ rfl).trans hr14
  have hr14' : reg st6.data .r14 = tA m0 := (hm7.regs .r14 _ rfl).trans hr14
  have hrbp : reg st6.data .rbp = cA m0 + 288#64 := by
    rw [show reg st6.data .rbp = _ from hm7.regs .rbp _ rfl]
    simp only [Sym.eval, SBool.eval, hl280, hl64, ult64]
    simp only [BitVec.toNat_ofNat] at hlt ⊢
    simp [hlt]
  have hr15 : reg st6.data .r15 = BitVec.ofNat 64 c.point.size := by
    rw [show reg st6.data .r15 = _ from hm7.regs .r15 _ rfl]
    simp only [Sym.eval, SBool.eval, hl280, ult64]
    simp only [BitVec.toNat_ofNat] at hlt ⊢
    simp [hlt]
  have hprod6 : NativeRustcVm.EWsAt st6.data.dmem (off (stackBelow m0 2016) 472) p.toList :=
    (h56.sub (o' := 472) (n' := 752) (by decide) (by decide)).ews hprod5
      (by rw [Array.length_toList, h.psize])
  have hA6 := frArea hpre hWo hb6 (Sk := polyEvalStack) (by decide) (o := 472) (n := 752)
    (by decide) (by decide)
  have hat6 := hb6.at_ hpre hWo (by decide)
  rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b50Offset + b50.length = k + NativeRustcVmX64.Vm.VerifyLayer.b51Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b50_next]] at hpc7
  refine leafX hpre hWo (Sk := polyEvalStack) (by decide) hpe
    (fun _ _ hq ↦ ⟨changes_stk hq.2.1, hq.2.2⟩) hpc7 hb6
    ⟨cx.stackOk hat6 (by decide), by rw [hrsi6]; decide,
      by rw [hrdi6, hrsi6]; exact ⟨⟨hA6.1, hA6.2.1⟩, hA6.2.2.2.2.1⟩⟩
    fun d8 hq8 hb8 hfr8 hts8 hcs8 _ ↦ ?_
  have hpe8 : ewArg (reg d8 .rax) (reg d8 .rdx) = polyEval p ch := by
    have := hq8.1
    rw [hrdi6, hrsi6, hrdx6, hrcx6, ewArg_ew,
      slice_of hprod6 (by rw [h.psize]; rfl)] at this
    exact this
  refine cont d8 ⟨hb8, hts8 _ hts6, hfr8.bw (FWs.bw_of h40 (h56.sub (by decide) (by decide)) hfw5),
    (hfr8.sub (o' := 32) (n' := 8) (by decide) (by decide)).word hk32 (by decide),
    (hfr8.sub (o' := 48) (n' := 8) (by decide) (by decide)).word hk48 (by decide),
    (hfr8.sub (o' := 1704) (n' := 8 + 16 * 16) (by decide) (by decide)).buf (h1704.buf hmu5),
    hpe8, (hcs8 .rbp rfl).trans hrbp, (hcs8 .r15 rfl).trans hr15, (hcs8 .r14 rfl).trans hr14',
    (hcs8 .r12 rfl).trans hr12'⟩

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
