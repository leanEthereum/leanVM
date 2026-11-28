module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.Layer
public import NativeRustcVm.Sumcheck.RoundPoly
public import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names

/-!
# `verify_layer` on x86-64: the plain sumcheck and the three values

From `C3` (`b53`, code index `485`): the local point's slots cleared, `11` pushed,
`sumcheck<sumcheck_plain>` from the claim `v` into the frame at `136` and the local point at `296`
(`b53`), its `None` to the exit (`b54`), `read_scalars(t, frame + 136, 3)` (`b55`), its `None` to
the exit (`b56`): at `b57` (`533`) with `C4`: `plain`.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVmX64.Sumcheck (Ctx At testAl_eq)
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)
open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- **After the three values** (`b57`, code index `533`): the local point `lp` at the frame's
`296`, the values `t` at `136`, the plain sumcheck's claim `val` in R14, RBX, the `TState` `s5`. -/
structure C4 (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (ch : EW) (pt lp t : Array EW)
    (val : EW) (s5 : TState) (d : MachineData) : Prop where
  body : Body m0 (wFront m0) 24 d
  ts : TStateAt d.dmem (tA m0) a s5
  fw : FWs m0 d.dmem (wl3 m0 c ch)
  mu : NativeRustcVm.BufEWAt d.dmem (off (stackBelow m0 2016) 1704) 16
    (keccakInstanceWeights ch).toList
  hpt : NativeRustcVm.EWsAt d.dmem (off (stackBelow m0 2016) 1224) pt.toList
  psz : pt.size = c.point.size
  hlp : NativeRustcVm.EWsAt d.dmem (off (stackBelow m0 2016) 296) lp.toList
  lsz : lp.size = 11
  ht : NativeRustcVm.EWsAt d.dmem (off (stackBelow m0 2016) 136) t.toList
  tsz : t.size = 3
  r14 : reg d .r14 = val.c0.toBitVec
  rbx : reg d .rbx = val.c1.toBitVec
  r12 : reg d .r12 = tA m0
  r15 : reg d .r15 = sA m0

end

public section

/-- The frame's words of `wl3` kept with `FrSame` at each of their offsets. -/
theorem FWs.keep3 {m0 : MachineData} {c : KeccakClaimW} {ch : EW} {d d' : DataMem}
    (hk : ∀ o ∈ [32, 40, 48, 64, 80, 96, 120, 128, 224], FrSame m0 d d' o 8)
    (h : FWs m0 d (wl3 m0 c ch)) : FWs m0 d' (wl3 m0 c ch) :=
  h.keep fun p hp ↦ hk p.1 (by
    have : (wl3 m0 c ch).map Prod.fst = [32, 40, 48, 64, 80, 96, 120, 128, 224] := rfl
    exact this ▸ List.mem_map_of_mem hp)

theorem rest5_eq {c : KeccakClaimW} {ch : EW} {pt lp t : Array EW} {val : EW} {s4 s5 : TState}
    (h : (readScalars 3).run s4 = some (t, s5)) :
    rest5 c ch pt lp val s4 =
      if checkB c (kap ch) lp t val then rest6 ch pt lp t s5 else none := by
  rw [rest5, h]; rfl

end

public section

variable [Host] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData} {k : Nat}

/-- **The plain sumcheck and the three values**, from `b53` to `b57`. -/
theorem plain (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    (hspl : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s)
      (SumcheckPlainPost a s))
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    {ch : EW} {pt : Array EW} {v : EW} {s3 : TState} {d : MachineData}
    (h : C3 m0 a c ch pt v s3 d) (hrun : runL s c m0 = rest4 c ch pt v s3)
    (cont : ∀ lp t val s5 d', C4 m0 a c ch pt lp t val s5 d' →
      runL s c m0 = (if checkB c (kap ch) lp t val then rest6 ch pt lp t s5 else none) →
      Eventually (step1 Host.exe) (Goal a s c m0) ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b57Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s c m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b53Offset)⟩ := by
  have g := geo_of hpre
  have hWo := wFront_outs hpre
  have hS := pre_stack hpre
  have cx := ctx hpre (F := 2016) (by decide)
  have hN := g.hN; have htop := g.top; have hfb := g.fbN
  have hv := NativeRustcVm.ewAt_iff.mp h.hv
  rw [show off (stackBelow m0 2016) 304 + BitVec.ofNat 64 8 = off (stackBelow m0 2016) 312 from
    NativeRustcVm.Transcript.off_add _ _ _] at hv
  -- `b53`: the local point's slots cleared, `11` pushed.
  have hwf := wf0 hS h.body (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b53Offset + b53.length)).toBitVec)
  have hm : Match (envB m0 d [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b53Offset + b53.length)).toBitVec)
      (fr 24) d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨h.body.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 0) g h.body hwf (blk hp b53_in_code (by simp [b53])) e53
    (fun _ _ ↦ rfl) hm (by decide +kernel) (hex0 (by decide +kernel)) fun st hm1 hpc1 hb1 _ ↦ ?_
  have hts1 := ts_blk0 hpre hwf hm1 (by decide +kernel) (by decide +kernel) h.ts
  have hfw1 : FWs m0 st.data.dmem (wl3 m0 c ch) :=
    FWs.blkO (os := [32, 40, 48, 64, 80, 96, 120, 128, 224]) rfl hwf hm1 (by decide +kernel)
      (by decide +kernel) h.fw
  have hfrB := frSame_blk (o := 1224) (n := 744) hwf hm1 (by decide +kernel) (by decide)
    (by decide +kernel)
  have hw8 : NativeRustcVm.WordAt st.data.dmem (off (stackBelow m0 2016) 8)
      (.ofBitVec (BitVec.ofNat 64 11)) :=
    fwW hm1 rfl rfl (by decide) (by decide +kernel) (by exact rfl)
  have hsp1 : rspOf st.data = stackBelow m0 2016 := by
    rw [hb1.fr.sp]; exact NativeRustcVm.Transcript.off_zero _
  have hrdi : reg st.data .rdi = off (stackBelow m0 2016) 136 :=
    (hm1.regs .rdi _ rfl).trans (eval_ptr0 136)
  have hr9 : reg st.data .r9 = off (stackBelow m0 2016) 296 :=
    (hm1.regs .r9 _ rfl).trans (eval_ptr0 296)
  have hrsi : reg st.data .rsi = tA m0 := (hm1.regs .rsi _ rfl).trans h.r12
  have hr8 : reg st.data .r8 = BitVec.ofNat 64 4 := hm1.regs .r8 _ rfl
  have hr12 : reg st.data .r12 = tA m0 := (hm1.regs .r12 _ rfl).trans h.r12
  have hr15 : reg st.data .r15 = sA m0 := (hm1.regs .r15 _ rfl).trans h.r15
  have hcl : claimArg st.data = v := by
    show ewArg (reg st.data .rdx) (reg st.data .rcx) = _
    rw [show reg st.data .rdx = _ from hm1.regs .rdx _ rfl,
      show reg st.data .rcx = _ from hm1.regs .rcx _ rfl]
    simp only [Sym.eval]
    rw [fload8 hv.1, fload8 hv.2, ewArg_ew]
  have ha0 : stackArg st.data 0 = BitVec.ofNat 64 11 := by
    unfold stackArg
    rw [hsp1, show stackBelow m0 2016 + BitVec.ofNat 64 (8 + 8 * 0) = off (stackBelow m0 2016) 8
      from rfl, NativeRustcVm.wordOf_of_wordAt hw8]
  have hat : At m0 2016 st.data := hb1.at_ hpre hWo (by decide)
  have hle : 2016 + sumcheckPlainStack ≤ 3232 := by decide
  have f136 : (off (stackBelow m0 2016) 136).toNat = (rspOf m0).toNat - 2016 + 136 :=
    g.fa (by decide)
  have f296 : (off (stackBelow m0 2016) 296).toNat = (rspOf m0).toNat - 2016 + 296 :=
    g.fa (by decide)
  have hpre1 : SumcheckPlainPre a s3 st.data := by
    unfold SumcheckPlainPre SumcheckOk
    rw [hrsi, hrdi, hr9, hr8, ha0]
    refine ⟨⟨?_, ?_⟩, cx.stackOk hat hle, cx.rcAt hat hle, hts1, cx.tstateOk hat hle,
      by decide, by decide, cx.outOk_frame hat hle (by decide) (by decide),
      cx.outOk_frame hat hle (by decide) (by decide), ?_, ?_⟩
    · show NativeRustcVm.Mapped _ (rspOf st.data + 8#64) _
      rw [hsp1]
      exact mapped_off (o := 8) (NativeRustcVm.Transcript.Mapped.keeps (frame_mapped (F := 2016) hS
        (by decide)) hb1.fr.kept) (by decide)
    · rw [hsp1, hfb]; omega
    · unfold NativeRustcX64.Apart; rw [f136, f296]; omega
    · apply hb1.got hpre hWo (by decide) (by decide)
      simp only [NativeRustcVm.Transcript.DecArea.region, show (11#64).toNat = 11 from rfl]
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, le_rfl⟩
      · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
      · refine ⟨(stackBelow m0 verifyLayerStack, verifyLayerStack + 8), by simp, ?_, ?_⟩
        all_goals simp only [stack_eq, g.sbN, f136]; omega
      · refine ⟨(stackBelow m0 verifyLayerStack, verifyLayerStack + 8), by simp, ?_, ?_⟩
        all_goals simp only [stack_eq, g.sbN, f296]; omega
      · exact ⟨(rcAddr, 192), by simp, le_rfl, le_rfl⟩
  refine call_then hpc1 (hspl s3) hpre1 fun st2 hpc2 hrsp2 hq2 ↦ ?_
  obtain ⟨hout, hso, hsv⟩ := hq2
  have h11 : (BitVec.ofNat 64 11).toNat = 11 := rfl
  rw [hrsi, hrdi, hr9, hr8, ha0, hcl, h11] at hout
  rw [hrsi, hrdi, hr9, ha0, h11] at hso
  have hso' : SameOutside st.data.dmem st2.data.dmem (fun q ↦
      InRange (stackBelow st.data sumcheckPlainStack) sumcheckPlainStack q ∨
        (InRange (off (stackBelow m0 2016) 136) 24 q ∨
          InRange (off (stackBelow m0 2016) 296) (16 * 11) q ∨
          InRange (tA m0) tstateBytes q)) :=
    NativeRustcVm.SameOutside.mono hso fun q hq ↦ by
      rcases hq with hq | hq | hq | hq
      · exact .inr (.inl hq)
      · exact .inr (.inr (.inl hq))
      · exact .inr (.inr (.inr hq))
      · exact .inl hq
  have hb2 : Body m0 (wFront m0) 8 st2.data :=
    Body.call g hWo hb1 (oc := 0) (by decide) hsv hrsp2 (by decide) hso' fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact .inr (fr_sub g (lo := 8) (len := 1960) (by decide) (by decide) (by decide) hq)
      · exact .inr (fr_sub g (lo := 8) (len := 1960) (by decide) (by decide) (by decide) hq)
      · exact .inl (.inl hq)
  have hmiss : ∀ {o n : Nat}, 24 ≤ o → o + n ≤ 2024 → o + n ≤ 136 ∨ (160 ≤ o ∧ o + n ≤ 296) ∨
      472 ≤ o → FrSame m0 st.data.dmem st2.data.dmem o n := fun h1 h2 h3 ↦
    frSame_call g hb1 (oc := 0) (by decide) hso' (by omega) h2 fun q hq hq' ↦ by
      rcases hq with hq | hq | hq
      · exact fr_miss g (by omega) (by decide) (by omega) hq hq'
      · exact fr_miss g (by omega) (by decide) (by omega) hq hq'
      · exact (frame_not_t hpre (fr_in g (by omega) hq')).1 hq
  have hfw2 : FWs m0 st2.data.dmem (wl3 m0 c ch) := FWs.keep3 (fun o ho ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hmiss (by decide) (by decide) (by decide)) hfw1
  have hfrB2 := hmiss (o := 1224) (n := 744) (by decide) (by decide) (by decide)
  have hmu2 := ((hfrB.trans hfrB2).sub (o' := 1704) (n' := 8 + 16 * 16) (by decide)
    (by decide)).buf h.mu
  have hpt2 := ((hfrB.trans hfrB2).sub (o' := 1224) (n' := 480) (by decide) (by decide)).ews h.hpt
    (by rw [Array.length_toList, h.psz]; have := (claimPt hpre (fun _ h ↦ h) h.body).1; omega)
  have hr12' : reg st2.data .r12 = tA m0 := (hsv.1 .r12 rfl).trans hr12
  have hr15' : reg st2.data .r15 = sA m0 := (hsv.1 .r15 rfl).trans hr15
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2 hb2 hout hfw2 hmu2 hpt2 hr12' hr15'
  subst hpc2
  -- `b54`: `None` exits.
  rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b53Offset + b53.length = k + NativeRustcVmX64.Vm.VerifyLayer.b54Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b53_next]]
  have hwf3 := wf0 hS hb2 (vars := fun _ ↦ 0) (ret := 0)
  have hm3 : Match (envB m0 d2 [] (fun _ ↦ 0) 0) (fr 8) d2 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hb2.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 24) g hb2 hwf3 (blk hp b54_in_code (by simp [b54])) e54 nofun hm3
    (by decide +kernel) (hex0 (by decide +kernel)) fun st4 hm4 hpc4 hb4 _ ↦ ?_
  simp only [PcOk] at hpc4
  have hd4 : st4.data.dmem = d2.dmem := hm4.dmem_eq hwf3 rfl
  have hr12'' : reg st4.data .r12 = tA m0 := (hm4.regs .r12 _ rfl).trans hr12'
  have hr15'' : reg st4.data .r15 = sA m0 := (hm4.regs .r15 _ rfl).trans hr15'
  obtain ⟨d4, pc4⟩ := st4
  simp only at hpc4 hb4 hd4 hr12'' hr15''
  have hrun' : runL s c m0 = ((sumcheckPlain v 4 11).run s3).bind
      fun u ↦ rest5 c ch pt u.1.1 u.1.2 u.2 := hrun
  cases hr : (sumcheckPlain v 4 11).run s3 with
  | none =>
    rw [show (BitVec.ofNat 64 4).toNat = 4 from rfl, hr] at hout
    have hl : (envB m0 d2 [] (fun _ ↦ 0) 0).load 0 136 1 = BitVec.ofNat 64 0 :=
      bk_load1 (w := 0) (.inl rfl) hout.1
    rw [show (SBool.cmp .eq .W8 (.load 0 136 1) (.lit 0)).eval
        (envB m0 d2 [] (fun _ ↦ 0) 0) = true by simp only [SBool.eval, Sym.eval, hl]; decide]
      at hpc4
    simp only [↓reduceIte] at hpc4
    subst hpc4
    rw [lbl hp b86_in_code rfl]
    exact exit49 hp hpre hWo hb4 (by rw [hrun', hr]; rfl)
  | some r =>
    obtain ⟨⟨lp, val⟩, s4⟩ := r
    rw [show (BitVec.ofNat 64 4).toNat = 4 from rfl, hr] at hout
    obtain ⟨h1, hval⟩ := hout.1
    have hl : (envB m0 d2 [] (fun _ ↦ 0) 0).load 0 136 1 = BitVec.ofNat 64 1 :=
      bk_load1 (w := 1) (.inr rfl) h1
    rw [show (SBool.cmp .eq .W8 (.load 0 136 1) (.lit 0)).eval
        (envB m0 d2 [] (fun _ ↦ 0) 0) = false by simp only [SBool.eval, Sym.eval, hl]; decide]
      at hpc4
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc4
    subst hpc4
    have hlsz : lp.size = 11 := by
      have := (NativeRustcVm.Top.sumcheck_size v 4 (Array.replicate 11 none)).gives s3 _ s4 hr
      simpa using this
    have hlp4 : NativeRustcVm.EWsAt d4.dmem (off (stackBelow m0 2016) 296) lp.toList := by
      rw [hd4]; exact hout.2.1 lp val s4 rfl
    have hts4 : TStateAt d4.dmem (tA m0) a s4 := by rw [hd4]; exact hout.2.2 _ s4 rfl
    have hval' := NativeRustcVm.ewAt_iff.mp hval
    rw [show off (off (stackBelow m0 2016) 136) 8 = off (stackBelow m0 2016) 144 from
        NativeRustcVm.Transcript.off_add _ _ _,
      show off (stackBelow m0 2016) 144 + BitVec.ofNat 64 8 = off (stackBelow m0 2016) 152 from
        NativeRustcVm.Transcript.off_add _ _ _] at hval'
    -- `b55`: the values' slots cleared, `read_scalars(t, frame + 136, 3)`.
    rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b54Offset + b54.length = k + NativeRustcVmX64.Vm.VerifyLayer.b55Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b54_next]]
    have hwf5 := wf0 hS hb4 (vars := fun _ ↦ 0)
      (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b55Offset + b55.length)).toBitVec)
    have hm5 : Match (envB m0 d4 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b55Offset + b55.length)).toBitVec)
        (fr 24) d4 :=
      match_ofMachine ⟨rfl, trivial⟩ ⟨hb4.rsp, trivial⟩ trivial trivial trivial
    refine Body.blk (o' := 16) g hb4 hwf5 (blk hp b55_in_code (by simp [b55])) e55
      (fun _ _ ↦ rfl) hm5 (by decide +kernel) (hex0 (by decide +kernel))
      fun st6 hm6 hpc6 hb6 _ ↦ ?_
    have hts6 := ts_blk0 hpre hwf5 hm6 (by decide +kernel) (by decide +kernel) hts4
    have hfw6 : FWs m0 st6.data.dmem (wl3 m0 c ch) :=
      FWs.blkO (os := [32, 40, 48, 64, 80, 96, 120, 128, 224]) rfl hwf5 hm6 (by decide +kernel)
        (by decide +kernel) (by rw [hd4]; exact hfw2)
    have hfr6 := frSame_blk (o := 184) (n := 1840) hwf5 hm6 (by decide +kernel) (by decide)
      (by decide +kernel)
    have hr14 : reg st6.data .r14 = val.c0.toBitVec := by
      rw [show reg st6.data .r14 = _ from hm6.regs .r14 _ rfl]
      simp only [Sym.eval]
      rw [fload8 (by rw [hd4]; exact hval'.1)]
    have hrbx : reg st6.data .rbx = val.c1.toBitVec := by
      rw [show reg st6.data .rbx = _ from hm6.regs .rbx _ rfl]
      simp only [Sym.eval]
      rw [fload8 (by rw [hd4]; exact hval'.2)]
    have hrdi6 : reg st6.data .rdi = tA m0 := (hm6.regs .rdi _ rfl).trans hr12''
    have hrsi6 : reg st6.data .rsi = off (stackBelow m0 2016) 136 :=
      (hm6.regs .rsi _ rfl).trans (eval_ptr0 136)
    have hrdx6 : reg st6.data .rdx = BitVec.ofNat 64 3 := hm6.regs .rdx _ rfl
    have hr12_6 : reg st6.data .r12 = tA m0 := (hm6.regs .r12 _ rfl).trans hr12''
    have hr15_6 : reg st6.data .r15 = sA m0 := (hm6.regs .r15 _ rfl).trans hr15''
    have hat6 := hb6.at_ hpre hWo (by decide)
    have cx2 := ctx hpre (F := 2000) (by decide)
    have hA6 := frArea hpre hWo hb6 (Sk := readScalarsStack) (by decide) (o := 136) (n := 48)
      (by decide) (by decide)
    have hgot6 : GotAt st6.data readScalarsStack
        [(tA m0, tstateBytes), (a.words, 8 * a.len),
          (off (stackBelow m0 2016) 136, 48), (rcAddr, 192)] ["memcpy"] := by
      apply hb6.got hpre hWo (by decide) (by decide)
      simp only [NativeRustcVm.Transcript.DecArea.region]
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, le_rfl⟩
      · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
      · refine ⟨(stackBelow m0 verifyLayerStack, verifyLayerStack + 8), by simp, ?_, ?_⟩
        all_goals simp only [stack_eq, g.sbN, f136]; omega
      · exact ⟨(rcAddr, 192), by simp, le_rfl, le_rfl⟩
    refine call_then hpc6 (hrs s4) ⟨cx2.stackOk hat6 (by decide), cx2.rcAt hat6 (by decide),
      by rw [hrdi6]; exact hts6, by rw [hrdi6]; exact cx2.tstateOk hat6 (by decide),
      by rw [hrdi6, hrsi6, hrdx6]; exact ⟨hA6, hgot6⟩⟩ fun st7 hpc7 hrsp7 hq7 ↦ ?_
    obtain ⟨hok, hxs, hnext, hso7, hsv7⟩ := hq7
    rw [hrdx6, show (BitVec.ofNat 64 3).toNat = 3 from rfl] at hok hxs hnext hso7
    rw [hrsi6] at hxs hso7
    rw [hrdi6] at hnext hso7
    have hso7' : SameOutside st6.data.dmem st7.data.dmem (fun q ↦
        InRange (stackBelow st6.data readScalarsStack) readScalarsStack q ∨
          (InRange (off (stackBelow m0 2016) 136) (16 * 3) q ∨ InRange (tA m0) tstateBytes q)) :=
      NativeRustcVm.SameOutside.mono hso7 fun q hq ↦ by
        rcases hq with hq | hq | hq
        · exact .inr (.inl hq)
        · exact .inr (.inr hq)
        · exact .inl hq
    have hb7 : Body m0 (wFront m0) 24 st7.data :=
      Body.callX hpre hWo hb6 hsv7 hrsp7 (by decide) hso7' fun q hq ↦ by
        rcases hq with hq | hq
        · exact .inr (fr_sub g (by decide) (by decide) (by decide) hq)
        · exact .inl (.inl hq)
    have hmiss7 : ∀ {o n : Nat}, 24 ≤ o → o + n ≤ 2024 → o + n ≤ 136 ∨ 184 ≤ o →
        FrSame m0 st6.data.dmem st7.data.dmem o n := fun h1 h2 h3 ↦
      frSame_call g hb6 (by decide) hso7' (by omega) h2 fun q hq hq' ↦ by
        rcases hq with hq | hq
        · exact fr_miss g (by omega) (by decide) (by omega) hq hq'
        · exact (frame_not_t hpre (fr_in g (by omega) hq')).1 hq
    have hcs7 := hsv7.1
    obtain ⟨d7, pc7⟩ := st7
    simp only at hpc7 hb7 hok hxs hnext hcs7 hmiss7
    subst hpc7
    -- `b56`: `None` exits.
    rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b55Offset + b55.length = k + NativeRustcVmX64.Vm.VerifyLayer.b56Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b55_next]]
    have hwf8 := wf0 hS hb7 (vars := fun _ ↦ 0) (ret := 0)
    have hm8 : Match (envB m0 d7 [] (fun _ ↦ 0) 0) (fr 24) d7 :=
      match_ofMachine ⟨rfl, trivial⟩ ⟨hb7.rsp, trivial⟩ trivial trivial trivial
    refine Body.blk (o' := 24) g hb7 hwf8 (blk hp b56_in_code (by simp [b56])) e56 nofun hm8
      (by decide +kernel) (hex0 (by decide +kernel)) fun st9 hm9 hpc9 hb9 _ ↦ ?_
    simp only [PcOk] at hpc9
    rw [show (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)).eval
        (envB m0 d7 [] (fun _ ↦ 0) 0) = !((readScalars 3).run s4).isSome from okAl_test hok]
      at hpc9
    have hd9 : st9.data.dmem = d7.dmem := hm9.dmem_eq hwf8 rfl
    have hk9 : ∀ r ∈ [Reg64.r12, .r14, .rbx, .r15], reg st9.data r = reg d7 r :=
      keepR_regs hm9 (by decide +kernel) fun _ ↦ rfl
    obtain ⟨d9, pc9⟩ := st9
    simp only at hpc9 hb9 hd9 hk9
    have hrun5 : runL s c m0 = rest5 c ch pt lp val s4 := by rw [hrun', hr]; rfl
    cases hr5 : (readScalars 3).run s4 with
    | none =>
      rw [hr5] at hpc9
      simp only [Option.isSome_none, Bool.not_false, ↓reduceIte] at hpc9
      subst hpc9
      rw [lbl hp b86_in_code rfl]
      exact exit49 hp hpre hWo hb9 (by rw [hrun5, rest5, hr5]; rfl)
    | some w =>
      obtain ⟨t, s5⟩ := w
      rw [hr5] at hpc9 hxs hnext
      simp only [Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc9
      subst hpc9
      have htsz : t.size = 3 := NativeRustcVm.Sumcheck.readScalars_size hr5
      have hfrA : FrSame m0 d4.dmem d9.dmem 184 1840 := by
        rw [hd9]; exact hfr6.trans (hmiss7 (by decide) (by decide) (by decide))
      refine cont lp t val s5 d9 ⟨hb9, by rw [hd9]; exact hnext t s5 rfl,
        by rw [hd9]; exact FWs.keep3 (fun o ho ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact hmiss7 (by decide) (by decide) (by decide)) hfw6,
        (hfrA.sub (o' := 1704) (n' := 8 + 16 * 16) (by decide) (by decide)).buf
          (by rw [hd4]; exact hmu2),
        (hfrA.sub (o' := 1224) (n' := 480) (by decide) (by decide)).ews (by rw [hd4]; exact hpt2)
          (by rw [Array.length_toList, h.psz]; have := (claimPt hpre (fun _ h ↦ h) h.body).1
              omega),
        h.psz,
        (hfrA.sub (o' := 296) (n' := 176) (by decide) (by decide)).ews hlp4
          (by rw [Array.length_toList, hlsz]),
        hlsz, by rw [hd9]; exact hxs t s5 rfl, htsz,
        (hk9 .r14 (by simp)).trans ((hcs7 .r14 rfl).trans hr14),
        (hk9 .rbx (by simp)).trans ((hcs7 .rbx rfl).trans hrbx),
        (hk9 .r12 (by simp)).trans ((hcs7 .r12 rfl).trans hr12_6),
        (hk9 .r15 (by simp)).trans ((hcs7 .r15 rfl).trans hr15_6)⟩ ?_
      rw [hrun5, rest5_eq hr5]

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
