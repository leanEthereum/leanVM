module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.Inst
public import NativeRustcVm.Top.Phases
public import NativeRustcVmX64.Code.Vm.SumcheckOfVerifyLayer.Names

/-!
# `verify_layer` on x86-64: the equality-mode sumcheck

From `C2` (`b51`, code index `470`): the point's size spilled at the frame's `64`, the stack
arguments (the slots at the frame's `1224`, the point's size) pushed, `sumcheck<verify_layer>`
into the frame at `296` (`b51`), its `None` to the exit (`b52`): at `b53` (`485`) with `C3`:
`layer`.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVmX64.Sumcheck (Ctx At)
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)
open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- The frame's words from the equality-mode sumcheck on: `κ`, the `TState`, the point's size,
the scratch, the claim, the claim's bit weights, the point's and the instance weights' `Buf`s. -/
def wl3 (m0 : MachineData) (c : KeccakClaimW) (ch : EW) : List (Nat × UInt64) :=
  [(32, (kap ch).c0), (40, .ofBitVec (tA m0)), (48, (kap ch).c1),
    (64, .ofBitVec (BitVec.ofNat 64 c.point.size)), (80, .ofBitVec (sA m0)),
    (96, .ofBitVec (cA m0)), (120, .ofBitVec (sA m0 + 25600#64)),
    (128, .ofBitVec (cA m0 + 280#64)), (224, .ofBitVec (cA m0 + 16#64))]

/-- `wl3` but the point's size. -/
def wl3a (m0 : MachineData) (ch : EW) : List (Nat × UInt64) :=
  [(32, (kap ch).c0), (40, .ofBitVec (tA m0)), (48, (kap ch).c1), (80, .ofBitVec (sA m0)),
    (96, .ofBitVec (cA m0)), (120, .ofBitVec (sA m0 + 25600#64)),
    (128, .ofBitVec (cA m0 + 280#64)), (224, .ofBitVec (cA m0 + 16#64))]

/-- **After the equality-mode sumcheck** (`b53`, code index `485`): its challenges `pt` at the
frame's `1224`, its final claim `v` at `304`, the `TState` `s3` (in R12), the scratch in R15. -/
structure C3 (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (ch : EW) (pt : Array EW)
    (v : EW) (s3 : TState) (d : MachineData) : Prop where
  body : Body m0 (wFront m0) 24 d
  ts : TStateAt d.dmem (tA m0) a s3
  fw : FWs m0 d.dmem (wl3 m0 c ch)
  mu : NativeRustcVm.BufEWAt d.dmem (off (stackBelow m0 2016) 1704) 16
    (keccakInstanceWeights ch).toList
  hpt : NativeRustcVm.EWsAt d.dmem (off (stackBelow m0 2016) 1224) pt.toList
  psz : pt.size = c.point.size
  hv : NativeRustcVm.EWAt d.dmem (off (stackBelow m0 2016) 304) v
  r12 : reg d .r12 = tA m0
  r15 : reg d .r15 = sA m0

end

public section

variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- **The claim's point** in a body of the front. -/
theorem claimPt (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop}
    (hW : ∀ q, W q → wFront m0 q) {o : Nat} {d : MachineData} (hb : Body m0 W o d) :
    c.point.size ≤ 30 ∧ NativeRustcVm.EWsAt d.dmem (cA m0 + 288#64) c.point.toList := by
  obtain ⟨-, -, hplen, -, hpts⟩ := hb.claim hpre hW
  refine ⟨by simpa [NativeRustcVm.KeccakGkr.claimPointCap] using hplen, ?_⟩
  have e : NativeRustcVm.KeccakGkr.off (cA m0) NativeRustcVm.KeccakGkr.pointOff + 8#64 =
      cA m0 + 288#64 := by
    unfold NativeRustcVm.KeccakGkr.off NativeRustcVm.KeccakGkr.pointOff; bv_omega
  rwa [e] at hpts

end

public section

variable [Host] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData} {k : Nat}
  {p : Array EW}

/-- **The equality-mode sumcheck**, from `b51` to `b53`. -/
theorem layer (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    (hsl : ∀ s pt, Spec (Labels.label NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.entryLabel) (SumcheckLayerPre a s pt)
      (SumcheckLayerPost a s pt))
    {ch : EW} {s2 : TState} {d : MachineData} (h : C2 m0 a c p ch s2 d)
    (hrun : runL s c m0 = rest3 c p ch s2)
    (cont : ∀ pt v s3 d', C3 m0 a c ch pt v s3 d' → runL s c m0 = rest4 c ch pt v s3 →
      Eventually (step1 Host.exe) (Goal a s c m0) ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b53Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s c m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b51Offset)⟩ := by
  have g := geo_of hpre
  have hWo := wFront_outs hpre
  have hS := pre_stack hpre
  have cx := ctx hpre (F := 2016) (by decide)
  obtain ⟨hsz, hpts⟩ := claimPt hpre (fun _ h ↦ h) h.body
  have hN := g.hN; have htop := g.top; have hfb := g.fbN; have hsb := g.sbN
  have hc := g.hc; have ht := g.ht; have hts := g.hts; have hcs := g.hcs; have htc := g.htc
  -- the words but the point's size
  have hL0 : FWs m0 d.dmem (wl3a m0 ch) := by
    intro q hq
    simp only [wl3a, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.k32
    · exact bw40 h.fw
    · exact h.k48
    · exact bw80 h.fw
    · exact bw96 h.fw
    · exact bw120 h.fw
    · exact bw128 h.fw
    · exact bw224 h.fw
  -- `b51`: the point's size spilled, the stack arguments pushed.
  have hwf := wf0 hS h.body (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b51Offset + b51.length)).toBitVec)
  have hm : Match (envB m0 d [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b51Offset + b51.length)).toBitVec)
      (fr 24) d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨h.body.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 0) g h.body hwf (blk hp b51_in_code (by simp [b51])) e51
    (fun _ _ ↦ rfl) hm (by decide +kernel) (hex0 (by decide +kernel)) fun st hm1 hpc1 hb1 _ ↦ ?_
  have hts1 := ts_blk0 hpre hwf hm1 (by decide +kernel) (by decide +kernel) h.ts
  have hL1 : FWs m0 st.data.dmem (wl3a m0 ch) :=
    FWs.blkO (os := [32, 40, 48, 80, 96, 120, 128, 224]) rfl hwf hm1 (by decide +kernel)
      (by decide +kernel) hL0
  have hw64 : NativeRustcVm.WordAt st.data.dmem (off (stackBelow m0 2016) 64)
      (.ofBitVec (BitVec.ofNat 64 c.point.size)) :=
    fwW hm1 rfl rfl (by decide) (by decide +kernel) (by exact h.r15)
  have hw8 : NativeRustcVm.WordAt st.data.dmem (off (stackBelow m0 2016) 8)
      (.ofBitVec (off (stackBelow m0 2016) 1224)) :=
    fwW hm1 rfl rfl (by decide) (by decide +kernel) (by exact eval_ptr0 1224)
  have hw16 : NativeRustcVm.WordAt st.data.dmem (off (stackBelow m0 2016) 16)
      (.ofBitVec (BitVec.ofNat 64 c.point.size)) :=
    fwW hm1 rfl rfl (by decide) (by decide +kernel) (by exact h.r15)
  have hfw1 : FWs m0 st.data.dmem (wl3 m0 c ch) := by
    intro q hq
    simp only [wl3, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hL1 _ (by fw_mem)
    · exact hL1 _ (by fw_mem)
    · exact hL1 _ (by fw_mem)
    · exact hw64
    · exact hL1 _ (by fw_mem)
    · exact hL1 _ (by fw_mem)
    · exact hL1 _ (by fw_mem)
    · exact hL1 _ (by fw_mem)
    · exact hL1 _ (by fw_mem)
  have hmu1 := (frSame_blk (o := 1704) (n := 8 + 16 * 16) hwf hm1 (by decide +kernel) (by decide)
    (by decide +kernel)).buf h.mu
  have hsp1 : rspOf st.data = stackBelow m0 2016 := by
    rw [hb1.fr.sp]; exact NativeRustcVm.Transcript.off_zero _
  have hrdi : reg st.data .rdi = off (stackBelow m0 2016) 296 :=
    (hm1.regs .rdi _ rfl).trans (eval_ptr0 296)
  have hrsi : reg st.data .rsi = tA m0 := (hm1.regs .rsi _ rfl).trans h.r14
  have hr8 : reg st.data .r8 = cA m0 + 288#64 := (hm1.regs .r8 _ rfl).trans h.rbp
  have hr9 : reg st.data .r9 = BitVec.ofNat 64 c.point.size := (hm1.regs .r9 _ rfl).trans h.r15
  have hr12 : reg st.data .r12 = tA m0 := (hm1.regs .r12 _ rfl).trans h.r12
  have hcl : claimArg st.data = polyEval p ch := by
    show ewArg (reg st.data .rdx) (reg st.data .rcx) = _
    rw [show reg st.data .rdx = _ from hm1.regs .rdx _ rfl,
      show reg st.data .rcx = _ from hm1.regs .rcx _ rfl]
    exact h.pe
  have hszN : (BitVec.ofNat 64 c.point.size).toNat = c.point.size := by
    rw [BitVec.toNat_ofNat]; omega
  have ha0 : stackArg st.data 0 = off (stackBelow m0 2016) 1224 := by
    unfold stackArg
    rw [hsp1, show stackBelow m0 2016 + BitVec.ofNat 64 (8 + 8 * 0) = off (stackBelow m0 2016) 8
      from rfl, NativeRustcVm.wordOf_of_wordAt hw8]
  have ha1 : stackArg st.data 1 = BitVec.ofNat 64 c.point.size := by
    unfold stackArg
    rw [hsp1, show stackBelow m0 2016 + BitVec.ofNat 64 (8 + 8 * 1) = off (stackBelow m0 2016) 16
      from rfl, NativeRustcVm.wordOf_of_wordAt hw16]
  have hat : At m0 2016 st.data := hb1.at_ hpre hWo (by decide)
  have hle : 2016 + sumcheckLayerStack ≤ 3232 := by decide
  have hslN : sumcheckLayerStack ≤ 1216 := by decide
  have hstk : (stackBelow st.data sumcheckLayerStack).toNat =
      (rspOf m0).toNat - 2016 - sumcheckLayerStack := by
    rw [stackBelow_toNat (by rw [hsp1, hfb]; omega), hsp1, hfb]
  have f8 : (off (stackBelow m0 2016) 8).toNat = (rspOf m0).toNat - 2016 + 8 := g.fa (by decide)
  have f296 : (off (stackBelow m0 2016) 296).toNat = (rspOf m0).toNat - 2016 + 296 :=
    g.fa (by decide)
  have f1224 : (off (stackBelow m0 2016) 1224).toNat = (rspOf m0).toNat - 2016 + 1224 :=
    g.fa (by decide)
  have c288 : (cA m0 + 288#64).toNat = (cA m0).toNat + 288 := g.ca (by decide)
  have hr8sp : rspOf st.data + 8#64 = off (stackBelow m0 2016) 8 := by rw [hsp1]
  have hpre1 : SumcheckLayerPre a s2 c.point st.data := by
    unfold SumcheckLayerPre SumcheckOk
    rw [hrsi, hrdi, hr8, hr9, ha0, ha1, hszN, hr8sp]
    refine ⟨⟨?_, ?_⟩, ⟨cx.stackOk hat hle, cx.rcAt hat hle, hts1, cx.tstateOk hat hle,
      by decide, by decide, cx.outOk_frame hat hle (by decide) (by decide),
      cx.outOk_frame hat hle (by decide) (by omega), ?_, ?_⟩, rfl, (claimPt hpre (fun _ h ↦ h) hb1).2,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show NativeRustcVm.Mapped _ (rspOf st.data + 8#64) _
      rw [hr8sp]
      exact mapped_off (NativeRustcVm.Transcript.Mapped.keeps (frame_mapped (F := 2016) hS
        (by decide)) hb1.fr.kept) (by decide)
    · rw [hsp1, hfb]; omega
    · unfold NativeRustcX64.Apart; rw [f296, f1224]; omega
    · apply hb1.got hpre hWo (by decide) (by decide)
      simp only [NativeRustcVm.Transcript.DecArea.region]
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, le_rfl⟩
      · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
      · refine ⟨(stackBelow m0 verifyLayerStack, verifyLayerStack + 8), by simp, ?_, ?_⟩
        all_goals simp only [stack_eq, g.sbN, f296]; omega
      · refine ⟨(stackBelow m0 verifyLayerStack, verifyLayerStack + 8), by simp, ?_, ?_⟩
        all_goals simp only [stack_eq, g.sbN, f1224]; omega
      · exact ⟨(rcAddr, 192), by simp, le_rfl, le_rfl⟩
    · unfold NativeRustcX64.NoWrap; rw [c288]; omega
    · unfold NativeRustcX64.Apart; rw [c288, hstk]; omega
    · unfold NativeRustcX64.Apart tstateBytes; rw [c288]; omega
    · unfold NativeRustcX64.Apart; rw [c288, f1224]; omega
    · unfold NativeRustcX64.Apart tstateBytes; rw [f8]; omega
    · unfold NativeRustcX64.Apart; rw [f8, f1224]; omega
  refine call_then hpc1 (hsl s2 c.point) hpre1 fun st2 hpc2 hrsp2 hq2 ↦ ?_
  obtain ⟨hout, hso, hsv⟩ := hq2
  rw [hrsi, hrdi, ha0, ha1, hszN, hcl, NativeRustcVm.Sumcheck.sumcheckFn_getElem?] at hout
  rw [hrsi, hrdi, ha0, ha1, hszN] at hso
  have hso' : SameOutside st.data.dmem st2.data.dmem (fun q ↦
      InRange (stackBelow st.data sumcheckLayerStack) sumcheckLayerStack q ∨
        (InRange (off (stackBelow m0 2016) 296) 24 q ∨
          InRange (off (stackBelow m0 2016) 1224) (16 * c.point.size) q ∨
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
      · exact .inr (fr_sub g (lo := 8) (len := 1960) (by decide) (by omega) (by decide) hq)
      · exact .inl (.inl hq)
  have hmiss : ∀ {o n : Nat}, 24 ≤ o → o + n ≤ 2024 → o + n ≤ 296 ∨ (320 ≤ o ∧ o + n ≤ 1224) ∨
      1704 ≤ o → FrSame m0 st.data.dmem st2.data.dmem o n := fun h1 h2 h3 ↦
    frSame_call g hb1 (oc := 0) (by decide) hso' (by omega) h2 fun q hq hq' ↦ by
      rcases hq with hq | hq | hq
      · exact fr_miss g (by omega) (by decide) (by omega) hq hq'
      · exact fr_miss g (by omega) (by omega) (by omega) hq hq'
      · exact (frame_not_t hpre (fr_in g (by omega) hq')).1 hq
  have hfw2 : FWs m0 st2.data.dmem (wl3 m0 c ch) :=
    FWs.keepR (os := [32, 40, 48, 64, 80, 96, 120, 128, 224]) rfl (hmiss (o := 24) (n := 248) (by decide) (by decide) (by decide))
      (by decide +kernel) hfw1
  have hmu2 := (hmiss (o := 1704) (n := 8 + 16 * 16) (by decide) (by decide) (by decide)).buf hmu1
  have hr12' : reg st2.data .r12 = tA m0 := (hsv.1 .r12 rfl).trans hr12
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2 hb2 hout hfw2 hmu2 hr12'
  subst hpc2
  -- `b52`: `None` exits.
  rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b51Offset + b51.length = k + NativeRustcVmX64.Vm.VerifyLayer.b52Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b51_next]]
  have hwf3 := wf0 hS hb2 (vars := fun _ ↦ 0) (ret := 0)
  have hm3 : Match (envB m0 d2 [] (fun _ ↦ 0) 0) (fr 8) d2 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hb2.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 24) g hb2 hwf3 (blk hp b52_in_code (by simp [b52])) e52 nofun hm3
    (by decide +kernel) (hex0 (by decide +kernel)) fun st4 hm4 hpc4 hb4 _ ↦ ?_
  simp only [PcOk] at hpc4
  have hd4 : st4.data.dmem = d2.dmem := hm4.dmem_eq hwf3 rfl
  have hr12'' : reg st4.data .r12 = tA m0 := (hm4.regs .r12 _ rfl).trans hr12'
  have hr15 : reg st4.data .r15 = sA m0 := by
    rw [show reg st4.data .r15 = _ from hm4.regs .r15 _ rfl]
    simp only [Sym.eval]
    rw [fload8 (hfw2 (80, .ofBitVec (sA m0)) (by fw_mem))]
  obtain ⟨d4, pc4⟩ := st4
  simp only at hpc4 hb4 hd4 hr12'' hr15
  cases hr : (sumcheck (polyEval p ch) 3 (c.point.map some)).run s2 with
  | none =>
    rw [hr] at hout
    have hl : (envB m0 d2 [] (fun _ ↦ 0) 0).load 0 296 4 = BitVec.ofNat 64 0 :=
      bk_load4 (w := 0) (.inl rfl) hout.1
    rw [show ((SBool.cmp .eq .W32 (.load 0 296 4) (.lit 1)).not).eval
        (envB m0 d2 [] (fun _ ↦ 0) 0) = true by simp only [SBool.eval, Sym.eval, hl]; decide]
      at hpc4
    simp only [↓reduceIte] at hpc4
    subst hpc4
    rw [lbl hp b86_in_code rfl]
    exact exit49 hp hpre hWo hb4 (by rw [hrun, rest3, hr]; rfl)
  | some r =>
    obtain ⟨⟨pt, v⟩, s3⟩ := r
    rw [hr] at hout
    obtain ⟨h1, hv⟩ := hout.1
    have hl : (envB m0 d2 [] (fun _ ↦ 0) 0).load 0 296 4 = BitVec.ofNat 64 1 :=
      bk_load4 (w := 1) (.inr rfl) h1
    rw [show ((SBool.cmp .eq .W32 (.load 0 296 4) (.lit 1)).not).eval
        (envB m0 d2 [] (fun _ ↦ 0) 0) = false by simp only [SBool.eval, Sym.eval, hl]; decide]
      at hpc4
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc4
    subst hpc4
    have hpsz : pt.size = c.point.size := by
      have := (NativeRustcVm.Top.sumcheck_size _ _ _).gives s2 _ s3 hr
      simpa using this
    have e304 : off (off (stackBelow m0 2016) 296) 8 = off (stackBelow m0 2016) 304 :=
      NativeRustcVm.Transcript.off_add _ _ _
    rw [e304] at hv
    refine cont pt v s3 d4 ⟨hb4, by rw [hd4]; exact hout.2.2 _ s3 rfl, by rw [hd4]; exact hfw2,
      by rw [hd4]; exact hmu2, by rw [hd4]; exact hout.2.1 pt v s3 rfl, hpsz, by rw [hd4]; exact hv,
      hr12'', hr15⟩ ?_
    rw [hrun, rest3, hr]
    rfl

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
