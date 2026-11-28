module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.ProjLoop
public import NativeVm.Math.Keccak.Facts
public import NativeRustcVmX64.Code.Vm.EqKernel.Names

/-!
# `verify_layer` on x86-64: the segment kernel

From `NativeRustcVmX64.Vm.VerifyLayer.label_17` (`PEnd`): `b24` spills the point's address and calls `eq_kernel` on the
point's coordinates past the pack's into the frame's four elements at `232`; `b25` (never taken:
the kernel exists, `SegmentsFit`) continues at `b26` (`SG`): `segs`.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVmX64.Sumcheck (Ctx At)
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)
open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- The spills after `b24`: the point's address at `64`. -/
def spills2 (m0 : MachineData) (c : KeccakClaimW) : List (Nat × UInt64) :=
  [(24, packV m0), (32, c.mu.size.toUInt64), (40, .ofBitVec (tA m0)),
    (48, .ofBitVec (cA m0 + 24#64)), (56, .ofBitVec (reg m0 .rdx)),
    (64, .ofBitVec (cA m0 + 288#64)), (80, .ofBitVec (sA m0)), (96, .ofBitVec (cA m0)),
    (224, .ofBitVec (cA m0 + 16#64))]

/-- The segment kernel of the claim's point. -/
def segK (m0 : MachineData) (c : KeccakClaimW) : Array EW :=
  eqKernel (c.point.extract ((reg m0 .rsi).toNat - 4) c.point.size)

/-- **The segment kernel computed**, at `b26`. -/
structure SG [Labels] (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW)
    (s1 : TState) (d : MachineData) : Prop where
  body : Body m0 (wFront m0) 24 d
  ts : TStateAt d.dmem (tA m0) a s1
  prod : NativeRustcVm.EWsAt d.dmem (off (stackBelow m0 2016) 472) p.toList
  sp : FWs m0 d.dmem (spills2 m0 c)
  seg : NativeRustcVm.EWsAt d.dmem (off (stackBelow m0 2016) 232) (segK m0 c).toList
  r14 : reg d .r14 = cA m0
  acc : ewArg (reg d .r12) (reg d .r13) = projectedOf c.mu p
  psize : p.size = 47
  ssize : 2 ≤ (segK m0 c).size

end

public section

variable {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

theorem spills2_in (c : KeccakClaimW) : ∀ q ∈ spills2 m0 c, 24 ≤ q.1 ∧ q.1 + 8 ≤ 232 := by
  intro q hq
  simp only [spills2, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem segK_size :
    (segK m0 c).size = 2 ^ (c.point.size - ((reg m0 .rsi).toNat - 4)) := by
  rw [segK, NativeVm.Math.Keccak.eqKernel_size, Array.size_extract, Nat.min_self]

theorem pack_lt (h : SegmentsFit (reg m0 .rsi).toNat c) (hp : c.point.size ≤ 30) :
    (packV m0).toNat = (reg m0 .rsi).toNat - 4 := by
  unfold packV
  have := h.1
  rw [Nat.toUInt64, UInt64.toNat_ofNat']
  have := (reg m0 .rsi).isLt
  omega

/-- The point's coordinates past the pack's, read from the claim. -/
theorem extract_ews {d : DataMem} {x : BitVec 64} {pt : Array EW} (h : NativeRustcVm.EWsAt d x pt.toList)
    {P : Nat} :
    (NativeRustcVm.ewsOf d (x + BitVec.ofNat 64 (16 * P)) (pt.size - P)).toArray = pt.extract P pt.size := by
  have h2 := NativeRustcVm.EWsAt.drop h P
  have e := NativeRustcVm.ewsOf_of_ewsAt h2
  rw [List.length_drop, Array.length_toList] at e
  rw [e]
  apply Array.ext'
  simp [Array.toList_extract, List.extract]

theorem shl4 (x : BitVec 64) :
    BinOp.apply .shl .W64 x (BitVec.ofNat 64 4) = BitVec.ofNat 64 (16 * x.toNat) := by
  simp only [BinOp.apply, low_W64, ext_W64, shiftCount, shiftMask]
  apply BitVec.eq_of_toNat_eq
  simp [low, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

theorem ite_lt31 (x : BitVec 64) (h : x.toNat < 31) :
    (if (!CmpOp.apply .ult .W64 x (BitVec.ofNat 64 31)) = true then BitVec.ofNat 64 0 else x) = x := by
  rw [ult64]; simp [h]

theorem ite_lt31' (x y : BitVec 64) (h : x.toNat < 31) :
    (if CmpOp.apply .ult .W64 x (BitVec.ofNat 64 31) = true then y else BitVec.ofNat 64 8) = y := by
  rw [ult64]; simp [h]

theorem ite_ge (x y u v : BitVec 64) (h : ¬x.toNat < y.toNat) :
    (if CmpOp.apply .ult .W64 x y = true then u else v) = v := by
  rw [ult64]; simp [h]

theorem test_al1 : CmpOp.apply .eq .W8 (BinOp.apply .and .W8 1#64 (BitVec.ofNat 64 1))
    (BitVec.ofNat 64 0) = false := by decide

variable [Host] {k : Nat} {p : Array EW} {s1 : TState}

/-- **The segment kernel**: `b24`, `eq_kernel`, `b25`. -/
theorem segs (hp : Placed code k) (hek : Spec (Labels.label NativeRustcVmX64.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost)
    (hpre : VerifyLayerPre a s c m0) {d : MachineData} (h : PEnd m0 a c p s1 d)
    {R : MachineState → Prop}
    (cont : ∀ d', SG m0 a c p s1 d' → Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b26Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b24Offset)⟩ := by
  have g := geo_of hpre
  have hWo := wFront_outs hpre
  have hseg := pre_seg hpre
  obtain ⟨-, -, hplen, hpw, hpts⟩ := h.body.claim hpre fun _ h ↦ h
  have hplen' : c.point.size ≤ 30 := by
    simpa [NativeRustcVm.KeccakGkr.claimPointCap] using hplen
  have hpk := pack_lt hseg hplen'
  have hwf : (envB m0 d [(cA m0, 768)] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b24Offset + b24.length)).toBitVec).WF :=
    wfC hpre h.body
  have hm : Match (envB m0 d [(cA m0, 768)] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b24Offset + b24.length)).toBitVec)
      (claimS (.load 0 96 8)) d :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨h.body.rsp, trivial⟩ trivial trivial
      ⟨by show Env.load _ 0 96 8 = cA m0 + BitVec.ofInt 64 0
          rw [fload8 (sp96 h.sp)]; simp, trivial⟩
  refine Body.blk (o' := 16) g h.body hwf (blk hp b24_in_code (by simp [b24])) e24 (fun _ _ ↦ rfl)
    hm (by decide +kernel) (hex0 (by decide +kernel)) fun st hm1 hpc1 hb1 hs1 ↦ ?_
  have e1 : ∀ r, (envB m0 d [(cA m0, 768)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b24Offset + b24.length)).toBitVec).regs r = reg d r := fun _ ↦ rfl
  have hl280 : (envB m0 d [(cA m0, 768)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b24Offset + b24.length)).toBitVec).load 1 280 8 = BitVec.ofNat 64 c.point.size := by
    rw [cload (o := 280) hpw]; simp only [Array.length_toList, Nat.toUInt64]; rfl
  have hl24 : (envB m0 d [(cA m0, 768)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b24Offset + b24.length)).toBitVec).load 0 24 8 = (packV m0).toBitVec :=
    fload8 (sp24 h.sp)
  have hl96 : (envB m0 d [(cA m0, 768)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b24Offset + b24.length)).toBitVec).load 0 96 8 = cA m0 :=
    fload8 (sp96 h.sp)
  have hpkB : (packV m0).toBitVec = BitVec.ofNat 64 ((reg m0 .rsi).toNat - 4) := rfl
  rw [hpkB] at hl24
  generalize hP : (reg m0 .rsi).toNat - 4 = P at hl24 hpk
  have hP30 : P < 30 := by have := hseg.1; omega
  have hlt : ¬(BitVec.ofNat 64 c.point.size).toNat < (BitVec.ofNat 64 P).toNat := by
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; have := hseg.1; omega
  have hrsi : reg st.data .rsi = BitVec.ofNat 64 (c.point.size - P) := by
    rw [show reg st.data .rsi = _ from hm1.regs .rsi _ rfl]
    simp only [Sym.eval, SBool.eval, hl280, hl24]
    rw [ite_lt31 _ (by rw [BitVec.toNat_ofNat]; omega), ite_ge _ _ _ _ hlt, sub64]
    have := hseg.1
    bv_omega
  have hrdi : reg st.data .rdi = cA m0 + BitVec.ofNat 64 (288 + 16 * P) := by
    rw [show reg st.data .rdi = _ from hm1.regs .rdi _ rfl]
    simp only [Sym.eval, SBool.eval, hl280, hl24, hl96]
    rw [ite_lt31 _ (by rw [BitVec.toNat_ofNat]; omega), ite_ge _ _ _ _ hlt,
      ite_lt31' _ _ (by rw [BitVec.toNat_ofNat]; omega), add64, add64, shl4,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    bv_omega
  have hrdx : reg st.data .rdx = off (stackBelow m0 2000) 216 := by
    rw [off_fr]; exact (hm1.regs .rdx _ rfl).trans (eval_ptr0 232)
  have hrcx : reg st.data .rcx = 4#64 := hm1.regs .rcx _ rfl
  have hr14 : reg st.data .r14 = cA m0 := by
    rw [show reg st.data .r14 = _ from hm1.regs .r14 _ rfl]; exact hl96
  have hcs1 : ∀ r ∈ [Reg64.r12, .r13], reg st.data r = reg d r :=
    keepR_regs hm1 (by decide +kernel) fun _ ↦ rfl
  have hts1 := ts_blk0 hpre hwf hm1 (by decide +kernel) (by decide +kernel) h.ts
  have hfrA := frSame_blk (o := 296) (n := 1720) hwf hm1 (by decide +kernel) (by decide)
    (by decide +kernel)
  have hfrB := frSame_blk (o := 24) (n := 40) hwf hm1 (by decide +kernel) (by decide)
    (by decide +kernel)
  have hfrC := frSame_blk (o := 72) (n := 160) hwf hm1 (by decide +kernel) (by decide)
    (by decide +kernel)
  have hw64 := fwW (o := 64) hm1 rfl rfl (by decide) (by decide +kernel) (w := .ofBitVec (cA m0 + 288#64))
    (by simp only [Sym.eval, hl96, add64])
  have hpts1 : NativeRustcVm.EWsAt st.data.dmem (cA m0 + 288#64) c.point.toList := by
    have e : NativeRustcVm.KeccakGkr.off (cA m0) NativeRustcVm.KeccakGkr.pointOff + 8#64 =
        cA m0 + 288#64 := by
      unfold NativeRustcVm.KeccakGkr.off NativeRustcVm.KeccakGkr.pointOff; bv_omega
    have := (hb1.claim hpre fun _ h ↦ h).2.2.2.2
    rwa [e] at this
  have cx := ctx hpre (F := 2000) (by decide)
  have hat := hb1.at_ hpre hWo (by decide)
  have hS := pre_stack hpre
  have hsl := claimSlice hpre hWo hb1 (Sk := eqKernelStack) (by decide) (o := 288 + 16 * P)
    (n := 16 * (c.point.size - P)) (by omega) (by omega)
  have hout := cx.outOk_frame hat (Nc := eqKernelStack) (by decide) (o := 216) (n := 64)
    (by decide) (by decide)
  have hcap := areas_stack (pre_areas hpre) (w := ⟨cA m0, 768⟩) (by simp)
  have hn1 : 1 ≤ c.point.size - P := by have := hseg.1; omega
  have hn2 : c.point.size - P ≤ 2 := by have := hseg.2; omega
  have hpow : 2 ^ (c.point.size - P) ≤ 4 := by
    rcases (show c.point.size - P = 1 ∨ c.point.size - P = 2 by omega) with h' | h' <;>
      rw [h'] <;> decide
  refine call_then hpc1 hek ⟨cx.stackOk hat (by decide), ?_, ⟨⟨?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    fun st2 hpc2 hrsp2 hq ↦ ?_
  · rw [hrsi, BitVec.toNat_ofNat]; omega
  · rw [hrdi, hrsi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hsl.1
  · rw [hrdi, hrsi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hsl.2.1
  · rw [hrdi, hrsi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hsl.2.2
  · rw [hrdx, hrcx]; exact hout.1
  · rw [hrdx, hrcx]; exact hout.2.1
  · rw [hrdx, hrcx]; exact hout.2.2.2.2.1
  · rw [hrdi, hrsi, hrdx, hrcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hfb := g.fbN; have := g.hN; have := g.top; have := g.hc; have hsb := g.sbN
    have h2000 : (off (stackBelow m0 2000) 216).toNat = (rspOf m0).toNat - 2016 + 232 := by
      rw [off_fr]; exact g.fa (o := 232) (by omega)
    have hcN : (cA m0 + BitVec.ofNat 64 (288 + 16 * P)).toNat = (cA m0).toNat + (288 + 16 * P) :=
      g.ca (by omega)
    unfold NativeRustcVm.Apart at hcap
    unfold NativeRustcX64.Apart
    dsimp only at hcap
    rw [hsb] at hcap
    rw [hcN, h2000, show (4#64 : BitVec 64).toNat = 4 from rfl]
    omega
  obtain ⟨hres, hch, hsv⟩ := hq
  simp only [hrsi, hrcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c.point.size - P < 2 ^ 64 by omega),
    show (4#64 : BitVec 64).toNat = 4 from rfl, hpow, ↓reduceIte] at hres
  obtain ⟨hrax, -, hker⟩ := hres
  have hsl' : slice st.data (reg st.data .rdi) (BitVec.ofNat 64 (c.point.size - P)) =
      c.point.extract P c.point.size := by
    unfold slice
    rw [hrdi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [show cA m0 + BitVec.ofNat 64 (288 + 16 * P) = cA m0 + 288#64 + BitVec.ofNat 64 (16 * P) by
      bv_omega]
    exact extract_ews hpts1
  rw [hsl', hrdx] at hker
  rw [hrdx, hrcx, show (4#64 : BitVec 64).toNat = 4 from rfl] at hch
  have hWc : ∀ q, (fun q ↦ InRange (off (stackBelow m0 2000) 216) (16 * 4) q ∨
      InRange (stackBelow st.data eqKernelStack) eqKernelStack q) q →
      InRange (stackBelow st.data eqKernelStack) eqKernelStack q ∨
        InRange (off (stackBelow m0 2016) 232) 64 q := fun q hq ↦ by
    rcases hq with hq | hq
    · right; rwa [off_fr] at hq
    · left; exact hq
  have hso2 := NativeRustcVm.SameOutside.mono hch hWc
  have hb2 : Body m0 (wFront m0) 24 st2.data :=
    Body.call g hWo hb1 (by decide) hsv hrsp2 (by decide) hso2 fun q hq ↦ .inr
      (fr_sub g (by decide) (by decide) (by decide) hq)
  have hkeep : ∀ o n, 24 ≤ o → o + n ≤ 2016 → (o + n ≤ 232 ∨ 296 ≤ o) →
      FrSame m0 st.data.dmem st2.data.dmem o n := fun o n h1 h2 h3 ↦
    frSame_call g hb1 (by decide) hso2 (by omega) (by omega) fun q hq hq' ↦ by
      have := g.top; have := g.hN
      by_cases hn : n = 0
      · subst hn; unfold InRange at hq'; omega
      rw [Sym.inRange_iff (by rw [off, g.fa (by omega)]; omega), off, g.fa (by omega)] at hq hq'
      omega
  have hts2 : TStateAt st2.data.dmem (tA m0) a s1 :=
    hts1.frame hsv.2 (fun q hq ↦ hq.elim
      (fun hq ↦ (ctx hpre (F := 2000) (by decide)).stack_not_t
        ((ctx hpre (F := 2000) (by decide)).inRange_callee hat (by decide) hq).1)
      fun hq ↦ frame_not_t hpre (fr_in g (o := 232) (n := 64) (by decide) hq)) hso2
  have hcs2 : ∀ r ∈ [Reg64.r12, .r13, .r14], reg st2.data r = reg st.data r := fun r hr ↦
    hsv.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                rcases hr with rfl | rfl | rfl <;> rfl)
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2 hb2 hts2 hrax hker hcs2 hkeep
  subst hpc2
  -- `b25`
  have hwf3 := wf0 (pre_stack hpre) hb2 (vars := fun _ ↦ 0) (ret := 0)
  have hm3 : Match (envB m0 d2 [] (fun _ ↦ 0) 0) (fr 24) d2 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hb2.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 24) g hb2 hwf3 (blk hp b25_in_code (by simp [b25])) e25 nofun hm3
    (by decide +kernel) (hex0 (by decide +kernel)) fun st hm4 hpc4 hb4 _ ↦ ?_
  simp only [PcOk] at hpc4
  rw [show (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.lit 1)) (.lit 0)).eval
      (envB m0 d2 [] (fun _ ↦ 0) 0) = false by
    simp only [SBool.eval, Sym.eval]
    rw [show (envB m0 d2 [] (fun _ ↦ 0) 0).regs .rax = reg d2 .rax from rfl, hrax]
    exact test_al1] at hpc4
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc4
  have hd4 : st.data.dmem = d2.dmem := hm4.dmem_eq hwf3 rfl
  have hk4 : ∀ r ∈ [Reg64.r12, .r13, .r14], reg st.data r = reg d2 r :=
    keepR_regs hm4 (by decide +kernel) fun _ ↦ rfl
  obtain ⟨d4, pc4⟩ := st
  simp only at hpc4 hb4 hd4 hk4
  subst hpc4
  refine cont d4 ⟨hb4, by rw [hd4]; exact hts2, ?_, ?_, ?_, ?_, ?_, h.psize, ?_⟩
  · rw [hd4]
    exact ((hfrA.trans (hkeep 296 1720 (by decide) (by decide) (by decide))).sub
      (o' := 472) (n' := 752) (by decide) (by decide)).ews h.prod (by rw [Array.length_toList, h.psize])
  · rw [hd4]
    have hB := hfrB.trans (hkeep 24 40 (by decide) (by decide) (by decide))
    have hC := hfrC.trans (hkeep 72 160 (by decide) (by decide) (by decide))
    have h64 := (hkeep 64 8 (by decide) (by decide) (by decide)).word hw64 (by decide)
    intro q hq
    simp only [spills2, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hB.sub (o' := 24) (n' := 8) (by decide) (by decide)).word (sp24 h.sp) (by decide)
    · exact (hB.sub (o' := 32) (n' := 8) (by decide) (by decide)).word (sp32 h.sp) (by decide)
    · exact (hB.sub (o' := 40) (n' := 8) (by decide) (by decide)).word (sp40 h.sp) (by decide)
    · exact (hB.sub (o' := 48) (n' := 8) (by decide) (by decide)).word (sp48 h.sp) (by decide)
    · exact (hB.sub (o' := 56) (n' := 8) (by decide) (by decide)).word (sp56 h.sp) (by decide)
    · exact h64
    · exact (hC.sub (o' := 80) (n' := 8) (by decide) (by decide)).word (sp80 h.sp) (by decide)
    · exact (hC.sub (o' := 96) (n' := 8) (by decide) (by decide)).word (sp96 h.sp) (by decide)
    · exact (hC.sub (o' := 224) (n' := 8) (by decide) (by decide)).word (sp224 h.sp) (by decide)
  · rw [hd4, segK, hP, show off (stackBelow m0 2016) 232 = off (stackBelow m0 2000) 216 by
      rw [off_fr]]
    exact hker
  · rw [hk4 .r14 (by simp), hcs2 .r14 (by simp), hr14]
  · rw [hk4 .r12 (by simp), hk4 .r13 (by simp), hcs2 .r12 (by simp), hcs2 .r13 (by simp),
      hcs1 .r12 (by simp), hcs1 .r13 (by simp)]
    exact h.acc
  · rw [segK_size, hP]
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (c.point.size - P) := Nat.pow_le_pow_right (by decide) hn1

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
