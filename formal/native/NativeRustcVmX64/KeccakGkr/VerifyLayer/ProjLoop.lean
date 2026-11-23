module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.ProjOuter
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `verify_layer` on x86-64: the product's projection

`masked`: from `NativeRustcVmX64.Vm.VerifyLayer.label_4` (`PHead j`) to `NativeRustcVmX64.Vm.VerifyLayer.label_3` with the masked sum at bit `j`
(`MQ j`). `mulStep`: `b5`, `EW::mul` of it and the product's element `j`, `b6` adds the term:
the next bit's head, or `NativeRustcVmX64.Vm.VerifyLayer.label_17` with the projection (`PEnd`). `proj`: the loop.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVmX64.Sumcheck (Ctx At)
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)
open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- **The projection done**, at `NativeRustcVmX64.Vm.VerifyLayer.label_17`. -/
structure PEnd [Labels] (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW)
    (s1 : TState) (d : MachineData) : Prop where
  body : Body m0 (wFront m0) 24 d
  ts : TStateAt d.dmem (tA m0) a s1
  prod : NativeRustcVm.EWsAt d.dmem (off (stackBelow m0 2016) 472) p.toList
  sp : FWs m0 d.dmem (spills m0 c)
  acc : ewArg (reg d .r12) (reg d .r13) = projectedOf c.mu p
  psize : p.size = 47

end

public section

theorem and_self64 (x : BitVec 64) :
    CmpOp.apply .eq .W64 (BinOp.apply .and .W64 x x) (BitVec.ofNat 64 0) = (x == 0#64) := by
  simp [CmpOp.apply, BinOp.apply]

theorem bitJ_eq (j : Nat) : BinOp.apply .shl .W64 (BitVec.ofNat 64 1)
    (UnOp.apply .trunc .W32 (BitVec.ofNat 64 j)) = bitJ j := rfl

variable [Host] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData} {k : Nat}
  {p : Array EW} {s1 : TState} {j : Nat}

theorem pstep (hpre : VerifyLayerPre a s c m0) {d : MachineData} (hc : PCore m0 a c p s1 j d) :
    Match (envB m0 d [] (fun _ ↦ 0) 0) (fr 24) d ∧ (envB m0 d [] (fun _ ↦ 0) 0).WF :=
  ⟨match_ofMachine ⟨rfl, trivial⟩ ⟨hc.body.rsp, trivial⟩ trivial trivial trivial,
    wf0 (pre_stack hpre) hc.body⟩

/-- **The masked sum at bit `j`**, from `NativeRustcVmX64.Vm.VerifyLayer.label_4` to `NativeRustcVmX64.Vm.VerifyLayer.label_3`. -/
theorem masked (hp : Placed code k) (hpre : VerifyLayerPre a s c m0) {d : MachineData}
    (h : PHead m0 a c p s1 j d) {R : MachineState → Prop}
    (cont : ∀ d', MQ m0 a c p s1 j d' → Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b5Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b7Offset)⟩ := by
  have hc := h.core
  have hlen := muSize hpre hc
  obtain ⟨hm, hwf⟩ := pstep hpre hc
  have e3 : ∀ r, (envB m0 d [] (fun _ ↦ 0) 0).regs r = reg d r := fun _ ↦ rfl
  refine hc.pure hpre hwf (blk hp b7_in_code (by simp [b7])) e7 nofun hm (by decide +kernel) rfl
    (by decide +kernel) fun st hm1 hpc1 _ hc1 ↦ ?_
  simp only [PcOk] at hpc1
  have hk1 : ∀ r ∈ [Reg64.rsi], reg st.data r = reg d r :=
    keepR_regs hm1 (by decide +kernel) fun _ ↦ rfl
  rw [show (SBool.cmp .eq .W64 (.bin .and .W64 (.reg .rsi) (.reg .rsi)) (.lit 0)).eval
      (envB m0 d [] (fun _ ↦ 0) 0) = decide (c.mu.size = 0) by
    simp only [SBool.eval, Sym.eval, e3, and_self64, h.rsi]
    by_cases h0 : c.mu.size = 0
    · simp [h0]
    · simp only [h0, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro he; have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this; exact h0 this] at hpc1
  obtain ⟨d1, pc1⟩ := st
  simp only at hpc1 hm1 hc1 hk1
  by_cases h0 : c.mu.size = 0
  · -- no instance weight: `b11`
    simp only [h0, decide_true, ↓reduceIte] at hpc1
    rw [lbl hp b11_in_code rfl] at hpc1
    subst hpc1
    obtain ⟨hm2, hwf2⟩ := pstep hpre hc1
    refine hc1.pure hpre hwf2 (blk hp b11_in_code (by simp [b11])) e11 nofun hm2
      (by decide +kernel) rfl (by decide +kernel) fun st hm3 hpc3 _ hc3 ↦ ?_
    simp only [PcOk] at hpc3
    rw [lbl hp b5_in_code rfl] at hpc3
    obtain ⟨d3, pc3⟩ := st
    simp only at hpc3 hm3 hc3
    subst hpc3
    refine cont d3 ⟨hc3, ?_⟩
    rw [show reg d3 .rdi = _ from hm3.regs .rdi _ rfl, show reg d3 .rsi = _ from hm3.regs .rsi _ rfl,
      ← masked_xs hlen, h0]
    rfl
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  subst hpc1
  -- `b8`
  obtain ⟨hm2, hwf2⟩ := pstep hpre hc1
  refine hc1.pure hpre hwf2 (blk hp b8_in_code (by simp [b8])) e8 nofun hm2
    (by decide +kernel) rfl (by decide +kernel) fun st hm3 hpc3 _ hc3 ↦ ?_
  simp only [PcOk] at hpc3
  have hrdx : reg st.data .rdx = bitJ j := by
    rw [show reg st.data .rdx = _ from hm3.regs .rdx _ rfl]
    simp only [Sym.eval]
    rw [show (envB m0 d1 [] (fun _ ↦ 0) 0).regs .r14 = reg d1 .r14 from rfl, hc1.r14]
    rfl
  rw [show (SBool.not (.cmp .eq .W64 (.reg .rsi) (.lit 1))).eval (envB m0 d1 [] (fun _ ↦ 0) 0) =
      !decide (c.mu.size = 1) by
    simp only [SBool.eval, Sym.eval, eq64]
    rw [show (envB m0 d1 [] (fun _ ↦ 0) 0).regs .rsi = reg d1 .rsi from rfl, hk1 .rsi (by simp),
      h.rsi]
    by_cases h1 : c.mu.size = 1
    · simp [h1]
    · simp only [h1, decide_false]
      congr 1
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro he; have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact h1 this] at hpc3
  obtain ⟨d3, pc3⟩ := st
  simp only at hpc3 hm3 hc3 hrdx
  by_cases h1 : c.mu.size = 1
  · -- one instance weight: `b9`
    simp only [h1, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc3
    subst hpc3
    obtain ⟨hm4, hwf4⟩ := pstep hpre hc3
    refine hc3.pure hpre hwf4 (blk hp b9_in_code (by simp [b9])) e9 nofun hm4
      (by decide +kernel) rfl (by decide +kernel) fun st hm5 hpc5 _ hc5 ↦ ?_
    simp only [PcOk] at hpc5
    rw [lbl hp b22_in_code rfl] at hpc5
    obtain ⟨d5, pc5⟩ := st
    simp only at hpc5 hm5 hc5
    subst hpc5
    refine lastW hp hpre ⟨hc5, ?_, ?_, ?_, by omega⟩ cont
    · rw [show reg d5 .rcx = _ from hm5.regs .rcx _ rfl, h1]; rfl
    · rw [show reg d5 .rdx = _ from hm5.regs .rdx _ rfl]; exact hrdx
    · rw [show reg d5 .rdi = _ from hm5.regs .rdi _ rfl, show reg d5 .rsi = _ from hm5.regs .rsi _ rfl,
        h1]
      rfl
  -- more: `b13`, the pairs, `b21`
  simp only [h1, decide_false, Bool.not_false, ↓reduceIte] at hpc3
  rw [lbl hp b13_in_code rfl] at hpc3
  subst hpc3
  obtain ⟨hm4, hwf4⟩ := pstep hpre hc3
  refine hc3.pure hpre hwf4 (blk hp b13_in_code (by simp [b13])) e13 nofun hm4
    (by decide +kernel) rfl (by decide +kernel) fun st hm5 hpc5 _ hc5 ↦ ?_
  simp only [PcOk] at hpc5
  rw [lbl hp b16_in_code rfl] at hpc5
  obtain ⟨d5, pc5⟩ := st
  simp only at hpc5 hm5 hc5
  subst hpc5
  have hin : MIn m0 a c p s1 j 0 d5 := by
    refine ⟨hc5, ?_, ?_, ?_, ?_, by omega⟩
    · rw [show reg d5 .rcx = _ from hm5.regs .rcx _ rfl]; rfl
    · rw [show reg d5 .r8 = _ from hm5.regs .r8 _ rfl]
      exact fload8 (sp64 hc3.sp)
    · rw [show reg d5 .rdx = _ from hm5.regs .rdx _ rfl]; exact hrdx
    · rw [show reg d5 .rdi = _ from hm5.regs .rdi _ rfl, show reg d5 .rsi = _ from hm5.regs .rsi _ rfl]
      rfl
  refine Eventually.bind (inner hp hpre hin) fun st ⟨hpc6, hx⟩ ↦ ?_
  obtain ⟨d6, pc6⟩ := st
  simp only at hpc6 hx
  subst hpc6
  have hc6 := hx.core
  obtain ⟨hm6, hwf6⟩ := pstep hpre hc6
  refine hc6.pure hpre hwf6 (blk hp b21_in_code (by simp [b21])) e21 nofun hm6
    (by decide +kernel) rfl (by decide +kernel) fun st hm7 hpc7 _ hc7 ↦ ?_
  simp only [PcOk] at hpc7
  have hk7 : ∀ r ∈ [Reg64.rcx, .rdx, .rdi, .rsi], reg st.data r = reg d6 r :=
    keepR_regs hm7 (by decide +kernel) fun _ ↦ rfl
  rw [show (SBool.cmp .eq .W8 (.bin .and .W8 (.load 0 32 1) (.lit 1)) (.lit 0)).eval
      (envB m0 d6 [] (fun _ ↦ 0) 0) = decide (c.mu.size % 2 = 0) by
    simp only [SBool.eval, Sym.eval]
    rw [fload1 (by omega) (sp32 hc6.sp)]
    exact test1 _ (by omega)] at hpc7
  obtain ⟨d7, pc7⟩ := st
  simp only at hpc7 hc7 hk7
  by_cases he : c.mu.size % 2 = 0
  · simp only [he, decide_true, ↓reduceIte] at hpc7
    rw [lbl hp b5_in_code rfl] at hpc7
    subst hpc7
    refine cont d7 ⟨hc7, ?_⟩
    rw [hk7 .rdi (by simp), hk7 .rsi (by simp), hx.acc, ← masked_xs hlen,
      show c.mu.size / 2 * 2 = c.mu.size by omega]
  · simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc7
    subst hpc7
    refine lastW hp hpre ⟨hc7, ?_, ?_, ?_, by omega⟩ cont
    · rw [hk7 .rcx (by simp)]; exact hx.rcx
    · rw [hk7 .rdx (by simp)]; exact hx.rdx
    · rw [hk7 .rdi (by simp), hk7 .rsi (by simp)]; exact hx.acc

omit [Host] in
theorem add16 (j : Nat) : BitVec.ofNat 64 (16 * j) + 16#64 = BitVec.ofNat 64 (16 * (j + 1)) := by
  bv_omega

/-- **A term of the projection**: `b5`, `EW::mul`, `b6`. -/
theorem mulStep (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hpre : VerifyLayerPre a s c m0) {d : MachineData} (h : MQ m0 a c p s1 j d)
    {R : MachineState → Prop}
    (hnext : ∀ d', PHead m0 a c p s1 (j + 1) d' →
      Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b7Offset)⟩)
    (hend : ∀ d', PEnd m0 a c p s1 d' → Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b24Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b5Offset)⟩ := by
  have g := geo_of hpre
  have hWo := wFront_outs hpre
  have hc := h.core
  have hwf := wf0 (pre_stack hpre) hc.body (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b5Offset + b5.length)).toBitVec)
  have hm : Match (envB m0 d [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b5Offset + b5.length)).toBitVec)
      (fr 24 [] [] [(.reg .rax, 752)]) d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hc.body.rsp, trivial⟩ trivial
      ⟨by show (reg d .rax).toNat < 752
          rw [hc.rax, BitVec.toNat_ofNat]; have := hc.lt; omega, trivial⟩ trivial
  refine Body.blk (o' := 16) g hc.body hwf (blk hp b5_in_code (by simp [b5])) e5 (fun _ _ ↦ rfl)
    hm (by decide +kernel) (hex0 (by decide +kernel)) fun st hm1 hpc1 hb1 hs1 ↦ ?_
  have e1 : ∀ r, (envB m0 d [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b5Offset + b5.length)).toBitVec).regs r =
      reg d r := fun _ ↦ rfl
  have hprodE : ewArg (reg st.data .rdx) (reg st.data .rcx) = p.getD j 0 := by
    rw [show reg st.data .rdx = _ from hm1.regs .rdx _ rfl,
      show reg st.data .rcx = _ from hm1.regs .rcx _ rfl]
    simp only [Sym.eval, e1, hc.rax]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hc.lt; omega)]
    exact prodLoad hc.prod (by rw [hc.psize]; exact hc.lt)
  have hmE : ewArg (reg st.data .rdi) (reg st.data .rsi) = maskedOf c.mu j := by
    rw [show reg st.data .rdi = _ from hm1.regs .rdi _ rfl,
      show reg st.data .rsi = _ from hm1.regs .rsi _ rfl]
    exact h.acc
  have hcs : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r15], reg st.data r = reg d r :=
    keepR_regs hm1 (by decide +kernel) fun _ ↦ rfl
  have hbp : reg st.data .rbp = BitVec.ofNat 64 (16 * (j + 1)) := by
    rw [show reg st.data .rbp = _ from hm1.regs .rbp _ rfl]
    simp only [Sym.eval, e1, hc.rax, add64]
    exact add16 j
  have h14 : reg st.data .r14 = BitVec.ofNat 64 (j + 1) := by
    rw [show reg st.data .r14 = _ from hm1.regs .r14 _ rfl]
    simp only [Sym.eval, e1, hc.r14, add64]
    bv_omega
  have hts1 := ts_blk0 hpre hwf hm1 (by decide +kernel) (by decide +kernel) hc.ts
  have hfr1 := frSame_blk (o := 24) (n := 2000) hwf hm1 (by decide +kernel) (by decide)
    (by decide +kernel)
  have cx := ctx hpre (F := 2000) (by decide)
  have hat := hb1.at_ hpre hWo (by decide)
  refine call_then hpc1 hmul (cx.stackOk hat (by decide)) fun st2 hpc2 hrsp2 hq ↦ ?_
  obtain ⟨h0, h1, hso, hsv⟩ := hq
  obtain ⟨hb2, hfr2, hts2⟩ := hb1.leaf hpre hWo (Sk := ewMulStack) (by decide) hsv hrsp2 hso
  have hfr := hfr1.trans hfr2
  have hmul2 : ewArg (reg st2.data .rax) (reg st2.data .rdx) = maskedOf c.mu j * p.getD j 0 := by
    rw [h0, h1, ← hmE, ← hprodE]
    rfl
  have hcs2 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg st2.data r = reg st.data r :=
    fun r hr ↦ hsv.1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2 hb2 hfr hts2 hmul2 hcs2
  subst hpc2
  -- `b6`
  have hwf3 := wf0 (pre_stack hpre) hb2 (vars := fun _ ↦ 0) (ret := 0)
  have hm3 : Match (envB m0 d2 [] (fun _ ↦ 0) 0) (fr 24) d2 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hb2.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 24) g hb2 hwf3 (blk hp b6_in_code (by simp [b6])) e6 nofun hm3
    (by decide +kernel) (hex0 (by decide +kernel)) fun st hm4 hpc4 hb4 hs4 ↦ ?_
  have e3 : ∀ r, (envB m0 d2 [] (fun _ ↦ 0) 0).regs r = reg d2 r := fun _ ↦ rfl
  have hd4 : st.data.dmem = d2.dmem := hm4.dmem_eq hwf3 rfl
  have hprod4 : NativeRustcVm.EWsAt st.data.dmem (off (stackBelow m0 2016) 472) p.toList := by
    rw [hd4]
    exact (hfr.sub (o' := 472) (n' := 752) (by decide) (by decide)).ews hc.prod
      (by rw [Array.length_toList, hc.psize])
  have hsp2 : FWs m0 d2.dmem (spills m0 c) :=
    hc.sp.keepIn hfr fun q hq ↦ by have := spills_in c q hq; omega
  have hsp4 : FWs m0 st.data.dmem (spills m0 c) := by rw [hd4]; exact hsp2
  have hts4 : TStateAt st.data.dmem (tA m0) a s1 := by rw [hd4]; exact hts2 _ hts1
  have hacc4 : ewArg (reg st.data .r12) (reg st.data .r13) = xs (projTerm c.mu p) (j + 1) := by
    rw [show reg st.data .r12 = _ from hm4.regs .r12 _ rfl,
      show reg st.data .r13 = _ from hm4.regs .r13 _ rfl]
    simp only [Sym.eval, e3, NativeRustcVmX64.Arrays.xor_eval]
    rw [NativeRustcVmX64.Arrays.ewArg_xor, hcs2 .r12 (by simp), hcs2 .r13 (by simp),
      hcs .r12 (by simp), hcs .r13 (by simp), hc.acc, hmul2, xs_succ]
    rfl
  simp only [PcOk] at hpc4
  rw [show (SBool.cmp .eq .W64 (.reg .rbp) (.lit 752)).eval (envB m0 d2 [] (fun _ ↦ 0) 0) =
      decide (j + 1 = 47) by
    simp only [SBool.eval, Sym.eval, e3, eq64]
    rw [hcs2 .rbp (by simp), hbp]
    have := hc.lt
    by_cases he : j + 1 = 47
    · simp [he]
    · simp only [he, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro he'; have := congrArg BitVec.toNat he'
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      omega] at hpc4
  obtain ⟨d4, pc4⟩ := st
  simp only at hpc4 hb4 hprod4 hsp4 hts4 hacc4
  by_cases he : j + 1 = 47
  · simp only [he, decide_true, ↓reduceIte] at hpc4
    rw [lbl hp b24_in_code rfl] at hpc4
    subst hpc4
    refine hend d4 ⟨hb4, hts4, hprod4, hsp4, ?_, hc.psize⟩
    rw [hacc4, he, projected_eq]
  · simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc4
    subst hpc4
    refine hnext d4 ⟨⟨hb4, hts4, hprod4, hsp4, ?_, ?_, ?_, ?_, hacc4, by have := hc.lt; omega,
      hc.psize⟩, ?_⟩
    · rw [show reg d4 .rax = _ from hm4.regs .rax _ rfl]
      simp only [Sym.eval, e3]
      rw [hcs2 .rbp (by simp), hbp]
    · rw [show reg d4 .r14 = _ from hm4.regs .r14 _ rfl]
      simp only [Sym.eval, e3]
      rw [hcs2 .r14 (by simp), h14]
    · rw [show reg d4 .rbx = _ from hm4.regs .rbx _ rfl]
      simp only [Sym.eval, e3]
      rw [hcs2 .rbx (by simp), hcs .rbx (by simp), hc.rbx]
    · rw [show reg d4 .r15 = _ from hm4.regs .r15 _ rfl]
      simp only [Sym.eval, e3]
      rw [hcs2 .r15 (by simp), hcs .r15 (by simp), hc.r15]
    · rw [show reg d4 .rsi = _ from hm4.regs .rsi _ rfl]
      simp only [Sym.eval]
      rw [fload8 (sp32 hsp2)]
      rfl

/-- **The product's projection**, from `NativeRustcVmX64.Vm.VerifyLayer.label_4` to `NativeRustcVmX64.Vm.VerifyLayer.label_17`. -/
theorem proj (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hpre : VerifyLayerPre a s c m0) {d : MachineData} (h : PHead m0 a c p s1 0 d) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b24Offset) ∧ PEnd m0 a c p s1 st.data)
      ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b7Offset)⟩ := by
  refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b7Offset) ∧ ∃ j, 47 - j = n ∧
    PHead m0 a c p s1 j st.data) (fun n st ⟨hpc, j, hn, hj⟩ ↦ ?_) ⟨rfl, 0, rfl, h⟩
  obtain ⟨d', pc⟩ := st
  simp only at hpc hj
  subst hpc
  exact masked hp hpre hj fun d1 hq ↦ mulStep hp hmul hpre hq
    (fun d2 hh ↦ .done _ (.inr ⟨_, by have := hj.core.lt; have := hh.core.lt; omega,
      rfl, j + 1, rfl, hh⟩)) fun d2 he ↦ .done _ (.inl ⟨rfl, he⟩)

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
