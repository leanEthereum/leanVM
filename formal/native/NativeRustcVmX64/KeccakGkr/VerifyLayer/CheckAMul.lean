module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Iota2
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `verify_layer` on x86-64: ι's two terms

From `NativeRustcVmX64.Vm.VerifyLayer.label_28` (`JX`): `b38` multiplies the first segment's weight by its bits, `b39` the
second's (from the frame's `24`, `72`) by theirs (`EW::mul` twice): `mulPair`, to `b40` with the
two products in R14, RBP and RAX, RDX (`CB`). ι's state across a leaf call (`K0.leaf`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVmX64.Sumcheck (Ctx At)
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)
open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- The second segment's weight. -/
abbrev seg1 (m0 : MachineData) (c : KeccakClaimW) : EW := (segK m0 c).getD 1 0

/-- **ι's two terms**, at `b40`. -/
structure CB [Labels] (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW)
    (s1 : TState) (d : MachineData) : Prop where
  k0 : K0 m0 a c p s1 (spillsJ m0 c) d
  m1 : ewArg (reg d .r14) (reg d .rbp) =
    (segK m0 c).getD 0 0 * bitsOf c.weights (rcW (11 - stepN m0))
  m2 : ewArg (reg d .rax) (reg d .rdx) = seg1 m0 c * bitsOf c.weights (rcW (23 - stepN m0))

end

public section

variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}
  {p : Array EW} {s1 : TState}

/-- **ι's state across a leaf call**: the block before the call writes the frame below `24` only,
the callee its stack only. -/
theorem K0.leaf (hpre : VerifyLayerPre a s c m0) {L : List (Nat × UInt64)}
    (hL : ∀ q ∈ L, 24 ≤ q.1 ∧ q.1 + 8 ≤ 232) {d mc d' : MachineData} (h : K0 m0 a c p s1 L d)
    {ex : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (envB m0 d ex vars ret).WF) (hm : Match (envB m0 d ex vars ret) S mc)
    (hb1 : Body m0 (wFront m0) 16 mc) (h0 : S.mem.all (fun w ↦ w.r == 0) = true)
    (hbr : belowRet 2016 S = true) (hin : writesIn S = true) (hmiss : missB 24 1992 S = true)
    (hr : ∀ r ∈ [Reg64.r12, .r13], reg mc r = reg d r) {Sk : Nat} (hSk : 2000 + Sk ≤ 3232)
    (hsv : Saved mc d') (hrsp : rspOf d' = rspOf mc + 8#64)
    (hso : SameOutside mc.dmem d'.dmem (InRange (stackBelow mc Sk) Sk)) :
    K0 m0 a c p s1 L d' := by
  have hfr1 := frSame_blk (o := 24) (n := 1992) hwf hm hin (by decide) hmiss
  obtain ⟨hb2, hfr2, hts2⟩ := hb1.leaf hpre (wFront_outs hpre) hSk hsv hrsp hso
  have hfr := hfr1.trans (hfr2.sub (o' := 24) (n' := 1992) (by decide) (by decide))
  exact ⟨hb2, hts2 _ (ts_blk0 hpre hwf hm h0 hbr h.ts),
    (hfr.sub (o' := 472) (n' := 752) (by decide) (by decide)).ews h.prod
      (by rw [Array.length_toList, h.psize]),
    h.sp.keepIn hfr fun q hq ↦ by have := hL q hq; omega,
    (hfr.sub (o' := 232) (n' := 64) (by decide) (by decide)).ews h.seg
      (by rw [Array.length_toList]; have := segK_le4 (pre_seg hpre); omega),
    by rw [show reg d' .r12 = reg mc .r12 from hsv.1 .r12 rfl,
      show reg d' .r13 = reg mc .r13 from hsv.1 .r13 rfl, hr .r12 (by simp), hr .r13 (by simp)]; exact h.acc,
    h.psize, h.ssize⟩

omit [Labels] in
/-- An `EW::mul` result. -/
theorem mul_ret {m m' : MachineData} (h : EWMulPost m m') :
    ewArg (reg m' .rax) (reg m' .rdx) =
      ewArg (reg m .rdi) (reg m .rsi) * ewArg (reg m .rdx) (reg m .rcx) := by
  rw [h.1, h.2.1]
  exact ewArg_ew _

end

public section

variable [Host] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}
  {p : Array EW} {s1 : TState} {k : Nat}

/-- **ι's two terms**: `b38`, `EW::mul`, `b39`, `EW::mul`. -/
theorem mulPair (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hpre : VerifyLayerPre a s c m0) {d : MachineData} (h : JX m0 a c p s1 d)
    {R : MachineState → Prop}
    (cont : ∀ d', CB m0 a c p s1 d' → Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b40Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b38Offset)⟩ := by
  have g := geo_of hpre
  have hWo := wFront_outs hpre
  have hk := h.k0
  have cx := ctx hpre (F := 2000) (by decide)
  -- `b38`
  have hwf := wf0 (pre_stack hpre) hk.body (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b38Offset + b38.length)).toBitVec)
  have hm : Match (envB m0 d [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b38Offset + b38.length)).toBitVec)
      (fr 24) d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hk.body.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 16) g hk.body hwf (blk hp b38_in_code (by simp [b38])) e38 (fun _ _ ↦ rfl)
    hm (by decide +kernel) (hex0 (by decide +kernel)) fun st hm1 hpc1 hb1 _ ↦ ?_
  have hkr1 : ∀ r ∈ [Reg64.rdi, .rsi, .rdx, .rbx, .r15, .r12, .r13], reg st.data r = reg d r :=
    keepR_regs hm1 (by decide +kernel) fun _ ↦ rfl
  have hrcx : reg st.data .rcx = reg d .rax := hm1.regs .rcx _ rfl
  have hat := hb1.at_ hpre hWo (by decide)
  refine call_then hpc1 hmul (cx.stackOk hat (by decide)) fun st2 hpc2 hrsp2 hq ↦ ?_
  have hm1v := mul_ret hq
  rw [hkr1 .rdi (by simp), hkr1 .rsi (by simp), hkr1 .rdx (by simp), hrcx, h.seg, h.b1] at hm1v
  have hk2 := hk.leaf hpre (spillsJ_in c) hwf hm1 hb1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (fun r hr ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact hkr1 _ (by simp)) (Sk := ewMulStack)
    (by decide) hq.2.2.2 hrsp2 hq.2.2.1
  have hcs2 : ∀ r ∈ [Reg64.rbx, .r15], reg st2.data r = reg d r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hq.2.2.2.1 .rbx rfl).trans (hkr1 .rbx (by simp))
    · exact (hq.2.2.2.1 .r15 rfl).trans (hkr1 .r15 (by simp))
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2 hk2 hm1v hcs2
  subst hpc2
  -- `b39`
  have hwf3 := wf0 (pre_stack hpre) hk2.body (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b39Offset + b39.length)).toBitVec)
  have hm3 : Match (envB m0 d2 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b39Offset + b39.length)).toBitVec)
      (fr 24) d2 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hk2.body.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 16) g hk2.body hwf3 (blk hp b39_in_code (by simp [b39])) e39
    (fun _ _ ↦ rfl) hm3 (by decide +kernel) (hex0 (by decide +kernel)) fun st hm4 hpc4 hb4 _ ↦ ?_
  have hkr4 : ∀ r ∈ [Reg64.r12, .r13], reg st.data r = reg d2 r :=
    keepR_regs hm4 (by decide +kernel) fun _ ↦ rfl
  have h24 : NativeRustcVm.WordAt d2.dmem (off (stackBelow m0 2016) 24) (seg1 m0 c).c0 :=
    hk2.sp (24, _) (by simp [spillsJ])
  have h72 : NativeRustcVm.WordAt d2.dmem (off (stackBelow m0 2016) 72) (seg1 m0 c).c1 :=
    hk2.sp (72, _) (by simp [spillsJ])
  have hA : ewArg (reg st.data .rdi) (reg st.data .rsi) = seg1 m0 c := by
    rw [show reg st.data .rdi = _ from hm4.regs .rdi _ rfl,
      show reg st.data .rsi = _ from hm4.regs .rsi _ rfl]
    simp only [Sym.eval]
    rw [fload8 h24, fload8 h72]
    exact ewArg_ew _
  have hB : ewArg (reg st.data .rdx) (reg st.data .rcx) =
      bitsOf c.weights (rcW (23 - stepN m0)) := by
    rw [show reg st.data .rdx = _ from hm4.regs .rdx _ rfl,
      show reg st.data .rcx = _ from hm4.regs .rcx _ rfl]
    simp only [Sym.eval]
    rw [show (envB m0 d2 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b39Offset + b39.length)).toBitVec).regs .r15 =
        reg d2 .r15 from rfl,
      show (envB m0 d2 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b39Offset + b39.length)).toBitVec).regs .rbx =
        reg d2 .rbx from rfl, hcs2 .r15 (by simp), hcs2 .rbx (by simp)]
    exact h.b2
  have h14 : reg st.data .r14 = reg d2 .rax := hm4.regs .r14 _ rfl
  have hbp : reg st.data .rbp = reg d2 .rdx := hm4.regs .rbp _ rfl
  have hat4 := hb4.at_ hpre hWo (by decide)
  refine call_then hpc4 hmul (cx.stackOk hat4 (by decide)) fun st5 hpc5 hrsp5 hq5 ↦ ?_
  have hm2v := mul_ret hq5
  rw [hA, hB] at hm2v
  have hk5 := hk2.leaf hpre (spillsJ_in c) hwf3 hm4 hb4 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hkr4 (Sk := ewMulStack) (by decide) hq5.2.2.2 hrsp5
    hq5.2.2.1
  have h14' : reg st5.data .r14 = reg d2 .rax := (hq5.2.2.2.1 .r14 rfl).trans h14
  have hbp' : reg st5.data .rbp = reg d2 .rdx := (hq5.2.2.2.1 .rbp rfl).trans hbp
  obtain ⟨d5, pc5⟩ := st5
  simp only at hpc5 hk5 hm2v h14' hbp'
  subst hpc5
  exact cont d5 ⟨hk5, by rw [h14', hbp']; exact hm1v, hm2v⟩

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
