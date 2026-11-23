module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.CheckAMul
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.SumE.Names

/-!
# `verify_layer` on x86-64: the first check

From `b40` (`CB`, ι's two terms): `b40` adds them and calls `sum_e` on the instance weights, `b41`
multiplies, `b42` and `b43` compare the projection plus the product with the claim's value, limb
by limb (`checkA`): on a mismatch `NativeRustcVmX64.Vm.VerifyLayer.label_50` with BL cleared (`exit50`, the layer's run
`None`), else `b44` (code index `370`) with ι's state: `checkARun`.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVmX64.Sumcheck (Ctx At)
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)
open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- ι times the instance weights' sum in RAX, RDX, at `b42`. -/
structure CC [Labels] (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW)
    (s1 : TState) (d : MachineData) : Prop where
  k0 : K0 m0 a c p s1 (spillsJ m0 c) d
  prod : ewArg (reg d .rax) (reg d .rdx) = iotaOf (reg m0 .rsi).toNat (stepN m0) c * sumE c.mu

end

public section

theorem ofBitVec_beq (a : BitVec 64) (b : UInt64) : (UInt64.ofBitVec a == b) = (a == b.toBitVec) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨fun h ↦ by subst h; rfl, fun h ↦ by subst h; rfl⟩

theorem ew_beq' (x y : EW) : (x == y) = (x.c0 == y.c0 && x.c1 == y.c1) := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  rfl

theorem ew_ext' {x y : EW} (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) : x = y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only at h0 h1
  rw [h0, h1]

/-- The layer's run with a failed first check. -/
theorem rest1_false {logSteps step : Nat} {c : KeccakClaimW} {p : Array EW} {s1 : TState}
    (h : checkA logSteps step c p = false) : rest1 logSteps step c p s1 = none := by
  unfold rest1
  rw [h]
  rfl

/-- The layer's run with a passed first check. -/
theorem rest1_true {logSteps step : Nat} {c : KeccakClaimW} {p : Array EW} {s1 : TState}
    (h : checkA logSteps step c p = true) : rest1 logSteps step c p s1 =
      ((grind (grindingBits (productBits - 1))).run s1).bind fun q ↦ rest2 c p q.2 := by
  unfold rest1
  rw [h]
  rfl

variable [Host] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData} {k : Nat}
  {p : Array EW} {s1 : TState}

/-- **ι times the instance weights' sum**: `b40`, `sum_e`, `b41`, `EW::mul`, to `b42`. -/
theorem iotaMu (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hsum : Spec (Labels.label NativeRustcVmX64.Vm.SumE.entryLabel) SumEPre SumEPost)
    (hpre : VerifyLayerPre a s c m0) {d : MachineData} (h : CB m0 a c p s1 d)
    {R : MachineState → Prop}
    (cont : ∀ d', CC m0 a c p s1 d' → Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b42Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b40Offset)⟩ := by
  have g := geo_of hpre
  have hWo := wFront_outs hpre
  have hk := h.k0
  have cx := ctx hpre (F := 2000) (by decide)
  have hspJ : ∀ (o : Nat) (w : UInt64), (o, w) ∈ spillsI m0 c → ∀ {dd : DataMem},
      FWs m0 dd (spillsJ m0 c) → NativeRustcVm.WordAt dd (off (stackBelow m0 2016) o) w :=
    fun o w hq _ hf ↦ hf (o, w) (List.mem_append_left _ hq)
  -- `b40`: ι, `sum_e`'s arguments
  have hwf := wf0 (pre_stack hpre) hk.body (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b40Offset + b40.length)).toBitVec)
  have hm : Match (envB m0 d [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b40Offset + b40.length)).toBitVec)
      (fr 24) d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hk.body.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 16) g hk.body hwf (blk hp b40_in_code (by simp [b40])) e40 (fun _ _ ↦ rfl)
    hm (by decide +kernel) (hex0 (by decide +kernel)) fun st hm1 hpc1 hb1 _ ↦ ?_
  have e1 : ∀ r, (envB m0 d [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b40Offset + b40.length)).toBitVec).regs r =
      reg d r := fun _ ↦ rfl
  have hiota : ewArg (reg st.data .r14) (reg st.data .rbp) =
      iotaOf (reg m0 .rsi).toNat (stepN m0) c := by
    rw [show reg st.data .r14 = _ from hm1.regs .r14 _ rfl,
      show reg st.data .rbp = _ from hm1.regs .rbp _ rfl]
    simp only [Sym.eval, e1, NativeRustcVmX64.Arrays.xor_eval]
    rw [NativeRustcVmX64.Arrays.ewArg_xor, h.m1, h.m2, iota_eq]
    rfl
  have hkr1 : ∀ r ∈ [Reg64.r12, .r13], reg st.data r = reg d r :=
    keepR_regs hm1 (by decide +kernel) fun _ ↦ rfl
  obtain ⟨hlen, hlw, hmus⟩ := (hb1.claim hpre fun _ h ↦ h).2.1
  have hmusz : c.mu.size ≤ 16 := by
    have : c.mu.toList.length ≤ 16 := hlen
    simpa using this
  have hmus' : NativeRustcVm.EWsAt st.data.dmem (cA m0 + 24#64) c.mu.toList := by
    have e : NativeRustcVm.KeccakGkr.off (cA m0) NativeRustcVm.KeccakGkr.muOff + 8#64 =
        cA m0 + 24#64 := by
      unfold NativeRustcVm.KeccakGkr.off NativeRustcVm.KeccakGkr.muOff; bv_omega
    rw [← e]; exact hmus
  have hrdi : reg st.data .rdi = cA m0 + 24#64 := by
    rw [show reg st.data .rdi = _ from hm1.regs .rdi _ rfl]
    have h48 : NativeRustcVm.WordAt d.dmem (off (stackBelow m0 2016) 48) (.ofBitVec (cA m0 + 24#64)) :=
      hspJ _ _ (by simp [spillsI, spills3]) hk.sp
    exact fload8 h48
  have hrsi : reg st.data .rsi = BitVec.ofNat 64 c.mu.size := by
    rw [show reg st.data .rsi = _ from hm1.regs .rsi _ rfl]
    have h32 : NativeRustcVm.WordAt d.dmem (off (stackBelow m0 2016) 32) c.mu.size.toUInt64 :=
      hspJ _ _ (by simp [spillsI, spills3]) hk.sp
    exact fload8 h32
  have hrsiN : (reg st.data .rsi).toNat = c.mu.size := by
    rw [hrsi, BitVec.toNat_ofNat]; omega
  have hat := hb1.at_ hpre hWo (by decide)
  have hsl := claimSlice hpre hWo hb1 (Sk := sumEStack) (by decide) (o := 24) (n := 16 * c.mu.size)
    (by decide) (by omega)
  refine call_then hpc1 hsum ⟨cx.stackOk hat (by decide), by rw [hrsiN]; exact hmusz,
    by rw [hrdi, hrsiN]; exact ⟨hsl.1, hsl.2.1⟩⟩ fun st2 hpc2 hrsp2 hq ↦ ?_
  obtain ⟨hret, hch, hsv⟩ := hq
  have hsumv : ewArg (reg st2.data .rax) (reg st2.data .rdx) = sumE c.mu := by
    rw [NativeRustcVmX64.Arrays.ewRet_eq, hret]
    congr 1
    unfold slice
    rw [hrdi, hrsiN]
    have := NativeRustcVm.ewsOf_of_ewsAt hmus'
    rw [Array.length_toList] at this
    rw [this]
  have hk2 := hk.leaf hpre (spillsJ_in c) hwf hm1 hb1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hkr1 (Sk := sumEStack) (by decide) hsv hrsp2
    (NativeRustcVm.SameOutside.mono hch fun q hq ↦ hq.elim (fun h ↦ absurd h (Nat.not_lt_zero _)) id)
  have hiota2 : ewArg (reg st2.data .r14) (reg st2.data .rbp) =
      iotaOf (reg m0 .rsi).toNat (stepN m0) c := by
    rw [show reg st2.data .r14 = reg st.data .r14 from hsv.1 .r14 rfl,
      show reg st2.data .rbp = reg st.data .rbp from hsv.1 .rbp rfl]
    exact hiota
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2 hk2 hsumv hiota2
  subst hpc2
  -- `b41`: the product
  have hwf3 := wf0 (pre_stack hpre) hk2.body (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b41Offset + b41.length)).toBitVec)
  have hm3 : Match (envB m0 d2 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b41Offset + b41.length)).toBitVec)
      (fr 24) d2 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hk2.body.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 16) g hk2.body hwf3 (blk hp b41_in_code (by simp [b41])) e41
    (fun _ _ ↦ rfl) hm3 (by decide +kernel) (hex0 (by decide +kernel)) fun st hm4 hpc4 hb4 _ ↦ ?_
  have hkr4 : ∀ r ∈ [Reg64.r12, .r13], reg st.data r = reg d2 r :=
    keepR_regs hm4 (by decide +kernel) fun _ ↦ rfl
  have hA : ewArg (reg st.data .rdi) (reg st.data .rsi) = iotaOf (reg m0 .rsi).toNat (stepN m0) c := by
    rw [show reg st.data .rdi = _ from hm4.regs .rdi _ rfl,
      show reg st.data .rsi = _ from hm4.regs .rsi _ rfl]
    exact hiota2
  have hB : ewArg (reg st.data .rdx) (reg st.data .rcx) = sumE c.mu := by
    rw [show reg st.data .rdx = _ from hm4.regs .rdx _ rfl,
      show reg st.data .rcx = _ from hm4.regs .rcx _ rfl]
    exact hsumv
  have hat4 := hb4.at_ hpre hWo (by decide)
  refine call_then hpc4 hmul (cx.stackOk hat4 (by decide)) fun st5 hpc5 hrsp5 hq5 ↦ ?_
  have hprod := mul_ret hq5
  rw [hA, hB] at hprod
  have hk5 := hk2.leaf hpre (spillsJ_in c) hwf3 hm4 hb4 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hkr4 (Sk := ewMulStack) (by decide) hq5.2.2.2 hrsp5
    hq5.2.2.1
  obtain ⟨d5, pc5⟩ := st5
  simp only at hpc5 hk5 hprod
  subst hpc5
  exact cont d5 ⟨hk5, hprod⟩

/-- **The first check**: `b42`, `b43`; on a mismatch the exit. -/
theorem checkARun (hp : Placed code k) (hpre : VerifyLayerPre a s c m0) {d5 : MachineData}
    (h : CC m0 a c p s1 d5)
    (hrun : runL s c m0 = rest1 (reg m0 .rsi).toNat (stepN m0) c p s1)
    (cont : ∀ d', K0 m0 a c p s1 (spillsJ m0 c) d' →
      checkA (reg m0 .rsi).toNat (stepN m0) c p = true →
      Eventually (step1 Host.exe) (Goal a s c m0) ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b44Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s c m0) ⟨d5, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b42Offset)⟩ := by
  have g := geo_of hpre
  have hWo := wFront_outs hpre
  have hk5 := h.k0
  have hprod := h.prod
  have hspJ : ∀ (o : Nat) (w : UInt64), (o, w) ∈ spillsI m0 c → ∀ {dd : DataMem},
      FWs m0 dd (spillsJ m0 c) → NativeRustcVm.WordAt dd (off (stackBelow m0 2016) o) w :=
    fun o w hq _ hf ↦ hf (o, w) (List.mem_append_left _ hq)
  -- `b42`, `b43`: the comparison
  have hX : ewArg (reg d5 .rax ^^^ reg d5 .r12) (reg d5 .rdx ^^^ reg d5 .r13) =
      projectedOf c.mu p + iotaOf (reg m0 .rsi).toNat (stepN m0) c * sumE c.mu := by
    rw [NativeRustcVmX64.Arrays.ewArg_xor, hprod, hk5.acc, ew_add_comm']
  have hcA : checkA (reg m0 .rsi).toNat (stepN m0) c p =
      ((UInt64.ofBitVec (reg d5 .rax ^^^ reg d5 .r12) == c.value.c0) &&
        (UInt64.ofBitVec (reg d5 .rdx ^^^ reg d5 .r13) == c.value.c1)) := by
    unfold checkA
    rw [← hX, ew_beq']
    rfl
  obtain ⟨hval, -, -⟩ := hk5.body.claim hpre fun _ h ↦ h
  rw [NativeRustcVm.ewAt_iff] at hval
  have h96 : NativeRustcVm.WordAt d5.dmem (off (stackBelow m0 2016) 96) (.ofBitVec (cA m0)) :=
    hspJ _ _ (by simp [spillsI, spills3]) hk5.sp
  have hwf6 := wfC hpre hk5.body (vars := fun _ ↦ 0) (ret := 0)
  have hm6 : Match (envB m0 d5 [(cA m0, 768)] (fun _ ↦ 0) 0) (claimS (.load 0 96 8)) d5 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hk5.body.rsp, trivial⟩ trivial trivial
      ⟨by show Env.load _ 0 96 8 = cA m0 + BitVec.ofInt 64 0
          rw [fload8 h96]; simp, trivial⟩
  have hv0 : (envB m0 d5 [(cA m0, 768)] (fun _ ↦ 0) 0).load 1 0 8 = c.value.c0.toBitVec :=
    load_of_wordAt (show NativeRustcVm.WordAt d5.dmem (cA m0 + BitVec.ofNat 64 0) c.value.c0 by
      rw [BitVec.add_zero]; exact hval.1)
  refine Body.blk (o' := 24) g hk5.body hwf6 (blk hp b42_in_code (by simp [b42])) e42 nofun hm6
    (by decide +kernel) (hex0 (by decide +kernel)) fun st hm7 hpc7 hb7 _ ↦ ?_
  have e6 : ∀ r, (envB m0 d5 [(cA m0, 768)] (fun _ ↦ 0) 0).regs r = reg d5 r := fun _ ↦ rfl
  have hk7 := hk5.blk hpre (spillsJ_in c) hwf6 hm7 hb7 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (keepR_regs hm7 (by decide +kernel) fun _ ↦ rfl)
  have hkr7 : ∀ r ∈ [Reg64.rdx, .r13], reg st.data r = reg d5 r :=
    keepR_regs hm7 (by decide +kernel) fun _ ↦ rfl
  have hrbx7 : reg st.data .rbx = 0#64 := hm7.regs .rbx _ rfl
  have hrcx7 : reg st.data .rcx = cA m0 := by
    rw [show reg st.data .rcx = _ from hm7.regs .rcx _ rfl]
    exact fload8 h96
  simp only [PcOk] at hpc7
  rw [show (SBool.not (SBool.cmp .eq .W64 (.bin .xor .W64 (.reg .rax) (.reg .r12)) (.load 1 0 8))).eval
      (envB m0 d5 [(cA m0, 768)] (fun _ ↦ 0) 0) =
      !(UInt64.ofBitVec (reg d5 .rax ^^^ reg d5 .r12) == c.value.c0) by
    simp only [SBool.eval, Sym.eval, e6, eq64, NativeRustcVmX64.Arrays.xor_eval]
    rw [hv0, ofBitVec_beq]] at hpc7
  have hfail : ∀ dd : MachineData, Body m0 (wFront m0) 24 dd → reg dd .rbx = 0#64 →
      checkA (reg m0 .rsi).toNat (stepN m0) c p = false →
      Eventually (step1 Host.exe) (Goal a s c m0) ⟨dd, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b87Offset)⟩ :=
    fun dd hbd hrb hc ↦ by
      have hnone : runL s c m0 = none := by rw [hrun]; exact rest1_false hc
      exact exit50 hp hpre hWo hbd (by rw [hrb, hnone]; rfl)
        (fun c' s' hh ↦ by rw [hnone] at hh; cases hh)
  obtain ⟨d7, pc7⟩ := st
  simp only at hpc7 hb7 hk7 hkr7 hrbx7 hrcx7
  cases hb0 : (UInt64.ofBitVec (reg d5 .rax ^^^ reg d5 .r12) == c.value.c0) with
  | false =>
    simp only [hb0, Bool.not_false, ↓reduceIte] at hpc7
    rw [lbl hp b87_in_code rfl] at hpc7
    subst hpc7
    exact hfail d7 hb7 hrbx7 (by rw [hcA, hb0]; rfl)
  | true =>
    simp only [hb0, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc7
    subst hpc7
    have hwf8 := wfC hpre hb7 (vars := fun _ ↦ 0) (ret := 0)
    have hm8 : Match (envB m0 d7 [(cA m0, 768)] (fun _ ↦ 0) 0) (claimS (.reg .rcx)) d7 :=
      match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb7.rsp, trivial⟩ trivial trivial
        ⟨by show reg d7 .rcx = cA m0 + BitVec.ofInt 64 0
            rw [hrcx7]; simp, trivial⟩
    have hval7 := (hk7.body.claim hpre fun _ h ↦ h).1
    rw [NativeRustcVm.ewAt_iff] at hval7
    have hv1 : (envB m0 d7 [(cA m0, 768)] (fun _ ↦ 0) 0).load 1 8 8 = c.value.c1.toBitVec :=
      cload hval7.2
    refine Body.blk (o' := 24) g hb7 hwf8 (blk hp b43_in_code (by simp [b43])) e43 nofun hm8
      (by decide +kernel) (hex0 (by decide +kernel)) fun st hm9 hpc9 hb9 _ ↦ ?_
    have e8 : ∀ r, (envB m0 d7 [(cA m0, 768)] (fun _ ↦ 0) 0).regs r = reg d7 r := fun _ ↦ rfl
    have hk9 := hk7.blk hpre (spillsJ_in c) hwf8 hm9 hb9 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (keepR_regs hm9 (by decide +kernel) fun _ ↦ rfl)
    have hrbx9 : reg st.data .rbx = 0#64 := (hm9.regs .rbx _ rfl).trans hrbx7
    simp only [PcOk] at hpc9
    rw [show (SBool.not (SBool.cmp .eq .W64 (.bin .xor .W64 (.reg .rdx) (.reg .r13))
        (.load 1 8 8))).eval (envB m0 d7 [(cA m0, 768)] (fun _ ↦ 0) 0) =
        !(UInt64.ofBitVec (reg d5 .rdx ^^^ reg d5 .r13) == c.value.c1) by
      simp only [SBool.eval, Sym.eval, e8, eq64, NativeRustcVmX64.Arrays.xor_eval]
      rw [hv1, hkr7 .rdx (by simp), hkr7 .r13 (by simp), ofBitVec_beq]] at hpc9
    obtain ⟨d9, pc9⟩ := st
    simp only at hpc9 hb9 hk9 hrbx9
    cases hb1' : (UInt64.ofBitVec (reg d5 .rdx ^^^ reg d5 .r13) == c.value.c1) with
    | false =>
      simp only [hb1', Bool.not_false, ↓reduceIte] at hpc9
      rw [lbl hp b87_in_code rfl] at hpc9
      subst hpc9
      exact hfail d9 hb9 hrbx9 (by rw [hcA, hb0, hb1']; rfl)
    | true =>
      simp only [hb1', Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc9
      subst hpc9
      exact cont d9 hk9 (by rw [hcA, hb0, hb1']; rfl)

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
