module

public import NativeRustcVmX64.Whir.BasisWEval.Ring
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `BasisW::eval`: the first product (x86-64)

After `ring_claim_weight` (`A5`, `Some` at the frame's `80`): `b5` drops the argument words and
falls into `b6`, which sets RBP to the scales' end and multiplies the first scale by the weight;
`b7` keeps the product (the frame's `24`, `64`) and the `BasisW`'s address (`56`) and reads the
column claims' count: none, `End` at `b21`; else `b8` keeps the placements' address (`104`) and
sets R12 16 bytes into the first claim, `Mid 0 0` at `b11` (`first`).
-/

namespace NativeRustcVmX64.Whir.BasisWEval

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model LeanVM.Parameters
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVm.Layout NativeRustcVm.Ring
open NativeRustcVmX64.Vm.BasisWEval
open NativeRustcVm.Transcript (off off_add off_zero toNat_off OptEWAt)
open LeanVM.Protocol.Verifier (qkeccak Placement)

public section

/-- `shlq $4, %r15; addq %r15, %rbp`: the scales' end. -/
theorem rbp6_eval [Labels] {env : Env} {c : Nat} {s : BitVec 64}
    (h15 : env.regs .r15 = c.toUInt64.toBitVec) (hbp : env.regs .rbp = s) (hc : c < 2 ^ 64) :
    (Sym.bin .add .W64 (.bin .shl .W64 (.reg .r15) (.lit 4)) (.reg .rbp)).eval env =
      off s (16 * c) := by
  have e := NativeRustcVmX64.Arrays.eval_shl_lit (env := env) (.reg .r15) (j := 4) (by decide)
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64] at e ⊢
  rw [e, h15, hbp]
  apply BitVec.eq_of_toNat_eq
  simp only [off, BitVec.toNat_add, BitVec.toNat_shiftLeft, toNat_bv_toUInt64 hc,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, show Width.W64.bits = 64 from rfl]
  omega

variable {m0 : MachineData} {ba : BasisAddrs} {b : BasisW} {v : Vals} [Host] {k : Nat}

/-- **The first product**, from `b5` to `Mid 0 0` at `b11` or `End` at `b21`. -/
theorem first (hp : Placed code k) (h : In m0 ba b v)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b5Offset)) (ha : A5 m0 ba b v st.data)
    {R : MachineState → Prop}
    (hloop : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b11Offset) → Mid m0 ba b v 0 0 st'.data →
      Eventually (step1 Host.exe) R st')
    (hend : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b21Offset) → End m0 ba b v st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hS := h.stackOk
  have hN := h.hN
  have hf := ha.base.fr
  obtain ⟨t80, t88, t96⟩ := optSome ha.out
  -- b5
  obtain ⟨hmid5, hmem5, hk5⟩ := ok_b5
  have hwf5 := h.wf0 hf (ret := 0)
  refine at_pc hpc (h.block hf hwf5 (inf hp b5_in_code (by simp [b5])) exit_b5 nofun
    (match_body hf ⟨rfl, trivial⟩) hmid5 (h0_of_nil hmem5) fun st1 hm1 hpc1 hf1 ↦ ?_)
  simp only [PcOk, tag_false t80, Bool.false_eq_true, ↓reduceIte] at hpc1
  rw [show k + NativeRustcVmX64.Vm.BasisWEval.b5Offset + b5.length = k + NativeRustcVmX64.Vm.BasisWEval.b6Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.BasisWEval.b5_next]] at hpc1
  have base1 := ha.base.nil hf1 hwf5 hm1 hmem5
  have k1 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg st1.data r = reg st.data r :=
    fun r hr ↦ keeps_reg hm1 hk5 hr
  have u24 := ha.w24.nil hwf5 hm1 hmem5
  have u88 := t88.nil hwf5 hm1 hmem5
  have u96 := t96.nil hwf5 hm1 hmem5
  -- b6
  obtain ⟨hmid6, h06, hmiss6, hrcx, hrdx, hrsi, hrdi, hrbp, hk6⟩ := ok_b6
  let ret6 := (Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b6Offset + b6.length)).toBitVec
  have hwf6 := h.wf0 hf1 (ret := ret6)
  refine at_pc hpc1 (h.block hf1 hwf6 (inf hp b6_in_code (by simp [b6])) exit_b6
    (fun _ _ ↦ rfl) (match_body hf1 ⟨rfl, trivial⟩) hmid6 h06 fun st2 hm2 hpc2 hf2 ↦ ?_)
  have hw6 := missWs_spec hmiss6
  have base2 := base1.block hf2 hwf6 hm2 hmid6 (by
    simp only [missWs, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨hw6 32 (by simp), hw6 40 (by simp), hw6 48 (by simp), hw6 72 (by simp)⟩)
  have e0 : reg st2.data .rdi = (sAt b.scales 0).c0.toBitVec :=
    (reg_eval hm2 hrdi).trans ((k1 .r14 (by simp)).trans ha.r14)
  have e1 : reg st2.data .rsi = (sAt b.scales 0).c1.toBitVec := (reg_eval hm2 hrsi).trans u24.load
  have e2 : reg st2.data .rdx = (ringW v (xpt m0)).c0.toBitVec := (reg_eval hm2 hrdx).trans u88.load
  have e3 : reg st2.data .rcx = (ringW v (xpt m0)).c1.toBitVec := (reg_eval hm2 hrcx).trans u96.load
  have ebp : reg st2.data .rbp = sA ba ba.count :=
    (reg_eval hm2 hrbp).trans (rbp6_eval ((k1 .r15 (by simp)).trans ha.r15)
      ((k1 .rbp (by simp)).trans ha.rbp) (count_lt h))
  have k2 : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14], reg st2.data r = reg st1.data r :=
    fun r hr ↦ keeps_reg hm2 hk6 hr
  have hle : 160 - 16 + ewMulStack ≤ basisWEvalStack := by have := stack_le.1; omega
  obtain ⟨hpcc, hretc⟩ := hpc2
  refine Fr.call (c := 16) (Nc := ewMulStack) (lo := 24) (len := 0) (X := fun _ ↦ False)
    hS N_ge (by omega) hle slots_c16 (by omega) (fun _ h ↦ h.elim) (fun _ h ↦ h.elim) hmul hf2
    ⟨hpcc, hretc⟩ (h.stackOk_at hf2 (by omega) hle)
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun _ h ↦ .inl h, hq.2.2.2⟩)
    fun m3 hf3 hq3 hk3 hcs3 ↦ ?_
  obtain ⟨hy0, hy1, -, -⟩ := hq3
  rw [e0, e1, e2, e3] at hy0 hy1
  have base3 : Base m0 ba 24 m3 := base2.call hf3 hk3 (by omega) (.inr (by omega))
  have rbx3 : reg m3 .rbx = reg m0 .rsi :=
    (hcs3 .rbx rfl).trans ((k2 .rbx (by simp)).trans ((k1 .rbx (by simp)).trans ha.rbx))
  have rbp3 : reg m3 .rbp = sA ba ba.count := (hcs3 .rbp rfl).trans ebp
  have r133 : reg m3 .r13 = sA ba (min 1 ba.count) :=
    (hcs3 .r13 rfl).trans ((k2 .r13 (by simp)).trans ((k1 .r13 (by simp)).trans ha.r13))
  -- b7
  rw [show k + NativeRustcVmX64.Vm.BasisWEval.b6Offset + b6.length = k + NativeRustcVmX64.Vm.BasisWEval.b7Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.BasisWEval.b6_next]]
  have hcin := h.claimsIn
  have hc8 : WhirIn m0 ba.claims 8 basisWEvalStack := WhirIn.mono' hcin (by decide)
  have hbc : NativeRustcVm.Apart (reg m0 .rsi) 56 ba.claims 8 :=
    NativeRustcVm.Apart.mono h.aparts.2.1 (Nat.le_refl _) (by unfold basisBytes; omega)
      (Nat.le_refl _) (by unfold claimsBytes; omega)
  have hwf7 : (envB m0 m3 [(reg m0 .rsi, 56), (ba.claims, 8)] 0).WF :=
    h.wf2 hf3.frame.kept h.basis hc8 hbc
  have hcl := h.claimsAt hf3
  have hle7 : v.cs.size ≤ 160 := hcl.len_le
  have l40 : (envB m0 m3 [(reg m0 .rsi, 56), (ba.claims, 8)] 0).load 1 40 8 = ba.claims :=
    load_ofMachine (r := 1) rfl (h.word hf3 5 (by decide))
  have l20 : (envB m0 m3 [(reg m0 .rsi, 56), (ba.claims, 8)] 0).load 2 0 8 =
      v.cs.size.toUInt64.toBitVec :=
    load_ofMachine (r := 2) (o := 0) rfl (by rw [off_zero]; exact hcl.len)
  have hm7 : Match (envB m0 m3 [(reg m0 .rsi, 56), (ba.claims, 8)] 0) claimsS m3 :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hf3.frame.rsp_eval, known_ptr rfl rbx3, trivial⟩
      trivial trivial ⟨l40.trans (eval_ptr (i := 2) rfl).symm, trivial⟩
  obtain ⟨hmid7, h07, w64, w56, w24, hmiss7, hrbx7, hr127, hk7⟩ := ok_b7
  refine h.block hf3 hwf7 (inf hp b7_in_code (by simp [b7])) exit_b7 nofun hm7 hmid7 h07
    fun st4 hm4 hpc4 hf4 ↦ ?_
  simp only [PcOk, c7_eval l20 hle7] at hpc4
  have base4 := base3.block hf4 hwf7 hm4 hmid7 hmiss7
  have hW0 : dot b.scales (ws v (xpt m0) 0) = EW.mul (sAt b.scales 0) (ringW v (xpt m0)) := by
    rw [ws_zero, dot_single]
  have acc4 : Acc m0 ba b (ws v (xpt m0) 0) st4.data := {
    w24 := FW.wrote hm4 (by omega) w24 (by rw [hW0]; exact hy0)
    w64 := FW.wrote hm4 (by omega) w64 (by rw [hW0]; exact hy1)
    r13 := (keeps_reg hm4 hk7 (by simp)).trans (by rw [ws_zero]; exact r133)
    rbp := (keeps_reg hm4 hk7 (by simp)).trans rbp3 }
  have f56 : FW m0 st4.data 56 (reg m0 .rsi) := FW.wrote hm4 (by omega) w56 (eval_ptr rfl)
  by_cases hc0 : v.cs.size = 0
  · simp only [hc0, decide_true, ↓reduceIte] at hpc4
    rw [hp.label NativeRustcVmX64.Vm.BasisWEval.label_10_at] at hpc4
    exact hend st4 hpc4 ⟨base4, f56, by rw [hc0]; exact acc4⟩
  · simp only [hc0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc4
    rw [show k + NativeRustcVmX64.Vm.BasisWEval.b7Offset + b7.length = k + NativeRustcVmX64.Vm.BasisWEval.b8Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.BasisWEval.b7_next]] at hpc4
    -- b8
    obtain ⟨hmid8, h08, w104, hmiss8, hrcx8, hr128, hk8⟩ := ok_b8
    have hwf8 := h.wf0 hf4 (ret := 0)
    refine at_pc hpc4 (h.block hf4 hwf8 (inf hp b8_in_code (by simp [b8])) exit_b8 nofun
      (match_body hf4 ⟨rfl, trivial⟩) hmid8 h08 fun st5 hm5 hpc5 hf5 ↦ ?_)
    simp only [PcOk] at hpc5
    rw [hp.label NativeRustcVmX64.Vm.BasisWEval.label_6_at] at hpc5
    have hw8 := missWs_spec hmiss8
    have l72 : (envB m0 st4.data [] 0).load 0 72 8 = ba.layout := base4.w72.load
    have k5 : ∀ r ∈ [Reg64.rbx, .rbp, .r13], reg st5.data r = reg st4.data r :=
      fun r hr ↦ keeps_reg hm5 hk8 hr
    have hrbx4 : (reg st4.data .rbx).toNat = 608 * v.cs.size :=
      (congrArg BitVec.toNat (reg_eval hm4 hrbx7)).trans (rbx7_eval l20 hle7)
    have hr124 : reg st4.data .r12 = off ba.claims 8 :=
      (reg_eval hm4 hr127).trans (r127_eval l20 l40 hle7)
    refine hloop st5 hpc5 {
      base := base4.block hf5 hwf8 hm5 hmid8 (by
        simp only [missWs, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
        exact ⟨hw8 32 (by simp), hw8 40 (by simp), hw8 48 (by simp), hw8 72 (by simp)⟩)
      w56 := f56.block hwf8 hm5 hmid8 (by omega) (hw8 56 (by simp))
      w104 := FW.wrote hm5 (by omega) w104 (by
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, l72])
      acc := {
        w24 := acc4.w24.block hwf8 hm5 hmid8 (by omega) (hw8 24 (by simp))
        w64 := acc4.w64.block hwf8 hm5 hmid8 (by omega) (hw8 64 (by simp))
        r13 := (k5 .r13 (by simp)).trans acc4.r13
        rbp := (k5 .rbp (by simp)).trans acc4.rbp }
      ilt := Nat.pos_of_ne_zero hc0
      rbx := by rw [k5 .rbx (by simp), hrbx4, Nat.sub_zero]
      r12 := by
        rw [reg_eval hm5 hr128]
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
        rw [show (envB m0 st4.data [] 0).regs .r12 = reg st4.data .r12 from rfl, hr124]
        apply BitVec.eq_of_toNat_eq
        simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat, show Width.W64.bits = 64 from rfl]
        omega
      rcx := by
        rw [reg_eval hm5 hrcx8]
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, l72] }

end

end NativeRustcVmX64.Whir.BasisWEval
