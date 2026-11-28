module

public import NativeRustcVmX64.Whir.BasisWEval.Steps
public import NativeRustcVmX64.Code.Vm.LayoutWPlacement.Names

/-!
# `BasisW::eval`: the entry (x86-64)

The prologue (`b0`) pushes the callee-saved registers, keeps the output's address, the point and
the layout's address in the frame, loads the scales' slice (RBP, R15) and the layout's address
from the `BasisW` (RSI, kept in RBX) and calls `LayoutW::placement` on `QKECCAK`; `b1` tests the
scales' count; `b2` takes the first scale (R14, the frame's `24`, R13 past it), `b3` `0` without
scales: `A4` at `NativeRustcVmX64.Vm.BasisWEval.label_3` (`entry`).
-/

namespace NativeRustcVmX64.Whir.BasisWEval

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model LeanVM.Parameters
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVm.Layout NativeRustcVm.Ring
open NativeRustcVmX64.Vm.BasisWEval
open NativeRustcVm.Transcript (off off_add off_zero toNat_off)
open LeanVM.Protocol.Verifier (qkeccak Placement)

@[expose] public section

/-- **At `NativeRustcVmX64.Vm.BasisWEval.label_3`** (`b4`): the `BasisW` (RBX), the scales' slice (RBP, R15), the
placement of `QKECCAK` (RAX, RDX), the first scale (R14, the frame's `24`) and the next one's
address (R13). -/
structure A4 (m0 : MachineData) (ba : BasisAddrs) (b : BasisW) (v : Vals) (d : MachineData) :
    Prop where
  base : Base m0 ba 24 d
  rbx : reg d .rbx = reg m0 .rsi
  rbp : reg d .rbp = ba.scales
  r15 : reg d .r15 = ba.count.toUInt64.toBitVec
  rax : reg d .rax = (v.L.placement qkeccak).variableCount.toUInt64.toBitVec
  rdx : reg d .rdx = (v.L.placement qkeccak).index.toUInt64.toBitVec
  r13 : reg d .r13 = sA ba (min 1 ba.count)
  r14 : reg d .r14 = (sAt b.scales 0).c0.toBitVec
  w24 : FW m0 d 24 (sAt b.scales 0).c1.toBitVec

end

public section

/-! ## Numbers -/

theorem test64 (x : BitVec 64) :
    CmpOp.apply .eq .W64 (BinOp.apply .and .W64 x x) (BitVec.ofNat 64 0) = decide (x.toNat = 0) := by
  simp only [BinOp.apply, CmpOp.apply, low_W64, ext_W64, BitVec.and_self]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat]

theorem sA_zero (ba : BasisAddrs) : sA ba 0 = ba.scales := by
  simp [sA, off]

theorem sA_succ (ba : BasisAddrs) (j : Nat) : sA ba j + BitVec.ofNat 64 16 = sA ba (j + 1) := by
  rw [sA, sA, off_add, Nat.mul_succ]

theorem inf [Host] {k : Nat} (hp : Placed code k) {ds : List Directive} {j : Nat}
    (hb : ds.IsInfixAt code j) (hne : ds ≠ []) : ds.IsInfixAt Host.prog (k + j) :=
  infix_of hb hne hp

variable {m0 : MachineData} {ba : BasisAddrs} {b : BasisW} {v : Vals}

theorem In.scale0 (h : In m0 ba b v) {o : Nat} {d : MachineData} (hf : Fb m0 o d)
    (hc : 0 < ba.count) :
    NativeRustcVm.WordAt d.dmem (off (sA ba 0) 0) (sAt b.scales 0).c0 ∧
      NativeRustcVm.WordAt d.dmem (off (sA ba 0) 8) (sAt b.scales 0).c1 :=
  h.scaleAt hf hc

variable [Host] {k : Nat}

/-- **The entry**, to `NativeRustcVmX64.Vm.BasisWEval.label_3`. -/
theorem entry (hp : Placed code k) (h : In m0 ba b v)
    (hpl : ∀ L, Spec (Labels.label NativeRustcVmX64.Vm.LayoutWPlacement.entryLabel) (LayoutWPlacementPre L)
      (LayoutWPlacementPost L))
    {R : MachineState → Prop}
    (cont : ∀ st : MachineState, st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b4Offset) → A4 m0 ba b v st.data →
      Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b0Offset)⟩ := by
  have hS := h.stackOk
  have hN := h.hN
  have hN0 := N_ge
  have hcl := count_lt h
  let p := reg m0 .rsi
  let ret0 := (Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b0Offset + b0.length)).toBitVec
  have hbasis : WhirIn m0 p 56 basisWEvalStack := h.basis
  have hwf : (envB m0 m0 [(p, 56)] ret0).WF := h.wf1 (fun _ h ↦ h) hbasis
  have hm : Match (envB m0 m0 [(p, 56)] ret0) entryS m0 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, (eval_ptr rfl).symm, trivial⟩ trivial trivial
      trivial
  refine exec_then (inf hp b0_in_code (by simp [b0])) exit_b0 hwf (fun _ _ ↦ rfl) hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, h0, hrbx, hrsi, hrdi, hrbp, hr15, w72, w32, w40, w48⟩ := ok_b0
  have hf1 : Fb m0 16 st1.data := Fr.of_prologue hS N_ge hwf hm1 hpro slots_le slots_cs h0
  have l0 : (envB m0 m0 [(p, 56)] ret0).load 1 0 8 = ba.scales :=
    load_ofMachine (r := 1) (o := 0) rfl (h.word0 0 (by decide))
  have l8 : (envB m0 m0 [(p, 56)] ret0).load 1 8 8 = ba.count.toUInt64.toBitVec :=
    load_ofMachine (r := 1) (o := 8) rfl (h.word0 1 (by decide))
  have l16 : (envB m0 m0 [(p, 56)] ret0).load 1 16 8 = ba.layout :=
    load_ofMachine (r := 1) (o := 16) rfl (h.word0 2 (by decide))
  have base1 : Base m0 ba 16 st1.data :=
    ⟨hf1, FW.wrote hm1 (by omega) w32 rfl, FW.wrote hm1 (by omega) w40 rfl,
      FW.wrote hm1 (by omega) w48 rfl, FW.wrote hm1 (by omega) w72 l16⟩
  have e1 : reg st1.data .rbx = p := (reg_eval hm1 hrbx).trans (eval_ptr rfl)
  have e2 : reg st1.data .rsi = 4#64 := reg_eval hm1 hrsi
  have e3 : reg st1.data .rdi = ba.layout := (reg_eval hm1 hrdi).trans l16
  have e4 : reg st1.data .rbp = ba.scales := (reg_eval hm1 hrbp).trans l0
  have e5 : reg st1.data .r15 = ba.count.toUInt64.toBitVec := (reg_eval hm1 hr15).trans l8
  have hle0 : 160 - 16 + layoutWPlacementStack ≤ basisWEvalStack := by
    unfold layoutWPlacementStack; omega
  have hpre : LayoutWPlacementPre v.L st1.data := by
    refine ⟨h.stackOk_at hf1 (by omega) hle0, ?_, ?_, ?_⟩
    · rw [e2]; decide
    · rw [e3]; exact h.layoutAt hf1
    · rw [e3]; exact (h.argIn hf1 (by omega) hle0 h.layoutIn).1
  refine Fr.call (c := 16) (Nc := layoutWPlacementStack) (lo := 24) (len := 0)
    (X := fun _ ↦ False) hS N_ge (by omega) hle0 slots_c16 (by omega) (fun _ h ↦ h.elim)
    (fun _ h ↦ h.elim) (hpl v.L) hf1 hpc1 hpre
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun _ h ↦ h.elim, hq.2.2.2⟩)
    fun m2 hf2 hq2 hk2 hcs2 ↦ ?_
  obtain ⟨hy0, hy1, -, -⟩ := hq2
  rw [e2] at hy0 hy1
  have base2 : Base m0 ba 24 m2 := base1.call hf2 hk2 (by omega) (.inr (by omega))
  have hq4 : (4#64 : BitVec 64).toNat = qkeccak := rfl
  rw [hq4] at hy0 hy1
  -- b1
  rw [show k + NativeRustcVmX64.Vm.BasisWEval.b0Offset + b0.length = k + NativeRustcVmX64.Vm.BasisWEval.b1Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.BasisWEval.b0_next]]
  obtain ⟨hmid1, hmem1, hk1⟩ := ok_b1
  refine h.block hf2 (h.wf0 hf2 (ret := 0)) (inf hp b1_in_code (by simp [b1])) exit_b1 nofun
    (match_body hf2 ⟨rfl, trivial⟩) hmid1 (h0_of_nil hmem1) fun st3 hm3 hpc3 hf3 ↦ ?_
  have base3 := base2.nil hf3 (h.wf0 hf2) hm3 hmem1
  have k3 : ∀ r ∈ [Reg64.rax, .rdx, .rbx, .rbp, .r15], reg st3.data r = reg m2 r :=
    fun r hr ↦ keeps_reg hm3 hk1 hr
  have r15 : reg st3.data .r15 = ba.count.toUInt64.toBitVec :=
    (k3 .r15 (by simp)).trans ((hcs2 .r15 rfl).trans e5)
  have rbp : reg st3.data .rbp = ba.scales := (k3 .rbp (by simp)).trans ((hcs2 .rbp rfl).trans e4)
  have rbx : reg st3.data .rbx = p := (k3 .rbx (by simp)).trans ((hcs2 .rbx rfl).trans e1)
  have rax : reg st3.data .rax = (v.L.placement qkeccak).variableCount.toUInt64.toBitVec :=
    (k3 .rax (by simp)).trans hy0
  have rdx : reg st3.data .rdx = (v.L.placement qkeccak).index.toUInt64.toBitVec :=
    (k3 .rdx (by simp)).trans hy1
  have hc1 : c1.eval (envB m0 m2 [] 0) = decide (ba.count = 0) := by
    simp only [c1, SBool.eval, Sym.eval]
    rw [test64]
    have e : reg m2 .r15 = ba.count.toUInt64.toBitVec := (hcs2 .r15 rfl).trans e5
    show decide ((reg m2 .r15).toNat = 0) = _
    rw [e, toNat_bv_toUInt64 hcl]
  simp only [PcOk] at hpc3
  rw [hc1] at hpc3
  have hsz := h.pre.2.1.scales_size
  by_cases hc0 : ba.count = 0
  · -- no scales: `b3`
    have hd : decide (ba.count = 0) = true := by simpa using hc0
    simp only [hd, ↓reduceIte] at hpc3
    rw [hp.label NativeRustcVmX64.Vm.BasisWEval.label_1_at] at hpc3
    obtain ⟨hmid, h0', w24, hmiss, hr13, hr14, hk⟩ := ok_b3
    refine at_pc hpc3 (h.block hf3 (h.wf0 hf3 (ret := 0)) (inf hp b3_in_code (by simp [b3]))
      exit_b3 nofun (match_body hf3 ⟨rfl, trivial⟩) hmid h0' fun st4 hm4 hpc4 hf4 ↦ ?_)
    have k4 : ∀ r ∈ [Reg64.rax, .rdx, .rbx, .rbp, .r15], reg st4.data r = reg st3.data r :=
      fun r hr ↦ keeps_reg hm4 hk hr
    have hs0 : sAt b.scales 0 = 0 := sAt_ge (by omega)
    simp only [PcOk] at hpc4
    rw [show k + NativeRustcVmX64.Vm.BasisWEval.b3Offset + b3.length = k + NativeRustcVmX64.Vm.BasisWEval.b4Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.BasisWEval.b3_next]] at hpc4
    refine cont st4 hpc4 {
      base := base3.block hf4 (h.wf0 hf3) hm4 hmid hmiss
      rbx := (k4 .rbx (by simp)).trans rbx
      rbp := (k4 .rbp (by simp)).trans rbp
      r15 := (k4 .r15 (by simp)).trans r15
      rax := (k4 .rax (by simp)).trans rax
      rdx := (k4 .rdx (by simp)).trans rdx
      r13 := by rw [reg_eval hm4 hr13, hc0, Nat.min_zero, sA_zero]; exact rbp
      r14 := by rw [reg_eval hm4 hr14, hs0]; rfl
      w24 := FW.wrote hm4 (by omega) w24 (by rw [hs0]; rfl) }
  · -- the first scale: `b2`
    have hd : decide (ba.count = 0) = false := by simpa using hc0
    simp only [hd, Bool.false_eq_true, ↓reduceIte] at hpc3
    rw [show k + NativeRustcVmX64.Vm.BasisWEval.b1Offset + b1.length = k + NativeRustcVmX64.Vm.BasisWEval.b2Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.BasisWEval.b1_next]] at hpc3
    have hpos : 0 < ba.count := Nat.pos_of_ne_zero hc0
    obtain ⟨hmid, h0', w24, hmiss, hr13, hr14, hr15, hk⟩ := ok_b2
    have hsc := h.scaleIn hpos (j := 0)
    have hwf2 : (envB m0 st3.data [(sA ba 0, 16)] 0).WF := h.wf1 hf3.frame.kept hsc
    have hm2 : Match (envB m0 st3.data [(sA ba 0, 16)] 0) (scaleS .rbp) st3.data :=
      match_ofMachine ⟨rfl, rfl, trivial⟩
        ⟨hf3.frame.rsp_eval, known_ptr rfl (by rw [sA_zero]; exact rbp), trivial⟩
        trivial trivial trivial
    have ⟨s0, s1⟩ := h.scale0 hf3 hpos
    refine at_pc hpc3 (h.block hf3 hwf2 (inf hp b2_in_code (by simp [b2])) exit_b2 nofun hm2
      hmid h0' fun st4 hm4 hpc4 hf4 ↦ ?_)
    simp only [PcOk] at hpc4
    rw [hp.label NativeRustcVmX64.Vm.BasisWEval.label_3_at] at hpc4
    have k4 : ∀ r ∈ [Reg64.rax, .rdx, .rbx, .r15], reg st4.data r = reg st3.data r :=
      fun r hr ↦ keeps_reg hm4 hk hr
    refine cont st4 hpc4 {
      base := base3.block hf4 hwf2 hm4 hmid hmiss
      rbx := (k4 .rbx (by simp)).trans rbx
      rbp := by rw [reg_eval hm4 hr15, eval_ptr rfl, sA_zero]
      r15 := (k4 .r15 (by simp)).trans r15
      rax := (k4 .rax (by simp)).trans rax
      rdx := (k4 .rdx (by simp)).trans rdx
      r13 := by
        rw [reg_eval hm4 hr13, show min 1 ba.count = 0 + 1 by omega, ← sA_succ]
        simp [Sym.eval]
      r14 := (reg_eval hm4 hr14).trans (load_ofMachine (r := 1) rfl s0)
      w24 := FW.wrote hm4 (by omega) w24 (load_ofMachine (r := 1) rfl s1) }

end

end NativeRustcVmX64.Whir.BasisWEval
