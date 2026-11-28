module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.WeightsA
import Mathlib.Tactic.IntervalCases

/-!
# `verify_layer`: the weights loop's iteration, to the first `EW::mul`

From `WHead j` at `.LVerifyLayer_30`: `b57` (the positions), `b58` (`eq[keccakAlong j 4]` into
X21, X22), `b60`, `b53` (`eq[keccakAlong j 3]` into X2, X3), `b54` (`eq[j]` into X28, X27, the
frame's word `96` advanced, β into X0, X1), then `EW::mul` (`phaseA`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVmArm.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes TStateAt DecArea)
open LeanVM.Protocol.Verifier (keccakAlong)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}
  {s' : TState} {t0 t1 t2 beta : EW} {mu point eq : Array EW}

/-- **The iteration to the first `EW::mul`**: back at `k + NativeRustcVmArm.Vm.VerifyLayer.b55Offset` with `WMid` and
`β · eq[keccakAlong j 3]` in X0, X1. -/
theorem phaseA (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hps : point.size ≤ 30) (heq : eq.size = 2048) {j : Nat} {st : MachineState}
    (hh : WHead k m0 a s' t0 t1 t2 beta mu point eq j st) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b55Offset) →
      WMid m0 a s' t0 t1 t2 beta mu point eq j st'.data →
      st'.data.regs.X0 = (beta * eq.getD (keccakAlong j 3) 0).c0 →
      st'.data.regs.X1 = (beta * eq.getD (keccakAlong j 3) 0).c1 →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have g := geo_of hpre
  have hj := hh.lt
  have hb := hh.body
  have := g.hs
  have hA4 : keccakAlong j 4 < 1600 := by rw [along_eq]; have := alongRow_lt j 4 hj; omega
  have hA3 : keccakAlong j 3 < 1600 := by rw [along_eq]; have := alongRow_lt j 3 hj; omega
  -- `b57`: the positions.
  have hwf := wf_fr hpre hb
  refine exec_at (blk hp b57_in_code (by simp [b57])) e57 hwf hh.pc (match_fr hpre hb)
    fun st1 hm1 hpc1 ↦ ?_
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hb1 : Body m0 st1.data :=
    Fr.ofBlock hb (match_fr hpre hb) hm1 hwf rfl rfl rfl (fun r hr ↦ by cases hr)
  have hx19 : ((Env.ofMachine st.data [(base m0 2032, 2032)]).regs .X19).toNat = j := hh.x19
  have h11 : (st1.data.regs.getXReg .X11).toBitVec.toNat = 64 * alongRow j 4 := by
    rw [hm1.regs .X11 x11S rfl, x11S_val hx19 hj]
  have h9 : (st1.data.regs.getXReg .X9).toBitVec.toNat = j / 64 % 5 := by
    rw [hm1.regs .X9 x9S rfl, x9S_val hx19 hj]
  have h10 : (st1.data.regs.getXReg .X10).toBitVec.toNat = 5 * (j / 320) := by
    rw [hm1.regs .X10 Tsym rfl, T_val hx19 hj]
  have h8 : (st1.data.regs.getXReg .X8).toBitVec.toNat = j % 64 := by
    rw [hm1.regs .X8 (.bin .and .W64 (.reg .X19) (.lit 63)) rfl, x8_val hx19]
  have hc57 : (SBool.and (SBool.not (SBool.cmp .ult .W64 x11S (.lit 2047)))
      (SBool.not (SBool.cmp .eq .W64 x11S (.lit 2047)))).eval
      (Env.ofMachine st.data [(base m0 2032, 2032)]) = false := by
    have h1 : 64 * alongRow j 4 < 2047 % 2 ^ 64 := by have := alongRow_lt j 4 hj; omega
    rw [sb_and, sb_not (SBool.cmp .ult .W64 x11S (.lit 2047)), sb_cmp .ult .W64 x11S (.lit 2047),
      ult_apply, x11S_val hx19 hj, ev_lit, BitVec.toNat_ofNat, decide_eq_true h1]
    rfl
  have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b58Offset) := pc_false hpc1 hc57
  have k1 : Bus.KeepRegs [.X19, .X20, .X23, .X24, .X25, .X26, .X29] st.data st1.data :=
    Bus.KeepRegs.of_block hm1 rfl
  -- `b58`: `eq[keccakAlong j 4]`.
  have hf1 : NativeRustcVm.WordAt st1.data.dmem (base m0 2032 + BitVec.ofNat 64 144)
      (UInt64.ofBitVec (eqA m0)) := by rw [hd1]; exact hh.mem.f144
  have hwf2 := wf_s hpre hb1 (o := 107520 + 16 * keccakAlong j 4) (n := 16) (by decide)
    (by omega)
  have hm2 := match_sAlias hpre hb1 (o := 107520 + 16 * keccakAlong j 4) (n := 16)
    (x := .bin .add .W64 (.bin .add .W64 (.load 0 144 8) (shl4 (.reg .X11))) (shl4 (.reg .X8)))
    (off := 0) (by
      rw [idx_eval (fw_load rfl hf1) h11 h8, ← along_eq, UInt64.toBitVec_ofBitVec,
        NativeRustcVm.addr_add_add, show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl,
        NativeRustcVm.addr_add_zero])
  refine exec_at (blk hp b58_in_code (by simp [b58])) e58 hwf2 hpc1' hm2 fun st2 hm2' hpc2 ↦ ?_
  have hb2 : Body m0 st2.data :=
    Fr.ofBlock hb1 hm2 hm2' hwf2 rfl rfl rfl (fun r hr ↦ by cases hr)
  have hd2 : st2.data.dmem = st1.data.dmem := hm2'.dmem_eq hwf2 rfl
  have hk4 := kern_word hh.mem heq (i := keccakAlong j 4) (by omega)
  rw [← hd1] at hk4
  have e21 : st2.data.regs.X21 = (eq.getD (keccakAlong j 4) 0).c0 :=
    reg_load (r := .X21) hm2' rfl hk4.1
  have e22 : st2.data.regs.X22 = (eq.getD (keccakAlong j 4) 0).c1 :=
    reg_load (r := .X22) hm2' rfl hk4.2
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b60Offset) := Eq.trans hpc2 (label33 hp)
  have k2 : Bus.KeepRegs [.X19, .X20, .X23, .X24, .X25, .X26, .X29] st1.data st2.data :=
    Bus.KeepRegs.of_block hm2' rfl
  have k2' : Bus.KeepRegs [.X8, .X9, .X10] st1.data st2.data := Bus.KeepRegs.of_block hm2' rfl
  -- `b60`: `keccakAlong j 3`.
  have hwf3 := wf_fr hpre hb2
  refine exec_at (blk hp b60_in_code (by simp [b60])) e60 hwf3 hpc2' (match_fr hpre hb2)
    fun st3 hm3 hpc3 ↦ ?_
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf3 rfl
  have hb3 : Body m0 st3.data :=
    Fr.ofBlock hb2 (match_fr hpre hb2) hm3 hwf3 rfl rfl rfl (fun r hr ↦ by cases hr)
  have h9' : ((Env.ofMachine st2.data [(base m0 2032, 2032)]).regs .X9).toNat = j / 64 % 5 := by
    show (st2.data.regs.getXReg .X9).toBitVec.toNat = _
    rw [k2' .X9 (by simp), h9]
  have h10' : ((Env.ofMachine st2.data [(base m0 2032, 2032)]).regs .X10).toNat =
      5 * (j / 320) := by
    show (st2.data.regs.getXReg .X10).toBitVec.toNat = _
    rw [k2' .X10 (by simp), h10]
  have hx9b := x9b_val h9' h10' (by omega) (by omega)
  have h93 : (st3.data.regs.getXReg .X9).toBitVec.toNat = 64 * alongRow j 3 := by
    rw [hm3.regs .X9 x9b rfl, hx9b, alongRow]
  have hc60 : (SBool.or (SBool.cmp .ult .W64 x9b (.lit 2047))
      (SBool.cmp .eq .W64 x9b (.lit 2047))).eval
      (Env.ofMachine st2.data [(base m0 2032, 2032)]) = true := by
    have h1 : 64 * ((j / 64 % 5 + 3) % 5 + 5 * (j / 320)) < 2047 % 2 ^ 64 := by omega
    rw [sb_or, sb_cmp .ult .W64 x9b (.lit 2047), ult_apply, hx9b, ev_lit, BitVec.toNat_ofNat,
      decide_eq_true h1]
    rfl
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b53Offset) := (pc_true hpc3 hc60).trans (label28 hp)
  have k3 : Bus.KeepRegs [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X29, .X8]
      st2.data st3.data := Bus.KeepRegs.of_block hm3 rfl
  have h83 : (st3.data.regs.getXReg .X8).toBitVec.toNat = j % 64 := by
    rw [k3 .X8 (by simp), k2' .X8 (by simp), h8]
  -- `b53`: `eq[keccakAlong j 3]`.
  have hf3 : NativeRustcVm.WordAt st3.data.dmem (base m0 2032 + BitVec.ofNat 64 144)
      (UInt64.ofBitVec (eqA m0)) := by rw [hd3, hd2]; exact hf1
  have hwf4 := wf_s hpre hb3 (o := 107520 + 16 * keccakAlong j 3) (n := 16) (by decide)
    (by omega)
  have hm4 := match_sAlias hpre hb3 (o := 107520 + 16 * keccakAlong j 3) (n := 16)
    (x := .bin .add .W64 (.bin .add .W64 (.load 0 144 8) (shl4 (.reg .X9))) (shl4 (.reg .X8)))
    (off := 0) (by
      rw [idx_eval (fw_load rfl hf3) h93 h83, ← along_eq, UInt64.toBitVec_ofBitVec,
        NativeRustcVm.addr_add_add, show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl,
        NativeRustcVm.addr_add_zero])
  refine exec_at (blk hp b53_in_code (by simp [b53])) e53 hwf4 hpc3' hm4 fun st4 hm4' hpc4 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b53Offset + b53.length = k + NativeRustcVmArm.Vm.VerifyLayer.b54Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b53_next]] at hpc4
  have hb4 : Body m0 st4.data :=
    Fr.ofBlock hb3 hm4 hm4' hwf4 rfl rfl rfl (fun r hr ↦ by cases hr)
  have hd4 : st4.data.dmem = st3.data.dmem := hm4'.dmem_eq hwf4 rfl
  have hk3 := kern_word hh.mem heq (i := keccakAlong j 3) (by omega)
  rw [← hd1, ← hd2, ← hd3] at hk3
  have e42 : st4.data.regs.X2 = (eq.getD (keccakAlong j 3) 0).c0 :=
    reg_load (r := .X2) hm4' rfl hk3.1
  have e43 : st4.data.regs.X3 = (eq.getD (keccakAlong j 3) 0).c1 :=
    reg_load (r := .X3) hm4' rfl hk3.2
  have k4 : Bus.KeepRegs [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X29]
      st3.data st4.data := Bus.KeepRegs.of_block hm4' rfl
  have k4' : Bus.KeepRegs [.X19, .X20, .X23, .X24, .X25, .X26, .X29] st.data st4.data :=
    k1.trans (k2.trans ((Bus.KeepRegs.of_block hm3 rfl).trans (Bus.KeepRegs.of_block hm4' rfl)))
  -- `b54`: `eq[j]`, the frame's word `96` advanced, β.
  have hf96 : NativeRustcVm.WordAt st4.data.dmem (base m0 2032 + BitVec.ofNat 64 96)
      (UInt64.ofBitVec (sA m0 + BitVec.ofNat 64 (107528 + 16 * j))) := by
    rw [hd4, hd3, hd2, hd1]; exact hh.f96
  have hwf5 := wf_s hpre hb4 (o := 107520 + 16 * j) (n := 16) (by decide) (by omega)
  have hm5 := match_sAlias hpre hb4 (o := 107520 + 16 * j) (n := 16) (x := .load 0 96 8)
    (off := 8) (by
      rw [ev_load, fw_load rfl hf96, UInt64.toBitVec_ofBitVec,
        show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add,
        show 107520 + 16 * j + 8 = 107528 + 16 * j by omega])
  refine exec_at (blk hp b54_in_code (by simp [b54])) e54 hwf5 hpc4 hm5 fun st5 hm5' hpc5 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b54Offset + b54.length = k + NativeRustcVmArm.Vm.VerifyLayer.b55Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b54_next]] at hpc5
  have hb5 : Body m0 st5.data :=
    Body.sBlock hpre hb4 (o := 107520 + 16 * j) (n := 16) (by decide) (by omega) (by omega)
      hm5 hm5' rfl rfl
  have hkj := kern_word hh.mem heq (i := j) (by omega)
  rw [← hd1, ← hd2, ← hd3, ← hd4] at hkj
  have e528 : st5.data.regs.X28 = (eq.getD j 0).c0 := reg_load (r := .X28) hm5' rfl hkj.1
  have e527 : st5.data.regs.X27 = (eq.getD j 0).c1 := reg_load (r := .X27) hm5' rfl hkj.2
  have k5 : Bus.KeepRegs [.X2, .X3, .X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X29]
      st4.data st5.data := Bus.KeepRegs.of_block hm5' rfl
  have e50 : st5.data.regs.X0 = beta.c0 :=
    (reg_of (r := .X0) (r' := .X23) hm5' rfl).trans ((k4' .X23 (by simp)).trans hh.x23)
  have e51 : st5.data.regs.X1 = beta.c1 :=
    (reg_of (r := .X1) (r' := .X25) hm5' rfl).trans ((k4' .X25 (by simp)).trans hh.x25)
  have e52 : st5.data.regs.X2 = (eq.getD (keccakAlong j 3) 0).c0 :=
    (k5 .X2 (by simp)).trans e42
  have e53 : st5.data.regs.X3 = (eq.getD (keccakAlong j 3) 0).c1 :=
    (k5 .X3 (by simp)).trans e43
  have hs5 : SameOutside st4.data.dmem st5.data.dmem
      (InRange (base m0 2032 + BitVec.ofNat 64 96) 8) := by
    have := g.hN; have := Geo.sp_lt m0
    have e96 := g.fa (o := 96) (by omega)
    refine NativeRustcVm.SameOutside.mono (hm5'.sameOutside hwf5)
      fun q ⟨w, hw, b, sz, hb', h1, h2⟩ ↦ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    subst hw
    simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb'
    obtain ⟨rfl, rfl⟩ := hb'
    simp only at h1 h2
    rw [g.bN] at h1 h2
    rw [Sym.inRange_iff (by rw [e96]; omega), e96]
    omega
  have hmem4 : WMem m0 a s' t0 t1 t2 beta mu point eq j st4.data.dmem := by
    rw [hd4, hd3, hd2, hd1]; exact hh.mem
  have hmem5 := hmem4.frame96 hpre hps heq (by omega) (hm5'.kept hwf5) hs5
  have hw96 := Bus.wordAt_write (r := 0) (o := 96) hm5' rfl (by omega)
    (v := .bin .add .W64 (.load 0 96 8) (.lit 16)) (fun i hi ↦ by interval_cases i <;> rfl)
  rw [ev_bin, ev_load, fw_load rfl hf96, ev_lit, add_apply, UInt64.toBitVec_ofBitVec,
    NativeRustcVm.addr_add_add, show 107528 + 16 * j + 16 = 107528 + 16 * (j + 1) by omega]
    at hw96
  have hmid5 : WMid m0 a s' t0 t1 t2 beta mu point eq j st5.data := by
    have kk : Bus.KeepRegs [.X19, .X20, .X23, .X24, .X25, .X26, .X29] st.data st5.data :=
      k4'.trans (Bus.KeepRegs.of_block hm5' rfl)
    have k21 : st5.data.regs.X21 = st2.data.regs.X21 :=
      (k5 .X21 (by simp)).trans ((k4 .X21 (by simp)).trans (k3 .X21 (by simp)))
    have k22 : st5.data.regs.X22 = st2.data.regs.X22 :=
      (k5 .X22 (by simp)).trans ((k4 .X22 (by simp)).trans (k3 .X22 (by simp)))
    exact ⟨hj, hb5, (congrArg UInt64.toNat (kk .X19 (by simp))).trans hh.x19,
      (congrArg UInt64.toNat (kk .X26 (by simp))).trans hh.x26,
      (congrArg UInt64.toBitVec (kk .X29 (by simp))).trans hh.x29,
      (congrArg UInt64.toBitVec (kk .X20 (by simp))).trans hh.x20,
      (kk .X23 (by simp)).trans hh.x23, (kk .X25 (by simp)).trans hh.x25,
      (congrArg UInt64.toNat (kk .X24 (by simp))).trans hh.x24, k21.trans e21, k22.trans e22,
      e528, e527, hmem5, hw96⟩
  refine mul_call hpre hmul hpc5 hb5 fun st6 hpc6 hb6 h60 h61 hsv6 hs6 ↦ ?_
  rw [e50, e51, e52, e53] at h60 h61
  exact cont st6 hpc6 (hmid5.call hpre hps heq hb6 hsv6 hs6) h60 h61

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
