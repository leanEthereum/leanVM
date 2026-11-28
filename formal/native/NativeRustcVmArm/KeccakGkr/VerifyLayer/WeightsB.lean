module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.WeightsHead
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.FrontDefs
import Mathlib.Tactic.IntervalCases

/-!
# `verify_layer`: the weights loop's iteration, from the first `EW::mul` on

From `WMid j` at `k + NativeRustcVmArm.Vm.VerifyLayer.b55Offset`, `β · eq[keccakAlong j 3]` in X0, X1: `b55` and `EW::mul`
(`β · (eq[keccakAlong j 4] + β · eq[keccakAlong j 3])`), `b56` (weight `j` stored, the index
advanced), then the next head `WHead (j + 1)` or, after the last weight, `.LVerifyLayer_35`
(`phaseB`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVmArm.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes TStateAt DecArea)
open LeanVM.Protocol.Verifier (keccakAlong)

public section

/-- A register a block set to the `eor` of two registers. -/
theorem eor_regs [Labels] {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    {r r1 r2 : XReg} (hm : Match (Env.ofMachine m rs) S m')
    (h : S.reg r = some (.bin .eor .W64 (.reg r1) (.reg r2))) :
    m'.regs.getXReg r = m.regs.getXReg r1 ^^^ m.regs.getXReg r2 := by
  apply UInt64.toBitVec_inj.mp
  rw [hm.regs r _ h, UInt64.toBitVec_xor]
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
  rfl

/-- The weight from its parts, limb by limb. -/
theorem lw_eq (x y z beta : EW) :
    (⟨(EW.mul beta ⟨(beta * z).c0 ^^^ y.c0, (beta * z).c1 ^^^ y.c1⟩).c0 ^^^ x.c0,
      (EW.mul beta ⟨(beta * z).c0 ^^^ y.c0, (beta * z).c1 ^^^ y.c1⟩).c1 ^^^ x.c1⟩ : EW) =
      x + beta * (y + beta * z) := by
  rw [ew_add y, ew_add x, UInt64.xor_comm y.c0, UInt64.xor_comm y.c1, UInt64.xor_comm x.c0,
    UInt64.xor_comm x.c1]
  rfl

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}
  {s' : TState} {t0 t1 t2 beta : EW} {mu point eq : Array EW}

/-- **The iteration from the first `EW::mul`**: weight `j` stored, then the next head or, after
the last weight, `.LVerifyLayer_35` with all `1600` written. -/
theorem phaseB (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hps : point.size ≤ 30) (heq : eq.size = 2048) {j : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b55Offset)) (hm : WMid m0 a s' t0 t1 t2 beta mu point eq j st.data)
    (h0 : st.data.regs.X0 = (beta * eq.getD (keccakAlong j 3) 0).c0)
    (h1 : st.data.regs.X1 = (beta * eq.getD (keccakAlong j 3) 0).c1)
    {R : MachineState → Prop}
    (next : ∀ st', j + 1 < 1600 → WHead k m0 a s' t0 t1 t2 beta mu point eq (j + 1) st' →
      Eventually (step1 Host.exe) R st')
    (last : ∀ st', j + 1 = 1600 → st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b62Offset) → Body m0 st'.data →
      st'.data.regs.X23 = beta.c0 → st'.data.regs.X25 = beta.c1 →
      st'.data.regs.X24.toNat = point.size →
      WMem m0 a s' t0 t1 t2 beta mu point eq 1600 st'.data.dmem →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have g := geo_of hpre
  have hj := hm.lt
  have hb := hm.body
  have := g.hs
  -- `b55`: `eq[keccakAlong j 4] + β · eq[keccakAlong j 3]`, β.
  have hwf := wf_fr hpre hb
  refine exec_at (blk hp b55_in_code (by simp [b55])) e55 hwf hpc (match_fr hpre hb)
    fun st1 hm1 hpc1 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b55Offset + b55.length = k + NativeRustcVmArm.Vm.VerifyLayer.b56Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b55_next]] at hpc1
  have hb1 : Body m0 st1.data :=
    Fr.ofBlock hb (match_fr hpre hb) hm1 hwf rfl rfl rfl (fun r hr ↦ by cases hr)
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have e10 : st1.data.regs.X0 = beta.c0 := (reg_of (r := .X0) (r' := .X23) hm1 rfl).trans hm.x23
  have e11 : st1.data.regs.X1 = beta.c1 := (reg_of (r := .X1) (r' := .X25) hm1 rfl).trans hm.x25
  have e12 : st1.data.regs.X2 =
      (beta * eq.getD (keccakAlong j 3) 0).c0 ^^^ (eq.getD (keccakAlong j 4) 0).c0 := by
    rw [← h0, ← hm.x21]; exact eor_regs (r := .X2) hm1 rfl
  have e13 : st1.data.regs.X3 =
      (beta * eq.getD (keccakAlong j 3) 0).c1 ^^^ (eq.getD (keccakAlong j 4) 0).c1 := by
    rw [← h1, ← hm.x22]; exact eor_regs (r := .X3) hm1 rfl
  have k1 : Bus.KeepRegs [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29]
      st.data st1.data := Bus.KeepRegs.of_block hm1 rfl
  have hmid1 : WMid m0 a s' t0 t1 t2 beta mu point eq j st1.data :=
    ⟨hj, hb1, (congrArg UInt64.toNat (k1 .X19 (by simp))).trans hm.x19,
      (congrArg UInt64.toNat (k1 .X26 (by simp))).trans hm.x26,
      (congrArg UInt64.toBitVec (k1 .X29 (by simp))).trans hm.x29,
      (congrArg UInt64.toBitVec (k1 .X20 (by simp))).trans hm.x20,
      (k1 .X23 (by simp)).trans hm.x23, (k1 .X25 (by simp)).trans hm.x25,
      (congrArg UInt64.toNat (k1 .X24 (by simp))).trans hm.x24,
      (k1 .X21 (by simp)).trans hm.x21, (k1 .X22 (by simp)).trans hm.x22,
      (k1 .X28 (by simp)).trans hm.x28, (k1 .X27 (by simp)).trans hm.x27,
      by rw [hd1]; exact hm.mem, by rw [hd1]; exact hm.f96⟩
  refine mul_call hpre hmul hpc1 hb1 fun st2 hpc2 hb2 h20 h21 hsv2 hs2 ↦ ?_
  rw [e10, e11, e12, e13] at h20 h21
  have hmid2 := hmid1.call hpre hps heq hb2 hsv2 hs2
  -- `b56`: weight `j` stored, the index advanced.
  have hwf3 := wf_s hpre hb2 (o := 51200 + 16 * j) (n := 16) (by decide) (by omega)
  have hm3 := match_sRegs hpre hb2 (o := 51200 + 16 * j) (n := 16)
    (known := [(.X29, .ptr 1 0), (.X20, .ptr 1 8)])
    ⟨by
      show st2.data.regs.X29.toBitVec = sA m0 + BitVec.ofNat 64 (51200 + 16 * j) +
        BitVec.ofInt 64 0
      rw [hmid2.x29, show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl,
        NativeRustcVm.addr_add_zero],
    by
      show st2.data.regs.X20.toBitVec = sA m0 + BitVec.ofNat 64 (51200 + 16 * j) +
        BitVec.ofInt 64 8
      rw [hmid2.x20, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl,
        NativeRustcVm.addr_add_add, show 51200 + 16 * j + 8 = 51208 + 16 * j by omega],
    trivial⟩
  refine exec_at (blk hp b56_in_code (by simp [b56])) e56 hwf3 hpc2 hm3 fun st3 hm3' hpc3 ↦ ?_
  have hb3 : Body m0 st3.data :=
    Body.sBlock hpre hb2 (o := 51200 + 16 * j) (n := 16) (by decide) (by omega) (by omega)
      hm3 hm3' rfl rfl
  have hw0 := Bus.wordAt_write (r := 1) (o := 0) hm3' rfl (by omega)
    (v := .bin .eor .W64 (.reg .X0) (.reg .X28)) (fun i hi ↦ by interval_cases i <;> rfl)
  have hw8 := Bus.wordAt_write (r := 1) (o := 8) hm3' rfl (by omega)
    (v := .bin .eor .W64 (.reg .X1) (.reg .X27)) (fun i hi ↦ by interval_cases i <;> rfl)
  rw [Bus.eval_eor _ _ _ st2.data.regs.X28 rfl] at hw0
  rw [Bus.eval_eor _ _ _ st2.data.regs.X27 rfl] at hw8
  have q0 : UInt64.ofBitVec ((Env.ofMachine st2.data [(base m0 2032, 2032),
      (sA m0 + BitVec.ofNat 64 (51200 + 16 * j), 16)]).regs .X0) = st2.data.regs.X0 := rfl
  have q1 : UInt64.ofBitVec ((Env.ofMachine st2.data [(base m0 2032, 2032),
      (sA m0 + BitVec.ofNat 64 (51200 + 16 * j), 16)]).regs .X1) = st2.data.regs.X1 := rfl
  rw [q0, h20, hmid2.x28] at hw0
  rw [q1, h21, hmid2.x27] at hw8
  rw [NativeRustcVm.addr_add_zero] at hw0
  have hlw : NativeRustcVm.EWAt st3.data.dmem (sA m0 + BitVec.ofNat 64 (51200 + 16 * j))
      (lwF eq beta j) := by
    rw [lwF, ← lw_eq, NativeRustcVm.ewAt_iff]
    exact ⟨hw0, hw8⟩
  have ej := g.sa (o := 51200 + 16 * j) (by omega)
  have hs3 : SameOutside st2.data.dmem st3.data.dmem
      (InRange (sA m0 + BitVec.ofNat 64 (51200 + 16 * j)) 16) :=
    NativeRustcVm.SameOutside.mono (hm3'.sameOutside hwf3) fun _ hq ↦
      Bus.Written.inRange (r := 1) rfl (by rw [ej]; omega) (by decide) hq
  have hmem3 := WMem.store hpre hps heq hj hmid2.mem (hm3'.kept hwf3) hs3 hlw
  have hf96 : NativeRustcVm.WordAt st3.data.dmem (base m0 2032 + BitVec.ofNat 64 96)
      (UInt64.ofBitVec (sA m0 + BitVec.ofNat 64 (107528 + 16 * (j + 1)))) :=
    keep_blk hm3' hwf3 (o := 96) (L := 8) (by omega)
      (fun w hw ↦ by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> simp)
      (le_of_eq (NativeRustcVm.length_wordBytes _)) hmid2.f96
  have k3 : Bus.KeepRegs [.X23, .X24, .X25] st2.data st3.data := Bus.KeepRegs.of_block hm3' rfl
  have r23 : st3.data.regs.X23 = beta.c0 := (k3 .X23 (by simp)).trans hmid2.x23
  have r25 : st3.data.regs.X25 = beta.c1 := (k3 .X25 (by simp)).trans hmid2.x25
  have r24 : st3.data.regs.X24.toNat = point.size :=
    (congrArg UInt64.toNat (k3 .X24 (by simp))).trans hmid2.x24
  have hx26 : ((Env.ofMachine st2.data [(base m0 2032, 2032),
      (sA m0 + BitVec.ofNat 64 (51200 + 16 * j), 16)]).regs .X26).toNat = 25600 - 16 * j :=
    hmid2.x26
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b56Offset + b56.length = k + NativeRustcVmArm.Vm.VerifyLayer.b57Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b56_next]] at hpc3
  by_cases hl : j + 1 = 1600
  · have hc : (SBool.cmp .eq .W64 (.reg .X26) (.lit 16)).eval (Env.ofMachine st2.data
        [(base m0 2032, 2032), (sA m0 + BitVec.ofNat 64 (51200 + 16 * j), 16)]) = true := by
      rw [sb_cmp, eq_apply, ev_reg, hx26, ev_lit, BitVec.toNat_ofNat]
      exact decide_eq_true (by omega)
    exact last st3 hl ((pc_true hpc3 hc).trans (label35 hp)) hb3 r23 r25 r24 (hl ▸ hmem3)
  · have hc : (SBool.cmp .eq .W64 (.reg .X26) (.lit 16)).eval (Env.ofMachine st2.data
        [(base m0 2032, 2032), (sA m0 + BitVec.ofNat 64 (51200 + 16 * j), 16)]) = false := by
      rw [sb_cmp, eq_apply, ev_reg, hx26, ev_lit, BitVec.toNat_ofNat]
      exact decide_eq_false (by omega)
    refine next st3 (by omega) ⟨by omega, pc_false hpc3 hc, hb3, ?_, ?_, ?_, ?_, r23, r25, r24,
      hmem3, hf96⟩
    · show (st3.data.regs.getXReg .X19).toBitVec.toNat = j + 1
      have hx19 : ((Env.ofMachine st2.data [(base m0 2032, 2032),
          (sA m0 + BitVec.ofNat 64 (51200 + 16 * j), 16)]).regs .X19).toNat = j := hmid2.x19
      rw [hm3'.regs .X19 _ rfl, ev_bin, add_toNat, ev_reg, hx19, ev_lit, BitVec.toNat_ofNat]
      omega
    · show (st3.data.regs.getXReg .X26).toBitVec.toNat = 25600 - 16 * (j + 1)
      rw [hm3'.regs .X26 _ rfl, ev_bin, sub_toNat, ev_reg, hx26, ev_lit, BitVec.toNat_ofNat]
      omega
    · show (st3.data.regs.getXReg .X29).toBitVec = _
      rw [hm3'.regs .X29 _ rfl, ev_ptr]
      show sA m0 + BitVec.ofNat 64 (51200 + 16 * j) + BitVec.ofInt 64 16 = _
      rw [show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, NativeRustcVm.addr_add_add,
        show 51200 + 16 * j + 16 = 51200 + 16 * (j + 1) by omega]
    · show (st3.data.regs.getXReg .X20).toBitVec = _
      rw [hm3'.regs .X20 _ rfl, ev_ptr]
      show sA m0 + BitVec.ofNat 64 (51200 + 16 * j) + BitVec.ofInt 64 24 = _
      rw [show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl, NativeRustcVm.addr_add_add,
        show 51200 + 16 * j + 24 = 51208 + 16 * (j + 1) by omega]

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
