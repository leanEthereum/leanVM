module

public import NativeRustcVmArm.KeccakGkr.LinearTranspose.Copy

/-!
# `linear_transpose`: lane `0`'s copy loop

`.LLinearTranspose_6` (`b8`), lane `0` unrolled by two: elements `z` and `z + 1` of `g`, from
positions `(z + ρ_0) % 64` and `(z + 1 + ρ_0) % 64` of lane `π 0` (`Copy2`).
-/

namespace NativeRustcVmArm.KeccakGkr.LinearTranspose

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVmArm.Vm.LinearTranspose LeanVM.Parameters
open NativeRustcVm (Region)
open NativeRustcVm.KeccakGkr (gW colW outW weightsBytes)

@[expose] public section

/-- **Lane `0`'s copy loop head** after `z` elements, `z` even. -/
structure Copy2 [Labels] (m0 : MachineData) (ws : Array EW) (z : Nat) (st : MachineData) : Prop where
  regs : LaneRegs m0 st 0
  z_lt : z < 64
  z_even : z % 2 = 0
  x8 : st.regs.X8.toNat = keccakRhoW.getD 0 0 + z
  x9 : st.regs.X9.toBitVec = wA m0 + BitVec.ofNat 64 (1024 * keccakPi 0)
  x10 : st.regs.X10.toBitVec = gA m0 + BitVec.ofNat 64 (16 + 16 * z)
  x11 : st.regs.X11.toNat = 64 - z
  g : ElemsAt st.dmem (gA m0) (gF ws) z

end

public section

/-- `w8 + 1` zero-extended, below `2 ^ 32`. -/
theorem w32_add1_toNat (x : BitVec 64) (h : x.toNat + 1 < 2 ^ 32) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 x + BitVec.setWidth 32 1#64)).toNat = x.toNat + 1 := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show x.toNat < 2 ^ 32 by omega)]
  omega

variable [NativeRustcArm.Host] {ws : Array EW} {m0 : MachineData} {k : Nat}

/-- **Two elements of lane `0`'s copy loop**. -/
theorem copy2_step (hp : Placed code k) (hpre : LinearTransposePre ws m0) {z : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b8Offset)) (hI : Copy2 m0 ws z s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b8Offset) ∧ Copy2 m0 ws (z + 2) s'.data) ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b9Offset) ∧ AfterLane m0 ws 0 s'.data)) s := by
  have hS := hpre.1
  have hA := pre_areas hpre
  have hz := hI.z_lt
  have hze := hI.z_even
  have hpi : keccakPi 0 = 0 := rfl
  have hrho : keccakRhoW.getD 0 0 = 0 := rfl
  have hgok := Areas.ok hA (r := ⟨gA m0, weightsBytes⟩) (Or.inl (by simp [wsR]))
  have hwok := Areas.ok hA (r := ⟨wA m0, weightsBytes⟩) (Or.inr (by simp [rsR]))
  have hgw := Areas.apart_rs hA (w := ⟨gA m0, weightsBytes⟩) (r := ⟨wA m0, weightsBytes⟩)
    (by simp [wsR]) (by simp [rsR])
  obtain ⟨hm0, hnw0⟩ := sub_ok hwok (o := 1024 * keccakPi 0) (n := 1024)
    (by show 1024 * keccakPi 0 + 1024 ≤ 25600; decide)
  obtain ⟨hm1, hnw1⟩ := sub_ok hgok (o := 16 * z) (n := 32)
    (by show 16 * z + 32 ≤ 25600; omega)
  have hap : Apart (wA m0 + BitVec.ofNat 64 (1024 * keccakPi 0)) 1024
      (gA m0 + BitVec.ofNat 64 (16 * z)) 32 :=
    Apart.sub (NativeRustcVm.Apart.symm hgw) hwok.2 hgok.2
      (by show 1024 * keccakPi 0 + 1024 ≤ 25600; decide) (by show 16 * z + 32 ≤ 25600; omega)
      (by decide) (by decide)
  let env := Env.ofMachine s.data [(wA m0 + BitVec.ofNat 64 (1024 * keccakPi 0), 1024),
    (gA m0 + BitVec.ofNat 64 (16 * z), 32)]
  have hwf : env.WF := Env.wf_of
    ⟨⟨Mapped.kept' hm0 hI.regs.ctx.body.kept, hnw0⟩, ⟨Mapped.kept' hm1 hI.regs.ctx.body.kept, hnw1⟩,
      trivial⟩ (List.pairwise_pair.mpr hap)
  have hm : Match env copy2S s.data :=
    match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl
      ⟨by
        show (s.data.regs.getXReg .X9).toBitVec = _ + BitVec.ofInt 64 0
        rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
        exact hI.x9,
       by
        show (s.data.regs.getXReg .X10).toBitVec = (gA m0 + BitVec.ofNat 64 (16 * z)) + BitVec.ofInt 64 16
        rw [show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, NativeRustcVm.addr_add_add]
        rw [show (s.data.regs.getXReg .X10) = s.data.regs.X10 from rfl, hI.x10]
        congr 2
        omega,
       trivial⟩ trivial ⟨and63_lt _, and63_lt _, trivial⟩ trivial
  refine exec_at (b8_in_code.trans hp.1 (by simp [b8])) e8 hwf hpc hm fun s' hm' hpc' ↦ ?_
  have h0 := KeccakGkr.Match.ewAt_write2 hm' (pre := [_, _]) rfl rfl (by decide) (r := 1) rfl
    (by decide)
  have h1 := KeccakGkr.Match.ewAt_write2 hm' (pre := []) rfl rfl nofun (r := 1) rfl (by decide)
  sym_simp at h0 h1
  have hx8 : (env.regs .X8).toNat = z := by
    show s.data.regs.X8.toNat = z; rw [hI.x8, hrho, Nat.zero_add]
  rw [idx63_toNat', hx8] at h0
  rw [idx63_toNat', w32_add1_toNat _ (by rw [hx8]; omega), hx8] at h1
  have hel0 : NativeRustcVm.EWAt s'.data.dmem (gA m0 + BitVec.ofNat 64 (16 * z)) (gF ws z) := by
    have hx := load_ew (env := env) (r := 0) (o := 16 * (z % 64))
      (lane_elem hpre hI.regs.ctx.body (l := 0) (by decide) (Nat.mod_lt _ (by decide)))
    rw [Nat.zero_add, Nat.add_comm 8, hx.1, hx.2, BitVec.add_zero] at h0
    convert h0 using 1
    show gW ws (z / 64) (z % 64) = _
    rw [show z / 64 = 0 by omega, gW, hrho, Nat.add_zero, Nat.mod_mod]
  have hel1 : NativeRustcVm.EWAt s'.data.dmem (gA m0 + BitVec.ofNat 64 (16 * (z + 1))) (gF ws (z + 1)) := by
    have hx := load_ew (env := env) (r := 0) (o := 16 * ((z + 1) % 64))
      (lane_elem hpre hI.regs.ctx.body (l := 0) (by decide) (Nat.mod_lt _ (by decide)))
    rw [Nat.zero_add, Nat.add_comm 8, hx.1, hx.2, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      NativeRustcVm.addr_add_add] at h1
    rw [show 16 * (z + 1) = 16 * z + 16 by omega]
    convert h1 using 1
    show gW ws ((z + 1) / 64) ((z + 1) % 64) = _
    rw [show (z + 1) / 64 = 0 by omega, gW, hrho, Nat.add_zero, Nat.mod_mod]
  have hso : SameOutside s.data.dmem s'.data.dmem (InRange (gA m0 + BitVec.ofNat 64 (16 * z)) 32) :=
    NativeRustcVm.SameOutside.mono (hm'.sameOutside hwf) fun p h ↦
      Written.inRange (r := 1) rfl hnw1 (by decide) h
  have hbody : Body m0 s'.data :=
    hI.regs.ctx.body.write hS (by decide) slots_le (wsOff hpre) hm hm' hwf rfl free_ok (by decide)
      fun p h ↦ ⟨⟨gA m0, weightsBytes⟩, by simp [wsR],
        inRange_mono (Written.inRange (r := 1) rfl hnw1 (by decide) h)
          (by show 16 * z + 32 ≤ 25600; omega)⟩
  have hkeep := KeccakGkr.Match.regs_keep hm hm' [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26]
    (by decide)
  have hregs := hI.regs.keep hbody hkeep
  have hg : ElemsAt s'.data.dmem (gA m0) (gF ws) (z + 2) :=
    hI.g.grow (NativeRustcVm.NoWrap.sub (o := 0) (by rw [NativeRustcVm.addr_add_zero] at *; exact hgok.2)
        (by show 0 + 16 * (z + 2) ≤ 25600; omega) |>.trans_eq' (by rw [NativeRustcVm.addr_add_zero]))
      (by rw [show 16 * 2 = 32 from rfl]; exact hso) fun j hj ↦ by
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
        · exact hel0
        · exact hel1
  have h8 := hm'.regs .X8 _ rfl
  have h10 := hm'.regs .X10 _ rfl
  have h11 := hm'.regs .X11 _ rfl
  have h9 := hm'.regs .X9 _ rfl
  sym_simp at h8 h9 h10 h11
  have hx11 : (env.regs .X11).toNat = 64 - z := hI.x11
  simp only [PcOk] at hpc'
  sym_simp at hpc'
  by_cases hlast : z = 62
  · have hc : (env.regs .X11 == 2#64) = true := by
      rw [beq_iff_eq]; apply BitVec.eq_of_toNat_eq; rw [hx11]; simp; omega
    simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false, NativeRustcVmArm.Vm.LinearTranspose.b8_length, NativeRustcVmArm.Vm.LinearTranspose.b8Length] at hpc'
    refine .done _ (Or.inr ⟨hpc', hregs, ?_⟩)
    rw [show 64 * 0 + 64 = z + 2 by omega]
    exact hg
  · have hc : (env.regs .X11 == 2#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have := congrArg BitVec.toNat h; rw [hx11] at this
      simp at this; omega
    simp only [hc, Bool.not_false, ite_true] at hpc'
    refine .done _ (Or.inl ⟨hpc'.trans (hp.label (j := NativeRustcVmArm.Vm.LinearTranspose.b8Offset) NativeRustcVmArm.Vm.LinearTranspose.label_6_at), hregs, by omega, by omega, ?_, ?_,
      ?_, ?_, hg⟩)
    · show (s'.data.regs.getXReg .X8).toBitVec.toNat = _
      rw [h8, toNat_add_ofNat' (by rw [hx8]; omega), hx8, hrho]; omega
    · show (s'.data.regs.getXReg .X9).toBitVec = _
      rw [h9]; simp; rfl
    · show (s'.data.regs.getXReg .X10).toBitVec = _
      rw [h10, show env.base 1 = gA m0 + BitVec.ofNat 64 (16 * z) from rfl,
        show BitVec.ofInt 64 48 = BitVec.ofNat 64 48 from rfl, NativeRustcVm.addr_add_add]
      congr 2; omega
    · show (s'.data.regs.getXReg .X11).toBitVec.toNat = _
      rw [h11, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega), hx11]; simp; omega

end

end NativeRustcVmArm.KeccakGkr.LinearTranspose
