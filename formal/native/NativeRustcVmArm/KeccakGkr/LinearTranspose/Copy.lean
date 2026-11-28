module

public import NativeRustcVmArm.KeccakGkr.LinearTranspose.Defs

/-!
# `linear_transpose`: the copy loop of a lane

`.LLinearTranspose_4` (`b5`), for a lane `l ≠ 0`: element `z` of lane `l` of `g` is the weight at
position `(z + ρ_l) % 64` of lane `π l` (`gW`), copied from the lane at X9 (`w + 1024 π_l`) at the
index `x8 & 63`, `x8 = ρ_l + z`, to X11 - 8 (`Copy`). After the last, `.LLinearTranspose_1`'s
jump (`b6`): the lane done (`AfterLane`).
-/

namespace NativeRustcVmArm.KeccakGkr.LinearTranspose

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVmArm.Vm.LinearTranspose LeanVM.Parameters
open NativeRustcVm (Region)
open NativeRustcVm.KeccakGkr (gW colW outW weightsBytes)

@[expose] public section

/-- The lane loop's registers for lane `l`. -/
structure LaneRegs [Labels] (m0 st : MachineData) (l : Nat) : Prop where
  ctx : Ctx m0 st
  lt : l < 25
  x23 : st.regs.X23.toNat = l
  x24 : st.regs.X24.toBitVec = gA m0 + BitVec.ofNat 64 (8 + 1024 * l)
  x25 : st.regs.X25.toBitVec = gA m0 + BitVec.ofNat 64 (16 + 1024 * l)
  x26 : st.regs.X26.toBitVec = rhoAddr

/-- **The copy loop's head** after `z` elements of lane `l`. -/
structure Copy [Labels] (m0 : MachineData) (ws : Array EW) (l z : Nat) (st : MachineData) :
    Prop where
  regs : LaneRegs m0 st l
  z_lt : z < 64
  x8 : st.regs.X8.toNat = keccakRhoW.getD l 0 + z
  x9 : st.regs.X9.toBitVec = wA m0 + BitVec.ofNat 64 (1024 * keccakPi l)
  x10 : st.regs.X10.toNat = 64 - z
  x11 : st.regs.X11.toBitVec = gA m0 + BitVec.ofNat 64 (8 + 1024 * l + 16 * z)
  g : ElemsAt st.dmem (gA m0) (gF ws) (64 * l + z)

/-- **A lane done**: `g`'s first `64 (l + 1)` elements. -/
structure AfterLane [Labels] (m0 : MachineData) (ws : Array EW) (l : Nat) (st : MachineData) :
    Prop where
  regs : LaneRegs m0 st l
  g : ElemsAt st.dmem (gA m0) (gF ws) (64 * l + 64)

end

public section

variable [Labels] {ws : Array EW} {m0 st st' : MachineData}

/-- `LaneRegs` of a body with the same X19 to X26. -/
theorem LaneRegs.keep {l : Nat} (h : LaneRegs m0 st l) (hb : Body m0 st')
    (e : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26],
      st'.regs.getXReg r = st.regs.getXReg r) : LaneRegs m0 st' l := by
  have e' : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26],
      (st'.regs.getXReg r) = (st.regs.getXReg r) := e
  refine ⟨⟨hb, ?_, ?_, ?_, ?_⟩, h.lt, ?_, ?_, ?_, ?_⟩
  · exact (e' .X19 (by simp)).trans h.ctx.x19
  · exact (e' .X20 (by simp)).trans h.ctx.x20
  · exact (e' .X21 (by simp)).trans h.ctx.x21
  · exact (e' .X22 (by simp)).trans h.ctx.x22
  · show (st'.regs.getXReg .X23).toNat = l; rw [e' .X23 (by simp)]; exact h.x23
  · show (st'.regs.getXReg .X24).toBitVec = _; rw [e' .X24 (by simp)]; exact h.x24
  · show (st'.regs.getXReg .X25).toBitVec = _; rw [e' .X25 (by simp)]; exact h.x25
  · show (st'.regs.getXReg .X26).toBitVec = _; rw [e' .X26 (by simp)]; exact h.x26

omit [Labels] in
theorem pi_lt {l : Nat} (hl : l < 25) : keccakPi l < 25 := by
  unfold keccakPi; omega

omit [Labels] in
/-- `(x & 63) << 4` as a number. -/
theorem idx63_toNat (x : BitVec 64) :
    (UnOp.apply (.shift .LSL 4) .W64 (BinOp.apply .and .W64 x (BitVec.ofNat 64 63))).toNat =
      16 * (x.toNat % 64) := by
  simp only [UnOp.apply, BinOp.apply, low_W64, ext_W64, shiftW, BitVec.toNat_shiftLeft,
    BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (63 : Nat) % 2 ^ 64 = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftLeft_eq]
  have := Nat.mod_lt x.toNat (show 2 ^ 6 > 0 by decide)
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

omit [Labels] in
/-- `(x & 63) << 4` as a number, as `sym_simp` leaves it. -/
theorem idx63_toNat' (x : BitVec 64) : ((x &&& 63#64) <<< 4).toNat = 16 * (x.toNat % 64) := by
  have := idx63_toNat x
  simpa [UnOp.apply, BinOp.apply, shiftW] using this

omit [Labels] in
theorem and63_lt (x : BitVec 64) : (BinOp.apply .and .W64 x (BitVec.ofNat 64 63)).toNat < 64 := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_and, BitVec.toNat_ofNat]
  have := Nat.and_le_right (n := x.toNat) (m := 63 % 2 ^ 64)
  simp only [show (63 : Nat) % 2 ^ 64 = 63 from rfl] at this ⊢
  omega

/-- An element of a lane of the weights, as the copy loop reads it. -/
theorem lane_elem (hpre : LinearTransposePre ws m0) (hb : Body m0 st) {l q : Nat} (hl : l < 25)
    (hq : q < 64) :
    NativeRustcVm.EWAt st.dmem (wA m0 + BitVec.ofNat 64 (1024 * keccakPi l) + BitVec.ofNat 64 (16 * q))
      (ws.getD (64 * keccakPi l + q) 0) := by
  have hpi := pi_lt hl
  rw [NativeRustcVm.addr_add_add, show 1024 * keccakPi l + 16 * q = 16 * (64 * keccakPi l + q) by omega]
  exact w_at hpre hb (by omega)

end

public section

variable [NativeRustcArm.Host] {ws : Array EW} {m0 : MachineData} {k : Nat}

/-- **One element of the copy loop**. -/
theorem copy_step (hp : Placed code k) (hpre : LinearTransposePre ws m0) {l z : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b5Offset)) (hI : Copy m0 ws l z s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b5Offset) ∧ Copy m0 ws l (z + 1) s'.data) ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b6Offset) ∧ AfterLane m0 ws l s'.data)) s := by
  have hS := hpre.1
  have hA := pre_areas hpre
  have hl := hI.regs.lt
  have hz := hI.z_lt
  have hpi := pi_lt hl
  have hrho := rho_lt hl
  have hgok := Areas.ok hA (r := ⟨gA m0, weightsBytes⟩) (Or.inl (by simp [wsR]))
  have hwok := Areas.ok hA (r := ⟨wA m0, weightsBytes⟩) (Or.inr (by simp [rsR]))
  have hgw := Areas.apart_rs hA (w := ⟨gA m0, weightsBytes⟩) (r := ⟨wA m0, weightsBytes⟩)
    (by simp [wsR]) (by simp [rsR])
  set n := 64 * l + z with hn
  have hn' : n < 1600 := by omega
  obtain ⟨hm0, hnw0⟩ := sub_ok hwok (o := 1024 * keccakPi l) (n := 1024)
    (by show 1024 * keccakPi l + 1024 ≤ 25600; omega)
  obtain ⟨hm1, hnw1⟩ := sub_ok hgok (o := 16 * n) (n := 16)
    (by show 16 * n + 16 ≤ 25600; omega)
  have hap : Apart (wA m0 + BitVec.ofNat 64 (1024 * keccakPi l)) 1024
      (gA m0 + BitVec.ofNat 64 (16 * n)) 16 :=
    Apart.sub (NativeRustcVm.Apart.symm hgw) hwok.2 hgok.2
      (by show 1024 * keccakPi l + 1024 ≤ 25600; omega) (by show 16 * n + 16 ≤ 25600; omega)
      (by decide) (by decide)
  let env := Env.ofMachine s.data [(wA m0 + BitVec.ofNat 64 (1024 * keccakPi l), 1024),
    (gA m0 + BitVec.ofNat 64 (16 * n), 16)]
  have hwf : env.WF := Env.wf_of
    ⟨⟨Mapped.kept' hm0 hI.regs.ctx.body.kept, hnw0⟩, ⟨Mapped.kept' hm1 hI.regs.ctx.body.kept, hnw1⟩,
      trivial⟩ (List.pairwise_pair.mpr hap)
  have hm : Match env copyS s.data :=
    match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl
      ⟨by
        show (s.data.regs.getXReg .X9).toBitVec = _ + BitVec.ofInt 64 0
        rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
        exact hI.x9,
       by
        show (s.data.regs.getXReg .X11).toBitVec = (gA m0 + BitVec.ofNat 64 (16 * n)) + BitVec.ofInt 64 8
        rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add]
        rw [show (s.data.regs.getXReg .X11) = s.data.regs.X11 from rfl, hI.x11]
        congr 2
        omega,
       trivial⟩ trivial ⟨and63_lt _, trivial⟩ trivial
  refine exec_at (b5_in_code.trans hp.1 (by simp [b5])) e5 hwf hpc hm fun s' hm' hpc' ↦ ?_
  -- the element
  have hel : NativeRustcVm.EWAt s'.data.dmem (gA m0 + BitVec.ofNat 64 (16 * n) + BitVec.ofNat 64 0)
      (gF ws n) := by
    have h := KeccakGkr.Match.ewAt_write2 hm' (pre := []) rfl rfl nofun (r := 1) rfl (by decide)
    have hq : (keccakRhoW.getD l 0 + z) % 64 < 64 := Nat.mod_lt _ (by decide)
    have hx := load_ew (env := env) (r := 0) (o := 16 * ((keccakRhoW.getD l 0 + z) % 64))
      (lane_elem hpre hI.regs.ctx.body hl hq)
    sym_simp at h
    rw [idx63_toNat'] at h
    rw [show (env.regs .X8).toNat = s.data.regs.X8.toNat from rfl, hI.x8,
      Nat.zero_add, Nat.add_comm 8, hx.1, hx.2] at h
    convert h using 1
    show gW ws (n / 64) (n % 64) = _
    rw [show n / 64 = l by omega, show n % 64 = z by omega, gW, Nat.add_comm z]
  -- what the block wrote: the element, in `g`
  have hso : SameOutside s.data.dmem s'.data.dmem (InRange (gA m0 + BitVec.ofNat 64 (16 * n)) 16) :=
    NativeRustcVm.SameOutside.mono (hm'.sameOutside hwf) fun p h ↦
      Written.inRange (r := 1) rfl hnw1 (by decide) h
  have hbody : Body m0 s'.data :=
    hI.regs.ctx.body.write hS (by decide) slots_le (wsOff hpre) hm hm' hwf rfl free_ok (by decide)
      fun p h ↦ ⟨⟨gA m0, weightsBytes⟩, by simp [wsR],
        inRange_mono (Written.inRange (r := 1) rfl hnw1 (by decide) h)
          (by show 16 * n + 16 ≤ 25600; omega)⟩
  have hkeep := KeccakGkr.Match.regs_keep hm hm' [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26]
    (by decide)
  have hregs := hI.regs.keep hbody hkeep
  have hg : ElemsAt s'.data.dmem (gA m0) (gF ws) (n + 1) :=
    hI.g.grow (NativeRustcVm.NoWrap.sub (o := 0) (by rw [NativeRustcVm.addr_add_zero] at *; exact hgok.2)
        (by show 0 + 16 * (n + 1) ≤ 25600; omega) |>.trans_eq' (by rw [NativeRustcVm.addr_add_zero]))
      (by rw [Nat.mul_one]; exact hso) fun j hj ↦ by
        obtain rfl : j = 0 := by omega
        rw [Nat.add_zero]
        rw [NativeRustcVm.addr_add_zero] at hel
        exact hel
  have h8 := hm'.regs .X8 _ rfl
  have h9 := hm'.regs .X9 _ rfl
  have h10 := hm'.regs .X10 _ rfl
  have h11 := hm'.regs .X11 _ rfl
  sym_simp at h8 h9 h10 h11
  have hx8 : (env.regs .X8).toNat = keccakRhoW.getD l 0 + z := hI.x8
  have hx10 : (env.regs .X10).toNat = 64 - z := hI.x10
  simp only [PcOk] at hpc'
  sym_simp at hpc'
  by_cases hlast : z = 63
  · have hc : (env.regs .X10 == 1#64) = true := by
      rw [beq_iff_eq]; apply BitVec.eq_of_toNat_eq; rw [hx10]; simp; omega
    simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false, NativeRustcVmArm.Vm.LinearTranspose.b5_length, NativeRustcVmArm.Vm.LinearTranspose.b5Length] at hpc'
    refine .done _ (Or.inr ⟨hpc', hregs, ?_⟩)
    rw [show 64 * l + 64 = n + 1 by omega]
    exact hg
  · have hc : (env.regs .X10 == 1#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have := congrArg BitVec.toNat h; rw [hx10] at this
      simp at this; omega
    simp only [hc, Bool.not_false, ite_true] at hpc'
    refine .done _ (Or.inl ⟨hpc'.trans (hp.label (j := NativeRustcVmArm.Vm.LinearTranspose.b5Offset) NativeRustcVmArm.Vm.LinearTranspose.label_4_at), hregs, by omega, ?_, ?_, ?_, ?_, ?_⟩)
    · show (s'.data.regs.getXReg .X8).toBitVec.toNat = _
      rw [h8, toNat_add_ofNat' (by rw [hx8]; omega), hx8]; omega
    · show (s'.data.regs.getXReg .X9).toBitVec = _
      rw [h9]; simp; rfl
    · show (s'.data.regs.getXReg .X10).toBitVec.toNat = _
      rw [h10, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega), hx10]; simp; omega
    · show (s'.data.regs.getXReg .X11).toBitVec = _
      rw [h11, show env.base 1 = gA m0 + BitVec.ofNat 64 (16 * n) from rfl,
        show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl, NativeRustcVm.addr_add_add]
      congr 2; omega
    · rw [show 64 * l + (z + 1) = n + 1 by omega]; exact hg

end

end NativeRustcVmArm.KeccakGkr.LinearTranspose
