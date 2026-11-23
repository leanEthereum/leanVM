module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.KeccakGkr.FirstClaim.Pro

/-!
# `first_claim`: the bit weights

`.LFirstClaim_2` (`b3`) loads lane `(j / 64) % 32` (`lane_addr`) and calls `EW::mul` by
`1 << (j % 64)`; `b4` stores the product at bit weight `j` (`w_step`, `w_loop`, to `WDone`).
-/

namespace NativeRustcVmArm.KeccakGkr.FirstClaim

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVmArm.Vm.FirstClaim NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVm (Region)
open NativeRustcVm.KeccakGkr (claimBytes weightsBytes)

@[expose] public section

/-- **The bit weights done**. -/
structure WDone [Labels] (m0 : MachineData) (lanePoint : Array EW) (st : MachineData) : Prop where
  body : Body m0 st
  args : Args m0 st
  x21 : st.regs.X21 = m0.regs.X6
  x25 : st.regs.X25 = m0.regs.X5
  lanes : NativeRustcVm.EWsAt st.dmem (fbA m0 + BitVec.ofNat 64 16) (eqKernel lanePoint).toList
  c1 : NativeRustcVm.WordAt st.dmem (fbA m0 + BitVec.ofNat 64 8) m0.regs.X7
  w : ElemsAt st.dmem (wtsA m0) (wOf (eqKernel lanePoint)) 1600

end

public section

theorem ubfm_6_10 (x : BitVec 64) :
    (UnOp.apply (.ubfm 6 10) .W64 x).toNat = x.toNat / 64 % 32 := by
  simp only [UnOp.apply, low_W64, ext_W64, evalUBFM]
  rw [ite_eq_left (by decide)]
  simp [BitVec.take, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

/-- **A lane's address**: lane `(j / 64) % 32` of the lanes at X26. -/
theorem lane_addr [Labels] (env : Env) {a : BitVec 64} {j : Nat} (h26 : env.regs .X26 = a)
    (h20 : (env.regs .X20).toNat = j) :
    laneAddr.eval env = a + BitVec.ofNat 64 (16 * (j / 64 % 32)) := by
  have h1 := ubfm_6_10 (env.regs .X20)
  show BinOp.apply .add .W64 (env.regs .X26)
    (UnOp.apply (.shift .LSL 4) .W64 (UnOp.apply (.ubfm 6 10) .W64 (env.regs .X20))) = _
  generalize UnOp.apply (.ubfm 6 10) .W64 (env.regs .X20) = u at h1 ⊢
  rw [h20] at h1
  simp only [BinOp.apply, UnOp.apply, low_W64, ext_W64, shiftW, shl4]
  rw [h26, h1]

/-- `1 << (j % 64)` as rustc computes it. -/
theorem shl_one (j : Nat) :
    UInt64.ofBitVec (BinOp.apply .lslv .W64 (BitVec.ofNat 64 1) (BitVec.ofNat 64 j)) =
      (1 : UInt64) <<< (j % 64).toUInt64 := by
  apply UInt64.toBitVec_inj.mp
  simp only [BinOp.apply, low_W64, ext_W64, UInt64.toBitVec_shiftLeft]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft]

variable [NativeRustcArm.Host] {inst segment lanePoint output : Array EW} {m0 : MachineData} {k : Nat}

/-- **A turn of the bit weights' loop**. -/
theorem w_step (hp : Placed code k) (hpre : FirstClaimPre inst segment lanePoint output m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {j : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FirstClaim.b3Offset)) (hI : WInv m0 lanePoint j s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FirstClaim.b3Offset) ∧
        WInv m0 lanePoint (j + 1) s'.data) ∨ (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FirstClaim.b5Offset) ∧
        WDone m0 lanePoint s'.data)) s := by
  have hS := hpre.1
  have hA := pre_areas hpre
  have hj := hI.j_lt
  have hlp : lanePoint.size = 5 := hpre.2.2.2.2.2.2.1
  have hlen : (eqKernel lanePoint).size = 32 := by
    rw [NativeVm.Math.Keccak.eqKernel_size, hlp]; rfl
  have hq : j / 64 % 32 = j / 64 := Nat.mod_eq_of_lt (by omega)
  -- `b3`: the lane, `EW::mul`
  have hl := local_readable hpre hI.body (o := 16 + 16 * (j / 64)) (n := 16) (by omega)
  have hwf1 := wf_one (m := s.data) hl.1 hl.2
  have hm1 : Match (Env.ofMachine s.data [(fbA m0 + BitVec.ofNat 64 (16 + 16 * (j / 64)), 16)])
      laneS s.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl trivial trivial trivial
      ⟨by
        show laneAddr.eval _ = _ + BitVec.ofInt 64 0
        rw [lane_addr (Env.ofMachine s.data [(fbA m0 + BitVec.ofNat 64 (16 + 16 * (j / 64)), 16)])
            hI.x26 hI.x20, show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl,
          NativeRustcVm.addr_add_zero, NativeRustcVm.addr_add_add, hq]
        rfl, trivial⟩
  refine exec_at (b3_in_code.trans hp.1 (by simp [b3])) e3 hwf1 hpc hm1 fun s1 hm1' hpc1 ↦ ?_
  have hb1 : Body m0 s1.data := hI.body.of_block hm1 hm1' hwf1 rfl all_slots (by decide)
  have k1 := KeccakGkr.Match.regs_keep hm1 hm1'
    [.X19, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29] (by decide)
  have hd1 : s1.data.dmem = s.data.dmem := hm1'.dmem_eq hwf1 rfl
  have hlane := ewsAt_getD hI.lanes (i := j / 64) (by rw [hlen]; omega)
  rw [NativeRustcVm.addr_add_add, ← NativeRustcVm.addr_add_zero (_ + _)] at hlane
  obtain ⟨hw0, hw1⟩ := load_ew (env := Env.ofMachine s.data
    [(fbA m0 + BitVec.ofNat 64 (16 + 16 * (j / 64)), 16)]) (r := 0) hlane
  refine call_then hpc1 hmul (hb1.stackOk hS (by decide) (by decide)) fun s2 hpc2 hpost2 ↦ ?_
  obtain ⟨hp0, hp1, hsame2, hsv2⟩ := hpost2
  have hb2 : Body m0 s2.data :=
    hb1.call hS (n := ewMulStack) (by decide) slots_le' (wsOff hpre) hsame2 (fun _ h ↦ Or.inl h)
      hsv2
  have hprod : (⟨s2.data.regs.X0, s2.data.regs.X1⟩ : EW) = wOf (eqKernel lanePoint) j := by
    rw [hp0, hp1, wOf]
    have e0 : s1.data.regs.X0 = ((eqKernel lanePoint).getD (j / 64) 0).c0 :=
      UInt64.toBitVec_inj.mp ((hm1'.regs .X0 _ rfl).trans hw0)
    have e1 : s1.data.regs.X1 = ((eqKernel lanePoint).getD (j / 64) 0).c1 :=
      UInt64.toBitVec_inj.mp ((hm1'.regs .X1 _ rfl).trans hw1)
    have e2 : s1.data.regs.X2 = (1 : UInt64) <<< (j % 64).toUInt64 := by
      rw [← shl_one j]
      apply UInt64.toBitVec_inj.mp
      show (s1.data.regs.getXReg .X2).toBitVec = _
      rw [hm1'.regs .X2 _ rfl]
      show BinOp.apply .lslv .W64 (s.data.regs.getXReg .X29).toBitVec
        (s.data.regs.getXReg .X20).toBitVec = _
      have h29 : (s.data.regs.getXReg .X29).toBitVec = BitVec.ofNat 64 1 := by
        show s.data.regs.X29.toBitVec = _; rw [hI.x29]; rfl
      have h20 : (s.data.regs.getXReg .X20).toBitVec = BitVec.ofNat 64 j := by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact hI.x20
      rw [h29, h20, UInt64.toBitVec_ofBitVec]
    have e3 : s1.data.regs.X3 = 0 := UInt64.toBitVec_inj.mp (hm1'.regs .X3 _ rfl)
    rw [e0, e1, e2, e3]
    rfl
  -- `b4`: the store
  have hwr : ⟨wtsA m0, weightsBytes⟩ ∈ wsOf m0 := by simp
  have hwok := Areas.ok hA (Or.inl hwr)
  obtain ⟨hwm, hwn⟩ := sub_ok hwok (o := 16 * j) (n := 16) (by show 16 * j + 16 ≤ 25600; omega)
  have hwf3 := wf_one (m := s2.data) (Mapped.kept' hwm hb2.kept) hwn
  have hk2 : ∀ r ∈ [XReg.X19, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
      s2.data.regs.getXReg r = s.data.regs.getXReg r := by
    intro r hr
    rw [← k1 r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hsv2.1 _ rfl
  have hm3 : Match (Env.ofMachine s2.data [(wtsA m0 + BitVec.ofNat 64 (16 * j), 16)]) storeS
      s2.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
      ⟨by
        show (s2.data.regs.getXReg .X27).toBitVec =
          (wtsA m0 + BitVec.ofNat 64 (16 * j)) + BitVec.ofInt 64 8
        rw [hk2 .X27 (by simp), show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl,
          NativeRustcVm.addr_add_add]
        exact hI.x27.trans (by congr 2; omega), trivial⟩ trivial trivial trivial
  refine exec_at (b4_in_code.trans hp.1 (by simp [b4])) e4 hwf3 hpc2 hm3 fun s3 hm3' hpc3 ↦ ?_
  have hwr3 : ∀ p, Written (Env.ofMachine s2.data [(wtsA m0 + BitVec.ofNat 64 (16 * j), 16)])
      (after b4 storeS) p → InRange (wtsA m0 + BitVec.ofNat 64 (16 * j)) 16 p := by
    rw [after_eq e4]
    exact fun p hw ↦ Written.inRange (r := 0) rfl hwn (by decide) hw
  rw [after_eq e4] at hwr3
  have hb3 : Body m0 s3.data :=
    hb2.write hS (by decide) slots_le' (wsOff hpre) hm3 hm3' hwf3 rfl all_slots (by decide)
      fun p hw ↦ ⟨⟨wtsA m0, weightsBytes⟩, hwr,
        inRange_mono (hwr3 p hw) (by show 16 * j + 16 ≤ 25600; omega)⟩
  have hso3 : SameOutside s2.data.dmem s3.data.dmem
      (InRange (wtsA m0 + BitVec.ofNat 64 (16 * j)) 16) :=
    fun p hp ↦ hm3'.sameOutside hwf3 p fun hw ↦ hp (hwr3 p hw)
  have hR3 : ∀ p, InRange (wtsA m0 + BitVec.ofNat 64 (16 * j)) 16 p →
      InRange (stackBelow s2.data 0) 0 p ∨ NativeRustcVm.InAny (wsOf m0) p := fun p h ↦
    Or.inr ⟨⟨wtsA m0, weightsBytes⟩, hwr, inRange_mono h (by show 16 * j + 16 ≤ 25600; omega)⟩
  have hR2 : ∀ p, InRange (stackBelow s1.data ewMulStack) ewMulStack p →
      InRange (stackBelow s1.data ewMulStack) ewMulStack p ∨ NativeRustcVm.InAny (wsOf m0) p :=
    fun _ h ↦ Or.inl h
  have k3 := KeccakGkr.Match.regs_keep hm3 hm3'
    [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X29] (by decide)
  -- the frame's locals and the bit weights kept
  have hlanes3 : NativeRustcVm.EWsAt s3.data.dmem (fbA m0 + BitVec.ofNat 64 16)
      (eqKernel lanePoint).toList :=
    local_keep hpre hb2 (local_keep hpre hb1 (hd1 ▸ hI.lanes) (by
      rw [length_flatMap_ewBytes, Array.length_toList, hlen]; decide) (by decide) hsame2 hR2)
      (by rw [length_flatMap_ewBytes, Array.length_toList, hlen]; decide) (by decide) hso3 hR3
  have hc13 : NativeRustcVm.WordAt s3.data.dmem (fbA m0 + BitVec.ofNat 64 8) m0.regs.X7 :=
    local_keep hpre hb2 (local_keep hpre hb1 (hd1 ▸ hI.c1) (by
      rw [NativeRustcVm.length_wordBytes]; decide) (by decide) hsame2 hR2)
      (by rw [NativeRustcVm.length_wordBytes]; decide) (by decide) hso3 hR3
  have hw2 : ElemsAt s2.data.dmem (wtsA m0) (wOf (eqKernel lanePoint)) j :=
    ws_keep_call hpre hb1 hwr (by decide) (by show 16 * j ≤ 25600; omega) (hd1 ▸ hI.w) hsame2
  have hw3 : ElemsAt s3.data.dmem (wtsA m0) (wOf (eqKernel lanePoint)) (j + 1) := by
    refine hw2.grow (k := 1) (show (wtsA m0).toNat + 16 * (j + 1) ≤ 2 ^ 64 from Nat.le_trans
      (Nat.add_le_add_left (show 16 * (j + 1) ≤ 25600 by omega) _) hwok.2)
      (by rw [Nat.mul_one]; exact hso3) fun i hi ↦ ?_
    obtain rfl : i = 0 := by omega
    have h := KeccakGkr.Match.ewAt_write hm3' (r := 0) (o := 0) rfl (by decide)
      (v0 := .reg .X0) (v1 := .reg .X1) (by decide +kernel) (by decide +kernel)
    rw [NativeRustcVm.addr_add_zero] at h
    rw [Nat.add_zero, ← hprod]
    exact h
  -- the counters
  have h28 := hm3'.regs .X28 _ rfl
  have hx28 : (s2.data.regs.getXReg .X28).toBitVec.toNat = 25600 - 16 * j := by
    rw [hk2 .X28 (by simp)]; exact hI.x28
  simp only [PcOk, NativeRustcVmArm.Vm.FirstClaim.b4_length, NativeRustcVmArm.Vm.FirstClaim.b4Length] at hpc3
  sym_simp at hpc3
  simp only [Env.ofMachine_regs] at hpc3
  have hargs : Args m0 s3.data :=
    ⟨(k3 .X19 (by simp)).trans ((hk2 .X19 (by simp)).trans hI.args.x19),
      (k3 .X22 (by simp)).trans ((hk2 .X22 (by simp)).trans hI.args.x22),
      (k3 .X23 (by simp)).trans ((hk2 .X23 (by simp)).trans hI.args.x23),
      (k3 .X24 (by simp)).trans ((hk2 .X24 (by simp)).trans hI.args.x24)⟩
  have h21 := (k3 .X21 (by simp)).trans ((hk2 .X21 (by simp)).trans hI.x21)
  have h25 := (k3 .X25 (by simp)).trans ((hk2 .X25 (by simp)).trans hI.x25)
  by_cases hlast : j = 1599
  · subst hlast
    have : (s2.data.regs.getXReg .X28).toBitVec = 16#64 :=
      BitVec.eq_of_toNat_eq (by rw [hx28]; rfl)
    simp only [this, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_false] at hpc3
    exact .done _ (Or.inr ⟨hpc3, hb3, hargs, h21, h25, hlanes3, hc13, hw3⟩)
  · have hne : ((s2.data.regs.getXReg .X28).toBitVec == 16#64) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      have := congrArg BitVec.toNat h
      rw [hx28] at this
      simp at this
      omega
    simp only [hne, Bool.not_false, ite_true] at hpc3
    refine .done _ (Or.inl ⟨hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.FirstClaim.b3Offset) NativeRustcVmArm.Vm.FirstClaim.label_2_at), hb3, hargs, h21, h25, ?_, ?_, ?_,
      ?_, ?_, by omega, hlanes3, hc13, hw3⟩)
    · show (s3.data.regs.getXReg .X26).toBitVec = _
      rw [k3 .X26 (by simp), hk2 .X26 (by simp)]; exact hI.x26
    · show (s3.data.regs.getXReg .X20).toBitVec.toNat = _
      rw [k3 .X20 (by simp), hsv2.1 .X20 rfl, hm1'.regs .X20 _ rfl]
      sym_simp
      simp only [Env.ofMachine_regs]
      rw [BitVec.toNat_add, show (s.data.regs.getXReg .X20).toBitVec.toNat = j from hI.x20]
      simp
      omega
    · show (s3.data.regs.getXReg .X27).toBitVec = _
      rw [hm3'.regs .X27 _ rfl]
      show wtsA m0 + BitVec.ofNat 64 (16 * j) + BitVec.ofInt 64 24 = _
      rw [show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl, NativeRustcVm.addr_add_add]
      congr 2
      omega
    · show (s3.data.regs.getXReg .X28).toBitVec.toNat = _
      rw [h28]
      sym_simp
      simp only [Env.ofMachine_regs]
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hx28]; simp; omega), hx28]
      simp
      omega
    · apply UInt64.toBitVec_inj.mp
      show (s3.data.regs.getXReg .X29).toBitVec = _
      rw [k3 .X29 (by simp), hk2 .X29 (by simp)]
      exact congrArg UInt64.toBitVec hI.x29

/-- **The bit weights' loop**, to its end. -/
theorem w_loop (hp : Placed code k) (hpre : FirstClaimPre inst segment lanePoint output m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {j : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FirstClaim.b3Offset)) (hI : WInv m0 lanePoint j s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FirstClaim.b5Offset) ∧
      WDone m0 lanePoint s'.data) s :=
  Sym.loop (fun n s ↦ ∃ j, n = 1600 - j ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FirstClaim.b3Offset) ∧ WInv m0 lanePoint j s.data)
    (fun _ s ⟨j, hn, hpc, hI⟩ ↦ (w_step hp hpre hmul hpc hI).mono fun s' h ↦ by
      rcases h with ⟨hpc', hI'⟩ | h
      · exact Or.inr ⟨1600 - (j + 1), by have := hI.j_lt; omega, j + 1, rfl, hpc', hI'⟩
      · exact Or.inl h)
    ⟨j, rfl, hpc, hI⟩

end

end NativeRustcVmArm.KeccakGkr.FirstClaim
