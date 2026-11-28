module

public import NativeRustcVmArm.Layout.StackOffsets.Base

/-!
# `stack_offsets`: the order array `0, 1, …, n - 1` (`b3`-`b12`)

After `memset`, `b3` keeps `8 n` in X23; with no block (`b6`) straight to the sort. Below four
blocks (`b4`, `b5`) one store at a time (`b10`, the loop `b11`, `Inv11`); from four on, `b7`
writes four words a turn (the loop `b8`, `Inv8`) up to `n / 4 * 4`, and `b9`, `b10`, `b11` the rest.
`b12` sets the sort's arguments: `Ready` at `b13` (`init_spec`).
-/

namespace NativeRustcVmArm.Layout.StackOffsets

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.StackOffsets
open NativeRustcVmArm.Arrays (regs_eq_of)
open NativeRustcVm (WordAt)

public section

/-- **Writing the order array**: `j` words written. -/
structure Init (m0 : MachineData) (j : Nat) (st : MachineData) : Prop where
  fr : Fr m0 st
  regs : Regs m0 st
  x23 : st.regs.X23.toNat = 8 * n m0
  ords : Ords m0 j st.dmem
  le : j ≤ n m0

/-- The registers `Init` reads. -/
def initRegs : List XReg := [.X19, .X20, .X21, .X22, .X23, .X24]

theorem regsList_sub : ∀ r ∈ regsList, r ∈ initRegs := by
  intro r hr
  simp only [regsList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [initRegs]

theorem Init.of {m0 st st' : MachineData} {j : Nat} (h : Init m0 j st) (fr : Fr m0 st')
    (he : ∀ r ∈ initRegs, st'.regs.getXReg r = st.regs.getXReg r) (hd : st'.dmem = st.dmem) :
    Init m0 j st' :=
  ⟨fr, h.regs.of fun r hr ↦ he r (regsList_sub r hr), by
    rw [show st'.regs.X23 = st.regs.X23 from he .X23 (by simp [initRegs])]; exact h.x23,
    hd ▸ h.ords, h.le⟩

/-- **At `b13`**: the order array written, the sort's arguments set. -/
structure Ready (m0 : MachineData) (st : MachineData) : Prop where
  init : Init m0 (n m0) st
  x0 : st.regs.X0.toBitVec = fb m0
  x1 : st.regs.X1.toNat = n m0
  x2 : st.regs.X2 = m0.regs.X0
  x3 : st.regs.X3.toNat = n m0

/-- **The quadruple loop's head** `.LStackOffsets_7`. -/
structure Inv8 (m0 : MachineData) (q : Nat) (st : MachineData) : Prop where
  init : Init m0 (4 * q) st
  lt : 4 * q + 4 ≤ n m0 / 4 * 4
  x8 : st.regs.X8.toNat = n m0 / 4 * 4
  x9 : st.regs.X9.toBitVec = fb m0 + BitVec.ofNat 64 (8 * (n m0 / 4 * 4))
  x10 : st.regs.X10.toNat = n m0
  x11 : st.regs.X11.toBitVec = fb m0 + BitVec.ofNat 64 (32 * q + 16)
  x12 : st.regs.X12.toNat = 4 * q + 1

/-- **The single loop's head** `.LStackOffsets_10`. -/
structure Inv11 (m0 : MachineData) (j : Nat) (st : MachineData) : Prop where
  init : Init m0 j st
  lt : j < n m0
  x8 : st.regs.X8.toNat = j
  x9 : st.regs.X9.toBitVec = fb m0 + BitVec.ofNat 64 (8 * j)
  x10 : st.regs.X10.toBitVec = fb m0 + BitVec.ofNat 64 (8 * n m0)

/-- `lsl #3` (`ubfm #61, #60`): times `8`. -/
theorem lsl3 (x : BitVec 64) :
    UnOp.apply (.ubfm 61 60) .W64 x = BitVec.ofNat 64 (8 * x.toNat) := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
  apply BitVec.eq_of_toNat_eq
  simp [evalUBFM, Arrays.toNat_take', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- `lsr #3` (`ubfm #3, #63`). -/
theorem lsr3 (v : BitVec 64) : (UnOp.apply (.ubfm 3 63) .W64 v).toNat = v.toNat / 2 ^ 3 := by
  simp only [UnOp.apply, Sym.low_W64, Sym.ext_W64, evalUBFM, BitVec.take]
  have hw : RegWidth.W64.bits = 64 := rfl
  simp only [hw]
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem and_mask : ∀ x : Fin 159, x.val &&& 4611686018427387900 = x.val / 4 * 4 := by decide

theorem shl3_toNat (x : BitVec 64) (h : x.toNat < 2 ^ 61) :
    (shiftW .LSL x 3).toNat = 8 * x.toNat := by
  simp only [shiftW, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

variable [Host] {k : Nat}

/-- At `b12`: the order array written. -/
abbrev At12 (k : Nat) (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b12Offset) ∧ Init m0 (n m0) s.data

/-- At `b13`. -/
abbrev At13 (k : Nat) (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b13Offset) ∧ Ready m0 s.data

/-- `b12`: the sort's arguments. -/
theorem l12 (hp : Placed code k) {m0 : MachineData} (hS : StackOk m0 1328) {st : MachineState}
    (h : At12 k m0 st) : Eventually (step1 Host.exe) (At13 k m0) st := by
  obtain ⟨hpc, hI⟩ := h
  refine run_regs hS (infix_of b12_in_code (by simp [b12]) hp) run_b12
    (after_eq run_b12 ▸ b12_keeps) hpc hI.fr fun st' hm hpc' hfr hd ↦ .done _ ⟨hpc', ?_⟩
  refine ⟨hI.of hfr (regs_eq_of (match_nil _) hm initRegs rfl) hd, ?_, ?_, ?_, ?_⟩
  · show (st'.data.regs.getXReg .X0).toBitVec = _
    rw [hm.regs .X0 _ rfl]
    exact hI.fr.sp
  · show (st'.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [hm.regs .X1 _ rfl]
    exact congrArg UInt64.toNat hI.regs.x21
  · exact (UInt64.toBitVec_inj.mp (hm.regs .X2 _ rfl)).trans hI.regs.x22
  · show (st'.data.regs.getXReg .X3).toBitVec.toNat = _
    rw [hm.regs .X3 _ rfl]
    exact congrArg UInt64.toNat hI.regs.x21

/-- **A turn of the single loop** `b11`: word `j` written. -/
theorem step11 (hp : Placed code k) {m0 : MachineData} (hS : StackOk m0 1328)
    (hn : n m0 ≤ 158) {j : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b11Offset))
    (hI : Inv11 m0 j st.data) :
    Eventually (step1 Host.exe) (fun s ↦ At12 k m0 s ∨
      (s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b11Offset) ∧ Inv11 m0 (j + 1) s.data)) st := by
  have hj := hI.lt
  have hrd : Readable st.data (fb m0 + BitVec.ofNat 64 (8 * j)) 8 :=
    frame_readable hS (Nat.le_refl _) hI.init.fr (by omega)
  have hwf := Arrays.wf_one hrd.1 hrd.2 (m := st.data)
  have hm : Match (Env.ofMachine st.data [(fb m0 + BitVec.ofNat 64 (8 * j), 8)]) wordS st.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl ⟨by
      show _ = fb m0 + BitVec.ofNat 64 (8 * j) + BitVec.ofInt 64 0
      rw [ofInt_zero, BitVec.add_zero]; exact hI.x9, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b11_in_code (by simp [b11]) hp) run_b11 hwf hpc hm fun st' hm' hpc' ↦ ?_
  obtain ⟨hk, hw, hv⟩ := after_eq run_b11 ▸ b11_facts
  have hfr := Fr.of_ords hS (o := 8 * j) (len := 8) (by omega) hI.init.fr hm hm' hwf hk hw
  have hsame := same_of_region hm' hwf (r := 0) rfl hw
  have w0 := Match.wordAt_write hm' (r := 0) (o := 0) rfl (by decide) hv
  have he := regs_eq_of hm hm' (.X10 :: initRegs) rfl
  have hords : Ords m0 (j + 1) st'.data.dmem := hI.init.ords.step (fb_noWrap hS) (by omega)
    hsame fun t h1 h2 ↦ by
      obtain rfl : t = j := by omega
      rw [NativeRustcVm.addr_add_zero] at w0
      rw [← u64_eq (v := st.data.regs.X8.toBitVec) hI.x8]
      exact w0
  have hinit : Init m0 (j + 1) st'.data :=
    ⟨hfr, hI.init.regs.of fun r hr ↦ he r (List.mem_cons_of_mem _ (regsList_sub r hr)), by
      rw [show st'.data.regs.X23 = st.data.regs.X23 from he .X23 (by simp [initRegs])]
      exact hI.init.x23, hords, by omega⟩
  have hfb := fb_toNat hS
  have h9 : (st'.data.regs.getXReg .X9).toBitVec = fb m0 + BitVec.ofNat 64 (8 * (j + 1)) := by
    rw [hm'.regs .X9 _ rfl]
    show fb m0 + BitVec.ofNat 64 (8 * j) + BitVec.ofInt 64 8 = _
    rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add,
      show 8 * j + 8 = 8 * (j + 1) by omega]
  have h10 : (st.data.regs.getXReg .X10).toBitVec.toNat = (fb m0).toNat + 8 * n m0 := by
    show st.data.regs.X10.toBitVec.toNat = _
    rw [hI.x10, fb_add hS (by omega)]
  have hx : (fb m0 + BitVec.ofNat 64 (8 * j) + BitVec.ofInt 64 8).toNat =
      (fb m0).toNat + 8 * (j + 1) := by
    rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add,
      fb_add hS (by omega)]
    omega
  simp only [PcOk, NativeRustcVmArm.Vm.StackOffsets.b11_length, NativeRustcVmArm.Vm.StackOffsets.b11Length] at hpc'
  obtain ⟨hy, hno⟩ := pc_of (P := (fb m0).toNat + 8 * (j + 1) ≠ (fb m0).toNat + 8 * n m0) hpc'
    (by sym_simp; exact nbeq_dec hx h10)
  by_cases hlast : j + 1 = n m0
  · exact .done _ (Or.inl ⟨hno (by omega), hlast ▸ hinit⟩)
  · refine .done _ (Or.inr ⟨(hy (by omega)).trans (lbl_10 hp), hinit, by omega, ?_, h9, ?_⟩)
    · show (st'.data.regs.getXReg .X8).toBitVec.toNat = _
      rw [hm'.regs .X8 _ rfl]
      sym_simp
      exact add_lit (a := j) hI.x8 (by omega)
    · rw [show st'.data.regs.X10 = st.data.regs.X10 from he .X10 (by simp)]
      exact hI.x10

/-- **The single loop**, to `b12`. -/
theorem loop11 (hp : Placed code k) {m0 : MachineData} (hS : StackOk m0 1328)
    (hn : n m0 ≤ 158) {j : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b11Offset))
    (hI : Inv11 m0 j st.data) : Eventually (step1 Host.exe) (At12 k m0) st := by
  refine Sym.loop (fun r s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b11Offset) ∧ ∃ j, n m0 - j = r ∧ Inv11 m0 j s.data)
    (fun r s ⟨hpc, j, hr, hI⟩ ↦ ?_) ⟨hpc, j, rfl, hI⟩
  refine Eventually.mono (step11 hp hS hn hpc hI) fun s' h ↦ ?_
  rcases h with h | ⟨hpc', hI'⟩
  · exact Or.inl h
  · exact Or.inr ⟨n m0 - (j + 1), by have := hI'.lt; omega, hpc', j + 1, rfl, hI'⟩

/-- `b10`: the single loop's end address. -/
theorem l10 (hp : Placed code k) {m0 : MachineData} (hS : StackOk m0 1328) (hn : n m0 ≤ 158)
    {j : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b10Offset)) (hI : Init m0 j st.data)
    (hj : j < n m0) (h8 : st.data.regs.X8.toNat = j)
    (h9 : st.data.regs.X9.toBitVec = fb m0 + BitVec.ofNat 64 (8 * j)) :
    Eventually (step1 Host.exe) (At12 k m0) st :=
  run_regs hS (infix_of b10_in_code (by simp [b10]) hp) run_b10 (after_eq run_b10 ▸ b10_keeps)
    hpc hI.fr fun st' hm hpc' hfr hd ↦ by
      have he := regs_eq_of (match_nil _) hm (.X8 :: .X9 :: initRegs) rfl
      refine loop11 hp hS hn hpc' ⟨hI.of hfr (fun r hr ↦ he r (by simp [hr])) hd, hj, ?_, ?_, ?_⟩
      · rw [show st'.data.regs.X8 = st.data.regs.X8 from he .X8 (by simp)]; exact h8
      · rw [show st'.data.regs.X9 = st.data.regs.X9 from he .X9 (by simp)]; exact h9
      · show (st'.data.regs.getXReg .X10).toBitVec = _
        rw [hm.regs .X10 _ rfl]
        sym_simp
        simp only [Env.ofMachine_regs]
        have h23 : (st.data.regs.getXReg .X23).toBitVec = BitVec.ofNat 64 (8 * n m0) := by
          apply BitVec.eq_of_toNat_eq
          rw [lit_toNat (by omega)]
          exact hI.x23
        rw [show (st.data.regs.getXReg .X24).toBitVec = fb m0 from hI.regs.x24, h23]

/-- **A turn of the quadruple loop** `b8`: words `4q` to `4q + 3` written. -/
theorem step8 (hp : Placed code k) {m0 : MachineData} (hS : StackOk m0 1328)
    (hn : n m0 ≤ 158) {q : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b8Offset))
    (hI : Inv8 m0 q st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b9Offset) ∧
        Init m0 (n m0 / 4 * 4) s.data ∧ s.data.regs.X8.toNat = n m0 / 4 * 4 ∧
        s.data.regs.X9.toBitVec = fb m0 + BitVec.ofNat 64 (8 * (n m0 / 4 * 4)) ∧
        s.data.regs.X10.toNat = n m0) ∨
      (s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b8Offset) ∧ Inv8 m0 (q + 1) s.data)) st := by
  have hlt := hI.lt
  have hN : n m0 / 4 * 4 ≤ n m0 := Nat.div_mul_le_self _ _
  have hrd : Readable st.data (fb m0 + BitVec.ofNat 64 (32 * q)) 32 :=
    frame_readable hS (Nat.le_refl _) hI.init.fr (by omega)
  have hwf := Arrays.wf_one hrd.1 hrd.2 (m := st.data)
  have hm : Match (Env.ofMachine st.data [(fb m0 + BitVec.ofNat 64 (32 * q), 32)]) quadS
      st.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl ⟨by
      show _ = fb m0 + BitVec.ofNat 64 (32 * q) + BitVec.ofInt 64 ((16 : Nat) : Int)
      rw [Arrays.ofInt_eq_ofNat, NativeRustcVm.addr_add]; exact hI.x11, trivial⟩
      trivial trivial trivial
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8 hwf hpc hm fun st' hm' hpc' ↦ ?_
  obtain ⟨hk, hw, hv0, hv1, hv2, hv3⟩ := after_eq run_b8 ▸ b8_facts
  have hfr := Fr.of_ords hS (o := 32 * q) (len := 32) (by omega) hI.init.fr hm hm' hwf hk hw
  have hsame := same_of_region hm' hwf (r := 0) rfl hw
  have w0 := Match.wordAt_write hm' (r := 0) (o := 0) rfl (by decide) hv0
  have w1 := Match.wordAt_write hm' (r := 0) (o := 8) rfl (by decide) hv1
  have w2 := Match.wordAt_write hm' (r := 0) (o := 16) rfl (by decide) hv2
  have w3 := Match.wordAt_write hm' (r := 0) (o := 24) rfl (by decide) hv3
  have h12 : (st.data.regs.getXReg .X12).toBitVec.toNat = 4 * q + 1 := hI.x12
  have e0 : UInt64.ofBitVec ((Sym.bin .sub .W64 (.reg .X12) (.lit 1)).eval
      (Env.ofMachine st.data [(fb m0 + BitVec.ofNat 64 (32 * q), 32)])) = (4 * q).toUInt64 :=
    u64_eq (by sym_simp; exact sub_lit (c := 1) h12 (by omega))
  have e1 : UInt64.ofBitVec ((Sym.reg .X12).eval
      (Env.ofMachine st.data [(fb m0 + BitVec.ofNat 64 (32 * q), 32)])) = (4 * q + 1).toUInt64 :=
    u64_eq h12
  have e2 : UInt64.ofBitVec ((Sym.bin .add .W64 (.reg .X12) (.lit 1)).eval
      (Env.ofMachine st.data [(fb m0 + BitVec.ofNat 64 (32 * q), 32)])) = (4 * q + 2).toUInt64 :=
    u64_eq (by sym_simp; exact add_lit (c := 1) h12 (by omega))
  have e3 : UInt64.ofBitVec ((Sym.bin .add .W64 (.reg .X12) (.lit 2)).eval
      (Env.ofMachine st.data [(fb m0 + BitVec.ofNat 64 (32 * q), 32)])) = (4 * q + 3).toUInt64 :=
    u64_eq (by sym_simp; exact add_lit (c := 2) h12 (by omega))
  rw [e0, NativeRustcVm.addr_add_zero] at w0
  rw [e1, NativeRustcVm.addr_add] at w1
  rw [e2, NativeRustcVm.addr_add] at w2
  rw [e3, NativeRustcVm.addr_add] at w3
  have hords : Ords m0 (4 * q + 4) st'.data.dmem := hI.init.ords.step (fb_noWrap hS) (by omega)
    (by rw [show 8 * (4 * q) = 32 * q by omega]; exact hsame) fun t h1 h2 ↦ by
      have : t = 4 * q ∨ t = 4 * q + 1 ∨ t = 4 * q + 2 ∨ t = 4 * q + 3 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · rw [show 8 * (4 * q) = 32 * q by omega]; exact w0
      · rw [show 8 * (4 * q + 1) = 32 * q + 8 by omega]; exact w1
      · rw [show 8 * (4 * q + 2) = 32 * q + 16 by omega]; exact w2
      · rw [show 8 * (4 * q + 3) = 32 * q + 24 by omega]; exact w3
  have he := regs_eq_of hm hm' (.X8 :: .X9 :: .X10 :: initRegs) rfl
  have hinit : Init m0 (4 * (q + 1)) st'.data :=
    ⟨hfr, hI.init.regs.of fun r hr ↦ he r (by simp [regsList_sub r hr]), by
      rw [show st'.data.regs.X23 = st.data.regs.X23 from he .X23 (by simp [initRegs])]
      exact hI.init.x23, by rw [show 4 * (q + 1) = 4 * q + 4 by omega]; exact hords, by omega⟩
  have h8 : st'.data.regs.X8.toNat = n m0 / 4 * 4 := by
    rw [show st'.data.regs.X8 = st.data.regs.X8 from he .X8 (by simp)]; exact hI.x8
  have h9 : st'.data.regs.X9.toBitVec = fb m0 + BitVec.ofNat 64 (8 * (n m0 / 4 * 4)) := by
    rw [show st'.data.regs.X9 = st.data.regs.X9 from he .X9 (by simp)]; exact hI.x9
  have h10 : st'.data.regs.X10.toNat = n m0 := by
    rw [show st'.data.regs.X10 = st.data.regs.X10 from he .X10 (by simp)]; exact hI.x10
  simp only [PcOk, NativeRustcVmArm.Vm.StackOffsets.b8_length, NativeRustcVmArm.Vm.StackOffsets.b8Length] at hpc'
  obtain ⟨hy, hno⟩ := pc_of (P := 4 * q + 1 + 3 ≠ n m0 / 4 * 4) hpc'
    (by sym_simp; exact nbeq_dec (add_lit (c := 3) h12 (by omega)) hI.x8)
  by_cases hlast : 4 * q + 4 = n m0 / 4 * 4
  · refine .done _ (Or.inl ⟨hno (by omega), ?_, h8, h9, h10⟩)
    rw [← hlast, show 4 * q + 4 = 4 * (q + 1) by omega]; exact hinit
  · refine .done _ (Or.inr ⟨(hy (by omega)).trans (lbl_7 hp), hinit, by omega, h8, h9, h10, ?_,
      ?_⟩)
    · show (st'.data.regs.getXReg .X11).toBitVec = _
      rw [hm'.regs .X11 _ rfl]
      show fb m0 + BitVec.ofNat 64 (32 * q) + BitVec.ofInt 64 ((48 : Nat) : Int) = _
      rw [Arrays.ofInt_eq_ofNat, NativeRustcVm.addr_add,
        show 32 * q + 48 = 32 * (q + 1) + 16 by omega]
    · show (st'.data.regs.getXReg .X12).toBitVec.toNat = _
      rw [hm'.regs .X12 _ rfl]
      sym_simp
      exact (add_lit (c := 4) h12 (by omega)).trans (by omega)

/-- `b9`: the rest one by one, or the sort. -/
theorem l9 (hp : Placed code k) {m0 : MachineData} (hS : StackOk m0 1328) (hn : n m0 ≤ 158)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b9Offset)) (hI : Init m0 (n m0 / 4 * 4) st.data)
    (h8 : st.data.regs.X8.toNat = n m0 / 4 * 4)
    (h9 : st.data.regs.X9.toBitVec = fb m0 + BitVec.ofNat 64 (8 * (n m0 / 4 * 4)))
    (h10 : st.data.regs.X10.toNat = n m0) : Eventually (step1 Host.exe) (At12 k m0) st :=
  run_regs hS (infix_of b9_in_code (by simp [b9]) hp) run_b9 (after_eq run_b9 ▸ b9_keeps)
    hpc hI.fr fun st' hm hpc' hfr hd ↦ by
      have he := regs_eq_of (match_nil _) hm (.X8 :: .X9 :: initRegs) rfl
      have hI' := hI.of hfr (fun r hr ↦ he r (by simp [hr])) hd
      have hN : n m0 / 4 * 4 ≤ n m0 := Nat.div_mul_le_self _ _
      simp only [PcOk, NativeRustcVmArm.Vm.StackOffsets.b9_length, NativeRustcVmArm.Vm.StackOffsets.b9Length] at hpc'
      obtain ⟨hy, hno⟩ := pc_of (P := n m0 = n m0 / 4 * 4) hpc' (by
        sym_simp
        simp only [Env.ofMachine_regs]
        exact beq_dec h10 h8)
      by_cases he4 : n m0 = n m0 / 4 * 4
      · exact .done _ ⟨(hy he4).trans (lbl_11 hp), by rw [← he4] at hI'; exact hI'⟩
      · refine l10 hp hS hn (hno he4) hI' (by omega) ?_ ?_
        · rw [show st'.data.regs.X8 = st.data.regs.X8 from he .X8 (by simp)]; exact h8
        · rw [show st'.data.regs.X9 = st.data.regs.X9 from he .X9 (by simp)]; exact h9

/-- **The quadruple loop**, to `b9`. -/
theorem loop8 (hp : Placed code k) {m0 : MachineData} (hS : StackOk m0 1328) (hn : n m0 ≤ 158)
    {q : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b8Offset)) (hI : Inv8 m0 q st.data) :
    Eventually (step1 Host.exe) (At12 k m0) st := by
  refine Eventually.bind (Sym.loop (Q := fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b9Offset) ∧
        Init m0 (n m0 / 4 * 4) s.data ∧ s.data.regs.X8.toNat = n m0 / 4 * 4 ∧
        s.data.regs.X9.toBitVec = fb m0 + BitVec.ofNat 64 (8 * (n m0 / 4 * 4)) ∧
        s.data.regs.X10.toNat = n m0)
      (fun r s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b8Offset) ∧ ∃ q, n m0 - 4 * q = r ∧ Inv8 m0 q s.data)
      (fun r s ⟨hpc, q, hr, hI⟩ ↦ ?_) ⟨hpc, q, rfl, hI⟩)
    fun s ⟨hpc, hI, h8, h9, h10⟩ ↦ l9 hp hS hn hpc hI h8 h9 h10
  refine Eventually.mono (step8 hp hS hn hpc hI) fun s' h ↦ ?_
  rcases h with h | ⟨hpc', hI'⟩
  · exact Or.inl h
  · exact Or.inr ⟨n m0 - 4 * (q + 1), by have := hI.lt; omega, hpc', q + 1, rfl, hI'⟩

/-- `b7`: the quadruple loop's set-up. -/
theorem l7 (hp : Placed code k) {m0 : MachineData} (hS : StackOk m0 1328) (hn : n m0 ≤ 158)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b7Offset)) (hI : Init m0 0 st.data)
    (h4 : 3 < n m0) (h8 : st.data.regs.X8.toNat = 8 * n m0 - 8)
    (h11 : st.data.regs.X11.toBitVec = fb m0) : Eventually (step1 Host.exe) (At12 k m0) st :=
  run_regs hS (infix_of b7_in_code (by simp [b7]) hp) run_b7 (after_eq run_b7 ▸ b7_keeps)
    hpc hI.fr fun st' hm hpc' hfr hd ↦ by
      have he := regs_eq_of (match_nil _) hm initRegs rfl
      have hI' := hI.of hfr he hd
      have hb : (BinOp.apply .add .W64 (UnOp.apply (.ubfm 3 63) .W64
          (st.data.regs.getXReg .X8).toBitVec) (BitVec.ofNat 64 1)).toNat = n m0 := by
        simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]
        rw [add_lit (a := n m0 - 1) (by rw [lsr3]; show st.data.regs.X8.toNat / 8 = _; omega)
          (by omega)]
        omega
      have hand : (BinOp.apply .and .W64 (BinOp.apply .add .W64 (UnOp.apply (.ubfm 3 63) .W64
          (st.data.regs.getXReg .X8).toBitVec) (BitVec.ofNat 64 1))
          (BitVec.ofNat 64 4611686018427387900)).toNat = n m0 / 4 * 4 := by
        simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64] at hb ⊢
        rw [BitVec.toNat_and, hb, lit_toNat (by decide)]
        exact and_mask ⟨n m0, by omega⟩
      refine loop8 hp hS hn (q := 0) hpc' ⟨hI', by omega, ?_, ?_, ?_, ?_, ?_⟩
      · show (st'.data.regs.getXReg .X8).toBitVec.toNat = _
        rw [hm.regs .X8 _ rfl]
        exact hand
      · show (st'.data.regs.getXReg .X9).toBitVec = _
        rw [hm.regs .X9 _ rfl]
        sym_simp
        simp only [Env.ofMachine_regs]
        rw [show (st.data.regs.getXReg .X11).toBitVec = fb m0 from h11]
        sym_simp at hand
        rw [shl3, hand]
      · show (st'.data.regs.getXReg .X10).toBitVec.toNat = _
        rw [hm.regs .X10 _ rfl]
        exact hb
      · show (st'.data.regs.getXReg .X11).toBitVec = _
        rw [hm.regs .X11 _ rfl]
        sym_simp
        simp only [Env.ofMachine_regs]
        rw [show (st.data.regs.getXReg .X11).toBitVec = fb m0 from h11]
      · show (st'.data.regs.getXReg .X12).toBitVec.toNat = _
        rw [hm.regs .X12 _ rfl]
        rfl

/-- `b5`: below four blocks, the single loop from `0`. -/
theorem l5 (hp : Placed code k) {m0 : MachineData} (hS : StackOk m0 1328) (hn : n m0 ≤ 158)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b5Offset)) (hI : Init m0 0 st.data)
    (h0 : 0 < n m0) : Eventually (step1 Host.exe) (At12 k m0) st :=
  run_regs hS (infix_of b5_in_code (by simp [b5]) hp) run_b5 (after_eq run_b5 ▸ b5_keeps)
    hpc hI.fr fun st' hm hpc' hfr hd ↦ by
      have he := regs_eq_of (match_nil _) hm initRegs rfl
      refine l10 hp hS hn (hpc'.trans (lbl_9 hp)) (hI.of hfr he hd) h0 ?_ ?_
      · show (st'.data.regs.getXReg .X8).toBitVec.toNat = _
        rw [hm.regs .X8 _ rfl]
        rfl
      · show (st'.data.regs.getXReg .X9).toBitVec = _
        rw [hm.regs .X9 _ rfl]
        rw [NativeRustcVm.addr_add_zero]
        exact hI.fr.sp

/-- `b4`: four blocks or more? -/
theorem l4 (hp : Placed code k) {m0 : MachineData} (hS : StackOk m0 1328) (hn : n m0 ≤ 158)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b4Offset)) (hI : Init m0 0 st.data)
    (h0 : 0 < n m0) : Eventually (step1 Host.exe) (At12 k m0) st :=
  run_regs hS (infix_of b4_in_code (by simp [b4]) hp) run_b4 (after_eq run_b4 ▸ b4_keeps)
    hpc hI.fr fun st' hm hpc' hfr hd ↦ by
      have he := regs_eq_of (match_nil _) hm initRegs rfl
      have hI' := hI.of hfr he hd
      have h23 : (st.data.regs.getXReg .X23).toBitVec.toNat = 8 * n m0 := hI.x23
      have h8 : (BinOp.apply .sub .W64 (st.data.regs.getXReg .X23).toBitVec
          (BitVec.ofNat 64 8)).toNat = 8 * n m0 - 8 := by
        simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]
        exact sub_lit h23 (by omega)
      simp only [PcOk, NativeRustcVmArm.Vm.StackOffsets.b4_length, NativeRustcVmArm.Vm.StackOffsets.b4Length] at hpc'
      obtain ⟨hy, hno⟩ := pc_of (P := 3 < n m0) hpc' (by
        sym_simp
        simp only [Env.ofMachine_regs]
        simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64] at h8
        rw [ult_dec h8 (lit_toNat (by decide)), beq_dec h8 (lit_toNat (by decide))]
        by_cases hc : 3 < n m0 <;> simp [hc] <;> omega)
      by_cases h4 : 3 < n m0
      · refine l7 hp hS hn ((hy h4).trans (lbl_6 hp)) hI' h4 ?_ ?_
        · show (st'.data.regs.getXReg .X8).toBitVec.toNat = _
          rw [hm.regs .X8 _ rfl]
          exact h8
        · show (st'.data.regs.getXReg .X11).toBitVec = _
          rw [hm.regs .X11 _ rfl]
          exact hI.fr.sp
      · exact l5 hp hS hn (hno h4) hI' h0

/-- `b6`: no block, straight to the sort. -/
theorem l6 (hp : Placed code k) {m0 : MachineData} (hS : StackOk m0 1328) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b6Offset)) (hI : Init m0 0 st.data) (h0 : n m0 = 0) :
    Eventually (step1 Host.exe) (At13 k m0) st :=
  run_regs hS (infix_of b6_in_code (by simp [b6]) hp) run_b6 (after_eq run_b6 ▸ b6_keeps)
    hpc hI.fr fun st' hm hpc' hfr hd ↦ by
      have he := regs_eq_of (match_nil _) hm initRegs rfl
      refine .done _ ⟨hpc'.trans (lbl_12 hp), ⟨h0 ▸ hI.of hfr he hd, ?_, ?_, ?_, ?_⟩⟩
      · show (st'.data.regs.getXReg .X0).toBitVec = _
        rw [hm.regs .X0 _ rfl]
        exact hI.fr.sp
      · show (st'.data.regs.getXReg .X1).toBitVec.toNat = _
        rw [hm.regs .X1 _ rfl, h0]
        rfl
      · exact (UInt64.toBitVec_inj.mp (hm.regs .X2 _ rfl)).trans hI.regs.x22
      · show (st'.data.regs.getXReg .X3).toBitVec.toNat = _
        rw [hm.regs .X3 _ rfl, h0]
        rfl

/-- **`b3`-`b12`**: from `memset`'s return, the order array written, at the sort's call. -/
theorem init_spec (hp : Placed code k) {m0 : MachineData} (hS : StackOk m0 1328)
    (hn : n m0 ≤ 158) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b3Offset))
    (hfr : Fr m0 st.data) (hR : Regs m0 st.data) : Eventually (step1 Host.exe) (At13 k m0) st :=
  run_regs hS (infix_of b3_in_code (by simp [b3]) hp) run_b3 (after_eq run_b3 ▸ b3_keeps)
    hpc hfr fun st' hm hpc' hfr' hd ↦ by
      have he := regs_eq_of (match_nil _) hm regsList rfl
      have h21 : (st.data.regs.getXReg .X21).toBitVec.toNat = n m0 := congrArg UInt64.toNat hR.x21
      have hI : Init m0 0 st'.data := ⟨hfr', hR.of he, by
        show (st'.data.regs.getXReg .X23).toBitVec.toNat = _
        rw [hm.regs .X23 _ rfl]
        show (UnOp.apply (.ubfm 61 60) .W64 (st.data.regs.getXReg .X21).toBitVec).toNat = _
        rw [lsl3, h21, lit_toNat (by omega)], fun t ht ↦ absurd ht (by omega), Nat.zero_le _⟩
      simp only [PcOk, NativeRustcVmArm.Vm.StackOffsets.b3_length, NativeRustcVmArm.Vm.StackOffsets.b3Length] at hpc'
      obtain ⟨hy, hno⟩ := pc_of (P := n m0 = 0) hpc' (by
        sym_simp
        simp only [Env.ofMachine_regs]
        exact beq_dec h21 (lit_toNat (by decide)))
      by_cases h0 : n m0 = 0
      · exact l6 hp hS ((hy h0).trans (lbl_5 hp)) hI h0
      · exact Eventually.bind (l4 hp hS hn (hno h0) hI (by omega)) fun s h ↦ l12 hp hS h

end

end NativeRustcVmArm.Layout.StackOffsets
