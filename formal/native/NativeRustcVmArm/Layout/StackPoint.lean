module

public import NativeRustcVmArm.Code.Vm.SelectorPoint.Names
public import NativeRustcVmArm.Code.Vm.StackPoint.Names
public import NativeRustcVmArm.Layout.StackPoint.Exec
public import NativeRustcVmArm.Layout.Body

/-!
# `stack_point` on AArch64

**`stackPoint_spec`**: rustc's `stack_point(p, point, stack_log, out)`, placed anywhere in the
program, meets `StackPointPre`/`StackPointPost` given `selector_point`'s contract. The prologue
(`b0`) saves X30 and X19, computes `n = |point| + (stack_log - vc)` and returns `None` past `66`
(`b11`). Else `b1` keeps `out + 16|point|` in X8, and the point is copied into `out` (`Copy`): two
elements a turn (`b4`, the loop `b5`, `InvA`), then one (`b7`, the loop `b8`, `InvB`); `b9` calls
`selector_point(index >> vc, out + 16|point|, tail)`, and `b10`, `b11` return `Some(n)`.
-/

namespace NativeRustcVmArm.Layout.StackPoint

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.StackPoint NativeVm.Model
open NativeRustcVmArm.Arrays (Body calleeRegs inSlots keepsAll restores savedRegs entry_match
  wf_one elem_of_apart pc_cond frame_ok regs_eq_of toNat_add_ofNat' inRange_mono inRange_add
  not_inRange_of_apart add_ofNat_zero)
open NativeRustcVm (ewsOf ewOf EWsAt EWAt WordAt)

public section

/-- The stack. -/
abbrev S : Nat := stackPointStack
/-- `out`. -/
abbrev out (m : MachineData) : BitVec 64 := m.regs.X5.toBitVec
/-- `out`'s bytes. -/
abbrev outB : Nat := 16 * stackPointOut
/-- The point. -/
abbrev pt (m : MachineData) : BitVec 64 := m.regs.X2.toBitVec
/-- Its length. -/
abbrev len (m : MachineData) : Nat := m.regs.X3.toNat
/-- Its elements. -/
abbrev ptl (m : MachineData) : List EW := ewsOf m.dmem (pt m) (len m)
/-- The selector's length. -/
abbrev tl (m : MachineData) : Nat := m.regs.X4.toNat - m.regs.X0.toNat
/-- The stack point's length. -/
abbrev nn (m : MachineData) : Nat := len m + tl m
/-- The pairs' part of the point. -/
abbrev E (m : MachineData) : Nat := len m / 2 * 2

/-- The registers the body keeps: the arguments, the selector's length in X2, `n` in X19. -/
structure Regs (m0 st : MachineData) : Prop where
  x0 : st.regs.X0 = m0.regs.X0
  x1 : st.regs.X1 = m0.regs.X1
  x2 : st.regs.X2.toNat = tl m0
  x3 : st.regs.X3 = m0.regs.X3
  x5 : st.regs.X5 = m0.regs.X5
  x19 : st.regs.X19.toNat = nn m0

/-- The registers `Regs` reads. -/
def regsList : List XReg := [.X0, .X1, .X2, .X3, .X5, .X19]

theorem Regs.of {m0 st st' : MachineData} (h : Regs m0 st)
    (he : ∀ r ∈ regsList, st'.regs.getXReg r = st.regs.getXReg r) : Regs m0 st' where
  x0 := (he .X0 (by simp [regsList])).trans h.x0
  x1 := (he .X1 (by simp [regsList])).trans h.x1
  x2 := by rw [show st'.regs.X2 = st.regs.X2 from he .X2 (by simp [regsList])]; exact h.x2
  x3 := (he .X3 (by simp [regsList])).trans h.x3
  x5 := (he .X5 (by simp [regsList])).trans h.x5
  x19 := by rw [show st'.regs.X19 = st.regs.X19 from he .X19 (by simp [regsList])]; exact h.x19

/-- **`i` elements of the point copied** into `out`. -/
structure Copy (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  body : Body m0 16 S slots (out m0) outB st
  regs : Regs m0 st
  x8 : st.regs.X8.toBitVec = out m0 + BitVec.ofNat 64 (16 * len m0)
  le : i ≤ len m0
  copied : EWsAt st.dmem (out m0) ((ptl m0).take i)

/-- **The pair loop's head** `.LStackPoint_5`. -/
structure InvA (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  copy : Copy m0 i st
  even : i % 2 = 0
  lt : i + 2 ≤ E m0
  x9 : st.regs.X9 = m0.regs.X2
  x10 : st.regs.X10.toNat = E m0
  x11 : st.regs.X11.toBitVec = pt m0 + BitVec.ofNat 64 (16 * i + 16)
  x12 : st.regs.X12.toBitVec = out m0 + BitVec.ofNat 64 (16 * i + 16)
  x13 : st.regs.X13.toNat = E m0 - i

/-- **The single loop's head** `.LStackPoint_8`. -/
structure InvB (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  copy : Copy m0 i st
  lt : i < len m0
  x9 : st.regs.X9.toBitVec = pt m0 + BitVec.ofNat 64 (16 * i + 8)
  x10 : st.regs.X10.toNat = len m0 - i
  x11 : st.regs.X11.toBitVec = out m0 + BitVec.ofNat 64 (16 * i + 8)

theorem and62 : ∀ x : Fin 64, x.val &&& 62 = x.val / 2 * 2 := by decide

theorem or8 (x : BitVec 64) (h : x.toNat < 2 ^ 59) :
    (BitVec.ofNat 64 8 ||| x <<< 4) = BitVec.ofNat 64 (16 * x.toNat + 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show x.toNat * 2 ^ 4 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 16 * x.toNat + 8 < 2 ^ 64 by omega),
    show 8 % 2 ^ 64 = 8 from rfl, Nat.lor_comm, Nat.mul_comm,
    ← Nat.two_pow_add_eq_or_of_lt (by decide : 8 < 2 ^ 4)]

variable [Host] {k : Nat}

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.StackPoint.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.StackPoint.b0Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.StackPoint.entryOffset) NativeRustcVmArm.Vm.StackPoint.entry_at
theorem lbl_4 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.StackPoint.label_4 = Host.addrOf (k + NativeRustcVmArm.Vm.StackPoint.b4Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.StackPoint.b4Offset) NativeRustcVmArm.Vm.StackPoint.label_4_at
theorem lbl_5 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.StackPoint.label_5 = Host.addrOf (k + NativeRustcVmArm.Vm.StackPoint.b5Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.StackPoint.b5Offset) NativeRustcVmArm.Vm.StackPoint.label_5_at
theorem lbl_7 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.StackPoint.label_7 = Host.addrOf (k + NativeRustcVmArm.Vm.StackPoint.b7Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.StackPoint.b7Offset) NativeRustcVmArm.Vm.StackPoint.label_7_at
theorem lbl_8 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.StackPoint.label_8 = Host.addrOf (k + NativeRustcVmArm.Vm.StackPoint.b8Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.StackPoint.b8Offset) NativeRustcVmArm.Vm.StackPoint.label_8_at
theorem lbl_9 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.StackPoint.label_9 = Host.addrOf (k + NativeRustcVmArm.Vm.StackPoint.b9Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.StackPoint.b9Offset) NativeRustcVmArm.Vm.StackPoint.label_9_at
theorem lbl_10 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.StackPoint.label_10 = Host.addrOf (k + NativeRustcVmArm.Vm.StackPoint.b11Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.StackPoint.b11Offset) NativeRustcVmArm.Vm.StackPoint.label_10_at

/-- `stack_point`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ StackPointPost m0 s.data

/-- What `stack_point` stores. -/
abbrev res (m : MachineData) : List EW :=
  (stackPoint ⟨m.regs.X0.toNat, m.regs.X1.toNat⟩ (slice m m.regs.X2 m.regs.X3)
    m.regs.X4.toNat).toList

/-- **The epilogue** `b11`: `X8`, `X19` returned. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hpre : StackPointPre m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackPoint.b11Offset))
    (hb : Body m0 16 S slots (out m0) outB st.data)
    (hok : nn m0 ≤ 66 → st.data.regs.X8 = 1 ∧ st.data.regs.X19.toNat = nn m0 ∧
      EWsAt st.data.dmem (out m0) (res m0))
    (hno : ¬nn m0 ≤ 66 → st.data.regs.X8 = 0) :
    Eventually (step1 Host.exe) (Post m0) st := by
  obtain ⟨hwf, hm⟩ := hb.exit_match hpre.1 (by decide) rfl
  refine exec_at (infix_of b11_in_code (by simp [b11]) hp) run_b11 hwf hpc hm
    fun s' hm' hpc' ↦ .done _ ?_
  obtain ⟨hres, hmem⟩ := after_eq run_b11 ▸ b11_restores
  obtain ⟨hsaved, hx30, hdm⟩ := hb.saved hm' hwf (by simp [slots]) hres hmem
  have h0 : s'.data.regs.X0 = st.data.regs.X8 := UInt64.toBitVec_inj.mp (hm'.regs .X0 _ rfl)
  have h1 : s'.data.regs.X1 = st.data.regs.X19 := UInt64.toBitVec_inj.mp (hm'.regs .X1 _ rfl)
  refine ⟨?_, ?_, fun p hp' ↦ by rw [hdm]; exact hb.same p hp', hsaved⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    simp only [retOf, hx30]
  · split
    · rename_i h
      obtain ⟨a, b, c⟩ := hok h
      exact ⟨h0.trans a, by rw [h1]; exact b, by rw [hdm]; exact c⟩
    · rename_i h
      exact h0.trans (hno h)

omit [Host] in
/-- Element `i` of the point, read in a body. -/
theorem elem {m0 st : MachineData} (hpre : StackPointPre m0)
    (hb : Body m0 16 S slots (out m0) outB st) {i : Nat} (hi : i < len m0) :
    ewOf st.dmem (pt m0 + BitVec.ofNat 64 (16 * i)) = (ptl m0)[i]'(by simp; exact hi) :=
  elem_of_apart hb.same hpre.1 hpre.2.1.1.2 hpre.2.1.2 (Or.symm hpre.2.2.2.2.1) hpre.2.2.1.2 hi

omit [Host] in
theorem ofInt_pos (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by simp

/-- **A turn of the pair loop** `b5`: `point[i]`, `point[i + 1]` copied. -/
theorem stepA (hp : Placed code k) {m0 : MachineData} (hpre : StackPointPre m0)
    (hfit : nn m0 ≤ 66) {i : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackPoint.b5Offset))
    (hI : InvA m0 i st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackPoint.b6Offset) ∧ Copy m0 (E m0) s.data ∧
        s.data.regs.X9 = m0.regs.X2 ∧ s.data.regs.X10.toNat = E m0) ∨
      (s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackPoint.b5Offset) ∧ InvA m0 (i + 2) s.data)) st := by
  have hlt := hI.lt
  have hE : E m0 ≤ len m0 := Nat.div_mul_le_self _ _
  have hfit' : len m0 + tl m0 ≤ 66 := hfit
  have hl3 : m0.regs.X3.toNat = len m0 := rfl
  have hro := hpre.2.2.1
  have hnwo : NoWrap (out m0) outB := hro.2
  have hrp := hpre.2.1.1
  have hb := hI.copy.body
  have hro' := readable_sub hro hb.kept (o := 16 * i) (j := 32) (by show _ ≤ 16 * 66; omega)
  have hrp' := readable_sub hrp hb.kept (o := 16 * i) (j := 32) (by omega)
  have hap := apart_sub hpre.2.2.2.2.1 hnwo hrp.2 (o := 16 * i) (j := 32) (o' := 16 * i) (j' := 32)
    (by show _ ≤ 16 * 66; omega) (by omega) (by decide) (by decide)
  have hwf : (Env.ofMachine st.data [(out m0 + BitVec.ofNat 64 (16 * i), 32),
      (pt m0 + BitVec.ofNat 64 (16 * i), 32)]).WF :=
    Env.wf_of ⟨hro', hrp', trivial⟩ (List.pairwise_pair.mpr hap)
  have hm : Match (Env.ofMachine st.data [(out m0 + BitVec.ofNat 64 (16 * i), 32),
      (pt m0 + BitVec.ofNat 64 (16 * i), 32)]) pairS st.data :=
    match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl ⟨by
        show _ = out m0 + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 ((16 : Nat) : Int)
        rw [ofInt_pos, NativeRustcVm.addr_add]; exact hI.x12, by
        show _ = pt m0 + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 ((16 : Nat) : Int)
        rw [ofInt_pos, NativeRustcVm.addr_add]; exact hI.x11, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 hwf hpc hm fun st' hm' hpc' ↦ ?_
  obtain ⟨hk, hw, hv⟩ := after_eq run_b5 ▸ b5_facts
  have bd := Body.of_write' hb hpre.1 hm hm' hwf (fun p h ↦ inRange_mono h (by
      show _ ≤ 16 * 66; omega)) hk hw
    (offStack_sub hpre.2.2.2.1 hnwo (by show _ ≤ 16 * 66; omega) (by decide))
    (by simp [slots]) (by decide)
  have hsame := same_of_region hm' hwf (r := 0) rfl hw
  have e0 := copy_ew hm' (od := 0) (os := 0) (by decide) (hv 0 (by simp)) (hv 8 (by simp))
  have e1 := copy_ew hm' (od := 16) (os := 16) (by decide) (hv 16 (by simp)) (hv 24 (by simp))
  rw [add_ofNat_zero, add_ofNat_zero, elem hpre hb (by omega)] at e0
  rw [NativeRustcVm.addr_add, NativeRustcVm.addr_add,
    show 16 * i + 16 = 16 * (i + 1) by omega, elem hpre hb (by omega)] at e1
  have hnew : EWsAt st'.data.dmem (out m0 + BitVec.ofNat 64 (16 * i)) (((ptl m0).drop i).take 2) := by
    rw [drop_take_two (by simp; omega)]
    show EWsAt _ _ ([_] ++ [_])
    rw [NativeRustcVm.ewsAt_append, NativeRustcVm.ewsAt_singleton, NativeRustcVm.ewsAt_singleton,
      List.length_singleton, Nat.mul_one, NativeRustcVm.addr_add]
    exact ⟨e0, e1⟩
  have hcp := copied_step (xs := ptl m0) (by
      have : (out m0).toNat + 1056 ≤ 2 ^ 64 := hnwo
      have hl : (ptl m0).length = len m0 := by simp
      show (out m0).toNat + 16 * (ptl m0).length ≤ 2 ^ 64
      rw [hl]; omega)
    hI.copy.copied hsame hnew (by simp; omega) (by decide)
  have he := regs_eq_of hm hm' regsList rfl
  have hc : Copy m0 (i + 2) st'.data :=
    ⟨bd, hI.copy.regs.of he, by
      rw [show st'.data.regs.X8 = st.data.regs.X8 from Match.reg_eq hm hm' (r := .X8) rfl rfl]
      exact hI.copy.x8, by omega, hcp⟩
  have h9 : st'.data.regs.X9 = st.data.regs.X9 := Match.reg_eq hm hm' (r := .X9) rfl rfl
  have h10 : st'.data.regs.X10 = st.data.regs.X10 := Match.reg_eq hm hm' (r := .X10) rfl rfl
  simp only [PcOk, NativeRustcVmArm.Vm.StackPoint.b5_length, NativeRustcVmArm.Vm.StackPoint.b5Length] at hpc'
  sym_simp at hpc'
  obtain ⟨hy, hn⟩ := pc_cond hpc'
  have h13 : (st.data.regs.getXReg .X13).toBitVec.toNat = E m0 - i := hI.x13
  have hEv : E m0 % 2 = 0 := by simp [E]
  have hiv := hI.even
  by_cases hlast : E m0 - i = 2
  · refine .done _ (Or.inl ⟨hn fun h ↦ ((not_beq_iff (by decide)).mp h) (h13.trans hlast), ?_,
      h9.trans hI.x9, by rw [h10]; exact hI.x10⟩)
    rw [show E m0 = i + 2 by omega]
    exact hc
  · refine .done _ (Or.inr ⟨(hy ((not_beq_iff (by decide)).mpr fun h ↦ hlast (h13.symm.trans h))).trans
      (lbl_5 hp), hc, by omega, by omega, h9.trans hI.x9, by rw [h10]; exact hI.x10, ?_, ?_, ?_⟩)
    · show (st'.data.regs.getXReg .X11).toBitVec = _
      rw [hm'.regs .X11 _ rfl]
      show pt m0 + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 ((48 : Nat) : Int) = _
      rw [ofInt_pos, NativeRustcVm.addr_add]
      congr 2
    · show (st'.data.regs.getXReg .X12).toBitVec = _
      rw [hm'.regs .X12 _ rfl]
      show out m0 + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 ((48 : Nat) : Int) = _
      rw [ofInt_pos, NativeRustcVm.addr_add]
      congr 2
    · show (st'.data.regs.getXReg .X13).toBitVec.toNat = _
      rw [hm'.regs .X13 _ rfl]
      sym_simp
      simp only [Env.ofMachine_regs]
      rw [BitVec.toNat_sub_of_le (by
        rw [BitVec.le_def, BitVec.toNat_ofNat]; simp only [Nat.reducePow, Nat.reduceMod]
        rw [h13]; omega), h13]
      simp only [BitVec.toNat_ofNat]
      omega

/-- At `b9`: the point copied. -/
abbrev At9 (k : Nat) (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackPoint.b9Offset) ∧ Copy m0 (len m0) s.data

/-- **A turn of the single loop** `b8`: `point[i]` copied. -/
theorem stepB (hp : Placed code k) {m0 : MachineData} (hpre : StackPointPre m0)
    (hfit : nn m0 ≤ 66) {i : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackPoint.b8Offset))
    (hI : InvB m0 i st.data) :
    Eventually (step1 Host.exe) (fun s ↦ At9 k m0 s ∨
      (s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackPoint.b8Offset) ∧ InvB m0 (i + 1) s.data)) st := by
  have hlt := hI.lt
  have hfit' : len m0 + tl m0 ≤ 66 := hfit
  have hl3 : m0.regs.X3.toNat = len m0 := rfl
  have hro := hpre.2.2.1
  have hnwo : NoWrap (out m0) outB := hro.2
  have hrp := hpre.2.1.1
  have hb := hI.copy.body
  have hro' := readable_sub hro hb.kept (o := 16 * i) (j := 16) (by show _ ≤ 16 * 66; omega)
  have hrp' := readable_sub hrp hb.kept (o := 16 * i) (j := 16) (by omega)
  have hap := apart_sub hpre.2.2.2.2.1 hnwo hrp.2 (o := 16 * i) (j := 16) (o' := 16 * i) (j' := 16)
    (by show _ ≤ 16 * 66; omega) (by omega) (by decide) (by decide)
  have hwf : (Env.ofMachine st.data [(out m0 + BitVec.ofNat 64 (16 * i), 16),
      (pt m0 + BitVec.ofNat 64 (16 * i), 16)]).WF :=
    Env.wf_of ⟨hro', hrp', trivial⟩ (List.pairwise_pair.mpr hap)
  have hm : Match (Env.ofMachine st.data [(out m0 + BitVec.ofNat 64 (16 * i), 16),
      (pt m0 + BitVec.ofNat 64 (16 * i), 16)]) oneS st.data :=
    match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl ⟨by
        show _ = out m0 + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 ((8 : Nat) : Int)
        rw [ofInt_pos, NativeRustcVm.addr_add]; exact hI.x11, by
        show _ = pt m0 + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 ((8 : Nat) : Int)
        rw [ofInt_pos, NativeRustcVm.addr_add]; exact hI.x9, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8 hwf hpc hm fun st' hm' hpc' ↦ ?_
  obtain ⟨hk, hw, hv⟩ := after_eq run_b8 ▸ b8_facts
  have bd := Body.of_write' hb hpre.1 hm hm' hwf (fun p h ↦ inRange_mono h (by
      show _ ≤ 16 * 66; omega)) hk hw
    (offStack_sub hpre.2.2.2.1 hnwo (by show _ ≤ 16 * 66; omega) (by decide))
    (by simp [slots]) (by decide)
  have hsame := same_of_region hm' hwf (r := 0) rfl hw
  have e0 := copy_ew hm' (od := 0) (os := 0) (by decide) (hv 0 (by simp)) (hv 8 (by simp))
  rw [add_ofNat_zero, add_ofNat_zero, elem hpre hb (by omega)] at e0
  have hnew : EWsAt st'.data.dmem (out m0 + BitVec.ofNat 64 (16 * i)) (((ptl m0).drop i).take 1) := by
    rw [drop_take_one (by simp; omega), NativeRustcVm.ewsAt_singleton]
    exact e0
  have hcp := copied_step (xs := ptl m0) (c := 1) (by
      have : (out m0).toNat + 1056 ≤ 2 ^ 64 := hnwo
      have hl : (ptl m0).length = len m0 := by simp
      show (out m0).toNat + 16 * (ptl m0).length ≤ 2 ^ 64
      rw [hl]; omega)
    hI.copy.copied hsame hnew (by simp; omega) (by decide)
  have he := regs_eq_of hm hm' regsList rfl
  have hc : Copy m0 (i + 1) st'.data :=
    ⟨bd, hI.copy.regs.of he, by
      rw [show st'.data.regs.X8 = st.data.regs.X8 from Match.reg_eq hm hm' (r := .X8) rfl rfl]
      exact hI.copy.x8, by omega, hcp⟩
  simp only [PcOk, NativeRustcVmArm.Vm.StackPoint.b8_length, NativeRustcVmArm.Vm.StackPoint.b8Length] at hpc'
  sym_simp at hpc'
  obtain ⟨hy, hn⟩ := pc_cond hpc'
  have h10 : (st.data.regs.getXReg .X10).toBitVec.toNat = len m0 - i := hI.x10
  by_cases hlast : len m0 - i = 1
  · refine .done _ (Or.inl ⟨hn fun h ↦ ((not_beq_iff (by decide)).mp h) (h10.trans hlast), ?_⟩)
    rw [show len m0 = i + 1 by omega]
    exact hc
  · refine .done _ (Or.inr ⟨(hy ((not_beq_iff (by decide)).mpr fun h ↦ hlast (h10.symm.trans h))).trans
      (lbl_8 hp), hc, by omega, ?_, ?_, ?_⟩)
    · show (st'.data.regs.getXReg .X9).toBitVec = _
      rw [hm'.regs .X9 _ rfl]
      show pt m0 + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 ((24 : Nat) : Int) = _
      rw [ofInt_pos, NativeRustcVm.addr_add]
      congr 2
    · show (st'.data.regs.getXReg .X10).toBitVec.toNat = _
      rw [hm'.regs .X10 _ rfl]
      sym_simp
      simp only [Env.ofMachine_regs]
      rw [BitVec.toNat_sub_of_le (by
        rw [BitVec.le_def, BitVec.toNat_ofNat]; simp only [Nat.reducePow, Nat.reduceMod]
        rw [h10]; omega), h10]
      simp only [BitVec.toNat_ofNat]
      omega
    · show (st'.data.regs.getXReg .X11).toBitVec = _
      rw [hm'.regs .X11 _ rfl]
      show out m0 + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 ((24 : Nat) : Int) = _
      rw [ofInt_pos, NativeRustcVm.addr_add]
      congr 2

/-- **The single loop** from its head to `b9`. -/
theorem loopB (hp : Placed code k) {m0 : MachineData} (hpre : StackPointPre m0)
    (hfit : nn m0 ≤ 66) {i : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackPoint.b8Offset))
    (hI : InvB m0 i st.data) : Eventually (step1 Host.exe) (At9 k m0) st := by
  refine Sym.loop (fun n s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackPoint.b8Offset) ∧ ∃ i, len m0 - i = n ∧ InvB m0 i s.data)
    (fun n s ⟨hpc, i, hn, hI⟩ ↦ ?_) ⟨hpc, i, rfl, hI⟩
  refine Eventually.mono (stepB hp hpre hfit hpc hI) fun s' h ↦ ?_
  rcases h with h | ⟨hpc', hI'⟩
  · exact Or.inl h
  · exact Or.inr ⟨len m0 - (i + 1), by have := hI'.lt; omega, hpc', i + 1, rfl, hI'⟩

/-- **`b7`**: from `i` elements copied, the single loop's head. -/
theorem from7 (hp : Placed code k) {m0 : MachineData} (hpre : StackPointPre m0)
    (hfit : nn m0 ≤ 66) {i : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackPoint.b7Offset))
    (hc : Copy m0 i st.data) (hlt : i < len m0) (h9 : st.data.regs.X9 = m0.regs.X2)
    (h10 : st.data.regs.X10.toNat = i) : Eventually (step1 Host.exe) (At9 k m0) st := by
  have h64 : len m0 < 64 := hpre.2.2.2.2.2
  have hl3 : m0.regs.X3.toNat = len m0 := rfl
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) run_b7 (Env.wf_nil _) hpc (match_nil _)
    fun st' hm' hpc' ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.StackPoint.b7_length, NativeRustcVmArm.Vm.StackPoint.b7Length] at hpc'
  have he := regs_eq_of (match_nil _) hm' regsList rfl
  have hor : (BitVec.ofNat 64 8 ||| (st.data.regs.getXReg .X10).toBitVec <<< 4) =
      BitVec.ofNat 64 (16 * i + 8) := by
    rw [or8 _ (by show st.data.regs.X10.toNat < _; omega)]
    rw [show (st.data.regs.getXReg .X10).toBitVec.toNat = i from h10]
  refine loopB hp hpre hfit hpc' ⟨⟨hc.body.of_block (match_nil _) hm' (Env.wf_nil _) rfl
    (after_eq run_b7 ▸ b7_keeps), hc.regs.of he, by
      rw [show st'.data.regs.X8 = st.data.regs.X8 from Match.reg_eq (match_nil _) hm' (r := .X8) rfl rfl]
      exact hc.x8, hc.le, ?_⟩, hlt, ?_, ?_, ?_⟩
  · rw [Match.dmem_eq hm' (Env.wf_nil _) rfl]
    exact hc.copied
  · show (st'.data.regs.getXReg .X9).toBitVec = _
    rw [hm'.regs .X9 _ rfl]
    sym_simp
    simp only [Env.ofMachine_regs, hor]
    rw [show (st.data.regs.getXReg .X9) = m0.regs.X2 from h9]
  · show (st'.data.regs.getXReg .X10).toBitVec.toNat = _
    rw [hm'.regs .X10 _ rfl]
    sym_simp
    simp only [Env.ofMachine_regs]
    rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def]
      show st.data.regs.X10.toNat ≤ st.data.regs.X3.toNat
      rw [h10, hc.regs.x3]; omega)]
    show st.data.regs.X3.toNat - st.data.regs.X10.toNat = _
    rw [h10, hc.regs.x3]
  · show (st'.data.regs.getXReg .X11).toBitVec = _
    rw [hm'.regs .X11 _ rfl]
    sym_simp
    simp only [Env.ofMachine_regs, hor]
    rw [show (st.data.regs.getXReg .X5) = m0.regs.X5 from hc.regs.x5]

/-- **The pair loop** from its head to its exit. -/
theorem loopA (hp : Placed code k) {m0 : MachineData} (hpre : StackPointPre m0)
    (hfit : nn m0 ≤ 66) {i : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackPoint.b5Offset))
    (hI : InvA m0 i st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackPoint.b6Offset) ∧ Copy m0 (E m0) s.data ∧
        s.data.regs.X9 = m0.regs.X2 ∧ s.data.regs.X10.toNat = E m0) st := by
  refine Sym.loop (fun n s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackPoint.b5Offset) ∧ ∃ i, E m0 - i = n ∧ InvA m0 i s.data)
    (fun n s ⟨hpc, i, hn, hI⟩ ↦ ?_) ⟨hpc, i, rfl, hI⟩
  refine Eventually.mono (stepA hp hpre hfit hpc hI) fun s' h ↦ ?_
  rcases h with h | ⟨hpc', hI'⟩
  · exact Or.inl h
  · exact Or.inr ⟨E m0 - (i + 2), by have := hI'.lt; have := hI.lt; omega, hpc', i + 2, rfl, hI'⟩

/-- **`b6`**: after the pairs, done or one more element. -/
theorem from6 (hp : Placed code k) {m0 : MachineData} (hpre : StackPointPre m0)
    (hfit : nn m0 ≤ 66) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackPoint.b6Offset))
    (hc : Copy m0 (E m0) st.data) (h9 : st.data.regs.X9 = m0.regs.X2)
    (h10 : st.data.regs.X10.toNat = E m0) : Eventually (step1 Host.exe) (At9 k m0) st := by
  have hE : E m0 ≤ len m0 := Nat.div_mul_le_self _ _
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 (Env.wf_nil _) hpc (match_nil _)
    fun st' hm' hpc' ↦ ?_
  have he := regs_eq_of (match_nil _) hm' (.X8 :: .X9 :: .X10 :: regsList) rfl
  have hc' : Copy m0 (E m0) st'.data := ⟨hc.body.of_block (match_nil _) hm' (Env.wf_nil _) rfl
    (after_eq run_b6 ▸ b6_keeps), hc.regs.of fun r hr ↦ he r (by simp [hr]), by
      rw [show st'.data.regs.X8 = st.data.regs.X8 from he .X8 (by simp)]; exact hc.x8, hc.le, by
      rw [Match.dmem_eq hm' (Env.wf_nil _) rfl]; exact hc.copied⟩
  simp only [PcOk, NativeRustcVmArm.Vm.StackPoint.b6_length, NativeRustcVmArm.Vm.StackPoint.b6Length] at hpc'
  sym_simp at hpc'
  obtain ⟨hy, hn⟩ := pc_cond hpc'
  have h3 : (st.data.regs.getXReg .X3).toBitVec.toNat = len m0 := by
    show st.data.regs.X3.toNat = _; rw [hc.regs.x3]
  by_cases heq : len m0 = E m0
  · refine .done _ ⟨(hy ?_).trans (lbl_9 hp), ?_⟩
    · simp only [Env.ofMachine_regs, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [h3]; exact heq.trans h10.symm
    · rw [heq]; exact hc'
  · have h10' : st'.data.regs.X10 = st.data.regs.X10 := he .X10 (by simp)
    refine from7 hp hpre hfit (hn ?_) hc' (by omega) ((he .X9 (by simp)).trans h9)
      (by rw [h10']; exact h10)
    simp only [Env.ofMachine_regs, beq_iff_eq]
    intro h
    exact heq (h3.symm.trans ((congrArg BitVec.toNat h).trans h10))

/-- **`b4`**: the pair loop's set-up. -/
theorem from4 (hp : Placed code k) {m0 : MachineData} (hpre : StackPointPre m0)
    (hfit : nn m0 ≤ 66) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackPoint.b4Offset))
    (hc : Copy m0 0 st.data) (h9 : st.data.regs.X9 = m0.regs.X2) (h2 : 2 ≤ len m0) :
    Eventually (step1 Host.exe) (At9 k m0) st := by
  have h64 : len m0 < 64 := hpre.2.2.2.2.2
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 (Env.wf_nil _) hpc (match_nil _)
    fun st' hm' hpc' ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.StackPoint.b4_length, NativeRustcVmArm.Vm.StackPoint.b4Length] at hpc'
  have he := regs_eq_of (match_nil _) hm' (.X8 :: .X9 :: regsList) rfl
  have hand : (BinOp.apply .and .W64 (st.data.regs.getXReg .X3).toBitVec (BitVec.ofNat 64 62)).toNat
      = E m0 := by
    simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.toNat_and, BitVec.toNat_ofNat]
    show st.data.regs.X3.toNat &&& 62 = _
    rw [hc.regs.x3]
    exact and62 ⟨len m0, h64⟩
  have hE2 : 2 ≤ E m0 := by simp only [E]; omega
  refine Eventually.bind (loopA hp hpre hfit (i := 0) hpc' ⟨⟨hc.body.of_block (match_nil _) hm'
    (Env.wf_nil _) rfl (after_eq run_b4 ▸ b4_keeps), hc.regs.of fun r hr ↦ he r (by simp [hr]), by
      rw [show st'.data.regs.X8 = st.data.regs.X8 from he .X8 (by simp)]; exact hc.x8, hc.le, by
      rw [Match.dmem_eq hm' (Env.wf_nil _) rfl]; exact hc.copied⟩, rfl, hE2,
    (he .X9 (by simp)).trans h9, ?_, ?_, ?_, ?_⟩) fun s ⟨hpc, hc, h9, h10⟩ ↦
      from6 hp hpre hfit hpc hc h9 h10
  · show (st'.data.regs.getXReg .X10).toBitVec.toNat = _
    rw [hm'.regs .X10 _ rfl]
    exact hand
  · show (st'.data.regs.getXReg .X11).toBitVec = _
    rw [hm'.regs .X11 _ rfl]
    sym_simp
    simp only [Env.ofMachine_regs]
    rw [show st.data.regs.getXReg .X9 = m0.regs.X2 from h9]
  · show (st'.data.regs.getXReg .X12).toBitVec = _
    rw [hm'.regs .X12 _ rfl]
    sym_simp
    simp only [Env.ofMachine_regs]
    rw [show st.data.regs.getXReg .X5 = m0.regs.X5 from hc.regs.x5]
  · show (st'.data.regs.getXReg .X13).toBitVec.toNat = _
    rw [hm'.regs .X13 _ rfl]
    exact hand

omit [Host] in
theorem ewsAt_nil (d : Mem 64) (a : BitVec 64) : EWsAt d a [] := fun i h ↦ absurd h (by simp)

/-- **`b1`-`b3`**: from the prologue, the copy's set-up. -/
theorem from1 (hp : Placed code k) {m0 : MachineData} (hpre : StackPointPre m0)
    (hfit : nn m0 ≤ 66) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackPoint.b1Offset))
    (hb : Body m0 16 S slots (out m0) outB st.data) (hR : Regs m0 st.data)
    (h9 : st.data.regs.X9 = m0.regs.X2) : Eventually (step1 Host.exe) (At9 k m0) st := by
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 (Env.wf_nil _) hpc (match_nil _)
    fun st1 hm1 hpc1 ↦ ?_
  have he1 := regs_eq_of (match_nil _) hm1 (.X9 :: regsList) rfl
  have hx8 : st1.data.regs.X8.toBitVec = out m0 + BitVec.ofNat 64 (16 * len m0) := by
    show (st1.data.regs.getXReg .X8).toBitVec = _
    rw [hm1.regs .X8 _ rfl]
    sym_simp
    simp only [Env.ofMachine_regs]
    rw [show st.data.regs.getXReg .X5 = m0.regs.X5 from hR.x5,
      show st.data.regs.getXReg .X3 = m0.regs.X3 from hR.x3, Arrays.shl4]
    rfl
  have hc1 : Copy m0 0 st1.data := ⟨hb.of_block (match_nil _) hm1 (Env.wf_nil _) rfl
    (after_eq run_b1 ▸ b1_keeps), hR.of fun r hr ↦ he1 r (by simp [hr]), hx8, Nat.zero_le _,
    ewsAt_nil _ _⟩
  have h3 : (st.data.regs.getXReg .X3).toBitVec.toNat = len m0 := by
    show st.data.regs.X3.toNat = _; rw [hR.x3]
  simp only [PcOk, NativeRustcVmArm.Vm.StackPoint.b1_length, NativeRustcVmArm.Vm.StackPoint.b1Length] at hpc1
  sym_simp at hpc1
  obtain ⟨hy, hn⟩ := pc_cond hpc1
  have h91 : st1.data.regs.X9 = m0.regs.X2 := (he1 .X9 (by simp)).trans h9
  by_cases h0 : len m0 = 0
  · exact .done _ ⟨(hy ((beq_iff (by decide)).mpr (h3.trans h0))).trans (lbl_9 hp),
      by rw [h0]; exact hc1⟩
  · have hpc2 := hn fun h ↦ h0 (h3.symm.trans ((beq_iff (by decide)).mp h))
    refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 (Env.wf_nil _) hpc2
      (match_nil _) fun st2 hm2 hpc2' ↦ ?_
    have he2 := regs_eq_of (match_nil _) hm2 (.X8 :: .X9 :: regsList) rfl
    have hc2 : Copy m0 0 st2.data := ⟨hc1.body.of_block (match_nil _) hm2 (Env.wf_nil _) rfl
      (after_eq run_b2 ▸ b2_keeps), hc1.regs.of fun r hr ↦ he2 r (by simp [hr]), by
        rw [show st2.data.regs.X8 = st1.data.regs.X8 from he2 .X8 (by simp)]; exact hc1.x8,
      Nat.zero_le _, ewsAt_nil _ _⟩
    have h92 : st2.data.regs.X9 = m0.regs.X2 := (he2 .X9 (by simp)).trans h91
    have h31 : (st1.data.regs.getXReg .X3).toBitVec.toNat = len m0 := by
      show st1.data.regs.X3.toNat = _; rw [hc1.regs.x3]
    simp only [PcOk, NativeRustcVmArm.Vm.StackPoint.b2_length, NativeRustcVmArm.Vm.StackPoint.b2Length] at hpc2'
    sym_simp at hpc2'
    obtain ⟨hy2, hn2⟩ := pc_cond hpc2'
    by_cases h1 : len m0 = 1
    · have hpc3 := hn2 fun h ↦ ((not_beq_iff (by decide)).mp h) (h31.trans h1)
      refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 (Env.wf_nil _) hpc3
        (match_nil _) fun st3 hm3 hpc3' ↦ ?_
      have he3 := regs_eq_of (match_nil _) hm3 (.X8 :: .X9 :: regsList) rfl
      simp only [PcOk] at hpc3'
      refine from7 hp hpre hfit (hpc3'.trans (lbl_7 hp)) ⟨hc2.body.of_block (match_nil _) hm3
        (Env.wf_nil _) rfl (after_eq run_b3 ▸ b3_keeps), hc2.regs.of fun r hr ↦ he3 r
        (by simp [hr]), by
          rw [show st3.data.regs.X8 = st2.data.regs.X8 from he3 .X8 (by simp)]; exact hc2.x8,
        Nat.zero_le _, ewsAt_nil _ _⟩ (by omega) ((he3 .X9 (by simp)).trans h92) ?_
      show (st3.data.regs.getXReg .X10).toBitVec.toNat = 0
      rw [hm3.regs .X10 _ rfl]
      rfl
    · exact from4 hp hpre hfit ((hy2 ((not_beq_iff (by decide)).mpr fun h ↦
        h1 (h31.symm.trans h))).trans (lbl_4 hp)) hc2 h92 (by omega)

omit [Host] in
theorem shr_toNat (x0 x1 : BitVec 64) :
    (if (!(x0.ult 63#64) && !(x0 == 63#64)) = true then 0#64
      else x1.ushiftRight (x0.toNat % RegWidth.W64.bits)).toNat = x1.toNat >>> x0.toNat := by
  have hb : RegWidth.W64.bits = 64 := rfl
  split
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true', BitVec.ult, decide_eq_false_iff_not,
      beq_eq_false_iff_ne, BitVec.toNat_ofNat] at hc
    have h : 63 < x0.toNat := by
      have h1 := hc.1
      have h2 : x0.toNat ≠ 63 := fun he ↦ hc.2 (BitVec.eq_of_toNat_eq (by rw [he]; rfl))
      simp only [Nat.reducePow, Nat.reduceMod] at h1
      omega
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt]
    · rfl
    · exact Nat.lt_of_lt_of_le x1.isLt (Nat.pow_le_pow_right (by decide) (by omega))
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true', BitVec.ult, decide_eq_false_iff_not,
      beq_eq_false_iff_ne, BitVec.toNat_ofNat, not_and, Classical.not_not] at hc
    have h : x0.toNat ≤ 63 := by
      by_cases h1 : x0.toNat < 63
      · omega
      · have := hc (by simpa using h1)
        rw [this]; decide
    rw [hb, Nat.mod_eq_of_lt (by omega)]
    exact BitVec.toNat_ushiftRight _ _

omit [Host] in
theorem not_inRange_of_apart' {a b p : BitVec 64} {n m : Nat} (h : Apart a n b m)
    (ha : NoWrap a n) (hb : NoWrap b m) (hp : InRange b m p) : ¬InRange a n p := by
  unfold NoWrap at ha hb
  unfold Apart at h
  rw [inRange_iff hb] at hp
  rw [inRange_iff ha]
  omega

/-- **`b9`-`b11`**: the selector after the point, and the return. -/
theorem from9 (hp : Placed code k)
    (hsel : Spec (Labels.label NativeRustcVmArm.Vm.SelectorPoint.entryLabel) SelectorPointPre SelectorPointPost)
    {m0 : MachineData} (hpre : StackPointPre m0) (hfit : nn m0 ≤ 66) {st : MachineState}
    (h9 : At9 k m0 st) : Eventually (step1 Host.exe) (Post m0) st := by
  obtain ⟨hpc, hc⟩ := h9
  have hfit' : len m0 + tl m0 ≤ 66 := hfit
  have hS := hpre.1
  have hro := hpre.2.2.1
  have hnwo : NoWrap (out m0) outB := hro.2
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) run_b9 (Env.wf_nil _) hpc (match_nil _)
    fun st9 hm9 hpc9 ↦ ?_
  have bd9 := hc.body.of_block (match_nil _) hm9 (Env.wf_nil _) rfl (after_eq run_b9 ▸ b9_keeps)
  have h1 : st9.data.regs.X1.toBitVec = out m0 + BitVec.ofNat 64 (16 * len m0) := by
    rw [show st9.data.regs.X1 = st.data.regs.X8 from UInt64.toBitVec_inj.mp (hm9.regs .X1 _ rfl)]
    exact hc.x8
  have h2 : st9.data.regs.X2.toNat = tl m0 := by
    rw [show st9.data.regs.X2 = st.data.regs.X2 from UInt64.toBitVec_inj.mp (hm9.regs .X2 _ rfl)]
    exact hc.regs.x2
  have h0 : st9.data.regs.X0.toNat = m0.regs.X1.toNat >>> m0.regs.X0.toNat := by
    show (st9.data.regs.getXReg .X0).toBitVec.toNat = _
    rw [hm9.regs .X0 _ rfl]
    sym_simp
    rw [shr_toNat]
    simp only [Env.ofMachine_regs]
    rw [show st.data.regs.getXReg .X1 = m0.regs.X1 from hc.regs.x1,
      show st.data.regs.getXReg .X0 = m0.regs.X0 from hc.regs.x0]
    rfl
  simp only [NativeRustcVmArm.Vm.StackPoint.b9_length, NativeRustcVmArm.Vm.StackPoint.b9Length] at hpc9
  have hrd : Readable st9.data st9.data.regs.X1.toBitVec (16 * st9.data.regs.X2.toNat) := by
    rw [h1, h2]
    exact readable_sub hro bd9.kept (by show _ ≤ 16 * 66; omega)
  refine call_then hpc9 hsel hrd fun st3 hpc3 hpost ↦ ?_
  have hR : ∀ p, (InRange st9.data.regs.X1.toBitVec (16 * st9.data.regs.X2.toNat) p ∨
      InRange (stackBelow st9.data selectorPointStack) selectorPointStack p) →
      InRange (out m0) outB p ∧
        ¬InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 16) 16 p := by
    intro p hp'
    rcases hp' with hp' | hp'
    · rw [h1, h2] at hp'
      have hin : InRange (out m0) outB p := inRange_mono hp' (by show _ ≤ 16 * 66; omega)
      exact ⟨hin, not_inRange_of_apart' (apart_frame hS (by decide) hpre.2.2.2.1)
        (frame_ok hS (by decide)).2.1 hnwo hin⟩
    · exact absurd hp' (by unfold InRange; simp [selectorPointStack])
  have bd3 := Body.of_call bd9 hpost.2.1 hR hpost.2.2 (by simp [slots]) (Nat.le_trans
    (by decide) hS.2.1)
  have hd9 : st9.data.dmem = st.data.dmem := hm9.dmem_eq (Env.wf_nil _) rfl
  have hcp : EWsAt st3.data.dmem (out m0) (ptl m0) := by
    have := hc.copied
    rw [List.take_of_length_le (by simp)] at this
    refine Arrays.bytesAt_congr this fun j hj ↦ ?_
    rw [Arrays.length_flatMap_ewBytes, NativeRustcVm.length_ewsOf] at hj
    rw [hpost.2.1 _ fun h ↦ ?_, hd9]
    rcases h with h | h
    · rw [h1, h2] at h
      by_cases ht : tl m0 = 0
      · rw [ht] at h; exact absurd h (by unfold InRange; simp)
      rw [inRange_iff (by
          rw [toNat_add_ofNat' (by have : (out m0).toNat + 1056 ≤ 2 ^ 64 := hnwo; omega)]
          have : (out m0).toNat + 1056 ≤ 2 ^ 64 := hnwo; omega),
        toNat_add_ofNat' (by have : (out m0).toNat + 1056 ≤ 2 ^ 64 := hnwo; omega),
        toNat_add_ofNat' (by have : (out m0).toNat + 1056 ≤ 2 ^ 64 := hnwo; omega)] at h
      omega
    · exact absurd h (by unfold InRange; simp [selectorPointStack])
  have hsel' := hpost.1
  rw [h1, h0, h2] at hsel'
  refine exec_at (infix_of b10_in_code (by simp [b10]) hp) run_b10 (Env.wf_nil _) hpc3
    (match_nil _) fun st10 hm10 hpc10 ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.StackPoint.b10_length, NativeRustcVmArm.Vm.StackPoint.b10Length] at hpc10
  have hd10 : st10.data.dmem = st3.data.dmem := hm10.dmem_eq (Env.wf_nil _) rfl
  have h19 : st10.data.regs.X19 = st.data.regs.X19 :=
    (Match.reg_eq (match_nil _) hm10 (r := .X19) rfl rfl).trans ((hpost.2.2.1 .X19 rfl).trans
      (Match.reg_eq (match_nil _) hm9 (r := .X19) rfl rfl))
  refine finish hp hpre hpc10 (bd3.of_block (match_nil _) hm10 (Env.wf_nil _) rfl
    (after_eq run_b10 ▸ b10_keeps)) (fun _ ↦ ⟨UInt64.toBitVec_inj.mp (hm10.regs .X8 _ rfl),
      by rw [h19]; exact hc.regs.x19, ?_⟩) (fun h ↦ absurd hfit h)
  have hres : res m0 = ptl m0 ++
      (selectorPoint (m0.regs.X1.toNat >>> m0.regs.X0.toNat) (tl m0)).toList := by
    simp [res, stackPoint, slice]
  rw [hres, hd10, NativeRustcVm.ewsAt_append, NativeRustcVm.length_ewsOf]
  exact ⟨hcp, hsel'⟩

omit [Host] in
theorem tail_toNat (x0 x4 : BitVec 64) :
    (if x4.ult x0 = true then 0#64 else x4 - x0).toNat = x4.toNat - x0.toNat := by
  split
  · rename_i h
    simp only [BitVec.ult, decide_eq_true_eq] at h
    simp; omega
  · rename_i h
    simp only [BitVec.ult, decide_eq_true_eq] at h
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]

omit [Host] in
/-- `b0`'s test: `n` past `66`, or its sum overflowing. -/
theorem cond_b0 (T x3 : BitVec 64) (t : Nat) (ht : T.toNat = t) :
    (!(if (BitVec.ult (T + x3) 66#64 || (T + x3 == 66#64)) = true then !BitVec.ult (T + x3) x3
      else false)) = true ↔ ¬(x3.toNat + t ≤ 66) := by
  have hx3 := x3.isLt
  have hT := T.isLt
  have hY : (T + x3).toNat = (t + x3.toNat) % 2 ^ 64 := by rw [BitVec.toNat_add, ht]
  have e1 : BitVec.ult (T + x3) 66#64 = decide ((t + x3.toNat) % 2 ^ 64 < 66) := by
    simp [BitVec.ult, hY]
  have e2 : (T + x3 == 66#64) = decide ((t + x3.toNat) % 2 ^ 64 = 66) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← hY]
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)
  have e3 : BitVec.ult (T + x3) x3 = decide ((t + x3.toNat) % 2 ^ 64 < x3.toNat) := by
    simp [BitVec.ult, hY]
  rw [e1, e2, e3]
  by_cases a : (t + x3.toNat) % 2 ^ 64 < 66 <;> by_cases b : (t + x3.toNat) % 2 ^ 64 = 66 <;>
    by_cases c : (t + x3.toNat) % 2 ^ 64 < x3.toNat <;> simp_all <;> omega

/-- **`stack_point` meets its contract.** -/
theorem stackPoint_spec (hp : Placed code k)
    (hsel : Spec (Labels.label NativeRustcVmArm.Vm.SelectorPoint.entryLabel) SelectorPointPre SelectorPointPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.StackPoint.entryLabel) StackPointPre StackPointPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  obtain ⟨hwf, hm⟩ := entry_match (F := 16) hpre.1 (by decide) rfl
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf hm fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hw, hmem, hregs⟩ := after_eq run_b0 ▸ b0_frame
  have hb : Body m0 16 S slots (out m0) outB st1.data :=
    Body.of_entry hpre.1 (by decide) hm1 rfl hw hregs hmem
  simp only [PcOk, NativeRustcVmArm.Vm.StackPoint.b0_length, NativeRustcVmArm.Vm.StackPoint.b0Length] at hpc1
  sym_simp at hpc1
  obtain ⟨hy, hn⟩ := pc_cond hpc1
  have hT := tail_toNat ((Arrays.frameEnv m0 m0 16).regs .X0) ((Arrays.frameEnv m0 m0 16).regs .X4)
  have hfit' : m0.regs.X3.toNat + tl m0 ≤ 66 ↔ nn m0 ≤ 66 := Iff.rfl
  by_cases hfit : nn m0 ≤ 66
  · have hpc := hn fun h ↦ ((cond_b0 _ _ _ hT).mp h) (hfit'.mpr hfit)
    have hx2 : st1.data.regs.X2.toNat = tl m0 := by
      show (st1.data.regs.getXReg .X2).toBitVec.toNat = _
      rw [hm1.regs .X2 _ rfl]
      sym_simp
      exact hT
    have hx19 : st1.data.regs.X19.toNat = nn m0 := by
      show (st1.data.regs.getXReg .X19).toBitVec.toNat = _
      rw [hm1.regs .X19 _ rfl]
      sym_simp
      rw [BitVec.toNat_add, hT]
      show (tl m0 + m0.regs.X3.toNat) % 2 ^ 64 = _
      have : nn m0 = m0.regs.X3.toNat + tl m0 := rfl
      omega
    have hR : Regs m0 st1.data := ⟨UInt64.toBitVec_inj.mp (hm1.regs .X0 _ rfl),
      UInt64.toBitVec_inj.mp (hm1.regs .X1 _ rfl), hx2, UInt64.toBitVec_inj.mp (hm1.regs .X3 _ rfl),
      UInt64.toBitVec_inj.mp (hm1.regs .X5 _ rfl), hx19⟩
    exact Eventually.bind (from1 hp hpre hfit hpc hb hR (UInt64.toBitVec_inj.mp (hm1.regs .X9 _ rfl)))
      fun s hs ↦ from9 hp hsel hpre hfit hs
  · exact finish hp hpre ((hy ((cond_b0 _ _ _ hT).mpr fun h ↦ hfit (hfit'.mp h))).trans (lbl_10 hp))
      hb (fun h ↦ absurd h hfit) fun _ ↦ UInt64.toBitVec_inj.mp (hm1.regs .X8 _ rfl)

end

end NativeRustcVmArm.Layout.StackPoint
