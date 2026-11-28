module

public import NativeRustcVmArm.Code.Vm.Dot.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Arrays.Dot.Exec
public import NativeRustcVm.Arrays.Folds

/-!
# `dot` on AArch64

**`dot_spec`**: rustc's `dot`, placed anywhere in the program, meets `DotPre`/`DotPost` given
`EW::mul`'s contract. The prologue (`b0`) saves X19-X23 and X30 in its 48-byte frame and takes the
common length `n`; at `n = 0` it returns `0` (`b5`); else the loop (`b2`, `EW::mul`, `b3`) adds
`left[i]·right[i]` to the accumulator (X20, X19) for `i < n` (`Inv`), and the epilogue (`b4`)
returns it.
-/

namespace NativeRustcVmArm.Arrays.Dot

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Dot NativeVm.Model
open NativeRustcVm (ewsOf ewOf)

public section

/-- The left slice at the entry. -/
abbrev lft (m : MachineData) : List EW := ewsOf m.dmem m.regs.X0.toBitVec m.regs.X1.toNat
/-- The right slice at the entry. -/
abbrev rgt (m : MachineData) : List EW := ewsOf m.dmem m.regs.X2.toBitVec m.regs.X3.toNat
/-- The common length. -/
abbrev cnt (m : MachineData) : Nat := min m.regs.X1.toNat m.regs.X3.toNat

/-- The sum of the first `i` products. -/
def acc (m : MachineData) (i : Nat) : EW :=
  (List.zipWith (· * ·) ((lft m).take i) ((rgt m).take i)).foldl (· + ·) 0

theorem dot_eq_acc (m : MachineData) :
    dot (slice m m.regs.X0 m.regs.X1) (slice m m.regs.X2 m.regs.X3) = acc m (cnt m) := by
  unfold slice acc
  rw [NativeRustcVm.dot_eq, NativeRustcVm.zipWith_take_min]
  simp

theorem acc_succ (m : MachineData) {i : Nat} (h : i < cnt m) :
    acc m (i + 1) = acc m i + (lft m)[i]'(by simp; exact Nat.lt_of_lt_of_le h (Nat.min_le_left _ _)) *
      (rgt m)[i]'(by simp; exact Nat.lt_of_lt_of_le h (Nat.min_le_right _ _)) :=
  NativeRustcVm.zipFold_take_succ _ _ _ _ _ _ _

/-- **The loop head** `.LDot_2`, `i` products summed. -/
structure Inv (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  body : Body m0 48 dotStack slots 0 0 st
  lt : i < cnt m0
  x21 : st.regs.X21.toNat = cnt m0 - i
  x23 : st.regs.X23.toBitVec = m0.regs.X0.toBitVec + BitVec.ofNat 64 (16 * i + 8)
  x22 : st.regs.X22.toBitVec = m0.regs.X2.toBitVec + BitVec.ofNat 64 (16 * i + 8)
  acc : (⟨st.regs.X20, st.regs.X19⟩ : EW) = acc m0 i

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Dot.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Dot.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2a.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Dot.b2Offset) ∧
    b2b.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Dot.b2Offset + 2) := by
  have h := b2_in_code.trans hp.1 (by simp [b2])
  rw [← List.take_append_drop 2 b2] at h
  exact h.append
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Dot.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Dot.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Dot.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.Dot.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.Dot.b0Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.Dot.entryOffset) NativeRustcVmArm.Vm.Dot.entry_at
theorem lbl_2 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.Dot.label_2 = Host.addrOf (k + NativeRustcVmArm.Vm.Dot.b2Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.Dot.b2Offset) NativeRustcVmArm.Vm.Dot.label_2_at
theorem lbl_4 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.Dot.label_4 = Host.addrOf (k + NativeRustcVmArm.Vm.Dot.b5Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.Dot.b5Offset) NativeRustcVmArm.Vm.Dot.label_4_at

/-- `dot`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ DotPost m0 st.data

/-- **The epilogue** `b4`: from the loop's exit, the sum returned. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hpre : DotPre m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Dot.b4Offset)) (hb : Body m0 48 dotStack slots 0 0 st.data)
    (hacc : (⟨st.data.regs.X20, st.data.regs.X19⟩ : EW) = acc m0 (cnt m0)) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hS := hpre.1
  have h48 : 48 ≤ dotStack := by decide
  obtain ⟨hmap, hnw, -⟩ := frame_ok hS h48
  have hwf := wf_one (m := st.data) (fun i hi ↦ hb.kept _ (hmap i hi)) hnw
  have hm : Match (Env.ofMachine st.data [(m0.regs.SP.toBitVec - BitVec.ofNat 64 48, 48)]) exitS
      st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h48 rfl, trivial⟩
      (by rw [hb.sp]; simp [Sym.eval]) trivial trivial trivial trivial
  refine exec_at (hb4 hp) run_b4 hwf hpc hm fun st' hm' hpc' ↦ .done _ ?_
  obtain ⟨hsaved, hx30, hdm⟩ := hb.saved hm' hwf (List.mem_map.mpr ⟨(0, .X30), by simp [slots], rfl⟩) (after_eq run_b4 ▸ b4_restores) rfl
  have h0 := hm'.regs .X0 _ rfl
  have h1 := hm'.regs .X1 _ rfl
  simp only [Sym.eval, Env.ofMachine_regs] at h0 h1
  refine ⟨?_, ?_, ?_, hsaved⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    simp only [retOf, hx30]
  · rw [dot_eq_acc, ← hacc]
    show (⟨st'.data.regs.getXReg .X0, st'.data.regs.getXReg .X1⟩ : EW) = _
    rw [UInt64.toBitVec_inj.mp h0, UInt64.toBitVec_inj.mp h1]
    rfl
  · intro p hp'
    rw [hdm]
    exact hb.same p hp'

/-- **A turn of the loop**: `left[i]·right[i]` added, back at the head or out of the loop and
returned. -/
theorem step (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : DotPre m0) {i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Dot.b2Offset)) (hI : Inv m0 i st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Dot.b2Offset) ∧ Inv m0 (i + 1) st'.data)) st := by
  obtain ⟨hS, ⟨hrL, hoL⟩, ⟨hrR, hoR⟩⟩ := hpre
  have hlt := hI.lt
  have hiL : i < m0.regs.X1.toNat := Nat.lt_of_lt_of_le hI.lt (Nat.min_le_left _ _)
  have hiR : i < m0.regs.X3.toNat := Nat.lt_of_lt_of_le hI.lt (Nat.min_le_right _ _)
  -- `left[i]`
  obtain ⟨hmA, hnA⟩ := elem_mapped hrL hI.body.kept hiL
  have hwf1 := wf_one hmA hnA (m := st.data)
  have hm1 : Match (Env.ofMachine st.data
      [(m0.regs.X0.toBitVec + BitVec.ofNat 64 (16 * i), 16)]) (ldS .X23) st.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
      ⟨by
        show st.data.regs.X23.toBitVec = _ + BitVec.ofInt 64 8
        rw [hI.x23, base0, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, addr_add],
       trivial⟩ trivial trivial trivial
  refine exec_at (hb2 hp).1 run_b2a hwf1 hpc hm1 fun st1 hm1' hpc1 ↦ ?_
  simp only [PcOk, show b2a.length = 2 from rfl] at hpc1
  have hb1 := hI.body.of_block hm1 hm1' hwf1 rfl (after_eq run_b2a ▸ b2a_keeps)
  have hL : (⟨st1.data.regs.getXReg .X0, st1.data.regs.getXReg .X1⟩ : EW) =
      (lft m0)[i]'(by simp; exact hiL) := by
    rw [ew_of_loads (off := 0) hm1' rfl rfl, add_ofNat_zero]
    exact elem_of_apart hI.body.same hS hrL.2 hoL (apart_zero _ _) noWrap_zero hiL
  have e1 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23], st1.data.regs.getXReg r =
      st.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm1 hm1' rfl rfl
  -- `right[i]`, then the call
  obtain ⟨hmB, hnB⟩ := elem_mapped hrR hb1.kept hiR
  have hwf2 := wf_one hmB hnB (m := st1.data)
  have hm2 : Match (Env.ofMachine st1.data
      [(m0.regs.X2.toBitVec + BitVec.ofNat 64 (16 * i), 16)]) (ldS .X22) st1.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
      ⟨by
        show (st1.data.regs.getXReg .X22).toBitVec = _ + BitVec.ofInt 64 8
        rw [e1 .X22 (by simp), show (st.data.regs.getXReg .X22) = st.data.regs.X22 from rfl,
          hI.x22, base0, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, addr_add],
       trivial⟩ trivial trivial trivial
  refine exec_at (hb2 hp).2 run_b2b hwf2 hpc1 hm2 fun st2 hm2' hpc2 ↦ ?_
  simp only [show b2b.length = 2 from rfl] at hpc2
  have hb2' := hb1.of_block hm2 hm2' hwf2 rfl (after_eq run_b2b ▸ b2b_keeps)
  have hR : (⟨st2.data.regs.getXReg .X2, st2.data.regs.getXReg .X3⟩ : EW) =
      (rgt m0)[i]'(by simp; exact hiR) := by
    rw [ew_of_loads (off := 0) hm2' rfl rfl, add_ofNat_zero]
    exact elem_of_apart hb1.same hS hrR.2 hoR (apart_zero _ _) noWrap_zero hiR
  have e2 : ∀ r ∈ [XReg.X0, .X1, .X19, .X20, .X21, .X22, .X23], st2.data.regs.getXReg r =
      st1.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm2 hm2' rfl rfl
  refine call_then hpc2 hmul (hb2'.ewMulPre hS (by decide) (by decide)) fun st3 hpc3 hpost ↦ ?_
  have hb3' := hb2'.call hS (by decide) (by decide) hpost
  have hprod : (⟨st3.data.regs.X0, st3.data.regs.X1⟩ : EW) =
      (lft m0)[i]'(by simp; exact hiL) * (rgt m0)[i]'(by simp; exact hiR) := by
    have hL2 : (⟨st2.data.regs.X0, st2.data.regs.X1⟩ : EW) = (lft m0)[i]'(by simp; exact hiL) := by
      rw [← hL]; exact congr (congrArg EW.mk (e2 .X0 (by simp))) (e2 .X1 (by simp))
    have hR2 : (⟨st2.data.regs.X2, st2.data.regs.X3⟩ : EW) = (rgt m0)[i]'(by simp; exact hiR) := hR
    rw [hpost.1, hpost.2.1, hL2, hR2]
    rfl
  have e3 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23], st3.data.regs.getXReg r =
      st.data.regs.getXReg r := by
    intro r hr
    have hc : calleeSaved r = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [hpost.2.2.2.1 r hc, e2 r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)), e1 r hr]
  -- `b3`: accumulate, count, advance
  refine exec_at (hb3 hp) run_b3 (Env.wf_nil _) hpc3 (match_nil _) fun st4 hm4 hpc4 ↦ ?_
  have hb4' := hb3'.of_block (match_nil _) hm4 (Env.wf_nil _) rfl (after_eq run_b3 ▸ b3_keeps)
  have h19 := hm4.regs .X19 _ rfl
  have h20 := hm4.regs .X20 _ rfl
  have h21 := hm4.regs .X21 _ rfl
  have h22 := hm4.regs .X22 _ rfl
  have h23 := hm4.regs .X23 _ rfl
  sym_simp at h19 h20 h21 h22 h23
  simp only [Env.ofMachine_regs, e3 _ (by simp : XReg.X19 ∈ _), e3 _ (by simp : XReg.X20 ∈ _),
    e3 _ (by simp : XReg.X21 ∈ _), e3 _ (by simp : XReg.X22 ∈ _),
    e3 _ (by simp : XReg.X23 ∈ _)] at h19 h20 h21 h22 h23
  have hcnt : 1 ≤ st.data.regs.X21.toNat := by rw [hI.x21]; have := hI.lt; omega
  have hacc : (⟨st4.data.regs.X20, st4.data.regs.X19⟩ : EW) = acc m0 (i + 1) := by
    rw [acc_succ m0 hI.lt, ← hI.acc, ← hprod]
    show (⟨st4.data.regs.getXReg .X20, st4.data.regs.getXReg .X19⟩ : EW) = _
    rw [UInt64.toBitVec_inj.mp (h20.trans (by rw [← UInt64.toBitVec_xor])),
      UInt64.toBitVec_inj.mp (h19.trans (by rw [← UInt64.toBitVec_xor])),
      UInt64.xor_comm (st3.data.regs.getXReg .X0), UInt64.xor_comm (st3.data.regs.getXReg .X1)]
    rfl
  have hx21 : st4.data.regs.X21.toNat = cnt m0 - i - 1 := by
    show (st4.data.regs.getXReg .X21).toBitVec.toNat = _
    rw [h21, BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def, BitVec.toNat_ofNat]; exact hcnt)]
    show st.data.regs.X21.toNat - 1 % 2 ^ 64 = _
    rw [hI.x21]
  simp only [PcOk] at hpc4
  sym_simp at hpc4
  simp only [Env.ofMachine_regs, e3 _ (by simp : XReg.X21 ∈ _)] at hpc4
  by_cases hlast : i + 1 = cnt m0
  · have : (st.data.regs.getXReg .X21).toBitVec = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      show st.data.regs.X21.toNat = 1
      rw [hI.x21]; omega
    rw [this] at hpc4
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_false,
      NativeRustcVmArm.Vm.Dot.b3_length, NativeRustcVmArm.Vm.Dot.b3Length] at hpc4
    refine Eventually.mono (finish hp ⟨hS, ⟨hrL, hoL⟩, ⟨hrR, hoR⟩⟩ hpc4 hb4' ?_) fun _ h ↦ Or.inl h
    rw [hacc, hlast]
  · have : ((st.data.regs.getXReg .X21).toBitVec == 1#64) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      have := congrArg BitVec.toNat h
      change st.data.regs.X21.toNat = 1 at this
      rw [hI.x21] at this
      omega
    rw [this] at hpc4
    simp only [Bool.not_false, ite_true] at hpc4
    refine .done _ (Or.inr ⟨hpc4.trans (lbl_2 hp), hb4', by omega, by rw [hx21]; omega, ?_, ?_, hacc⟩)
    · show (st4.data.regs.getXReg .X23).toBitVec = _
      rw [h23, show (st.data.regs.getXReg .X23) = st.data.regs.X23 from rfl, hI.x23, addr_add]
      congr 2
    · show (st4.data.regs.getXReg .X22).toBitVec = _
      rw [h22, show (st.data.regs.getXReg .X22) = st.data.regs.X22 from rfl, hI.x22, addr_add]
      congr 2

/-- **`dot` meets its contract.** -/
theorem dot_spec (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.Dot.entryLabel) DotPre DotPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  have hS := hpre.1
  have h48 : 48 ≤ dotStack := by decide
  obtain ⟨hmap, hnw, -⟩ := frame_ok hS h48
  have hwf := wf_one hmap hnw (m := m0)
  have hm : Match (Env.ofMachine m0 [(m0.regs.SP.toBitVec - BitVec.ofNat 64 48, 48)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h48 rfl, trivial⟩
      (by
        show _ = (m0.regs.SP.toBitVec - BitVec.ofNat 64 48) + BitVec.ofInt 64 48
        rw [show BitVec.ofInt 64 48 = BitVec.ofNat 64 48 from rfl, BitVec.sub_add_cancel])
      trivial trivial trivial trivial
  have hcnt := min_toNat (m0.regs.getXReg .X1).toBitVec (m0.regs.getXReg .X3).toBitVec
  refine exec_then (hb0 hp) run_b0 hwf hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.Dot.b0_length, NativeRustcVmArm.Vm.Dot.b0Length] at hpc1
  sym_simp at hpc1
  have hpc1' := pc_cond hpc1
  have hc : (((if (m0.regs.getXReg .X3).toBitVec.ult (m0.regs.getXReg .X1).toBitVec then
      (m0.regs.getXReg .X3).toBitVec else (m0.regs.getXReg .X1).toBitVec) == 0#64) = true) ↔
      cnt m0 = 0 := by
    rw [beq_iff_eq]
    constructor
    · intro h
      have hc' := hcnt
      rw [h] at hc'
      show min (m0.regs.getXReg .X1).toBitVec.toNat (m0.regs.getXReg .X3).toBitVec.toNat = 0
      rw [← hc']
      rfl
    · intro h; apply BitVec.eq_of_toNat_eq; rw [hcnt]; exact h
  by_cases hz' : cnt m0 = 0
  · -- `n = 0`: return `0`.
    have hpc1 := hpc1'.1 (hc.mpr hz')
    refine exec_at (hb5 hp) (exec_after run_b0 run_b5) hwf (hpc1.trans (lbl_4 hp)) hm1
      fun st2 hm2 hpc2 ↦ .done _ ⟨?_, ?_, ?_, ?_⟩
    · simp only [PcOk] at hpc2
      rw [hpc2]
      simp only [retOf]
      rw [show st2.data.regs.X30 = m0.regs.X30 from Match.reg_eq (r := .X30) hm hm2 rfl rfl]
    · rw [dot_eq_acc, hz']
      have h0 := hm2.regs .X0 _ rfl
      have h1 := hm2.regs .X1 _ rfl
      simp only [Sym.eval] at h0 h1
      show (⟨st2.data.regs.getXReg .X0, st2.data.regs.getXReg .X1⟩ : EW) = _
      rw [UInt64.toBitVec_inj.mp (h0.trans rfl), UInt64.toBitVec_inj.mp (h1.trans rfl)]
      rfl
    · exact changes_of_frame hS h48 hm2 (after_eq run_b5 ▸ b5_frame)
    · exact Match.saved hm hm2 hwf rfl (after_eq run_b5 ▸ b5_keeps)
  · -- `n > 0`: the loop.
    have hpc1 := hpc1'.2 (fun h ↦ hz' (hc.mp h))
    have hpos : 0 < cnt m0 := Nat.pos_of_ne_zero hz'
    refine exec_at (hb1 hp) (exec_after run_b0 run_b1) hwf hpc1 hm1 fun st2 hm2 hpc2 ↦ ?_
    simp only [PcOk, NativeRustcVmArm.Vm.Dot.b1_length, NativeRustcVmArm.Vm.Dot.b1Length] at hpc2
    obtain ⟨hw, hmem, hregs⟩ := after_eq run_b1 ▸ b1_frame
    have hI : Inv m0 0 st2.data := by
      have h19 := hm2.regs .X19 _ rfl
      have h20 := hm2.regs .X20 _ rfl
      have h21 := hm2.regs .X21 _ rfl
      have h22 := hm2.regs .X22 _ rfl
      have h23 := hm2.regs .X23 _ rfl
      sym_simp at h19 h20 h21 h22 h23
      simp only [Env.ofMachine_regs] at h19 h20 h21 h22 h23
      refine ⟨Body.of_entry hS h48 hm2 rfl hw hregs hmem, hpos, ?_, ?_, ?_, ?_⟩
      · show (st2.data.regs.getXReg .X21).toBitVec.toNat = _
        rw [h21]
        exact hcnt
      · show (st2.data.regs.getXReg .X23).toBitVec = _
        rw [h23]
        rfl
      · show (st2.data.regs.getXReg .X22).toBitVec = _
        rw [h22]
        rfl
      · show (⟨st2.data.regs.getXReg .X20, st2.data.regs.getXReg .X19⟩ : EW) = _
        rw [UInt64.toBitVec_inj.mp (h20.trans rfl), UInt64.toBitVec_inj.mp (h19.trans rfl)]
        rfl
    refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Dot.b2Offset) ∧ ∃ i, cnt m0 - i = n ∧
      Inv m0 i st.data) (fun n st ⟨hpc, i, hn, hI⟩ ↦ ?_) ⟨hpc2, 0, rfl, hI⟩
    refine Eventually.mono (step hp hmul hpre hpc hI) fun st' h ↦ ?_
    rcases h with h | ⟨hpc', hI'⟩
    · exact Or.inl h
    · exact Or.inr ⟨cnt m0 - (i + 1), by have := hI'.lt; omega, hpc', i + 1, rfl, hI'⟩

end

end NativeRustcVmArm.Arrays.Dot
