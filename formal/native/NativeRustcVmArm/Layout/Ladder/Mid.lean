module

public import NativeRustcVmArm.Layout.Ladder.Tail

/-!
# `ladder`'s query counts (`b9` to `b17`)

At `b9` the registers hold the count, `μ - 16`, `r - 1` and the words of the levels past the third
(`R9`). From there, one environment (`envB`: region 0 the result, region 1 the row `r - 1` of
`QUERY_TABLE`): `b9` loads the first three counts of the entry `μ - 16`, `b12`, `b16`, `b17` the
others the count asks for, `b10`, `b13`, `b14` zero the rest, up to `b15` (`mid`, `R15`).
-/

namespace NativeRustcVmArm.Layout.Ladder

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Ladder
open LeanVM.Parameters NativeRustcVm.Layout
open NativeRustcVm (WordAt WordsAt addr_add_add addr_add_zero)

@[expose] public section

/-- **The registers at `b9`**, for the entry `m`. -/
structure R9 (m st : MachineData) : Prop where
  dmem : st.dmem = m.dmem
  saved : Saved m st
  x0 : st.regs.X0 = m.regs.X0
  x30 : st.regs.X30 = m.regs.X30
  x2 : st.regs.X2 = m.regs.X2
  x13 : st.regs.X13.toNat = nOf m.regs.X1.toNat
  x15 : st.regs.X15.toNat = m.regs.X1.toNat - 16
  x16 : st.regs.X16.toNat = m.regs.X2.toNat - 1
  l3 : 3 < nOf m.regs.X1.toNat → st.regs.X12.toNat = 4 ∧ st.regs.X8.toNat = m.regs.X2.toNat + 9
  l4 : 4 < nOf m.regs.X1.toNat → st.regs.X14.toNat = 4 ∧ st.regs.X9.toNat = m.regs.X2.toNat + 12
  l5 : 5 < nOf m.regs.X1.toNat → st.regs.X11.toNat = 4 ∧ st.regs.X10.toNat = m.regs.X2.toNat + 15

/-- The row `r - 1` of `QUERY_TABLE`. -/
def qtBase [Labels] (m : MachineData) : BitVec 64 :=
  rodataAddr .queryTable + BitVec.ofNat 64 (720 * (m.regs.X2.toNat - 1))

/-- The environment from `b9`. -/
def envB [Labels] (m st : MachineData) : Env :=
  Env.ofMachine st [(m.regs.X0.toBitVec, 160), (qtBase m, 720)]

end

public section

/-- A branch's target, its condition known. -/
theorem pc_cond [Labels] {env : Env} {c : SBool} {l : Label} {next : Int64} {st : MachineState}
    {b : Bool} (h : PcOk env (.cond c l) next st) (hc : c.eval env = b) :
    st.pc = if b then Labels.label l else next := by
  rw [← hc]; exact h

/-- `X13 - 1 = c`, for the count in X13. -/
theorem x13_eval [Labels] {env : Env} {n : Nat} (hx : (env.regs .X13).toNat = n) (hn : 1 ≤ n)
    (hn' : n < 2 ^ 63) (c : Nat) (hc : c < 2 ^ 63) :
    (SBool.cmp .eq .W64 (.bin .sub .W64 (.reg .X13) (.lit 1)) (.lit c)).eval env =
      decide (n = c + 1) := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, Sym.low_W64, Sym.ext_W64]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_sub, hx, BitVec.toNat_ofNat, MemWidth.bits] at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, hx, BitVec.toNat_ofNat, MemWidth.bits]
    omega

theorem x13_not_eval [Labels] {env : Env} {n : Nat} (hx : (env.regs .X13).toNat = n) (hn : 1 ≤ n)
    (hn' : n < 2 ^ 63) (c : Nat) (hc : c < 2 ^ 63) :
    (SBool.not (.cmp .eq .W64 (.bin .sub .W64 (.reg .X13) (.lit 1)) (.lit c))).eval env =
      !decide (n = c + 1) := by
  rw [SBool.eval, x13_eval hx hn hn' c hc]

/-- `x + c` for small numbers. -/
theorem add_lit_toNat (x : BitVec 64) (c : Nat) (h : x.toNat + c < 2 ^ 64) :
    (BinOp.apply .add .W64 x (BitVec.ofNat 64 c)).toNat = x.toNat + c := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The row of `QUERY_TABLE` the executor's alias names. -/
theorem qtRow_eval [Labels] {m st : MachineData} (hx : st.regs.X16.toNat = m.regs.X2.toNat - 1) :
    qtRow.eval (envB m st) = (envB m st).base 1 + BitVec.ofInt 64 0 := by
  rw [Layout.ofInt_zero]
  show BinOp.apply .add .W64 (BinOp.apply .mul .W64 st.regs.X16.toBitVec (BitVec.ofNat 64 720))
    (rodataAddr .queryTable) = qtBase m + 0#64
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, qtBase]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, MemWidth.bits]
  rw [show st.regs.X16.toBitVec.toNat = st.regs.X16.toNat from rfl, hx]
  omega

variable [Host] {k : Nat}

/-- The query count `i` in a register a slot load of `b9` to `b17` filled. -/
theorem slot_count {m st : MachineData} (hR : RodataAt m 0)
    (hadm : Whir.Admissible m.regs.X1.toNat m.regs.X2.toNat) (h9 : R9 m st)
    {S : SState} {st' : MachineData} (hm : Match (envB m st) S st') {x : XReg} {i : Nat} (hi : i < 6)
    (hx : S.reg x = some (slotLoad [] 1 (8 * i) 48 8 (.reg .X15) 0 14)) :
    (st'.regs.getXReg x).toNat = qAt m.regs.X1.toNat m.regs.X2.toNat i := by
  have hb := admissible_iff.mp hadm
  have h15 : (Sym.reg .X15).eval (envB m st) = BitVec.ofNat 64 (m.regs.X1.toNat - 16) := by
    apply BitVec.eq_of_toNat_eq
    show st.regs.X15.toNat = _
    rw [h9.x15, BitVec.toNat_ofNat]; omega
  have := (hm.regs x _ hx).trans (eval_slotLoad h15 (by omega) 14 0 (by omega) (by omega))
  have hw := table_word (hR.bytesAt .queryTable) hadm hi
  rw [← h9.dmem] at hw
  have hl : (envB m st).load 1 (8 * i + 48 * (m.regs.X1.toNat - 16)) 8 =
      (qAt m.regs.X1.toNat m.regs.X2.toNat i).toUInt64.toBitVec :=
    load_word hw
  rw [show (loadSym [] 1 (8 * i + 48 * (m.regs.X1.toNat - 16)) 8).eval (envB m st) =
    (envB m st).load 1 (8 * i + 48 * (m.regs.X1.toNat - 16)) 8 from rfl, hl] at this
  show (st'.regs.getXReg x).toBitVec.toNat = _
  rw [this]
  have := qAt_le m.regs.X1.toNat m.regs.X2.toNat i
  show (BitVec.ofNat 64 (qAt m.regs.X1.toNat m.regs.X2.toNat i)).toNat = _
  rw [BitVec.toNat_ofNat]
  omega

/-- **At `b15`**: the registers, from a run of `b9` to `b17` that wrote nothing, kept the frame and
left these registers. -/
theorem r15_of {m st : MachineData} (hR : RodataAt m 0)
    (hadm : Whir.Admissible m.regs.X1.toNat m.regs.X2.toNat) (h9 : R9 m st)
    (hwf : (envB m st).WF) (hm9 : Match (envB m st) midS st) {S : SState} {st' : MachineData}
    (hm : Match (envB m st) S st') (hkeep : keeps midS S = true) (hmem : S.mem = [])
    (h0 : S.reg .X0 = some (.ptr 0 0)) (h1 : S.reg .X1 = some (.bin .add .W64 (.reg .X2) (.lit 3)))
    (h17 : S.reg .X17 = some (.bin .add .W64 (.reg .X2) (.lit 6)))
    (h18 : S.reg .X18 = some (slotLoad [] 1 (8 * 0) 48 8 (.reg .X15) 0 14))
    (h16 : S.reg .X16 = some (slotLoad [] 1 (8 * 1) 48 8 (.reg .X15) 0 14))
    (h15 : S.reg .X15 = some (slotLoad [] 1 (8 * 2) 48 8 (.reg .X15) 0 14))
    (h3 : 3 < nOf m.regs.X1.toNat → S.reg .X3 = some (slotLoad [] 1 (8 * 3) 48 8 (.reg .X15) 0 14))
    (h4 : 4 < nOf m.regs.X1.toNat → S.reg .X4 = some (slotLoad [] 1 (8 * 4) 48 8 (.reg .X15) 0 14))
    (h5 : 5 < nOf m.regs.X1.toNat → S.reg .X5 = some (slotLoad [] 1 (8 * 5) 48 8 (.reg .X15) 0 14))
    (hkept : ∀ r ∈ [XReg.X2, .X8, .X9, .X10, .X11, .X12, .X13, .X14, .X30],
      S.reg r = some (.reg r)) :
    R15 m st' := by
  have hb := admissible_iff.mp hadm
  have hs : ∀ r ∈ [XReg.X2, .X8, .X9, .X10, .X11, .X12, .X13, .X14, .X30],
      st'.regs.getXReg r = st.regs.getXReg r :=
    fun r hr ↦ UInt64.toBitVec_inj.mp (hm.regs r _ (hkept r hr))
  have hx2 : st.regs.X2.toBitVec.toNat = m.regs.X2.toNat := congrArg UInt64.toNat h9.x2
  have hadd : ∀ {x : XReg} {c : Nat}, S.reg x = some (.bin .add .W64 (.reg .X2) (.lit c)) →
      c ≤ 6 → (st'.regs.getXReg x).toNat = m.regs.X2.toNat + c := fun hx hc ↦ by
    show (st'.regs.getXReg _).toBitVec.toNat = _
    rw [hm.regs _ _ hx]
    show (BinOp.apply .add .W64 st.regs.X2.toBitVec (BitVec.ofNat 64 _)).toNat = _
    rw [add_lit_toNat _ _ (by omega), hx2]
  have h12 := hs .X12 (by simp)
  have h8 := hs .X8 (by simp)
  have h14 := hs .X14 (by simp)
  have h9' := hs .X9 (by simp)
  have h11 := hs .X11 (by simp)
  have h10 := hs .X10 (by simp)
  refine ⟨(hm.dmem_eq hwf hmem).trans h9.dmem, h9.saved.trans (Match.saved hm9 hm hwf rfl hkeep),
    ?_, (hs .X30 (by simp)).trans h9.x30, (hs .X2 (by simp)).trans h9.x2,
    by rw [show st'.regs.X13 = st'.regs.getXReg .X13 from rfl, hs .X13 (by simp)]; exact h9.x13,
    hadd h1 (by decide), hadd h17 (by decide), slot_count hR hadm h9 hm (by decide) h18,
    slot_count hR hadm h9 hm (by decide) h16, slot_count hR hadm h9 hm (by decide) h15,
    fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · apply UInt64.toBitVec_inj.mp
    rw [show st'.regs.X0 = st'.regs.getXReg .X0 from rfl, hm.regs _ _ h0, ptr_zero_eval]
    rfl
  · obtain ⟨a, b⟩ := h9.l3 h
    exact ⟨by rw [show st'.regs.X12 = st'.regs.getXReg .X12 from rfl, h12]; exact a,
      by rw [show st'.regs.X8 = st'.regs.getXReg .X8 from rfl, h8]; exact b,
      slot_count hR hadm h9 hm (by decide) (h3 h)⟩
  · obtain ⟨a, b⟩ := h9.l4 h
    exact ⟨by rw [show st'.regs.X14 = st'.regs.getXReg .X14 from rfl, h14]; exact a,
      by rw [show st'.regs.X9 = st'.regs.getXReg .X9 from rfl, h9']; exact b,
      slot_count hR hadm h9 hm (by decide) (h4 h)⟩
  · obtain ⟨a, b⟩ := h9.l5 h
    exact ⟨by rw [show st'.regs.X11 = st'.regs.getXReg .X11 from rfl, h11]; exact a,
      by rw [show st'.regs.X10 = st'.regs.getXReg .X10 from rfl, h10]; exact b,
      slot_count hR hadm h9 hm (by decide) (h5 h)⟩

/-- **`b9` to `b17`**: from `b9` to `b15`, the query counts loaded. -/
theorem mid (hp : Placed code k) {m : MachineData} (hR : RodataAt m 0)
    (hO : Readable m m.regs.X0.toBitVec ladderBytes) (hA : RodataApart m.regs.X0.toBitVec ladderBytes)
    (hadm : Whir.Admissible m.regs.X1.toNat m.regs.X2.toNat) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Ladder.b9Offset)) (h9 : R9 m st.data) {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Ladder.b15Offset) → R15 m st'.data → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hb := admissible_iff.mp hadm
  have hn := nOf_le m.regs.X1.toNat
  set o := m.regs.X0.toBitVec with ho
  have hT := hR.bytesAt .queryTable
  have hTn := hR.noWrap .queryTable
  rw [length_table_bytes] at hTn
  have hTm := hT.mapped
  rw [length_table_bytes] at hTm
  have hsub : 720 * (m.regs.X2.toNat - 1) + 720 ≤ 2880 := by omega
  have hqt : (qtBase m).toNat = (rodataAddr .queryTable).toNat + 720 * (m.regs.X2.toNat - 1) :=
    NativeRustcVm.toNat_add_ofNat (by unfold NativeRustcVm.NoWrap at hTn; omega)
  have hap : NativeRustcVm.Apart o 160 (qtBase m) 720 := by
    have h := hA .queryTable
    rw [length_table_bytes] at h
    exact NativeRustcVm.Apart.mono_right h (by omega) (by omega)
  have hwf : (envB m st.data).WF := Env.wf_of
    ⟨⟨show Mapped st.data.dmem o 160 by rw [h9.dmem]; exact hO.1, hO.2⟩,
      ⟨show Mapped st.data.dmem (qtBase m) 720 by
        rw [h9.dmem]; exact NativeRustcVm.Mapped.sub hTm hsub,
        NativeRustcVm.NoWrap.sub hTn hsub⟩, trivial⟩
    (List.Pairwise.cons (fun e he ↦ by obtain rfl := List.mem_singleton.mp he; exact hap)
      (List.pairwise_singleton _ _))
  have hm9 : Match (envB m st.data) midS st.data :=
    match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl
      ⟨show _ = (Sym.ptr 0 0).eval (envB m st.data) by
        rw [ptr_zero_eval]; exact congrArg UInt64.toBitVec h9.x0, trivial⟩ trivial
      ⟨show st.data.regs.X15.toNat < 15 by rw [h9.x15]; omega, trivial⟩
      ⟨qtRow_eval h9.x16, trivial⟩
  have hx13 : ((envB m st.data).regs .X13).toNat = nOf m.regs.X1.toNat := h9.x13
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) run_b9 hwf hpc hm9 fun s1 hm1 hpc1 ↦ ?_
  have c9 := pc_cond hpc1 (x13_not_eval hx13 (by omega) (by omega) 2 (by decide))
  by_cases n3 : nOf m.regs.X1.toNat = 3
  · simp only [n3, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at c9
    rw [NativeRustcVmArm.Vm.Ladder.b9_length, NativeRustcVmArm.Vm.Ladder.b9Length] at c9
    refine exec_at (infix_of b10_in_code (by simp [b10]) hp) (exec_after run_b9 run_b10) hwf c9 hm1
      fun s2 hm2 hpc2 ↦ ?_
    simp only [PcOk] at hpc2
    rw [hp.label (j := NativeRustcVmArm.Vm.Ladder.b13Offset) NativeRustcVmArm.Vm.Ladder.label_13_at] at hpc2
    refine exec_at (infix_of b13_in_code (by simp [b13]) hp) (exec_after run_b10 run_b13a) hwf hpc2
      hm2 fun s3 hm3 hpc3 ↦ ?_
    simp only [PcOk] at hpc3
    rw [NativeRustcVmArm.Vm.Ladder.b13_length, NativeRustcVmArm.Vm.Ladder.b13Length] at hpc3
    refine exec_at (infix_of b14_in_code (by simp [b14]) hp) (exec_after run_b13a run_b14a) hwf hpc3
      hm3 fun s4 hm4 hpc4 ↦ ?_
    simp only [PcOk] at hpc4
    rw [NativeRustcVmArm.Vm.Ladder.b14_length, NativeRustcVmArm.Vm.Ladder.b14Length] at hpc4
    exact cont s4 hpc4 (r15_of hR hadm h9 hwf hm9 hm4 (by decide) rfl rfl rfl rfl rfl rfl rfl
      (fun h ↦ absurd h (by omega)) (fun h ↦ absurd h (by omega)) (fun h ↦ absurd h (by omega))
      (by decide))
  · simp only [n3, decide_false, Bool.not_false, ↓reduceIte] at c9
    rw [hp.label (j := NativeRustcVmArm.Vm.Ladder.b12Offset) NativeRustcVmArm.Vm.Ladder.label_12_at] at c9
    refine exec_at (infix_of b12_in_code (by simp [b12]) hp) (exec_after run_b9 run_b12) hwf c9 hm1
      fun s2 hm2 hpc2 ↦ ?_
    have c12 := pc_cond hpc2 (x13_not_eval hx13 (by omega) (by omega) 3 (by decide))
    by_cases n4 : nOf m.regs.X1.toNat = 4
    · simp only [n4, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at c12
      rw [NativeRustcVmArm.Vm.Ladder.b12_length, NativeRustcVmArm.Vm.Ladder.b12Length] at c12
      refine exec_at (infix_of b13_in_code (by simp [b13]) hp) (exec_after run_b12 run_b13b) hwf
        c12 hm2 fun s3 hm3 hpc3 ↦ ?_
      simp only [PcOk] at hpc3
      rw [NativeRustcVmArm.Vm.Ladder.b13_length, NativeRustcVmArm.Vm.Ladder.b13Length] at hpc3
      refine exec_at (infix_of b14_in_code (by simp [b14]) hp) (exec_after run_b13b run_b14b) hwf
        hpc3 hm3 fun s4 hm4 hpc4 ↦ ?_
      simp only [PcOk] at hpc4
      rw [NativeRustcVmArm.Vm.Ladder.b14_length, NativeRustcVmArm.Vm.Ladder.b14Length] at hpc4
      exact cont s4 hpc4 (r15_of hR hadm h9 hwf hm9 hm4 (by decide) rfl rfl rfl rfl rfl rfl rfl
        (fun _ ↦ rfl) (fun h ↦ absurd h (by omega)) (fun h ↦ absurd h (by omega)) (by decide))
    · simp only [show (nOf m.regs.X1.toNat = 3 + 1) = False from propext ⟨fun h ↦ n4 h, False.elim⟩,
        decide_false, Bool.not_false, ↓reduceIte] at c12
      rw [hp.label (j := NativeRustcVmArm.Vm.Ladder.b16Offset) NativeRustcVmArm.Vm.Ladder.label_16_at] at c12
      refine exec_at (infix_of b16_in_code (by simp [b16]) hp) (exec_after run_b12 run_b16) hwf
        c12 hm2 fun s3 hm3 hpc3 ↦ ?_
      have c16 := pc_cond hpc3 (x13_eval hx13 (by omega) (by omega) 4 (by decide))
      by_cases n5 : nOf m.regs.X1.toNat = 5
      · simp only [n5, decide_true, ↓reduceIte] at c16
        rw [hp.label (j := NativeRustcVmArm.Vm.Ladder.b14Offset) NativeRustcVmArm.Vm.Ladder.label_14_at] at c16
        refine exec_at (infix_of b14_in_code (by simp [b14]) hp) (exec_after run_b16 run_b14c) hwf
          c16 hm3 fun s4 hm4 hpc4 ↦ ?_
        simp only [PcOk] at hpc4
        rw [NativeRustcVmArm.Vm.Ladder.b14_length, NativeRustcVmArm.Vm.Ladder.b14Length] at hpc4
        exact cont s4 hpc4 (r15_of hR hadm h9 hwf hm9 hm4 (by decide) rfl rfl rfl rfl rfl rfl rfl
          (fun _ ↦ rfl) (fun _ ↦ rfl) (fun h ↦ absurd h (by omega)) (by decide))
      · simp only [show (nOf m.regs.X1.toNat = 4 + 1) = False from propext ⟨fun h ↦ n5 h, False.elim⟩,
          decide_false, Bool.false_eq_true, ↓reduceIte] at c16
        rw [NativeRustcVmArm.Vm.Ladder.b16_length, NativeRustcVmArm.Vm.Ladder.b16Length] at c16
        refine exec_at (infix_of b17_in_code (by simp [b17]) hp) (exec_after run_b16 run_b17) hwf
          c16 hm3 fun s4 hm4 hpc4 ↦ ?_
        simp only [PcOk] at hpc4
        rw [hp.label (j := NativeRustcVmArm.Vm.Ladder.b15Offset) NativeRustcVmArm.Vm.Ladder.label_15_at] at hpc4
        exact cont s4 hpc4 (r15_of hR hadm h9 hwf hm9 hm4 (by decide) rfl rfl rfl rfl rfl rfl rfl
          (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (by decide))

end

end NativeRustcVmArm.Layout.Ladder
