module

public import NativeRustcVmArm.Layout.Ladder.Mid

/-!
# `ladder`'s window and level count (`b0` to `b8`)

Outside the window `b0` branches to `b11`, which stores the `None` tag (`outside`). Inside, one
environment (`envA`: region 0 the result, region 1 the row `r - 1` of `QUERY_LEVELS`): `b1`, `b3`,
`b5` compare `μ` with `20`, `24`, `28`, `b2`, `b4`, `b6`, `b7` set the count and the words of the
levels past the third, and `b8` checks the count against `QUERY_LEVELS`, up to `b9` (`head`, `R9`).
-/

namespace NativeRustcVmArm.Layout.Ladder

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Ladder
open LeanVM.Parameters NativeRustcVm.Layout
open NativeRustcVm (WordAt WordsAt addr_add_add addr_add_zero)

@[expose] public section

/-- The row `r - 1` of `QUERY_LEVELS`. -/
def lvBase [Labels] (m : MachineData) : BitVec 64 :=
  rodataAddr .queryLevels + BitVec.ofNat 64 (120 * (m.regs.X2.toNat - 1))

/-- The environment from the entry, inside the window. -/
def envA [Labels] (m : MachineData) : Env :=
  Env.ofMachine m [(m.regs.X0.toBitVec, 160), (lvBase m, 120)]

end

public section

/-- `x - c` below `n`, unsigned. -/
theorem sub_ult (x : BitVec 64) (c n : Nat) (hc : c < 2 ^ 32) (hn : n < 2 ^ 32) :
    (BinOp.apply .sub .W64 x (BitVec.ofNat 64 c)).ult (BitVec.ofNat 64 n) =
      decide (c ≤ x.toNat ∧ x.toNat < c + n) := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.ult]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, BitVec.toNat_sub,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := x.isLt
  omega

/-- The window's check, as `b0` computes it. -/
theorem window_eval [Labels] {env : Env} {m : MachineData} (h1 : env.regs .X1 = m.regs.X1.toBitVec)
    (h2 : env.regs .X2 = m.regs.X2.toBitVec) :
    (SBool.ite (.cmp .ult .W64 (.bin .sub .W64 (.reg .X2) (.lit 1)) (.lit 4))
      (.not (.cmp .ult .W64 (.bin .sub .W64 (.reg .X1) (.lit 16)) (.lit 15))) (.lit true)).eval env =
      !decide (Whir.Admissible m.regs.X1.toNat m.regs.X2.toNat) := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, h1, h2, Sym.low_W64]
  rw [sub_ult _ _ _ (by decide) (by decide), sub_ult _ _ _ (by decide) (by decide)]
  have e1 : m.regs.X1.toBitVec.toNat = m.regs.X1.toNat := rfl
  have e2 : m.regs.X2.toBitVec.toNat = m.regs.X2.toNat := rfl
  rw [e1, e2]
  by_cases hadm : Whir.Admissible m.regs.X1.toNat m.regs.X2.toNat
  · have hb := admissible_iff.mp hadm
    rw [decide_eq_true hadm, decide_eq_true (show 1 ≤ m.regs.X2.toNat ∧ m.regs.X2.toNat < 1 + 4 by
      omega), decide_eq_true (show 16 ≤ m.regs.X1.toNat ∧ m.regs.X1.toNat < 16 + 15 by omega)]
    rfl
  · rw [decide_eq_false hadm]
    rw [admissible_iff] at hadm
    by_cases hr : 1 ≤ m.regs.X2.toNat ∧ m.regs.X2.toNat < 1 + 4
    · rw [decide_eq_true hr, decide_eq_false (show ¬(16 ≤ m.regs.X1.toNat ∧
        m.regs.X1.toNat < 16 + 15) by omega)]
      rfl
    · rw [decide_eq_false hr]
      rfl

theorem ge_table : ∀ μ < 31, ∀ c ∈ [20, 24, 28],
    (((BinOp.apply .sub .W64 (BitVec.ofNat 64 μ) (BitVec.ofNat 64 c))).msb ==
      CmpOp.apply .subV .W64 (BitVec.ofNat 64 μ) (BitVec.ofNat 64 c)) = decide (c ≤ μ) := by
  decide +kernel

/-- `μ ≥ c`, signed, as `b1`, `b3`, `b5` compute it. -/
theorem ge_eval [Labels] {env : Env} {μ : Nat} (hμ : μ < 31)
    (h1 : env.regs .X1 = BitVec.ofNat 64 μ) {c : Nat} (hc : c ∈ [20, 24, 28]) :
    ((SBool.msb .W64 (.bin .sub .W64 (.reg .X1) (.lit c))).beq
      (.cmp .subV .W64 (.reg .X1) (.lit c))).eval env = decide (c ≤ μ) := by
  simp only [SBool.eval, Sym.eval, h1, Sym.low_W64]
  exact ge_table μ hμ c hc

/-- An index scaled by `8` (`[xn, xm, lsl #3]`). -/
theorem memExtend3_toNat (x : BitVec 64) :
    (BitVec.ofInt 64 (x.apply_mem_extend ⟨.UXTX, .E3⟩)).toNat = x.toNat * 8 % 2 ^ 64 := by
  simp only [BitVec.apply_mem_extend, BitVec.unsigned]
  rw [Int.shiftLeft_eq, BitVec.toNat_ofInt]
  push_cast
  omega

/-- `x - c` for `c ≤ x`. -/
theorem sub_lit_toNat (x : BitVec 64) (c : Nat) (h : c ≤ x.toNat) :
    (BinOp.apply .sub .W64 x (BitVec.ofNat 64 c)).toNat = x.toNat - c := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega

variable [Host] {k : Nat}

/-- **Outside the window**: `b0`, `b11`, the `None` tag. -/
theorem outside (hp : Placed code k) {m : MachineData} (hpre : LadderPre m)
    (hadm : ¬Whir.Admissible m.regs.X1.toNat m.regs.X2.toNat) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m ∧ LadderPost m st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.Ladder.b0Offset)⟩ := by
  obtain ⟨-, hO, -⟩ := hpre
  let env := Env.ofMachine m [(m.regs.X0.toBitVec, 160)]
  have hwf : env.WF := Env.wf_of ⟨⟨hO.1, hO.2⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match env outS m :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
      ⟨show _ = (Sym.ptr 0 0).eval env by rw [ptr_zero_eval]; rfl, trivial⟩ trivial trivial trivial
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_out hwf hm fun st hm1 hpc ↦ ?_
  have c0 := pc_cond hpc (window_eval (env := env) (m := m) rfl rfl)
  rw [decide_eq_false hadm] at c0
  simp only [Bool.not_false, ↓reduceIte] at c0
  rw [hp.label (j := NativeRustcVmArm.Vm.Ladder.b11Offset) NativeRustcVmArm.Vm.Ladder.label_11_at] at c0
  refine exec_at (infix_of b11_in_code (by simp [b11]) hp) (exec_after run_out run_b11) hwf c0 hm1
    fun st2 hm2 hpc2 ↦ .done _ ⟨?_, ?_, ?_, ?_⟩
  · simp only [PcOk] at hpc2
    exact hpc2.trans (retOf_of_x30 hm2 rfl rfl)
  · rw [ladder_none hadm]
    have w := Layout.Match.wordAt_write hm2 (r := 0) (o := 0) (v := .lit 0) rfl (by decide)
      (by decide)
    rw [addr_add_zero] at w
    exact w
  · have hs := Layout.Match.sameOutside_regions hm2 hwf (by decide)
    intro p hp'
    refine hs p fun ⟨e, he, h⟩ ↦ hp' ?_
    obtain rfl := List.mem_singleton.mp he
    exact .inl h
  · exact Match.saved hm hm2 hwf rfl (by decide)

/-- **At `b9`**: the registers, from a run of `b0` to `b8` that wrote nothing and kept the frame. -/
theorem r9_of {m st : MachineData} (hwf : (envA m).WF) (hm0 : Match (envA m) entryS m)
    (hadm : Whir.Admissible m.regs.X1.toNat m.regs.X2.toNat) {S : SState}
    (hm : Match (envA m) S st) (hkeep : keeps entryS S = true) (hmem : S.mem = [])
    (h0 : S.reg .X0 = some (.ptr 0 0)) (h2 : S.reg .X2 = some (.reg .X2))
    (h30 : S.reg .X30 = some (.reg .X30)) (h13 : S.reg .X13 = some (.lit (nOf m.regs.X1.toNat)))
    (h15 : S.reg .X15 = some mu16) (h16 : S.reg .X16 = some rm1)
    (h3 : 3 < nOf m.regs.X1.toNat → S.reg .X12 = some (.lit 4) ∧
      S.reg .X8 = some (.bin .add .W64 (.reg .X2) (.lit 9)))
    (h4 : 4 < nOf m.regs.X1.toNat → S.reg .X14 = some (.lit 4) ∧
      S.reg .X9 = some (.bin .add .W64 (.reg .X2) (.lit 12)))
    (h5 : 5 < nOf m.regs.X1.toNat → S.reg .X11 = some (.lit 4) ∧
      S.reg .X10 = some (.bin .add .W64 (.reg .X2) (.lit 15))) :
    R9 m st := by
  have hb := admissible_iff.mp hadm
  have hn := nOf_le m.regs.X1.toNat
  have hreg : ∀ {r : XReg} {v : Sym}, S.reg r = some v →
      (st.regs.getXReg r).toNat = (v.eval (envA m)).toNat := fun {r v} h ↦ by
    show (st.regs.getXReg _).toBitVec.toNat = _
    rw [hm.regs _ _ h]
  have hlit : ∀ {r : XReg} {c : Nat}, S.reg r = some (.lit c) → c < 2 ^ 64 →
      (st.regs.getXReg r).toNat = c := fun {r c} h hc ↦ by
    rw [hreg h]; exact NativeRustcVm.toNat_ofNat_of_lt hc
  have hadd : ∀ {r : XReg} {c : Nat}, S.reg r = some (.bin .add .W64 (.reg .X2) (.lit c)) →
      c ≤ 15 → (st.regs.getXReg r).toNat = m.regs.X2.toNat + c := fun {r c} h hc ↦ by
    rw [hreg h]
    exact add_lit_toNat m.regs.X2.toBitVec c (by
      show m.regs.X2.toNat + c < 2 ^ 64; omega)
  refine ⟨(hm.dmem_eq hwf hmem), Match.saved hm0 hm hwf rfl hkeep, ?_, ?_, ?_,
    hlit h13 (by omega), ?_, ?_, fun h ↦ ⟨hlit (h3 h).1 (by decide), hadd (h3 h).2 (by decide)⟩,
    fun h ↦ ⟨hlit (h4 h).1 (by decide), hadd (h4 h).2 (by decide)⟩,
    fun h ↦ ⟨hlit (h5 h).1 (by decide), hadd (h5 h).2 (by decide)⟩⟩
  · apply UInt64.toBitVec_inj.mp
    rw [show st.regs.X0 = st.regs.getXReg .X0 from rfl, hm.regs _ _ h0, ptr_zero_eval]
    rfl
  · exact UInt64.toBitVec_inj.mp (hm.regs _ _ h30)
  · exact UInt64.toBitVec_inj.mp (hm.regs _ _ h2)
  · rw [show st.regs.X15 = st.regs.getXReg .X15 from rfl, hreg h15]
    exact sub_lit_toNat m.regs.X1.toBitVec 16 hb.1
  · rw [show st.regs.X16 = st.regs.getXReg .X16 from rfl, hreg h16]
    exact sub_lit_toNat m.regs.X2.toBitVec 1 hb.2.2.1

/-- The row of `QUERY_LEVELS` the executor's alias names. -/
theorem lvRow_eval {m : MachineData} (hr : 1 ≤ m.regs.X2.toNat) :
    lvRow.eval (envA m) = (envA m).base 1 + BitVec.ofInt 64 0 := by
  rw [Layout.ofInt_zero]
  show BinOp.apply .add .W64 (BinOp.apply .mul .W64 (BinOp.apply .sub .W64 m.regs.X2.toBitVec
    (BitVec.ofNat 64 1)) (BitVec.ofNat 64 120)) (rodataAddr .queryLevels) = lvBase m + 0#64
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, lvBase]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_ofNat, MemWidth.bits]
  rw [show m.regs.X2.toBitVec.toNat = m.regs.X2.toNat from rfl]
  have := m.regs.X2.toNat_lt
  rw [show (2 ^ 64 - 1 % 2 ^ 64 + m.regs.X2.toNat) % 2 ^ 64 = m.regs.X2.toNat - 1 by omega]
  omega

/-- `b8`'s check passes: `QUERY_LEVELS`' entry is the count. -/
theorem count_eval {m : MachineData} (hR : RodataAt m 0)
    (hadm : Whir.Admissible m.regs.X1.toNat m.regs.X2.toNat) :
    (SBool.not (.cmp .eq .W64 (.loadx 1 0 (.un (.memExtend ⟨.UXTX, .E3⟩) .W64 mu16) 8)
      (.lit (nOf m.regs.X1.toNat)))).eval (envA m) = false := by
  have hb := admissible_iff.mp hadm
  have hw := levels_word (hR.bytesAt .queryLevels) hadm
  have hidx : ((UnOp.memExtend ⟨.UXTX, .E3⟩).apply .W64 (mu16.eval (envA m))).toNat =
      8 * (m.regs.X1.toNat - 16) := by
    show (BitVec.ofInt 64 ((BinOp.apply .sub .W64 m.regs.X1.toBitVec
      (BitVec.ofNat 64 16)).apply_mem_extend ⟨.UXTX, .E3⟩)).toNat = _
    rw [memExtend3_toNat, sub_lit_toNat _ _ hb.1]
    show (m.regs.X1.toNat - 16) * 8 % 2 ^ 64 = _
    omega
  have hl : (envA m).load 1 (0 + 8 * (m.regs.X1.toNat - 16)) 8 =
      (nOf m.regs.X1.toNat).toUInt64.toBitVec := by
    rw [Nat.zero_add]; exact load_word hw
  have hn := nOf_le m.regs.X1.toNat
  simp only [SBool.eval, Sym.eval, CmpOp.apply, Sym.low_W64]
  rw [hidx, hl, show (nOf m.regs.X1.toNat).toUInt64.toBitVec = BitVec.ofNat 64 (nOf m.regs.X1.toNat)
    from rfl]
  simp

/-- **`b0` to `b8`**: inside the window, from the entry to `b9`. -/
theorem head (hp : Placed code k) {m : MachineData} (hpre : LadderPre m)
    (hadm : Whir.Admissible m.regs.X1.toNat m.regs.X2.toNat) {R : MachineState → Prop}
    (cont : ∀ st, st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Ladder.b9Offset) → R9 m st.data → Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.Ladder.b0Offset)⟩ := by
  obtain ⟨hR, hO, hA⟩ := hpre
  have hb := admissible_iff.mp hadm
  set μ := m.regs.X1.toNat with hμ
  have hL := hR.bytesAt .queryLevels
  have hLn := hR.noWrap .queryLevels
  rw [length_levels_bytes] at hLn
  have hLm := hL.mapped
  rw [length_levels_bytes] at hLm
  have hsub : 120 * (m.regs.X2.toNat - 1) + 120 ≤ 480 := by omega
  have hlv : (lvBase m).toNat = (rodataAddr .queryLevels).toNat + 120 * (m.regs.X2.toNat - 1) :=
    NativeRustcVm.toNat_add_ofNat (by unfold NativeRustcVm.NoWrap at hLn; omega)
  have hap : NativeRustcVm.Apart m.regs.X0.toBitVec 160 (lvBase m) 120 := by
    have h := hA .queryLevels
    rw [length_levels_bytes] at h
    exact NativeRustcVm.Apart.mono_right h (by omega) (by omega)
  have hwf : (envA m).WF := Env.wf_of
    ⟨⟨hO.1, hO.2⟩, ⟨NativeRustcVm.Mapped.sub hLm hsub, NativeRustcVm.NoWrap.sub hLn hsub⟩, trivial⟩
    (List.Pairwise.cons (fun e he ↦ by obtain rfl := List.mem_singleton.mp he; exact hap)
      (List.pairwise_singleton _ _))
  have hm : Match (envA m) entryS m :=
    match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl
      ⟨show _ = (Sym.ptr 0 0).eval (envA m) by rw [ptr_zero_eval]; rfl, trivial⟩ trivial
      ⟨show (BinOp.apply .sub .W64 m.regs.X1.toBitVec (BitVec.ofNat 64 16)).toNat < 15 by
        rw [sub_lit_toNat _ _ hb.1]; show m.regs.X1.toNat - 16 < 15; omega, trivial⟩
      ⟨lvRow_eval hb.2.2.1, trivial⟩
  have hx1 : (envA m).regs .X1 = BitVec.ofNat 64 μ := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt m.regs.X1.toNat_lt]; rfl
  have hc8 := count_eval hR hadm
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf hm fun s0 hm0 hpc0 ↦ ?_
  have c0 := pc_cond hpc0 (window_eval (env := envA m) (m := m) rfl rfl)
  rw [decide_eq_true hadm] at c0
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at c0
  rw [NativeRustcVmArm.Vm.Ladder.b0_length, NativeRustcVmArm.Vm.Ladder.b0Length] at c0
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) (exec_after run_b0 run_b1) hwf c0 hm0
    fun s1 hm1 hpc1 ↦ ?_
  have c1 := pc_cond hpc1 (ge_eval (by omega) hx1 (c := 20) (by simp))
  by_cases g20 : 20 ≤ μ
  · simp only [g20, decide_true, ↓reduceIte] at c1
    rw [hp.label (j := NativeRustcVmArm.Vm.Ladder.b3Offset) NativeRustcVmArm.Vm.Ladder.label_3_at] at c1
    refine exec_at (infix_of b3_in_code (by simp [b3]) hp) (exec_after run_b1 run_b3) hwf c1 hm1
      fun s3 hm3 hpc3 ↦ ?_
    have c3 := pc_cond hpc3 (ge_eval (by omega) hx1 (c := 24) (by simp))
    by_cases g24 : 24 ≤ μ
    · simp only [g24, decide_true, ↓reduceIte] at c3
      rw [hp.label (j := NativeRustcVmArm.Vm.Ladder.b5Offset) NativeRustcVmArm.Vm.Ladder.label_5_at] at c3
      refine exec_at (infix_of b5_in_code (by simp [b5]) hp) (exec_after run_b3 run_b5) hwf c3 hm3
        fun s5 hm5 hpc5 ↦ ?_
      have c5 := pc_cond hpc5 (ge_eval (by omega) hx1 (c := 28) (by simp))
      by_cases g28 : 28 ≤ μ
      · have hn : nOf μ = 6 := by unfold nOf; split_ifs <;> omega
        rw [hμ] at hn
        simp only [g28, decide_true, ↓reduceIte] at c5
        rw [hp.label (j := NativeRustcVmArm.Vm.Ladder.b7Offset) NativeRustcVmArm.Vm.Ladder.label_7_at] at c5
        refine exec_at (infix_of b7_in_code (by simp [b7]) hp) (exec_after run_b5 run_b7) hwf c5
          hm5 fun s7 hm7 hpc7 ↦ ?_
        simp only [PcOk] at hpc7
        rw [NativeRustcVmArm.Vm.Ladder.b7_length, NativeRustcVmArm.Vm.Ladder.b7Length] at hpc7
        refine exec_at (infix_of b8_in_code (by simp [b8]) hp) (exec_after run_b7 run_b8d) hwf hpc7
          hm7 fun s8 hm8 hpc8 ↦ ?_
        have c8 := pc_cond hpc8 (hn ▸ hc8)
        simp only [Bool.false_eq_true, ↓reduceIte] at c8
        rw [NativeRustcVmArm.Vm.Ladder.b8_length, NativeRustcVmArm.Vm.Ladder.b8Length] at c8
        exact cont s8 c8 (r9_of hwf hm hadm hm8 (by decide) rfl rfl rfl rfl (by rw [hn]; rfl) rfl rfl
          (fun _ ↦ ⟨rfl, rfl⟩) (fun _ ↦ ⟨rfl, rfl⟩) (fun _ ↦ ⟨rfl, rfl⟩))
      · have hn : nOf μ = 5 := by unfold nOf; split_ifs <;> omega
        rw [hμ] at hn
        simp only [g28, decide_false, Bool.false_eq_true, ↓reduceIte] at c5
        rw [NativeRustcVmArm.Vm.Ladder.b5_length, NativeRustcVmArm.Vm.Ladder.b5Length] at c5
        refine exec_at (infix_of b6_in_code (by simp [b6]) hp) (exec_after run_b5 run_b6) hwf c5
          hm5 fun s6 hm6 hpc6 ↦ ?_
        simp only [PcOk] at hpc6
        rw [hp.label (j := NativeRustcVmArm.Vm.Ladder.b8Offset) NativeRustcVmArm.Vm.Ladder.label_8_at] at hpc6
        refine exec_at (infix_of b8_in_code (by simp [b8]) hp) (exec_after run_b6 run_b8c) hwf hpc6
          hm6 fun s8 hm8 hpc8 ↦ ?_
        have c8 := pc_cond hpc8 (hn ▸ hc8)
        simp only [Bool.false_eq_true, ↓reduceIte] at c8
        rw [NativeRustcVmArm.Vm.Ladder.b8_length, NativeRustcVmArm.Vm.Ladder.b8Length] at c8
        exact cont s8 c8 (r9_of hwf hm hadm hm8 (by decide) rfl rfl rfl rfl (by rw [hn]; rfl) rfl rfl
          (fun _ ↦ ⟨rfl, rfl⟩) (fun _ ↦ ⟨rfl, rfl⟩) (fun h ↦ absurd h (by omega)))
    · have hn : nOf μ = 4 := by unfold nOf; split_ifs <;> omega
      rw [hμ] at hn
      simp only [g24, decide_false, Bool.false_eq_true, ↓reduceIte] at c3
      rw [NativeRustcVmArm.Vm.Ladder.b3_length, NativeRustcVmArm.Vm.Ladder.b3Length] at c3
      refine exec_at (infix_of b4_in_code (by simp [b4]) hp) (exec_after run_b3 run_b4) hwf c3 hm3
        fun s4 hm4 hpc4 ↦ ?_
      simp only [PcOk] at hpc4
      rw [hp.label (j := NativeRustcVmArm.Vm.Ladder.b8Offset) NativeRustcVmArm.Vm.Ladder.label_8_at] at hpc4
      refine exec_at (infix_of b8_in_code (by simp [b8]) hp) (exec_after run_b4 run_b8b) hwf hpc4
        hm4 fun s8 hm8 hpc8 ↦ ?_
      have c8 := pc_cond hpc8 (hn ▸ hc8)
      simp only [Bool.false_eq_true, ↓reduceIte] at c8
      rw [NativeRustcVmArm.Vm.Ladder.b8_length, NativeRustcVmArm.Vm.Ladder.b8Length] at c8
      exact cont s8 c8 (r9_of hwf hm hadm hm8 (by decide) rfl rfl rfl rfl (by rw [hn]; rfl) rfl rfl
        (fun _ ↦ ⟨rfl, rfl⟩) (fun h ↦ absurd h (by omega)) (fun h ↦ absurd h (by omega)))
  · have hn : nOf μ = 3 := by unfold nOf; split_ifs <;> omega
    rw [hμ] at hn
    simp only [g20, decide_false, Bool.false_eq_true, ↓reduceIte] at c1
    rw [NativeRustcVmArm.Vm.Ladder.b1_length, NativeRustcVmArm.Vm.Ladder.b1Length] at c1
    refine exec_at (infix_of b2_in_code (by simp [b2]) hp) (exec_after run_b1 run_b2) hwf c1 hm1
      fun s2 hm2 hpc2 ↦ ?_
    simp only [PcOk] at hpc2
    rw [hp.label (j := NativeRustcVmArm.Vm.Ladder.b8Offset) NativeRustcVmArm.Vm.Ladder.label_8_at] at hpc2
    refine exec_at (infix_of b8_in_code (by simp [b8]) hp) (exec_after run_b2 run_b8a) hwf hpc2
      hm2 fun s8 hm8 hpc8 ↦ ?_
    have c8 := pc_cond hpc8 (hn ▸ hc8)
    simp only [Bool.false_eq_true, ↓reduceIte] at c8
    rw [NativeRustcVmArm.Vm.Ladder.b8_length, NativeRustcVmArm.Vm.Ladder.b8Length] at c8
    exact cont s8 c8 (r9_of hwf hm hadm hm8 (by decide) rfl rfl rfl rfl (by rw [hn]; rfl) rfl rfl
      (fun h ↦ absurd h (by omega)) (fun h ↦ absurd h (by omega)) (fun h ↦ absurd h (by omega)))

end

end NativeRustcVmArm.Layout.Ladder
