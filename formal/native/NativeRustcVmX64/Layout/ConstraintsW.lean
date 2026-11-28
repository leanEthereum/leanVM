module

public import NativeRustcVmX64.Layout.ConstraintsW.Exec
public import NativeRustcVmX64.Code.Vm.ConstraintsW.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `constraints_w` on x86-64

**`constraintsW_spec`**: rustc's `constraints_w(opcode, row, out)`, placed anywhere in the
program, meets `ConstraintsWPre`/`ConstraintsWPost` given `EW::mul`'s contract. Not `JUMP`
(`b0`): it returns `0` (`b5`). `JUMP`: the prologue (`b1`) pushes RBX, R12-R15 and keeps `out`
in RBX; the row's `condition`, `inverse` and `flag` (`row[5]`, `row[12]`, `row[13]`, `0` past the
row) come to R15:R14, RDX:RCX, R13:R12 (`b2`-`b4`, `b6`-`b8`; `At9`); `b9` multiplies
`condition·inverse`, `b10` stores `flag + condition·inverse` in `out[0]` and multiplies
`condition·(flag + 1)`, which `b11` stores in `out[1]` before the epilogue returns `2`.
-/

namespace NativeRustcVmX64.Layout.ConstraintsW

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.ConstraintsW NativeVm.Model
open NativeRustcVmX64.Field (frameEnv frame_wf match_frame midS leaf_done)
open NativeRustcVmX64.Arrays (Body after after_eq exec_after freeRegs keepsAll keepsRegs restores
  ew_of_loads elem_of_apart apart_zero noWrap_zero pc_cond stackOk_mono not_inRange_zero
  ewAt_of_writes ewArg_xor ew_add_comm one_add_ewArg ewRet_eq inRange_stack ret_not_in
  bytesAt_keep)
open NativeRustcVmX64.Transcript (infix_of infix_take infix_drop known_ptr apart_frame)
open NativeRustcVm (ewsOf ewOf EWsAt EWAt)

public section

/-- The row. -/
abbrev row (m : MachineData) : Array EW := slice m (reg m .rsi) (reg m .rdx)

/-- `constraintsW` of `JUMP`. -/
theorem constraintsW_jump (r : Array EW) :
    constraintsW 4 r =
      #[r.getD 13 0 + r.getD 5 0 * r.getD 12 0, r.getD 5 0 * (r.getD 13 0 + 1)] := by
  unfold constraintsW LeanVM.Protocol.Verifier.opJump
  simp only [↓reduceIte]
  rfl

/-- `constraintsW` of another table. -/
theorem constraintsW_other {op : Nat} (h : op ≠ 4) (r : Array EW) : constraintsW op r = #[] := by
  unfold constraintsW LeanVM.Protocol.Verifier.opJump
  simp [h]

theorem row_getD {m : MachineData} {i : Nat} (h : i < (reg m .rdx).toNat) :
    (row m).getD i 0 = (ewsOf m.dmem (reg m .rsi) (reg m .rdx).toNat)[i]'(by simpa using h) := by
  simp [row, slice, Array.getD, h]

theorem row_getD_ge {m : MachineData} {i : Nat} (h : (reg m .rdx).toNat ≤ i) :
    (row m).getD i 0 = 0 := by
  simp [row, slice, Array.getD]
  omega

theorem beq_ofNat (x : BitVec 64) {n : Nat} (hn : n < 2 ^ 64) :
    (x == BitVec.ofNat 64 n) = decide (x.toNat = n) := by
  by_cases h : x.toNat = n
  · have : x = BitVec.ofNat 64 n := by
      apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    rw [decide_eq_true h, this, beq_self_eq_true]
  · have : x ≠ BitVec.ofNat 64 n := fun e ↦ h (by rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn])
    rw [decide_eq_false h]
    simpa using this

theorem ult_ofNat (x : BitVec 64) {n : Nat} (hn : n < 2 ^ 64) :
    x.ult (BitVec.ofNat 64 n) = decide (x.toNat < n) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

abbrev S : Nat := constraintsWStack

/-- **At `b9`**: the body, `out` in RBX, `condition`, `inverse`, `flag` in R15:R14, RDX:RCX,
R13:R12. -/
structure At9 (m0 : MachineData) (s : MachineData) : Prop where
  body : Body m0 48 S slots 0 0 s
  rbx : reg s .rbx = reg m0 .rcx
  cond : ewArg (reg s .r15) (reg s .r14) = (row m0).getD 5 0
  inv : ewArg (reg s .rdx) (reg s .rcx) = (row m0).getD 12 0
  flag : ewArg (reg s .r13) (reg s .r12) = (row m0).getD 13 0

variable [Host] {k : Nat}

/-- At `b9`. -/
abbrev G (k : Nat) (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ConstraintsW.b9Offset) ∧ At9 m0 s.data

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.ConstraintsW.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.ConstraintsW.b0Offset) :=
  hp.label NativeRustcVmX64.Vm.ConstraintsW.entry_at
theorem lbl_1 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.ConstraintsW.label_1 = Host.addrOf (k + NativeRustcVmX64.Vm.ConstraintsW.b5Offset) :=
  hp.label NativeRustcVmX64.Vm.ConstraintsW.label_1_at
theorem lbl_3 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.ConstraintsW.label_3 = Host.addrOf (k + NativeRustcVmX64.Vm.ConstraintsW.b6Offset) :=
  hp.label NativeRustcVmX64.Vm.ConstraintsW.label_3_at
theorem lbl_5 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.ConstraintsW.label_5 = Host.addrOf (k + NativeRustcVmX64.Vm.ConstraintsW.b7Offset) :=
  hp.label NativeRustcVmX64.Vm.ConstraintsW.label_5_at
theorem lbl_7 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.ConstraintsW.label_7 = Host.addrOf (k + NativeRustcVmX64.Vm.ConstraintsW.b8Offset) :=
  hp.label NativeRustcVmX64.Vm.ConstraintsW.label_7_at
theorem lbl_9 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.ConstraintsW.label_9 = Host.addrOf (k + NativeRustcVmX64.Vm.ConstraintsW.b9Offset) :=
  hp.label NativeRustcVmX64.Vm.ConstraintsW.label_9_at

omit [Host] in
/-- A register a block left as it was. -/
theorem keep [Labels] {env : Env} {S₀ S₁ : SState} {m m' : MachineData} (hm : Match env S₀ m)
    (hm' : Match env S₁ m') {r : Reg64} {v : Sym} (h0 : S₀.reg r = some v)
    (h1 : S₁.reg r = some v) : reg m' r = reg m r :=
  Match.reg_eq hm hm' h0 h1

omit [Host] in
/-- Element `i` of the row, read in a body. -/
theorem elem_row {m0 st : MachineData} (hpre : ConstraintsWPre m0)
    (hb : Body m0 48 S slots 0 0 st) {i : Nat} (hi : i < (reg m0 .rdx).toNat) :
    ewOf st.dmem (reg m0 .rsi + BitVec.ofNat 64 (16 * i)) = (row m0).getD i 0 := by
  rw [row_getD hi]
  exact elem_of_apart hb.same hpre.1 hpre.2.1.1.2 hpre.2.1.2 (apart_zero _ _) noWrap_zero hi

/-- The row's first `n` bytes as region 0, RSI its base. -/
theorem row_match {m0 : MachineData} (hpre : ConstraintsWPre m0) {st : MachineData}
    (hb : Body m0 48 S slots 0 0 st) (hsi : reg st .rsi = reg m0 .rsi) {n : Nat}
    (hn : n ≤ 16 * (reg m0 .rdx).toNat) :
    (Env.ofMachine st [(reg m0 .rsi, n)]).WF ∧
      Match (Env.ofMachine st [(reg m0 .rsi, n)]) (rowS n) st := by
  obtain ⟨hmap, hnw⟩ := hpre.2.1.1
  refine ⟨Env.wf_of ⟨⟨fun j hj ↦ hb.kept _ (hmap j (by omega)), NativeRustcVm.NoWrap.mono hnw hn⟩,
    trivial⟩ (List.pairwise_singleton _ _),
    match_ofMachine ⟨rfl, trivial⟩ ⟨known_ptr rfl hsi, trivial⟩ trivial trivial trivial⟩

/-- **`b8`**: `flag` is `0`. -/
theorem from8 (hp : Placed code k) {m0 : MachineData} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ConstraintsW.b8Offset)) (hb : Body m0 48 S slots 0 0 st.data)
    (hbx : reg st.data .rbx = reg m0 .rcx)
    (hc : ewArg (reg st.data .r15) (reg st.data .r14) = (row m0).getD 5 0)
    (hi : ewArg (reg st.data .rdx) (reg st.data .rcx) = (row m0).getD 12 0)
    (hf : (row m0).getD 13 0 = 0) : Eventually (step1 Host.exe) (G k m0) st := by
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8 (Env.wf_nil _) nofun hpc
    (match_nil _) fun st' hm hpc' ↦ .done _ ⟨?_, hb.of_block (match_nil _) hm (Env.wf_nil _) rfl
      (after_eq run_b8 ▸ b8_keeps), ?_, ?_, ?_, ?_⟩
  · simp only [PcOk, NativeRustcVmX64.Vm.ConstraintsW.b8_length] at hpc'
    exact hpc'
  · rw [← hbx]; exact keep (match_nil _) hm (r := .rbx) rfl rfl
  · rw [← hc, keep (match_nil _) hm (r := .r15) rfl rfl,
      keep (match_nil _) hm (r := .r14) rfl rfl]
  · rw [← hi, keep (match_nil _) hm (r := .rdx) rfl rfl,
      keep (match_nil _) hm (r := .rcx) rfl rfl]
  · rw [hf, show reg st'.data .r13 = 0#64 from hm.regs .r13 _ rfl,
      show reg st'.data .r12 = 0#64 from hm.regs .r12 _ rfl]
    rfl

/-- **`b7`**: `inverse` and `flag` are `0`. -/
theorem from7 (hp : Placed code k) {m0 : MachineData} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ConstraintsW.b7Offset)) (hb : Body m0 48 S slots 0 0 st.data)
    (hbx : reg st.data .rbx = reg m0 .rcx)
    (hc : ewArg (reg st.data .r15) (reg st.data .r14) = (row m0).getD 5 0)
    (hi : (row m0).getD 12 0 = 0) (hf : (row m0).getD 13 0 = 0) :
    Eventually (step1 Host.exe) (G k m0) st := by
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) run_b7 (Env.wf_nil _) nofun hpc
    (match_nil _) fun st' hm hpc' ↦ ?_
  simp only [PcOk, NativeRustcVmX64.Vm.ConstraintsW.b7_length] at hpc'
  refine from8 hp hpc' (hb.of_block (match_nil _) hm (Env.wf_nil _) rfl
    (after_eq run_b7 ▸ b7_keeps)) ?_ ?_ ?_ hf
  · rw [← hbx]; exact keep (match_nil _) hm (r := .rbx) rfl rfl
  · rw [← hc, keep (match_nil _) hm (r := .r15) rfl rfl,
      keep (match_nil _) hm (r := .r14) rfl rfl]
  · rw [hi, show reg st'.data .rdx = 0#64 from hm.regs .rdx _ rfl,
      show reg st'.data .rcx = 0#64 from hm.regs .rcx _ rfl]
    rfl

/-- **`b6`**: a row shorter than `6`, all three `0`. -/
theorem from6 (hp : Placed code k) {m0 : MachineData} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ConstraintsW.b6Offset)) (hb : Body m0 48 S slots 0 0 st.data)
    (hbx : reg st.data .rbx = reg m0 .rcx) (hc : (row m0).getD 5 0 = 0)
    (hi : (row m0).getD 12 0 = 0) (hf : (row m0).getD 13 0 = 0) :
    Eventually (step1 Host.exe) (G k m0) st := by
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 (Env.wf_nil _) nofun hpc
    (match_nil _) fun st' hm hpc' ↦ ?_
  simp only [PcOk] at hpc'
  refine from8 hp (hpc'.trans (lbl_7 hp)) (hb.of_block (match_nil _) hm (Env.wf_nil _) rfl
    (after_eq run_b6 ▸ b6_keeps)) ?_ ?_ ?_ hf
  · rw [← hbx]; exact keep (match_nil _) hm (r := .rbx) rfl rfl
  · rw [hc, show reg st'.data .r15 = 0#64 from hm.regs .r15 _ rfl,
      show reg st'.data .r14 = 0#64 from hm.regs .r14 _ rfl]
    rfl
  · rw [hi, show reg st'.data .rdx = 0#64 from hm.regs .rdx _ rfl,
      show reg st'.data .rcx = 0#64 from hm.regs .rcx _ rfl]
    rfl

/-- **The entry and the prologue**: `JUMP`, on to `b9`. -/
theorem head (hp : Placed code k) {m0 : MachineData} (hpre : ConstraintsWPre m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ConstraintsW.b1Offset))
    (hm1 : Match (frameEnv m0 m0 48) (after b0 entryS) st.data)
    (hwf : (frameEnv m0 m0 48).WF) : Eventually (step1 Host.exe) (G k m0) st := by
  have hm1' := hm1
  rw [after_eq run_b0] at hm1'
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) (exec_after run_b0 run_b1) hwf nofun hpc
    hm1' fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hw, hregs, hmem, hsp, hbx, hsi, hdx⟩ := after_eq run_b1 ▸ b1_entry
  have hb : Body m0 48 S slots 0 0 st2.data :=
    Body.of_entry hpre.1 (by decide) hm2 hsp hw hregs hmem
  have hbx2 : reg st2.data .rbx = reg m0 .rcx := hm2.regs .rbx _ hbx
  have hsi2 : reg st2.data .rsi = reg m0 .rsi := hm2.regs .rsi _ hsi
  have hdx2 : reg st2.data .rdx = reg m0 .rdx := hm2.regs .rdx _ hdx
  have hlen := Arrays.lt_of_offStack hpre.2.1.1.2 hpre.2.1.2
  simp only [PcOk, NativeRustcVmX64.Vm.ConstraintsW.b1_length] at hpc2
  obtain ⟨hy, hn⟩ := pc_cond hpc2
  by_cases h6 : (reg m0 .rdx).toNat < 6
  · refine from6 hp ((hy ?_).trans (lbl_3 hp)) hb hbx2 (row_getD_ge (by omega))
      (row_getD_ge (by omega)) (row_getD_ge (by omega))
    simp only [SBool.eval, CmpOp.apply, Sym.eval, low_W64, Env.ofMachine_regs]
    rw [ult_ofNat _ (by decide)]
    simpa using h6
  have hpc3 := hn (by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, low_W64, Env.ofMachine_regs]
    rw [ult_ofNat _ (by decide)]
    simpa using h6)
  -- the row's loads, as far as its length allows
  have hrow : ∀ {n : Nat}, n ≤ 16 * (reg m0 .rdx).toNat →
      (Env.ofMachine st2.data [(reg m0 .rsi, n)]).WF ∧
        Match (Env.ofMachine st2.data [(reg m0 .rsi, n)]) (rowS n) st2.data :=
    fun hn ↦ row_match hpre hb hsi2 hn
  have hcond : ∀ {n : Nat} {S₁ : SState} {d : MachineData}, 96 ≤ n →
      n ≤ 16 * (reg m0 .rdx).toNat →
      Match (Env.ofMachine st2.data [(reg m0 .rsi, n)]) S₁ d →
      S₁.reg .r15 = some (.load 0 80 8) → S₁.reg .r14 = some (.load 0 88 8) →
      ewArg (reg d .r15) (reg d .r14) = (row m0).getD 5 0 := by
    intro n S₁ d h96 hn hm h15 h14
    rw [ew_of_loads hm h15 h14]
    exact elem_row hpre hb (i := 5) (by omega)
  by_cases h13 : (reg m0 .rdx).toNat < 13
  · obtain ⟨hwf3, hm3⟩ := hrow (n := 96) (by omega)
    refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf3 nofun hpc3 hm3
      fun st3 hm3' hpc3' ↦ ?_
    obtain ⟨hk, h15, h14, hbx3⟩ := after_eq run_b2 ▸ b2_keeps
    simp only [PcOk] at hpc3'
    obtain ⟨hy3, -⟩ := pc_cond hpc3'
    refine from7 hp ((hy3 ?_).trans (lbl_5 hp)) (hb.of_block hm3 hm3' hwf3 rfl hk)
      ((hm3'.regs .rbx _ hbx3).trans hbx2) (hcond le_rfl (by omega) hm3' h15 h14)
      (row_getD_ge (by omega)) (row_getD_ge (by omega))
    simp only [SBool.eval, CmpOp.apply, Sym.eval, low_W64, Env.ofMachine_regs]
    rw [show st2.data.regs.get64 .rdx = reg m0 .rdx from hdx2, ult_ofNat _ (by decide)]
    simpa using h13
  by_cases h13' : (reg m0 .rdx).toNat = 13
  · obtain ⟨hwf3, hm3⟩ := hrow (n := 208) (by omega)
    refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2' hwf3 nofun hpc3 hm3
      fun st3 hm3' hpc3' ↦ ?_
    simp only [PcOk] at hpc3'
    obtain ⟨-, hn3⟩ := pc_cond hpc3'
    have hpc4 := hn3 (by
      simp only [SBool.eval, CmpOp.apply, Sym.eval, low_W64, Env.ofMachine_regs]
      rw [show st2.data.regs.get64 .rdx = reg m0 .rdx from hdx2, ult_ofNat _ (by decide)]
      simpa using h13)
    refine exec_at (infix_of b3_in_code (by simp [b3]) hp) (exec_after run_b2' run_b3) hwf3 nofun
      (hpc4.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.ConstraintsW.b2_next))) hm3'
      fun st4 hm4 hpc4' ↦ ?_
    obtain ⟨hk, h15, h14, h2, h1, hbx4⟩ := after_eq run_b3 ▸ b3_keeps
    simp only [PcOk] at hpc4'
    obtain ⟨hy4, -⟩ := pc_cond hpc4'
    refine from8 hp ((hy4 ?_).trans (lbl_7 hp)) (hb.of_block hm3 hm4 hwf3 rfl hk)
      ((hm4.regs .rbx _ hbx4).trans hbx2) (hcond (by omega) (by omega) hm4 h15 h14)
      ((ew_of_loads hm4 h2 h1).trans (elem_row hpre hb (i := 12) (by omega)))
      (row_getD_ge (by omega))
    simp only [SBool.eval, CmpOp.apply, Sym.eval, low_W64, Env.ofMachine_regs]
    rw [show st2.data.regs.get64 .rdx = reg m0 .rdx from hdx2, beq_ofNat _ (by decide)]
    simpa using h13'
  · obtain ⟨hwf3, hm3⟩ := hrow (n := 224) (by omega)
    refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2'' hwf3 nofun hpc3 hm3
      fun st3 hm3' hpc3' ↦ ?_
    simp only [PcOk] at hpc3'
    obtain ⟨-, hn3⟩ := pc_cond hpc3'
    have hpc4 := hn3 (by
      simp only [SBool.eval, CmpOp.apply, Sym.eval, low_W64, Env.ofMachine_regs]
      rw [show st2.data.regs.get64 .rdx = reg m0 .rdx from hdx2, ult_ofNat _ (by decide)]
      simpa using h13)
    refine exec_at (infix_of b3_in_code (by simp [b3]) hp) (exec_after run_b2'' run_b3'') hwf3
      nofun (hpc4.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.ConstraintsW.b2_next))) hm3'
      fun st4 hm4 hpc4' ↦ ?_
    simp only [PcOk] at hpc4'
    obtain ⟨-, hn4⟩ := pc_cond hpc4'
    have hpc5 := hn4 (by
      simp only [SBool.eval, CmpOp.apply, Sym.eval, low_W64, Env.ofMachine_regs]
      rw [show st2.data.regs.get64 .rdx = reg m0 .rdx from hdx2, beq_ofNat _ (by decide)]
      simpa using h13')
    refine exec_at (infix_of b4_in_code (by simp [b4]) hp)
      (exec_after (exec_after run_b2'' run_b3'') run_b4) hwf3 nofun
      (hpc5.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.ConstraintsW.b3_next))) hm4
      fun st5 hm5 hpc5' ↦ ?_
    obtain ⟨hk, h15, h14, h2, h1, h13r, h12r, hbx5⟩ := after_eq run_b4 ▸ b4_keeps
    simp only [PcOk] at hpc5'
    exact .done _ ⟨hpc5'.trans (lbl_9 hp), hb.of_block hm3 hm5 hwf3 rfl hk,
      (hm5.regs .rbx _ hbx5).trans hbx2, hcond (by omega) (by omega) hm5 h15 h14,
      (ew_of_loads hm5 h2 h1).trans (elem_row hpre hb (i := 12) (by omega)),
      (ew_of_loads hm5 h13r h12r).trans (elem_row hpre hb (i := 13) (by omega))⟩

omit [Host] in
/-- A body with no outputs has the outputs `out`. -/
theorem Body.widen {m0 st : MachineData} {F S : Nat} {slots : List (Nat × Reg64)} {oa : BitVec 64}
    {on : Nat} (hb : Body m0 F S slots 0 0 st) : Body m0 F S slots oa on st :=
  ⟨hb.rsp, hb.frame, hb.regs, fun p hp ↦ hb.same p fun h ↦
    hp (h.elim (fun h0 ↦ absurd h0 (not_inRange_zero _)) Or.inr), hb.kept⟩

/-- `constraints_w`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧ ConstraintsWPost m0 s.data

/-- **`b9`-`b11`**: the two products, stored, and the return. -/
theorem tail (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : ConstraintsWPre m0) (h4 : (reg m0 .rdi).toNat = 4)
    {st : MachineState} (hG : G k m0 st) : Eventually (step1 Host.exe) (Post m0) st := by
  obtain ⟨hpc, hA⟩ := hG
  obtain ⟨hS, -, hrO, hoO⟩ := hpre
  have hF : 48 ≤ S := by decide
  have hnot : ∀ j < 32, ¬InRange (stackBelow m0 S) S (reg m0 .rcx + BitVec.ofNat 64 j) :=
    fun j hj ↦ Arrays.not_inRange_of_apart (Arrays.apart_mono hoO (Nat.le_add_right S 8)) hrO.2
      (Transcript.stack_noWrap hS) hj
  -- `b9`: `condition·inverse`
  have hwf9 := hA.body.wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.ConstraintsW.b9Offset + b9.length)).toBitVec)
    hS hF
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) run_b9 hwf9 (fun _ _ ↦ rfl) hpc
    hA.body.mid_match fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hk9, hsp9, hw9, hdi9, hsi9, hdx9, hcx9⟩ := after_eq run_b9 ▸ b9_call
  refine Body.call_mul hmul hA.body hS (by decide) (L := 8) (by decide) slots_ok hwf9
    hA.body.mid_match hm1 hpc1 hk9 hsp9 hw9 fun st2 hpc2 hb2 hprod hsv2 _ _ ↦ ?_
  have e1 : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14, .r15], reg st2.data r = reg st.data r := by
    intro r hr
    have hc : calleeSaved r = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [hsv2 r hc]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact keep hA.body.mid_match hm1 rfl rfl
  have hP1 : ewRet st2.data = (row m0).getD 5 0 * (row m0).getD 12 0 := by
    rw [hprod, show reg st1.data .rdi = reg st.data .r15 from hm1.regs .rdi _ hdi9,
      show reg st1.data .rsi = reg st.data .r14 from hm1.regs .rsi _ hsi9,
      show reg st1.data .rdx = reg st.data .rdx from hm1.regs .rdx _ hdx9,
      show reg st1.data .rcx = reg st.data .rcx from hm1.regs .rcx _ hcx9, hA.cond, hA.inv]
    rfl
  have hbx2 : reg st2.data .rbx = reg m0 .rcx := (e1 .rbx (by simp)).trans hA.rbx
  -- `b10a`: `out[0]`
  have hb2' : Body m0 48 S slots (reg m0 .rcx) 32 st2.data := Body.widen hb2
  have hwf10 : (Env.ofMachine st2.data [(stackBelow m0 48, 48 + 8), (reg m0 .rcx, 32)]).WF :=
    Arrays.wf_two (stackOk_mono hS hF) hb2.kept ⟨fun j hj ↦ hb2.kept _ (hrO.1 j hj), hrO.2⟩
      (Transcript.Apart.symm' (apart_frame hoO hS.1 hF))
  have hm10 : Match (Env.ofMachine st2.data [(stackBelow m0 48, 48 + 8), (reg m0 .rcx, 32)])
      outS st2.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb2.rsp, known_ptr rfl hbx2, trivial⟩ trivial trivial
      trivial
  refine exec_at (infix_of ((infix_take b10 4).trans b10_in_code (by simp [b10]))
    (by simp [b10]) hp) run_b10a hwf10 nofun
    (hpc2.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.ConstraintsW.b9_next))) hm10
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hk10, hw10, hv0, hv1⟩ := after_eq run_b10a ▸ b10a_store
  have hb3 := hb2'.of_store hwf10 hm10 hm3 hk10 hw10 (fun _ h ↦ h)
    (fun p hp ↦ (slots_ok p hp).2)
  have e3 : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14, .r15], reg st3.data r = reg st.data r := by
    intro r hr
    rw [← e1 r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact keep hm10 hm3 rfl rfl
  have hE0 : EWAt st3.data.dmem (reg m0 .rcx)
      ((row m0).getD 13 0 + (row m0).getD 5 0 * (row m0).getD 12 0) := by
    have := ewAt_of_writes hm3 (r := 1) (o := 0) rfl (by decide) hv0 hv1
    rw [Arrays.add_ofNat_zero] at this
    simp only [Sym.eval, Arrays.xor_eval, Env.ofMachine_regs] at this
    rw [ewArg_xor] at this
    rw [ew_add_comm, ← hP1, ← hA.flag, ← e1 .r13 (by simp), ← e1 .r12 (by simp)]
    exact this
  -- `b10b`: `condition·(flag + 1)`
  have hwf11 := hb3.wf (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + (40 + 4) + b10b.length)).toBitVec) hS hF
  simp only [PcOk] at hpc3
  refine exec_at (infix_of ((infix_drop b10 4).trans b10_in_code (by simp [b10]))
    (by simp [b10]) hp) run_b10b hwf11 (fun _ _ ↦ rfl)
    (hpc3.trans (congrArg Host.addrOf (by have : (b10.take 4).length = 4 := rfl; omega)))
    hb3.mid_match fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hk11, hsp11, hw11, hdi11, hsi11, hdx11, hcx11⟩ := after_eq run_b10b ▸ b10b_call
  refine Body.call_mul hmul hb3 hS (by decide) (L := 8) (by decide) slots_ok hwf11
    hb3.mid_match hm4 hpc4 hk11 hsp11 hw11 fun st5 hpc5 hb5 hprod2 hsv5 hout5 _ ↦ ?_
  have hP2 : ewRet st5.data = (row m0).getD 5 0 * ((row m0).getD 13 0 + 1) := by
    have hdx : reg st4.data .rdx = reg st.data .r13 ^^^ BitVec.ofNat 64 1 := by
      rw [show reg st4.data .rdx = _ from hm4.regs .rdx _ hdx11, ← e3 .r13 (by simp)]
      simp only [Sym.eval, Arrays.xor_eval, Env.ofMachine_regs]
    rw [hprod2, show reg st4.data .rdi = reg st3.data .r15 from hm4.regs .rdi _ hdi11,
      show reg st4.data .rsi = reg st3.data .r14 from hm4.regs .rsi _ hsi11, hdx,
      show reg st4.data .rcx = reg st3.data .r12 from hm4.regs .rcx _ hcx11,
      e3 .r15 (by simp), e3 .r14 (by simp), e3 .r12 (by simp), one_add_ewArg, hA.flag, hA.cond,
      ew_add_comm 1]
    rfl
  have hbx5 : reg st5.data .rbx = reg m0 .rcx := by
    rw [hsv5 .rbx rfl, keep hb3.mid_match hm4 (r := .rbx) rfl rfl, e3 .rbx (by simp), hA.rbx]
  have hE0' : EWAt st5.data.dmem (reg m0 .rcx)
      ((row m0).getD 13 0 + (row m0).getD 5 0 * (row m0).getD 12 0) := fun i hi ↦ by
    have hi16 : i < 16 := by simpa [NativeRustcVm.length_ewBytes] using hi
    rw [hout5 _ (hnot i (by omega))]
    exact hE0 i hi
  -- `b11a`: `out[1]`
  have hwf12 : (Env.ofMachine st5.data [(stackBelow m0 48, 48 + 8), (reg m0 .rcx, 32)]).WF :=
    Arrays.wf_two (stackOk_mono hS hF) hb5.kept ⟨fun j hj ↦ hb5.kept _ (hrO.1 j hj), hrO.2⟩
      (Transcript.Apart.symm' (apart_frame hoO hS.1 hF))
  have hm12 : Match (Env.ofMachine st5.data [(stackBelow m0 48, 48 + 8), (reg m0 .rcx, 32)])
      outS st5.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb5.rsp, known_ptr rfl hbx5, trivial⟩ trivial trivial
      trivial
  refine exec_at (infix_of ((infix_take b11 2).trans b11_in_code (by simp [b11]))
    (by simp [b11]) hp) run_b11a hwf12 nofun
    (hpc5.trans (congrArg Host.addrOf (by have hn := NativeRustcVmX64.Vm.ConstraintsW.b10_next; have hl := NativeRustcVmX64.Vm.ConstraintsW.b10_length; simp only [NativeRustcVmX64.Vm.ConstraintsW.b10Length] at hl; simp only [List.length_drop]; omega))) hm12
    fun st6 hm6 hpc6 ↦ ?_
  obtain ⟨hk12, hw12, hov, hz0, hz1⟩ := after_eq run_b11a ▸ b11a_store
  have hb6 := hb5.of_store hwf12 hm12 hm6 hk12 hw12 (fun _ h ↦ h)
    (fun p hp ↦ (slots_ok p hp).2)
  have hE1 : EWAt st6.data.dmem (reg m0 .rcx + BitVec.ofNat 64 16) (ewRet st5.data) := by
    have := ewAt_of_writes hm6 (r := 1) (o := 16) (u := .reg .rax) (v := .reg .rdx) rfl
      (by decide) hz0 hz1
    rwa [Arrays.eval_reg, Arrays.eval_reg, Env.ofMachine_regs, Env.ofMachine_regs] at this
  have hE0'' : EWAt st6.data.dmem (reg m0 .rcx)
      ((row m0).getD 13 0 + (row m0).getD 5 0 * (row m0).getD 12 0) := by
    have := bytesAt_keep hm6 (r := 1) (o := 0)
      (bs := NativeRustcVm.ewBytes ((row m0).getD 13 0 + (row m0).getD 5 0 * (row m0).getD 12 0))
      rfl (by rw [NativeRustcVm.length_ewBytes]; decide)
      (by rw [NativeRustcVm.length_ewBytes]; exact hov)
      (by rw [Arrays.add_ofNat_zero]; exact hE0')
    rwa [Arrays.add_ofNat_zero] at this
  -- `b11b`: the epilogue
  simp only [PcOk] at hpc6
  refine exec_at (infix_of ((infix_drop b11 2).trans b11_in_code (by simp [b11]))
    (by simp [b11]) hp) run_b11b (hb6.wf (vars := fun _ ↦ 0) (ret := 0) hS hF) nofun
    (hpc6.trans (congrArg Host.addrOf (by have : (b11.take 2).length = 2 := rfl; omega)))
    hb6.mid_match fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨hres, hmem7, hax7⟩ := after_eq run_b11b ▸ b11b_restores
  obtain ⟨hpc7', hrsp7, hdm7, hsv7⟩ := hb6.done hS hF hm7 hpc7 hres hmem7 (ret_not_in hS hrO.2 hoO)
  have hr : constraintsW (reg m0 .rdi).toNat (row m0) =
      #[(row m0).getD 13 0 + (row m0).getD 5 0 * (row m0).getD 12 0,
        (row m0).getD 5 0 * ((row m0).getD 13 0 + 1)] := by
    rw [h4, constraintsW_jump]
  refine .done _ ⟨hpc7', hrsp7, ?_, ?_, fun p hp' ↦ by rw [hdm7]; exact hb6.same p hp', hsv7⟩
  · rw [hr, show reg st7.data .rax = _ from hm7.regs .rax _ hax7]
    rfl
  · show EWsAt st7.data.dmem (reg m0 .rcx) (constraintsW (reg m0 .rdi).toNat (row m0)).toList
    rw [hr, hdm7]
    show EWsAt _ _ ([_] ++ [_])
    rw [NativeRustcVm.ewsAt_append_iff, NativeRustcVm.ewsAt_singleton_iff,
      NativeRustcVm.ewsAt_singleton_iff, ← hP2]
    exact ⟨hE0'', hE1⟩

/-- **`constraints_w` meets its contract.** -/
theorem constraintsW_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.ConstraintsW.entryLabel) ConstraintsWPre ConstraintsWPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  have hF : 48 ≤ S := by decide
  have hS48 := stackOk_mono hpre.1 hF
  have hwf := frame_wf (m0 := m0) (m := m0) (vars := fun _ ↦ 0) (ret := 0) hS48 fun _ h ↦ h
  have hm : Match (frameEnv m0 m0 48) entryS m0 := match_frame
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf nofun hm
    fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, NativeRustcVmX64.Vm.ConstraintsW.b0_length] at hpc1
  obtain ⟨hy, hn⟩ := pc_cond hpc1
  by_cases h4 : (reg m0 .rdi).toNat = 4
  · have hpc2 := hn (by
      simp only [SBool.eval, CmpOp.apply, Sym.eval, low_W64, Env.ofMachine_regs]
      rw [beq_ofNat _ (by decide)]
      simpa using h4)
    exact Eventually.bind (head hp hpre hpc2 (by rw [after_eq run_b0]; exact hm1) hwf)
      fun s hs ↦ tail hp hmul hpre h4 hs
  · have hpc2 := hy (by
      simp only [SBool.eval, CmpOp.apply, Sym.eval, low_W64, Env.ofMachine_regs]
      rw [beq_ofNat _ (by decide)]
      simpa using h4)
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) (exec_after run_b0 run_b5) hwf nofun
      (hpc2.trans (lbl_1 hp)) hm1 fun st2 hm2 hpc3 ↦ ?_
    obtain ⟨hsp, hkeep, -, hax⟩ := after_eq (exec_after run_b0 run_b5) ▸ b5_ret
    obtain ⟨h1, h2, h3, h4'⟩ := leaf_done hS48 hm2 hpc3 hsp hkeep (by simp)
    refine .done _ ⟨h1, h2, ?_, ?_, fun p hp' ↦ h3 p fun h ↦ hp' (Or.inr ?_), h4'⟩
    · rw [constraintsW_other h4, show reg st2.data .rax = _ from hm2.regs .rax _ hax]
      rfl
    · rw [constraintsW_other h4]
      intro i hi
      simp at hi
    · exact inRange_stack (F := 48) (n := 0) (k := 48) hpre.1.1 (by decide) le_rfl
        (by simpa using h)

end

end NativeRustcVmX64.Layout.ConstraintsW
