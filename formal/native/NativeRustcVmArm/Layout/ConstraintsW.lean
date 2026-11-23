module

public import NativeRustcVmArm.Code.Vm.ConstraintsW.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Layout.ConstraintsW.Exec
public import NativeRustcVmArm.Layout.Body

/-!
# `constraints_w` on AArch64

**`constraintsW_spec`**: rustc's `constraints_w(opcode, row, out)`, placed anywhere in the
program, meets `ConstraintsWPre`/`ConstraintsWPost` given `EW::mul`'s contract. Not `JUMP`
(`b0`): it returns `0` (`b5`). `JUMP`: the prologue (`b1`) saves X19-X23 and X30 and keeps `out`
in X19; the row's `condition`, `inverse` and `flag` (`row[5]`, `row[12]`, `row[13]`, `0` past the
row) come to X21:X20, X2:X3, X23:X22 (`b2`-`b4`, `b6`-`b8`; `At9`); `b9` multiplies
`condition·inverse`, `b10` stores `flag + condition·inverse` in `out[0]` and multiplies
`condition·(flag + 1)`, which `b11` stores in `out[1]` before the epilogue returns `2`.
-/

namespace NativeRustcVmArm.Layout.ConstraintsW

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.ConstraintsW NativeVm.Model
open LeanVM.Protocol.Verifier
open NativeRustcVmArm.Arrays (Body calleeRegs inSlots keepsAll restores savedRegs entry_match
  wf_one elem_of_apart apart_zero noWrap_zero ew_of_loads add_ofNat_zero pc_cond frame_ok
  toNat_add_ofNat')
open NativeRustcVm (ewsOf ewOf EWsAt EWAt WordAt)

public section

/-- The row. -/
abbrev row (m : MachineData) : Array EW := slice m m.regs.X1 m.regs.X2

/-- `constraintsW` of `JUMP`. -/
theorem constraintsW_jump (r : Array EW) :
    constraintsW 4 r =
      #[r.getD 13 0 + r.getD 5 0 * r.getD 12 0, r.getD 5 0 * (r.getD 13 0 + 1)] := by
  unfold constraintsW opJump
  simp only [↓reduceIte]
  rfl

/-- `constraintsW` of another table. -/
theorem constraintsW_other {op : Nat} (h : op ≠ 4) (r : Array EW) : constraintsW op r = #[] := by
  unfold constraintsW opJump
  simp [h]

theorem row_getD {m : MachineData} {i : Nat} (h : i < m.regs.X2.toNat) :
    (row m).getD i 0 = ewOf m.dmem (m.regs.X1.toBitVec + BitVec.ofNat 64 (16 * i)) := by
  unfold Array.getD
  simp [slice, h, ewsOf]

theorem row_getD_ge {m : MachineData} {i : Nat} (h : m.regs.X2.toNat ≤ i) :
    (row m).getD i 0 = 0 := by
  unfold Array.getD
  simp [slice, ewsOf]
  omega

variable [Host] {k : Nat}

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.ConstraintsW.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.ConstraintsW.b0Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.ConstraintsW.entryOffset) NativeRustcVmArm.Vm.ConstraintsW.entry_at
theorem lbl_5 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.ConstraintsW.label_5 = Host.addrOf (k + NativeRustcVmArm.Vm.ConstraintsW.b5Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.ConstraintsW.b5Offset) NativeRustcVmArm.Vm.ConstraintsW.label_5_at
theorem lbl_6 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.ConstraintsW.label_6 = Host.addrOf (k + NativeRustcVmArm.Vm.ConstraintsW.b6Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.ConstraintsW.b6Offset) NativeRustcVmArm.Vm.ConstraintsW.label_6_at
theorem lbl_7 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.ConstraintsW.label_7 = Host.addrOf (k + NativeRustcVmArm.Vm.ConstraintsW.b7Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.ConstraintsW.b7Offset) NativeRustcVmArm.Vm.ConstraintsW.label_7_at
theorem lbl_8 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.ConstraintsW.label_8 = Host.addrOf (k + NativeRustcVmArm.Vm.ConstraintsW.b8Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.ConstraintsW.b8Offset) NativeRustcVmArm.Vm.ConstraintsW.label_8_at
theorem lbl_9 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.ConstraintsW.label_9 = Host.addrOf (k + NativeRustcVmArm.Vm.ConstraintsW.b9Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.ConstraintsW.b9Offset) NativeRustcVmArm.Vm.ConstraintsW.label_9_at

abbrev S : Nat := constraintsWStack

/-- A register the block left as it was (its literal state maps it to its atom). -/
theorem keep {env : Env} {S₀ S₁ : SState} {m m' : MachineData} (hm : Match env S₀ m)
    (hm' : Match env S₁ m') {r : XReg} (h0 : S₀.reg r = some (.reg r))
    (h1 : S₁.reg r = some (.reg r)) : m'.regs.getXReg r = m.regs.getXReg r :=
  Match.reg_eq hm hm' h0 h1

/-- A register the block set to `0`. -/
theorem zero_of {env : Env} {S₁ : SState} {m' : MachineData} (hm' : Match env S₁ m') {r : XReg}
    (h1 : S₁.reg r = some (.lit 0)) : m'.regs.getXReg r = 0 :=
  UInt64.toBitVec_inj.mp (hm'.regs r _ h1)

/-- **At `b9`**: the body, `out` in X19, `condition`, `inverse`, `flag` in X21:X20, X2:X3,
X23:X22. -/
structure At9 (m0 : MachineData) (s : MachineData) : Prop where
  body : Body m0 48 S slots 0 0 s
  x19 : s.regs.X19 = m0.regs.X3
  cond : (⟨s.regs.X21, s.regs.X20⟩ : EW) = (row m0).getD 5 0
  inv : (⟨s.regs.X2, s.regs.X3⟩ : EW) = (row m0).getD 12 0
  flag : (⟨s.regs.X23, s.regs.X22⟩ : EW) = (row m0).getD 13 0

/-- At `b9`. -/
abbrev G (k : Nat) (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ConstraintsW.b9Offset) ∧ At9 m0 s.data

omit [Host] in
/-- Element `i` of the row, read in a body. -/
theorem elem_row {m0 st : MachineData} (hpre : ConstraintsWPre m0)
    (hb : Body m0 48 S slots 0 0 st) {i : Nat} (hi : i < m0.regs.X2.toNat) :
    ewOf st.dmem (m0.regs.X1.toBitVec + BitVec.ofNat 64 (16 * i)) = (row m0).getD i 0 := by
  rw [row_getD hi, elem_of_apart hb.same hpre.1 hpre.2.1.1.2 hpre.2.1.2 (apart_zero _ _)
    noWrap_zero hi, NativeRustcVm.getElem_ewsOf]

/-- The row's first `n` bytes as region 0, X1 its base. -/
theorem row_match {m0 : MachineData} (hpre : ConstraintsWPre m0) {st : MachineData}
    (hb : Body m0 48 S slots 0 0 st) (h1 : st.regs.X1 = m0.regs.X1) {n : Nat}
    (hn : n ≤ 16 * m0.regs.X2.toNat) :
    (Env.ofMachine st [(m0.regs.X1.toBitVec, n)]).WF ∧
      Match (Env.ofMachine st [(m0.regs.X1.toBitVec, n)]) (rowS n) st := by
  obtain ⟨hmap, hnw⟩ := readable_prefix hpre.2.1.1 hb.kept hn
  refine ⟨wf_one hmap hnw, match_ofMachine ⟨rfl, nofun, trivial⟩ rfl ⟨?_, trivial⟩ trivial
    trivial trivial⟩
  show (st.regs.getXReg .X1).toBitVec = m0.regs.X1.toBitVec + BitVec.ofInt 64 0
  rw [ofInt_zero, BitVec.add_zero]
  exact congrArg UInt64.toBitVec h1

/-- X1 after a block run from `rowS n`, which kept it: the row's base. -/
theorem x1_of {st st' : MachineData} {m0 : MachineData} {n : Nat} {S₁ : SState}
    (hm' : Match (Env.ofMachine st [(m0.regs.X1.toBitVec, n)]) S₁ st')
    (h : S₁.reg .X1 = some (.ptr 0 0) := by rfl) : st'.regs.X1 = m0.regs.X1 := by
  apply UInt64.toBitVec_inj.mp
  rw [show st'.regs.X1 = st'.regs.getXReg .X1 from rfl, hm'.regs .X1 _ h]
  show m0.regs.X1.toBitVec + BitVec.ofInt 64 0 = _
  rw [ofInt_zero, BitVec.add_zero]

/-- **`b8`**: `flag` is `0`. -/
theorem from8 (hp : Placed code k) {m0 : MachineData} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ConstraintsW.b8Offset)) (hb : Body m0 48 S slots 0 0 st.data)
    (h19 : st.data.regs.X19 = m0.regs.X3)
    (hc : (⟨st.data.regs.X21, st.data.regs.X20⟩ : EW) = (row m0).getD 5 0)
    (hi : (⟨st.data.regs.X2, st.data.regs.X3⟩ : EW) = (row m0).getD 12 0)
    (hf : (row m0).getD 13 0 = 0) : Eventually (step1 Host.exe) (G k m0) st := by
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8 (Env.wf_nil _) hpc (match_nil _)
    fun st' hm hpc' ↦ .done _ ⟨?_, hb.of_block (match_nil _) hm (Env.wf_nil _) rfl
      (after_eq run_b8 ▸ b8_keeps), ?_, ?_, ?_, ?_⟩
  · simp only [PcOk, NativeRustcVmArm.Vm.ConstraintsW.b8_length, NativeRustcVmArm.Vm.ConstraintsW.b8Length] at hpc'
    exact hpc'
  · rw [← h19]; exact keep (match_nil _) hm (r := .X19) rfl rfl
  · rw [← hc]
    show (⟨st'.data.regs.getXReg .X21, st'.data.regs.getXReg .X20⟩ : EW) = _
    rw [keep (match_nil _) hm (r := .X21) rfl rfl, keep (match_nil _) hm (r := .X20) rfl rfl]; rfl
  · rw [← hi]
    show (⟨st'.data.regs.getXReg .X2, st'.data.regs.getXReg .X3⟩ : EW) = _
    rw [keep (match_nil _) hm (r := .X2) rfl rfl, keep (match_nil _) hm (r := .X3) rfl rfl]; rfl
  · rw [hf]
    show (⟨st'.data.regs.getXReg .X23, st'.data.regs.getXReg .X22⟩ : EW) = _
    rw [zero_of hm (r := .X23) rfl, zero_of hm (r := .X22) rfl]; rfl

/-- **`b7`**: `inverse` and `flag` are `0`. -/
theorem from7 (hp : Placed code k) {m0 : MachineData} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ConstraintsW.b7Offset)) (hb : Body m0 48 S slots 0 0 st.data)
    (h19 : st.data.regs.X19 = m0.regs.X3)
    (hc : (⟨st.data.regs.X21, st.data.regs.X20⟩ : EW) = (row m0).getD 5 0)
    (hi : (row m0).getD 12 0 = 0) (hf : (row m0).getD 13 0 = 0) :
    Eventually (step1 Host.exe) (G k m0) st := by
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) run_b7 (Env.wf_nil _) hpc (match_nil _)
    fun st' hm hpc' ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.ConstraintsW.b7_length, NativeRustcVmArm.Vm.ConstraintsW.b7Length] at hpc'
  refine from8 hp hpc' (hb.of_block (match_nil _) hm (Env.wf_nil _) rfl
    (after_eq run_b7 ▸ b7_keeps)) ?_ ?_ ?_ hf
  · rw [← h19]; exact keep (match_nil _) hm (r := .X19) rfl rfl
  · rw [← hc]
    show (⟨st'.data.regs.getXReg .X21, st'.data.regs.getXReg .X20⟩ : EW) = _
    rw [keep (match_nil _) hm (r := .X21) rfl rfl, keep (match_nil _) hm (r := .X20) rfl rfl]; rfl
  · rw [hi]
    show (⟨st'.data.regs.getXReg .X2, st'.data.regs.getXReg .X3⟩ : EW) = _
    rw [zero_of hm (r := .X2) rfl, zero_of hm (r := .X3) rfl]; rfl

/-- **`b6`**: a row shorter than `6`, all three `0`. -/
theorem from6 (hp : Placed code k) {m0 : MachineData} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ConstraintsW.b6Offset)) (hb : Body m0 48 S slots 0 0 st.data)
    (h19 : st.data.regs.X19 = m0.regs.X3) (hc : (row m0).getD 5 0 = 0)
    (hi : (row m0).getD 12 0 = 0) (hf : (row m0).getD 13 0 = 0) :
    Eventually (step1 Host.exe) (G k m0) st := by
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 (Env.wf_nil _) hpc (match_nil _)
    fun st' hm hpc' ↦ ?_
  simp only [PcOk] at hpc'
  refine from8 hp (hpc'.trans (lbl_8 hp)) (hb.of_block (match_nil _) hm (Env.wf_nil _) rfl
    (after_eq run_b6 ▸ b6_keeps)) ?_ ?_ ?_ hf
  · rw [← h19]; exact keep (match_nil _) hm (r := .X19) rfl rfl
  · rw [hc]
    show (⟨st'.data.regs.getXReg .X21, st'.data.regs.getXReg .X20⟩ : EW) = _
    rw [zero_of hm (r := .X21) rfl, zero_of hm (r := .X20) rfl]; rfl
  · rw [hi]
    show (⟨st'.data.regs.getXReg .X2, st'.data.regs.getXReg .X3⟩ : EW) = _
    rw [zero_of hm (r := .X2) rfl, zero_of hm (r := .X3) rfl]; rfl

/-- **`b4`**: `flag` loaded. -/
theorem from4 (hp : Placed code k) {m0 : MachineData} (hpre : ConstraintsWPre m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ConstraintsW.b4Offset)) (hb : Body m0 48 S slots 0 0 st.data)
    (hlen : 14 ≤ m0.regs.X2.toNat) (h1 : st.data.regs.X1 = m0.regs.X1)
    (h19 : st.data.regs.X19 = m0.regs.X3)
    (hc : (⟨st.data.regs.X21, st.data.regs.X20⟩ : EW) = (row m0).getD 5 0)
    (hi : (⟨st.data.regs.X2, st.data.regs.X3⟩ : EW) = (row m0).getD 12 0) :
    Eventually (step1 Host.exe) (G k m0) st := by
  obtain ⟨hwf, hm⟩ := row_match hpre hb h1 (n := 224) (by omega)
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf hpc hm fun st' hm' hpc' ↦
    .done _ ⟨?_, hb.of_block hm hm' hwf rfl (after_eq run_b4 ▸ b4_keeps), ?_, ?_, ?_, ?_⟩
  · simp only [PcOk] at hpc'
    exact hpc'.trans (lbl_9 hp)
  · rw [← h19]; exact keep hm hm' (r := .X19) rfl rfl
  · rw [← hc]
    show (⟨st'.data.regs.getXReg .X21, st'.data.regs.getXReg .X20⟩ : EW) = _
    rw [keep hm hm' (r := .X21) rfl rfl, keep hm hm' (r := .X20) rfl rfl]; rfl
  · rw [← hi]
    show (⟨st'.data.regs.getXReg .X2, st'.data.regs.getXReg .X3⟩ : EW) = _
    rw [keep hm hm' (r := .X2) rfl rfl, keep hm hm' (r := .X3) rfl rfl]; rfl
  · exact (ew_of_loads (off := 208) (lo := .X23) (hi := .X22) hm' rfl rfl).trans (elem_row hpre hb (i := 13) (by omega))

/-- **`b3`**: `inverse` loaded; a row of `13` has no `flag`. -/
theorem from3 (hp : Placed code k) {m0 : MachineData} (hpre : ConstraintsWPre m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ConstraintsW.b3Offset)) (hb : Body m0 48 S slots 0 0 st.data)
    (hlen : 13 ≤ m0.regs.X2.toNat) (h1 : st.data.regs.X1 = m0.regs.X1)
    (h2 : st.data.regs.X2 = m0.regs.X2) (h19 : st.data.regs.X19 = m0.regs.X3)
    (hc : (⟨st.data.regs.X21, st.data.regs.X20⟩ : EW) = (row m0).getD 5 0) :
    Eventually (step1 Host.exe) (G k m0) st := by
  obtain ⟨hwf, hm⟩ := row_match hpre hb h1 (n := 208) (by omega)
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf hpc hm fun st' hm' hpc' ↦ ?_
  have hb' := hb.of_block hm hm' hwf rfl (after_eq run_b3 ▸ b3_keeps)
  have h19' : st'.data.regs.X19 = m0.regs.X3 := by rw [← h19]; exact keep hm hm' (r := .X19) rfl rfl
  have hc' : (⟨st'.data.regs.X21, st'.data.regs.X20⟩ : EW) = (row m0).getD 5 0 := by
    rw [← hc]
    show (⟨st'.data.regs.getXReg .X21, st'.data.regs.getXReg .X20⟩ : EW) = _
    rw [keep hm hm' (r := .X21) rfl rfl, keep hm hm' (r := .X20) rfl rfl]; rfl
  have hi' : (⟨st'.data.regs.X2, st'.data.regs.X3⟩ : EW) = (row m0).getD 12 0 :=
    (ew_of_loads (off := 192) (lo := .X2) (hi := .X3) hm' rfl rfl).trans (elem_row hpre hb (i := 12) (by omega))
  simp only [PcOk, NativeRustcVmArm.Vm.ConstraintsW.b3_length, NativeRustcVmArm.Vm.ConstraintsW.b3Length] at hpc'
  sym_simp at hpc'
  have hx2 : (st.data.regs.getXReg .X2).toBitVec.toNat = m0.regs.X2.toNat := by
    show (st.data.regs.X2).toNat = _; rw [h2]
  obtain ⟨hy, hn⟩ := pc_cond hpc'
  by_cases h13 : m0.regs.X2.toNat = 13
  · exact from8 hp ((hy ((beq_iff (by decide)).mpr (hx2.trans h13))).trans (lbl_8 hp)) hb' h19'
      hc' hi' (row_getD_ge (by omega))
  · exact from4 hp hpre (hn fun h ↦ h13 (hx2.symm.trans ((beq_iff (by decide)).mp h))) hb'
      (by omega) (x1_of hm') h19' hc' hi'

/-- **`b2`**: `condition` loaded; a row shorter than `13` has no `inverse`. -/
theorem from2 (hp : Placed code k) {m0 : MachineData} (hpre : ConstraintsWPre m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ConstraintsW.b2Offset)) (hb : Body m0 48 S slots 0 0 st.data)
    (hlen : 6 ≤ m0.regs.X2.toNat) (h1 : st.data.regs.X1 = m0.regs.X1)
    (h2 : st.data.regs.X2 = m0.regs.X2) (h19 : st.data.regs.X19 = m0.regs.X3) :
    Eventually (step1 Host.exe) (G k m0) st := by
  obtain ⟨hwf, hm⟩ := row_match hpre hb h1 (n := 96) (by omega)
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf hpc hm fun st' hm' hpc' ↦ ?_
  have hb' := hb.of_block hm hm' hwf rfl (after_eq run_b2 ▸ b2_keeps)
  have h19' : st'.data.regs.X19 = m0.regs.X3 := by rw [← h19]; exact keep hm hm' (r := .X19) rfl rfl
  have hc' : (⟨st'.data.regs.X21, st'.data.regs.X20⟩ : EW) = (row m0).getD 5 0 :=
    (ew_of_loads (off := 80) (lo := .X21) (hi := .X20) hm' rfl rfl).trans (elem_row hpre hb (i := 5) (by omega))
  simp only [PcOk, NativeRustcVmArm.Vm.ConstraintsW.b2_length, NativeRustcVmArm.Vm.ConstraintsW.b2Length] at hpc'
  sym_simp at hpc'
  have hx2 : (st.data.regs.getXReg .X2).toBitVec.toNat = m0.regs.X2.toNat := by
    show (st.data.regs.X2).toNat = _; rw [h2]
  obtain ⟨hy, hn⟩ := pc_cond hpc'
  by_cases h13 : m0.regs.X2.toNat < 13
  · exact from7 hp ((hy ((ult_iff (by decide)).mpr (hx2.trans_lt h13))).trans (lbl_7 hp)) hb'
      h19' hc' (row_getD_ge (by omega)) (row_getD_ge (by omega))
  · exact from3 hp hpre (hn fun h ↦ h13 (hx2.symm.trans_lt ((ult_iff (by decide)).mp h))) hb'
      (by omega) (x1_of hm')
      (by rw [← h2]; exact keep hm hm' (r := .X2) rfl rfl) h19' hc'

/-- **The entry and the prologue**: `JUMP`, on to `b9`. -/
theorem head (hp : Placed code k) {m0 : MachineData} (hpre : ConstraintsWPre m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ConstraintsW.b1Offset))
    (hm1 : Match (Arrays.frameEnv m0 m0 48) (after b0 entryS) st.data)
    (hwf : (Arrays.frameEnv m0 m0 48).WF) : Eventually (step1 Host.exe) (G k m0) st := by
  have hm1' : Match (Arrays.frameEnv m0 m0 48) (after b0 entryS) st.data := hm1
  rw [after_eq run_b0] at hm1'
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) (exec_after run_b0 run_b1) hwf hpc hm1'
    fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hw, hmem, hregs⟩ := after_eq run_b1 ▸ b1_frame
  have hb : Body m0 48 S slots 0 0 st2.data := Body.of_entry hpre.1 (by decide) hm2 rfl hw hregs hmem
  have h1 : st2.data.regs.X1 = m0.regs.X1 := UInt64.toBitVec_inj.mp (hm2.regs .X1 _ rfl)
  have h2 : st2.data.regs.X2 = m0.regs.X2 := UInt64.toBitVec_inj.mp (hm2.regs .X2 _ rfl)
  have h19 : st2.data.regs.X19 = m0.regs.X3 := UInt64.toBitVec_inj.mp (hm2.regs .X19 _ rfl)
  simp only [PcOk, NativeRustcVmArm.Vm.ConstraintsW.b1_length, NativeRustcVmArm.Vm.ConstraintsW.b1Length] at hpc2
  sym_simp at hpc2
  obtain ⟨hy, hn⟩ := pc_cond hpc2
  by_cases h6 : m0.regs.X2.toNat < 6
  · exact from6 hp ((hy ((ult_iff (by decide)).mpr h6)).trans (lbl_6 hp)) hb h19
      (row_getD_ge (by omega)) (row_getD_ge (by omega)) (row_getD_ge (by omega))
  · exact from2 hp hpre (hn fun h ↦ h6 ((ult_iff (by decide)).mp h)) hb (by omega) h1 h2 h19

/-- `constraints_w`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ ConstraintsWPost m0 s.data

/-- **`b9`-`b11`**: the two products, stored, and the return. -/
theorem tail (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : ConstraintsWPre m0) (h4 : m0.regs.X0.toNat = 4) {st : MachineState}
    (hG : G k m0 st) : Eventually (step1 Host.exe) (Post m0) st := by
  obtain ⟨hpc, hA⟩ := hG
  obtain ⟨hS, -, hro, hoo⟩ := hpre
  -- `b9`: `condition·inverse`
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) run_b9 (Env.wf_nil _) hpc (match_nil _)
    fun st9 hm9 hpc9 ↦ ?_
  have bd9 := hA.body.of_block (match_nil _) hm9 (Env.wf_nil _) rfl (after_eq run_b9 ▸ b9_keeps)
  simp only [NativeRustcVmArm.Vm.ConstraintsW.b9_length, NativeRustcVmArm.Vm.ConstraintsW.b9Length] at hpc9
  refine call_then hpc9 hmul (bd9.ewMulPre hS (by decide) (by decide)) fun st3 hpc3 hpost ↦ ?_
  have bd3 := bd9.call hS (by decide) (by decide) hpost
  have k3 : ∀ r, calleeSaved r = true → regsS.reg r = some (.reg r) →
      (after b9 regsS).reg r = some (.reg r) →
      st3.data.regs.getXReg r = st.data.regs.getXReg r := fun r hr h0 h ↦
    (hpost.2.2.2.1 r hr).trans (keep (match_nil _) hm9 h0 ((after_eq run_b9) ▸ h))
  have hP1 : (⟨st3.data.regs.X0, st3.data.regs.X1⟩ : EW) =
      (row m0).getD 5 0 * (row m0).getD 12 0 := by
    have a0 : st9.data.regs.X0 = st.data.regs.X21 := UInt64.toBitVec_inj.mp (hm9.regs .X0 _ rfl)
    have a1 : st9.data.regs.X1 = st.data.regs.X20 := UInt64.toBitVec_inj.mp (hm9.regs .X1 _ rfl)
    have a2 : st9.data.regs.X2 = st.data.regs.X2 := UInt64.toBitVec_inj.mp (hm9.regs .X2 _ rfl)
    have a3 : st9.data.regs.X3 = st.data.regs.X3 := UInt64.toBitVec_inj.mp (hm9.regs .X3 _ rfl)
    rw [hpost.1, hpost.2.1, a0, a1, a2, a3, hA.cond, hA.inv]
    rfl
  have hx19_3 : st3.data.regs.X19 = m0.regs.X3 := (k3 .X19 rfl rfl rfl).trans hA.x19
  -- `b10`: `out[0]`, then `condition·(flag + 1)`
  have hmo3 : Mapped st3.data.dmem m0.regs.X3.toBitVec 32 := fun j hj ↦ bd3.kept _ (hro.1 j hj)
  have hwf10 := wf_one hmo3 hro.2 (m := st3.data)
  have hm10 : Match (Env.ofMachine st3.data [(m0.regs.X3.toBitVec, 32)]) outS st3.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl ⟨by
      show (st3.data.regs.getXReg .X19).toBitVec = m0.regs.X3.toBitVec + BitVec.ofInt 64 0
      rw [ofInt_zero, BitVec.add_zero]
      exact congrArg UInt64.toBitVec hx19_3, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b10_in_code (by simp [b10]) hp) run_b10 hwf10 hpc3 hm10
    fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hk10, hw10, hv0, hv1⟩ := after_eq run_b10 ▸ b10_facts
  have bd4 := (Body.widen (oa := m0.regs.X3.toBitVec) (on := 32) bd3).of_write hS hm10 hm4 hwf10
    (fun _ h ↦ h) hk10 hw10 hoo (by decide) (by decide)
  have w0 := Match.wordAt_write hm4 (r := 0) (o := 0) (b := m0.regs.X3.toBitVec) (sz := 32) rfl
    (by decide) hv0
  have w1 := Match.wordAt_write hm4 (r := 0) (o := 8) (b := m0.regs.X3.toBitVec) (sz := 32) rfl
    (by decide) hv1
  sym_simp at w0 w1
  simp only [Env.ofMachine_regs] at w0 w1
  have e21 := k3 .X21 rfl rfl rfl
  have e20 := k3 .X20 rfl rfl rfl
  have e23 := k3 .X23 rfl rfl rfl
  have e22 := k3 .X22 rfl rfl rfl
  have hE0 : NativeRustcVm.EWAt st4.data.dmem m0.regs.X3.toBitVec
      ((row m0).getD 13 0 + (row m0).getD 5 0 * (row m0).getD 12 0) := by
    rw [← hP1, ← hA.flag, NativeRustcVm.ewAt_iff]
    rw [add_ofNat_zero] at w0
    refine ⟨?_, ?_⟩
    · have : UInt64.ofBitVec ((st3.data.regs.getXReg .X0).toBitVec ^^^
          (st3.data.regs.getXReg .X23).toBitVec) = st.data.regs.X23 ^^^ st3.data.regs.X0 := by
        rw [e23, UInt64.xor_comm]; rfl
      rw [this] at w0
      exact w0
    · have : UInt64.ofBitVec ((st3.data.regs.getXReg .X1).toBitVec ^^^
          (st3.data.regs.getXReg .X22).toBitVec) = st.data.regs.X22 ^^^ st3.data.regs.X1 := by
        rw [e22, UInt64.xor_comm]; rfl
      rw [this] at w1
      exact w1
  simp only [NativeRustcVmArm.Vm.ConstraintsW.b10_length, NativeRustcVmArm.Vm.ConstraintsW.b10Length] at hpc4
  refine call_then hpc4 hmul (bd4.ewMulPre hS (by decide) (by decide)) fun st5 hpc5 hpost2 ↦ ?_
  have bd5 := bd4.call hS (by decide) (by decide) hpost2
  have hP2 : (⟨st5.data.regs.X0, st5.data.regs.X1⟩ : EW) =
      (row m0).getD 5 0 * ((row m0).getD 13 0 + 1) := by
    have a0 : st4.data.regs.X0 = st.data.regs.X21 :=
      (UInt64.toBitVec_inj.mp (hm4.regs .X0 _ rfl)).trans e21
    have a1 : st4.data.regs.X1 = st.data.regs.X20 :=
      (UInt64.toBitVec_inj.mp (hm4.regs .X1 _ rfl)).trans e20
    have a2 : st4.data.regs.X2 = st.data.regs.X23 ^^^ 1 := by
      apply UInt64.toBitVec_inj.mp
      rw [show st4.data.regs.X2 = st4.data.regs.getXReg .X2 from rfl, hm4.regs .X2 _ rfl]
      sym_simp
      simp only [Env.ofMachine_regs, e23]
      rfl
    have a3 : st4.data.regs.X3 = st.data.regs.X22 :=
      (UInt64.toBitVec_inj.mp (hm4.regs .X3 _ rfl)).trans e22
    have hf1 : (⟨st.data.regs.X23 ^^^ 1, st.data.regs.X22⟩ : EW) = (row m0).getD 13 0 + 1 := by
      rw [← hA.flag]
      show _ = (⟨_ ^^^ 1, _ ^^^ 0⟩ : EW)
      rw [UInt64.xor_zero]
    rw [hpost2.1, hpost2.2.1, a0, a1, a2, a3, hf1, hA.cond]
    rfl
  have keep2 := Body.keep_call bd4 hS (n' := ewMulStack) (by decide) hoo hro.2 hpost2.2.2.1
  -- `b11`: `out[1]`, the epilogue
  have hx19_5 : st5.data.regs.X19 = m0.regs.X3 :=
    (hpost2.2.2.2.1 .X19 rfl).trans (UInt64.toBitVec_inj.mp (ptr0_of hm4 rfl))
  obtain ⟨hmapF, hnwF, -⟩ := frame_ok hS (by decide : 48 ≤ S)
  have hwf11 : (Env.ofMachine st5.data [(m0.regs.SP.toBitVec - BitVec.ofNat 64 48, 48),
      (m0.regs.X3.toBitVec, 32)]).WF :=
    Env.wf_of ⟨⟨fun j hj ↦ bd5.kept _ (hmapF j hj), hnwF⟩,
      ⟨fun j hj ↦ bd5.kept _ (hro.1 j hj), hro.2⟩, trivial⟩
      (List.pairwise_pair.mpr (apart_frame hS (by decide) hoo))
  have hm11 : Match (Env.ofMachine st5.data [(m0.regs.SP.toBitVec - BitVec.ofNat 64 48, 48),
      (m0.regs.X3.toBitVec, 32)]) exitS st5.data :=
    match_ofMachine ⟨rfl, fun _ ↦ Arrays.frame_aligned hS (by decide) rfl, rfl, nofun, trivial⟩
      (by
        rw [bd5.sp]
        show _ = (m0.regs.SP.toBitVec - BitVec.ofNat 64 48) + BitVec.ofInt 64 0
        rw [ofInt_zero, BitVec.add_zero])
      ⟨by
        show (st5.data.regs.getXReg .X19).toBitVec = m0.regs.X3.toBitVec + BitVec.ofInt 64 0
        rw [ofInt_zero, BitVec.add_zero]
        exact congrArg UInt64.toBitVec hx19_5, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b11_in_code (by simp [b11]) hp) run_b11 hwf11 hpc5 hm11
    fun st6 hm6 hpc6 ↦ .done _ ?_
  obtain ⟨hres, hw11, hz0, hz1, hov⟩ := after_eq run_b11 ▸ b11_facts
  obtain ⟨hsaved, hx30⟩ := Body.saved_of bd5 hm6 hwf11 (by simp [slots]) hres
  have hsame6 := same_of_region hm6 hwf11 (r := 1) rfl hw11
  have hr : constraintsW m0.regs.X0.toNat (row m0) =
      #[(row m0).getD 13 0 + (row m0).getD 5 0 * (row m0).getD 12 0,
        (row m0).getD 5 0 * ((row m0).getD 13 0 + 1)] := by
    rw [h4, constraintsW_jump]
  refine ⟨?_, ?_, ?_, ?_, hsaved⟩
  · simp only [PcOk] at hpc6
    rw [hpc6]
    simp only [retOf, hx30]
  · show (st6.data.regs.getXReg .X0).toBitVec.toNat = (constraintsW m0.regs.X0.toNat (row m0)).size
    rw [hr, hm6.regs .X0 _ rfl]
    rfl
  · show NativeRustcVm.EWsAt st6.data.dmem m0.regs.X3.toBitVec
      (constraintsW m0.regs.X0.toNat (row m0)).toList
    rw [hr]
    show NativeRustcVm.EWsAt _ _ ([_] ++ [_])
    rw [NativeRustcVm.ewsAt_append, NativeRustcVm.ewsAt_singleton, NativeRustcVm.ewsAt_singleton]
    refine ⟨fun i hi ↦ ?_, ?_⟩
    · have hi16 : i < 16 := by simpa [NativeRustcVm.length_ewBytes] using hi
      have h6 := Match.same_untouched hm6 (r := 1) (o := 0) (len := 16) rfl (by decide) hov i hi16
      rw [add_ofNat_zero] at h6
      rw [h6, Env.ofMachine_mem0, keep2 _ (Arrays.inRange_add (j := i) hro.2 (by omega))]
      exact hE0 i hi
    · rw [NativeRustcVm.ewAt_iff, ← hP2]
      have z0 := Match.wordAt_write hm6 (r := 1) (o := 16) (b := m0.regs.X3.toBitVec) (sz := 32)
        rfl (by decide) hz0
      have z1 := Match.wordAt_write hm6 (r := 1) (o := 24) (b := m0.regs.X3.toBitVec) (sz := 32)
        rfl (by decide) hz1
      refine ⟨z0, ?_⟩
      rw [NativeRustcVm.addr_add]
      exact z1
  · intro p hp'
    rw [hsame6 p fun h ↦ hp' (Or.inl h)]
    exact bd5.same p hp'

/-- **`constraints_w` meets its contract.** -/
theorem constraintsW_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.ConstraintsW.entryLabel) ConstraintsWPre ConstraintsWPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  obtain ⟨hwf, hm⟩ := entry_match (F := 48) hpre.1 (by decide) rfl
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.ConstraintsW.b0_length, NativeRustcVmArm.Vm.ConstraintsW.b0Length] at hpc1
  sym_simp at hpc1
  obtain ⟨hy, hn⟩ := pc_cond hpc1
  have hx0 : (m0.regs.getXReg .X0).toBitVec.toNat = m0.regs.X0.toNat := rfl
  by_cases h4 : m0.regs.X0.toNat = 4
  · have hc : ¬((!((Arrays.frameEnv m0 m0 48).regs .X0 == 4#64)) = true) := by
      simp only [Env.ofMachine_regs, Bool.not_eq_true', Bool.not_eq_false]
      exact (beq_iff (by decide)).mpr (hx0.trans h4)
    exact Eventually.bind (head hp hpre (hn hc) (by rw [after_eq run_b0]; exact hm1) hwf)
      fun s hs ↦ tail hp hmul hpre h4 hs
  · have hc : (!((Arrays.frameEnv m0 m0 48).regs .X0 == 4#64)) = true := by
      simp only [Env.ofMachine_regs, Bool.not_eq_eq_eq_not, Bool.not_true]
      exact Bool.eq_false_iff.mpr fun h ↦ h4 (hx0.symm.trans ((beq_iff (by decide)).mp h))
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) (exec_after run_b0 run_b5) hwf
      ((hy hc).trans (lbl_5 hp)) hm1 fun st2 hm2 hpc2 ↦ .done _ ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [PcOk] at hpc2
      rw [hpc2]
      simp only [retOf]
      rw [show st2.data.regs.X30 = m0.regs.X30 from Match.reg_eq (r := .X30) hm hm2 rfl rfl]
    · show (st2.data.regs.getXReg .X0).toBitVec.toNat = (constraintsW m0.regs.X0.toNat (row m0)).size
      rw [constraintsW_other h4, hm2.regs .X0 _ rfl]
      rfl
    · show NativeRustcVm.EWsAt _ _ (constraintsW m0.regs.X0.toNat (row m0)).toList
      rw [constraintsW_other h4]
      intro i hi
      simp at hi
    · intro p _
      rw [hm2.dmem_eq hwf (after_eq run_b5 ▸ b5_keeps).2]
      rfl
    · exact Match.saved hm hm2 hwf rfl (after_eq run_b5 ▸ b5_keeps).1

end

end NativeRustcVmArm.Layout.ConstraintsW
