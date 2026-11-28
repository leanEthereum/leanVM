module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.Evaluate.Names
public import NativeRustcVmArm.Layout.Evaluate.Exec
public import NativeRustcVmArm.Layout.FormBufAddTerm.Lemmas
public import NativeRustcVm.Arrays.Folds

/-!
# `evaluate`

The prologue (`b0`) saves X19-X27 and X30 in its 80-byte frame; no terms: `b14` and the epilogue
(`b15`) return `0`. Else (`b1`) the loop (`.L5`, `Regs i`: `i` terms summed in X23, X19, `sumAcc`)
reads term `i` (`b5`): its degree, coefficient and columns. Its product (`prodT`) is the
coefficient times the row's entry at each column, `0` past the row (`part`, `Mid i j`): at most
two columns, the first at `b6` (`b7` or `b10`), the second at `.L9` (`b12`, then `.L2` or `b13`,
and `.L3`), each by `EW::mul`. At `.L4` (`b4`) the product is added to the sum; past the last
term the epilogue returns the sum, the model's `FormW.evaluate` (`evaluate_eq`).
-/

namespace NativeRustcVmArm.Layout.Evaluate

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Evaluate
open NativeVm.Model NativeRustcVm.Layout NativeRustcVmArm.Layout.Forms
open NativeRustcVm.Transcript (off)
open NativeRustcVm (WordAt EWAt ewsOf addr_add_add addr_add_zero toNat_add_ofNat)
open NativeRustcVmArm.Arrays (Body calleeRegs inSlots keepsAll restores)

public section

/-! ## The model -/

/-- A term's product on a row: its coefficient times the row's entries at its columns. -/
abbrev gT (row : Array EW) (acc : EW) (c : Nat) : EW := acc * row.getD c 0

/-- The product after the first `j` columns. -/
def part (row : Array EW) (t : TermW) (j : Nat) : EW := (t.cols.toList.take j).foldl (gT row) t.coeff

/-- A term's product. -/
def prodT (row : Array EW) (t : TermW) : EW := t.cols.foldl (gT row) t.coeff

/-- The sum of the first `i` terms' products. -/
def sumAcc (f : FormW) (row : Array EW) (i : Nat) : EW :=
  ((f.toList.take i).map (prodT row)).foldl (· + ·) 0

theorem part_zero (row : Array EW) (t : TermW) : part row t 0 = t.coeff := by simp [part]

theorem part_succ (row : Array EW) (t : TermW) {j : Nat} (hj : j < t.cols.size) :
    part row t (j + 1) = part row t j * row.getD t.cols[j] 0 := by
  unfold part
  rw [List.take_succ_eq_append_getElem (by simpa using hj), List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, gT, Array.getElem_toList]

theorem part_size (row : Array EW) (t : TermW) : part row t t.cols.size = prodT row t := by
  unfold part prodT
  rw [← Array.foldl_toList, ← Array.length_toList, List.take_length]

theorem sumAcc_zero (f : FormW) (row : Array EW) : sumAcc f row 0 = 0 := by simp [sumAcc]

theorem sumAcc_succ (f : FormW) (row : Array EW) {i : Nat} (hi : i < f.size) :
    sumAcc f row (i + 1) = sumAcc f row i + prodT row f[i] := by
  unfold sumAcc
  rw [List.take_succ_eq_append_getElem (by simpa using hi), List.map_append, List.foldl_append]
  simp

theorem evaluate_eq (f : FormW) (row : Array EW) : f.evaluate row = sumAcc f row f.size := by
  unfold FormW.evaluate sumAcc
  show (f.map (prodT row)).foldl (· + ·) 0 = _
  rw [show f.size = f.toList.length from (Array.length_toList).symm, List.take_length,
    ← Array.foldl_toList, Array.toList_map]

theorem getD_of_lt {row : Array EW} {c : Nat} (h : c < row.size) : row.getD c 0 = row[c] := by
  simp [Array.getD, h]

theorem getD_of_ge {row : Array EW} {c : Nat} (h : ¬c < row.size) : row.getD c 0 = 0 := by
  simp [Array.getD, h]

/-! ## The state -/

/-- The terms. -/
abbrev tt (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
/-- The row. -/
abbrev rw0 (m0 : MachineData) : Array EW := slice m0 m0.regs.X2 m0.regs.X3
/-- The stack. -/
abbrev SS : Nat := evaluateStack

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 80 := by decide

theorem size_rw0 (m0 : MachineData) : (rw0 m0).size = m0.regs.X3.toNat := by simp [slice]

/-- **The loop's registers**: `i` terms summed. -/
structure Regs (f : FormW) (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  body : Body m0 80 SS slots 0 0 st
  lt : i < f.size
  x20 : st.regs.X20 = m0.regs.X3
  x21 : st.regs.X21 = m0.regs.X2
  x22 : st.regs.X22.toNat = f.size - i
  x24 : st.regs.X24.toBitVec = tt m0 + BitVec.ofNat 64 (40 * i + 32)
  x25 : st.regs.X25 = 8
  sum : (⟨st.regs.X23, st.regs.X19⟩ : EW) = sumAcc f (rw0 m0) i

/-- **Inside term `i`**: its first `j` columns multiplied. -/
structure Mid (f : FormW) (m0 : MachineData) (i j : Nat) (st : MachineData) : Prop
    extends Regs f m0 i st where
  x26 : st.regs.X26 = (f[i]'lt).cols.size.toUInt64
  x27 : st.regs.X27.toBitVec = tt m0 + BitVec.ofNat 64 (40 * i + 8)
  le : j ≤ (f[i]'lt).cols.size
  acc : (⟨st.regs.X0, st.regs.X1⟩ : EW) = part (rw0 m0) (f[i]'lt) j

theorem low7_sub' (r : XReg) (h : r ∈ low7) : r ∈ keepL.drop 2 := by
  simp only [low7, keepL, List.drop, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem low7_sub (r : XReg) (h : r ∈ low7) : r ∈ keepL :=
  List.mem_of_mem_drop (low7_sub' r h)

theorem Regs.mono {f : FormW} {m0 st st' : MachineData} {i : Nat} (h : Regs f m0 i st)
    (hb : Body m0 80 SS slots 0 0 st')
    (he : ∀ r ∈ low7, st'.regs.getXReg r = st.regs.getXReg r) : Regs f m0 i st' :=
  ⟨hb, h.lt, (he .X20 (by simp [low7])).trans h.x20, (he .X21 (by simp [low7])).trans h.x21,
    by rw [show st'.regs.X22 = st.regs.X22 from he .X22 (by simp [low7])]; exact h.x22,
    by rw [show st'.regs.X24 = st.regs.X24 from he .X24 (by simp [low7])]; exact h.x24,
    (he .X25 (by simp [low7])).trans h.x25,
    by rw [show st'.regs.X23 = st.regs.X23 from he .X23 (by simp [low7]),
      show st'.regs.X19 = st.regs.X19 from he .X19 (by simp [low7])]; exact h.sum⟩

theorem Mid.mono {f : FormW} {m0 st st' : MachineData} {i j : Nat} (h : Mid f m0 i j st)
    (hb : Body m0 80 SS slots 0 0 st')
    (he : ∀ r ∈ keepL, st'.regs.getXReg r = st.regs.getXReg r) : Mid f m0 i j st' :=
  ⟨h.toRegs.mono hb fun r hr ↦ he r (low7_sub r hr),
    (he .X26 (by simp [keepL])).trans h.x26,
    by rw [show st'.regs.X27 = st.regs.X27 from he .X27 (by simp [keepL])]; exact h.x27, h.le,
    by rw [show st'.regs.X0 = st.regs.X0 from he .X0 (by simp [keepL]),
      show st'.regs.X1 = st.regs.X1 from he .X1 (by simp [keepL])]; exact h.acc⟩

theorem keepL_callee : ∀ r ∈ keepL.drop 2, calleeSaved r = true := by decide

/-- **A call of `EW::mul`** in a term: the product by X2, X3. -/
theorem Mid.call {f : FormW} {m0 st st' : MachineData} {i j : Nat} (h : Mid f m0 i j st)
    (hS : StackOk m0 SS) (hj : j < (f[i]'h.lt).cols.size)
    (he : (⟨st.regs.X2, st.regs.X3⟩ : EW) = (rw0 m0).getD ((f[i]'h.lt).cols[j]) 0)
    (hpost : EWMulPost st st') : Mid f m0 i (j + 1) st' := by
  have hb := h.body.call hS (by decide) slots_le hpost
  have hk : ∀ r ∈ keepL.drop 2, st'.regs.getXReg r = st.regs.getXReg r :=
    fun r hr ↦ hpost.2.2.2.1 r (keepL_callee r hr)
  have hr : Regs f m0 i st' := h.toRegs.mono hb fun r hr ↦ hk r (low7_sub' r hr)
  refine ⟨hr, (hk .X26 (by simp [keepL])).trans h.x26,
    by rw [show st'.regs.X27 = st.regs.X27 from hk .X27 (by simp [keepL])]; exact h.x27,
    Nat.succ_le_of_lt hj, ?_⟩
  rw [part_succ _ _ hj, ← h.acc, ← he, hpost.1, hpost.2.1]
  rfl

/-- `evaluate`'s postcondition, reached. -/
abbrev Post (f : FormW) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ EvaluatePost f m0 st.data

/-- The facts of the precondition the blocks use. -/
structure Facts (f : FormW) (m0 : MachineData) : Prop where
  stack : StackOk m0 SS
  size : m0.regs.X1.toNat = f.size
  terms : TermsAt m0.dmem (tt m0) f
  tr : Readable m0 (tt m0) (40 * f.size)
  toff : OffStack m0 (tt m0) (40 * f.size) SS
  row : SliceOk m0 m0.regs.X2 m0.regs.X3 SS

theorem Facts.of_pre {f : FormW} {m0 : MachineData} (h : EvaluatePre f m0) : Facts f m0 := by
  obtain ⟨hS, hsz, hT, hr, ho, hrow⟩ := h
  have e : termBytes * m0.regs.X1.toNat = 40 * f.size := by rw [hsz]; rfl
  rw [e] at hr ho
  exact ⟨hS, hsz, hT, hr, ho, hrow⟩

/-- Term `i`, read in a body. -/
theorem Facts.term {f : FormW} {m0 st : MachineData} (hF : Facts f m0)
    (hb : Body m0 80 SS slots 0 0 st) {i : Nat} (hi : i < f.size) :
    TermWAt st.dmem (tt m0 + BitVec.ofNat 64 (40 * i)) f[i] := by
  have hs : Same m0.dmem st.dmem (tt m0) (40 * f.size) :=
    Arrays.same_of_apart hb.same hF.stack hF.tr.2 hF.toff (Arrays.apart_zero _ _) Arrays.noWrap_zero
  have := hF.terms i hi
  simp only [off, termBytes] at this
  exact TermWAt.of_same this (hs.sub (o := 40 * i) (k := termBytes) (by unfold termBytes; omega))

/-- Term `i`'s bytes from `o`, a region of a body's state. -/
theorem Facts.sub {f : FormW} {m0 st : MachineData} (hF : Facts f m0)
    (hb : Body m0 80 SS slots 0 0 st) {i o n : Nat} (hi : i < f.size) (hon : o + n ≤ 40) :
    NativeRustcVm.Mapped st.dmem (tt m0 + BitVec.ofNat 64 (40 * i + o)) n ∧
      NativeRustcVm.NoWrap (tt m0 + BitVec.ofNat 64 (40 * i + o)) n :=
  ⟨fun j hj ↦ by rw [addr_add_add]; exact hb.kept _ (hF.tr.1 _ (by omega)),
    NativeRustcVm.NoWrap.sub (a := tt m0) (n := 40 * f.size) hF.tr.2 (by omega)⟩

theorem ofNat_beq {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x == BitVec.ofNat 64 y) = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne]
    intro he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat] at this
    omega

theorem ofNat_ult {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x).ult (BitVec.ofNat 64 y) = decide (x < y) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem ptr_eval [Labels] (env : Env) (r : Nat) (o : Int) :
    (Sym.ptr r o).eval env = env.base r + BitVec.ofInt 64 o := by
  simp [Sym.eval]

theorem toBitVec_X3 (m0 : MachineData) : m0.regs.X3.toBitVec = BitVec.ofNat 64 m0.regs.X3.toNat := by
  simp

theorem ptr0 [Labels] (env : Env) (r : Nat) : (Sym.ptr r 0).eval env = env.base r := by
  simp [Sym.eval]

theorem ite_false {α : Sort _} {x a b : α} {c : Bool} {inst : Decidable (c = true)}
    (h : x = @ite α (c = true) inst a b) (hc : c = false) : x = b := by
  rw [h, Arrays.ite_bool, hc]; rfl

theorem shl4' (x : BitVec 64) (y : BitVec 64) (c : Nat) (hx : x.toNat = c) :
    y + x <<< 4 = y + BitVec.ofNat 64 (16 * c) + BitVec.ofInt 64 0 := by
  rw [Arrays.shl4, hx, Layout.ofInt_zero, BitVec.add_zero]

variable [Host] {k : Nat}

theorem pc_of {pc : Int64} {a b : Nat} (h : pc = Host.addrOf a) (e : a = b) : pc = Host.addrOf b :=
  e ▸ h

theorem hb7 (hp : Placed code k) : b7a.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Evaluate.b7Offset) ∧
    b7b.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Evaluate.b7Offset + 1) := by
  have h := b7_in_code.trans hp.1 (by simp [b7])
  rw [← List.take_append_drop 1 b7] at h
  exact h.append

theorem hb2 (hp : Placed code k) : b2a.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Evaluate.b2Offset) ∧
    b2b.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Evaluate.b2Offset + 2) := by
  have h := b2_in_code.trans hp.1 (by simp [b2])
  rw [← List.take_append_drop 2 b2] at h
  exact h.append

/-- At `.L4`: term `i`'s product in X0, X1. -/
abbrev AtL4 (f : FormW) (m0 : MachineData) (i : Nat) (st : MachineState) : Prop :=
  st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Evaluate.b4Offset) ∧ ∃ h : i < f.size, Mid f m0 i (f[i]'h).cols.size st.data

/-- **`.L3`**: the call of `EW::mul` by the second column's entry. -/
theorem l3 (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {f : FormW} {m0 : MachineData} (hF : Facts f m0) {i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Evaluate.b3Offset)) (hM : Mid f m0 i 1 st.data)
    (h2 : (f[i]'hM.lt).cols.size = 2)
    (he : (⟨st.data.regs.X2, st.data.regs.X3⟩ : EW) = (rw0 m0).getD ((f[i]'hM.lt).cols[1]) 0) :
    Eventually (step1 Host.exe) (AtL4 (k := k) f m0 i) st := by
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 (Env.wf_nil _) hpc (match_nil _)
    fun st1 hm1 hpc1 ↦ ?_
  have hb := hM.body.of_block (match_nil _) hm1 (Env.wf_nil _) rfl
    (Arrays.after_eq run_b3 ▸ b3_keeps)
  have hk := Arrays.regs_eq_of (match_nil _) hm1 keepL (Arrays.after_eq run_b3 ▸ b3_keepL)
  have hM1 := hM.mono hb hk
  have e2 : st1.data.regs.X2 = st.data.regs.X2 := Match.reg_eq (match_nil _) hm1 (r := .X2) rfl rfl
  have e3 : st1.data.regs.X3 = st.data.regs.X3 := Match.reg_eq (match_nil _) hm1 (r := .X3) rfl rfl
  refine call_then hpc1 hmul (hb.ewMulPre hF.stack (by decide) (by decide)) fun st2 hpc2 hpost ↦
    .done _ ⟨pc_of hpc2 rfl, hM.lt, ?_⟩
  have := hM1.call hF.stack (by omega) (by rw [e2, e3]; exact he) hpost
  rwa [h2]

/-- **The epilogue** `b15`: the sum in X23, X19 returned. -/
theorem finish (hp : Placed code k) {f : FormW} {m0 : MachineData} (hF : Facts f m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Evaluate.b15Offset))
    (hb : Body m0 80 SS slots 0 0 st.data)
    (hsum : (⟨st.data.regs.X23, st.data.regs.X19⟩ : EW) = f.evaluate (rw0 m0)) :
    Eventually (step1 Host.exe) (Post f m0) st := by
  obtain ⟨hwf, hm⟩ := hb.exit_match hF.stack (by decide) (by decide)
  refine exec_at (infix_of b15_in_code (by simp [b15]) hp) run_b15 hwf hpc hm
    fun st' hm' hpc' ↦ .done _ ?_
  obtain ⟨hsaved, hx30, hdm⟩ := hb.saved hm' hwf (List.mem_map.mpr ⟨(0, .X30), by simp [slots], rfl⟩)
    (Arrays.after_eq run_b15 ▸ b15_restores).1 (Arrays.after_eq run_b15 ▸ b15_restores).2
  have h0 : st'.data.regs.X0 = st.data.regs.X23 := UInt64.toBitVec_inj.mp (hm'.regs .X0 _ rfl)
  have h1 : st'.data.regs.X1 = st.data.regs.X19 := UInt64.toBitVec_inj.mp (hm'.regs .X1 _ rfl)
  refine ⟨?_, ?_, ?_, hsaved⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    simp only [retOf, hx30]
  · show (⟨st'.data.regs.X0, st'.data.regs.X1⟩ : EW) = _
    rw [h0, h1]; exact hsum
  · intro q hq; rw [hdm]; exact hb.same q hq

/-- **`.L4`**: the product added; past the last term, the epilogue. -/
theorem l4 (hp : Placed code k) {f : FormW} {m0 : MachineData} (hF : Facts f m0) {i : Nat}
    {st : MachineState} (hA : AtL4 (k := k) f m0 i st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post f m0 st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Evaluate.b5Offset) ∧ Regs f m0 (i + 1) st'.data)) st := by
  obtain ⟨hpc, hlt, hM⟩ := hA
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 (Env.wf_nil _) hpc (match_nil _)
    fun st1 hm1 hpc1 ↦ ?_
  have hb := hM.body.of_block (match_nil _) hm1 (Env.wf_nil _) rfl
    (Arrays.after_eq run_b4 ▸ b4_keeps)
  have hk := Arrays.regs_eq_of (match_nil _) hm1 _ (Arrays.after_eq run_b4 ▸ b4_keep)
  have h19 := hm1.regs .X19 _ rfl
  have h22 := hm1.regs .X22 _ rfl
  have h23 := hm1.regs .X23 _ rfl
  have h24 := hm1.regs .X24 _ rfl
  sym_simp at h19 h22 h23 h24
  have hsum : (⟨st1.data.regs.X23, st1.data.regs.X19⟩ : EW) = sumAcc f (rw0 m0) (i + 1) := by
    rw [sumAcc_succ _ _ hlt, ← hM.sum, ← part_size, ← hM.acc]
    show (⟨st1.data.regs.getXReg .X23, st1.data.regs.getXReg .X19⟩ : EW) = _
    rw [UInt64.toBitVec_inj.mp (h23.trans (by rw [← UInt64.toBitVec_xor])),
      UInt64.toBitVec_inj.mp (h19.trans (by rw [← UInt64.toBitVec_xor]))]
    show (⟨_, _⟩ : EW) = ⟨st.data.regs.X23 ^^^ st.data.regs.X0, st.data.regs.X19 ^^^ st.data.regs.X1⟩
    rw [UInt64.xor_comm st.data.regs.X23, UInt64.xor_comm st.data.regs.X19]
    rfl
  have hx22 : st.data.regs.X22.toNat = f.size - i := hM.x22
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  obtain ⟨hpa, hpb⟩ := Arrays.pc_cond hpc1
  by_cases hlast : i + 1 = f.size
  · have hc : ((Env.ofMachine st.data []).regs .X22 == 1#64) = true := by
      rw [beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      show st.data.regs.X22.toNat = 1
      omega
    refine Eventually.mono (finish hp hF ((hpa hc).trans (hp.label (j := NativeRustcVmArm.Vm.Evaluate.b15Offset) NativeRustcVmArm.Vm.Evaluate.label_12_at)) hb ?_)
      fun _ h ↦ Or.inl h
    rw [hsum, hlast, evaluate_eq]
  · have hc : ¬((Env.ofMachine st.data []).regs .X22 == 1#64) = true := by
      rw [beq_iff_eq]
      intro he
      have := congrArg BitVec.toNat he
      change st.data.regs.X22.toNat = 1 at this
      omega
    refine .done _ (Or.inr ⟨pc_of (hpb hc) rfl, hb, by omega,
      (hk .X20 (by simp)).trans hM.x20, (hk .X21 (by simp)).trans hM.x21, ?_, ?_,
      (hk .X25 (by simp)).trans hM.x25, hsum⟩)
    · show (st1.data.regs.getXReg .X22).toBitVec.toNat = _
      rw [h22, BitVec.toNat_sub_of_le (by
        rw [BitVec.le_def, BitVec.toNat_ofNat]; show 1 % 2 ^ 64 ≤ st.data.regs.X22.toNat; omega)]
      show st.data.regs.X22.toNat - 1 % 2 ^ 64 = _
      omega
    · show (st1.data.regs.getXReg .X24).toBitVec = _
      rw [h24]
      show st.data.regs.X24.toBitVec + BitVec.ofNat 64 40 = _
      rw [hM.x24, addr_add_add]
      exact congrArg (fun x ↦ tt m0 + BitVec.ofNat 64 x) (by omega)

omit [Host] in
theorem tbn (n : Nat) : n.toUInt64.toBitVec = BitVec.ofNat 64 n := rfl

omit [Host] in
/-- The row's length, as a bit vector. -/
theorem e20 {f : FormW} {m0 : MachineData} {i : Nat} {st : MachineData} (h : Regs f m0 i st)
    (rs : List (BitVec 64 × Nat)) :
    (Env.ofMachine st rs).regs .X20 = BitVec.ofNat 64 m0.regs.X3.toNat := by
  show (st.regs.getXReg .X20).toBitVec = _
  rw [show st.regs.getXReg .X20 = m0.regs.X3 from h.x20]
  simp

omit [Host] in
/-- The degree, as a bit vector. -/
theorem e26 {f : FormW} {m0 : MachineData} {i j : Nat} {st : MachineData} (h : Mid f m0 i j st)
    (rs : List (BitVec 64 × Nat)) :
    (Env.ofMachine st rs).regs .X26 = BitVec.ofNat 64 (f[i]'h.lt).cols.size := by
  show (st.regs.getXReg .X26).toBitVec = _
  rw [show st.regs.getXReg .X26 = _ from h.x26]
  rfl

omit [Host] in
/-- Column `j` of term `i`, loaded from the columns' region. -/
theorem col_load {f : FormW} {m0 st : MachineData} {i j : Nat} (hi : i < f.size)
    (hT : TermWAt st.dmem (tt m0 + BitVec.ofNat 64 (40 * i)) f[i]) (hj : j < f[i].cols.size)
    {rs : List (BitVec 64 × Nat)} :
    (Env.ofMachine st ((tt m0 + BitVec.ofNat 64 (40 * i + 8), 16) :: rs)).load 0 (8 * j) 8 =
      BitVec.ofNat 64 f[i].cols[j] := by
  refine load_word ?_
  have := hT.cols j hj
  simp only [off] at this
  show WordAt st.dmem (tt m0 + BitVec.ofNat 64 (40 * i + 8) + BitVec.ofNat 64 (8 * j)) _
  rw [addr_add_add] at this ⊢
  rw [show 40 * i + 8 + 8 * j = 40 * i + (8 + 8 * j) by omega]
  exact this

omit [Host] in
/-- The row's element `c`, as `load_step` gives it. -/
theorem elem_eq {m0 : MachineData} {c : Nat} (h : c < m0.regs.X3.toNat) {x : EW}
    (hx : x = (ewsOf m0.dmem m0.regs.X2.toBitVec m0.regs.X3.toNat)[c]'(by simpa using h)) :
    x = (rw0 m0).getD c 0 := by
  rw [getD_of_lt (by rw [size_rw0]; exact h), hx]
  simp [slice]

/-- **`.L9`**: the second column. -/
theorem col1 (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {f : FormW} {m0 : MachineData} (hF : Facts f m0) {i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Evaluate.b12Offset)) (hM : Mid f m0 i 1 st.data)
    (h2 : (f[i]'hM.lt).cols.size = 2) :
    Eventually (step1 Host.exe) (AtL4 (k := k) f m0 i) st := by
  have hlt := hM.lt
  have hT := hF.term hM.body hlt
  obtain ⟨hmB, hnB⟩ := hF.sub hM.body hlt (o := 8) (n := 16) (by omega)
  let env := Env.ofMachine st.data [(tt m0 + BitVec.ofNat 64 (40 * i + 8), 16)]
  have hwf : env.WF := Arrays.wf_one hmB hnB
  have hm : Match env colS st.data := match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
    ⟨by show _ = (Sym.ptr 0 0).eval env; rw [ptr0]; exact hM.x27, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b12_in_code (by simp [b12]) hp) run_b12 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hb1 := hM.body.of_block hm hm1 hwf rfl (Arrays.after_eq run_b12 ▸ b12_keeps)
  have hM1 := hM.mono hb1 (Arrays.regs_eq_of hm hm1 keepL (Arrays.after_eq run_b12 ▸ b12_keepL))
  have hj1 : 1 < f[i].cols.size := by omega
  have hclt := hT.cols_lt 1 hj1
  have l8 : env.load 0 8 8 = BitVec.ofNat 64 f[i].cols[1] := col_load hlt hT hj1
  have hx8 : (st1.data.regs.getXReg .X8).toBitVec = BitVec.ofNat 64 f[i].cols[1] := by
    have := hm1.regs .X8 _ rfl
    sym_simp at this
    rw [this, l8]
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  rw [l8, e20 hM.toRegs, ofNat_ult hclt m0.regs.X3.toNat_lt] at hpc1
  obtain ⟨hpa, hpb⟩ := Arrays.pc_cond hpc1
  by_cases hin : f[i].cols[1] < m0.regs.X3.toNat
  · -- `.L2`: the row's entry
    have hpc2 := (hpa (by simpa using hin)).trans (hp.label (j := NativeRustcVmArm.Vm.Evaluate.b2Offset) NativeRustcVmArm.Vm.Evaluate.label_2_at)
    refine exec_at (hb2 hp).1 run_b2a (Env.wf_nil _) hpc2 (match_nil _) fun st2 hm2 hpc3 ↦ ?_
    have hb2' := hb1.of_block (match_nil _) hm2 (Env.wf_nil _) rfl
      (Arrays.after_eq run_b2a ▸ b2a_keeps)
    have hM2 := hM1.mono hb2' (Arrays.regs_eq_of (match_nil _) hm2 keepL
      (Arrays.after_eq run_b2a ▸ b2a_keepL))
    have h8 := hm2.regs .X8 _ rfl
    sym_simp at h8
    simp only [PcOk, show b2a.length = 2 from rfl] at hpc3
    have hreg : (st2.data.regs.getXReg .X8).toBitVec =
        m0.regs.X2.toBitVec + BitVec.ofNat 64 (16 * f[i].cols[1]) + BitVec.ofInt 64 0 := by
      rw [h8, Env.ofMachine_regs, Env.ofMachine_regs,
        show st1.data.regs.getXReg .X21 = m0.regs.X2 from hM1.x21]
      exact shl4' _ _ _ (by rw [hx8, BitVec.toNat_ofNat]; omega)
    refine Arrays.load_step (lo := .X2) (hi' := .X3) (hb2 hp).2 run_b2b rfl rfl (Arrays.after_eq run_b2b ▸ b2b_keeps) keepL
      (Arrays.after_eq run_b2b ▸ b2b_keepL) hb2' hF.stack hF.row.1 hF.row.2
      (Arrays.apart_zero _ _) Arrays.noWrap_zero hin hpc3 hreg fun st3 hm3 hpc4 hb3 helem hk3 ↦ ?_
    simp only [PcOk, show b2b.length = 1 from rfl] at hpc4
    exact l3 hp hmul hF (pc_of hpc4 rfl) (hM2.mono hb3 hk3) h2 (elem_eq hin helem)
  · -- `b13`: past the row, `0`
    have hpc2 := pc_of (hpb (by simpa using hin)) rfl
    refine exec_at (infix_of b13_in_code (by simp [b13]) hp) run_b13 (Env.wf_nil _) hpc2
      (match_nil _) fun st2 hm2 hpc3 ↦ ?_
    have hb2' := hb1.of_block (match_nil _) hm2 (Env.wf_nil _) rfl
      (Arrays.after_eq run_b13 ▸ b13_keeps)
    have hM2 := hM1.mono hb2' (Arrays.regs_eq_of (match_nil _) hm2 keepL
      (Arrays.after_eq run_b13 ▸ b13_keepL))
    simp only [PcOk] at hpc3
    have e2 : st2.data.regs.X2 = 0 := UInt64.toBitVec_inj.mp ((hm2.regs .X2 _ rfl).trans rfl)
    have e3 : st2.data.regs.X3 = 0 := UInt64.toBitVec_inj.mp ((hm2.regs .X3 _ rfl).trans rfl)
    refine l3 hp hmul hF (hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.Evaluate.b3Offset) NativeRustcVmArm.Vm.Evaluate.label_3_at)) hM2 h2 ?_
    rw [getD_of_ge (by rw [size_rw0]; exact hin), e2, e3]
    rfl


/-- After the first column (`b8` or `b11`): one column, `.L4`; two, on (`kelse`). -/
theorem after0 {f : FormW} {m0 : MachineData} {i : Nat} {st : MachineState} {kb kelse : Nat}
    {b : List Directive} {S' : SState} {x : Exit} (hk : b.IsInfixAt Host.prog kb)
    (hx : exec b regsS = some (S', x)) (hkeeps : keepsAll regsS S' keptRegs = true)
    (hkeep : keepR regsS S' keepL = true)
    (hcont : ∀ st', Match (Env.ofMachine st.data []) S' st'.data →
      PcOk (Env.ofMachine st.data []) x (Host.addrOf (kb + b.length)) st' →
      (st.data.regs.X26 = 1 → st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Evaluate.b4Offset)) ∧
      (st.data.regs.X26 ≠ 1 → st'.pc = Host.addrOf kelse))
    (hpc : st.pc = Host.addrOf kb) (hM : Mid f m0 i 1 st.data)
    (h12 : (f[i]'hM.lt).cols.size = 1 ∨ (f[i]'hM.lt).cols.size = 2)
    (helse : ∀ st', st'.pc = Host.addrOf kelse → Mid f m0 i 1 st'.data →
      (f[i]'hM.lt).cols.size = 2 → Eventually (step1 Host.exe) (AtL4 (k := k) f m0 i) st') :
    Eventually (step1 Host.exe) (AtL4 (k := k) f m0 i) st := by
  refine exec_at hk hx (Env.wf_nil _) hpc (match_nil _) fun st1 hm1 hpc1 ↦ ?_
  have hb := hM.body.of_block (match_nil _) hm1 (Env.wf_nil _) rfl hkeeps
  have hM1 := hM.mono hb (Arrays.regs_eq_of (match_nil _) hm1 keepL hkeep)
  obtain ⟨ha, hb'⟩ := hcont st1 hm1 hpc1
  rcases h12 with h1 | h2
  · refine .done _ ⟨ha (by rw [hM.x26, h1]; rfl), hM.lt, ?_⟩
    rw [h1]; exact hM1
  · refine helse st1 (hb' ?_) hM1 h2
    rw [hM.x26, h2]
    decide

/-- The test `X26 = 1` (`cmp x26, #1; b.eq .L4`). -/
theorem test1 (hp : Placed code k) {st st' : MachineState} {nx : Int64}
    {inst : Decidable (((Env.ofMachine st.data []).regs .X26 == 1#64) = true)}
    (hpc : st'.pc = @_root_.ite _ (((Env.ofMachine st.data []).regs .X26 == 1#64) = true) inst
      (Labels.label NativeRustcVmArm.Vm.Evaluate.label_4) nx) :
    (st.data.regs.X26 = 1 → st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Evaluate.b4Offset)) ∧
      (st.data.regs.X26 ≠ 1 → st'.pc = nx) := by
  obtain ⟨ha, hb⟩ := Arrays.pc_cond hpc
  refine ⟨fun h ↦ (ha ?_).trans (hp.label (j := NativeRustcVmArm.Vm.Evaluate.b4Offset) NativeRustcVmArm.Vm.Evaluate.label_4_at), fun h ↦ hb fun h' ↦ h ?_⟩
  · rw [beq_iff_eq]; exact congrArg UInt64.toBitVec h
  · exact UInt64.toBitVec_inj.mp (beq_iff_eq.mp h')

/-- **`b9`**: on to `.L9`. -/
theorem to9 (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {f : FormW} {m0 : MachineData} (hF : Facts f m0) {i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Evaluate.b9Offset)) (hM : Mid f m0 i 1 st.data)
    (h2 : (f[i]'hM.lt).cols.size = 2) :
    Eventually (step1 Host.exe) (AtL4 (k := k) f m0 i) st := by
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) run_b9 (Env.wf_nil _) hpc (match_nil _)
    fun st1 hm1 hpc1 ↦ ?_
  have hb := hM.body.of_block (match_nil _) hm1 (Env.wf_nil _) rfl
    (Arrays.after_eq run_b9 ▸ b9_keeps)
  have hM1 := hM.mono hb (Arrays.regs_eq_of (match_nil _) hm1 keepL
    (Arrays.after_eq run_b9 ▸ b9_keepL))
  simp only [PcOk] at hpc1
  exact col1 hp hmul hF (hpc1.trans (hp.label (j := NativeRustcVmArm.Vm.Evaluate.b12Offset) NativeRustcVmArm.Vm.Evaluate.label_9_at)) hM1 h2

/-- **`b6`**: the first column. -/
theorem col0 (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {f : FormW} {m0 : MachineData} (hF : Facts f m0) {i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Evaluate.b6Offset)) (hM : Mid f m0 i 0 st.data)
    (h12 : (f[i]'hM.lt).cols.size = 1 ∨ (f[i]'hM.lt).cols.size = 2) :
    Eventually (step1 Host.exe) (AtL4 (k := k) f m0 i) st := by
  have hlt := hM.lt
  have hT := hF.term hM.body hlt
  obtain ⟨hmB, hnB⟩ := hF.sub hM.body hlt (o := 8) (n := 16) (by omega)
  let env := Env.ofMachine st.data [(tt m0 + BitVec.ofNat 64 (40 * i + 8), 16)]
  have hwf : env.WF := Arrays.wf_one hmB hnB
  have hm : Match env colS st.data := match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
    ⟨by show _ = (Sym.ptr 0 0).eval env; rw [ptr0]; exact hM.x27, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hb1 := hM.body.of_block hm hm1 hwf rfl (Arrays.after_eq run_b6 ▸ b6_keeps)
  have hM1 := hM.mono hb1 (Arrays.regs_eq_of hm hm1 keepL (Arrays.after_eq run_b6 ▸ b6_keepL))
  have hj0 : 0 < f[i].cols.size := by omega
  have hclt := hT.cols_lt 0 hj0
  have l0 : env.load 0 0 8 = BitVec.ofNat 64 f[i].cols[0] := col_load (j := 0) hlt hT hj0
  have hx8 : (st1.data.regs.getXReg .X8).toBitVec = BitVec.ofNat 64 f[i].cols[0] := by
    have := hm1.regs .X8 _ rfl
    sym_simp at this
    rw [this, l0]
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  rw [l0, e20 hM.toRegs, ofNat_ult hclt m0.regs.X3.toNat_lt] at hpc1
  obtain ⟨hpa, hpb⟩ := Arrays.pc_cond hpc1
  by_cases hin : f[i].cols[0] < m0.regs.X3.toNat
  · -- `b7`: the row's entry, then `EW::mul`
    have hpc2 := pc_of (hpb (by simpa using hin)) rfl
    refine exec_at (hb7 hp).1 run_b7a (Env.wf_nil _) hpc2 (match_nil _) fun st2 hm2 hpc3 ↦ ?_
    have hb2' := hb1.of_block (match_nil _) hm2 (Env.wf_nil _) rfl
      (Arrays.after_eq run_b7a ▸ b7a_keeps)
    have hM2 := hM1.mono hb2' (Arrays.regs_eq_of (match_nil _) hm2 keepL
      (Arrays.after_eq run_b7a ▸ b7a_keepL))
    have h8 := hm2.regs .X8 _ rfl
    sym_simp at h8
    simp only [PcOk, show b7a.length = 1 from rfl] at hpc3
    have hreg : (st2.data.regs.getXReg .X8).toBitVec =
        m0.regs.X2.toBitVec + BitVec.ofNat 64 (16 * f[i].cols[0]) + BitVec.ofInt 64 0 := by
      rw [h8, Env.ofMachine_regs, Env.ofMachine_regs,
        show st1.data.regs.getXReg .X21 = m0.regs.X2 from hM1.x21]
      exact shl4' _ _ _ (by rw [hx8, BitVec.toNat_ofNat]; omega)
    refine Arrays.load_step (lo := .X2) (hi' := .X3) (hb7 hp).2 run_b7b rfl rfl
      (Arrays.after_eq run_b7b ▸ b7b_keeps) keepL (Arrays.after_eq run_b7b ▸ b7b_keepL) hb2'
      hF.stack hF.row.1 hF.row.2 (Arrays.apart_zero _ _) Arrays.noWrap_zero hin hpc3 hreg
      fun st3 hm3 hpc4 hb3 helem hk3 ↦ ?_
    have hM3 := hM2.mono hb3 hk3
    refine call_then hpc4 hmul (hb3.ewMulPre hF.stack (by decide) (by decide))
      fun st4 hpc5 hpost ↦ ?_
    have hM4 := hM3.call hF.stack hj0 (elem_eq hin helem) hpost
    refine after0 (kelse := k + NativeRustcVmArm.Vm.Evaluate.b9Offset) (infix_of b8_in_code (by simp [b8]) hp) run_b8
      (Arrays.after_eq run_b8 ▸ b8_keeps) (Arrays.after_eq run_b8 ▸ b8_keepL)
      (fun st5 _ hpc6 ↦ ?_) (pc_of hpc5 rfl) hM4 h12
      fun st5 hpc6 hM5 h2 ↦ to9 hp hmul hF hpc6 hM5 h2
    simp only [PcOk] at hpc6
    sym_simp at hpc6
    exact test1 hp (hpc6.trans (by rfl))
  · -- `.L8`: past the row, `0`
    have hpc2 := (hpa (by simpa using hin)).trans (hp.label (j := NativeRustcVmArm.Vm.Evaluate.b10Offset) NativeRustcVmArm.Vm.Evaluate.label_8_at)
    refine exec_at (infix_of b10_in_code (by simp [b10]) hp) run_b10 (Env.wf_nil _) hpc2
      (match_nil _) fun st2 hm2 hpc3 ↦ ?_
    have hb2' := hb1.of_block (match_nil _) hm2 (Env.wf_nil _) rfl
      (Arrays.after_eq run_b10 ▸ b10_keeps)
    have hM2 := hM1.mono hb2' (Arrays.regs_eq_of (match_nil _) hm2 keepL
      (Arrays.after_eq run_b10 ▸ b10_keepL))
    have e2 : st2.data.regs.X2 = 0 := UInt64.toBitVec_inj.mp ((hm2.regs .X2 _ rfl).trans rfl)
    have e3 : st2.data.regs.X3 = 0 := UInt64.toBitVec_inj.mp ((hm2.regs .X3 _ rfl).trans rfl)
    refine call_then hpc3 hmul (hb2'.ewMulPre hF.stack (by decide) (by decide))
      fun st4 hpc5 hpost ↦ ?_
    have hM4 := hM2.call hF.stack hj0 (by
      rw [getD_of_ge (by rw [size_rw0]; exact hin), e2, e3]; rfl) hpost
    refine after0 (kelse := k + NativeRustcVmArm.Vm.Evaluate.b12Offset) (infix_of b11_in_code (by simp [b11]) hp) run_b11
      (Arrays.after_eq run_b11 ▸ b11_keeps) (Arrays.after_eq run_b11 ▸ b11_keepL)
      (fun st5 _ hpc6 ↦ ?_) (pc_of hpc5 rfl) hM4 h12
      fun st5 hpc6 hM5 h2 ↦ col1 hp hmul hF hpc6 hM5 h2
    simp only [PcOk] at hpc6
    sym_simp at hpc6
    exact test1 hp (hpc6.trans (by rfl))

/-- **`.L5`**: term `i`'s degree, coefficient and columns (`b5`); no columns: `.L4`. -/
theorem head (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {f : FormW} {m0 : MachineData} (hF : Facts f m0) {i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Evaluate.b5Offset)) (hR : Regs f m0 i st.data) :
    Eventually (step1 Host.exe) (AtL4 (k := k) f m0 i) st := by
  have hlt := hR.lt
  have hT := hF.term hR.body hlt
  have hd2 := hT.degree_le
  obtain ⟨hmB, hnB⟩ := hF.sub hR.body hlt (o := 0) (n := 40) (by omega)
  rw [Nat.add_zero] at hmB hnB
  let env := Env.ofMachine st.data [(tt m0 + BitVec.ofNat 64 (40 * i), 40)]
  have hwf : env.WF := Arrays.wf_one hmB hnB
  have hm : Match env termS st.data := match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
    ⟨by
      show st.data.regs.X24.toBitVec = (Sym.ptr 0 32).eval env
      rw [ptr_eval, hR.x24, show BitVec.ofInt 64 32 = BitVec.ofNat 64 32 from rfl]
      exact (addr_add_add _ _ _).symm, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hb1 := hR.body.of_block hm hm1 hwf rfl (Arrays.after_eq run_b5 ▸ b5_keeps)
  have hR1 := hR.mono hb1 (Arrays.regs_eq_of hm hm1 low7 (Arrays.after_eq run_b5 ▸ b5_low7))
  have ld : ∀ {o : Nat} {w : UInt64}, WordAt st.data.dmem (tt m0 + BitVec.ofNat 64 (40 * i) +
      BitVec.ofNat 64 o) w → env.load 0 o 8 = w.toBitVec := fun h ↦ load_word h
  have l0 : env.load 0 0 8 = BitVec.ofNat 64 f[i].cols.size := ld (by rw [addr_add_zero]; exact hT.degree)
  obtain ⟨hc0, hc1⟩ := NativeRustcVm.ewAt_iff.mp hT.coeff
  have l24 : env.load 0 24 8 = f[i].coeff.c0.toBitVec := ld (by simpa [off] using hc0)
  have l32 : env.load 0 32 8 = f[i].coeff.c1.toBitVec := ld (by
    simp only [off] at hc1; rw [addr_add_add _ 24 8] at hc1; exact hc1)
  have h26 := hm1.regs .X26 _ rfl
  have h27 := hm1.regs .X27 _ rfl
  have h0 := hm1.regs .X0 _ rfl
  have h1 := hm1.regs .X1 _ rfl
  sym_simp at h26 h27 h0 h1
  rw [l0] at h26 h27
  rw [l24] at h0
  rw [l32] at h1
  have h27' := ite_false h27 (by
    rcases (show f[i].cols.size = 0 ∨ f[i].cols.size = 1 ∨ f[i].cols.size = 2 by omega)
      with h | h | h <;> rw [h] <;> decide)
  have hM : Mid f m0 i 0 st1.data := by
    refine ⟨hR1, UInt64.toBitVec_inj.mp h26, ?_, Nat.zero_le _, ?_⟩
    · show (st1.data.regs.getXReg .X27).toBitVec = _
      rw [h27', show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl]
      exact addr_add_add _ _ _
    · rw [part_zero]
      show (⟨st1.data.regs.getXReg .X0, st1.data.regs.getXReg .X1⟩ : EW) = _
      rw [UInt64.toBitVec_inj.mp h0, UInt64.toBitVec_inj.mp h1]
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  rw [l0] at hpc1
  obtain ⟨hpa, hpb⟩ := Arrays.pc_cond hpc1
  by_cases hz : f[i].cols.size = 0
  · refine .done _ ⟨(hpa ?_).trans (hp.label (j := NativeRustcVmArm.Vm.Evaluate.b4Offset) NativeRustcVmArm.Vm.Evaluate.label_4_at), hlt, ?_⟩
    · rw [hz]; decide
    · rw [hz]; exact hM
  · refine col0 hp hmul hF (pc_of (hpb ?_) rfl) hM (by omega)
    rcases (show f[i].cols.size = 1 ∨ f[i].cols.size = 2 by omega) with h | h <;> rw [h] <;> decide

/-- **`evaluate`'s contract.** -/
theorem evaluate_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {f : FormW} :
    Spec (Labels.label NativeRustcVmArm.Vm.Evaluate.entryLabel) (EvaluatePre f) (EvaluatePost f) := by
  intro m0 hpre
  have hF := Facts.of_pre hpre
  have hS := hF.stack
  have hsz := hF.size
  have hX1 := m0.regs.X1.toNat_lt
  obtain ⟨hwf, hm⟩ := Arrays.entry_match hS (F := 80) (by decide) (by decide)
  rw [show Labels.label NativeRustcVmArm.Vm.Evaluate.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.Evaluate.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.Evaluate.entryOffset) NativeRustcVmArm.Vm.Evaluate.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf hm fun st0 hm0 hpc0 ↦ ?_
  simp only [PcOk] at hpc0
  sym_simp at hpc0
  have e1 : (Arrays.frameEnv m0 m0 80).regs .X1 = BitVec.ofNat 64 f.size := by
    apply BitVec.eq_of_toNat_eq
    show m0.regs.X1.toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hsz
  rw [e1, ofNat_beq (by omega) (by omega)] at hpc0
  obtain ⟨hpa, hpb⟩ := Arrays.pc_cond hpc0
  by_cases hz : f.size = 0
  · -- no terms: `b14`, then the epilogue
    have hpc1 := (hpa (by simpa using hz)).trans (hp.label (j := NativeRustcVmArm.Vm.Evaluate.b14Offset) NativeRustcVmArm.Vm.Evaluate.label_11_at)
    refine exec_at (infix_of b14_in_code (by simp [b14]) hp) (Arrays.exec_after run_b0 run_b14) hwf
      hpc1 hm0 fun st1 hm1 hpc2 ↦ ?_
    obtain ⟨hw, hmem, hregs⟩ := Arrays.after_eq run_b14 ▸ b14_frame
    simp only [PcOk] at hpc2
    refine finish hp hF (pc_of hpc2 rfl) (Arrays.Body.of_entry hS (by decide) hm1 rfl hw hregs hmem) ?_
    rw [evaluate_eq, hz, sumAcc_zero]
    show (⟨st1.data.regs.getXReg .X23, st1.data.regs.getXReg .X19⟩ : EW) = ⟨0, 0⟩
    rw [UInt64.toBitVec_inj.mp ((hm1.regs .X23 _ rfl).trans rfl),
      UInt64.toBitVec_inj.mp ((hm1.regs .X19 _ rfl).trans rfl)]
    rfl
  · -- the prologue, then the loop
    have hpc1 := pc_of (hpb (by simpa using hz)) rfl
    refine exec_at (infix_of b1_in_code (by simp [b1]) hp) (Arrays.exec_after run_b0 run_b1) hwf
      hpc1 hm0 fun st1 hm1 hpc2 ↦ ?_
    obtain ⟨hw, hmem, hregs⟩ := Arrays.after_eq run_b1 ▸ b1_frame
    simp only [PcOk] at hpc2
    have hR : Regs f m0 0 st1.data := by
      have h22 := hm1.regs .X22 _ rfl
      have h24 := hm1.regs .X24 _ rfl
      sym_simp at h22 h24
      refine ⟨Arrays.Body.of_entry hS (by decide) hm1 rfl hw hregs hmem, by omega,
        UInt64.toBitVec_inj.mp (hm1.regs .X20 _ rfl), UInt64.toBitVec_inj.mp (hm1.regs .X21 _ rfl),
        ?_, ?_, UInt64.toBitVec_inj.mp ((hm1.regs .X25 _ rfl).trans rfl), ?_⟩
      · show (st1.data.regs.getXReg .X22).toBitVec.toNat = _
        rw [h22]
        show m0.regs.X1.toNat = _
        omega
      · show (st1.data.regs.getXReg .X24).toBitVec = _
        rw [h24]
        rfl
      · rw [sumAcc_zero]
        show (⟨st1.data.regs.getXReg .X23, st1.data.regs.getXReg .X19⟩ : EW) = ⟨0, 0⟩
        rw [UInt64.toBitVec_inj.mp ((hm1.regs .X23 _ rfl).trans rfl),
          UInt64.toBitVec_inj.mp ((hm1.regs .X19 _ rfl).trans rfl)]
        rfl
    refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Evaluate.b5Offset) ∧ ∃ i, f.size - i = n ∧
      Regs f m0 i st.data) (fun n st ⟨hpc, i, hn, hR⟩ ↦ ?_)
      ⟨hpc2.trans (hp.label (j := NativeRustcVmArm.Vm.Evaluate.b5Offset) NativeRustcVmArm.Vm.Evaluate.label_5_at), 0, rfl, hR⟩
    refine Eventually.bind (head hp hmul hF hpc hR) fun st' hA ↦ ?_
    refine Eventually.mono (l4 hp hF hA) fun st'' h ↦ ?_
    rcases h with h | ⟨hpc', hR'⟩
    · exact Or.inl h
    · exact Or.inr ⟨f.size - (i + 1), by have := hR.lt; omega, hpc', i + 1, rfl, hR'⟩

end

end NativeRustcVmArm.Layout.Evaluate
