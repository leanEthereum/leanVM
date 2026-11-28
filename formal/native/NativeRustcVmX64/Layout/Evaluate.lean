module

public import NativeRustcVmX64.Layout.Evaluate.Exec
public import NativeRustcVmX64.Layout.Forms.Lemmas
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.Evaluate.Names

/-!
# `evaluate` on x86-64

The prologue (`b0`) pushes RBP, R15-R12, RBX, keeps the terms' address and count in its frame
(offsets `16`, `24`, `Core`); no terms: `b12` and the epilogue (`b13`) return `0`. Else (`b1`)
the outer loop (`.L3`, `Outer i`: `i` terms summed in RAX, RDX, `sumAcc`) stores the sum
(offsets `32`, `40`, `Stored`) and reads term `i` (`b4`): its degree (R13), coefficient (RAX, RDX)
and columns' address (RBX). Degree `0`: on to `.L9` (`AtL9`). Else the inner loop (`.L5`,
`Inner i j`) multiplies by the row's entry at column `j`, `0` past the row (`b10`, `b7` or `b11`,
`EW::mul` at `b8`, `b9`). At `.L9` (`b3`) the product is added to the sum; past the last term the
epilogue returns the sum, the model's `FormW.evaluate` (`evaluate_eq`).
-/

namespace NativeRustcVmX64.Layout.Evaluate

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Evaluate NativeVm.Model
open NativeRustcVm.Layout NativeRustcVmX64.Layout.Forms
open NativeRustcVmX64.Field (frameEnv frame_wf match_frame midS)
open NativeRustcVmX64.Arrays (Body after after_eq exec_after freeRegs keepsAll keepsRegs restores
  pc_cond stackOk_mono regs_eq_of)
open NativeRustcVmX64.Transcript (infix_of)
open NativeRustcVm.Transcript (off off_off)
open NativeRustcVm (WordAt EWAt ewsOf ewOf)

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

theorem getD_of_ge {row : Array EW} {c : Nat} (h : ¬c < row.size) : row.getD c 0 = 0 := by
  simp [Array.getD, h]

theorem ewArg_zero : ewArg 0#64 0#64 = 0 := rfl

theorem ewArg_toBitVec (x : EW) : ewArg x.c0.toBitVec x.c1.toBitVec = x := rfl

theorem c0_of {a b : BitVec 64} {x : EW} (h : ewArg a b = x) : x.c0 = UInt64.ofBitVec a := by
  rw [← h]; rfl

theorem c1_of {a b : BitVec 64} {x : EW} (h : ewArg a b = x) : x.c1 = UInt64.ofBitVec b := by
  rw [← h]; rfl

/-- `b4`'s branch on the degree `d ≤ 2`: taken at `0`. -/
theorem deg_cond (d : Nat) (hd : d ≤ 2) :
    CmpOp.apply .ult .W64 (BinOp.apply .sub .W64 (BitVec.ofNat 64 d) (BitVec.ofNat 64 3))
      (BitVec.ofNat 64 18446744073709551614) = decide (d = 0) := by
  interval_cases d <;> decide

/-- `b4`'s columns' address for a degree `d ≤ 2`. -/
theorem deg_lt3 (d : Nat) (hd : d ≤ 2) :
    CmpOp.apply .ult .W64 (BitVec.ofNat 64 d) (BitVec.ofNat 64 3) = true := by
  interval_cases d <;> decide

/-- `test x, x` for `je`: `x = 0`. -/
theorem test_self (x : BitVec 64) :
    CmpOp.apply .eq .W64 (BinOp.apply .and .W64 x x) (BitVec.ofNat 64 0) = decide (x.toNat = 0) := by
  simp only [CmpOp.apply, BinOp.apply, low_W64, ext_W64, BitVec.and_self]
  by_cases h : x.toNat = 0
  · have : x = 0#64 := BitVec.eq_of_toNat_eq h
    simp [this]
  · have : x ≠ BitVec.ofNat 64 0 := fun e ↦ h (by rw [e]; rfl)
    simp [this, h]

theorem beq_ofNat {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x == BitVec.ofNat 64 y) = decide (x = y) :=
  NativeRustcX64.Sym.ofNat_beq hx hy

/-! ## The state -/

/-- The terms. -/
abbrev tt (m0 : MachineData) : BitVec 64 := reg m0 .rdi
/-- The row. -/
abbrev row (m0 : MachineData) : Array EW := slice m0 (reg m0 .rdx) (reg m0 .rcx)
/-- The stack. -/
abbrev SS : Nat := evaluateStack
/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := stackBelow m0 96

theorem size_row (m0 : MachineData) : (row m0).size = (reg m0 .rcx).toNat := by simp [slice]

/-- The frame's bytes `lo ≤ j < hi` the same. -/
def FSame (m0 st st' : MachineData) (lo hi : Nat) : Prop :=
  ∀ j, lo ≤ j → j < hi →
    st'.dmem.get? (fb m0 + BitVec.ofNat 64 j) = st.dmem.get? (fb m0 + BitVec.ofNat 64 j)

theorem FSame.trans {m0 a b c : MachineData} {lo hi : Nat} (h : FSame m0 a b lo hi)
    (h' : FSame m0 b c lo hi) : FSame m0 a c lo hi :=
  fun j h1 h2 ↦ (h' j h1 h2).trans (h j h1 h2)

theorem FSame.mono {m0 a b : MachineData} {lo hi lo' hi' : Nat} (h : FSame m0 a b lo hi)
    (h1 : lo ≤ lo') (h2 : hi' ≤ hi) : FSame m0 a b lo' hi' :=
  fun j h3 h4 ↦ h j (by omega) (by omega)

theorem FSame.of_eq {m0 a b : MachineData} {lo hi : Nat} (h : b.dmem = a.dmem) :
    FSame m0 a b lo hi := fun _ _ _ ↦ by rw [h]

theorem FSame.word {m0 a b : MachineData} {lo hi o : Nat} {w : UInt64} (h : FSame m0 a b lo hi)
    (h1 : lo ≤ o) (h2 : o + 8 ≤ hi) (hw : WordAt a.dmem (fb m0 + BitVec.ofNat 64 o) w) :
    WordAt b.dmem (fb m0 + BitVec.ofNat 64 o) w :=
  Arrays.wordAt_congr hw fun j hj ↦ by
    rw [NativeRustcVm.addr_add_add]; exact h _ (by omega) (by omega)

/-- **Frame bytes a block's writes miss**. -/
theorem fsame_of_writes [Labels] {m0 st st' : MachineData} {rs : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (Env.ofMachine st ((fb m0, 96 + 8) :: rs) vars ret).WF)
    (hm : Match (Env.ofMachine st ((fb m0, 96 + 8) :: rs) vars ret) S st') {lo hi : Nat}
    (hhi : hi ≤ 104) (hw : ∀ w ∈ S.mem, w.r = 0 ∧ (w.off + w.n ≤ lo ∨ hi ≤ w.off)) :
    FSame m0 st st' lo hi := by
  intro j hlo hj
  refine hm.get?_mem0 hwf fun ⟨w, hw', b, sz, hb, h1, h2⟩ ↦ ?_
  obtain ⟨hr, hd⟩ := hw w hw'
  rw [hr] at hb
  simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hb
  obtain ⟨hb1, -⟩ := hb
  subst hb1
  have hnw := hwf.noWrap 0 (fb m0) (96 + 8) rfl
  rw [NativeRustcVm.toNat_add_ofNat (by omega)] at h1 h2
  omega

/-- The prologue's slots fit the frame above the call's slot. -/
theorem slots_ok8 : ∀ p ∈ slots, 8 ≤ p.1 ∧ p.1 + 8 ≤ 96 := fun p hp ↦
  ⟨by have := (slots_ok p hp).1; omega, (slots_ok p hp).2⟩

/-- **What every loop state holds**: the body, term `i` of the form, the terms' address and count
at the frame's `16`, `24`, R12 `i`, the row in R15 (address), R14 (length). -/
structure Core (f : FormW) (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  body : Body m0 96 SS slots 0 0 st
  lt : i < f.size
  t : WordAt st.dmem (fb m0 + BitVec.ofNat 64 16) (UInt64.ofBitVec (reg m0 .rdi))
  n : WordAt st.dmem (fb m0 + BitVec.ofNat 64 24) (UInt64.ofBitVec (reg m0 .rsi))
  r12 : reg st .r12 = BitVec.ofNat 64 i
  r14 : reg st .r14 = reg m0 .rcx
  r15 : reg st .r15 = reg m0 .rdx

theorem Core.mono {f : FormW} {m0 st st' : MachineData} {i : Nat} (h : Core f m0 i st)
    (hb : Body m0 96 SS slots 0 0 st') (hf : FSame m0 st st' 16 32)
    (h12 : reg st' .r12 = reg st .r12) (h14 : reg st' .r14 = reg st .r14)
    (h15 : reg st' .r15 = reg st .r15) : Core f m0 i st' :=
  ⟨hb, h.lt, hf.word (by omega) (by omega) h.t, hf.word (by omega) (by omega) h.n,
    h12.trans h.r12, h14.trans h.r14, h15.trans h.r15⟩

/-- The sum stored at the frame's `32`, `40`. -/
def Stored (m0 st : MachineData) (x : EW) : Prop :=
  WordAt st.dmem (fb m0 + BitVec.ofNat 64 32) x.c0 ∧
    WordAt st.dmem (fb m0 + BitVec.ofNat 64 40) x.c1

theorem Stored.mono {m0 st st' : MachineData} {x : EW} (h : Stored m0 st x)
    (hf : FSame m0 st st' 32 48) : Stored m0 st' x :=
  ⟨hf.word (by omega) (by omega) h.1, hf.word (by omega) (by omega) h.2⟩

/-- **At the outer loop's head** `.L3`: `i` terms summed in RAX, RDX. -/
structure Outer (f : FormW) (m0 : MachineData) (i : Nat) (st : MachineData) : Prop
    extends Core f m0 i st where
  sum : ewArg (reg st .rax) (reg st .rdx) = sumAcc f (row m0) i

/-- **At `.L9`**: the sum stored, term `i`'s product in RAX, RDX. -/
structure AtL9 (f : FormW) (m0 : MachineData) (i : Nat) (st : MachineData) : Prop
    extends Core f m0 i st where
  stored : Stored m0 st (sumAcc f (row m0) i)
  acc : ewArg (reg st .rax) (reg st .rdx) = prodT (row m0) (f[i]'lt)

/-- **At the inner loop's head** `.L5`: term `i`'s first `j` columns multiplied, R13 its degree,
RBX its columns' address, RBP `j`. -/
structure Inner (f : FormW) (m0 : MachineData) (i j : Nat) (st : MachineData) : Prop
    extends Core f m0 i st where
  stored : Stored m0 st (sumAcc f (row m0) i)
  r13 : reg st .r13 = BitVec.ofNat 64 (f[i]'lt).cols.size
  rbx : reg st .rbx = off (tt m0) (40 * i + 8)
  rbp : reg st .rbp = BitVec.ofNat 64 j
  jlt : j < (f[i]'lt).cols.size
  acc : ewArg (reg st .rax) (reg st .rdx) = part (row m0) (f[i]'lt) j

/-- The facts of the precondition the blocks use. -/
structure Facts (f : FormW) (m0 : MachineData) : Prop where
  stack : StackOk m0 SS
  size : (reg m0 .rsi).toNat = f.size
  terms : TermsAt m0.dmem (tt m0) f
  tr : Readable m0 (tt m0) (40 * f.size)
  toff : OffStack m0 (tt m0) (40 * f.size) SS
  row : SliceOk m0 (reg m0 .rdx) (reg m0 .rcx) SS

theorem Facts.of_pre {f : FormW} {m0 : MachineData} (h : EvaluatePre f m0) : Facts f m0 := by
  obtain ⟨hS, hsz, hT, hr, ho, hrow⟩ := h
  have e : termBytes * (reg m0 .rsi).toNat = 40 * f.size := by rw [hsz]; rfl
  rw [e] at hr ho
  exact ⟨hS, hsz, hT, hr, ho, hrow⟩

/-- Term `i`, read in a body. -/
theorem Facts.term {f : FormW} {m0 st : MachineData} (hF : Facts f m0)
    (hb : Body m0 96 SS slots 0 0 st) {i : Nat} (hi : i < f.size) :
    TermWAt st.dmem (off (tt m0) (40 * i)) f[i] := by
  have hs : Same m0.dmem st.dmem (tt m0) (40 * f.size) :=
    Arrays.same_of_apart hb.same hF.stack hF.tr.2 hF.toff (Arrays.apart_zero _ _)
      Arrays.noWrap_zero
  exact TermWAt.of_same (hF.terms i hi) (hs.sub (o := 40 * i) (k := termBytes)
    (by unfold termBytes; omega))

/-- Term `i`'s bytes from `o`, mapped in a body's state and not wrapping. -/
theorem Facts.sub {f : FormW} {m0 st : MachineData} (hF : Facts f m0)
    (hb : Body m0 96 SS slots 0 0 st) {i o n : Nat} (hi : i < f.size) (hon : o + n ≤ 40) :
    NativeRustcVm.Mapped st.dmem (off (tt m0) (40 * i + o)) n ∧
      NativeRustcVm.NoWrap (off (tt m0) (40 * i + o)) n :=
  ⟨fun j hj ↦ by rw [NativeRustcVm.addr_add_add]; exact hb.kept _ (hF.tr.1 _ (by omega)),
    NativeRustcVm.NoWrap.sub (a := tt m0) (n := 40 * f.size) hF.tr.2 (by omega)⟩

/-- Term `i`'s bytes from `o` are apart from the frame. -/
theorem Facts.apart {f : FormW} {m0 : MachineData} (hF : Facts f m0) {i o n : Nat}
    (hi : i < f.size) (hon : o + n ≤ 40) (hn : 0 < n) :
    NativeRustcVm.Apart (fb m0) (96 + 8) (off (tt m0) (40 * i + o)) n := by
  have ha : NativeRustcVm.Apart (tt m0) (40 * f.size) (stackBelow m0 96) (96 + 8) :=
    Transcript.apart_frame hF.toff hF.stack.1 (show 96 ≤ SS by decide)
  have hnw : (tt m0).toNat + 40 * f.size ≤ 2 ^ 64 := hF.tr.2
  unfold NativeRustcVm.Apart at ha ⊢
  rw [show fb m0 = stackBelow m0 96 from rfl, off, NativeRustcVm.toNat_add_ofNat (by omega)]
  omega

theorem tt_lt {f : FormW} {m0 : MachineData} (hF : Facts f m0) {i : Nat} (hi : i < f.size) :
    (tt m0).toNat + 40 * i + 40 ≤ 2 ^ 64 := by
  have : (tt m0).toNat + 40 * f.size ≤ 2 ^ 64 := hF.tr.2
  omega

theorem deg_le {f : FormW} {m0 st : MachineData} (hF : Facts f m0)
    (hb : Body m0 96 SS slots 0 0 st) {i : Nat} (hi : i < f.size) : f[i].cols.size ≤ 2 :=
  (hF.term hb hi).degree_le

variable [Host] {k : Nat}

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.Evaluate.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b0Offset) :=
  hp.label NativeRustcVmX64.Vm.Evaluate.entry_at
theorem lbl_1 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.Evaluate.label_1 = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b12Offset) :=
  hp.label NativeRustcVmX64.Vm.Evaluate.label_1_at
theorem lbl_3 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.Evaluate.label_3 = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b4Offset) :=
  hp.label NativeRustcVmX64.Vm.Evaluate.label_3_at
theorem lbl_5 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.Evaluate.label_5 = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b10Offset) :=
  hp.label NativeRustcVmX64.Vm.Evaluate.label_5_at
theorem lbl_7 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.Evaluate.label_7 = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b7Offset) :=
  hp.label NativeRustcVmX64.Vm.Evaluate.label_7_at
theorem lbl_8 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.Evaluate.label_8 = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b8Offset) :=
  hp.label NativeRustcVmX64.Vm.Evaluate.label_8_at
theorem lbl_9 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.Evaluate.label_9 = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b3Offset) :=
  hp.label NativeRustcVmX64.Vm.Evaluate.label_9_at
theorem lbl_10 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.Evaluate.label_10 = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b13Offset) :=
  hp.label NativeRustcVmX64.Vm.Evaluate.label_10_at

/-- `evaluate`'s postcondition, reached. -/
abbrev Post (f : FormW) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ EvaluatePost f m0 st.data

/-- **The epilogue** `b13`: from a body, the sum returned. -/
theorem finish (hp : Placed code k) {f : FormW} {m0 : MachineData} (hF : Facts f m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b13Offset))
    (hb : Body m0 96 SS slots 0 0 st.data)
    (hsum : ewArg (reg st.data .rax) (reg st.data .rdx) = f.evaluate (row m0)) :
    Eventually (step1 Host.exe) (Post f m0) st := by
  have hS := hF.stack
  have h96 : 96 ≤ SS := by decide
  refine exec_at (infix_of b13_in_code (by simp [b13]) hp) run_b13
    (hb.wf (vars := fun _ ↦ 0) (ret := 0) hS h96) nofun hpc hb.mid_match fun st' hm' hpc' ↦
      .done _ ?_
  obtain ⟨hres, hmem, hax, hdx⟩ := after_eq run_b13 ▸ b13_restores
  obtain ⟨hpc'', hrsp, hdm, hsaved⟩ := hb.done hS h96 hm' hpc' hres hmem
    (fun _ _ ↦ Arrays.not_inRange_zero _)
  refine ⟨hpc'', hrsp, ?_, fun p hp' ↦ by rw [hdm]; exact hb.same p hp', hsaved⟩
  rw [← hsum]
  show ewArg (st'.data.regs.get64 .rax) (st'.data.regs.get64 .rdx) = _
  rw [hm'.regs .rax _ hax, hm'.regs .rdx _ hdx]
  rfl

/-- **The call at `.L8` and `b9`**: term `i`'s `j`th column's entry in R8, RCX multiplied in; on
to `.L9` past the last column, else back to `.L5`. -/
theorem at8 (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {f : FormW} {m0 : MachineData} (hF : Facts f m0) {i j : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b8Offset)) (hI : Inner f m0 i j st.data)
    (hent : ewArg (reg st.data .r8) (reg st.data .rcx) =
      (row m0).getD ((f[i]'hI.lt).cols[j]'hI.jlt) 0) :
    Eventually (step1 Host.exe) (fun s ↦ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b3Offset) ∧ AtL9 f m0 i s.data) ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b10Offset) ∧ Inner f m0 i (j + 1) s.data)) st := by
  have hS := hF.stack
  have h96 : 96 ≤ SS := by decide
  have hb := hI.body
  have hwf := hb.wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b8Offset + b8.length)).toBitVec)
    hS h96
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8 hwf (fun _ _ ↦ rfl) hpc
    hb.mid_match fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hk, hkr, hsp, hw, hdi, hsi, hdx, hcx⟩ := after_eq run_b8 ▸ b8_call
  have hf1 : FSame m0 st.data st1.data 8 104 :=
    fsame_of_writes hwf hm1 le_rfl fun w hw' ↦ ⟨(hw w hw').1, Or.inl (hw w hw').2⟩
  have e1 := regs_eq_of hb.mid_match hm1 hkr
  refine Body.call_mul hmul hb hS (by decide) (L := 8) (by decide) slots_ok8 hwf hb.mid_match hm1
    hpc1 hk hsp hw fun st2 hpc2 hb2 hprod hsv _ hfr ↦ ?_
  have hf2 : FSame m0 st.data st2.data 16 48 :=
    (hf1.mono (by omega) (by omega)).trans fun j' _ hj ↦ hfr j' (by omega)
  have e2 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg st2.data r = reg st.data r := by
    intro r hr
    have hc : calleeSaved r = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [hsv r hc, e1 r hr]
  have hP : ewRet st2.data = part (row m0) (f[i]'hI.lt) (j + 1) := by
    rw [hprod, show reg st1.data .rdi = reg st.data .rax from hm1.regs .rdi _ hdi,
      show reg st1.data .rsi = reg st.data .rdx from hm1.regs .rsi _ hsi,
      show reg st1.data .rdx = reg st.data .r8 from hm1.regs .rdx _ hdx,
      show reg st1.data .rcx = reg st.data .rcx from hm1.regs .rcx _ hcx, hI.acc, hent,
      part_succ _ _ hI.jlt]
    rfl
  -- `b9`
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) run_b9 (Env.wf_nil _) nofun
    (hpc2.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.Evaluate.b8_next))) (match_nil _)
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hk9, hkr9, hrbp9, hzf9⟩ := after_eq run_b9 ▸ b9_facts
  have hb3 := hb2.of_block (match_nil _) hm3 (Env.wf_nil _) rfl hk9
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq (Env.wf_nil _) (mem_of_keepsAll hk9)
  have e3 := regs_eq_of (match_nil _) hm3 hkr9
  have hf3 : FSame m0 st.data st3.data 16 48 := hf2.trans (FSame.of_eq hd3)
  have hcore : Core f m0 i st3.data :=
    hI.toCore.mono hb3 (hf3.mono le_rfl (by omega))
      ((e3 .r12 (by simp)).trans (e2 .r12 (by simp)))
      ((e3 .r14 (by simp)).trans (e2 .r14 (by simp)))
      ((e3 .r15 (by simp)).trans (e2 .r15 (by simp)))
  have hst3 : Stored m0 st3.data (sumAcc f (row m0) i) := hI.stored.mono (hf3.mono (by omega) le_rfl)
  have hacc3 : ewArg (reg st3.data .rax) (reg st3.data .rdx) =
      part (row m0) (f[i]'hI.lt) (j + 1) := by
    rw [e3 .rax (by simp), e3 .rdx (by simp)]; exact hP
  have hdeg := deg_le hF hb hI.lt
  have hj := hI.jlt
  have hrbp3 : reg st3.data .rbp = BitVec.ofNat 64 (j + 1) := by
    rw [show reg st3.data .rbp = _ from hm3.regs .rbp _ hrbp9]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show st2.data.regs.get64 .rbp = reg st.data .rbp from e2 .rbp (by simp), hI.rbp]
    rw [BitVec.ofNat_add]
  simp only [PcOk] at hpc3
  obtain ⟨hy, hn⟩ := pc_cond hpc3
  simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
    Env.ofMachine_regs] at hy hn
  rw [show st2.data.regs.get64 .r13 = reg st.data .r13 from e2 .r13 (by simp),
    show st2.data.regs.get64 .rbp = reg st.data .rbp from e2 .rbp (by simp), hI.r13, hI.rbp,
    ← BitVec.ofNat_add, beq_ofNat (by omega) (by omega)] at hy hn
  by_cases hlast : (f[i]'hI.lt).cols.size = j + 1
  · refine .done _ (Or.inl ⟨(hy (by simpa using hlast)).trans (lbl_9 hp), hcore, hst3, ?_⟩)
    rw [hacc3, ← hlast, part_size]
  · refine .done _ (Or.inr ⟨(hn (by simpa using hlast)).trans
      (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.Evaluate.b9_next)), hcore, hst3, ?_, ?_,
      hrbp3, by omega, hacc3⟩)
    · rw [e3 .r13 (by simp), e2 .r13 (by simp)]; exact hI.r13
    · rw [e3 .rbx (by simp), e2 .rbx (by simp)]; exact hI.rbx

/-- **A turn of the inner loop** `.L5`: column `j`'s entry read, multiplied in. -/
theorem inner_step (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {f : FormW} {m0 : MachineData} (hF : Facts f m0) {i j : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b10Offset)) (hI : Inner f m0 i j st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b3Offset) ∧ AtL9 f m0 i s.data) ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b10Offset) ∧ Inner f m0 i (j + 1) s.data)) st := by
  have hb := hI.body
  have hi := hI.lt
  have hdeg := deg_le hF hb hi
  have hj := hI.jlt
  have htl := tt_lt hF hi
  have ht := hF.term hb hi
  set c := (f[i]'hi).cols[j]'hj with hcdef
  have hclt : c < 2 ^ 64 := ht.cols_lt j hj
  -- `b10`: the column
  have hsub := hF.sub hb hi (o := 8 + 8 * j) (n := 8) (by omega)
  let env := Env.ofMachine st.data [(off (tt m0) (40 * i + (8 + 8 * j)), 8)]
  have hwf : env.WF := Env.wf_of ⟨hsub, trivial⟩ (List.pairwise_singleton _ _)
  have halias : colAddr.eval env = env.base 0 + BitVec.ofInt 64 0 := by
    rw [show env.base 0 = off (tt m0) (40 * i + (8 + 8 * j)) from rfl, Transcript.ofInt_zero64,
      BitVec.add_zero]
    simp only [colAddr, Sym.eval, BinOp.apply, low_W64, ext_W64, env, Env.ofMachine_regs]
    rw [show st.data.regs.get64 .rbx = reg st.data .rbx from rfl,
      show st.data.regs.get64 .rbp = reg st.data .rbp from rfl, hI.rbx, hI.rbp]
    apply BitVec.eq_of_toNat_eq
    simp only [off, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
      show Width.W64.bits = 64 from rfl]
    omega
  have hm : Match env colS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨halias, trivial⟩
  refine exec_at (infix_of b10_in_code (by simp [b10]) hp) run_b10 hwf nofun hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hk, hkr, hrcx, hcf⟩ := after_eq run_b10 ▸ b10_facts
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf (mem_of_keepsAll hk)
  have hb1 := hb.of_block hm hm1 hwf rfl hk
  have e1 := regs_eq_of hm hm1 hkr
  have hcol : env.load 0 0 8 = c.toUInt64.toBitVec := by
    refine Arrays.load_word ?_
    rw [show env.base 0 = off (tt m0) (40 * i + (8 + 8 * j)) from rfl, Arrays.add_ofNat_zero]
    have := ht.cols j hj
    rwa [off_off] at this
  have hrcx1 : reg st1.data .rcx = BitVec.ofNat 64 c := (hm1.regs .rcx _ hrcx).trans hcol
  have hcore1 : Inner f m0 i j st1.data :=
    ⟨hI.toCore.mono hb1 (FSame.of_eq hd1) (e1 .r12 (by simp [keepI])) (e1 .r14 (by simp [keepI]))
        (e1 .r15 (by simp [keepI])),
      hI.stored.mono (FSame.of_eq hd1), (e1 .r13 (by simp [keepI])).trans hI.r13,
      (e1 .rbx (by simp [keepI])).trans hI.rbx, (e1 .rbp (by simp [keepI])).trans hI.rbp, hj,
      by rw [e1 .rax (by simp [keepI]), e1 .rdx (by simp [keepI])]; exact hI.acc⟩
  simp only [PcOk] at hpc1
  obtain ⟨hy, hn⟩ := pc_cond hpc1
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, hcol] at hy hn
  rw [show env.regs .r14 = reg st.data .r14 from rfl, hI.r14] at hy hn
  have hult : (c.toUInt64.toBitVec).ult (reg m0 .rcx) = decide (c < (reg m0 .rcx).toNat) := by
    simp only [BitVec.ult, Nat.toUInt64_eq, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt hclt]
  rw [hult] at hy hn
  by_cases hin : c < (reg m0 .rcx).toNat
  · -- `b7`: the row's entry
    have hpc2 := (hy (by simpa using hin)).trans (lbl_7 hp)
    obtain ⟨⟨hrm, hrn⟩, hro⟩ := hF.row
    have hrd := Arrays.elem_mapped ⟨hrm, hrn⟩ hb1.kept hin
    let env2 := Env.ofMachine st1.data [(reg m0 .rdx + BitVec.ofNat 64 (16 * c), 16)]
    have hwf2 : env2.WF := Env.wf_of ⟨hrd, trivial⟩ (List.pairwise_singleton _ _)
    have hlen := Arrays.lt_of_offStack hrn hro
    have halias2 : elemAddr.eval env2 = env2.base 0 + BitVec.ofInt 64 0 := by
      rw [show env2.base 0 = reg m0 .rdx + BitVec.ofNat 64 (16 * c) from rfl,
        Transcript.ofInt_zero64, BitVec.add_zero]
      simp only [elemAddr]
      rw [Arrays.eval_add, Arrays.eval_shl_lit _ (by decide), Arrays.eval_reg, Arrays.eval_reg]
      simp only [env2, Env.ofMachine_regs]
      rw [show st1.data.regs.get64 .r15 = reg st1.data .r15 from rfl,
        show st1.data.regs.get64 .rcx = reg st1.data .rcx from rfl, hcore1.r15, hrcx1]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega
    have hm2 : Match env2 elemS st1.data :=
      match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨halias2, trivial⟩
    refine exec_at (infix_of b7_in_code (by simp [b7]) hp) run_b7 hwf2 nofun hpc2 hm2
      fun st3 hm3 hpc3 ↦ ?_
    obtain ⟨hk7, hkr7, hr8, hrc⟩ := after_eq run_b7 ▸ b7_facts
    have hd3 : st3.data.dmem = st1.data.dmem := hm3.dmem_eq hwf2 (mem_of_keepsAll hk7)
    have hb3 := hb1.of_block hm2 hm3 hwf2 rfl hk7
    have e3 := regs_eq_of hm2 hm3 hkr7
    have hent : ewArg (reg st3.data .r8) (reg st3.data .rcx) = (row m0).getD c 0 := by
      rw [Arrays.ew_of_loads hm3 hr8 hrc]
      show ewOf st1.data.dmem (reg m0 .rdx + BitVec.ofNat 64 (16 * c) + BitVec.ofNat 64 0) = _
      rw [Arrays.add_ofNat_zero, Arrays.elem_of_apart hb1.same hF.stack hrn hro
        (Arrays.apart_zero _ _) Arrays.noWrap_zero hin]
      simp [row, slice, Array.getD, hin]
    simp only [PcOk] at hpc3
    refine at8 hp hmul hF (hpc3.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.Evaluate.b7_next)))
      ⟨hcore1.toCore.mono hb3 (FSame.of_eq hd3) (e3 .r12 (by simp [keepI]))
          (e3 .r14 (by simp [keepI])) (e3 .r15 (by simp [keepI])),
        hcore1.stored.mono (FSame.of_eq hd3), (e3 .r13 (by simp [keepI])).trans hcore1.r13,
        (e3 .rbx (by simp [keepI])).trans hcore1.rbx, (e3 .rbp (by simp [keepI])).trans hcore1.rbp,
        hj, by rw [e3 .rax (by simp [keepI]), e3 .rdx (by simp [keepI])]; exact hcore1.acc⟩ hent
  · -- `b11`: past the row, `0`
    have hpc2 := hn (by simpa using hin)
    refine exec_at (infix_of b11_in_code (by simp [b11]) hp) run_b11 (Env.wf_nil _) nofun
      (hpc2.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.Evaluate.b10_next))) (match_nil _)
      fun st3 hm3 hpc3 ↦ ?_
    obtain ⟨hk11, hkr11, hr8, hrc⟩ := after_eq run_b11 ▸ b11_facts
    have hd3 : st3.data.dmem = st1.data.dmem := hm3.dmem_eq (Env.wf_nil _) (mem_of_keepsAll hk11)
    have hb3 := hb1.of_block (match_nil _) hm3 (Env.wf_nil _) rfl hk11
    have e3 := regs_eq_of (match_nil _) hm3 hkr11
    have hent : ewArg (reg st3.data .r8) (reg st3.data .rcx) = (row m0).getD c 0 := by
      rw [show reg st3.data .r8 = 0#64 from hm3.regs .r8 _ hr8,
        show reg st3.data .rcx = 0#64 from hm3.regs .rcx _ hrc, getD_of_ge (by rw [size_row]; exact hin)]
      rfl
    simp only [PcOk] at hpc3
    refine at8 hp hmul hF (hpc3.trans (lbl_8 hp))
      ⟨hcore1.toCore.mono hb3 (FSame.of_eq hd3) (e3 .r12 (by simp [keepI]))
          (e3 .r14 (by simp [keepI])) (e3 .r15 (by simp [keepI])),
        hcore1.stored.mono (FSame.of_eq hd3), (e3 .r13 (by simp [keepI])).trans hcore1.r13,
        (e3 .rbx (by simp [keepI])).trans hcore1.rbx, (e3 .rbp (by simp [keepI])).trans hcore1.rbp,
        hj, by rw [e3 .rax (by simp [keepI]), e3 .rdx (by simp [keepI])]; exact hcore1.acc⟩ hent

/-- **The outer loop's head** `.L3` (`b4`): the sum stored, term `i` read; degree `0` on to
`.L9`, else (`b5`) into the inner loop. -/
theorem outer_step (hp : Placed code k) {f : FormW} {m0 : MachineData} (hF : Facts f m0) {i : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b4Offset)) (hO : Outer f m0 i st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b3Offset) ∧ AtL9 f m0 i s.data) ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b10Offset) ∧ Inner f m0 i 0 s.data)) st := by
  have hS := hF.stack
  have h96 : 96 ≤ SS := by decide
  have hb := hO.body
  have hi := hO.lt
  have htl := tt_lt hF hi
  have ht := hF.term hb hi
  have hdeg := ht.degree_le
  have hsub := hF.sub hb hi (o := 0) (n := 40) (by omega)
  let env := Env.ofMachine st.data [(fb m0, 96 + 8), (off (tt m0) (40 * i + 0), 40)]
  have hwf : env.WF := Arrays.wf_two (stackOk_mono hS h96) hb.kept hsub
    (hF.apart hi (by omega) (by omega))
  have h16 : env.load 0 16 8 = tt m0 := Arrays.load_word hO.t
  have halias : termAddr.eval env = env.base 1 + BitVec.ofInt 64 0 := by
    rw [show env.base 1 = off (tt m0) (40 * i + 0) from rfl, Transcript.ofInt_zero64,
      BitVec.add_zero]
    simp only [termAddr, fiveI, Sym.eval, BinOp.apply, low_W64, ext_W64, env,
      Env.ofMachine_regs]
    rw [h16, show st.data.regs.get64 .r12 = reg st.data .r12 from rfl, hO.r12]
    apply BitVec.eq_of_toNat_eq
    simp only [off, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
      show Width.W64.bits = 64 from rfl]
    omega
  have hm : Match env termS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb.rsp, trivial⟩ trivial trivial ⟨halias, trivial⟩
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf nofun hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hk, hkr, hw, hw', hv0, hv1, hax, hdx, hr13, hrbx, hcf⟩ := after_eq run_b4 ▸ b4_facts
  have hb1 := hb.of_frame hS h96 hwf hm hm1 hk hw (by omega) slots_ok
  have hf1 : FSame m0 st.data st1.data 16 32 :=
    fsame_of_writes hwf hm1 (by omega) fun w hw'' ↦ ⟨(hw' w hw'').1, (hw' w hw'').2⟩
  have e1 := regs_eq_of hm hm1 hkr
  have hcore : Core f m0 i st1.data :=
    hO.toCore.mono hb1 hf1 (e1 .r12 (by simp)) (e1 .r14 (by simp)) (e1 .r15 (by simp))
  have hstored : Stored m0 st1.data (sumAcc f (row m0) i) := by
    have w0 := Arrays.wordAt_of_write hm1 (r := 0) (o := 32) (b := fb m0) (sz := 96 + 8)
      (v := .reg .rax) rfl (by omega) hv0
    have w1 := Arrays.wordAt_of_write hm1 (r := 0) (o := 40) (b := fb m0) (sz := 96 + 8)
      (v := .reg .rdx) rfl (by omega) hv1
    rw [Arrays.eval_reg, Env.ofMachine_regs] at w0 w1
    rw [Stored, c0_of hO.sum, c1_of hO.sum]
    exact ⟨w0, w1⟩
  have hd : env.load 1 0 8 = BitVec.ofNat 64 (f[i]'hi).cols.size := by
    rw [Arrays.load_word (r := 1) (o := 0) (env := env) (w := (f[i]'hi).cols.size.toUInt64)
      (by rw [show env.base 1 = off (tt m0) (40 * i + 0) from rfl, Arrays.add_ofNat_zero,
        Nat.add_zero]; exact ht.degree)]
    rfl
  have hcoef : ewArg (reg st1.data .rax) (reg st1.data .rdx) = (f[i]'hi).coeff := by
    rw [Arrays.ew_of_loads hm1 hax hdx]
    show ewOf st.data.dmem (off (tt m0) (40 * i + 0) + BitVec.ofNat 64 24) = _
    rw [Nat.add_zero]
    exact NativeRustcVm.ewOf_of_ewAt ht.coeff
  simp only [PcOk] at hpc1
  obtain ⟨hy, hn⟩ := pc_cond hpc1
  simp only [SBool.eval, Sym.eval, hd] at hy hn
  rw [deg_cond _ hdeg] at hy hn
  by_cases h0 : (f[i]'hi).cols.size = 0
  · refine .done _ (Or.inl ⟨(hy (by simpa using h0)).trans (lbl_9 hp), hcore, hstored, ?_⟩)
    rw [hcoef, ← part_size, h0, part_zero]
  · have hpc2 := hn (by simpa using h0)
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 (Env.wf_nil _) nofun
      (hpc2.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.Evaluate.b4_next))) (match_nil _)
      fun st2 hm2 hpc3 ↦ ?_
    obtain ⟨hk5, hkr5, hrbp⟩ := after_eq run_b5 ▸ b5_facts
    have hb2 := hb1.of_block (match_nil _) hm2 (Env.wf_nil _) rfl hk5
    have hd2 : st2.data.dmem = st1.data.dmem := hm2.dmem_eq (Env.wf_nil _) (mem_of_keepsAll hk5)
    have e2 := regs_eq_of (match_nil _) hm2 hkr5
    simp only [PcOk] at hpc3
    refine .done _ (Or.inr ⟨hpc3.trans (lbl_5 hp),
      hcore.mono hb2 (FSame.of_eq hd2) (e2 .r12 (by simp)) (e2 .r14 (by simp)) (e2 .r15 (by simp)),
      hstored.mono (FSame.of_eq hd2), ?_, ?_, hm2.regs .rbp _ hrbp, by omega, ?_⟩)
    · rw [e2 .r13 (by simp), show reg st1.data .r13 = _ from hm1.regs .r13 _ hr13]; exact hd
    · rw [e2 .rbx (by simp), show reg st1.data .rbx = _ from hm1.regs .rbx _ hrbx]
      simp only [rbxS, Sym.eval, SBool.eval, hd, deg_lt3 _ hdeg, Bool.not_true,
        Bool.false_eq_true, ite_false, BinOp.apply, low_W64, ext_W64]
      rw [halias, show env.base 1 = off (tt m0) (40 * i + 0) from rfl, Transcript.ofInt_zero64,
        BitVec.add_zero]
      simp only [off, Nat.add_zero]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [e2 .rax (by simp), e2 .rdx (by simp), hcoef, part_zero]

/-- **At `.L9`** (`b3`): the product added to the sum; past the last term to the epilogue, else
back to `.L3`. -/
theorem end_step (hp : Placed code k) {f : FormW} {m0 : MachineData} (hF : Facts f m0) {i : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b3Offset)) (hA : AtL9 f m0 i st.data) :
    Eventually (step1 Host.exe) (fun s ↦ Post f m0 s ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b4Offset) ∧ Outer f m0 (i + 1) s.data)) st := by
  have hS := hF.stack
  have h96 : 96 ≤ SS := by decide
  have hb := hA.body
  have hi := hA.lt
  have hwf := hb.wf (vars := fun _ ↦ 0) (ret := 0) hS h96
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf nofun hpc hb.mid_match
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hk, hkr, hax, hdx, hr12, hzf⟩ := after_eq run_b3 ▸ b3_facts
  have hb1 := hb.of_block hb.mid_match hm1 hwf rfl hk
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf (mem_of_keepsAll hk)
  have e1 := regs_eq_of hb.mid_match hm1 hkr
  have hsize : (reg m0 .rsi).toNat = f.size := hF.size
  have hsz64 : f.size < 2 ^ 64 := by rw [← hsize]; exact BitVec.isLt _
  have hsum : ewArg (reg st1.data .rax) (reg st1.data .rdx) = sumAcc f (row m0) (i + 1) := by
    rw [show reg st1.data .rax = _ from hm1.regs .rax _ hax,
      show reg st1.data .rdx = _ from hm1.regs .rdx _ hdx]
    simp only [Sym.eval, Arrays.xor_eval]
    rw [Arrays.load_word hA.stored.1, Arrays.load_word hA.stored.2, Arrays.ewArg_xor,
      ewArg_toBitVec, sumAcc_succ _ _ hi]
    show sumAcc f (row m0) i + ewArg (reg st.data .rax) (reg st.data .rdx) = _
    rw [hA.acc]
  have hr12' : reg st1.data .r12 = BitVec.ofNat 64 (i + 1) := by
    rw [show reg st1.data .r12 = _ from hm1.regs .r12 _ hr12]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show st.data.regs.get64 .r12 = reg st.data .r12 from rfl, hA.r12, BitVec.ofNat_add]
  simp only [PcOk] at hpc1
  obtain ⟨hy, hn⟩ := pc_cond hpc1
  simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
    Env.ofMachine_regs] at hy hn
  rw [Arrays.load_word hA.n, show st.data.regs.get64 .r12 = reg st.data .r12 from rfl, hA.r12,
    ← BitVec.ofNat_add, show (UInt64.ofBitVec (reg m0 .rsi)).toBitVec = BitVec.ofNat 64 f.size by
      rw [← hsize]; simp, beq_ofNat (by omega) hsz64] at hy hn
  by_cases hlast : i + 1 = f.size
  · refine Eventually.mono (finish hp hF ((hy (by simpa using hlast)).trans (lbl_10 hp)) hb1 ?_)
      fun s h ↦ Or.inl h
    rw [hsum, hlast, evaluate_eq]
  · exact .done _ (Or.inr ⟨(hn (by simpa using hlast)).trans
      (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.Evaluate.b3_next)),
      ⟨⟨hb1, by omega, (by rw [hd1]; exact hA.t), (by rw [hd1]; exact hA.n), hr12', (e1 .r14 (by simp)).trans hA.r14,
        (e1 .r15 (by simp)).trans hA.r15⟩, hsum⟩⟩)

/-- **`evaluate` meets its contract.** -/
theorem evaluate_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (f : FormW) :
    Spec (Labels.label NativeRustcVmX64.Vm.Evaluate.entryLabel) (EvaluatePre f) (EvaluatePost f) := by
  intro m0 hpre
  have hF := Facts.of_pre hpre
  have hS := hF.stack
  have h96 : 96 ≤ SS := by decide
  rw [lbl_entry hp]
  have hwf := frame_wf (m0 := m0) (m := m0) (vars := fun _ ↦ 0) (ret := 0) (stackOk_mono hS h96)
    fun _ h ↦ h
  have hm : Match (frameEnv m0 m0 96) entryS m0 := match_frame
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf nofun hm
    fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, NativeRustcVmX64.Vm.Evaluate.b0_length] at hpc1
  obtain ⟨hy, hn⟩ := pc_cond hpc1
  have hsize : (reg m0 .rsi).toNat = f.size := hF.size
  have entry : ∀ {S' : SState} {st : MachineState}, EntryOk S' →
      Match (frameEnv m0 m0 96) S' st.data →
      Body m0 96 SS slots 0 0 st.data ∧
        WordAt st.data.dmem (fb m0 + BitVec.ofNat 64 16) (UInt64.ofBitVec (reg m0 .rdi)) ∧
        WordAt st.data.dmem (fb m0 + BitVec.ofNat 64 24) (UInt64.ofBitVec (reg m0 .rsi)) ∧
        ewArg (reg st.data .rax) (reg st.data .rdx) = 0 := by
    intro S' st hE hm2
    obtain ⟨hw, hregs, hmem, hsp, h16, h24, hax, hdx⟩ := hE
    have w0 := Arrays.wordAt_of_write hm2 (r := 0) (o := 16) (b := fb m0) (sz := 96 + 8)
      (v := .reg .rdi) rfl (by omega) h16
    have w1 := Arrays.wordAt_of_write hm2 (r := 0) (o := 24) (b := fb m0) (sz := 96 + 8)
      (v := .reg .rsi) rfl (by omega) h24
    rw [Arrays.eval_reg, Env.ofMachine_regs] at w0 w1
    refine ⟨Body.of_entry hS h96 hm2 hsp hw hregs hmem, w0, w1, ?_⟩
    rw [show reg st.data .rax = _ from hm2.regs .rax _ hax,
      show reg st.data .rdx = _ from hm2.regs .rdx _ hdx]
    rfl
  by_cases hz : f.size = 0
  · -- no terms
    have hpc2 := (hy (by
      simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
      rw [test_self]
      simpa [hsize] using hz)).trans (lbl_1 hp)
    refine exec_at (infix_of b12_in_code (by simp [b12]) hp) (exec_after run_b0 run_b12) hwf nofun
      hpc2 hm1 fun st2 hm2 hpc3 ↦ ?_
    obtain ⟨hb2, -, -, h0⟩ := entry (after_eq run_b12 ▸ b12_entry) hm2
    simp only [PcOk] at hpc3
    have hl : b12.length = 3 := rfl
    refine finish hp hF (hpc3.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.Evaluate.b12_next))) hb2 ?_
    rw [h0, evaluate_eq, hz, sumAcc_zero]
  · -- the loop
    have hpc2 := hn (by
      simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
      rw [test_self]
      simpa [hsize] using hz)
    refine exec_at (infix_of b1_in_code (by simp [b1]) hp) (exec_after run_b0 run_b1) hwf nofun
      hpc2 hm1 fun st2 hm2 hpc3 ↦ ?_
    obtain ⟨hE, h12, h14, h15⟩ := after_eq run_b1 ▸ b1_entry
    obtain ⟨hb2, ht2, hn2, h0⟩ := entry hE hm2
    simp only [PcOk] at hpc3
    have hO : Outer f m0 0 st2.data :=
      ⟨⟨hb2, Nat.pos_of_ne_zero hz, ht2, hn2, hm2.regs .r12 _ h12, hm2.regs .r14 _ h14,
        hm2.regs .r15 _ h15⟩, by rw [h0, sumAcc_zero]⟩
    refine Sym.loop (fun n s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b4Offset) ∧ ∃ i, f.size - i = n ∧
      Outer f m0 i s.data) (fun n s ⟨hpc, i, hni, hOi⟩ ↦ ?_) ⟨hpc3.trans (lbl_3 hp), 0, rfl, hO⟩
    have hlt := hOi.lt
    refine Eventually.bind (outer_step hp hF hpc hOi) fun s1 h1 ↦ ?_
    have toEnd : ∀ {s2 : MachineState}, s2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b3Offset) → AtL9 f m0 i s2.data →
        Eventually (step1 Host.exe) (fun s' ↦ Post f m0 s' ∨ ∃ n' < n,
          s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b4Offset) ∧ ∃ i, f.size - i = n' ∧ Outer f m0 i s'.data) s2 :=
      fun h2 hA ↦ Eventually.mono (end_step hp hF h2 hA) fun s' h ↦ h.elim Or.inl
        fun ⟨hp', hO'⟩ ↦ Or.inr ⟨f.size - (i + 1), by omega, hp', i + 1, rfl, hO'⟩
    rcases h1 with ⟨h2, hA⟩ | ⟨h2, hI⟩
    · exact toEnd h2 hA
    · refine Eventually.bind (p := fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b3Offset) ∧ AtL9 f m0 i s.data)
        (Sym.loop (fun n' s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Evaluate.b10Offset) ∧ ∃ j, (f[i]'hlt).cols.size - j = n' ∧
          Inner f m0 i j s.data) (fun n' s ⟨hpc', j, hnj, hIj⟩ ↦ ?_) ⟨h2, 0, rfl, hI⟩)
        fun s3 ⟨h3, hA⟩ ↦ toEnd h3 hA
      refine Eventually.mono (inner_step hp hmul hF hpc' hIj) fun s' h ↦ ?_
      rcases h with h | ⟨h4, hI'⟩
      · exact Or.inl h
      · exact Or.inr ⟨(f[i]'hlt).cols.size - (j + 1), by have := hI'.jlt; omega, h4, j + 1, rfl,
          hI'⟩

end

end NativeRustcVmX64.Layout.Evaluate
