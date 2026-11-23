module

public import NativeRustcVmX64.Bus.AccumulateSide.Exec
public import NativeRustcVmX64.Bus.AccumulateSide.Track
public import NativeRustcVmX64.Bus.AccumulateSide.Model
public import NativeRustcVmX64.Bus.BlockForm.Lemmas

/-!
# `accumulate_side`: what its proof shares (x86-64)

The precondition by name (`Pre`, `pre_of`). The body's state (`St m0 O V D o m`): the frame (RSP at
offset `o`), memory changed only in the outputs `O` and the stack, and a
description `D` of the values the body keeps, registers and frame words, holding the table `V`
(`Holds`). A block writing the frame below its slots keeps it (`St.run`); a call changing its
stack, the frame's `n` bytes from `lo` and the forms keeps it where `D`'s locations are not
among them (`callOk`, `St.call`).
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Bus NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

@[expose] public section

/-- The stack the function uses. -/
abbrev N : Nat := accumulateSideStack

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := stackBelow m0 F

/-- The forms: the outputs until the end. -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (reg m0 .rsi) formsBytes q

/-- A location a call keeps, the call writing the frame's `n` bytes from `lo`: a callee-saved
register, a literal, a frame word outside those bytes. -/
def callOk (lo n : Nat) : Sym → Bool
  | .reg r => calleeSaved r
  | .lit _ => true
  | .load 0 o 8 => decide (o + 8 ≤ lo ∨ lo + n ≤ o) && decide (o + 8 ≤ F + 8)
  | _ => false

section
variable (m0 : MachineData)

/-- The fingerprints' count. -/
abbrev nA : Nat := (stackArg m0 2).toNat
/-- The fingerprints. -/
abbrev fpsA : Array EW := (NativeRustcVm.ewsOf m0.dmem (stackArg m0 1) (nA m0)).toArray
/-- The weights. -/
abbrev wA : Array EW := slice m0 (stackArg m0 3) (stackArg m0 4)
/-- `side_beta`. -/
abbrev betaA : EW := ewArg (stackArg m0 5) (stackArg m0 6)
/-- The point. -/
abbrev ptA : Array EW := slice m0 (stackArg m0 7) (stackArg m0 8)
/-- The tree's value. -/
abbrev treeA : EW := ewArg (stackArg m0 9) (stackArg m0 10)

end

/-- The side's blocks at the layout's heights and rows. -/
abbrev BA (L : LayoutW) (rows : Array Nat) (bl : List NativeRustcVm.Data.Block) :
    Array BusBlockW :=
  (bl.map (blockW L.tableLogHeights rows)).toArray

section
variable [Labels]

/-- `AccumulateSidePre`'s conjuncts. -/
structure Pre (L : LayoutW) (rows : Array Nat) (bl : List NativeRustcVm.Data.Block)
    (Fm : Array (Array FormW)) (SL : BusLayoutW) (m0 : MachineData) : Prop where
  stack : StackOk m0 N
  rodata : RodataAt m0 N
  args : ArgsOk m0 11
  side : (reg m0 .rdx).toNat < 3
  forms : FormsAt m0.dmem (reg m0 .rsi) Fm
  formsOk : InOk m0 (reg m0 .rsi) formsBytes N
  formsRo : RodataApart (reg m0 .rsi) formsBytes
  blen : 1 ≤ bl.length
  r8 : (reg m0 .r8).toNat = bl.length
  bown : ∀ x ∈ bl, x.owner < nTables ∧ x.tuple < NativeRustcVm.Data.tuples.length
  blocks : NativeRustcVm.BytesAt m0.dmem (reg m0 .rcx) (bl.flatMap NativeRustcVm.Data.Block.bytes)
  blocksOk : InOk m0 (reg m0 .rcx) (16 * bl.length) N
  lay : LayoutWAt m0.dmem (reg m0 .r9) L
  rows_size : rows.size = nTables
  rowsW : NativeRustcVm.WordsAt m0.dmem (off (reg m0 .r9) 72) (rows.toList.map Nat.toUInt64)
  layOk : InOk m0 (reg m0 .r9) layoutBytes N
  sl : BusLayoutWAt m0.dmem (stackArg m0 0) SL
  sl_size : SL.tables.size = bl.length
  slOk : InOk m0 (stackArg m0 0) busLayoutBytes N
  fp : 0 < nA m0 → InOk m0 (stackArg m0 1) (16 * nA m0) N
  w : SliceOk m0 (stackArg m0 3) (stackArg m0 4) N
  pn : (stackArg m0 8).toNat < 64
  pt : SliceOk m0 (stackArg m0 7) (stackArg m0 8) N
  fits : SideFits Fm (reg m0 .rdx).toNat (BA L rows bl) SL (fpsA m0) (wA m0) (betaA m0) (ptA m0)
    (treeA m0)
  out : InOk m0 (reg m0 .rdi) 24 N
  outRo : RodataApart (reg m0 .rdi) 24
  outF : Apart (reg m0 .rdi) 24 (reg m0 .rsi) formsBytes
  fB : Apart (reg m0 .rsi) formsBytes (reg m0 .rcx) (16 * bl.length)
  fL : Apart (reg m0 .rsi) formsBytes (reg m0 .r9) layoutBytes
  fSL : Apart (reg m0 .rsi) formsBytes (stackArg m0 0) busLayoutBytes
  fFp : 0 < nA m0 → Apart (reg m0 .rsi) formsBytes (stackArg m0 1) (16 * nA m0)
  fW : Apart (reg m0 .rsi) formsBytes (stackArg m0 3) (16 * (stackArg m0 4).toNat)
  fPt : Apart (reg m0 .rsi) formsBytes (stackArg m0 7) (16 * (stackArg m0 8).toNat)
  fArgs : Apart (reg m0 .rsi) formsBytes (rspOf m0 + 8#64) 88
  slArgs : Apart (stackArg m0 0) busLayoutBytes (rspOf m0 + 8#64) 88
  slFp : 0 < nA m0 → Apart (stackArg m0 0) busLayoutBytes (stackArg m0 1) (16 * nA m0)
  got : GotAt m0 N ([(reg m0 .rdi, 24), (reg m0 .rsi, formsBytes),
    (reg m0 .rcx, 16 * bl.length), (reg m0 .r9, layoutBytes),
    (stackArg m0 0, busLayoutBytes),
    (stackArg m0 3, 16 * (stackArg m0 4).toNat),
    (stackArg m0 7, 16 * (stackArg m0 8).toNat), (rspOf m0 + 8#64, 88)] ++
    (if nA m0 = 0 then [] else [(stackArg m0 1, 16 * nA m0)]) ++
    ([.tuples, .tables, .padding, .one] : List NativeRustcVm.Data.Item).map
      (fun i => (rodataAddr i, i.bytes.length))) ["memcpy"]

/-- **The body's state**: the frame (RSP at offset `o`), memory changed only in the outputs `O`
and the stack, the description `D` of the table `V`. -/
structure St (m0 : MachineData) (O : BitVec 64 → Prop) (V : Nat → UInt64) (D : List (Sym × Nat))
    (o : Nat) (m : MachineData) : Prop where
  fr : Frame m0 F slots o m
  same : NativeRustcVm.SameOutside m0.dmem m.dmem
    (fun q ↦ O q ∨ NativeRustcVm.InRange (stackBelow m0 N) N q)
  hd : Holds [(fb m0, F + 8)] V D m

end

end

public section

theorem pre_of [Labels] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
    {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData}
    (h : AccumulateSidePre L rows bl Fm SL m0) : Pre L rows bl Fm SL m0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, hg⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, hg⟩

theorem le_F : F ≤ N := by decide
theorem le_ee : F + eqEvalFnStack ≤ N := by decide
theorem le_mul : F + ewMulStack ≤ N := by decide
theorem le_bf : F + blockFormStack ≤ N := by decide
theorem le_as : F + formBufAddScaledStack ≤ N := by decide
theorem le_pw : F + paddingWeightStack ≤ N := by decide
theorem le_ev : F + evaluateStack ≤ N := by decide
theorem le_mc : F + 0 ≤ N := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ F := by decide
theorem slots_ge : ∀ p ∈ slots, 11984 ≤ p.1 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide

theorem isLoc_of_loc0 {s : Sym} (h : loc0 s = true) : isLoc s = true := by
  match s, h with
  | .reg _, _ => rfl
  | .lit _, _ => rfl
  | .load 0 _ 8, _ => rfl

theorem loc0_of_callOk {lo n : Nat} {s : Sym} (h : callOk lo n s = true) : loc0 s = true := by
  match s, h with
  | .reg _, _ => rfl
  | .lit _, _ => rfl
  | .load 0 _ 8, _ => rfl

theorem all_isLoc {D : List (Sym × Nat)} (h : D.all (fun p ↦ loc0 p.1) = true) :
    D.all (fun p ↦ isLoc p.1) = true :=
  List.all_eq_true.mpr fun p hp ↦ isLoc_of_loc0 (List.all_eq_true.mp h p hp)

section
variable [Labels] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData}

theorem Pre.spN (h : Pre L rows bl Fm SL m0) : N ≤ (rspOf m0).toNat := h.stack.1
theorem Pre.sp8 (h : Pre L rows bl Fm SL m0) : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := h.stack.2.1

theorem Pre.fbN (h : Pre L rows bl Fm SL m0) : (fb m0).toNat = (rspOf m0).toNat - F :=
  stackBelow_toNat (by have := h.spN; have := le_F; omega)

theorem Pre.frame_nw (h : Pre L rows bl Fm SL m0) : NativeRustcVm.NoWrap (fb m0) (F + 8) :=
  frame_noWrap h.stack le_F

theorem Pre.forms_nw (h : Pre L rows bl Fm SL m0) :
    NativeRustcVm.NoWrap (reg m0 .rsi) formsBytes := h.formsOk.1.2

/-- The forms are apart from the frame. -/
theorem Pre.outs_frame (h : Pre L rows bl Fm SL m0) {q : BitVec 64} (hq : outs m0 q) :
    ¬ NativeRustcVm.InRange (fb m0) (F + 8) q :=
  NativeRustcVm.Apart.not_inRange (apart_frame h.formsOk.2 h.spN le_F) h.forms_nw h.frame_nw hq

/-- A frame byte is no byte of the forms. -/
theorem Pre.frame_not_outs (h : Pre L rows bl Fm SL m0) {j : Nat} (hj : j < F + 8) :
    ¬ outs m0 (off (fb m0) j) := fun hq ↦
  h.outs_frame hq (inRange_off_self hj (by have := h.frame_nw; unfold NativeRustcVm.NoWrap at this; omega))

/-- A frame byte outside `[lo, lo + n)`. -/
theorem Pre.not_loc (h : Pre L rows bl Fm SL m0) {lo n j : Nat} (hj : j < F + 8)
    (hlo : lo + n ≤ F + 8) (hjn : j < lo ∨ lo + n ≤ j) :
    ¬ NativeRustcVm.InRange (off (fb m0) lo) n (off (fb m0) j) := by
  have hnw := h.frame_nw
  unfold NativeRustcVm.NoWrap at hnw
  rw [inRange_off_iff (by omega) (by omega)]
  omega

/-- A callee's stack misses the frame. -/
theorem Pre.not_callee (h : Pre L rows bl Fm SL m0) {d : MachineData} (hsp : rspOf d = fb m0)
    {Nc : Nat} (hle : F + Nc ≤ N) {j : Nat} (hj : j < F + 8) :
    ¬ NativeRustcVm.InRange (stackBelow d Nc) Nc (off (fb m0) j) := fun hq ↦
  (inRange_callee hsp h.sp8 h.spN hle hq).2
    (inRange_off_self hj (by have := h.frame_nw; unfold NativeRustcVm.NoWrap at this; omega))

/-- The frame below its return address is in the stack. -/
theorem Pre.frame_stk (h : Pre L rows bl Fm SL m0) {lo n : Nat} (hlo : lo + n ≤ F) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (off (fb m0) lo) n q) :
    NativeRustcVm.InRange (stackBelow m0 N) N q :=
  inRange_frame_stack h.sp8 h.spN le_F (inRange_of_off (h.frame_nw.mono (by omega)) hlo hq)

end

variable [Host] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData}

/-- **A block of the body**, region `0` the frame, the other regions `rest`, from a state
whose frame and memory are the body's and whose locations `D0` hold their values: the frame
words and registers `D'` tracked (`trackOk`); a location's value after it is its content's
(`hc`). -/
theorem St.run (h : Pre L rows bl Fm SL m0) {rest : List (BitVec 64 × Nat)} {sz : List Nat}
    (hsz : ((fb m0, F + 8) :: rest).map Prod.snd = sz) {vs : Nat → BitVec 64} {ret : BitVec 64}
    {S S' : SState} {ds : List Directive} {k : Nat} {x : Exit} {R : MachineState → Prop}
    {m : MachineData} {V : Nat → UInt64} {D0 D' : List (Sym × Nat)} {o o' : Nat}
    {O : BitVec 64 → Prop} (hk : ds.IsInfixAt Host.prog k) (hrun : exec ds S = some (S', x))
    (hret : ∀ l, x = .call l → ret = (Host.addrOf (k + ds.length)).toBitVec)
    (hfr : Frame m0 F slots o m) (hsame : NativeRustcVm.SameOutside m0.dmem m.dmem
      (fun q ↦ O q ∨ NativeRustcVm.InRange (stackBelow m0 N) N q))
    (hH : Holds ((fb m0, F + 8) :: rest) V D0 m) (hD0 : D0.all (fun p ↦ isLoc p.1) = true)
    (hwf : (frameEnv m0 m F rest vs ret).WF) (hm : Match (frameEnv m0 m F rest vs ret) S m)
    (hmid : MidOk F o' slots S' = true) (hw : S'.mem.all (fun w ↦ w.r == 0) = true)
    (hD' : D'.all (fun p ↦ loc0 p.1) = true) (htr : trackOk sz S' D0 D' = true)
    (cont : ∀ st, Match (frameEnv m0 m F rest vs ret) S' st.data →
      PcOk (frameEnv m0 m F rest vs ret) x (Host.addrOf (k + ds.length)) st →
      St m0 O V D' o' st.data →
      (∀ s c, loc0 s = true → content sz S' s = some c →
        tval [(fb m0, F + 8)] st.data s = UInt64.ofBitVec (c.eval (frameEnv m0 m F rest vs ret))) →
      Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf k⟩ :=
  exec_then hk hrun hwf (fun l hl ↦ hret l hl) hm fun st hm' hpc ↦ cont st hm' hpc
    ⟨Frame.of_block hfr hwf hm' hmid slots_le,
      fun q hq ↦ (hm'.get?_mem0 hwf fun hW ↦ hq (.inr (inRange_frame_stack h.sp8 h.spN le_F
        (written_low hwf (fun w hw' ↦ by simpa using List.all_eq_true.mp hw w hw')
          (belowRet_of_mid hmid) hW)))).trans (hsame q hq),
      Holds.reg0 (Holds.after hsz hH hD0 hm' htr) hD' rfl⟩
    fun s c hs hc ↦ by
      rw [← content_eval hsz hm' hc]
      unfold tval
      congr 1
      match s, hs with
      | .reg _, _ => rfl
      | .lit _, _ => rfl
      | .load 0 _ 8, _ => rfl

omit [Host] in
/-- **Other outputs**: more outputs. -/
theorem St.widen [Labels] {O O' : BitVec 64 → Prop} {V : Nat → UInt64} {D : List (Sym × Nat)}
    {o : Nat} {m : MachineData} (hst : St m0 O V D o m) (hO : ∀ q, O q → O' q) :
    St m0 O' V D o m :=
  ⟨hst.fr, NativeRustcVm.SameOutside.mono hst.same fun q hq ↦ hq.imp_left (hO q), hst.hd⟩

omit [Host] in
/-- **More values**: a description holding with a table `V` holds with a table `V'` agreeing on
its indices, and more locations `E`. -/
theorem St.add [Labels] {O : BitVec 64 → Prop} {V V' : Nat → UInt64} {D E : List (Sym × Nat)}
    {o : Nat} {m : MachineData} (hst : St m0 O V D o m) (hV : ∀ p ∈ D, V p.2 = V' p.2)
    (hE : Holds [(fb m0, F + 8)] V' E m) : St m0 O V' (D ++ E) o m :=
  ⟨hst.fr, hst.same, (hst.hd.congrV hV).append hE⟩

omit [Host] in
/-- **Fewer values.** -/
theorem St.sub [Labels] {O : BitVec 64 → Prop} {V : Nat → UInt64} {D D' : List (Sym × Nat)}
    {o : Nat} {m : MachineData} (hst : St m0 O V D o m) (hD : ∀ p ∈ D', p ∈ D) :
    St m0 O V D' o m :=
  ⟨hst.fr, hst.same, hst.hd.mono hD⟩

/-- **A call from the body** (RSP at offset `0`): its stack, the frame's `n` bytes from `lo` and
outputs `W` among `O` (apart from the frame) written, the description's locations kept. -/
theorem St.call (h : Pre L rows bl Fm SL m0) {l : Label} {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} {Nc lo n : Nat} {st : MachineState} {next : Int64}
    {R : MachineState → Prop} {O W : BitVec 64 → Prop} {V : Nat → UInt64} {D : List (Sym × Nat)}
    (hst : St m0 O V D 0 st.data) (hle : F + Nc ≤ N) (hlo : lo + n ≤ 11984)
    (hD : D.all (fun p ↦ callOk lo n p.1) = true) (hspec : Spec (Labels.label l) P Q)
    (hpc : st.pc = Labels.label l ∧ retOf st.data = next) (hP : P st.data)
    (hW : ∀ q, W q → O q ∧ ¬ NativeRustcVm.InRange (fb m0) (F + 8) q)
    (hQ : ∀ m', Q st.data m' → NativeRustcVm.SameOutside st.data.dmem m'.dmem (fun q ↦
      NativeRustcVm.InRange (stackBelow st.data Nc) Nc q ∨
        NativeRustcVm.InRange (off (fb m0) lo) n q ∨ W q) ∧ Saved st.data m')
    (cont : ∀ m2, St m0 O V D 8 m2 → Q st.data m2 → Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hsp : rspOf st.data = fb m0 := by rw [hst.fr.sp, off_zero]
  have hF : F = 12032 := rfl
  have hnotR : ∀ j, j < F + 8 → (j < lo ∨ lo + n ≤ j) → ¬ (NativeRustcVm.InRange
      (stackBelow st.data Nc) Nc (off (fb m0) j) ∨
        NativeRustcVm.InRange (off (fb m0) lo) n (off (fb m0) j) ∨ W (off (fb m0) j)) :=
    fun j hj hjn hq ↦ by
      rcases hq with hq | hq | hq
      · exact h.not_callee hsp hle hj hq
      · exact h.not_loc hj (by omega) hjn hq
      · exact (hW _ hq).2 (inRange_off_self hj
          (by have := h.frame_nw; unfold NativeRustcVm.NoWrap at this; omega))
  refine call_then (env := Env.ofMachine st.data []) hpc hspec hP fun st' hpc' hrsp' hq ↦ ?_
  obtain ⟨hso, hsv⟩ := hQ _ hq
  obtain ⟨m2, pc2⟩ := st'
  simp only at hpc' hrsp' hq hso hsv
  subst hpc'
  refine cont m2 ⟨Frame.call_slots hst.fr hsv hrsp' hso (fun p hp i hi ↦ hnotR _
      (by have := slots_le p hp; omega) (.inr (by have := slots_ge p hp; omega)))
      (fun j hj ↦ hnotR _ (by omega) (.inr (by omega))), fun q hq' ↦ ?_, fun p hp ↦ ?_⟩ hq
  · refine (hso q fun hR ↦ hq' ?_).trans (hst.same q hq')
    rcases hR with hR | hR | hR
    · exact .inr (inRange_callee hsp h.sp8 h.spN hle hR).1
    · exact .inr (h.frame_stk (by omega) hR)
    · exact .inl (hW q hR).1
  · rw [← hst.hd p hp]
    have hc : callOk lo n p.1 = true := List.all_eq_true.mp hD p hp
    unfold tval
    congr 1
    match hs : p.1, hc with
    | .reg r, hc =>
      show m2.regs.get64 r = st.data.regs.get64 r
      exact hsv.1 r hc
    | .lit _, _ => rfl
    | .load 0 o 8, hc =>
      simp only [callOk, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hc1, hc2⟩ := hc
      simp only [Sym.eval, Env.load]
      congr 2
      apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      show (m2.dmem.get? (fb m0 + BitVec.ofNat 64 (o + j))).getD 0 =
        (st.data.dmem.get? (fb m0 + BitVec.ofNat 64 (o + j))).getD 0
      rw [show (fb m0) + BitVec.ofNat 64 (o + j) = off (fb m0) (o + j) from rfl,
        hso _ (hnotR (o + j) (by omega) (by omega))]

end

end NativeRustcVmX64.Bus.AccumulateSide
