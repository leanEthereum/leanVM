module

public import NativeRustcVmX64.Layout.FormBufAddTerm.Exec
public import NativeRustcVmX64.Layout.Forms.Lemmas
public import NativeRustcVmX64.Code.Vm.FormBufAddTerm.Names

/-!
# `FormBuf::add_term` on x86-64

`b0` reads the count `n` (at most `148`, so its `ja` is not taken); the prologue `b1` pushes
RBX, R12-R15 and reads `t`'s degree `d`; no terms: on to `.L12`. The search (`.L5`, `Head j`)
compares term `j`'s degree with `d` (`b5`), then its columns with `t`'s, one word a turn (`.L7`,
`Inner j c`: `b7`, `b8`); a mismatch goes on to the next term (`.L9`, `b4`). A term with `t`'s
columns gets `c` added to its coefficient (`.L13`, `b11`: `found`); past the last term (`.L10`,
`b12`), the term is appended (`.L12`, `b14`: `push`) if there is room, else AL = `0` (`b13`). The
model's `addTerm` finds the same term (`addTerm_found`, `addTerm_none`). `b15` sets AL = `1`,
`b16` pops and returns (`finish`). The frame (`Transcript.Frame`, RSP at offset `0` in the body)
carries the pushed registers.
-/

namespace NativeRustcVmX64.Layout.FormBufAddTerm

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.FormBufAddTerm NativeVm.Model
open NativeRustcVm.Layout NativeRustcVmX64.Layout.Forms
open NativeRustcVmX64.Transcript (after after_eq exec_after infix_of Frame frameEnv)
open NativeRustcVmX64.Arrays (pc_cond regs_eq_of keepsRegs)
open NativeRustcVm.Transcript (off)
open NativeRustcVm (WordAt EWAt)

public section

/-! ## Arithmetic -/

theorem ofNat_beq {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x == BitVec.ofNat 64 y) = decide (x = y) :=
  NativeRustcX64.Sym.ofNat_beq hx hy

theorem ofNat_ult {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x).ult (BitVec.ofNat 64 y) = decide (x < y) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

/-- Two addresses of one range are equal iff their offsets are. -/
theorem addr_beq {b : BitVec 64} {x y : Nat} (hx' : x < 2 ^ 64) (hy' : y < 2 ^ 64) :
    (b + BitVec.ofNat 64 x == b + BitVec.ofNat 64 y) = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne]
    intro he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
    have := b.isLt
    omega

theorem toBitVec_toUInt64 (n : Nat) : n.toUInt64.toBitVec = BitVec.ofNat 64 n := rfl

/-- Sub-ranges of two apart ranges are apart. -/
theorem apart_offs {a c : BitVec 64} {N M o n o' n' : Nat} (h : NativeRustcVm.Apart a N c M)
    (ha : NativeRustcVm.NoWrap a N) (hc : NativeRustcVm.NoWrap c M) (h1 : o + n ≤ N)
    (h2 : o' + n' ≤ M) (hn : 0 < n) (hn' : 0 < n') :
    NativeRustcVm.Apart (a + BitVec.ofNat 64 o) n (c + BitVec.ofNat 64 o') n' := by
  unfold NativeRustcVm.NoWrap at ha hc
  unfold NativeRustcVm.Apart at h ⊢
  rw [NativeRustcVm.toNat_add_ofNat (a := a) (i := o) (by omega),
    NativeRustcVm.toNat_add_ofNat (a := c) (i := o') (by omega)]
  omega

/-! ## The state -/

/-- The buffer. -/
abbrev bb (m0 : MachineData) : BitVec 64 := reg m0 .rdi
/-- The term. -/
abbrev pp (m0 : MachineData) : BitVec 64 := reg m0 .rsi
/-- The coefficient added. -/
abbrev cc (m0 : MachineData) : EW := ewArg (reg m0 .rdx) (reg m0 .rcx)
/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := stackBelow m0 40

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 40 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide

/-- The facts of the precondition the blocks use. -/
structure Facts (f : FormW) (t : TermW) (m0 : MachineData) : Prop where
  stack : StackOk m0 40
  form : FormBufAt m0.dmem (bb m0) f
  term : TermWAt m0.dmem (pp m0) t
  bm : NativeRustcVm.Mapped m0.dmem (bb m0) 5928
  bn : NativeRustcVm.NoWrap (bb m0) 5928
  bo : NativeRustcVm.Apart (bb m0) 5928 (fb m0) (40 + 8)
  pm : NativeRustcVm.Mapped m0.dmem (pp m0) 40
  pn : NativeRustcVm.NoWrap (pp m0) 40
  po : NativeRustcVm.Apart (pp m0) 40 (fb m0) (40 + 8)
  apart : NativeRustcVm.Apart (bb m0) 5928 (pp m0) 40

theorem Facts.of_pre {f : FormW} {t : TermW} {m0 : MachineData} (h : FormBufAddTermPre f t m0) :
    Facts f t m0 := by
  obtain ⟨hS, hF, hT, ⟨bm, bn⟩, bo, ⟨pm, pn⟩, po, hA⟩ := h
  exact ⟨hS, hF, hT, bm, bn, bo, pm, pn, po, hA⟩

theorem Facts.size_le {f : FormW} {t : TermW} {m0 : MachineData} (h : Facts f t m0) :
    f.size ≤ 148 := h.form.len_le

theorem Facts.deg_le {f : FormW} {t : TermW} {m0 : MachineData} (h : Facts f t m0) :
    t.cols.size ≤ 2 := h.term.degree_le

theorem Facts.bnat {f : FormW} {t : TermW} {m0 : MachineData} (h : Facts f t m0) :
    (bb m0).toNat + 5928 ≤ 2 ^ 64 := h.bn

theorem Facts.fnw {f : FormW} {t : TermW} {m0 : MachineData} (h : Facts f t m0) :
    NativeRustcVm.NoWrap (fb m0) (40 + 8) := Transcript.frame_noWrap h.stack le_rfl

/-- A sub-range of the buffer is apart from the frame. -/
theorem Facts.bfr {f : FormW} {t : TermW} {m0 : MachineData} (h : Facts f t m0) {o n : Nat}
    (hon : o + n ≤ 5928) (hn : 0 < n) :
    NativeRustcVm.Apart (fb m0) (40 + 8) (bb m0 + BitVec.ofNat 64 o) n := by
  have := apart_offs (o' := 0) (n' := 48) h.bo h.bn h.fnw hon (by omega) hn (by omega)
  rw [BitVec.add_zero] at this
  exact Transcript.Apart.symm' this

/-- The term is apart from the frame. -/
theorem Facts.pfr {f : FormW} {t : TermW} {m0 : MachineData} (h : Facts f t m0) :
    NativeRustcVm.Apart (fb m0) (40 + 8) (pp m0) 40 := Transcript.Apart.symm' h.po

/-- **The body's registers and memory**: the frame, memory as at the entry outside the pushes,
the arguments, the count, the end of the terms, `t`'s degree. -/
structure Ctx (f : FormW) (t : TermW) (m0 st : MachineData) : Prop where
  frame : Frame m0 40 slots 0 st
  same : ∀ q, ¬InRange (fb m0) 40 q → st.dmem.get? q = m0.dmem.get? q
  rdi : reg st .rdi = bb m0
  rsi : reg st .rsi = pp m0
  rdx : reg st .rdx = reg m0 .rdx
  rcx : reg st .rcx = reg m0 .rcx
  rax : reg st .rax = BitVec.ofNat 64 f.size
  r8 : reg st .r8 = bb m0 + BitVec.ofNat 64 (8 + 40 * f.size)
  r9 : reg st .r9 = BitVec.ofNat 64 t.cols.size

/-- **The search's registers**: `t`'s columns (R11), its degree (RBX), `8` (R14). -/
structure Srch (f : FormW) (t : TermW) (m0 st : MachineData) : Prop extends Ctx f t m0 st where
  r11 : reg st .r11 = pp m0 + BitVec.ofNat 64 8
  rbx : reg st .rbx = BitVec.ofNat 64 t.cols.size
  r14 : reg st .r14 = BitVec.ofNat 64 8

/-- A quiet block keeps the context. -/
theorem Ctx.quiet [Labels] {f : FormW} {t : TermW} {m0 st st' : MachineData}
    {rest : List (BitVec 64 × Nat)} {S₀ S : SState} (hc : Ctx f t m0 st)
    (hwf : (frameEnv m0 st 40 rest).WF) (hm₀ : Match (frameEnv m0 st 40 rest) S₀ st)
    (hm : Match (frameEnv m0 st 40 rest) S st') (hq : Quiet S)
    (hk : keepsRegs S₀ S keepS = true) : Ctx f t m0 st' := by
  have e := regs_eq_of hm₀ hm hk
  have hd : st'.dmem = st.dmem := hm.dmem_eq hwf hq.2
  exact ⟨Frame.of_block hc.frame hwf hm hq.1 slots_le, fun q hq' ↦ by rw [hd]; exact hc.same q hq',
    (e .rdi (by simp [keepS])).trans hc.rdi, (e .rsi (by simp [keepS])).trans hc.rsi,
    (e .rdx (by simp [keepS])).trans hc.rdx, (e .rcx (by simp [keepS])).trans hc.rcx,
    (e .rax (by simp [keepS])).trans hc.rax, (e .r8 (by simp [keepS])).trans hc.r8,
    (e .r9 (by simp [keepS])).trans hc.r9⟩

/-- A quiet block keeps the search's registers. -/
theorem Srch.quiet [Labels] {f : FormW} {t : TermW} {m0 st st' : MachineData}
    {rest : List (BitVec 64 × Nat)} {S₀ S : SState} (hc : Srch f t m0 st)
    (hwf : (frameEnv m0 st 40 rest).WF) (hm₀ : Match (frameEnv m0 st 40 rest) S₀ st)
    (hm : Match (frameEnv m0 st 40 rest) S st') (hq : Quiet S)
    (hk : keepsRegs S₀ S keepL = true) : Srch f t m0 st' := by
  have e := regs_eq_of hm₀ hm hk
  have hk' : keepsRegs S₀ S keepS = true := by
    simp only [keepsRegs, keepL, List.all_append, Bool.and_eq_true] at hk ⊢; exact hk.1
  exact ⟨hc.toCtx.quiet hwf hm₀ hm hq hk', (e .r11 (by simp [keepL])).trans hc.r11,
    (e .rbx (by simp [keepL])).trans hc.rbx, (e .r14 (by simp [keepL])).trans hc.r14⟩

/-- The environment of a body block: the frame, then `rest`. -/
theorem Facts.wf {f : FormW} {t : TermW} {m0 st : MachineData} (hF : Facts f t m0)
    (hk : Kept m0.dmem st.dmem) {rest : List (BitVec 64 × Nat)}
    (hrest : ∀ x ∈ rest, NativeRustcVm.Mapped m0.dmem x.1 x.2 ∧ NativeRustcVm.NoWrap x.1 x.2)
    (hap : ((fb m0, 40 + 8) :: rest).Pairwise fun x y ↦ NativeRustcVm.Apart x.1 x.2 y.1 y.2) :
    (frameEnv m0 st 40 rest).WF :=
  Transcript.frame_wf ⟨NativeRustcVm.Transcript.Mapped.keeps
      (Transcript.frame_mapped hF.stack le_rfl) hk, hF.fnw⟩
    (fun x hx ↦ ⟨NativeRustcVm.Transcript.Mapped.keeps (hrest x hx).1 hk, (hrest x hx).2⟩) hap

/-- The frame alone. -/
theorem Facts.wf0 {f : FormW} {t : TermW} {m0 st : MachineData} (hF : Facts f t m0)
    (hk : Kept m0.dmem st.dmem) : (frameEnv m0 st 40 []).WF :=
  hF.wf hk (by simp) (List.pairwise_singleton _ _)

/-- Term `j`'s region. -/
theorem Facts.wf1 {f : FormW} {t : TermW} {m0 st : MachineData} (hF : Facts f t m0)
    (hk : Kept m0.dmem st.dmem) {j : Nat} (hj : j < 148) :
    (frameEnv m0 st 40 [(bb m0 + BitVec.ofNat 64 (8 + 40 * j), 40)]).WF :=
  hF.wf hk (by
      intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨hF.bm.sub (by omega), hF.bn.sub (by omega)⟩)
    (List.pairwise_pair.mpr (hF.bfr (by omega) (by omega)))

/-- Term `j`'s and `t`'s regions. -/
theorem Facts.wf2 {f : FormW} {t : TermW} {m0 st : MachineData} (hF : Facts f t m0)
    (hk : Kept m0.dmem st.dmem) {j : Nat} (hj : j < 148) :
    (frameEnv m0 st 40 [(bb m0 + BitVec.ofNat 64 (8 + 40 * j), 40), (pp m0, 40)]).WF :=
  hF.wf hk (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨hF.bm.sub (by omega), hF.bn.sub (by omega)⟩
      · exact ⟨hF.pm, hF.pn⟩)
    (Transcript.pairwise3 (hF.bfr (by omega) (by omega)) hF.pfr (by
      have := apart_offs (o := 8 + 40 * j) (n := 40) (o' := 0) (n' := 40) hF.apart hF.bn hF.pn
        (by omega) (by omega) (by omega) (by omega)
      rwa [BitVec.add_zero] at this))

/-- Term `j` of the buffer, in a body's memory. -/
theorem Ctx.termAt {f : FormW} {t : TermW} {m0 st : MachineData} (hF : Facts f t m0)
    (hc : Ctx f t m0 st) {j : Nat} (hj : j < f.size) :
    TermWAt st.dmem (bb m0 + BitVec.ofNat 64 (8 + 40 * j)) f[j] := by
  have := hF.form.terms j hj
  rw [term_addr] at this
  have hn := hF.size_le
  refine TermWAt.of_same this fun i hi ↦ hc.same _ fun h ↦ ?_
  have ha := hF.bfr (o := 8 + 40 * j + i) (n := 1) (by unfold termBytes at hi; omega) (by omega)
  have hfn := hF.fnw
  unfold NativeRustcVm.NoWrap at hfn
  unfold NativeRustcVm.Apart at ha
  rw [NativeRustcVm.addr_add_add] at h
  rw [Sym.inRange_iff (by omega)] at h
  omega

/-- `t`, in a body's memory. -/
theorem Ctx.tAt {f : FormW} {t : TermW} {m0 st : MachineData} (hF : Facts f t m0)
    (hc : Ctx f t m0 st) : TermWAt st.dmem (pp m0) t := by
  refine TermWAt.of_same hF.term fun i hi ↦ hc.same _ fun h ↦ ?_
  have ha := hF.pfr
  have hfn := hF.fnw
  have hpn : (pp m0).toNat + 40 ≤ 2 ^ 64 := hF.pn
  unfold NativeRustcVm.NoWrap at hfn
  unfold NativeRustcVm.Apart at ha
  unfold termBytes at hi
  rw [Sym.inRange_iff (by omega), NativeRustcVm.toNat_add_ofNat (a := pp m0) (i := i) (by omega)] at h
  omega

/-- The buffer, in a body's memory. -/
theorem Ctx.formAt {f : FormW} {t : TermW} {m0 st : MachineData} (hF : Facts f t m0)
    (hc : Ctx f t m0 st) : FormBufAt st.dmem (bb m0) f := by
  refine FormBufAt.of_same hF.form fun i hi ↦ hc.same _ fun h ↦ ?_
  have ha := hF.bo
  have hfn := hF.fnw
  have hb := hF.bnat
  unfold NativeRustcVm.NoWrap at hfn
  unfold NativeRustcVm.Apart at ha
  unfold formBufBytes formCap termBytes at hi
  rw [Sym.inRange_iff (by omega), NativeRustcVm.toNat_add_ofNat (a := bb m0) (i := i) (by omega)] at h
  omega

/-- **The search's head** `.L5`: terms before `j` have other columns. -/
structure Head (f : FormW) (t : TermW) (m0 : MachineData) (j : Nat) (st : MachineData) : Prop
    extends Srch f t m0 st where
  lt : j < f.size
  ne : ∀ j' (hj : j' < j), (f[j']'(Nat.lt_trans hj lt)).cols ≠ t.cols
  r10 : reg st .r10 = bb m0 + BitVec.ofNat 64 (8 + 40 * j)

/-- **At `.L9`**: terms up to `j` have other columns. -/
structure Next (f : FormW) (t : TermW) (m0 : MachineData) (j : Nat) (st : MachineData) : Prop
    extends Srch f t m0 st where
  lt : j < f.size
  ne : ∀ j' (hj : j' < j + 1), (f[j']'(Nat.lt_of_lt_of_le hj lt)).cols ≠ t.cols
  r10 : reg st .r10 = bb m0 + BitVec.ofNat 64 (8 + 40 * j)

/-- **The columns' comparison** `.L7`: term `j` has `t`'s degree, its first `c` columns are
`t`'s. -/
structure Inner (f : FormW) (t : TermW) (m0 : MachineData) (j c : Nat) (st : MachineData) :
    Prop extends Head f t m0 j st where
  deg : (f[j]'lt).cols.size = t.cols.size
  le : c ≤ t.cols.size
  pre : ∀ c' (hc : c' < c), (f[j]'lt).cols[c']'(by rw [deg]; omega) = t.cols[c']'(by omega)
  r12 : reg st .r12 = BitVec.ofNat 64 c
  r15 : reg st .r15 = bb m0 + BitVec.ofNat 64 (8 + 40 * j + 8)

/-- What the function leaves before its epilogue: the frame, AL and memory as the contract
says. -/
structure Done (f : FormW) (t : TermW) (m0 st : MachineData) : Prop where
  frame : Frame m0 40 slots 0 st
  res : let g := f.addTerm t.cols (cc m0)
    if g.size ≤ formCap then boolRet st = 1 ∧ FormBufAt st.dmem (bb m0) g else boolRet st = 0
  same : Changes m0 st formBufAddTermStack (bb m0) formBufBytes

variable [Host] {k : Nat}

/-- `add_term`'s postcondition, reached. -/
abbrev Post (f : FormW) (t : TermW) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ FormBufAddTermPost f t m0 st.data

/-- **The epilogue** `b16`. -/
theorem finish (hp : Placed code k) {f : FormW} {t : TermW} {m0 : MachineData}
    (hF : Facts f t m0) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddTerm.b16Offset))
    (hD : Done f t m0 st.data) : Eventually (step1 Host.exe) (Post f t m0) st := by
  have hwf := hF.wf0 hD.frame.kept (st := st.data)
  refine exec_at (infix_of b16_in_code (by simp [b16]) hp) run_b16 hwf nofun hpc
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hD.frame.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hepi, hmem, hax⟩ := after_eq run_b16 ▸ b16_facts
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hD.frame hwf hm' hepi
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf hmem
  have hal : boolRet st'.data = boolRet st.data := by
    unfold boolRet; rw [show reg st'.data .rax = _ from hm'.regs .rax _ hax]; rfl
  simp only [PcOk] at hpc'
  refine .done _ ⟨by rw [hpc']; exact hD.frame.load_ret hF.stack le_rfl, hrsp, ?_,
    fun q hq ↦ by rw [hd]; exact hD.same q hq, hsv⟩
  have hres := hD.res
  simp only at hres
  rw [hal, hd]
  exact hres

/-- **`b15`**: AL `1`, then the epilogue. -/
theorem ok (hp : Placed code k) {f : FormW} {t : TermW} {m0 : MachineData} (hF : Facts f t m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddTerm.b15Offset)) (hf : Frame m0 40 slots 0 st.data)
    (hle : (f.addTerm t.cols (cc m0)).size ≤ formCap)
    (hg : FormBufAt st.data.dmem (bb m0) (f.addTerm t.cols (cc m0)))
    (hs : Changes m0 st.data formBufAddTermStack (bb m0) formBufBytes) :
    Eventually (step1 Host.exe) (Post f t m0) st := by
  have hwf := hF.wf0 hf.kept (st := st.data)
  have hm : Match (frameEnv m0 st.data 40 []) regsS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b15_in_code (by simp [b15]) hp) run_b15 hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hq, hax⟩ := after_eq run_b15 ▸ b15_facts
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf hq.2
  simp only [PcOk] at hpc'
  refine finish hp hF (hpc'.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.FormBufAddTerm.b15_next)))
    ⟨Frame.of_block hf hwf hm' hq.1 slots_le, ?_, fun q hq' ↦ by rw [hd]; exact hs q hq'⟩
  simp only [hle, ↓reduceIte]
  refine ⟨?_, by rw [hd]; exact hg⟩
  unfold boolRet
  rw [show reg st'.data .rax = _ from hm'.regs .rax _ hax]
  exact Transcript.merge_one_mod _

omit [Host] in
/-- A region pointer's value. -/
theorem ptr_eval [Labels] {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {m : MachineData} {i o : Nat} {b : BitVec 64} {n : Nat} (hb : rs[i]? = some (b, n)) :
    (Sym.ptr i (o : Int)).eval (Env.ofMachine m rs vars ret) = b + BitVec.ofNat 64 o := by
  rw [Sym.eval, Env.base_ofMachine m rs vars ret hb, BitVec.ofInt_natCast]

/-- **No room**: `b13` sets AL = `0`; the model's form has `149` terms. -/
theorem full (hp : Placed code k) {f : FormW} {t : TermW} {m0 : MachineData} (hF : Facts f t m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddTerm.b13Offset)) (hc : Ctx f t m0 st.data)
    (hn : f.size = 148) (hne : ∀ j (hj : j < f.size), f[j].cols ≠ t.cols) :
    Eventually (step1 Host.exe) (Post f t m0) st := by
  have hwf := hF.wf0 hc.frame.kept (st := st.data)
  have hm : Match (frameEnv m0 st.data 40 []) regsS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hc.frame.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b13_in_code (by simp [b13]) hp) run_b13 hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hq, hax⟩ := after_eq run_b13 ▸ b13_facts
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf hq.2
  have hsize : (FormW.addTerm f t.cols (cc m0)).size = 149 := by
    rw [addTerm_none hne, Array.size_push, hn]
  simp only [PcOk] at hpc'
  refine finish hp hF (hpc'.trans (hp.label NativeRustcVmX64.Vm.FormBufAddTerm.label_15_at))
    ⟨Frame.of_block hc.frame hwf hm' hq.1 slots_le, ?_, fun q hq' ↦ by
      rw [hd]; exact hc.same q fun h ↦ hq' (Or.inr h)⟩
  have hle : ¬(FormW.addTerm f t.cols (cc m0)).size ≤ formCap := by
    rw [hsize]; unfold formCap; omega
  simp only [hle, ↓reduceIte]
  unfold boolRet
  rw [show reg st'.data .rax = _ from hm'.regs .rax _ hax]
  rfl

/-- **Room, a new monomial**: `b14` appends the term, the count plus one. -/
theorem push (hp : Placed code k) {f : FormW} {t : TermW} {m0 : MachineData} (hF : Facts f t m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddTerm.b14Offset)) (hc : Ctx f t m0 st.data)
    (hlt : f.size < 148) (hne : ∀ j (hj : j < f.size), f[j].cols ≠ t.cols) :
    Eventually (step1 Host.exe) (Post f t m0) st := by
  have hb := hF.bnat
  set n := f.size with hn
  set u := bb m0 + BitVec.ofNat 64 (8 + 40 * n) with hu
  have hk := hc.frame.kept
  let rest : List (BitVec 64 × Nat) := [(u, 40), (pp m0, 40), (bb m0, 8)]
  have a12 : NativeRustcVm.Apart u 40 (pp m0) 40 := by
    have := apart_offs (o := 8 + 40 * n) (n := 40) (o' := 0) (n' := 40) hF.apart hF.bn hF.pn
      (by omega) (by omega) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  have a13 : NativeRustcVm.Apart u 40 (bb m0) 8 := by
    have := NativeRustcVm.apart_of_le (a := bb m0) (N := 5928) (o := 8 + 40 * n) (n := 40)
      (o' := 0) (n' := 8) hF.bn (by omega) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  have a23 : NativeRustcVm.Apart (pp m0) 40 (bb m0) 8 := by
    have := apart_offs (o := 0) (n := 8) (o' := 0) (n' := 40) hF.apart hF.bn hF.pn
      (by omega) (by omega) (by omega) (by omega)
    rw [BitVec.add_zero, BitVec.add_zero] at this
    exact Transcript.Apart.symm' this
  have b0' : NativeRustcVm.Apart (fb m0) (40 + 8) (bb m0) 8 := by
    have := hF.bfr (o := 0) (n := 8) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  have hwf : (frameEnv m0 st.data 40 rest).WF := hF.wf hk (by
      intro x hx
      simp only [rest, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨hF.bm.sub (by omega), hF.bn.sub (by omega)⟩
      · exact ⟨hF.pm, hF.pn⟩
      · exact ⟨hF.bm.mono (by omega), hF.bn.mono (by omega)⟩)
    (List.Pairwise.cons (by
        intro e he
        simp only [rest, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        exacts [hF.bfr (by omega) (by omega), hF.pfr, b0'])
      (Transcript.pairwise3 a12 a13 a23))
  have hm : Match (frameEnv m0 st.data 40 rest) pushS st.data :=
    match_ofMachine ⟨rfl, rfl, rfl, rfl, trivial⟩
      ⟨hc.frame.rsp_eval, Transcript.known_ptr rfl hc.r8, Transcript.known_ptr rfl hc.rsi,
        Transcript.known_ptr rfl hc.rdi, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b14_in_code (by simp [b14]) hp) run_b14 hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hmid, hw, hwc, hw0, hw8, hw16, hw24, hw32⟩ := after_eq run_b14 ▸ b14_facts
  have hf' := Frame.of_block hc.frame hwf hm' hmid slots_le
  have hadd := addTerm_none (c := cc m0) hne
  have hsize : (FormW.addTerm f t.cols (cc m0)).size = n + 1 := by rw [hadd, Array.size_push]
  -- what `b14` wrote
  have hws : SameOutside st.data.dmem st'.data.dmem fun q ↦
      InRange (bb m0 + BitVec.ofNat 64 0) 8 q ∨ InRange (bb m0 + BitVec.ofNat 64 (8 + 40 * n)) 40 q :=
    fun q hq ↦ hm'.get?_mem0 hwf fun hW ↦ hq (by
      obtain ⟨e, he, hin⟩ := written_in hwf (rs := [(1, 40), (3, 8)])
        (by
          intro e he
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl
          · exact ⟨40, rfl, le_rfl⟩
          · exact ⟨8, rfl, le_rfl⟩)
        (fun w hw' ↦ by
          rcases hw w hw' with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨(1, 40), by simp, h1, h2⟩
          · exact ⟨(3, 8), by simp, h1, h2⟩) hW
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact Or.inr hin
      · rw [BitVec.add_zero]; exact Or.inl hin)
  have hlen : WordAt st'.data.dmem (bb m0) (n + 1).toUInt64 := by
    have := Arrays.wordAt_of_write hm' (r := 3) (o := 0) (b := bb m0) (sz := 8) rfl (by omega) hwc
    rw [BitVec.add_zero] at this
    convert this using 1
    apply UInt64.toBitVec_inj.mp
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show st.data.regs.get64 .rax = reg st.data .rax from rfl, hc.rax, toBitVec_toUInt64,
      BitVec.ofNat_add]
  have hT := hc.tAt hF
  have hld : ∀ {o : Nat} {w : UInt64}, WordAt st.data.dmem (pp m0 + BitVec.ofNat 64 o) w →
      (frameEnv m0 st.data 40 rest).load 2 o 8 = w.toBitVec := fun h ↦ Arrays.load_word h
  have hwd : ∀ {o : Nat} {v : Sym}, o + 8 ≤ 40 →
      (∀ i < 8, findWrite 1 (o + i) (after b14 pushS).mem = some (v, i)) →
      WordAt st'.data.dmem (u + BitVec.ofNat 64 o)
        (UInt64.ofBitVec (v.eval (frameEnv m0 st.data 40 rest))) := fun hle hw ↦
    Arrays.wordAt_of_write hm' (r := 1) rfl hle (after_eq run_b14 ▸ hw)
  have hnew : TermWAt st'.data.dmem u ⟨t.cols, 0 + cc m0⟩ := by
    refine ⟨hT.degree_le, ?_, hT.cols_lt, fun i hi ↦ ?_, ?_⟩
    · have := hwd (o := 0) (by omega) hw0
      rw [BitVec.add_zero] at this
      convert this using 1
      apply UInt64.toBitVec_inj.mp
      exact hc.r9.symm
    · have hd2 := hT.degree_le
      have hi' : i < t.cols.size := hi
      simp only [off]
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · have := hwd (o := 8) (by omega) hw8
        convert this using 1
        apply UInt64.toBitVec_inj.mp
        exact (hld (hT.cols 0 hi)).symm
      · have := hwd (o := 16) (by omega) hw16
        convert this using 1
        apply UInt64.toBitVec_inj.mp
        exact (hld (hT.cols 1 hi)).symm
    · rw [Forms.zero_add]
      simp only [off]
      have := Arrays.ewAt_of_writes hm' (r := 1) (o := 24) rfl (by omega) hw24 hw32
      simp only [Sym.eval, Env.ofMachine_regs] at this
      rw [show st.data.regs.get64 .rdx = reg st.data .rdx from rfl,
        show st.data.regs.get64 .rcx = reg st.data .rcx from rfl, hc.rdx, hc.rcx] at this
      exact this
  have hg : FormBufAt st'.data.dmem (bb m0) (FormW.addTerm f t.cols (cc m0)) := by
    rw [hadd]
    exact FormBufAt.push (hc.formAt hF) hlt hF.bn hlen hws hnew
  simp only [PcOk] at hpc'
  refine ok hp hF (hpc'.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.FormBufAddTerm.b14_next)))
    hf' (by rw [hsize]; unfold formCap; omega) hg fun q hq ↦ ?_
  rw [hws q fun h ↦ hq (Or.inl ?_)]
  · exact hc.same q fun h ↦ hq (Or.inr h)
  · show InRange (bb m0) 5928 q
    rcases h with h | h
    · exact NativeRustcVm.InRange.of_sub h hF.bn (by omega)
    · exact NativeRustcVm.InRange.of_sub h hF.bn (by omega)

/-- **A term with `t`'s columns**: `b11` adds `c` to its coefficient. -/
theorem found (hp : Placed code k) {f : FormW} {t : TermW} {m0 : MachineData} (hF : Facts f t m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddTerm.b11Offset)) (hc : Ctx f t m0 st.data) {j : Nat}
    (hj : j < f.size) (heq : f[j].cols = t.cols) (hne : ∀ j' (hj : j' < j), f[j'].cols ≠ t.cols)
    (h10 : reg st.data .r10 = bb m0 + BitVec.ofNat 64 (8 + 40 * j)) :
    Eventually (step1 Host.exe) (Post f t m0) st := by
  have hb := hF.bnat
  have hn := hF.size_le
  set u := bb m0 + BitVec.ofNat 64 (8 + 40 * j) with hu
  have hwf := hF.wf1 hc.frame.kept (st := st.data) (j := j) (by omega)
  have hm : Match (frameEnv m0 st.data 40 [(u, 40)]) foundS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hc.frame.rsp_eval, Transcript.known_ptr rfl h10, trivial⟩
      trivial trivial trivial
  refine exec_at (infix_of b11_in_code (by simp [b11]) hp) run_b11 hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hmid, hw, hw24, hw32⟩ := after_eq run_b11 ▸ b11_facts
  have hf' := Frame.of_block hc.frame hwf hm' hmid slots_le
  have hadd := addTerm_found (c := cc m0) hj heq hne
  have hT := hc.termAt hF hj
  have hunw : NativeRustcVm.NoWrap u 40 := hF.bn.sub (by omega)
  have hws : SameOutside st.data.dmem st'.data.dmem (InRange (u + BitVec.ofNat 64 24) 16) :=
    fun q hq ↦ hm'.get?_mem0 hwf fun ⟨w, hw', b', sz', hb', h1, h2⟩ ↦ hq (by
      obtain ⟨hr, h3, h4⟩ := hw w hw'
      rw [hr] at hb'
      simp only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Prod.mk.injEq] at hb'
      obtain ⟨rfl, rfl⟩ := hb'
      exact inRange_of_written hunw (by omega) h1 h2 h3 h4)
  have hcoef : EWAt st'.data.dmem (bb m0 + BitVec.ofNat 64 (8 + 40 * j + 24))
      (f[j].coeff + cc m0) := by
    have := Arrays.ewAt_of_writes hm' (r := 1) (o := 24) rfl (by omega) hw24 hw32
    rw [NativeRustcVm.addr_add_add] at this
    convert this using 1
    simp only [Sym.eval, Arrays.xor_eval, Env.ofMachine_regs]
    rw [Arrays.ewArg_xor, show st.data.regs.get64 .rdx = reg st.data .rdx from rfl,
      show st.data.regs.get64 .rcx = reg st.data .rcx from rfl, hc.rdx, hc.rcx]
    congr 1
    rw [← Arrays.ewOf_loads]
    exact (NativeRustcVm.ewOf_of_ewAt (by
      have := hT.coeff
      simp only [off] at this
      exact this)).symm
  have hg : FormBufAt st'.data.dmem (bb m0) (FormW.addTerm f t.cols (cc m0)) := by
    rw [hadd]
    exact FormBufAt.modify hj (hc.formAt hF) hF.bn _ rfl
      (by rw [hu, NativeRustcVm.addr_add_add] at hws; exact hws) hcoef
  simp only [PcOk] at hpc'
  refine ok hp hF (hpc'.trans (hp.label NativeRustcVmX64.Vm.FormBufAddTerm.label_14_at)) hf'
    (by rw [hadd, Array.size_modify]; exact hF.form.len_le) hg fun q hq ↦ ?_
  rw [hws q fun h ↦ hq (Or.inl ?_)]
  · exact hc.same q fun h ↦ hq (Or.inr h)
  · show InRange (bb m0) 5928 q
    rw [hu, NativeRustcVm.addr_add_add] at h
    exact NativeRustcVm.InRange.of_sub h hF.bn (by omega)

/-- What a turn of the search reaches: the end, or the head at the next term. -/
abbrev Turn (f : FormW) (t : TermW) (m0 : MachineData) (j : Nat) (st : MachineState) : Prop :=
  Post f t m0 st ∨ (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddTerm.b5Offset) ∧ Head f t m0 (j + 1) st.data)

omit [Host] in
/-- The frame-only state of a body. -/
theorem match_regs [Labels] {f : FormW} {t : TermW} {m0 st : MachineData} (hc : Ctx f t m0 st) :
    Match (frameEnv m0 st 40 []) regsS st :=
  match_ofMachine ⟨rfl, trivial⟩ ⟨hc.frame.rsp_eval, trivial⟩ trivial trivial trivial

/-- **`.L9`** (`b4`): past the last term, `b12` appends or fails; else the head at the next term. -/
theorem next (hp : Placed code k) {f : FormW} {t : TermW} {m0 : MachineData} (hF : Facts f t m0)
    {j : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddTerm.b4Offset))
    (hN : Next f t m0 j st.data) : Eventually (step1 Host.exe) (Turn (k := k) f t m0 j) st := by
  have hb := hF.bnat
  have hn := hF.size_le
  have hlt := hN.lt
  have hwf := hF.wf0 hN.frame.kept (st := st.data)
  have hm := match_regs hN.toCtx
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf nofun hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hq, hk, h10, hzf⟩ := after_eq run_b4 ▸ b4_facts
  have hs1 := hN.toSrch.quiet hwf hm hm1 hq hk
  have hr10 : reg st1.data .r10 = bb m0 + BitVec.ofNat 64 (8 + 40 * (j + 1)) := by
    rw [show reg st1.data .r10 = _ from hm1.regs .r10 _ h10]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show st.data.regs.get64 .r10 = reg st.data .r10 from rfl, hN.r10, BitVec.add_comm,
      BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
  simp only [PcOk] at hpc1
  obtain ⟨hy, hn'⟩ := pc_cond hpc1
  simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
    Env.ofMachine_regs] at hy hn'
  rw [show st.data.regs.get64 .r10 = reg st.data .r10 from rfl, hN.r10,
    show st.data.regs.get64 .r8 = reg st.data .r8 from rfl, hN.r8, BitVec.add_comm,
    BitVec.add_assoc, ← BitVec.ofNat_add, addr_beq (by omega) (by omega)] at hy hn'
  by_cases hend : j + 1 = f.size
  · have hpc2 := (hy (by simp; omega)).trans (hp.label NativeRustcVmX64.Vm.FormBufAddTerm.label_10_at)
    have hne : ∀ j' (hj : j' < f.size), f[j'].cols ≠ t.cols := fun j' hj ↦ hN.ne j' (by omega)
    -- `b12`
    have hwf2 := hF.wf0 hs1.frame.kept (st := st1.data)
    have hm2 := match_regs hs1.toCtx
    refine exec_at (infix_of b12_in_code (by simp [b12]) hp) run_b12 hwf2 nofun hpc2 hm2
      fun st2 hm2' hpc3 ↦ ?_
    obtain ⟨hq2, hk2, hzf2⟩ := after_eq run_b12 ▸ b12_facts
    have hc2 := (hs1.quiet hwf2 hm2 hm2' hq2 hk2).toCtx
    simp only [PcOk] at hpc3
    obtain ⟨hy3, hn3⟩ := pc_cond hpc3
    simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs] at hy3 hn3
    rw [show st1.data.regs.get64 .rax = reg st1.data .rax from rfl, hs1.rax,
      ofNat_beq (by omega) (by omega)] at hy3 hn3
    by_cases h148 : f.size = 148
    · exact Eventually.mono (full hp hF ((hn3 (by simpa using h148)).trans
        (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.FormBufAddTerm.b12_next))) hc2 h148 hne)
        fun _ h ↦ Or.inl h
    · exact Eventually.mono (push hp hF ((hy3 (by simpa using h148)).trans
        (hp.label NativeRustcVmX64.Vm.FormBufAddTerm.label_12_at)) hc2 (by omega) hne) fun _ h ↦ Or.inl h
  · have hpc2 := hn' (by simp; omega)
    exact .done _ (Or.inr ⟨hpc2.trans (congrArg Host.addrOf
      (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.FormBufAddTerm.b4_next])), hs1, by omega, fun j' hj ↦ hN.ne j' hj, hr10⟩)

omit [Host] in
theorem toUInt64_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : a.toUInt64 = b.toUInt64) : a = b := by
  have := congrArg UInt64.toNat h
  simp only [Nat.toUInt64, UInt64.toNat_ofNat'] at this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

omit [Host] in
theorem toBitVec_inj' {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (a.toUInt64.toBitVec == b.toUInt64.toBitVec) = decide (a = b) := by
  rw [toBitVec_toUInt64, toBitVec_toUInt64, ofNat_beq ha hb]

/-- **A turn of the columns' comparison** `.L7`: all columns equal (`found`), a mismatch (`.L9`),
or the next column. -/
theorem inner_step (hp : Placed code k) {f : FormW} {t : TermW} {m0 : MachineData}
    (hF : Facts f t m0) {j c : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddTerm.b7Offset))
    (hI : Inner f t m0 j c st.data) :
    Eventually (step1 Host.exe) (fun s ↦ Turn (k := k) f t m0 j s ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddTerm.b7Offset) ∧ Inner f t m0 j (c + 1) s.data)) st := by
  have hb := hF.bnat
  have hn := hF.size_le
  have hd2 := hF.deg_le
  have hlt := hI.lt
  have hwf := hF.wf0 hI.frame.kept (st := st.data)
  have hm := match_regs hI.toCtx
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) run_b7 hwf nofun hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hq, hk, hzf⟩ := after_eq run_b7 ▸ b7_facts
  have hk' : keepsRegs regsS (after b7 regsS) keepL = true := by
    simp only [keepsRegs, List.all_cons, Bool.and_eq_true] at hk ⊢; exact hk.2.2.2
  have hs1 := hI.toSrch.quiet hwf hm hm1 hq hk'
  have e1 := regs_eq_of hm hm1 hk
  simp only [PcOk] at hpc1
  obtain ⟨hy, hn'⟩ := pc_cond hpc1
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs] at hy hn'
  rw [show st.data.regs.get64 .rbx = reg st.data .rbx from rfl, hI.rbx,
    show st.data.regs.get64 .r12 = reg st.data .r12 from rfl, hI.r12,
    ofNat_beq (by omega) (by have := hI.le; omega)] at hy hn'
  have hdeg := hI.deg
  by_cases hend : t.cols.size = c
  · -- all columns equal
    have heq : f[j].cols = t.cols := Array.ext hdeg fun c' h1 h2 ↦ hI.pre c' (by omega)
    exact Eventually.mono (found hp hF ((hy (by simpa using hend)).trans (hp.label NativeRustcVmX64.Vm.FormBufAddTerm.label_13_at))
      hs1.toCtx hlt heq (fun j' hj ↦ hI.ne j' hj) ((e1 .r10 (by simp)).trans hI.r10))
      fun _ h ↦ Or.inl (Or.inl h)
  have hcl : c < t.cols.size := by have := hI.le; omega
  have hpc2 := hn' (by simpa using hend)
  -- `b8`: column `c`
  have hwf2 := hF.wf2 hs1.frame.kept (st := st1.data) (j := j) (by omega)
  have hr15 : reg st1.data .r15 = (bb m0 + BitVec.ofNat 64 (8 + 40 * j)) + BitVec.ofNat 64 8 := by
    rw [e1 .r15 (by simp), hI.r15, NativeRustcVm.addr_add_add]
  have hr12 : reg st1.data .r12 = BitVec.ofNat 64 c := (e1 .r12 (by simp)).trans hI.r12
  have hm2 : Match (frameEnv m0 st1.data 40 [((bb m0 + BitVec.ofNat 64 (8 + 40 * j)), 40), (pp m0, 40)]) colS st1.data := by
    refine match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hs1.frame.rsp_eval, ?_, ?_, trivial⟩ trivial
      ⟨?_, trivial⟩ trivial
    · show reg st1.data .r15 = (Sym.ptr 1 ((8 : Nat) : Int)).eval _
      rw [ptr_eval rfl]; exact hr15
    · show reg st1.data .r11 = (Sym.ptr 2 ((8 : Nat) : Int)).eval _
      rw [ptr_eval rfl]; exact hs1.r11
    · show (reg st1.data .r12).toNat < 2
      rw [hr12, BitVec.toNat_ofNat]; omega
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8 hwf2 nofun
    (hpc2.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.FormBufAddTerm.b7_next))) hm2
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hq3, hk3, h12', hzf3⟩ := after_eq run_b8 ▸ b8_facts
  have hk3' : keepsRegs colS (after b8 colS) keepL = true := by
    simp only [keepsRegs, List.all_cons, Bool.and_eq_true] at hk3 ⊢; exact hk3.2.2
  have hs3 := hs1.quiet hwf2 hm2 hm3 hq3 hk3'
  have e3 := regs_eq_of hm2 hm3 hk3
  have hT := hs1.termAt hF hlt
  have htt := hs1.tAt hF
  have hidx : (BinOp.apply .mul .W64 ((frameEnv m0 st1.data 40
      [((bb m0 + BitVec.ofNat 64 (8 + 40 * j)), 40), (pp m0, 40)]).regs .r12)
      (BitVec.ofNat 64 8)).toNat = 8 * c := by
    simp only [BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, BitVec.toNat_mul,
      BitVec.toNat_ofNat]
    rw [show st1.data.regs.get64 .r12 = reg st1.data .r12 from rfl, hr12, BitVec.toNat_ofNat]
    omega
  have hcj : c < (f[j]'hlt).cols.size := by rw [hdeg]; exact hcl
  have l1 : (frameEnv m0 st1.data 40 [((bb m0 + BitVec.ofNat 64 (8 + 40 * j)), 40), (pp m0, 40)]).load 1 (8 + 8 * c) 8 =
      ((f[j]'hlt).cols[c]'hcj).toUInt64.toBitVec := Arrays.load_word (hT.cols c hcj)
  have l2 : (frameEnv m0 st1.data 40 [((bb m0 + BitVec.ofNat 64 (8 + 40 * j)), 40), (pp m0, 40)]).load 2 (8 + 8 * c) 8 =
      (t.cols[c]'hcl).toUInt64.toBitVec := Arrays.load_word (htt.cols c hcl)
  simp only [PcOk] at hpc3
  obtain ⟨hy3, hn3⟩ := pc_cond hpc3
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64] at hy3 hn3
  rw [hidx, l1, l2, toBitVec_inj' (hT.cols_lt c hcj) (htt.cols_lt c hcl)] at hy3 hn3
  have hr12' : reg st3.data .r12 = BitVec.ofNat 64 (c + 1) := by
    rw [show reg st3.data .r12 = _ from hm3.regs .r12 _ h12']
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show st1.data.regs.get64 .r12 = reg st1.data .r12 from rfl, hr12, BitVec.ofNat_add]
  by_cases hceq : (f[j]'hlt).cols[c]'hcj = t.cols[c]'hcl
  · refine .done _ (Or.inr ⟨(hy3 (by simpa using hceq)).trans (hp.label NativeRustcVmX64.Vm.FormBufAddTerm.label_7_at),
      ⟨⟨hs3, hlt, fun j' hj ↦ hI.ne j' hj, (e3 .r10 (by simp)).trans (by
        rw [e1 .r10 (by simp)]; exact hI.r10)⟩, hdeg, by omega, fun c' hc' ↦ ?_, hr12',
        (e3 .r15 (by simp)).trans (by rw [hr15, NativeRustcVm.addr_add_add])⟩⟩)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc' with h | h
    · exact hI.pre c' h
    · subst h; exact hceq
  · -- a mismatch: `b9`, then `.L9`
    have hpc4 := hn3 (by simpa using hceq)
    have hwf4 := hF.wf0 hs3.frame.kept (st := st3.data)
    have hm4 := match_regs hs3.toCtx
    refine exec_at (infix_of b9_in_code (by simp [b9]) hp) run_b9 hwf4 nofun
      (hpc4.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.FormBufAddTerm.b8_next))) hm4
      fun st5 hm5 hpc5 ↦ ?_
    obtain ⟨hq5, hk5⟩ := after_eq run_b9 ▸ b9_facts
    have hk5' : keepsRegs regsS (after b9 regsS) keepL = true := by
      simp only [keepsRegs, List.all_cons, Bool.and_eq_true] at hk5 ⊢; exact hk5.2
    have hs5 := hs3.quiet hwf4 hm4 hm5 hq5 hk5'
    have e5 := regs_eq_of hm4 hm5 hk5
    simp only [PcOk] at hpc5
    refine Eventually.mono (next hp hF (hpc5.trans (hp.label NativeRustcVmX64.Vm.FormBufAddTerm.label_9_at))
      ⟨hs5, hlt, fun j' hj ↦ ?_, ?_⟩) fun _ h ↦ Or.inl h
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact hI.ne j' h
      · subst h
        intro he
        exact hceq (by simp [he])
    · rw [e5 .r10 (by simp), e3 .r10 (by simp), e1 .r10 (by simp)]; exact hI.r10

/-- **The search's head** `.L5` (`b5`, `b6`): another degree goes on to `.L9`; else the columns'
comparison. -/
theorem head_step (hp : Placed code k) {f : FormW} {t : TermW} {m0 : MachineData}
    (hF : Facts f t m0) {j : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddTerm.b5Offset))
    (hH : Head f t m0 j st.data) :
    Eventually (step1 Host.exe) (fun s ↦ Turn (k := k) f t m0 j s ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddTerm.b7Offset) ∧ Inner f t m0 j 0 s.data)) st := by
  have hb := hF.bnat
  have hn := hF.size_le
  have hd2 := hF.deg_le
  have hlt := hH.lt
  have hwf := hF.wf1 hH.frame.kept (st := st.data) (j := j) (by omega)
  have hm : Match (frameEnv m0 st.data 40 [((bb m0 + BitVec.ofNat 64 (8 + 40 * j)), 40)]) degS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hH.frame.rsp_eval, Transcript.known_ptr rfl hH.r10, trivial⟩
      trivial trivial trivial
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 hwf nofun hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hq, hk, hzf⟩ := after_eq run_b5 ▸ b5_facts
  have hk' : keepsRegs degS (after b5 degS) keepL = true := by
    simp only [keepsRegs, List.all_cons, Bool.and_eq_true] at hk ⊢; exact hk.2
  have hs1 := hH.toSrch.quiet hwf hm hm1 hq hk'
  have e1 := regs_eq_of hm hm1 hk
  have hT := hH.termAt hF hlt
  have l0 : (frameEnv m0 st.data 40 [((bb m0 + BitVec.ofNat 64 (8 + 40 * j)), 40)]).load 1 0 8 =
      (f[j]'hlt).cols.size.toUInt64.toBitVec := Arrays.load_word (by
    rw [show (frameEnv m0 st.data 40 [((bb m0 + BitVec.ofNat 64 (8 + 40 * j)), 40)]).base 1 = (bb m0 + BitVec.ofNat 64 (8 + 40 * j)) from rfl, BitVec.add_zero]
    exact hT.degree)
  have hdj := hT.degree_le
  simp only [PcOk] at hpc1
  obtain ⟨hy, hn'⟩ := pc_cond hpc1
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs] at hy hn'
  rw [l0, show st.data.regs.get64 .r9 = reg st.data .r9 from rfl, hH.r9, ← toBitVec_toUInt64,
    toBitVec_inj' (by omega) (by omega)] at hy hn'
  have hr10 : reg st1.data .r10 = (bb m0 + BitVec.ofNat 64 (8 + 40 * j)) := (e1 .r10 (by simp)).trans hH.r10
  by_cases hdeg : (f[j]'hlt).cols.size = t.cols.size
  · have hpc2 := hn' (by simpa using hdeg)
    -- `b6`
    have hwf2 := hF.wf0 hs1.frame.kept (st := st1.data)
    have hm2 := match_regs hs1.toCtx
    refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 hwf2 nofun
      (hpc2.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.FormBufAddTerm.b5_next))) hm2
      fun st3 hm3 hpc3 ↦ ?_
    obtain ⟨hq3, hk3, h15, h12⟩ := after_eq run_b6 ▸ b6_facts
    have hk3' : keepsRegs regsS (after b6 regsS) keepL = true := by
      simp only [keepsRegs, List.all_cons, Bool.and_eq_true] at hk3 ⊢; exact hk3.2
    have hs3 := hs1.quiet hwf2 hm2 hm3 hq3 hk3'
    have e3 := regs_eq_of hm2 hm3 hk3
    simp only [PcOk] at hpc3
    refine .done _ (Or.inr ⟨hpc3.trans (congrArg Host.addrOf
      (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.FormBufAddTerm.b6_next])), ⟨⟨hs3, hlt, fun j' hj ↦ hH.ne j' hj,
        (e3 .r10 (by simp)).trans hr10⟩, hdeg, by omega, fun c' hc' ↦ absurd hc' (by omega),
        hm3.regs .r12 _ h12, ?_⟩⟩)
    rw [show reg st3.data .r15 = _ from hm3.regs .r15 _ h15]
    simp only [Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
      Env.ofMachine_regs]
    rw [show st1.data.regs.get64 .r9 = reg st1.data .r9 from rfl, hs1.r9,
      show st1.data.regs.get64 .r10 = reg st1.data .r10 from rfl, hr10,
      ofNat_ult (by omega) (by omega)]
    simp only [show t.cols.size < 3 by omega, decide_true, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte]
    rw [NativeRustcVm.addr_add_add]
  · have hpc2 := (hy (by simpa using hdeg)).trans (hp.label NativeRustcVmX64.Vm.FormBufAddTerm.label_9_at)
    exact Eventually.mono (next hp hF hpc2 ⟨hs1, hlt, fun j' hj ↦ by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · exact hH.ne j' h
        · subst h
          intro he
          exact hdeg (by rw [he]), hr10⟩) fun _ h ↦ Or.inl h

/-- **A turn of the search**: from the head at term `j`, the end or the head at `j + 1`. -/
theorem turn (hp : Placed code k) {f : FormW} {t : TermW} {m0 : MachineData} (hF : Facts f t m0)
    {j : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddTerm.b5Offset))
    (hH : Head f t m0 j st.data) : Eventually (step1 Host.exe) (Turn (k := k) f t m0 j) st := by
  refine Eventually.bind (head_step hp hF hpc hH) fun s h ↦ ?_
  rcases h with h | ⟨hpc', hI⟩
  · exact .done _ h
  · refine Sym.loop (fun n s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddTerm.b7Offset) ∧ ∃ c, t.cols.size - c = n ∧
      Inner f t m0 j c s.data) (fun n s ⟨hpc, c, hn, hI⟩ ↦ ?_) ⟨hpc', 0, rfl, hI⟩
    refine Eventually.mono (inner_step hp hF hpc hI) fun s' h ↦ ?_
    rcases h with h | ⟨hpc'', hI'⟩
    · exact Or.inl h
    · exact Or.inr ⟨t.cols.size - (c + 1), by have := hI'.le; omega, hpc'', c + 1, rfl, hI'⟩

/-- **`FormBuf::add_term`'s contract.** -/
theorem formBufAddTerm_spec (hp : Placed code k) (f : FormW) (t : TermW) :
    Spec (Labels.label NativeRustcVmX64.Vm.FormBufAddTerm.entryLabel) (FormBufAddTermPre f t) (FormBufAddTermPost f t) := by
  intro m0 hpre
  have hF := Facts.of_pre hpre
  have hb := hF.bnat
  have hn := hF.size_le
  have hd2 := hF.deg_le
  rw [show Labels.label NativeRustcVmX64.Vm.FormBufAddTerm.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddTerm.b0Offset) from hp.label NativeRustcVmX64.Vm.FormBufAddTerm.entry_at]
  let rest : List (BitVec 64 × Nat) := [(bb m0, 8), (pp m0, 40)]
  have b0' : NativeRustcVm.Apart (fb m0) (40 + 8) (bb m0) 8 := by
    have := hF.bfr (o := 0) (n := 8) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  have a12 : NativeRustcVm.Apart (bb m0) 8 (pp m0) 40 := by
    have := apart_offs (o := 0) (n := 8) (o' := 0) (n' := 40) hF.apart hF.bn hF.pn
      (by omega) (by omega) (by omega) (by omega)
    rwa [BitVec.add_zero, BitVec.add_zero] at this
  have hwf : (frameEnv m0 m0 40 rest).WF := hF.wf (fun _ h ↦ h) (by
      intro x hx
      simp only [rest, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨hF.bm.mono (by omega), hF.bn.mono (by omega)⟩
      · exact ⟨hF.pm, hF.pn⟩)
    (Transcript.pairwise3 b0' hF.pfr a12)
  have hm : Match (frameEnv m0 m0 40 rest) entryS m0 :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨Transcript.match_rsp, Transcript.known_ptr rfl rfl,
      Transcript.known_ptr rfl rfl, trivial⟩ trivial trivial trivial
  have hcnt : (frameEnv m0 m0 40 rest).load 1 0 8 = BitVec.ofNat 64 f.size := by
    refine (Arrays.load_word ?_).trans (toBitVec_toUInt64 _)
    rw [show (frameEnv m0 m0 40 rest).base 1 = bb m0 from rfl, BitVec.add_zero]
    exact hF.form.len
  have hdeg : (frameEnv m0 m0 40 rest).load 2 0 8 = BitVec.ofNat 64 t.cols.size := by
    refine (Arrays.load_word ?_).trans (toBitVec_toUInt64 _)
    rw [show (frameEnv m0 m0 40 rest).base 2 = pp m0 from rfl, BitVec.add_zero]
    exact hF.term.degree
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf nofun hm
    fun st0 hm0 hpc0 ↦ ?_
  simp only [PcOk, NativeRustcVmX64.Vm.FormBufAddTerm.b0_length] at hpc0
  obtain ⟨-, hn0⟩ := pc_cond hpc0
  have hpc1 := hn0 (by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, hcnt]
    rw [ofNat_ult (x := f.size) (y := 148) (by omega) (by omega),
      ofNat_beq (x := f.size) (y := 148) (by omega) (by omega)]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_and, not_not]
    omega)
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) (exec_after run_b0 run_b1) hwf nofun hpc1
    hm0 fun st1 hm1 hpc2 ↦ ?_
  obtain ⟨hpro, hw, h8, h9, hax, hdi, hsi, hdx, hcx, hzf⟩ := after_eq run_b1 ▸ b1_facts
  have hf1 := Frame.of_prologue (Frame.entry (m0 := m0) (F := 40)) hwf hm1 hpro slots_le slots_cs
  have hc1 : Ctx f t m0 st1.data := by
    refine ⟨hf1, fun q hq ↦ hm1.get?_mem0 hwf fun hW ↦ hq ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Arrays.written_region0 (k := 40) rfl hwf (by omega) hw hW
    · rw [show reg st1.data .rdi = _ from hm1.regs .rdi _ hdi]; exact Transcript.eval_ptr rfl
    · rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hsi]; exact Transcript.eval_ptr rfl
    · exact hm1.regs .rdx _ hdx
    · exact hm1.regs .rcx _ hcx
    · rw [show reg st1.data .rax = _ from hm1.regs .rax _ hax]; exact hcnt
    · rw [show reg st1.data .r8 = _ from hm1.regs .r8 _ h8]
      simp only [r8S, nS, Sym.eval, BinOp.apply, low_W64, ext_W64, hcnt]
      rw [show (frameEnv m0 m0 40 rest).base 1 + BitVec.ofInt 64 0 = bb m0 by
        rw [Transcript.ofInt_zero64, BitVec.add_zero]; rfl]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
        show Width.W64.bits = 64 from rfl]
      omega
    · rw [show reg st1.data .r9 = _ from hm1.regs .r9 _ h9]; exact hdeg
  simp only [PcOk] at hpc2
  obtain ⟨hy, hn'⟩ := pc_cond hpc2
  simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, hcnt,
    BitVec.and_self] at hy hn'
  rw [ofNat_beq (by omega) (by omega)] at hy hn'
  by_cases hz : f.size = 0
  · exact push hp hF ((hy (by simpa using hz)).trans (hp.label NativeRustcVmX64.Vm.FormBufAddTerm.label_12_at)) hc1 (by omega)
      fun j hj ↦ absurd hj (by omega)
  have hpc3 := hn' (by simpa using hz)
  -- `b2`
  have hwf2 := hF.wf0 hc1.frame.kept (st := st1.data)
  have hm2 := match_regs hc1
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf2 nofun
    (hpc3.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.FormBufAddTerm.b1_next))) hm2
    fun st2 hm2' hpc4 ↦ ?_
  obtain ⟨hq, hk, h10, h11, hbx, h14⟩ := after_eq run_b2 ▸ b2_facts
  have hc2 := hc1.quiet hwf2 hm2 hm2' hq hk
  have hlt3 : CmpOp.apply .ult .W64 ((frameEnv m0 st1.data 40 []).regs .r9)
      (BitVec.ofNat 64 3) = true := by
    show CmpOp.apply .ult .W64 (reg st1.data .r9) _ = true
    rw [hc1.r9]; simp only [CmpOp.apply, low_W64]
    rw [ofNat_ult (x := t.cols.size) (y := 3) (by omega) (by omega)]
    simpa using (show t.cols.size < 3 by omega)
  have hH : Head f t m0 0 st2.data := by
    refine ⟨⟨hc2, ?_, ?_, hm2'.regs .r14 _ h14⟩, Nat.pos_of_ne_zero hz, fun j' hj ↦ absurd hj (by omega), ?_⟩
    · rw [show reg st2.data .r11 = _ from hm2'.regs .r11 _ h11]
      simp only [Sym.eval, SBool.eval, BinOp.apply, low_W64, ext_W64, hlt3, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte]
      show reg st1.data .rsi + _ = _
      rw [hc1.rsi]
    · rw [show reg st2.data .rbx = _ from hm2'.regs .rbx _ hbx]
      simp only [Sym.eval, SBool.eval, hlt3, ↓reduceIte]
      exact hc1.r9
    · rw [show reg st2.data .r10 = _ from hm2'.regs .r10 _ h10]
      simp only [Sym.eval, Env.ofMachine_regs, BinOp.apply, low_W64, ext_W64]
      rw [show st1.data.regs.get64 .rdi = reg st1.data .rdi from rfl, hc1.rdi]
  simp only [PcOk] at hpc4
  refine Sym.loop (fun n s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddTerm.b5Offset) ∧ ∃ j, f.size - j = n ∧
      Head f t m0 j s.data) (fun n s ⟨hpc, j, hnj, hH⟩ ↦ ?_)
    ⟨hpc4.trans (hp.label NativeRustcVmX64.Vm.FormBufAddTerm.label_5_at), 0, rfl, hH⟩
  refine Eventually.mono (turn hp hF hpc hH) fun s' h ↦ ?_
  rcases h with h | ⟨hpc', hH'⟩
  · exact Or.inl h
  · exact Or.inr ⟨f.size - (j + 1), by have := hH'.lt; omega, hpc', j + 1, rfl, hH'⟩

end

end NativeRustcVmX64.Layout.FormBufAddTerm
