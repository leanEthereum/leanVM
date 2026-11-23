module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.FormBufAddScaled.Names
public import NativeRustcVmArm.Code.Vm.FormBufAddTerm.Names
public import NativeRustcVmArm.Layout.FormBufAddScaled.Exec
public import NativeRustcVmArm.Layout.FormBufAddTerm.Lemmas

/-!
# `FormBuf::add_scaled`

No terms (`b0`): `b7` returns `1`. Else the prologue (`b1`) saves X19-X23 and X30 in its 48-byte
frame; the loop (`.L2`, `Inv i`: `i` terms added, the form at X0 the model's fold over them,
`acc`) multiplies term `i`'s coefficient by the weight (`b2`, `EW::mul`) and adds it to the form
(`b3`, `FormBuf::add_term`); `None` (`b4`) leaves the loop with `0`, the model's form then too
large (`le_size_addScaled`); past the last term (`b5`) the epilogue (`b6`) returns `1`.
-/

namespace NativeRustcVmArm.Layout.FormBufAddScaled

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.FormBufAddScaled
open NativeVm.Model NativeRustcVm.Layout NativeRustcVmArm.Layout.Forms
open NativeRustcVm.Transcript (off)
open NativeRustcVm (WordAt EWAt addr_add_add addr_add_zero toNat_add_ofNat)
open NativeRustcVmArm.Arrays (Body calleeRegs inSlots keepsAll restores)

public section

/-! ## The model -/

/-- One term added to the fold. -/
abbrev stepT (w : EW) (a : FormW) (t : TermW) : FormW := FormW.addTerm a t.cols (w * t.coeff)

/-- The fold after `i` terms. -/
def acc (f other : FormW) (w : EW) (i : Nat) : FormW := (other.toList.take i).foldl (stepT w) f

theorem acc_zero (f other : FormW) (w : EW) : acc f other w 0 = f := by simp [acc]

theorem acc_succ (f other : FormW) (w : EW) {i : Nat} (hi : i < other.size) :
    acc f other w (i + 1) = stepT w (acc f other w i) other[i] := by
  unfold acc
  rw [List.take_succ_eq_append_getElem (by simpa using hi), List.foldl_append]
  simp

theorem acc_size (f other : FormW) (w : EW) : acc f other w other.size = f.addScaled other w := by
  unfold acc FormW.addScaled
  rw [← Array.foldl_toList, ← Array.length_toList, List.take_length]

/-- The fold never shrinks. -/
theorem le_size_addScaled (f other : FormW) (w : EW) (i : Nat) :
    (acc f other w i).size ≤ (f.addScaled other w).size := by
  unfold acc FormW.addScaled
  rw [← Array.foldl_toList, ← List.take_append_drop i other.toList, List.foldl_append,
    List.take_append_drop]
  exact le_size_foldl_addTerm _ _ _

/-! ## The state -/

/-- The buffer. -/
abbrev bb (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
/-- The terms added. -/
abbrev pp (m0 : MachineData) : BitVec 64 := m0.regs.X1.toBitVec
/-- The weight. -/
abbrev ww (m0 : MachineData) : EW := ewArg m0.regs.X3 m0.regs.X4

/-- The stack. -/
abbrev SS : Nat := formBufAddScaledStack

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 48 := by decide

/-- **The loop head** `.L2`: `i` terms added. -/
structure Inv (f other : FormW) (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  body : Body m0 48 SS slots (bb m0) formBufBytes st
  lt : i < other.size
  x8 : st.regs.X8.toNat = 40 * (other.size - 1 - i)
  x19 : st.regs.X19 = m0.regs.X4
  x20 : st.regs.X20 = m0.regs.X3
  x21 : st.regs.X21.toBitVec = pp m0 + BitVec.ofNat 64 (40 * i)
  x22 : st.regs.X22 = m0.regs.X0
  form : FormBufAt st.dmem (bb m0) (acc f other (ww m0) i)

/-- `add_scaled`'s postcondition, reached. -/
abbrev Post (f other : FormW) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ FormBufAddScaledPost f other m0 st.data

/-- The facts of the precondition the blocks use. -/
structure Facts (f other : FormW) (m0 : MachineData) : Prop where
  stack : StackOk m0 SS
  size : m0.regs.X2.toNat = other.size
  form : FormBufAt m0.dmem (bb m0) f
  terms : TermsAt m0.dmem (pp m0) other
  bm : NativeRustcVm.Mapped m0.dmem (bb m0) 5928
  bn : NativeRustcVm.NoWrap (bb m0) 5928
  bo : NativeRustcVm.Apart (bb m0) 5928 (stackBelow m0 SS) SS
  pm : NativeRustcVm.Mapped m0.dmem (pp m0) (40 * other.size)
  pn : NativeRustcVm.NoWrap (pp m0) (40 * other.size)
  po : NativeRustcVm.Apart (pp m0) (40 * other.size) (stackBelow m0 SS) SS
  apart : NativeRustcVm.Apart (bb m0) 5928 (pp m0) (40 * other.size)

theorem Facts.of_pre {f other : FormW} {m0 : MachineData} (h : FormBufAddScaledPre f other m0) :
    Facts f other m0 := by
  obtain ⟨hS, hsz, hF, hT, ⟨hbm, hbn⟩, hbo, ⟨hpm, hpn⟩, hpo, hA⟩ := h
  have e : termBytes * m0.regs.X2.toNat = 40 * other.size := by rw [hsz]; rfl
  rw [e] at hpm hpn hpo hA
  exact ⟨hS, hsz, hF, hT, hbm, hbn, hbo, hpm, hpn, hpo, hA⟩

theorem toNat_sub_ofNat' {x : BitVec 64} {n : Nat} (h : x.toNat = n) (hn : 40 ≤ n) :
    (x - 40#64).toNat = n - 40 := by
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), h]
  rfl

theorem ubfm_lsl3 (x : BitVec 64) : evalUBFM x 61 60 = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [evalUBFM, Arrays.toNat_take', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- `b1`'s X8: `40` times the count less one. -/
theorem x8_init (x : BitVec 64) (h1 : 1 ≤ x.toNat) (h2 : 40 * x.toNat < 2 ^ 64) :
    (evalUBFM (x + x <<< 2) 61 60 - 40#64).toNat = 40 * (x.toNat - 1) := by
  have e : (x + x <<< 2).toNat = 5 * x.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    omega
  rw [ubfm_lsl3, e]
  rw [toNat_sub_ofNat' (n := 40 * x.toNat) (by rw [BitVec.toNat_ofNat]; omega) (by omega)]
  omega

theorem not_inRange_zero {a p : BitVec 64} : ¬InRange a 0 p := by
  unfold InRange; omega

/-- A term added from an argument slice apart from the outputs, read in a body. -/
theorem Facts.term {f other : FormW} {m0 st : MachineData} (hF : Facts f other m0)
    (hb : Body m0 48 SS slots (bb m0) formBufBytes st) {i : Nat} (hi : i < other.size) :
    TermWAt st.dmem (pp m0 + BitVec.ofNat 64 (40 * i)) other[i] := by
  have hs : Same m0.dmem st.dmem (pp m0) (40 * other.size) :=
    Arrays.same_of_apart hb.same hF.stack hF.pn hF.po hF.apart.symm hF.bn
  have := hF.terms i hi
  simp only [off, termBytes] at this
  exact TermWAt.of_same this (hs.sub (o := 40 * i) (k := termBytes) (by unfold termBytes; omega))

/-- **A call of `add_term`** keeps a body: it changes only the form. -/
theorem body_add {f other : FormW} {m0 st st' : MachineData} (hF : Facts f other m0)
    (hb : Body m0 48 SS slots (bb m0) formBufBytes st)
    (hc : Changes st st' 0 (bb m0) formBufBytes) (hs : Saved st st') :
    Body m0 48 SS slots (bb m0) formBufBytes st' := by
  have hS := hF.stack
  have hSle : SS ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  refine ⟨hs.2.1 ▸ hb.sp, fun p hp i hi ↦ ?_, fun r hr hn ↦ (hs.1 r hr).trans (hb.regs r hr hn),
    fun q hq ↦ ?_, fun q h ↦ hs.2.2 q (hb.kept q h)⟩
  · rw [hc _ ?_]
    · exact hb.frame p hp i hi
    · simp only [List.length_map, List.length_range] at hi
      have := slots_le p hp
      have e : m0.regs.SP.toBitVec - BitVec.ofNat 64 48 + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i =
          stackBelow m0 SS + BitVec.ofNat 64 (SS - 48 + p.1 + i) := by
        unfold stackBelow
        have : (48 : Nat) ≤ SS := by decide
        bv_omega
      rw [e]
      rintro (h | h)
      · exact Arrays.not_inRange_of_apart hF.bo.symm (Arrays.stack_noWrap hS) hF.bn
          (by unfold SS formBufAddScaledStack ewMulStack at *; omega) h
      · exact not_inRange_zero h
  · rw [hc q fun h ↦ h.elim (fun h' ↦ hq (.inl h')) not_inRange_zero]
    exact hb.same q hq

variable [Host] {k : Nat}

theorem pc_of {pc : Int64} {a b : Nat} (h : pc = Host.addrOf a) (e : a = b) : pc = Host.addrOf b :=
  e ▸ h

/-- **The epilogue** `b6`: X0 as the loop left it. -/
theorem finish (hp : Placed code k) {f other : FormW} {m0 : MachineData} (hF : Facts f other m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FormBufAddScaled.b6Offset))
    (hb : Body m0 48 SS slots (bb m0) formBufBytes st.data)
    (hres : if (f.addScaled other (ww m0)).size ≤ formCap then
        st.data.regs.X0 = 1 ∧ FormBufAt st.data.dmem (bb m0) (f.addScaled other (ww m0))
      else st.data.regs.X0 = 0) :
    Eventually (step1 Host.exe) (Post f other m0) st := by
  obtain ⟨hwf, hm⟩ := hb.exit_match hF.stack (by decide) (by decide)
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 hwf hpc hm
    fun st' hm' hpc' ↦ .done _ ?_
  obtain ⟨hsaved, hx30, hdm⟩ := hb.saved hm' hwf (List.mem_map.mpr ⟨(0, .X30), by simp [slots], rfl⟩)
    (Arrays.after_eq run_b6 ▸ b6_restores).1 (Arrays.after_eq run_b6 ▸ b6_restores).2
  have h0 : st'.data.regs.X0 = st.data.regs.X0 :=
    UInt64.toBitVec_inj.mp (hm'.regs .X0 _ rfl)
  refine ⟨?_, ?_, ?_, hsaved⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    simp only [retOf, hx30]
  · rw [h0, hdm]; exact hres
  · intro q hq; rw [hdm]; exact hb.same q hq

omit [Host] in
theorem ptr_zero_eval [Labels] (env : Env) (r : Nat) : (Sym.ptr r 0).eval env = env.base r := by
  simp [Sym.eval]

omit [Host] in
theorem ofNat_beq {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x == BitVec.ofNat 64 y) = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne]
    intro he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat] at this
    omega

omit [Host] in
/-- A callee's stack below a body's frame is inside the function's. -/
theorem callee_stack {f other : FormW} {m0 st : MachineData} (hF : Facts f other m0)
    (hb : Body m0 48 SS slots (bb m0) formBufBytes st) {p : BitVec 64}
    (h : InRange (stackBelow st ewMulStack) ewMulStack p) : InRange (stackBelow m0 SS) SS p := by
  unfold stackBelow at h
  rw [hb.sp] at h
  exact Arrays.inRange_stack (by decide) hF.stack.2.1 h

omit [Host] in
/-- The form's bytes, apart from the stack. -/
theorem Facts.not_stack {f other : FormW} {m0 : MachineData} (hF : Facts f other m0) {j : Nat}
    (hj : j < formBufBytes) : ¬InRange (stackBelow m0 SS) SS (bb m0 + BitVec.ofNat 64 j) :=
  Arrays.not_inRange_of_apart hF.bo hF.bn (Arrays.stack_noWrap hF.stack) hj

/-- **A turn of the loop**: term `i` scaled and added; back at the head, or out with the
result. -/
theorem step (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hadd : ∀ f t, Spec (Labels.label NativeRustcVmArm.Vm.FormBufAddTerm.entryLabel) (FormBufAddTermPre f t)
      (FormBufAddTermPost f t))
    {f other : FormW} {m0 : MachineData} (hF : Facts f other m0) {i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FormBufAddScaled.b2Offset)) (hI : Inv f other m0 i st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ Post f other m0 st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FormBufAddScaled.b2Offset) ∧ Inv f other m0 (i + 1) st'.data)) st := by
  have hS := hF.stack
  have hlt := hI.lt
  have hpn := hF.pn
  unfold NativeRustcVm.NoWrap at hpn
  have hT := hF.term hI.body hlt
  obtain ⟨q, hq⟩ : ∃ q, q = pp m0 + BitVec.ofNat 64 (40 * i) := ⟨_, rfl⟩
  rw [← hq] at hT
  have hqm : NativeRustcVm.Mapped st.data.dmem q 40 := fun j hj ↦ by
    rw [hq, addr_add_add]; exact hI.body.kept _ (hF.pm _ (by omega))
  have hqn : NativeRustcVm.NoWrap q 40 := hq ▸ hF.pn.sub (o := 40 * i) (m := 40) (by omega)
  let env := Env.ofMachine st.data [(q, 40)]
  have hwf : env.WF := Arrays.wf_one hqm hqn
  have hm : Match env termS st.data := match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
    ⟨by show _ = (Sym.ptr 0 0).eval env; rw [ptr_zero_eval]; exact hI.x21.trans hq.symm, trivial⟩
    trivial trivial trivial
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hb1 := hI.body.of_block hm hm1 hwf rfl (Arrays.after_eq run_b2 ▸ b2_keeps)
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  obtain ⟨hc0, hc1⟩ := NativeRustcVm.ewAt_iff.mp hT.coeff
  have l24 : env.load 0 24 8 = other[i].coeff.c0.toBitVec := load_word hc0
  have l32 : env.load 0 32 8 = other[i].coeff.c1.toBitVec := load_word (by
    simp only [off] at hc1; rw [addr_add_add q 24 8] at hc1; exact hc1)
  have e0 : st1.data.regs.X0 = m0.regs.X3 := (UInt64.toBitVec_inj.mp (hm1.regs .X0 _ rfl)).trans hI.x20
  have e1 : st1.data.regs.X1 = m0.regs.X4 := (UInt64.toBitVec_inj.mp (hm1.regs .X1 _ rfl)).trans hI.x19
  have e2 : st1.data.regs.X2 = other[i].coeff.c0 := UInt64.toBitVec_inj.mp ((hm1.regs .X2 _ rfl).trans l24)
  have e3 : st1.data.regs.X3 = other[i].coeff.c1 := UInt64.toBitVec_inj.mp ((hm1.regs .X3 _ rfl).trans l32)
  have k19 : st1.data.regs.X19 = st.data.regs.X19 := Match.reg_eq hm hm1 (r := .X19) rfl rfl
  have k20 : st1.data.regs.X20 = st.data.regs.X20 := Match.reg_eq hm hm1 (r := .X20) rfl rfl
  have k21 : st1.data.regs.X21 = st.data.regs.X21 := Match.reg_eq hm hm1 (r := .X21) rfl rfl
  have k22 : st1.data.regs.X22 = st.data.regs.X22 := Match.reg_eq hm hm1 (r := .X22) rfl rfl
  have k23 : st1.data.regs.X23 = st.data.regs.X8 := UInt64.toBitVec_inj.mp (hm1.regs .X23 _ rfl)
  -- `EW::mul`: the weight times the coefficient
  refine call_then hpc1 hmul (hb1.ewMulPre hS (by decide) (by decide)) fun st2 hpc2 hpost ↦ ?_
  have hb2 := hb1.call hS (by decide) slots_le hpost
  have hprod : (⟨st2.data.regs.X0, st2.data.regs.X1⟩ : EW) = ww m0 * other[i].coeff := by
    rw [hpost.1, hpost.2.1, e0, e1, e2, e3]
    rfl
  have hs2 := hpost.2.2.2
  have hd2 : Same st1.data.dmem st2.data.dmem (bb m0) formBufBytes :=
    Same.of_sameOutside hpost.2.2.1 fun j hj h ↦ hF.not_stack hj (callee_stack hF hb1 h)
  -- `b3`: the call of `add_term`
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 (Env.wf_nil _) (pc_of hpc2 rfl)
    (match_nil _) fun st3 hm3 hpc3 ↦ ?_
  have hb3 := hb2.of_block (match_nil _) hm3 (Env.wf_nil _) rfl (Arrays.after_eq run_b3 ▸ b3_keeps)
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq (Env.wf_nil _) rfl
  have hx0 : st3.data.regs.X0.toBitVec = bb m0 := by
    rw [show st3.data.regs.X0 = st2.data.regs.X22 from UInt64.toBitVec_inj.mp (hm3.regs .X0 _ rfl)]
    exact congrArg UInt64.toBitVec ((hs2.1 .X22 rfl).trans (k22.trans hI.x22))
  have hx1 : st3.data.regs.X1.toBitVec = q := by
    rw [show st3.data.regs.X1 = st2.data.regs.X21 from UInt64.toBitVec_inj.mp (hm3.regs .X1 _ rfl)]
    exact (congrArg UInt64.toBitVec ((hs2.1 .X21 rfl).trans k21)).trans (hI.x21.trans hq.symm)
  have hc : ewArg st3.data.regs.X2 st3.data.regs.X3 = ww m0 * other[i].coeff := by
    rw [← hprod]
    show (⟨st3.data.regs.getXReg .X2, st3.data.regs.getXReg .X3⟩ : EW) = _
    rw [UInt64.toBitVec_inj.mp (hm3.regs .X2 _ rfl), UInt64.toBitVec_inj.mp (hm3.regs .X3 _ rfl)]
    rfl
  have hpre' : FormBufAddTermPre (acc f other (ww m0) i) other[i] st3.data := by
    show FormBufAt st3.data.dmem st3.data.regs.X0.toBitVec _ ∧
      TermWAt st3.data.dmem st3.data.regs.X1.toBitVec _ ∧
      Readable st3.data st3.data.regs.X0.toBitVec formBufBytes ∧
      Readable st3.data st3.data.regs.X1.toBitVec termBytes ∧
      NativeRustcVm.Apart st3.data.regs.X0.toBitVec formBufBytes st3.data.regs.X1.toBitVec termBytes
    rw [hx0, hx1, hd3]
    refine ⟨FormBufAt.of_same (hd1 ▸ hI.form) hd2, ?_,
      ⟨fun j hj ↦ by rw [hd3]; exact hb2.kept _ (hF.bm _ hj), hF.bn⟩,
      ⟨fun j hj ↦ by rw [hd3]; exact hs2.2.2 _ (by rw [hd1]; exact hqm j hj), hqn⟩, ?_⟩
    · have := hF.term hb3 hlt
      rw [← hq, hd3] at this
      exact this
    · have hb := hF.bn
      have hA := hF.apart
      unfold NativeRustcVm.NoWrap at hb
      have h1 := toNat_add_ofNat (a := pp m0) (i := 40 * i) (by omega)
      unfold NativeRustcVm.Apart at hA ⊢
      rw [hq, h1]
      unfold formBufBytes formCap termBytes
      omega
  refine call_then hpc3 (hadd _ _) hpre' fun st4 hpc4 hpost' ↦ ?_
  have hpost'' : (if (acc f other (ww m0) (i + 1)).size ≤ formCap then
        st4.data.regs.X0 = 1 ∧ FormBufAt st4.data.dmem (bb m0) (acc f other (ww m0) (i + 1))
      else st4.data.regs.X0 = 0) ∧ Changes st3.data st4.data 0 (bb m0) formBufBytes ∧
      Saved st3.data st4.data := by
    have h := hpost'
    simp only [FormBufAddTermPost] at h
    rw [hx0, hc, ← stepT, ← acc_succ _ _ _ hlt] at h
    exact h
  obtain ⟨hres, hch, hs4⟩ := hpost''
  have hb4 := body_add hF hb3 hch hs4
  -- `b4`: `add_term`'s result
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 (Env.wf_nil _) (pc_of hpc4 rfl)
    (match_nil _) fun st5 hm5 hpc5 ↦ ?_
  have hb5 := hb4.of_block (match_nil _) hm5 (Env.wf_nil _) rfl (Arrays.after_eq run_b4 ▸ b4_keeps)
  have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq (Env.wf_nil _) rfl
  have k0 : st5.data.regs.X0 = st4.data.regs.X0 := Match.reg_eq (match_nil _) hm5 (r := .X0) rfl rfl
  simp only [PcOk] at hpc5
  sym_simp at hpc5
  by_cases hsz : (acc f other (ww m0) (i + 1)).size ≤ formCap
  · simp only [hsz, ↓reduceIte] at hres
    have e0 : (Env.ofMachine st4.data []).regs .X0 = 1#64 := congrArg UInt64.toBitVec hres.1
    rw [e0] at hpc5
    have hpc6 := pc_of ((Arrays.pc_cond hpc5).2 (by decide)) rfl
    -- `b5`: the next term
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 (Env.wf_nil _) hpc6
      (match_nil _) fun st6 hm6 hpc7 ↦ ?_
    have hb6 := hb5.of_block (match_nil _) hm6 (Env.wf_nil _) rfl
      (Arrays.after_eq run_b5 ▸ b5_keeps)
    have hd6 : st6.data.dmem = st5.data.dmem := hm6.dmem_eq (Env.wf_nil _) rfl
    have c23 : st5.data.regs.X23 = st.data.regs.X8 := by
      exact (Match.reg_eq (match_nil _) hm5 (r := .X23) rfl rfl).trans ((hs4.1 .X23 rfl).trans
        ((Match.reg_eq (match_nil _) hm3 (r := .X23) rfl rfl).trans ((hs2.1 .X23 rfl).trans k23)))
    have e23 : (Env.ofMachine st5.data []).regs .X23 =
        BitVec.ofNat 64 (40 * (other.size - 1 - i)) := by
      apply BitVec.eq_of_toNat_eq
      show st5.data.regs.X23.toNat = _
      rw [c23, hI.x8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [PcOk] at hpc7
    sym_simp at hpc7
    rw [e23, ofNat_beq (by omega) (by omega)] at hpc7
    have k0' : st6.data.regs.X0 = st5.data.regs.X0 :=
      Match.reg_eq (match_nil _) hm6 (r := .X0) rfl rfl
    have c19 : st6.data.regs.X19 = m0.regs.X4 :=
      (Match.reg_eq (match_nil _) hm6 (r := .X19) rfl rfl).trans
      ((Match.reg_eq (match_nil _) hm5 (r := .X19) rfl rfl).trans ((hs4.1 .X19 rfl).trans
        ((Match.reg_eq (match_nil _) hm3 (r := .X19) rfl rfl).trans ((hs2.1 .X19 rfl).trans
          (k19.trans hI.x19)))))
    have c20 : st6.data.regs.X20 = m0.regs.X3 :=
      (Match.reg_eq (match_nil _) hm6 (r := .X20) rfl rfl).trans
      ((Match.reg_eq (match_nil _) hm5 (r := .X20) rfl rfl).trans ((hs4.1 .X20 rfl).trans
        ((Match.reg_eq (match_nil _) hm3 (r := .X20) rfl rfl).trans ((hs2.1 .X20 rfl).trans
          (k20.trans hI.x20)))))
    have c22 : st6.data.regs.X22 = m0.regs.X0 :=
      (Match.reg_eq (match_nil _) hm6 (r := .X22) rfl rfl).trans
      ((Match.reg_eq (match_nil _) hm5 (r := .X22) rfl rfl).trans ((hs4.1 .X22 rfl).trans
        ((Match.reg_eq (match_nil _) hm3 (r := .X22) rfl rfl).trans ((hs2.1 .X22 rfl).trans
          (k22.trans hI.x22)))))
    have c21 : st5.data.regs.X21 = st.data.regs.X21 :=
      (Match.reg_eq (match_nil _) hm5 (r := .X21) rfl rfl).trans ((hs4.1 .X21 rfl).trans
        ((Match.reg_eq (match_nil _) hm3 (r := .X21) rfl rfl).trans ((hs2.1 .X21 rfl).trans k21)))
    by_cases hlast : i + 1 = other.size
    · have hpc8 := pc_of ((Arrays.pc_cond hpc7).2 (by simp; omega)) rfl
      refine Eventually.mono (finish hp hF hpc8 hb6 ?_) fun _ h ↦ Or.inl h
      rw [← acc_size, ← hlast]
      simp only [hsz, ↓reduceIte]
      exact ⟨k0'.trans (k0.trans hres.1), by rw [hd6, hd5]; exact hres.2⟩
    · have hpc8 := ((Arrays.pc_cond hpc7).1 (by simp; omega)).trans (hp.label (j := NativeRustcVmArm.Vm.FormBufAddScaled.b2Offset) NativeRustcVmArm.Vm.FormBufAddScaled.label_2_at)
      have h21 := hm6.regs .X21 _ rfl
      have h8 := hm6.regs .X8 _ rfl
      sym_simp at h21 h8
      rw [e23] at h8
      refine .done _ (Or.inr ⟨hpc8, hb6, by omega, ?_, c19, c20, ?_, c22, ?_⟩)
      · show (st6.data.regs.getXReg .X8).toBitVec.toNat = _
        rw [h8, toNat_sub_ofNat' (n := 40 * (other.size - 1 - i))
          (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) (by omega)]
        omega
      · show (st6.data.regs.getXReg .X21).toBitVec = _
        rw [h21]
        show st5.data.regs.X21.toBitVec + BitVec.ofNat 64 40 = _
        rw [c21, hI.x21, addr_add_add]
        exact congrArg (fun x ↦ pp m0 + BitVec.ofNat 64 x) (by omega)
      · rw [hd6, hd5]; exact hres.2
  · simp only [hsz, ↓reduceIte] at hres
    have e0 : (Env.ofMachine st4.data []).regs .X0 = 0#64 := congrArg UInt64.toBitVec hres
    rw [e0] at hpc5
    have hpc6 := ((Arrays.pc_cond hpc5).1 (by decide)).trans (hp.label (j := NativeRustcVmArm.Vm.FormBufAddScaled.b6Offset) NativeRustcVmArm.Vm.FormBufAddScaled.label_4_at)
    refine Eventually.mono (finish hp hF hpc6 hb5 ?_) fun _ h ↦ Or.inl h
    have hgt : ¬(f.addScaled other (ww m0)).size ≤ formCap := fun h ↦
      hsz (Nat.le_trans (le_size_addScaled _ _ _ _) h)
    simp only [hgt, ↓reduceIte]
    exact k0.trans hres

omit [Host] in
/-- The frame is inside the function's stack. -/
theorem frame_in_stack {f other : FormW} {m0 : MachineData} (hF : Facts f other m0) {p : BitVec 64}
    (h : InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 48) 48 p) :
    InRange (stackBelow m0 SS) SS p := by
  have hle : SS ≤ m0.regs.SP.toBitVec.toNat := hF.stack.2.1
  refine Arrays.inRange_mono (c := SS - 48) (n := 48) ?_ (by decide)
  have e : stackBelow m0 SS + BitVec.ofNat 64 (SS - 48) = m0.regs.SP.toBitVec - BitVec.ofNat 64 48 := by
    unfold stackBelow
    have : (48 : Nat) ≤ SS := by decide
    bv_omega
  rw [e]
  exact h

/-- **`FormBuf::add_scaled`'s contract.** -/
theorem formBufAddScaled_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hadd : ∀ f t, Spec (Labels.label NativeRustcVmArm.Vm.FormBufAddTerm.entryLabel) (FormBufAddTermPre f t)
      (FormBufAddTermPost f t)) {f other : FormW} :
    Spec (Labels.label NativeRustcVmArm.Vm.FormBufAddScaled.entryLabel) (FormBufAddScaledPre f other)
      (FormBufAddScaledPost f other) := by
  intro m0 hpre
  have hF := Facts.of_pre hpre
  have hS := hF.stack
  have hpn := hF.pn
  unfold NativeRustcVm.NoWrap at hpn
  obtain ⟨hwf, hm⟩ := Arrays.entry_match hS (F := 48) (by decide) (by decide)
  rw [show Labels.label NativeRustcVmArm.Vm.FormBufAddScaled.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.FormBufAddScaled.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.FormBufAddScaled.entryOffset) NativeRustcVmArm.Vm.FormBufAddScaled.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf hm fun st0 hm0 hpc0 ↦ ?_
  simp only [PcOk] at hpc0
  sym_simp at hpc0
  have e2 : (Arrays.frameEnv m0 m0 48).regs .X2 = BitVec.ofNat 64 other.size := by
    apply BitVec.eq_of_toNat_eq
    show m0.regs.X2.toNat = _
    rw [hF.size, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [e2, ofNat_beq (by omega) (by omega)] at hpc0
  obtain ⟨hpa, hpb⟩ := Arrays.pc_cond hpc0
  by_cases hz : other.size = 0
  · -- no terms: `b7` returns `1`
    have hpc1 := (hpa (by simpa using hz)).trans (hp.label (j := NativeRustcVmArm.Vm.FormBufAddScaled.b7Offset) NativeRustcVmArm.Vm.FormBufAddScaled.label_5_at)
    refine exec_at (infix_of b7_in_code (by simp [b7]) hp) (Arrays.exec_after run_b0 run_b7) hwf
      hpc1 hm0 fun st1 hm1 hpc2 ↦ .done _ ?_
    have hdm : st1.data.dmem = m0.dmem :=
      hm1.dmem_eq hwf (Arrays.after_eq run_b7 ▸ b7_keeps).2
    have hg : f.addScaled other (ww m0) = f := by rw [← acc_size, hz, acc_zero]
    refine ⟨?_, ?_, ?_, Match.saved hm hm1 hwf rfl (Arrays.after_eq run_b7 ▸ b7_keeps).1⟩
    · simp only [PcOk] at hpc2
      exact hpc2.trans (retOf_of_x30 hm1 rfl rfl)
    · rw [hg]
      simp only [hF.form.len_le, ↓reduceIte]
      exact ⟨UInt64.toBitVec_inj.mp (hm1.regs .X0 _ rfl), hdm ▸ hF.form⟩
    · exact NativeRustcVm.SameOutside.of_eq hdm _
  · -- the prologue, then the loop
    have hpc1 := pc_of (hpb (by simpa using hz)) rfl
    refine exec_at (infix_of b1_in_code (by simp [b1]) hp) (Arrays.exec_after run_b0 run_b1) hwf
      hpc1 hm0 fun st1 hm1 hpc2 ↦ ?_
    obtain ⟨hw, hmem, hregs⟩ := Arrays.after_eq run_b1 ▸ b1_frame
    have hsz := hF.size
    simp only [PcOk] at hpc2
    have hI : Inv f other m0 0 st1.data := by
      have h8 := hm1.regs .X8 _ rfl
      sym_simp at h8
      refine ⟨Arrays.Body.of_entry hS (by decide) hm1 rfl hw hregs hmem, by omega, ?_, ?_, ?_, ?_, ?_,
        ?_⟩
      · show (st1.data.regs.getXReg .X8).toBitVec.toNat = _
        rw [h8, x8_init _ (by show 1 ≤ m0.regs.X2.toNat; omega)
          (by show 40 * m0.regs.X2.toNat < 2 ^ 64; omega)]
        show 40 * (m0.regs.X2.toNat - 1) = _
        rw [hF.size]
        omega
      · exact UInt64.toBitVec_inj.mp (hm1.regs .X19 _ rfl)
      · exact UInt64.toBitVec_inj.mp (hm1.regs .X20 _ rfl)
      · show (st1.data.regs.getXReg .X21).toBitVec = _
        rw [hm1.regs .X21 _ rfl]
        exact (addr_add_zero _).symm
      · exact UInt64.toBitVec_inj.mp (hm1.regs .X22 _ rfl)
      · rw [acc_zero]
        exact FormBufAt.of_same hF.form fun j hj ↦ Arrays.same_of_region0 hm1 hwf hmem _
          fun h ↦ hF.not_stack hj (frame_in_stack hF h)
    refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FormBufAddScaled.b2Offset) ∧ ∃ i, other.size - i = n ∧
      Inv f other m0 i st.data) (fun n st ⟨hpc, i, hn, hI⟩ ↦ ?_) ⟨pc_of hpc2 rfl, 0, rfl, hI⟩
    refine Eventually.mono (step hp hmul hadd hF hpc hI) fun st' h ↦ ?_
    rcases h with h | ⟨hpc', hI'⟩
    · exact Or.inl h
    · exact Or.inr ⟨other.size - (i + 1), by have := hI.lt; omega, hpc', i + 1, rfl, hI'⟩

end

end NativeRustcVmArm.Layout.FormBufAddScaled
