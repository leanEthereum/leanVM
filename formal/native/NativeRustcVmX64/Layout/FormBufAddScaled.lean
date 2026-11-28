module

public import NativeRustcVmX64.Layout.FormBufAddScaled.Exec
public import NativeRustcVmX64.Layout.Forms.Lemmas
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.FormBufAddScaled.Names
public import NativeRustcVmX64.Code.Vm.FormBufAddTerm.Names

/-!
# `FormBuf::add_scaled` on x86-64

No terms (`b0`): `b7` returns `1`. Else the prologue (`b1`) pushes RBX, R12-R15; the loop
(`.L4`, `Inv i`: `i` terms added, the form at RDI the model's fold over them, `acc`) multiplies
term `i`'s coefficient by the weight (`b2`, `EW::mul`) and adds it to the form (`b3`,
`FormBuf::add_term`); AL `0` (`b4`) leaves the loop with it, the model's form then too large
(`le_size_addScaled`); past the last term (`b5`) the epilogue (`b6`) returns add_term's AL `1`.
-/

namespace NativeRustcVmX64.Layout.FormBufAddScaled

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.FormBufAddScaled NativeVm.Model
open NativeRustcVm.Layout NativeRustcVmX64.Layout.Forms
open NativeRustcVmX64.Field (frameEnv frame_wf match_frame midS leaf_done)
open NativeRustcVmX64.Arrays (Body after after_eq exec_after freeRegs keepsAll keepsRegs restores
  pc_cond stackOk_mono regs_eq_of)
open NativeRustcVmX64.Transcript (infix_of)
open NativeRustcVm.Transcript (off)
open NativeRustcVm (WordAt EWAt)

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
abbrev bb (m0 : MachineData) : BitVec 64 := reg m0 .rdi
/-- The terms added. -/
abbrev pp (m0 : MachineData) : BitVec 64 := reg m0 .rsi
/-- The weight. -/
abbrev ww (m0 : MachineData) : EW := ewArg (reg m0 .rcx) (reg m0 .r8)
/-- The stack. -/
abbrev SS : Nat := formBufAddScaledStack

theorem SS_eq : SS = 192 := rfl

/-- **The loop head** `.L4`: `i` terms added. -/
structure Inv (f other : FormW) (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  body : Body m0 48 SS slots (bb m0) formBufBytes st
  lt : i < other.size
  r13 : (reg st .r13).toNat = 40 * (other.size - 1 - i)
  rbx : reg st .rbx = reg m0 .r8
  r14 : reg st .r14 = reg m0 .rcx
  r15 : reg st .r15 = pp m0 + BitVec.ofNat 64 (40 * i)
  r12 : reg st .r12 = reg m0 .rdi
  form : FormBufAt st.dmem (bb m0) (acc f other (ww m0) i)

/-- The facts of the precondition the blocks use. -/
structure Facts (f other : FormW) (m0 : MachineData) : Prop where
  stack : StackOk m0 SS
  size : (reg m0 .rdx).toNat = other.size
  form : FormBufAt m0.dmem (bb m0) f
  terms : TermsAt m0.dmem (pp m0) other
  bm : NativeRustcVm.Mapped m0.dmem (bb m0) 5928
  bn : NativeRustcVm.NoWrap (bb m0) 5928
  bo : NativeRustcVm.Apart (bb m0) 5928 (stackBelow m0 SS) (SS + 8)
  pm : NativeRustcVm.Mapped m0.dmem (pp m0) (40 * other.size)
  pn : NativeRustcVm.NoWrap (pp m0) (40 * other.size)
  po : NativeRustcVm.Apart (pp m0) (40 * other.size) (stackBelow m0 SS) (SS + 8)
  apart : NativeRustcVm.Apart (bb m0) 5928 (pp m0) (40 * other.size)

theorem Facts.of_pre {f other : FormW} {m0 : MachineData} (h : FormBufAddScaledPre f other m0) :
    Facts f other m0 := by
  obtain ⟨hS, hsz, hF, hT, ⟨hbm, hbn⟩, hbo, ⟨hpm, hpn⟩, hpo, hA⟩ := h
  have e : termBytes * (reg m0 .rdx).toNat = 40 * other.size := by rw [hsz]; rfl
  rw [e] at hpm hpn hpo hA
  exact ⟨hS, hsz, hF, hT, hbm, hbn, hbo, hpm, hpn, hpo, hA⟩

/-- The form's bytes are not the stack's. -/
theorem Facts.not_stack {f other : FormW} {m0 : MachineData} (hF : Facts f other m0) (p : BitVec 64)
    (h : InRange (bb m0) formBufBytes p) : ¬InRange (stackBelow m0 SS) SS p := by
  have hbo := hF.bo
  have hbn : (bb m0).toNat + 5928 ≤ 2 ^ 64 := hF.bn
  have hsn := Transcript.stack_noWrap hF.stack
  unfold NativeRustcVm.NoWrap at hsn
  unfold NativeRustcVm.Apart at hbo
  intro h'
  rw [show formBufBytes = 5928 from rfl, Sym.inRange_iff hbn] at h
  rw [Sym.inRange_iff hsn] at h'
  omega

/-- A term added, read in a body. -/
theorem Facts.term {f other : FormW} {m0 st : MachineData} (hF : Facts f other m0)
    (hb : Body m0 48 SS slots (bb m0) formBufBytes st) {i : Nat} (hi : i < other.size) :
    TermWAt st.dmem (pp m0 + BitVec.ofNat 64 (40 * i)) other[i] := by
  have hs : Same m0.dmem st.dmem (pp m0) (40 * other.size) :=
    Arrays.same_of_apart hb.same hF.stack hF.pn hF.po (Arrays.apart_symm hF.apart) hF.bn
  exact TermWAt.of_same (hF.terms i hi) (hs.sub (o := 40 * i) (k := termBytes)
    (by unfold termBytes; omega))

/-- A form over bytes a change misses. -/
theorem form_keep {d d' : Mem 64} {b : BitVec 64} {x : FormW} (h : FormBufAt d b x)
    (hb : NativeRustcVm.NoWrap b 5928)
    (hs : ∀ p, InRange b formBufBytes p → d'.get? p = d.get? p) : FormBufAt d' b x :=
  FormBufAt.of_same h fun _ hj ↦ hs _ (Arrays.inRange_add hb hj)

/-- A term over bytes a change misses. -/
theorem term_keep {d d' : Mem 64} {q : BitVec 64} {t : TermW} (h : TermWAt d q t)
    (hq : NativeRustcVm.NoWrap q 40)
    (hs : ∀ p, InRange q 40 p → d'.get? p = d.get? p) : TermWAt d' q t :=
  TermWAt.of_same h fun _ hj ↦ hs _ (Arrays.inRange_add hq hj)

/-- `b1`'s R13 for a count `x ≥ 1` with `40 x < 2 ^ 64`: `40 (x - 1)`. -/
theorem r13_eval (x : BitVec 64) (h1 : 1 ≤ x.toNat) (h2 : 40 * x.toNat < 2 ^ 64) :
    (BitVec.ofNat 64 18446744073709551576 + (x <<< 3 + x <<< 3 * BitVec.ofNat 64 4)).toNat =
      40 * (x.toNat - 1) := by
  have e : (x <<< 3).toNat = 8 * x.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have e2 : (x <<< 3 + x <<< 3 * BitVec.ofNat 64 4).toNat = 40 * x.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, e, BitVec.toNat_ofNat]; omega
  rw [BitVec.toNat_add, e2, BitVec.toNat_ofNat]
  omega

/-- `b5`'s R13 less `40`. -/
theorem r13_step (x : BitVec 64) {n : Nat} (hx : x.toNat = 40 * n) (hn : 1 ≤ n) :
    (BinOp.apply .add .W64 x (BitVec.ofNat 64 18446744073709551576)).toNat = 40 * (n - 1) := by
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [BitVec.toNat_add, hx, BitVec.toNat_ofNat]
  have : 40 * n < 2 ^ 64 := hx ▸ x.isLt
  omega

/-- `b5`'s R15 plus `40`. -/
theorem r15_step (q a : BitVec 64) {i : Nat} (h : q = a + BitVec.ofNat 64 (40 * i)) :
    BinOp.apply .add .W64 (BitVec.ofNat 64 40) q = a + BitVec.ofNat 64 (40 * (i + 1)) := by
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [h, BitVec.add_comm, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2

theorem test8 (x : BitVec 64) :
    CmpOp.apply .eq .W8 (BinOp.apply .and .W8 x x) (BitVec.ofNat 64 0) = decide (x.toNat % 256 = 0) := by
  simp only [CmpOp.apply, BinOp.apply]
  have h1 : low .W8 (ext .W8 (low .W8 x &&& low .W8 x)) = low .W8 x := by
    simp [ext, low, BitVec.and_self]
  rw [h1]
  by_cases h : x.toNat % 256 = 0
  · have : low .W8 x = low .W8 (BitVec.ofNat 64 0) :=
      BitVec.eq_of_toNat_eq (by rw [toNat_low, toNat_low]; simpa using h)
    rw [this, beq_self_eq_true, decide_eq_true h]
  · have : low .W8 x ≠ low .W8 (BitVec.ofNat 64 0) := fun e ↦ h (by
      have := congrArg BitVec.toNat e
      rw [toNat_low, toNat_low] at this
      simpa using this)
    rw [beq_eq_false_iff_ne.mpr this, decide_eq_false h]

theorem test64 (x : BitVec 64) :
    CmpOp.apply .eq .W64 (BinOp.apply .and .W64 x x) (BitVec.ofNat 64 0) = decide (x.toNat = 0) := by
  simp only [CmpOp.apply, BinOp.apply, low_W64, ext_W64, BitVec.and_self]
  by_cases h : x.toNat = 0
  · have : x = 0#64 := BitVec.eq_of_toNat_eq h
    simp [this]
  · have : x ≠ BitVec.ofNat 64 0 := fun e ↦ h (by rw [e]; rfl)
    simp [this, h]

variable [Host] {k : Nat}

/-- `add_scaled`'s postcondition, reached. -/
abbrev Post (f other : FormW) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ FormBufAddScaledPost f other m0 st.data

/-- **The epilogue** `b6`: AL as the loop left it. -/
theorem finish (hp : Placed code k) {f other : FormW} {m0 : MachineData} (hF : Facts f other m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddScaled.b6Offset))
    (hb : Body m0 48 SS slots (bb m0) formBufBytes st.data)
    (hres : if (f.addScaled other (ww m0)).size ≤ formCap then
        boolRet st.data = 1 ∧ FormBufAt st.data.dmem (bb m0) (f.addScaled other (ww m0))
      else boolRet st.data = 0) :
    Eventually (step1 Host.exe) (Post f other m0) st := by
  have hS := hF.stack
  have h48 : 48 ≤ SS := by decide
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6
    (hb.wf (vars := fun _ ↦ 0) (ret := 0) hS h48) nofun hpc hb.mid_match fun st' hm' hpc' ↦
      .done _ ?_
  obtain ⟨hres', hmem, hax⟩ := after_eq run_b6 ▸ b6_restores
  obtain ⟨hpc'', hrsp, hdm, hsaved⟩ := hb.done hS h48 hm' hpc' hres' hmem
    (Arrays.ret_not_in hS hF.bn hF.bo)
  have h0 : boolRet st'.data = boolRet st.data := by
    unfold boolRet; rw [show reg st'.data .rax = _ from hm'.regs .rax _ hax]; rfl
  refine ⟨hpc'', hrsp, ?_, fun p hp' ↦ by rw [hdm]; exact hb.same p hp', hsaved⟩
  rw [h0, hdm]; exact hres

/-- **After `add_term`** (`b4`, `b5`): AL `0` leaves the loop; else the next term or the
epilogue. -/
theorem step_tail (hp : Placed code k) {f other : FormW} {m0 : MachineData}
    (hF : Facts f other m0) {i : Nat} {st : MachineData} (hI : Inv f other m0 i st)
    {st4 : MachineState} (hpc4' : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddScaled.b4Offset))
    (hb4 : Body m0 48 SS slots (bb m0) formBufBytes st4.data)
    (e4 : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14, .r15], reg st4.data r = reg st r)
    (hres : if (acc f other (ww m0) (i + 1)).size ≤ formCap then
        boolRet st4.data = 1 ∧ FormBufAt st4.data.dmem (bb m0) (acc f other (ww m0) (i + 1))
      else boolRet st4.data = 0) :
    Eventually (step1 Host.exe) (fun st' ↦ Post f other m0 st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddScaled.b2Offset) ∧ Inv f other m0 (i + 1) st'.data)) st4 := by
  have hlt := hI.lt
  -- `b4`: `add_term`'s AL
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 (Env.wf_nil _) nofun
    hpc4' (match_nil _) fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hk5, hkr5⟩ := after_eq run_b4 ▸ b4_facts
  have hb5 := hb4.of_block (match_nil _) hm5 (Env.wf_nil _) rfl hk5
  have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq (Env.wf_nil _) (mem_of_keepsAll hk5)
  have e5 := regs_eq_of (match_nil _) hm5 hkr5
  have hal5 : boolRet st5.data = boolRet st4.data := by
    unfold boolRet; rw [e5 .rax (by simp)]
  simp only [PcOk] at hpc5
  obtain ⟨hy, hn⟩ := pc_cond hpc5
  simp only [SBool.eval, Sym.eval, Env.ofMachine_regs] at hy hn
  rw [test8] at hy hn
  by_cases hsz : (acc f other (ww m0) (i + 1)).size ≤ formCap
  · simp only [hsz, ↓reduceIte] at hres
    have hpc6 := hn (by
      have : (st4.data.regs.get64 .rax).toNat % 256 = 1 := hres.1
      simp [this])
    -- `b5`: the next term
    have hl4 : b4.length = 2 := rfl
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 (Env.wf_nil _) nofun
      (hpc6.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.FormBufAddScaled.b4_next))) (match_nil _) fun st6 hm6 hpc7 ↦ ?_
    obtain ⟨hk6, hkr6, h15, h13⟩ := after_eq run_b5 ▸ b5_facts
    have hb6 := hb5.of_block (match_nil _) hm6 (Env.wf_nil _) rfl hk6
    have hd6 : st6.data.dmem = st5.data.dmem := hm6.dmem_eq (Env.wf_nil _) (mem_of_keepsAll hk6)
    have e6 := regs_eq_of (match_nil _) hm6 hkr6
    have hr13 : (reg st5.data .r13).toNat = 40 * (other.size - 1 - i) := by
      rw [e5 .r13 (by simp), e4 .r13 (by simp)]; exact hI.r13
    simp only [PcOk] at hpc7
    obtain ⟨hy7, hn7⟩ := pc_cond hpc7
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs] at hy7 hn7
    rw [test64] at hy7 hn7
    have hr13' : (st5.data.regs.get64 .r13).toNat = 40 * (other.size - 1 - i) := hr13
    rw [hr13'] at hy7 hn7
    have hform : FormBufAt st6.data.dmem (bb m0) (acc f other (ww m0) (i + 1)) := by
      rw [hd6, hd5]; exact hres.2
    by_cases hlast : i + 1 = other.size
    · have hl5 : b5.length = 4 := rfl
      have hpc8 := hn7 (by simp; omega)
      refine Eventually.mono (finish hp hF (hpc8.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.FormBufAddScaled.b5_next))) hb6 ?_)
        fun _ h ↦ Or.inl h
      rw [← acc_size, ← hlast]
      simp only [hsz, ↓reduceIte]
      refine ⟨?_, hform⟩
      unfold boolRet; rw [e6 .rax (by simp)]; exact hal5.trans hres.1
    · have hpc8 := (hy7 (by simp; omega)).trans (hp.label NativeRustcVmX64.Vm.FormBufAddScaled.label_4_at)
      have h13' := hm6.regs .r13 _ h13
      have h15' := hm6.regs .r15 _ h15
      simp only [Sym.eval, Env.ofMachine_regs] at h13' h15'
      have h15q : reg st5.data .r15 = pp m0 + BitVec.ofNat 64 (40 * i) := by
        rw [e5 .r15 (by simp), e4 .r15 (by simp)]; exact hI.r15
      refine .done _ (Or.inr ⟨hpc8, hb6, by omega, ?_, ?_, ?_, h15'.trans (r15_step _ _ h15q), ?_,
        hform⟩)
      · show (st6.data.regs.get64 .r13).toNat = _
        rw [h13', r13_step _ hr13' (by omega)]
        omega
      · rw [e6 .rbx (by simp), e5 .rbx (by simp), e4 .rbx (by simp)]; exact hI.rbx
      · rw [e6 .r14 (by simp), e5 .r14 (by simp), e4 .r14 (by simp)]; exact hI.r14
      · rw [e6 .r12 (by simp), e5 .r12 (by simp), e4 .r12 (by simp)]; exact hI.r12
  · simp only [hsz, ↓reduceIte] at hres
    have hpc6 := (hy (by
      have : (st4.data.regs.get64 .rax).toNat % 256 = 0 := hres
      simp [this])).trans (hp.label NativeRustcVmX64.Vm.FormBufAddScaled.label_6_at)
    refine Eventually.mono (finish hp hF hpc6 hb5 ?_) fun _ h ↦ Or.inl h
    have hgt : ¬(f.addScaled other (ww m0)).size ≤ formCap := fun h ↦
      hsz (Nat.le_trans (le_size_addScaled _ _ _ _) h)
    simp only [hgt, ↓reduceIte]
    exact hal5.trans hres


/-- **A turn of the loop**: term `i` scaled and added; back at the head, or out with the
result. -/
theorem step (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hadd : ∀ f t, Spec (Labels.label NativeRustcVmX64.Vm.FormBufAddTerm.entryLabel) (FormBufAddTermPre f t)
      (FormBufAddTermPost f t))
    {f other : FormW} {m0 : MachineData} (hF : Facts f other m0) {i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddScaled.b2Offset)) (hI : Inv f other m0 i st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ Post f other m0 st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddScaled.b2Offset) ∧ Inv f other m0 (i + 1) st'.data)) st := by
  have hS := hF.stack
  have h48 : 48 ≤ SS := by decide
  have hlt := hI.lt
  have hpn : (pp m0).toNat + 40 * other.size ≤ 2 ^ 64 := hF.pn
  have hb := hI.body
  have hT := hF.term hb hlt
  set q := pp m0 + BitVec.ofNat 64 (40 * i) with hq
  have hqm : NativeRustcVm.Mapped st.data.dmem q 40 := fun j hj ↦ by
    rw [hq, NativeRustcVm.addr_add_add]; exact hb.kept _ (hF.pm _ (by omega))
  have hqn : NativeRustcVm.NoWrap q 40 := hF.pn.sub (o := 40 * i) (m := 40) (by omega)
  have hqa : NativeRustcVm.Apart (stackBelow m0 48) (48 + 8) q 40 := by
    have ha := Transcript.apart_frame hF.po hS.1 h48
    unfold NativeRustcVm.Apart at ha ⊢
    rw [hq, NativeRustcVm.toNat_add_ofNat (by omega)]
    omega
  -- `b2`: `EW::mul`
  let ret2 := (Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddScaled.b2Offset + b2.length)).toBitVec
  have hwf := Arrays.wf_two (vars := fun _ ↦ 0) (ret := ret2) (stackOk_mono hS h48) hb.kept
    ⟨hqm, hqn⟩ hqa
  have hm : Match (Env.ofMachine st.data [(stackBelow m0 48, 48 + 8), (q, 40)] (fun _ ↦ 0) ret2)
      termS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨hb.rsp, Transcript.known_ptr rfl (hI.r15.trans hq.symm), trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf (fun _ _ ↦ rfl) hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hk, hkr, hsp, hw, hdi, hsi, hdx, hcx⟩ := after_eq run_b2 ▸ b2_call
  have e1 := regs_eq_of hm hm1 hkr
  have hcoef : ewArg (reg st1.data .rdx) (reg st1.data .rcx) = other[i].coeff := by
    rw [Arrays.ew_of_loads hm1 hdx hcx]
    exact NativeRustcVm.ewOf_of_ewAt hT.coeff
  refine Body.call_mul hmul hb hS (by decide) (L := 8) (by decide) slots_ok hwf hm hm1 hpc1 hk hsp
    hw fun st2 hpc2 hb2 hprod hsv2 hout2 _ ↦ ?_
  have hP : ewRet st2.data = ww m0 * other[i].coeff := by
    rw [hprod, ← hcoef, show reg st1.data .rdi = reg st.data .r14 from hm1.regs .rdi _ hdi,
      show reg st1.data .rsi = reg st.data .rbx from hm1.regs .rsi _ hsi, hI.r14, hI.rbx]
    rfl
  have e2 : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14, .r15], reg st2.data r = reg st.data r := by
    intro r hr
    have hc : calleeSaved r = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [hsv2 r hc, e1 r hr]
  -- `b3`: `add_term`
  let ret3 := (Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddScaled.b3Offset + b3.length)).toBitVec
  have hwf3 := hb2.wf (vars := fun _ ↦ 0) (ret := ret3) hS h48
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddScaled.b3Offset) := hpc2.trans (congrArg Host.addrOf
    (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.FormBufAddScaled.b2_next]))
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf3 (fun _ _ ↦ rfl) hpc2'
    hb2.mid_match fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hk3, hkr3, hsp3, hw3, hdi3, hsi3, hdx3, hcx3⟩ := after_eq run_b3 ▸ b3_call
  have e3 := regs_eq_of hb2.mid_match hm3 hkr3
  have hrsp3 : rspOf st3.data = stackBelow m0 48 := by
    show st3.data.regs.get64 .rsp = _
    rw [hm3.regs .rsp _ hsp3]
    simp [Sym.eval]
  have hwr3 : ∀ p, Written (frameEnv m0 st2.data 48 (fun _ ↦ 0) ret3) (after b3 (midS 48)) p →
      InRange (stackBelow m0 SS) SS p := fun p h ↦
    Arrays.inRange_stack (F := 48) (n := 0) (k := 8) hS.1 (by decide) (by omega)
      (by simpa using Arrays.written_region0 rfl hwf3 (by omega) (after_eq run_b3 ▸ hw3) h)
  have hk3' : Kept m0.dmem st3.data.dmem := fun p h ↦ hm3.kept hwf3 p (hb2.kept p h)
  -- the memory st3 sees: the form and term as at `st`
  have hsame : ∀ p, ¬InRange (stackBelow m0 SS) SS p → st3.data.dmem.get? p = st.data.dmem.get? p :=
    fun p hp' ↦ by
      rw [hm3.get?_mem0 hwf3 fun h ↦ hp' (hwr3 p (after_eq run_b3 ▸ h))]
      exact hout2 p hp'
  have hqm0 : NativeRustcVm.Mapped m0.dmem q 40 := fun j hj ↦ by
    rw [hq, NativeRustcVm.addr_add_add]; exact hF.pm _ (by omega)
  have hqo : NativeRustcVm.Apart q 40 (stackBelow m0 SS) (SS + 8) := by
    have ha := hF.po
    unfold NativeRustcVm.Apart at ha ⊢
    rw [hq, NativeRustcVm.toNat_add_ofNat (by omega)]
    omega
  have hqs : ∀ p, InRange q 40 p → ¬InRange (stackBelow m0 SS) SS p := fun p hp1 hp2 ↦ by
    have hsn := Transcript.stack_noWrap hS
    unfold NativeRustcVm.NoWrap at hsn hqn
    unfold NativeRustcVm.Apart at hqo
    rw [Sym.inRange_iff hqn] at hp1
    rw [Sym.inRange_iff hsn] at hp2
    omega
  have hbq : NativeRustcVm.Apart (bb m0) 5928 q 40 := by
    have ha := hF.apart
    unfold NativeRustcVm.Apart at ha ⊢
    rw [hq, NativeRustcVm.toNat_add_ofNat (by omega)]
    omega
  have e23 : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14, .r15], reg st3.data r = reg st.data r :=
    fun r hr ↦ (e3 r hr).trans (e2 r hr)
  have hrdi : reg st3.data .rdi = bb m0 :=
    (show reg st3.data .rdi = reg st2.data .r12 from hm3.regs .rdi _ hdi3).trans
      ((e2 .r12 (by simp)).trans hI.r12)
  have hrsi : reg st3.data .rsi = q :=
    (show reg st3.data .rsi = reg st2.data .r15 from hm3.regs .rsi _ hsi3).trans
      ((e2 .r15 (by simp)).trans hI.r15)
  have hc3 : ewArg (reg st3.data .rdx) (reg st3.data .rcx) = ww m0 * other[i].coeff := by
    rw [show reg st3.data .rdx = reg st2.data .rax from hm3.regs .rdx _ hdx3,
      show reg st3.data .rcx = reg st2.data .rdx from hm3.regs .rcx _ hcx3]
    exact hP
  have hpre : FormBufAddTermPre (acc f other (ww m0) i) other[i] st3.data := by
    simp only [FormBufAddTermPre]
    rw [hrdi, hrsi]
    exact ⟨Transcript.stackOk_callee hS hk3' hrsp3 (by decide),
      form_keep hI.form hF.bn fun p hp' ↦ hsame p (hF.not_stack p hp'),
      term_keep hT hqn fun p hp' ↦ hsame p (hqs p hp'),
      ⟨fun j hj ↦ hk3' _ (hF.bm j hj), hF.bn⟩,
      Transcript.apart_callee hF.bo hrsp3 hS.1 (by decide),
      ⟨fun j hj ↦ hk3' _ (hqm0 j hj), hqn⟩,
      Transcript.apart_callee hqo hrsp3 hS.1 (by decide), hbq⟩
  refine call_then hpc3 (hadd _ _) hpre fun st4 hpc4 hrsp4 hpost ↦ ?_
  simp only [FormBufAddTermPost] at hpost
  rw [hrdi, hc3, ← stepT, ← acc_succ _ _ _ hlt] at hpost
  obtain ⟨hres, hch, hsv4⟩ := hpost
  have hb4 := body_after_call (n := 40) hb2 hS (by decide) (by decide) slots_ok hwf3
    hb2.mid_match hm3 hk3 hsp3 hw3 hsv4 hrsp4 hch fun p hp' ↦ hF.not_stack p hp'
  have e4 : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14, .r15], reg st4.data r = reg st.data r := by
    intro r hr
    have hc : calleeSaved r = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl
    exact (hsv4.1 r hc).trans (e23 r hr)
  exact step_tail hp hF hI (hpc4.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.FormBufAddScaled.b3_next))) hb4 e4 hres

/-- **`FormBuf::add_scaled`'s contract.** -/
theorem formBufAddScaled_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hadd : ∀ f t, Spec (Labels.label NativeRustcVmX64.Vm.FormBufAddTerm.entryLabel) (FormBufAddTermPre f t)
      (FormBufAddTermPost f t)) {f other : FormW} :
    Spec (Labels.label NativeRustcVmX64.Vm.FormBufAddScaled.entryLabel) (FormBufAddScaledPre f other)
      (FormBufAddScaledPost f other) := by
  intro m0 hpre
  have hF := Facts.of_pre hpre
  have hS := hF.stack
  have h48 : 48 ≤ SS := by decide
  have hpn : (pp m0).toNat + 40 * other.size ≤ 2 ^ 64 := hF.pn
  have hS48 := stackOk_mono hS h48
  have hwf := frame_wf (m0 := m0) (m := m0) (vars := fun _ ↦ 0) (ret := 0) hS48 fun _ h ↦ h
  have hm : Match (frameEnv m0 m0 48) entryS m0 := match_frame
  rw [show Labels.label NativeRustcVmX64.Vm.FormBufAddScaled.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddScaled.b0Offset) from hp.label NativeRustcVmX64.Vm.FormBufAddScaled.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf nofun hm
    fun st0 hm0 hpc0 ↦ ?_
  simp only [PcOk, NativeRustcVmX64.Vm.FormBufAddScaled.b0_length] at hpc0
  obtain ⟨hpa, hpb⟩ := pc_cond hpc0
  simp only [SBool.eval, Sym.eval, Env.ofMachine_regs] at hpa hpb
  rw [test64, show (m0.regs.get64 .rdx).toNat = other.size from hF.size] at hpa hpb
  have hwr : ∀ {S' : SState} {d : MachineData}, Match (frameEnv m0 m0 48) S' d →
      (∀ w ∈ S'.mem, w.r = 0 ∧ w.off + w.n ≤ 48) →
      ∀ p, ¬InRange (stackBelow m0 SS) SS p → d.dmem.get? p = m0.dmem.get? p :=
    fun hm' hw p hp' ↦ hm'.get?_mem0 hwf fun h ↦ hp' (Arrays.inRange_stack (F := 48) (n := 0)
      (k := 48) hS.1 h48 le_rfl (by simpa using Arrays.written_region0 rfl hwf (by omega) hw h))
  by_cases hz : other.size = 0
  · -- no terms: `b7` returns `1`
    have hpc1 := (hpa (by simpa using hz)).trans (hp.label NativeRustcVmX64.Vm.FormBufAddScaled.label_1_at)
    refine exec_at (infix_of b7_in_code (by simp [b7]) hp) (exec_after run_b0 run_b7) hwf nofun
      hpc1 hm0 fun st1 hm1 hpc2 ↦ ?_
    obtain ⟨hsp, hkeep, hmem, hax⟩ := after_eq (exec_after run_b0 run_b7) ▸ b7_ret
    obtain ⟨h1, h2, h3, h4⟩ := leaf_done hS48 hm1 hpc2 hsp hkeep (by simp)
    have hdm : st1.data.dmem = m0.dmem := hm1.dmem_eq hwf hmem
    have hg : f.addScaled other (ww m0) = f := by rw [← acc_size, hz, acc_zero]
    refine .done _ ⟨h1, h2, ?_, fun p _ ↦ by rw [hdm], h4⟩
    rw [hg]
    simp only [hF.form.len_le, ↓reduceIte]
    refine ⟨?_, hdm ▸ hF.form⟩
    unfold boolRet
    rw [show reg st1.data .rax = _ from hm1.regs .rax _ hax]
    exact Transcript.merge_one_mod _
  · -- the prologue, then the loop
    have hpc1 := hpb (by simpa using hz)
    refine exec_at (infix_of b1_in_code (by simp [b1]) hp) (exec_after run_b0 run_b1) hwf nofun
      hpc1 hm0 fun st1 hm1 hpc2 ↦ ?_
    obtain ⟨hw, hregs, hmem, hsp, hbx, h14, h15, h12, h13⟩ := after_eq run_b1 ▸ b1_entry
    simp only [PcOk] at hpc2
    have hI : Inv f other m0 0 st1.data := by
      refine ⟨Body.of_entry hS h48 hm1 hsp hw hregs hmem, by omega, ?_, hm1.regs .rbx _ hbx,
        hm1.regs .r14 _ h14, ?_, hm1.regs .r12 _ h12, ?_⟩
      · rw [show reg st1.data .r13 = _ from hm1.regs .r13 _ h13]
        simp only [r13S, Sym.eval, BinOp.apply, low_W64, ext_W64,
          show shiftCount .W64 (BitVec.ofNat 64 3) = 3 from rfl]
        exact (r13_eval (reg m0 .rdx) (by rw [hF.size]; omega) (by rw [hF.size]; omega)).trans
          (by rw [hF.size, Nat.sub_zero])
      · rw [show reg st1.data .r15 = _ from hm1.regs .r15 _ h15]
        show reg m0 .rsi = _
        simp
      · rw [acc_zero]
        exact form_keep hF.form hF.bn fun p hp' ↦ hwr hm1 hmem p (hF.not_stack p hp')
    refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FormBufAddScaled.b2Offset) ∧ ∃ i, other.size - i = n ∧
      Inv f other m0 i st.data) (fun n st ⟨hpc, i, hn, hI⟩ ↦ ?_)
      ⟨hpc2.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.FormBufAddScaled.b1_next)), 0, rfl, hI⟩
    refine Eventually.mono (step hp hmul hadd hF hpc hI) fun st' h ↦ ?_
    rcases h with h | ⟨hpc', hI'⟩
    · exact Or.inl h
    · exact Or.inr ⟨other.size - (i + 1), by have := hI.lt; omega, hpc', i + 1, rfl, hI'⟩

end

end NativeRustcVmX64.Layout.FormBufAddScaled
