module

public import NativeRustcVmX64.Ring.Column.Exec
public import NativeRustcVmX64.Ring.Stack
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVmX64.Code.Vm.ColumnWeight.Names
public import NativeRustcVmX64.Code.Vm.EqEval.Names
public import NativeRustcVmX64.Code.Vm.StackPoint.Names

/-!
# `column_weight` on x86-64

**`columnWeight_spec`**: rustc's `column_weight(out, p, point, stack_log, x)`, placed anywhere in
the program, given `stack_point`'s and `eq_eval`'s contracts, stores `StackWeight.eval (.eq
(stackPoint p point stackLog)) x` at `out` when the stack point fits its 66 slots, else `None`.
`b0` (the prologue, `x` loaded from the stack), the zeroing loop `b1` (`loop`), `b2` (`stack_point`
into the frame's slots); `b3` its tag: `Some`, `b4` (`eq_eval` on the slots and `x`), `b5`, `b7`;
`None`, `b6`, `b7`.
-/

namespace NativeRustcVmX64.Ring.Column

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.ColumnWeight NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeVm.Model

/-! ## The blocks' facts -/

public theorem exit_b3 : exec b3 midS =
    some (M3, .cond (SBool.cmp .eq .W64 (.reg .rax) (.lit 1)).not NativeRustcVmX64.Vm.ColumnWeight.label_3) :=
  run_b3.trans (by rw [show M3 = _ from after_eq run_b3])

public theorem ok_b2 : ProOk 1088 0 slots (after b2 (L 22)) = true ∧
    (∀ w ∈ (after b2 (L 22)).mem, w.r = 0 ∧ w.off + w.n ≤ 1088) ∧
    (after b2 (L 22)).reg .rdi = some (.reg .rsi) ∧ (after b2 (L 22)).reg .rsi = some (.reg .rdx) ∧
    (after b2 (L 22)).reg .rdx = some (.reg .rcx) ∧ (after b2 (L 22)).reg .rcx = some (.reg .r8) ∧
    (after b2 (L 22)).reg .r8 = some (.reg .r9) ∧ (after b2 (L 22)).reg .r9 = some (.ptr 0 8) ∧
    (after b2 (L 22)).reg .rbx = some (.ptr 2 0) ∧ (after b2 (L 22)).reg .r14 = some (.load 1 8 8) ∧
    (after b2 (L 22)).reg .r15 = some (.load 1 0 8) := by
  decide +kernel

public theorem ok_b4 : MidOk 1088 0 slots (after b4 M3) = true ∧
    (∀ w ∈ (after b4 M3).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b4 M3).reg .rdi = some (.ptr 0 8) ∧ (after b4 M3).reg .rsi = some (.reg .rdx) ∧
    (after b4 M3).reg .rdx = some (.reg .r15) ∧ (after b4 M3).reg .rcx = some (.reg .r14) ∧
    (after b4 M3).reg .rbx = some (.ptr 2 0) := by
  decide +kernel

/-- `None`: the tag `0` stored, the epilogue. -/
public theorem ok_n : EpiOk 1088 slots (after b7 (after b6 M3)) = true ∧
    (∀ t < 8, findWrite 2 t (after b7 (after b6 M3)).mem = some (.lit 0, t)) ∧
    (∀ w ∈ (after b7 (after b6 M3)).mem, w.r = 2 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 24) := by
  decide +kernel

/-- `Some`: the value and the tag `1` stored, the epilogue. -/
public theorem ok_s : EpiOk 1088 slots (after b7 (after b5 midS)) = true ∧
    (∀ t < 8, findWrite 2 t (after b7 (after b5 midS)).mem = some (.lit 1, t)) ∧
    (∀ t < 8, findWrite 2 (8 + t) (after b7 (after b5 midS)).mem = some (.reg .rax, t)) ∧
    (∀ t < 8, findWrite 2 (16 + t) (after b7 (after b5 midS)).mem = some (.reg .rdx, t)) ∧
    (∀ w ∈ (after b7 (after b5 midS)).mem, w.r = 2 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 24) := by
  decide +kernel

public theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 1088 := by decide

public section

/-! ## The zeroing loop -/

variable [Host] {k : Nat}

/-- **The zeroing loop**, from turn `i`. -/
theorem loop (hp : Placed code k) {env : Env} (hwf : env.WF) {R : MachineState → Prop}
    (cont : ∀ st, Match env (L 22) st.data → st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ColumnWeight.b2Offset) →
      Eventually (step1 Host.exe) R st) :
    ∀ n i, i + n = 21 → ∀ st : MachineState, Match env (L i) st.data →
      st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ColumnWeight.b1Offset) → Eventually (step1 Host.exe) R st := by
  intro n
  induction n with
  | zero =>
    intro i hi st hm hpc
    obtain rfl : i = 21 := by omega
    refine exec_at (infix_of b1_in_code (by simp [b1]) hp) (loop_step 21 (by decide)) hwf nofun
      hpc hm fun st' hm' hpc' ↦ cont st' hm' ?_
    simp only [PcOk, SBool.eval] at hpc'
    rw [hpc']
    rfl
  | succ n ih =>
    intro i hi st hm hpc
    refine exec_at (infix_of b1_in_code (by simp [b1]) hp) (loop_step i (by omega)) hwf nofun
      hpc hm fun st' hm' hpc' ↦ ih (i + 1) (by omega) st' hm' ?_
    simp only [PcOk, SBool.eval, show decide (i < 21) = true from decide_eq_true (by omega),
      ↓reduceIte] at hpc'
    rw [hpc']
    exact hp.label NativeRustcVmX64.Vm.ColumnWeight.label_1_at

/-! ## The contract -/

omit [Host] in
theorem stack_eq : columnWeightStack = 1280 := rfl

/-- **`column_weight` meets its contract.** -/
theorem columnWeight_spec (hp : Placed code k)
    (hsp : Spec (Labels.label NativeRustcVmX64.Vm.StackPoint.entryLabel) StackPointPre StackPointPost)
    (hee : Spec (Labels.label NativeRustcVmX64.Vm.EqEval.entryLabel) EqEvalPre EqEvalPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.ColumnWeight.entryLabel) ColumnWeightPre ColumnWeightPost := by
  rintro m0 ⟨hst, hargs, hpt, hx, ⟨⟨hom, hon⟩, hoS, hoA⟩, hlt⟩
  set o := reg m0 .rdi with hodef
  set xa := rspOf m0 + 8#64 with hxadef
  set fb := stackBelow m0 1088 with hfb
  have hn : 1280 ≤ (rspOf m0).toNat := hst.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hfbN : fb.toNat = (rspOf m0).toNat - 1088 := stackBelow_toNat (by omega)
  have hfnw : NativeRustcVm.NoWrap fb (1088 + 8) := frame_noWrap hst (by decide)
  have hxN : xa.toNat = (rspOf m0).toNat + 8 := args_toNat hargs (by decide)
  have hA2 := hargs.2
  obtain ⟨hxm, hxn⟩ := args_readable hargs (by decide)
  have hxF : NativeRustcVm.Apart fb (1088 + 8) xa (8 * 2) := args_apart hst hargs (by decide) (by decide)
  have hoF : NativeRustcVm.Apart o 24 fb (1088 + 8) :=
    apart_frame hoS hst.1 (by decide)
  have hpw := pairwise3 (R := fun x y : BitVec 64 × Nat ↦ NativeRustcVm.Apart x.1 x.2 y.1 y.2)
    (x := (fb, 1088 + 8)) (y := (xa, 16)) (z := (o, 24)) hxF (Apart.symm' hoF)
    (Apart.symm' hoA)
  have hstack : ∀ q, NativeRustcVm.InRange fb 1088 q →
      NativeRustcVm.InRange (stackBelow m0 columnWeightStack) columnWeightStack q :=
    fun q h ↦ frame_in hst (by decide) h
  -- `b0`, the loop, `b2`: the prologue, `x`, the slots zeroed, `call stack_point`.
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 1088) (rest := [(xa, 16), (o, 24)])
    (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.ColumnWeight.b2Offset + b2.length)).toBitVec)
    ⟨frame_mapped hst (by decide), hfnw⟩ (rest2_ok ⟨hxm, hxn⟩ ⟨hom, hon⟩ fun _ h ↦ h) hpw
  have hal : ∀ j : Nat, j < 16 → (Sym.ptr 0 ((1096 + j : Nat) : Int)).eval
      (frameEnv m0 m0 1088 [(xa, 16), (o, 24)] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.ColumnWeight.b2Offset + b2.length)).toBitVec) =
      xa + BitVec.ofInt 64 (j : Int) := by
    intro j hj
    rw [eval_ptr0, ← hfb, BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_off (by omega), BitVec.toNat_add, BitVec.toNat_ofNat, hxN, hfbN]
    omega
  have hm0 : Match (frameEnv m0 m0 1088 [(xa, 16), (o, 24)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.ColumnWeight.b2Offset + b2.length)).toBitVec) entryS m0 :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨match_rsp, known_ptr rfl rfl, trivial⟩ trivial
      trivial ⟨hal 8 (by decide), hal 0 (by decide), trivial⟩
  unfold NativeRustcVmX64.Vm.ColumnWeight.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.ColumnWeight.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 nofun hm0
    fun st1 hm1 hpc1 ↦ ?_
  refine loop hp hwf0 (fun st2 hm2 hpc2 ↦ ?_) 21 0 rfl st1 hm1 hpc1
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf0 (fun _ _ ↦ rfl) hpc2 hm2
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hpro, hws3, hrdi, hrsi, hrdx, hrcx, hr8, hr9, hrbx, hr14, hr15⟩ :=
    after_eq run_b2 ▸ ok_b2
  have hf3 : Frame m0 1088 slots 0 st3.data :=
    Frame.of_prologue Frame.entry hwf0 hm3 hpro slots_le (by decide)
  have hs3 : NativeRustcVm.SameOutside m0.dmem st3.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 columnWeightStack) columnWeightStack) :=
    fun q hq ↦ sameOutside_low hwf0 hm3 (r := 0) rfl (by decide) hws3 q
      fun h ↦ hq (hstack q h)
  have hsp3 : rspOf st3.data = fb := by rw [hf3.sp, off_zero]
  have hX7 : reg st3.data .rdi = reg m0 .rsi := hm3.regs .rdi _ hrdi
  have hX6 : reg st3.data .rsi = reg m0 .rdx := hm3.regs .rsi _ hrsi
  have hX2 : reg st3.data .rdx = reg m0 .rcx := hm3.regs .rdx _ hrdx
  have hX1 : reg st3.data .rcx = reg m0 .r8 := hm3.regs .rcx _ hrcx
  have hX8 : reg st3.data .r8 = reg m0 .r9 := hm3.regs .r8 _ hr8
  have hX9 : reg st3.data .r9 = off fb 8 := (hm3.regs .r9 _ hr9).trans (eval_ptr0 8)
  have hXb : reg st3.data .rbx = o := (hm3.regs .rbx _ hrbx).trans (eval_ptr rfl)
  have hX14 : reg st3.data .r14 = stackArg m0 1 := by
    rw [show reg st3.data .r14 = _ from hm3.regs .r14 _ hr14, Sym.eval, NativeRustcVmX64.Ring.load_eq_wordOf,
      stackArg_eq]
    rfl
  have hX15 : reg st3.data .r15 = stackArg m0 0 := by
    rw [show reg st3.data .r15 = _ from hm3.regs .r15 _ hr15, Sym.eval, NativeRustcVmX64.Ring.load_eq_wordOf,
      stackArg_eq]
    rfl
  -- `stack_point` into the slots.
  have hpre3 : StackPointPre st3.data := by
    unfold StackPointPre SliceOk Readable OffStack stackPointOut
    rw [hX2, hX1, hX9]
    refine ⟨stackOk_callee hst hf3.kept hsp3 (by decide),
      ⟨⟨Mapped.keeps hpt.1.1 hf3.kept, hpt.1.2⟩, apart_callee hpt.2 hsp3 hst.1 (by decide)⟩,
      ⟨Mapped.keeps (mapped_off (o := 8) (k := 16 * 66) (frame_mapped (F := 1088) hst (by decide))
        (by decide)) hf3.kept, ?_⟩, ?_, ?_, hlt⟩
    · show (off fb 8).toNat + 16 * 66 ≤ 2 ^ 64
      rw [toNat_off (by omega)]
      omega
    · rw [stackBelow_callee hsp3 (by simp only [stackPointStack, selectorPointStack]; omega)]
      have := stackBelow_toNat (m := m0) (n := 1088 + stackPointStack) (by
        simp only [stackPointStack, selectorPointStack]; omega)
      unfold Apart
      rw [toNat_off (by omega), this]
      simp only [stackPointStack, selectorPointStack]
      omega
    · have h := hpt.2
      unfold OffStack Apart at h
      unfold Apart
      rw [toNat_off (by omega)]
      rw [stackBelow_toNat hst.1] at h
      simp only [columnWeightStack, eqEvalStack, ewMulStack] at h
      omega
  refine call_then hpc3 hsp hpre3 fun st4 hpc4 hrsp4 ⟨hres4, hs4, hsv4⟩ ↦ ?_
  rw [hX9, hX7, hX6, hX2, hX1, hX8] at hres4
  rw [hX9] at hs4
  have hR4 : ∀ j, 1064 ≤ j → j < 1088 + 8 → ¬ (NativeRustcVm.InRange (off fb 8) (16 * 66)
      (off fb j) ∨ NativeRustcVm.InRange (stackBelow st3.data stackPointStack) stackPointStack
        (off fb j)) := by
    rintro j hj hj' (h | h)
    · rw [inRange_off_iff (by omega) (by omega)] at h
      omega
    · exact not_callee hst hsp3 (by decide) hj' h
  have hf4 : Frame m0 1088 slots 8 st4.data :=
    Frame.call_slots hf3 hsv4 hrsp4 hs4
      (fun p hp i hi ↦ hR4 _ (by
        simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> simp <;> omega) (by have := slots_le p hp; omega))
      (fun j hj ↦ hR4 _ (by omega) (by omega))
  have hs4' : NativeRustcVm.SameOutside m0.dmem st4.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 columnWeightStack) columnWeightStack) :=
    same_trans hs3 hs4 fun q h ↦ h.elim
      (fun h ↦ hstack q (inRange_of_off (N := 1088) (by unfold NativeRustcVm.NoWrap; omega)
        (by decide) h))
      (fun h ↦ callee_in hst hsp3 (by decide) h)
  have h4b : reg st4.data .rbx = o := (hsv4.1 .rbx rfl).trans hXb
  have h414 : reg st4.data .r14 = stackArg m0 1 := (hsv4.1 .r14 rfl).trans hX14
  have h415 : reg st4.data .r15 = stackArg m0 0 := (hsv4.1 .r15 rfl).trans hX15
  -- `b3`: the tag.
  have hwf4 := frame_wf (m0 := m0) (d := st4.data) (F := 1088) (rest := [(xa, 16), (o, 24)])
    (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.ColumnWeight.b4Offset + b4.length)).toBitVec)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf4.kept, hfnw⟩
    (rest2_ok ⟨hxm, hxn⟩ ⟨hom, hon⟩ hf4.kept) hpw
  have hm4 : Match (frameEnv m0 st4.data 1088 [(xa, 16), (o, 24)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.ColumnWeight.b4Offset + b4.length)).toBitVec) midS st4.data :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hf4.rsp_eval, known_ptr rfl h4b, trivial⟩ trivial
      trivial trivial
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf4 nofun
    (hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.ColumnWeight.b2_next)) hm4 fun st5 hm5 hpc5 ↦ ?_
  simp only [PcOk] at hpc5
  have hc : (SBool.not (SBool.cmp .eq .W64 (.reg .rax) (.lit 1))).eval
      (frameEnv m0 st4.data 1088 [(xa, 16), (o, 24)] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.ColumnWeight.b4Offset + b4.length)).toBitVec) =
      !(reg st4.data .rax == BitVec.ofNat 64 1) := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, Env.ofMachine_regs, low_W64]
  rw [hc] at hpc5
  by_cases hfit : (reg m0 .r8).toNat + ((reg m0 .r9).toNat - (reg m0 .rsi).toNat) ≤ stackPointOut
  · -- `Some`: `b4`, `eq_eval`.
    simp only [hfit, ↓reduceIte] at hres4
    obtain ⟨hrax, hrdx, hz⟩ := hres4
    rw [hrax, show (!((1#64 : BitVec 64) == BitVec.ofNat 64 1)) = false from rfl] at hpc5
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc5
    refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf4 (fun _ _ ↦ rfl)
      (hpc5.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.ColumnWeight.b3_next)) hm5 fun st6 hm6 hpc6 ↦ ?_
    obtain ⟨hmid, hws6, hrdi6, hrsi6, hrdx6, hrcx6, hrbx6⟩ := after_eq run_b4 ▸ ok_b4
    have hm56 : Match (frameEnv m0 st4.data 1088 [(xa, 16), (o, 24)] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.ColumnWeight.b4Offset + b4.length)).toBitVec) (after b4 M3) st6.data := by
      rw [after_eq run_b4]; exact hm6
    have hf6 : Frame m0 1088 slots 0 st6.data := Frame.of_block hf4 hwf4 hm56 hmid slots_le
    have hsp6 : rspOf st6.data = fb := by rw [hf6.sp, off_zero]
    have hs6 : NativeRustcVm.SameOutside st4.data.dmem st6.data.dmem (NativeRustcVm.InRange fb 8) :=
      sameOutside_low hwf4 hm56 (r := 0) rfl (by decide) hws6
    have h6di : reg st6.data .rdi = off fb 8 := (hm56.regs .rdi _ hrdi6).trans (eval_ptr0 8)
    have h6si : reg st6.data .rsi = reg st4.data .rdx := hm56.regs .rsi _ hrsi6
    have h6dx : reg st6.data .rdx = stackArg m0 0 := (hm56.regs .rdx _ hrdx6).trans h415
    have h6cx : reg st6.data .rcx = stackArg m0 1 := (hm56.regs .rcx _ hrcx6).trans h414
    have h6b : reg st6.data .rbx = o := (hm56.regs .rbx _ hrbx6).trans (eval_ptr rfl)
    have hs6' : NativeRustcVm.SameOutside m0.dmem st6.data.dmem
        (NativeRustcVm.InRange (stackBelow m0 columnWeightStack) columnWeightStack) :=
      same_trans hs4' hs6 fun q h ↦ hstack q (inRange_le h (by decide))
    -- The stack point in the slots.
    have hslice : slice st3.data (reg m0 .rcx) (reg m0 .r8) = slice m0 (reg m0 .rcx) (reg m0 .r8) :=
      slice_keep hst hs3 hpt
    rw [hslice] at hz
    set z := stackPoint (placementArg m0) (slice m0 (reg m0 .rcx) (reg m0 .r8)) (reg m0 .r9).toNat
      with hzdef
    have hzn : z.toList.length =
        (reg m0 .r8).toNat + ((reg m0 .r9).toNat - (reg m0 .rsi).toNat) := by
      simp [hzdef, stackPoint, selectorPoint, slice, placementArg]
    have hfit' : (reg m0 .r8).toNat + ((reg m0 .r9).toNat - (reg m0 .rsi).toNat) ≤ 66 := hfit
    have hz6 : NativeRustcVm.EWsAt st6.data.dmem (off fb 8) z.toList :=
      NativeRustcVm.BytesAt.of_sameOutside hz hs6 fun i hi h ↦ by
        rw [NativeRustcVm.length_ewsBytes, hzn] at hi
        rw [off_add, inRange_iff' (by unfold NativeRustcVm.NoWrap; omega),
          toNat_off (by omega)] at h
        omega
    have hzs : slice st6.data (off fb 8) (reg st4.data .rdx) = z := by
      unfold slice
      rw [hrdx, ← hzn, NativeRustcVm.ewsOf_of_ewsAt hz6]
    have hpre6 : EqEvalPre st6.data := by
      unfold EqEvalPre SliceOk Readable OffStack
      rw [h6di, h6si, h6dx, h6cx, hrdx]
      refine ⟨stackOk_callee hst hf6.kept hsp6 (le_of_eq rfl),
        ⟨⟨Mapped.keeps (mapped_off (frame_mapped (F := 1088) hst (by decide)) (by omega))
          hf6.kept, ?_⟩, ?_⟩,
        ⟨⟨Mapped.keeps hx.1.1 hf6.kept, hx.1.2⟩, apart_callee hx.2 hsp6 hst.1 (le_of_eq rfl)⟩⟩
      · show (off fb 8).toNat + _ ≤ 2 ^ 64
        rw [toNat_off (by omega)]
        omega
      · rw [stackBelow_callee hsp6 (by simp only [eqEvalStack, ewMulStack]; omega)]
        have := stackBelow_toNat (m := m0) (n := 1088 + eqEvalStack) (by
          simp only [eqEvalStack, ewMulStack]; omega)
        unfold Apart
        rw [toNat_off (by omega), this]
        simp only [eqEvalStack, ewMulStack]
        omega
    refine call_then hpc6 hee hpre6 fun st7 hpc7 hrsp7 ⟨hv7, hs7, hsv7⟩ ↦ ?_
    rw [h6di, h6si, h6dx, h6cx, hzs, slice_keep hst hs6' hx] at hv7
    have hR7 : ∀ j, j < 1088 + 8 → ¬ (NativeRustcVm.InRange 0 0 (off fb j) ∨
        NativeRustcVm.InRange (stackBelow st6.data eqEvalStack) eqEvalStack (off fb j)) := by
      rintro j hj (h | h)
      · unfold NativeRustcVm.InRange at h; omega
      · exact not_callee hst hsp6 (le_of_eq rfl) hj h
    have hf7 : Frame m0 1088 slots 8 st7.data :=
      Frame.call_slots hf6 hsv7 hrsp7 hs7
        (fun p hp i hi ↦ hR7 _ (by have := slots_le p hp; omega)) (fun j hj ↦ hR7 _ (by omega))
    have hs7' : NativeRustcVm.SameOutside m0.dmem st7.data.dmem
        (NativeRustcVm.InRange (stackBelow m0 columnWeightStack) columnWeightStack) :=
      same_trans hs6' hs7 fun q h ↦ h.elim (fun h ↦ by unfold InRange at h; omega)
        (fun h ↦ callee_in hst hsp6 (le_of_eq rfl) h)
    have h7b : reg st7.data .rbx = o := (hsv7.1 .rbx rfl).trans h6b
    -- `b5`, `b7`: the value and the tag `1` stored, the epilogue.
    have hwf7 := frame_wf (m0 := m0) (d := st7.data) (F := 1088) (rest := [(xa, 16), (o, 24)])
      (vars := fun _ ↦ 0) (ret := 0)
      ⟨Mapped.keeps (frame_mapped hst (by decide)) hf7.kept, hfnw⟩
      (rest2_ok ⟨hxm, hxn⟩ ⟨hom, hon⟩ hf7.kept) hpw
    have hm7 : Match (frameEnv m0 st7.data 1088 [(xa, 16), (o, 24)] (fun _ ↦ 0) 0) midS
        st7.data :=
      match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hf7.rsp_eval, known_ptr rfl h7b, trivial⟩ trivial
        trivial trivial
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 hwf7 nofun
      (hpc7.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.ColumnWeight.b4_next)) hm7 fun st8 hm8 hpc8 ↦ ?_
    simp only [PcOk] at hpc8
    refine exec_at (infix_of b7_in_code (by simp [b7]) hp) (exec_after run_b5 run_b7s) hwf7 nofun
      (hpc8.trans (hp.label NativeRustcVmX64.Vm.ColumnWeight.label_5_at)) hm8 fun st9 hm9 hpc9 ↦ ?_
    obtain ⟨hepi, hw0, hw1, hw2, hws9⟩ := after_eq run_b7s ▸ ok_s
    obtain ⟨hsv9, hrsp9⟩ := Frame.epilogue hf7 hwf7 hm9 hepi
    have hs9 := sameOutside_region hwf7 hm9 (r := 2) rfl hws9
    have ht := wordAt_write hm9 (r := 2) (o := 0) rfl (by decide)
      (fun i hi ↦ by rw [Nat.zero_add]; exact hw0 i hi)
    rw [off_zero, show UInt64.ofBitVec ((Sym.lit 1).eval
      (frameEnv m0 st7.data 1088 [(xa, 16), (o, 24)] (fun _ ↦ 0) 0)) = 1 from rfl] at ht
    have hc0 := wordAt_write hm9 (r := 2) (o := 8) rfl (by decide) hw1
    have hc1 := wordAt_write hm9 (r := 2) (o := 16) rfl (by decide) hw2
    simp only [PcOk] at hpc9
    refine .done _ ⟨by rw [hpc9]; exact hf7.load_ret hst (by decide), hrsp9, ?_, ?_, hsv9⟩
    · simp only [hfit, ↓reduceIte]
      refine ⟨ht, ?_⟩
      rw [show StackWeight.eval (.eq z) (slice m0 (stackArg m0 0) (stackArg m0 1)) =
        ewRet st7.data from hv7.symm]
      exact ewAt_iff.mpr ⟨hc0, by rw [off_off]; exact hc1⟩
    · intro q hq
      rw [hs9 q fun h ↦ hq (.inl h)]
      exact hs7' q fun h ↦ hq (.inr h)
  · -- `None`: `b6`, `b7`.
    simp only [hfit, ↓reduceIte] at hres4
    rw [hres4, show (!((0#64 : BitVec 64) == BitVec.ofNat 64 1)) = true from rfl] at hpc5
    simp only [↓reduceIte] at hpc5
    refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 hwf4 nofun
      (hpc5.trans (hp.label NativeRustcVmX64.Vm.ColumnWeight.label_3_at)) hm5 fun st6 hm6 hpc6 ↦ ?_
    simp only [PcOk] at hpc6
    refine exec_at (infix_of b7_in_code (by simp [b7]) hp) (exec_after run_b6 run_b7n) hwf4 nofun
      (hpc6.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.ColumnWeight.b6_next)) hm6 fun st7 hm7 hpc7 ↦ ?_
    obtain ⟨hepi, hw0, hws7⟩ := after_eq run_b7n ▸ ok_n
    obtain ⟨hsv7, hrsp7⟩ := Frame.epilogue hf4 hwf4 hm7 hepi
    have hs7 := sameOutside_region hwf4 hm7 (r := 2) rfl hws7
    have ht := wordAt_write hm7 (r := 2) (o := 0) rfl (by decide)
      (fun i hi ↦ by rw [Nat.zero_add]; exact hw0 i hi)
    rw [off_zero, show UInt64.ofBitVec ((Sym.lit 0).eval
      (frameEnv m0 st4.data 1088 [(xa, 16), (o, 24)] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.ColumnWeight.b4Offset + b4.length)).toBitVec)) = 0 from rfl] at ht
    simp only [PcOk] at hpc7
    refine .done _ ⟨by rw [hpc7]; exact hf4.load_ret hst (by decide), hrsp7, ?_, ?_, hsv7⟩
    · simp only [hfit, ↓reduceIte]
      exact ht
    · intro q hq
      rw [hs7 q fun h ↦ hq (.inl h)]
      exact hs4' q fun h ↦ hq (.inr h)

end

end NativeRustcVmX64.Ring.Column
