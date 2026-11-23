module

public import NativeRustcVmX64.Arrays.PaddingWeight.Exec
public import NativeRustcVm.Arrays.Folds
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.PaddingWeight.Names

/-!
# `padding_weight` on x86-64

**`paddingWeight_spec`**: rustc's `padding_weight`, placed anywhere in the program, meets
`PaddingWeightPre`/`PaddingWeightPost` given `EW::mul`'s contract. The prologue (`b0`) pushes RBP,
R15-R12, RBX, opens a 56-byte frame and keeps `|point|` there (with the point's end and `n`,
`b1`); the loop (`b2`, `EW::mul`, `b3`, `EW::mul`, `b4`) folds coordinate `i` (at R13) into the
accumulator (R15, R12) with bit `i` of `n` (`Inv`); the epilogue (`b7`) restores the registers and
tail-calls `EW::mul` with `1 + bit_e(n, |point|)` and the accumulator.
-/

namespace NativeRustcVmX64.Arrays.PaddingWeight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.PaddingWeight NativeVm.Model
  NativeRustcVmX64.Field
open NativeRustcVm (ewsOf WordAt)

public section

/-- The point at the entry. -/
abbrev pts (m : MachineData) : List EW := ewsOf m.dmem (reg m .rdi) (reg m .rsi).toNat
/-- Its length. -/
abbrev len (m : MachineData) : Nat := (reg m .rsi).toNat
/-- `n`. -/
abbrev nn (m : MachineData) : Nat := (reg m .rdx).toNat
/-- The frame's base. -/
abbrev fb (m : MachineData) : BitVec 64 := stackBelow m 112

/-- The model's step. -/
def g (n : Nat) (pad : EW) (p : EW × Nat) : EW :=
  (1 + EW.ofNat ((n >>> p.2) % 2)) * p.1 + (1 + EW.ofNat ((n >>> p.2) % 2) + p.1) * pad

/-- The model's fold after `i` coordinates. -/
def pad (m : MachineData) (i : Nat) : EW := (((pts m).zipIdx).take i).foldl (g (nn m)) 1

theorem paddingWeight_eq_pad (m : MachineData) :
    paddingWeight (slice m (reg m .rdi) (reg m .rsi)) (nn m) =
      (1 + EW.ofNat ((nn m >>> len m) % 2)) * pad m (len m) := by
  unfold slice pad paddingWeight
  rw [← Array.foldl_toList, Array.toList_zipIdx, List.take_of_length_le (by simp)]
  simp only [List.size_toArray, NativeRustcVm.length_ewsOf]
  rfl

theorem lt_len {m : MachineData} {i : Nat} (h : i < len m) : i < (pts m).length := by
  simp only [pts, len, NativeRustcVm.length_ewsOf] at h ⊢; exact h

theorem pad_succ (m : MachineData) {i : Nat} (h : i < len m) :
    pad m (i + 1) = g (nn m) (pad m i) ((pts m)[i]'(lt_len h), i) := by
  unfold pad
  rw [NativeRustcVm.foldl_take_succ _ _ _ (by rw [List.length_zipIdx]; exact lt_len h),
    List.getElem_zipIdx, Nat.zero_add]

/-- The frame's words the loop reads: the point's end, `n`. -/
structure Locals (m0 : MachineData) (d : DataMem) : Prop where
  fin : WordAt d (fb m0 + BitVec.ofNat 64 24)
    (UInt64.ofBitVec (reg m0 .rdi + BitVec.ofNat 64 (16 * len m0)))
  n : WordAt d (fb m0 + BitVec.ofNat 64 32) (UInt64.ofBitVec (reg m0 .rdx))

/-- **The loop head** `NativeRustcVmX64.Vm.PaddingWeight.label_3`, `i` coordinates folded. -/
structure Inv (m0 : MachineData) (i : Nat) (s : MachineData) : Prop where
  body : Body m0 112 paddingWeightStack slots 0 0 s
  lt : i < len m0
  rcx : reg s .rcx = BitVec.ofNat 64 i
  rbp : reg s .rbp = reg m0 .rdx
  r13 : reg s .r13 = reg m0 .rdi + BitVec.ofNat 64 (16 * i)
  pad : ewArg (reg s .r15) (reg s .r12) = pad m0 i
  lenw : WordAt s.dmem (fb m0 + BitVec.ofNat 64 16) (UInt64.ofBitVec (reg m0 .rsi))
  loc : Locals m0 s.dmem

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.PaddingWeight.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.PaddingWeight.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.PaddingWeight.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.PaddingWeight.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.PaddingWeight.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.PaddingWeight.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.PaddingWeight.b6Offset) :=
  b6_in_code.trans hp.1 (by simp [b6])
theorem hb7 (hp : Placed code k) : b7.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.PaddingWeight.b7Offset) :=
  b7_in_code.trans hp.1 (by simp [b7])

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.PaddingWeight.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.PaddingWeight.b0Offset) :=
  hp.label NativeRustcVmX64.Vm.PaddingWeight.entry_at
theorem lbl_1 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.PaddingWeight.label_1 = Host.addrOf (k + NativeRustcVmX64.Vm.PaddingWeight.b6Offset) :=
  hp.label NativeRustcVmX64.Vm.PaddingWeight.label_1_at
theorem lbl_3 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.PaddingWeight.label_3 = Host.addrOf (k + NativeRustcVmX64.Vm.PaddingWeight.b2Offset) :=
  hp.label NativeRustcVmX64.Vm.PaddingWeight.label_3_at
theorem lbl_4 (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.PaddingWeight.label_4 = Host.addrOf (k + NativeRustcVmX64.Vm.PaddingWeight.b7Offset) :=
  hp.label NativeRustcVmX64.Vm.PaddingWeight.label_4_at

/-- `padding_weight`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧ PaddingWeightPost m0 s.data

/-- **`NativeRustcVmX64.Vm.PaddingWeight.label_4`** (`b7`): `1 + bit_e(n, |point|)`, the epilogue, the tail call. -/
theorem finish (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : PaddingWeightPre m0) {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PaddingWeight.b7Offset)) (hb : Body m0 112 paddingWeightStack slots 0 0 s.data)
    (hrbp : reg s.data .rbp = reg m0 .rdx)
    (hlenw : WordAt s.data.dmem (fb m0 + BitVec.ofNat 64 16) (UInt64.ofBitVec (reg m0 .rsi)))
    (hpad : ewArg (reg s.data .r15) (reg s.data .r12) = pad m0 (len m0)) :
    Eventually (step1 Host.exe) (Post m0) s := by
  have hS := hpre.1
  have h112 : 112 ≤ paddingWeightStack := by decide
  have hlt := hpre.2.1
  have hwf := hb.wf (vars := fun _ ↦ 0) (ret := 0) hS h112
  refine exec_at (hb7 hp) run_b7 hwf (by intro l h; cases h) hpc hb.mid_match fun s' hm' hpc' ↦ ?_
  obtain ⟨hr, hsp, hmem⟩ := after_eq run_b7 ▸ b7_tail
  simp only [PcOk] at hpc'
  have hl16 : (frameEnv m0 s.data 112).load 0 16 8 = reg m0 .rsi := load_word hlenw
  have hdi : reg s'.data .rdi = BitVec.ofNat 64 (1 - (nn m0 >>> len m0) % 2) := by
    rw [show reg s'.data .rdi = _ from hm'.regs .rdi (.bin .and .W32 (.un .not .W32
      (.bin .shr .W64 (.reg .rbp) (.load 0 16 8))) (.lit 1)) rfl]
    show BinOp.apply .and .W32 (UnOp.apply .not .W32 (BinOp.apply .shr .W64
      (reg s.data .rbp) ((frameEnv m0 s.data 112).load 0 16 8))) (BitVec.ofNat 64 1) = _
    rw [hrbp, hl16, nbit_eval _ _ hlt]
  have hargs : EW.mul (ewArg (reg s'.data .rdi) (reg s'.data .rsi))
      (ewArg (reg s'.data .rdx) (reg s'.data .rcx)) =
        (1 + EW.ofNat ((nn m0 >>> len m0) % 2)) * pad m0 (len m0) := by
    rw [hdi, show reg s'.data .rsi = BitVec.ofNat 64 0 from hm'.regs .rsi (.lit 0) rfl,
      show reg s'.data .rdx = reg s.data .r15 from hm'.regs .rdx (.reg .r15) rfl,
      show reg s'.data .rcx = reg s.data .r12 from hm'.regs .rcx (.reg .r12) rfl, hpad,
      one_add_bit _ (Nat.mod_lt _ (by decide))]
    rfl
  refine Eventually.mono (hb.tail_mul hmul hS h112 (by decide) hm' hpc' hr hsp hmem
    (fun _ _ ↦ not_inRange_zero _)) fun s'' ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, ?_, h4, h5⟩
  rw [h3, hargs, ← paddingWeight_eq_pad]

/-- **A turn of the loop**: coordinate `i` folded in, back at the head or out of the loop and
returned. -/
theorem step (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : PaddingWeightPre m0) {i : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PaddingWeight.b2Offset)) (hI : Inv m0 i s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ Post m0 s' ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PaddingWeight.b2Offset) ∧ Inv m0 (i + 1) s'.data)) s := by
  have hS := hpre.1
  have hA := SliceIn.of_ok hpre.2.2
  have h112 : 112 ≤ paddingWeightStack := by decide
  have hlt := hI.lt
  have hl : len m0 = (reg m0 .rsi).toNat := rfl
  have h64 := hpre.2.1
  have hlen := lt_of_offStack hpre.2.2.1.2 hpre.2.2.2
  -- `b2`: the coordinate, `(1 + b)·r`
  obtain ⟨hwf1, hm1, hel⟩ := hI.body.elem (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.PaddingWeight.b3Offset)).toBitVec) hS h112
    hA hlt (x := .reg .r13) (o := 0) (by rw [eval_reg, add_ofNat_zero]; exact hI.r13)
  refine exec_at (hb2 hp) run_b2 hwf1 (fun _ _ ↦ rfl) hpc hm1 fun s1 hm1' hpc1 ↦ ?_
  obtain ⟨hk1, hsp1, hw1, h56, ho16, ho24, ho32⟩ := after_eq run_b2 ▸ b2_call
  have hnb : reg s1.data .rbp = BitVec.ofNat 64 (1 - (nn m0 >>> i) % 2) := by
    rw [show reg s1.data .rbp = _ from hm1'.regs .rbp (.bin .and .W32 (.un .not .W32
      (.bin .shr .W64 (.reg .rbp) (.reg .rcx))) (.lit 1)) rfl]
    show BinOp.apply .and .W32 (UnOp.apply .not .W32 (BinOp.apply .shr .W64
      (reg s.data .rbp) (reg s.data .rcx))) (BitVec.ofNat 64 1) = _
    rw [hI.rbp, hI.rcx, nbit_eval _ _ (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := i) (b := 2 ^ 64) (by omega)]
  have hr : ewArg (reg s1.data .r14) (reg s1.data .rbx) = (pts m0)[i]'(lt_len hlt) := by
    rw [show reg s1.data .r14 = _ from hm1'.regs .r14 (.load 1 0 8) rfl,
      show reg s1.data .rbx = _ from hm1'.regs .rbx (.load 1 8 8) rfl, eval_load, eval_load, hel]
  have hargs1 : EW.mul (ewArg (reg s1.data .rdi) (reg s1.data .rsi))
      (ewArg (reg s1.data .rdx) (reg s1.data .rcx)) =
        (1 + EW.ofNat ((nn m0 >>> i) % 2)) * (pts m0)[i]'(lt_len hlt) := by
    rw [show reg s1.data .rdi = reg s1.data .rbp from
        (hm1'.regs .rdi _ rfl).trans (hm1'.regs .rbp _ rfl).symm,
      show reg s1.data .rsi = BitVec.ofNat 64 0 from hm1'.regs .rsi (.lit 0) rfl,
      show reg s1.data .rdx = reg s1.data .r14 from
        (hm1'.regs .rdx _ rfl).trans (hm1'.regs .r14 _ rfl).symm,
      show reg s1.data .rcx = reg s1.data .rbx from
        (hm1'.regs .rcx _ rfl).trans (hm1'.regs .rbx _ rfl).symm,
      hr, hnb, one_add_bit _ (Nat.mod_lt _ (by decide))]
    rfl
  have hw56 : WordAt s1.data.dmem (fb m0 + BitVec.ofNat 64 56)
      (UInt64.ofBitVec (BitVec.ofNat 64 (i + 1))) := by
    have := wordAt_of_write hm1' (r := 0) (o := 56) rfl (by omega) h56
    rwa [eval_add, eval_reg, eval_lit, show (elemEnv m0 s.data 112 (reg m0 .rdi) i
      (Host.addrOf (k + NativeRustcVmX64.Vm.PaddingWeight.b3Offset)).toBitVec).regs .rcx = reg s.data .rcx from rfl, hI.rcx,
      ← BitVec.ofNat_add] at this
  have hlenw1 := wordAt_keep hm1' (r := 0) (o := 16) rfl (by omega) ho16 hI.lenw
  have hloc1 : Locals m0 s1.data.dmem :=
    ⟨wordAt_keep hm1' (r := 0) (o := 24) rfl (by omega) ho24 hI.loc.fin,
      wordAt_keep hm1' (r := 0) (o := 32) rfl (by omega) ho32 hI.loc.n⟩
  have e1 : ∀ r ∈ [Reg64.r12, .r13, .r15], reg s1.data r = reg s.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Match.reg_eq hm1 hm1' rfl rfl
  refine Body.call_mul (L := 64) hmul hI.body hS (by decide) (by decide) slots_ok hwf1 hm1 hm1'
    hpc1 hk1 hsp1 hw1 fun s2 hpc2 hb2' hprod1 hsv1 _ hfr1 ↦ ?_
  rw [hargs1] at hprod1
  have hfr1' : ∀ o, o + 8 ≤ 120 → ∀ j < 8,
      s2.data.dmem.get? (fb m0 + BitVec.ofNat 64 o + BitVec.ofNat 64 j) =
        s1.data.dmem.get? (fb m0 + BitVec.ofNat 64 o + BitVec.ofNat 64 j) := fun o ho j hj ↦ by
    rw [addr_add]; exact hfr1 _ (by omega)
  -- `b3`: `(1 + b + r)·pad`, the first product kept
  have hwf3 := hb2'.wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.PaddingWeight.b4Offset)).toBitVec) hS
    h112
  refine exec_at (hb3 hp) run_b3 hwf3 (fun _ _ ↦ rfl) hpc2 hb2'.mid_match fun s3 hm3 hpc3 ↦ ?_
  obtain ⟨hk3, hsp3, hw3, h40, h48, ho16', ho24', ho32', ho56'⟩ := after_eq run_b3 ▸ b3_call
  have hargs3 : EW.mul (ewArg (reg s3.data .rdi) (reg s3.data .rsi))
      (ewArg (reg s3.data .rdx) (reg s3.data .rcx)) =
        (1 + EW.ofNat ((nn m0 >>> i) % 2) + (pts m0)[i]'(lt_len hlt)) * pad m0 i := by
    rw [show reg s3.data .rdi = _ from hm3.regs .rdi (.bin .xor .W64 (.reg .r14) (.reg .rbp)) rfl,
      show reg s3.data .rsi = _ from hm3.regs .rsi (.reg .rbx) rfl,
      show reg s3.data .rdx = _ from hm3.regs .rdx (.reg .r15) rfl,
      show reg s3.data .rcx = _ from hm3.regs .rcx (.reg .r12) rfl, eval_xor, eval_reg, eval_reg,
      eval_reg, eval_reg, eval_reg]
    show EW.mul (ewArg (reg s2.data .r14 ^^^ reg s2.data .rbp) (reg s2.data .rbx))
      (ewArg (reg s2.data .r15) (reg s2.data .r12)) = _
    rw [hsv1 .r14 rfl, hsv1 .rbp rfl, hsv1 .rbx rfl, hsv1 .r15 rfl, hsv1 .r12 rfl, ewArg_xor_lo,
      hr, hnb, e1 .r15 (by simp), e1 .r12 (by simp), hI.pad,
      show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, one_add_bit _ (Nat.mod_lt _ (by decide))]
    rfl
  have hw40 := wordAt_of_write hm3 (r := 0) (o := 40) rfl (by omega) h40
  have hw48 := wordAt_of_write hm3 (r := 0) (o := 48) rfl (by omega) h48
  have hw56' := wordAt_keep hm3 (r := 0) (o := 56) rfl (by omega) ho56'
    (wordAt_congr hw56 (hfr1' 56 (by omega)))
  have hlenw3 := wordAt_keep hm3 (r := 0) (o := 16) rfl (by omega) ho16'
    (wordAt_congr hlenw1 (hfr1' 16 (by omega)))
  have hloc3 : Locals m0 s3.data.dmem :=
    ⟨wordAt_keep hm3 (r := 0) (o := 24) rfl (by omega) ho24'
      (wordAt_congr hloc1.fin (hfr1' 24 (by omega))),
     wordAt_keep hm3 (r := 0) (o := 32) rfl (by omega) ho32'
      (wordAt_congr hloc1.n (hfr1' 32 (by omega)))⟩
  refine Body.call_mul (L := 64) (rs := []) hmul hb2' hS (by decide) (by decide) slots_ok hwf3
    hb2'.mid_match hm3 hpc3 hk3 hsp3 hw3 fun s4 hpc4 hb4' hprod2 hsv2 _ hfr2 ↦ ?_
  rw [hargs3] at hprod2
  have hfr2' : ∀ o, o + 8 ≤ 120 → ∀ j < 8,
      s4.data.dmem.get? (fb m0 + BitVec.ofNat 64 o + BitVec.ofNat 64 j) =
        s3.data.dmem.get? (fb m0 + BitVec.ofNat 64 o + BitVec.ofNat 64 j) := fun o ho j hj ↦ by
    rw [addr_add]; exact hfr2 _ (by omega)
  have hw40' := wordAt_congr hw40 (hfr2' 40 (by omega))
  have hw48' := wordAt_congr hw48 (hfr2' 48 (by omega))
  have hw56'' := wordAt_congr hw56' (hfr2' 56 (by omega))
  have hlenw4 := wordAt_congr hlenw3 (hfr2' 16 (by omega))
  have hloc4 : Locals m0 s4.data.dmem :=
    ⟨wordAt_congr hloc3.fin (hfr2' 24 (by omega)), wordAt_congr hloc3.n (hfr2' 32 (by omega))⟩
  have hr13 : reg s4.data .r13 = reg m0 .rdi + BitVec.ofNat 64 (16 * i) := by
    rw [hsv2 .r13 rfl, show reg s3.data .r13 = reg s2.data .r13 from
      Match.reg_eq hb2'.mid_match hm3 rfl rfl, hsv1 .r13 rfl, e1 .r13 (by simp), hI.r13]
  -- `b4`: add the products, restore `n`, advance, compare
  have hwf4 := hb4'.wf (vars := fun _ ↦ 0) (ret := 0) hS h112
  refine exec_at (hb4 hp) run_b4 hwf4 (by intro l h; cases h) hpc4 hb4'.mid_match
    fun s5 hm5 hpc5 ↦ ?_
  have hb5' := hb4'.of_block hb4'.mid_match hm5 hwf4 rfl (after_eq run_b4 ▸ b4_keeps)
  have hdm5 : s5.data.dmem = s4.data.dmem := by
    exact hm5.dmem_eq hwf4 rfl
  have l40 : (frameEnv m0 s4.data 112).load 0 40 8 = reg s2.data .rax := load_word hw40'
  have l48 : (frameEnv m0 s4.data 112).load 0 48 8 = reg s2.data .rdx := load_word hw48'
  have l32 : (frameEnv m0 s4.data 112).load 0 32 8 = reg m0 .rdx := load_word hloc4.n
  have l24 : (frameEnv m0 s4.data 112).load 0 24 8 =
      reg m0 .rdi + BitVec.ofNat 64 (16 * len m0) := load_word hloc4.fin
  have l56 : (frameEnv m0 s4.data 112).load 0 56 8 = BitVec.ofNat 64 (i + 1) := load_word hw56''
  have hpad : ewArg (reg s5.data .r15) (reg s5.data .r12) = pad m0 (i + 1) := by
    rw [show reg s5.data .r15 = _ from hm5.regs .r15 (.bin .xor .W64 (.reg .rax) (.load 0 40 8))
        rfl,
      show reg s5.data .r12 = _ from hm5.regs .r12 (.bin .xor .W64 (.reg .rdx) (.load 0 48 8))
        rfl, eval_xor, eval_xor, eval_reg, eval_reg, eval_load, eval_load, l40, l48, ewArg_xor]
    show ewRet s4.data + ewRet s2.data = _
    rw [hprod2, hprod1, pad_succ m0 hlt, ew_add_comm]
    rfl
  have hrbp : reg s5.data .rbp = reg m0 .rdx := by
    rw [show reg s5.data .rbp = _ from hm5.regs .rbp (.load 0 32 8) rfl, eval_load, l32]
  have hrcx : reg s5.data .rcx = BitVec.ofNat 64 (i + 1) := by
    rw [show reg s5.data .rcx = _ from hm5.regs .rcx (.load 0 56 8) rfl, eval_load, l56]
  have hr13' : reg s5.data .r13 = reg m0 .rdi + BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [show reg s5.data .r13 = _ from hm5.regs .r13 (.bin .add .W64 (.lit 16) (.reg .r13)) rfl,
      eval_add, eval_lit, eval_reg]
    show BitVec.ofNat 64 16 + reg s4.data .r13 = _
    rw [hr13, add16]
  simp only [PcOk] at hpc5
  rw [eval_not, eval_cmp_eq, eval_add, eval_lit, eval_reg, eval_load, l24,
    show (frameEnv m0 s4.data 112).regs .r13 = reg s4.data .r13 from rfl, hr13, add16,
    beq_add_left, ofNat_beq (by omega) (by omega)] at hpc5
  obtain ⟨hT, hF⟩ := pc_cond hpc5
  by_cases hlast : 16 * (i + 1) = 16 * len m0
  · have hpc5' := hF (by simp [hlast])
    simp only [NativeRustcVmX64.Vm.PaddingWeight.b4_length] at hpc5'
    refine exec_at (hb5 hp) run_b5 (Env.wf_nil _) (by intro l h; cases h) hpc5' (match_nil _)
      fun s6 hm6 hpc6 ↦ ?_
    have hb6' := hb5'.of_block (match_nil _) hm6 (Env.wf_nil _) rfl (after_eq run_b5 ▸ b5_keeps)
    have hdm6 : s6.data.dmem = s5.data.dmem := hm6.dmem_eq (Env.wf_nil _) rfl
    simp only [PcOk] at hpc6
    refine Eventually.mono (finish hp hmul hpre (hpc6.trans (lbl_4 hp)) hb6' ?_ ?_ ?_)
      fun _ h ↦ Or.inl h
    · rw [show reg s6.data .rbp = reg s5.data .rbp from Match.reg_eq (match_nil _) hm6 rfl rfl,
        hrbp]
    · rw [hdm6, hdm5]; exact hlenw4
    · rw [show reg s6.data .r15 = reg s5.data .r15 from Match.reg_eq (match_nil _) hm6 rfl rfl,
        show reg s6.data .r12 = reg s5.data .r12 from Match.reg_eq (match_nil _) hm6 rfl rfl,
        hpad, show i + 1 = len m0 by omega]
  · exact .done _ (Or.inr ⟨(hT (by simp [hlast])).trans (lbl_3 hp),
      ⟨hb5', by omega, hrcx, hrbp, hr13', hpad, hdm5 ▸ hlenw4, hdm5 ▸ hloc4⟩⟩)

/-- **`padding_weight` meets its contract.** -/
theorem paddingWeight_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.PaddingWeight.entryLabel) PaddingWeightPre PaddingWeightPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  have hS := hpre.1
  have h112 : 112 ≤ paddingWeightStack := by decide
  have hwf := frame_wf (m := m0) (vars := fun _ ↦ 0) (ret := 0) (stackOk_mono hS h112)
    fun _ h ↦ h
  have hl : len m0 = (reg m0 .rsi).toNat := rfl
  have hlen := lt_of_offStack hpre.2.2.1.2 hpre.2.2.2
  have hx : BitVec.ofNat 64 (len m0) = m0.regs.get64 .rsi := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine exec_then (hb0 hp) run_b0 hwf (by intro l h; cases h) match_frame fun s1 hm1 hpc1 ↦ ?_
  simp only [PcOk, NativeRustcVmX64.Vm.PaddingWeight.b0_length] at hpc1
  rw [eval_test, eval_reg, Env.ofMachine_regs, ← hx, ofNat_beq (by omega) (by decide)] at hpc1
  obtain ⟨hT, hF⟩ := pc_cond hpc1
  by_cases hz : len m0 = 0
  · -- `|point| = 0`: the accumulator `1`.
    have hpc1 := hT (decide_eq_true hz)
    refine exec_at (hb6 hp) (exec_after run_b0 run_b6) hwf (by intro l h; cases h)
      (hpc1.trans (lbl_1 hp)) hm1 fun s2 hm2 hpc2 ↦ ?_
    simp only [PcOk, NativeRustcVmX64.Vm.PaddingWeight.b6_length] at hpc2
    obtain ⟨hw, hregs, hmem, hsp, h16⟩ := after_eq run_b6 ▸ b6_entry
    have hb2 := Body.of_entry (oa := 0) (on := 0) hS h112 hm2 hsp hw hregs hmem
    have h16w : WordAt s2.data.dmem (fb m0 + BitVec.ofNat 64 16) (UInt64.ofBitVec (reg m0 .rsi)) := by
      have := wordAt_of_write hm2 (r := 0) (o := 16) rfl (by omega) h16
      rw [eval_reg] at this
      exact this
    have hrbp : reg s2.data .rbp = reg m0 .rdx := hm2.regs .rbp (.reg .rdx) rfl
    refine finish hp hmul hpre hpc2 hb2 hrbp h16w ?_
    rw [show reg s2.data .r15 = 1#64 from hm2.regs .r15 _ rfl,
      show reg s2.data .r12 = 0#64 from hm2.regs .r12 _ rfl]
    unfold pad
    rw [hz, List.take_zero, List.foldl_nil]
    rfl
  · -- the loop.
    have hpc1 := hF (fun h ↦ hz (of_decide_eq_true h))
    refine exec_at (hb1 hp) (exec_after run_b0 run_b1) hwf (by intro l h; cases h) hpc1 hm1
      fun s2 hm2 hpc2 ↦ ?_
    simp only [PcOk, NativeRustcVmX64.Vm.PaddingWeight.b1_length] at hpc2
    obtain ⟨hw, hregs, hmem, hsp, h16, h24, h32⟩ := after_eq run_b1 ▸ b1_entry
    have hfin : reg m0 .rdi + reg m0 .rsi <<< 4 = reg m0 .rdi + BitVec.ofNat 64 (16 * len m0) := by
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      show (len m0) * 2 ^ 4 % 2 ^ 64 = _
      omega
    have hI : Inv m0 0 s2.data := by
      refine ⟨Body.of_entry hS h112 hm2 hsp hw hregs hmem, Nat.pos_of_ne_zero hz,
        hm2.regs .rcx _ rfl, hm2.regs .rbp _ rfl, ?_, ?_,
        ?_, ⟨?_, ?_⟩⟩
      · rw [show reg s2.data .r13 = reg m0 .rdi from hm2.regs .r13 _ rfl, add_ofNat_zero]
      · rw [show reg s2.data .r15 = 1#64 from hm2.regs .r15 _ rfl,
          show reg s2.data .r12 = 0#64 from hm2.regs .r12 _ rfl]
        unfold pad
        rw [List.take_zero, List.foldl_nil]
        rfl
      · have := wordAt_of_write hm2 (r := 0) (o := 16) rfl (by omega) h16
        rw [eval_reg] at this
        exact this
      · have := wordAt_of_write hm2 (r := 0) (o := 24) rfl (by omega) h24
        rw [eval_add, eval_shl_lit (hj := by decide), eval_reg, eval_reg, Env.ofMachine_regs,
          Env.ofMachine_regs, hfin] at this
        exact this
      · have := wordAt_of_write hm2 (r := 0) (o := 32) rfl (by omega) h32
        rw [eval_reg] at this
        exact this
    refine Sym.loop (fun n s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PaddingWeight.b2Offset) ∧ ∃ i, len m0 - i = n ∧
      Inv m0 i s.data) (fun n s ⟨hpc, i, hn, hI⟩ ↦ ?_) ⟨hpc2, 0, rfl, hI⟩
    refine Eventually.mono (step hp hmul hpre hpc hI) fun s' h ↦ ?_
    rcases h with h | ⟨hpc', hI'⟩
    · exact Or.inl h
    · exact Or.inr ⟨len m0 - (i + 1), by have := hI'.lt; omega, hpc', i + 1, rfl, hI'⟩

end

end NativeRustcVmX64.Arrays.PaddingWeight
