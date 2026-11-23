module

public import NativeRustcVmX64.Whir.EachRowOfNextLevel.IterE
public import NativeRustcVmX64.Whir.MathFrame
public import NativeRustcVmX64.Code.Vm.EachRowOfNextLevel.Names

/-!
# `each_row` with `next_level`'s closure: adding a row's term (x86-64)

After `EW::mul` returned row `j`'s term (RAX, RDX) with the batched value's limbs in R12, R13
(`AtB8`): `b8` stores their sum at `&mut batched` and reads the rows left: the exit after the last
row, else the invariant before row `j + 1` (`b8_step`). Row `j`'s term (`nextTerm_eq`): the query
weight times the folded row plus the scaled `novel_eval`.
-/

namespace NativeRustcVmX64.Whir.EachRowOfNextLevel

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmX64.Vm.EachRowOfNextLevel
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off OptEWAt)

@[expose] public section

/-- Row `j`'s term. -/
abbrev termJ (rows : Array (Array UInt64)) (m0 : MachineData) (j : Nat) : EW :=
  EachRow.nextTerm (reg m0 .rdi).toNat (reg m0 .r8).toNat (eachRowArgs m0).2 (highOf m0)
    (qsOf m0) rows (qwOf m0) j

/-- **At `b8`**, after `EW::mul`: row `j`'s term in RAX, RDX, the batched value's limbs in R12,
R13. -/
structure AtB8 (rows : Array (Array UInt64)) (m0 : MachineData) (j : Nat) (m : MachineData) :
    Prop where
  fr : FR m0 8 m
  hj : j < rows.size
  hjq : j < (qsOf m0).size
  mm : MidN rows m0 j m.dmem
  rax : reg m .rax = (termJ rows m0 j).c0.toBitVec
  rdx : reg m .rdx = (termJ rows m0 j).c1.toBitVec
  r12 : reg m .r12 = (parOf rows m0 j).c0.toBitVec
  r13 : reg m .r13 = (parOf rows m0 j).c1.toBitVec
  rbx : reg m .rbx = BitVec.ofNat 64 (j + 1)
  r15 : reg m .r15 = reg m0 .rsi + BitVec.ofNat 64 (8 * (j + 1))
  r14 : reg m .r14 = bOf m0

end

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData} {j : Nat}

/-- **Row `j`'s term**: the query weight times the folded row plus the scaled `novel_eval`. -/
theorem nextTerm_eq (hj : j < rows.size) (hjq : j < (qsOf m0).size) :
    termJ rows m0 j = (qwOf m0).getD j 0 *
      (foldJ rows m0 j hj hjq + scaleJ m0 ((qsOf m0)[j]'hjq)) := by
  unfold termJ EachRow.nextTerm
  rw [show rows.getD j #[] = rows[j] by simp [Array.getD, hj],
    show (qsOf m0).getD j 0 = (qsOf m0)[j] by simp [Array.getD, hjq]]

/-- The sum the code forms, limb by limb, with the limbs swapped. -/
theorem xor_add (f s : EW) :
    (⟨UInt64.ofBitVec (s.c0.toBitVec ^^^ f.c0.toBitVec),
      UInt64.ofBitVec (s.c1.toBitVec ^^^ f.c1.toBitVec)⟩ : EW) = f + s := by
  show _ = EW.add f s
  unfold EW.add
  rw [show UInt64.ofBitVec (s.c0.toBitVec ^^^ f.c0.toBitVec) = s.c0 ^^^ f.c0 from rfl,
    show UInt64.ofBitVec (s.c1.toBitVec ^^^ f.c1.toBitVec) = s.c1 ^^^ f.c1 from rfl,
    UInt64.xor_comm s.c0, UInt64.xor_comm s.c1]

variable [Host] {k : Nat}

/-- **Adding row `j`'s term**: from `b8` to the invariant before row `j + 1` or the exit. -/
theorem b8_step (hp : Placed code k) (c : Ctx rows op m0) {m : MachineData} (h : AtB8 rows m0 j m)
    (cont : ∀ m', Inv rows m0 (j + 1) m' →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m', Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b9Offset)⟩) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b8Offset)⟩ := by
  have hl := lay c
  have hrs : rows.size ≤ 256 := c.rowsAt.2.1
  have hjr := h.hj
  let env := EachRow.envE m0 m 1984 0 [(bOf m0, 16)] (fun _ ↦ 0) 0
  have hwf : env.WF := env1 c h.fr c.bin 0
  have hm : Match env batS m :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨h.fr.match_rsp, by
        show reg m .r14 = bOf m0 + BitVec.ofInt 64 0
        rw [h.r14]
        exact (BitVec.add_zero _).symm, trivial⟩ trivial trivial trivial
  have hk8 : b8.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b8Offset) := b8_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hl120 : env.load 0 120 8 = BitVec.ofNat 64 (rows.size - (j + 1)) :=
    NativeRustcVmX64.Arrays.load_word h.mm.w120
  refine exec_then hk8 run_b8 hwf (fun _ h ↦ by cases h) hm fun st hm1 hpc ↦ ?_
  rw [← after_eq run_b8] at hm1
  have hs : SameOutside m.dmem st.data.dmem (InRange (bOf m0) 16) :=
    NativeRustcVmX64.Whir.same_region_le hm1 hwf (r := 1) rfl le_rfl
      (by rw [after_eq run_b8]; decide)
  have hfr : FR m0 8 st.data :=
    h.fr.stepR ((rv hm1 (v := .ptr 0 8) rfl).trans (EachRow.eval_ptr0 8)) (hm1.kept hwf) hs
      (fun q hq ↦ .inr hq) fun p hp i hi ↦ notB c (by
        simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega)
  have hP := h.mm.bat
  have hT := nextTerm_eq (m0 := m0) hjr h.hjq
  have w0 := NativeRustcVmX64.Transcript.wordAt_write hm1 (r := 1) (o := 0) rfl (by decide)
    (v := .bin .xor .W64 (.reg .rax) (.reg .r12)) (by rw [after_eq run_b8]; decide)
  have w8 := NativeRustcVmX64.Transcript.wordAt_write hm1 (r := 1) (o := 8) rfl (by decide)
    (v := .bin .xor .W64 (.reg .rdx) (.reg .r13)) (by rw [after_eq run_b8]; decide)
  have hbat : EWAt st.data.dmem (bOf m0) (parOf rows m0 (j + 1)) := by
    show EWAt _ _ (EachRow.nextPartial _ _ _ _ _ _ _ (j + 1))
    rw [EachRow.nextPartial_succ]
    refine NativeRustcVm.ewAt_iff.mpr ⟨?_, ?_⟩
    · have e : (Sym.bin .xor .W64 (.reg .rax) (.reg .r12)).eval env =
          ((parOf rows m0 j) + termJ rows m0 j).c0.toBitVec := by
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
        show reg m .rax ^^^ reg m .r12 = _
        rw [h.rax, h.r12]
        show _ = (EW.add _ _).c0.toBitVec
        unfold EW.add
        rw [UInt64.toBitVec_xor, BitVec.xor_comm]
      rw [e, UInt64.ofBitVec_toBitVec] at w0
      have := w0
      rwa [show off (bOf m0) 0 = bOf m0 from NativeRustcVm.addr_add_zero _] at this
    · have e : (Sym.bin .xor .W64 (.reg .rdx) (.reg .r13)).eval env =
          ((parOf rows m0 j) + termJ rows m0 j).c1.toBitVec := by
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
        show reg m .rdx ^^^ reg m .r13 = _
        rw [h.rdx, h.r13]
        show _ = (EW.add _ _).c1.toBitVec
        unfold EW.add
        rw [UInt64.toBitVec_xor, BitVec.xor_comm]
      rw [e, UInt64.ofBitVec_toBitVec] at w8
      exact w8
  have hlow : Low m0 st.data.dmem := h.mm.low.keepR hs (bR c)
  simp only [PcOk] at hpc
  rw [after_eq run_b8] at hm1
  have hc : (SBool.cmp .eq .W64 (.bin .and .W64 (.load 0 120 8) (.load 0 120 8)) (.lit 0)).eval env =
      decide (rows.size = j + 1) := by
    rw [NativeRustcVmX64.Arrays.eval_test, Sym.eval, hl120,
      NativeRustcVmX64.Arrays.beq_ofNat _ (by decide), BitVec.toNat_ofNat]
    simp only [decide_eq_decide]
    omega
  rw [hc] at hpc
  by_cases hlast : rows.size = j + 1
  · simp only [hlast, decide_true, ↓reduceIte] at hpc
    rw [show Labels.label NativeRustcVmX64.Vm.EachRowOfNextLevel.label_17 = Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b27Offset) from hp.label NativeRustcVmX64.Vm.EachRowOfNextLevel.label_17_at]
      at hpc
    obtain ⟨d, pc⟩ := st
    simp only at hpc hfr hbat
    subst hpc
    refine exit_17 hp c hfr ?_
    rw [batched_end (j := j + 1) (by have := h.hjq; omega)]
    exact hbat
  · simp only [hlast, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc
    obtain ⟨d, pc⟩ := st
    simp only at hpc hfr hbat hlow hm1
    subst hpc
    have e : ∀ r, (after b8 batS).reg r = some (.reg r) → reg d r = reg m r := fun r hr ↦
      rv hm1 (by rw [← after_eq run_b8]; exact hr)
    refine cont d ⟨hfr, hlow, by omega, by have := h.hjq; omega, hbat, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e .r15 rfl]; exact h.r15
    · rw [e .rbx rfl]; exact h.rbx
    · rw [rv hm1 (v := .load 0 120 8) rfl]; exact hl120
    · rw [rv hm1 (v := .load 0 24 8) rfl]
      exact NativeRustcVmX64.Arrays.load_word h.mm.low.w24
    · rw [rv hm1 (v := .load 0 40 8) rfl]
      exact NativeRustcVmX64.Arrays.load_word h.mm.low.w40
    · rw [rv hm1 (v := .ptr 1 0) rfl]
      show bOf m0 + BitVec.ofInt 64 0 = _
      exact BitVec.add_zero _

end

end NativeRustcVmX64.Whir.EachRowOfNextLevel
