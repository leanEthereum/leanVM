module

public import NativeRustcVmX64.Whir.EachRowOfNextLevel.IterG
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EachRowOfNextLevel.Names

/-!
# `each_row` with `next_level`'s closure: query weight `j` (x86-64)

At `b23` (`AtB23`): `j` below the query weights' count, `b6` reads weight `j` and `b7` calls
`EW::mul`; else `b24` takes `0` and `b7` calls it (`iter_h`).
-/

namespace NativeRustcVmX64.Whir.EachRowOfNextLevel

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmX64.Vm.EachRowOfNextLevel
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off OptEWAt)

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData} {j : Nat}

/-- `rbx << 4`. -/
theorem eval_shl4 (x : BitVec 64) {n : Nat} (hx : x = BitVec.ofNat 64 n) (hn : 16 * n < 2 ^ 64) :
    BinOp.apply .shl .W64 x (BitVec.ofNat 64 4) = BitVec.ofNat 64 (16 * n) := by
  subst hx
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [show shiftCount .W64 (BitVec.ofNat 64 4) = 4 from rfl]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have : n < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this, show Width.W64.bits = 64 from rfl]
  omega

variable [Host] {k : Nat}

/-- **Row `j`'s term**: from `b23` to `b8_step`. -/
theorem iter_h (hp : Placed code k) (hmul : Spec (label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (c : Ctx rows op m0) {m : MachineData} (h : AtB23 rows m0 j m)
    (cont : ∀ m', Inv rows m0 (j + 1) m' →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m', Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b9Offset)⟩) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b23Offset)⟩ := by
  have hl := lay c
  have hsp := hl.sp
  have htop := hl.ok.2.1
  have hP := h.mm.bat
  have hPc := NativeRustcVm.ewAt_iff.mp hP
  have hjr := h.hj
  have hjq := h.hjq
  have hqs : (qwOf m0).size = (nextEnv m0 5).toNat := qw_size
  -- the folded row and the scaled value, as the code adds them
  have hx : ∀ (env : Env) (mc : MachineData), env.mem0 = m.dmem → env.base 0 = fb m0 →
      env.regs .rbp = reg m .rbp → env.regs .rax = reg m .rax →
      reg mc .rdx = (Sym.bin .xor .W64 (.reg .rbp) (.load 0 112 8)).eval env →
      reg mc .rcx = (Sym.bin .xor .W64 (.reg .rax) (.load 0 104 8)).eval env →
      (⟨UInt64.ofBitVec (reg mc .rdx), UInt64.ofBitVec (reg mc .rcx)⟩ : EW) =
        foldJ rows m0 j hjr hjq + scaleJ m0 ((qsOf m0)[j]'hjq) := by
    intro env mc hmem hb hbp hax hdx hcx
    rw [← xor_add, hdx, hcx]
    have l112 : env.load 0 112 8 = (foldJ rows m0 j hjr hjq).c0.toBitVec :=
      NativeRustcVmX64.Arrays.load_word (by rw [hmem, hb]; exact h.w112)
    have l104 : env.load 0 104 8 = (foldJ rows m0 j hjr hjq).c1.toBitVec :=
      NativeRustcVmX64.Arrays.load_word (by rw [hmem, hb]; exact h.w104)
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, l112, l104, hbp, hax]
    rw [h.rbp, h.rax]
  -- `b23`
  let envB := EachRow.envE m0 m 1984 0 [(bOf m0, 16)] (fun _ ↦ 0)
    (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b7Offset + b7.length)).toBitVec
  have hwfB : envB.WF := env1 c h.fr c.bin _
  have hmB : Match envB batS m :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨h.fr.match_rsp, by
        show reg m .r14 = bOf m0 + BitVec.ofInt 64 0
        rw [h.r14]
        exact (BitVec.add_zero _).symm, trivial⟩ trivial trivial trivial
  have hk23 : b23.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b23Offset) := b23_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hl16 : envB.load 0 16 8 = nextEnv m0 5 := NativeRustcVmX64.Arrays.load_word h.mm.low.w16
  have hP0 : envB.load 1 0 8 = (parOf rows m0 j).c0.toBitVec :=
    NativeRustcVmX64.Arrays.load_word (by
      show WordAt m.dmem (bOf m0 + BitVec.ofNat 64 0) _
      rw [NativeRustcVm.addr_add_zero]; exact hPc.1)
  have hP8 : envB.load 1 8 8 = (parOf rows m0 j).c1.toBitVec :=
    NativeRustcVmX64.Arrays.load_word hPc.2
  refine exec_then hk23 run_b23 hwfB (fun _ h ↦ by cases h) hmB fun st1 hm1 hpc1 ↦ ?_
  have hd1 : st1.data.dmem = m.dmem := hm1.dmem_eq hwfB rfl
  have e1 : ∀ r, (after b23 batS).reg r = some (.reg r) → reg st1.data r = reg m r := fun r hr ↦
    rv hm1 (by rw [← after_eq run_b23]; exact hr)
  have hfr1 : FR m0 8 st1.data := h.fr.ofBlock hwfB hm1 rfl rfl
  simp only [PcOk] at hpc1
  have hc : (SBool.cmp .ult .W64 (.reg .rbx) (.load 0 16 8)).eval envB =
      decide (j < (qwOf m0).size) := by
    simp only [SBool.eval, CmpOp.apply, low_W64, Sym.eval]
    rw [hl16, hqs]
    show (reg m .rbx).ult _ = _
    have : LeanVM.Protocol.Compile.wireMaxQueries = 256 := rfl
    rw [h.rbx, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := c.rowsAt.2.1; omega)]
  rw [hc] at hpc1
  by_cases hlt : j < (qwOf m0).size
  · -- `b6`, `b7`: query weight `j`
    simp only [hlt, decide_true, ↓reduceIte] at hpc1
    rw [show Labels.label NativeRustcVmX64.Vm.EachRowOfNextLevel.label_3 = Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b6Offset) from hp.label NativeRustcVmX64.Vm.EachRowOfNextLevel.label_3_at]
      at hpc1
    let qa := nextEnv m0 4 + BitVec.ofNat 64 (16 * j)
    have hqin : WhirIn m0 qa 16 eachRowNextStack :=
      NativeRustcVmX64.Whir.WhirIn.sub c.qwin (by rw [← hqs]; omega)
    have hqo : ∀ i < 16, ¬InRange (bOf m0) 16 (qa + BitVec.ofNat 64 i) := fun i hi ↦ by
      rw [addr_add]
      exact notB_in c c.qwin c.bqw _ (by rw [← hqs]; omega)
    let env6 := EachRow.envE m0 st1.data 1984 0 [(qa, 16), (bOf m0, 16)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b7Offset + b7.length)).toBitVec
    have hwf6 : env6.WF := by
      refine EachRow.envE_wf hl (Nat.zero_le _) hfr1.kept ?_
        (NativeRustcVmX64.Transcript.pairwise3 (hl.apart0 hqin.2) (hl.apart0 c.bin.2) ?_)
      · intro x hx'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
        rcases hx' with rfl | rfl
        · exact ⟨fun i hi ↦ hfr1.kept _ (hqin.1.1 i hi), hqin.1.2⟩
        · exact ⟨fun i hi ↦ hfr1.kept _ (c.bin.1.1 i hi), c.bin.1.2⟩
      · have hb := c.bqw
        have hq := hqin.1.2
        have hbn := c.qwin.1.2
        unfold Apart at hb ⊢
        unfold NoWrap at hq hbn
        show qa.toNat + 16 ≤ (bOf m0).toNat ∨ (bOf m0).toNat + 16 ≤ qa.toNat
        rw [toNat_add_ofNat _ _ (by rw [← hqs] at hbn; omega)]
        rw [← hqs] at hb hbn
        omega
    have hm6 : Match env6 qwS st1.data :=
      match_ofMachine ⟨rfl, rfl, rfl, trivial⟩
        ⟨hfr1.match_rsp, by
          show reg st1.data .r14 = bOf m0 + BitVec.ofInt 64 0
          rw [rv hm1 (v := .ptr 1 0) rfl]
          rfl, trivial⟩ trivial trivial
        ⟨by
          show (Sym.bin .add .W64 (.load 0 8 8) (.bin .shl .W64 (.reg .rbx) (.lit 4))).eval env6 =
            qa + BitVec.ofInt 64 0
          have w8 : WordAt env6.mem0 (env6.base 0 + BitVec.ofNat 64 8)
              (UInt64.ofBitVec (nextEnv m0 4)) := by
            show WordAt st1.data.dmem _ _
            rw [hd1]
            exact h.mm.low.w8
          have l8 : env6.load 0 8 8 = nextEnv m0 4 := NativeRustcVmX64.Arrays.load_word w8
          rw [NativeRustcVmX64.Arrays.eval_add]
          show env6.load 0 8 8 + BinOp.apply .shl .W64 (env6.regs .rbx) (BitVec.ofNat 64 4) = _
          have : LeanVM.Protocol.Compile.wireMaxQueries = 256 := rfl
          rw [l8, eval_shl4 (env6.regs .rbx) ((e1 .rbx rfl).trans h.rbx)
            (by have := c.rowsAt.2.1; omega)]
          exact (BitVec.add_zero _).symm, trivial⟩
    have hk6 : b6.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b6Offset) := b6_in_code.trans hp.1 (List.cons_ne_nil _ _)
    have hk7 : b7.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b7Offset) := b7_in_code.trans hp.1 (List.cons_ne_nil _ _)
    refine exec_at hk6 run_b6 hwf6 (fun _ h ↦ by cases h) hpc1 hm6 fun st2 hm2 hpc2 ↦ ?_
    refine exec_at hk7 (exec_after run_b6 run_b7) hwf6 (fun _ _ ↦ rfl) hpc2 hm2
      fun st3 hm3 hpc3 ↦ ?_
    rw [← after_eq (exec_after run_b6 run_b7)] at hm3
    have hs3 : SameOutside st1.data.dmem st3.data.dmem
        (EachRow.Hit m0 1984 eachRowNextStack 1432 1432) :=
      EachRow.hit_of_block hl le_rfl (by decide) hm3 hwf6
        (by rw [after_eq (exec_after run_b6 run_b7)]; decide)
    rw [after_eq (exec_after run_b6 run_b7)] at hm3
    have hfr3 : FR m0 0 st3.data :=
      hfr1.step hl le_rfl (by decide) ((rv hm3 (v := .ptr 0 0) rfl).trans (EachRow.eval_ptr0 0))
        (hm3.kept hwf6) hs3 (by decide)
    have hqv : ∀ o, o = 0 ∨ o = 8 → env6.load 1 o 8 =
        (NativeRustcVm.wordOf m0.dmem (qa + BitVec.ofNat 64 o)).toBitVec := fun o ho ↦ by
      rw [NativeRustcVmX64.Arrays.load8_eq, show env6.base 1 = qa from rfl,
        show env6.mem0 = st1.data.dmem from rfl, hd1,
        NativeRustcVm.wordOf_congr (d := m0.dmem) fun i hi ↦ by
          rw [addr_add]; exact h.fr.input_same hl hqin hqo _ (by omega)]
    refine mul_then hp hmul c hpc3.1 hpc3.2 hfr3 hjr hjq
      (h.mm.keep c (lo := 1432) (hi := 1432) le_rfl (by decide) (by decide) (by decide)
        (by rw [← hd1]; exact hs3))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ cont
    · rw [rv hm3 (v := .load 1 0 8) rfl, rv hm3 (v := .load 1 8 8) rfl, qw_getD hlt]
      show (⟨UInt64.ofBitVec (env6.load 1 0 8), UInt64.ofBitVec (env6.load 1 8 8)⟩ : EW) = _
      rw [hqv 0 (.inl rfl), hqv 8 (.inr rfl), NativeRustcVm.addr_add_zero]
      rfl
    · exact hx env6 st3.data hd1 rfl ((e1 .rbp rfl)) ((e1 .rax rfl)) (rv hm3 rfl) (rv hm3 rfl)
    · rw [rv hm3 (v := .load 2 0 8) rfl]
      exact NativeRustcVmX64.Arrays.load_word (by
        show WordAt st1.data.dmem (bOf m0 + BitVec.ofNat 64 0) _
        rw [NativeRustcVm.addr_add_zero, hd1]; exact hPc.1)
    · rw [rv hm3 (v := .load 2 8 8) rfl]
      exact NativeRustcVmX64.Arrays.load_word (by
        show WordAt st1.data.dmem (bOf m0 + BitVec.ofNat 64 8) _
        rw [hd1]; exact hPc.2)
    · rw [rv hm3 (v := .bin .add .W64 (.reg .rbx) (.lit 1)) rfl]
      show reg st1.data .rbx + BitVec.ofNat 64 1 = _
      rw [e1 .rbx rfl, h.rbx, ← BitVec.ofNat_add]
    · rw [rv hm3 (v := .bin .add .W64 (.lit 8) (.reg .r15)) rfl]
      show BitVec.ofNat 64 8 + reg st1.data .r15 = _
      rw [e1 .r15 rfl, h.r15, BitVec.add_comm, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2
    · rw [rv hm3 (v := .ptr 2 0) rfl]
      exact BitVec.add_zero _
  · -- `b24`, `b7`: the weight `0`
    simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    have hk24 : b24.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b24Offset) := b24_in_code.trans hp.1 (List.cons_ne_nil _ _)
    have hk7 : b7.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b7Offset) := b7_in_code.trans hp.1 (List.cons_ne_nil _ _)
    refine exec_at hk24 (exec_after run_b23 run_b24) hwfB (fun _ h ↦ by cases h) hpc1 hm1
      fun st2 hm2 hpc2 ↦ ?_
    have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b7Offset) := by
      simp only [PcOk] at hpc2
      rw [hpc2]
      exact hp.label NativeRustcVmX64.Vm.EachRowOfNextLevel.label_4_at
    refine exec_at hk7 (exec_after (exec_after run_b23 run_b24) run_b7z) hwfB (fun _ _ ↦ rfl)
      hpc2' hm2 fun st3 hm3 hpc3 ↦ ?_
    rw [← after_eq (exec_after (exec_after run_b23 run_b24) run_b7z)] at hm3
    have hs3 : SameOutside m.dmem st3.data.dmem
        (EachRow.Hit m0 1984 eachRowNextStack 1432 1432) :=
      EachRow.hit_of_block hl le_rfl (by decide) hm3 hwfB
        (by rw [after_eq (exec_after (exec_after run_b23 run_b24) run_b7z)]; decide)
    rw [after_eq (exec_after (exec_after run_b23 run_b24) run_b7z)] at hm3
    have hfr3 : FR m0 0 st3.data :=
      h.fr.step hl le_rfl (by decide) ((rv hm3 (v := .ptr 0 0) rfl).trans (EachRow.eval_ptr0 0))
        (hm3.kept hwfB) hs3 (by decide)
    refine mul_then hp hmul c hpc3.1 hpc3.2 hfr3 hjr hjq
      (h.mm.keep c le_rfl (by decide) (by decide) (by decide) hs3) ?_ ?_ ?_ ?_ ?_ ?_ ?_ cont
    · rw [rv hm3 (v := .lit 0) rfl, rv hm3 (v := .lit 0) rfl, qw_getD_none (by omega)]
      rfl
    · exact hx envB st3.data rfl rfl rfl rfl (rv hm3 rfl) (rv hm3 rfl)
    · rw [rv hm3 (v := .load 1 0 8) rfl]; exact hP0
    · rw [rv hm3 (v := .load 1 8 8) rfl]; exact hP8
    · rw [rv hm3 (v := .bin .add .W64 (.reg .rbx) (.lit 1)) rfl]
      show reg m .rbx + BitVec.ofNat 64 1 = _
      rw [h.rbx, ← BitVec.ofNat_add]
    · rw [rv hm3 (v := .bin .add .W64 (.lit 8) (.reg .r15)) rfl]
      show BitVec.ofNat 64 8 + reg m .r15 = _
      rw [h.r15, BitVec.add_comm, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2
    · rw [rv hm3 (v := .ptr 1 0) rfl]
      exact BitVec.add_zero _

end

end NativeRustcVmX64.Whir.EachRowOfNextLevel
