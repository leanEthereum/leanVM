module

public import NativeRustcVmX64.Whir.EachRowOfNextLevel.IterD
public import NativeRustcVmX64.Code.Vm.Kmul.Names

/-!
# `each_row` with `next_level`'s closure: the scaled `novel_eval` (x86-64)

At `b21` (`AtB21`): `b21` spills the folded row's high limb at 104 and calls `kmul` on `What` `μ`
and `novel_eval`'s low limb; `b22` keeps it in RBP and calls `kmul` on the high limb: at `b23`
(`AtB23`, `iter_e`) the scaled value in RBP, RAX.
-/

namespace NativeRustcVmX64.Whir.EachRowOfNextLevel

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmX64.Vm.EachRowOfNextLevel
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off OptEWAt)

@[expose] public section

/-- Row `j`'s scaled `novel_eval`. -/
abbrev scaleJ (m0 : MachineData) (q : UInt64) : EW :=
  EW.scale ((whatJ m0 q).getD (reg m0 .r8).toNat 0) (novelEval (highOf m0) (whatJ m0 q))

/-- **At `b23`**, in iteration `j`: the folded row at 112, 104, the scaled value in RBP, RAX. -/
structure AtB23 (rows : Array (Array UInt64)) (m0 : MachineData) (j : Nat) (m : MachineData) :
    Prop where
  fr : FR m0 8 m
  hj : j < rows.size
  hjq : j < (qsOf m0).size
  mm : MidN rows m0 j m.dmem
  w112 : WordAt m.dmem (fb m0 + BitVec.ofNat 64 112) (foldJ rows m0 j hj hjq).c0
  w104 : WordAt m.dmem (fb m0 + BitVec.ofNat 64 104) (foldJ rows m0 j hj hjq).c1
  rbp : reg m .rbp = (scaleJ m0 ((qsOf m0)[j]'hjq)).c0.toBitVec
  rax : reg m .rax = (scaleJ m0 ((qsOf m0)[j]'hjq)).c1.toBitVec
  rbx : reg m .rbx = BitVec.ofNat 64 j
  r15 : reg m .r15 = reg m0 .rsi + BitVec.ofNat 64 (8 * j)
  r14 : reg m .r14 = bOf m0

end

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData} {j : Nat}

variable [Host] {k : Nat}

/-- **The scaled `novel_eval`**: from `b21` to `b23`. -/
theorem iter_e (hp : Placed code k)
    (hkmul : Spec (label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost)
    (c : Ctx rows op m0) {m : MachineData} (h : AtB21 rows m0 j m)
    (cont : ∀ m', AtB23 rows m0 j m' →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m', Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b23Offset)⟩) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b21Offset)⟩ := by
  have hl := lay c
  obtain ⟨W, hW⟩ : ∃ W, W = whatJ m0 ((qsOf m0)[j]'h.hjq) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = novelEval (highOf m0) W := ⟨_, rfl⟩
  have hnov : OptEWAt m.dmem (fb m0 + BitVec.ofNat 64 128) (some r) := by
    rw [hr, hW]; exact h.nov
  have hrc := NativeRustcVm.ewAt_iff.mp hnov.2
  -- `b21`
  obtain ⟨hwf, hm⟩ := frame_env c h.fr (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b21Offset + b21.length)).toBitVec
  have hk21 : b21.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b21Offset) := b21_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hl136 : (EachRow.envE m0 m 1984 16 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b21Offset + b21.length)).toBitVec).load 0 136 8 = r.c0.toBitVec := by
    have := hrc.1
    rw [show off (fb m0 + BitVec.ofNat 64 128) 8 = fb m0 + BitVec.ofNat 64 136 from
      addr_add _ _ _] at this
    exact NativeRustcVmX64.Arrays.load_word this
  have hl144 : (EachRow.envE m0 m 1984 16 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b21Offset + b21.length)).toBitVec).load 0 144 8 = r.c1.toBitVec := by
    have := hrc.2
    rw [show off (fb m0 + BitVec.ofNat 64 128) 8 + BitVec.ofNat 64 8 = fb m0 + BitVec.ofNat 64 144
      by unfold off; rw [addr_add, addr_add]] at this
    exact NativeRustcVmX64.Arrays.load_word this
  refine exec_then hk21 run_b21 hwf (fun _ _ ↦ rfl) hm fun st1 hm1 hpc1 ↦ ?_
  have hs1 : SameOutside m.dmem st1.data.dmem (EachRow.Hit m0 1984 eachRowNextStack 104 112) :=
    EachRow.hit_of_block hl (by decide) (by decide) hm1 hwf (by decide)
  have hfr1 : FR m0 0 st1.data :=
    h.fr.step hl (by decide) (by decide) ((rv hm1 (v := .ptr 0 0) rfl).trans (EachRow.eval_ptr0 0))
      (hm1.kept hwf) hs1 (by decide)
  have w104 : WordAt st1.data.dmem (fb m0 + BitVec.ofNat 64 104)
      (foldJ rows m0 j h.hj h.hjq).c1 := by
    have := NativeRustcVmX64.Transcript.wordAt_write hm1 (r := 0) (o := 104) rfl (by decide)
      (v := .reg .r12) (by decide)
    rw [show (Sym.reg .r12).eval (EachRow.envE m0 m 1984 16 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b21Offset + b21.length)).toBitVec) = _ from h.r12,
      UInt64.ofBitVec_toBitVec] at this
    exact this
  have e1rdi : reg st1.data .rdi = (W.getD (reg m0 .r8).toNat 0).toBitVec := by
    rw [rv hm1 (v := .reg .r13) rfl, hW]; exact h.r13
  have e1rsi : reg st1.data .rsi = r.c0.toBitVec := (rv hm1 (v := .load 0 136 8) rfl).trans hl136
  have e1r12 : reg st1.data .r12 = r.c1.toBitVec := (rv hm1 (v := .load 0 144 8) rfl).trans hl144
  have e1 : ∀ r, calleeSaved r = true → r ≠ .r12 → reg st1.data r = reg m r := fun r hc hr ↦
    rv hm1 (v := .reg r) (by revert hc hr; cases r <;> decide)
  refine call_then hpc1 hkmul (hfr1.stackOk hl (by decide)) fun st2 hpc2 hrsp2 hq2 ↦ ?_
  obtain ⟨hval2, hch2, hsv2⟩ := hq2
  have hs2 := EachRow.hit_of_stack hl (lo := 1432) (hi := 1432) le_rfl (by decide) hfr1.rsp0
    (N' := kmulStack) (by decide) hch2
  have hfr2 : FR m0 8 st2.data :=
    EachRow.Fr.call hl le_rfl (by decide) hfr1 hrsp2 hsv2 hs2 (by decide)
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2 hfr2 hs2 hsv2 hval2
  subst hpc2
  rw [show k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b21Offset + b21.length = k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b22Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.EachRowOfNextLevel.b21_next]]
  -- `b22`
  obtain ⟨hwf2, hm2⟩ := frame_env c hfr2 (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b22Offset + b22.length)).toBitVec
  have hk22 : b22.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b22Offset) := b22_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk22 run_b22 hwf2 (fun _ _ ↦ rfl) hm2 fun st3 hm3 hpc3 ↦ ?_
  have hs3 : SameOutside d2.dmem st3.data.dmem (EachRow.Hit m0 1984 eachRowNextStack 1432 1432) :=
    EachRow.hit_of_block hl le_rfl (by decide) hm3 hwf2 (by decide)
  have hfr3 : FR m0 0 st3.data :=
    hfr2.step hl le_rfl (by decide) ((rv hm3 (v := .ptr 0 0) rfl).trans (EachRow.eval_ptr0 0))
      (hm3.kept hwf2) hs3 (by decide)
  have k2 : ∀ r, calleeSaved r = true → reg d2 r = reg st1.data r := fun r hc ↦ sv hsv2 r hc
  have e3rdi : reg st3.data .rdi = (W.getD (reg m0 .r8).toNat 0).toBitVec := by
    rw [rv hm3 (v := .reg .r13) rfl]
    show reg d2 .r13 = _
    rw [k2 .r13 rfl, e1 .r13 rfl (by decide), hW]
    exact h.r13
  have e3rsi : reg st3.data .rsi = r.c1.toBitVec := by
    rw [rv hm3 (v := .reg .r12) rfl]
    show reg d2 .r12 = _
    rw [k2 .r12 rfl]
    exact e1r12
  have e3rbp : reg st3.data .rbp = (kmul (W.getD (reg m0 .r8).toNat 0) r.c0).toBitVec := by
    rw [rv hm3 (v := .reg .rax) rfl]
    show reg d2 .rax = _
    rw [hval2, e1rdi, e1rsi]
  have e3 : ∀ r, calleeSaved r = true → r ≠ .rbp → r ≠ .r12 → reg st3.data r = reg m r :=
    fun r hc h1 h2 ↦ by
      rw [rv hm3 (v := .reg r) (by revert hc h1; cases r <;> decide)]
      show reg d2 r = _
      rw [k2 r hc, e1 r hc h2]
  refine call_then hpc3 hkmul (hfr3.stackOk hl (by decide)) fun st4 hpc4 hrsp4 hq4 ↦ ?_
  obtain ⟨hval4, hch4, hsv4⟩ := hq4
  have hs4 := EachRow.hit_of_stack hl (lo := 1432) (hi := 1432) le_rfl (by decide) hfr3.rsp0
    (N' := kmulStack) (by decide) hch4
  have hfr4 : FR m0 8 st4.data :=
    EachRow.Fr.call hl le_rfl (by decide) hfr3 hrsp4 hsv4 hs4 (by decide)
  obtain ⟨d4, pc4⟩ := st4
  simp only at hpc4 hfr4 hs4 hsv4 hval4
  subst hpc4
  rw [show k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b22Offset + b22.length = k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b23Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.EachRowOfNextLevel.b22_next]]
  have hall : SameOutside m.dmem d4.dmem (EachRow.Hit m0 1984 eachRowNextStack 104 112) := by
    intro q hq
    have hq' : ¬EachRow.Hit m0 1984 eachRowNextStack 1432 1432 q := fun h' ↦ hq (by
      rw [hl.hit_iff (by decide) (by decide)] at h' ⊢
      omega)
    rw [hs4 q hq', hs3 q hq', hs2 q hq', hs1 q hq]
  have hsc : scaleJ m0 ((qsOf m0)[j]'h.hjq) =
      ⟨kmul (W.getD (reg m0 .r8).toNat 0) r.c0, kmul (W.getD (reg m0 .r8).toNat 0) r.c1⟩ := by
    rw [hr, hW]
    rfl
  refine cont d4 ⟨hfr4, h.hj, h.hjq, h.mm.keep c (by decide) (by decide) (by decide) (by decide)
    hall, keepW hl (by decide) (by decide) hall (by decide) (by decide) h.w112,
    keepW hl (by decide) (by decide) hs4 (by decide) (by decide)
      (keepW hl le_rfl (by decide) hs3 (by decide) (by decide)
        (keepW hl le_rfl (by decide) hs2 (by decide) (by decide) w104)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [sv hsv4 .rbp rfl, e3rbp, hsc]
  · rw [hval4, e3rdi, e3rsi, hsc]
  · rw [sv hsv4 .rbx rfl, e3 .rbx rfl (by decide) (by decide)]; exact h.rbx
  · rw [sv hsv4 .r15 rfl, e3 .r15 rfl (by decide) (by decide)]; exact h.r15
  · rw [sv hsv4 .r14 rfl, e3 .r14 rfl (by decide) (by decide)]; exact h.r14

end

end NativeRustcVmX64.Whir.EachRowOfNextLevel
