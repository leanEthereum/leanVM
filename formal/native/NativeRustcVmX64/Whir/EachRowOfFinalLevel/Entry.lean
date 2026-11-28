module

public import NativeRustcVmX64.Whir.EachRowOfFinalLevel.Basic
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.SubspaceTable.Names

/-!
# `each_row` with `final_level`'s closure: up to `b3` (x86-64)

`b0` pushes, spills the rounds and the index, keeps the queries, their count and the `Rows` in
RBP, RBX, R14 and calls `subspace_table(μ)` into the frame at 104; `b1` checks its `Some`; `b2`
calls `memcpy` to copy the table's pairs to 1392. At `b3` (`AtB3`): the pairs at 1392, their
count in R12, the spills, the arguments in callee-saved registers.
-/

namespace NativeRustcVmX64.Whir.EachRowOfFinalLevel

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmX64.Vm.EachRowOfFinalLevel
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off)

@[expose] public section

/-- **At `b3`.** -/
structure AtB3 (m0 m : MachineData) : Prop where
  fr : FR m0 8 m
  w32 : WordAt m.dmem (fb m0 + BitVec.ofNat 64 32) (UInt64.ofBitVec (reg m0 .r9))
  w40 : WordAt m.dmem (fb m0 + BitVec.ofNat 64 40) (UInt64.ofBitVec (reg m0 .rdi))
  copy : PairsAt m.dmem (fb m0 + BitVec.ofNat 64 1392) (tableOf m0).toList
  tlen : (tableOf m0).size ≤ 31
  r12 : reg m .r12 = BitVec.ofNat 64 (tableOf m0).size
  r15 : reg m .r15 = fb m0 + BitVec.ofNat 64 1392
  rbp : reg m .rbp = reg m0 .rsi
  rbx : reg m .rbx = reg m0 .rdx
  r14 : reg m .r14 = reg m0 .rcx

end

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData}

theorem rv [Labels] {env : Env} {S : SState} {m : MachineData} {r : Reg64} {v : Sym}
    (hm : Match env S m) (h : S.reg r = some v) : reg m r = v.eval env :=
  hm.regs r v h

variable [Host] {k : Nat}

/-- **From the entry to `b3`.** -/
theorem entry_a (hp : Placed code k)
    (htab : Spec (label NativeRustcVmX64.Vm.SubspaceTable.entryLabel) SubspaceTablePre SubspaceTablePost)
    (hmemcpy : Spec (label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hpre : EachRowFinalPre rows op m0) {R : MachineState → Prop}
    (cont : ∀ m, AtB3 m0 m → Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b3Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b0Offset)⟩ := by
  have hl := lay hpre
  have hmu : (reg m0 .r8).toNat ≤ stackCap := hpre.1.2.2.2.2.2.2.1
  let env0 := EachRow.envE m0 m0 1936 24 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b0Offset + b0.length)).toBitVec
  have hwf0 : env0.WF := EachRow.envE_wf hl le_rfl (fun _ h ↦ h) (fun _ h ↦ by cases h)
    (List.pairwise_singleton _ _)
  have hm0 : Match env0 entryS m0 :=
    match_ofMachine ⟨rfl, trivial⟩
      ⟨by
        show rspOf m0 = stackBelow m0 1936 + BitVec.ofInt 64 1936
        rw [show (1936 : Int) = ((1936 + 0 : Nat) : Int) from rfl,
          NativeRustcVmX64.Field.frame_rsp]
        simp, trivial⟩ trivial trivial trivial
  have hk0 : b0.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b0Offset) := b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk0 run_b0 hwf0 (fun _ _ ↦ rfl) hm0 fun st1 hm1 hpc1 ↦ ?_
  have hfr1 : FR m0 0 st1.data :=
    EachRow.Fr.ofPrologue hl le_rfl hm1 rfl (by decide) (by decide)
  have e1rdi : reg st1.data .rdi = fb m0 + BitVec.ofNat 64 104 :=
    (rv hm1 (v := .ptr 0 104) rfl).trans (EachRow.eval_ptr0 104)
  have e1rsi : reg st1.data .rsi = reg m0 .r8 := rv hm1 (v := .reg .r8) rfl
  have w32 : WordAt st1.data.dmem (fb m0 + BitVec.ofNat 64 32) (UInt64.ofBitVec (reg m0 .r9)) :=
    NativeRustcVmX64.Transcript.wordAt_write hm1 (r := 0) rfl (by decide) (v := .reg .r9)
      (by decide)
  have w40 : WordAt st1.data.dmem (fb m0 + BitVec.ofNat 64 40) (UInt64.ofBitVec (reg m0 .rdi)) :=
    NativeRustcVmX64.Transcript.wordAt_write hm1 (r := 0) rfl (by decide) (v := .reg .rdi)
      (by decide)
  -- `subspace_table(μ)`
  have hP1 : SubspaceTablePre st1.data := by
    refine ⟨hfr1.stackOk hl (by decide), ?_, ?_⟩
    · rw [e1rdi]
      exact hfr1.whirIn_frame hl (by decide) (by decide) (by decide)
    · apply hfr1.got_callee hl hpre.2.2.2 (got_nw hpre) (by intro q h; cases h) (by decide)
      intro a ha
      simp only [List.mem_singleton] at ha
      subst a
      have hsp : 3088 ≤ (rspOf m0).toNat := hl.sp
      have hb : (stackBelow m0 eachRowFinalStack).toNat = (rspOf m0).toNat - 3088 := by
        rw [hl.baseN, stack_eq]
      refine ⟨(stackBelow m0 eachRowFinalStack, eachRowFinalStack + 8), by simp, ?_, ?_⟩
      · change (stackBelow m0 eachRowFinalStack).toNat ≤ (reg st1.data .rdi).toNat
        rw [e1rdi, hl.addr (o := 104) (by decide), hb]
        omega
      · change (reg st1.data .rdi).toNat + 512 ≤ (stackBelow m0 eachRowFinalStack).toNat + 3096
        rw [e1rdi, hl.addr (o := 104) (by decide), hb]
        omega
  refine call_then hpc1 htab hP1 fun st2 hpc2 hrsp2 hq ↦ ?_
  simp only [SubspaceTablePost] at hq
  obtain ⟨hval, hch, hsv⟩ := hq
  rw [e1rsi, e1rdi] at hval
  simp only [hmu, ↓reduceIte] at hval
  obtain ⟨htag, htabb⟩ := hval
  rw [e1rdi] at hch
  have hs2 : SameOutside st1.data.dmem st2.data.dmem (EachRow.Hit m0 1936 eachRowFinalStack 104 616) :=
    EachRow.hit_of_call hl (by decide) (by decide) hfr1.rsp0 (N' := subspaceTableStack)
      (by decide) le_rfl (by decide) hch
  have hfr2 : FR m0 8 st2.data :=
    EachRow.Fr.call hl (by decide) (by decide) hfr1 hrsp2 hsv hs2 (by decide)
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2 hfr2 hs2 hsv htag htabb
  subst hpc2
  -- `b1`, `b2`
  obtain ⟨hwf, hm⟩ := hfr2.got_env hl hpre.2.2.2 (got_nw hpre) (by intro q h; cases h)
    (by simp) (by simp : "memcpy" ∈ ["memcpy", "memset"])
    (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b2Offset + b2.length)).toBitVec
  have hk1 : b1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b1Offset) := b1_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hk2 : b2.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b2Offset) := b2_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hl104 : (EachRow.envE m0 d2 1936 24 [(gotAddr "memcpy", 8)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b2Offset + b2.length)).toBitVec).load 0 104 4 = BitVec.ofNat 64 (1 : UInt64).toNat :=
    NativeRustcVmX64.Transcript.load4_of_tag (.inr rfl) htag
  have hlen : (tableOf m0).toList.length = (tableOf m0).size := Array.length_toList
  have hl112 : (EachRow.envE m0 d2 1936 24 [(gotAddr "memcpy", 8)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b2Offset + b2.length)).toBitVec).load 0 112 8 =
        BitVec.ofNat 64 (tableOf m0).size := by
    have := htabb.2.1
    rw [hlen] at this
    rw [show off (fb m0 + BitVec.ofNat 64 104) 8 = fb m0 + BitVec.ofNat 64 112 from
      NativeRustcVm.addr_add_add _ _ _] at this
    exact NativeRustcVmX64.Arrays.load_word this
  rw [show (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b0Offset + b0.length) = k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b1Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.EachRowOfFinalLevel.b0_next]]
  refine exec_then hk1 run_b1 hwf (fun _ h ↦ by cases h) hm fun st3 hm3 hpc3 ↦ ?_
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b2Offset) := by
    simp only [PcOk] at hpc3
    split at hpc3
    · rename_i hc
      exact absurd hc (by simp only [SBool.eval, Sym.eval, CmpOp.apply, hl104]; decide)
    · exact hpc3
  refine exec_at hk2 (exec_after run_b1 run_b2) hwf (fun _ _ ↦ rfl) hpc3' hm3
    fun st4 hm4 hpc4 ↦ ?_
  have hs4 : SameOutside d2.dmem st4.data.dmem (EachRow.Hit m0 1936 eachRowFinalStack 1384 1384) :=
    EachRow.hit_of_block hl le_rfl (by decide) hm4 hwf (by decide)
  have hfr4 : FR m0 0 st4.data :=
    hfr2.step hl le_rfl (by decide)
      ((rv hm4 (v := .ptr 0 0) rfl).trans (EachRow.eval_ptr0 0)) (hm4.kept hwf) hs4 (by decide)
  have e4rdi : reg st4.data .rdi = fb m0 + BitVec.ofNat 64 1392 :=
    (rv hm4 (v := .ptr 0 1392) rfl).trans (EachRow.eval_ptr0 1392)
  have e4rsi : reg st4.data .rsi = fb m0 + BitVec.ofNat 64 120 :=
    (rv hm4 (v := .ptr 0 120) rfl).trans (EachRow.eval_ptr0 120)
  have e4rdx : (reg st4.data .rdx).toNat = 496 := by rw [rv hm4 (v := .lit 496) rfl]; rfl
  -- `memcpy`
  have hdst := hfr4.whirIn_frame hl (o := 1392) (c := 496) (N' := 0) (by decide) (by decide)
    (by decide)
  have hsrc := hfr4.whirIn_frame hl (o := 120) (c := 496) (N' := 0) (by decide) (by decide)
    (by decide)
  have a1392 := hl.addr (o := 1392) (by decide)
  have a120 := hl.addr (o := 120) (by decide)
  have a0 := hl.addr (o := 0) (by decide)
  have hP4 : MemcpyPre st4.data := by
    unfold MemcpyPre
    simp only
    rw [e4rdi, e4rsi, e4rdx]
    refine ⟨hfr4.stackOk hl (by decide), hdst.1.1, hsrc.1.1, hdst.1.2, hsrc.1.2, ?_, ?_⟩
    · unfold Apart
      rw [a1392, a120]
      omega
    · unfold Apart
      rw [hfr4.rsp, a1392, a0]
      omega
  refine call_then hpc4 hmemcpy hP4 fun st5 hpc5 hrsp5 hq5 ↦ ?_
  simp only [MemcpyPost] at hq5
  obtain ⟨-, hcopy, hsame5, hsv5⟩ := hq5
  rw [e4rdi, e4rdx] at hsame5
  rw [e4rdi, e4rsi, e4rdx] at hcopy
  have hs5 : SameOutside st4.data.dmem st5.data.dmem
      (EachRow.Hit m0 1936 eachRowFinalStack 1392 1888) :=
    EachRow.hit_of_call hl (by decide) (by decide) hfr4.rsp0 (N' := 0) (by decide) le_rfl
      (by decide) fun q hq ↦ hsame5 q fun h ↦ hq (.inl ⟨_, List.mem_singleton_self _, h⟩)
  have hfr5 : FR m0 8 st5.data :=
    EachRow.Fr.call hl (by decide) (by decide) hfr4 hrsp5 hsv5 hs5 (by decide)
  obtain ⟨d5, pc5⟩ := st5
  simp only at hpc5 hfr5 hs5 hsv5 hcopy
  subst hpc5
  rw [show k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b2Offset + b2.length = k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b3Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.EachRowOfFinalLevel.b2_next]]
  -- the table's pairs, kept to the copy
  have hsrcP : PairsAt st4.data.dmem (fb m0 + BitVec.ofNat 64 120) (tableOf m0).toList := by
    have := htabb.2.2
    rw [show off (off (fb m0 + BitVec.ofNat 64 104) 8) 8 = fb m0 + BitVec.ofNat 64 120 by
      rw [NativeRustcVm.Transcript.off_off]; exact NativeRustcVm.addr_add_add _ _ _] at this
    unfold PairsAt at this ⊢
    refine EachRow.keep_frame hl le_rfl (by decide) hs4 (by decide) (.inl ?_) this
    rw [NativeRustcVm.length_wordsBytes, EachRow.length_pairWords, hlen]
    have := htabb.1
    rw [hlen] at this
    have : rootCap = 31 := rfl
    omega
  have k1 : ∀ r, calleeSaved r = true → (after b2 (after b1 (EachRow.gotFrameS 1936 24 "memcpy"))).reg r = some (.reg r) →
      reg d5 r = reg st1.data r := fun r hc hr ↦ by
    rw [sv hsv5 r hc, rv hm4 (by rw [← after_eq (exec_after run_b1 run_b2)]; exact hr)]
    exact sv hsv r hc
  refine cont d5 ⟨hfr5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact keepW hl (by decide) (by decide) hs5 (by decide) (by decide)
      (keepW hl le_rfl (by decide) hs4 (by decide) (by decide)
        (keepW hl (by decide) (by decide) hs2 (by decide) (by decide) w32))
  · exact keepW hl (by decide) (by decide) hs5 (by decide) (by decide)
      (keepW hl le_rfl (by decide) hs4 (by decide) (by decide)
        (keepW hl (by decide) (by decide) hs2 (by decide) (by decide) w40))
  · unfold PairsAt at hsrcP ⊢
    refine EachRow.bytesAt_copy hcopy hsrcP ?_
    rw [NativeRustcVm.length_wordsBytes, EachRow.length_pairWords, hlen]
    have := htabb.1
    rw [hlen] at this
    have : rootCap = 31 := rfl
    omega
  · have := htabb.1
    rw [hlen] at this
    exact this
  · rw [sv hsv5 .r12 rfl, rv hm4 (v := .load 0 112 8) rfl]
    exact hl112
  · rw [sv hsv5 .r15 rfl, rv hm4 (v := .ptr 0 1392) rfl]
    exact EachRow.eval_ptr0 1392
  · rw [k1 .rbp rfl rfl]; exact rv hm1 (v := .reg .rsi) rfl
  · rw [k1 .rbx rfl rfl]; exact rv hm1 (v := .reg .rdx) rfl
  · rw [k1 .r14 rfl rfl]; exact rv hm1 (v := .reg .rcx) rfl

end

end NativeRustcVmX64.Whir.EachRowOfFinalLevel
