module

public import NativeRustcVmX64.Whir.EachRowOfNextLevel.Basic
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.SubspaceTable.Names

/-!
# `each_row` with `next_level`'s closure: up to `b3` (x86-64)

`b0` pushes, spills the rounds and the index, keeps the queries, their count and the `Rows` in
R15, RBX, R12 and calls `subspace_table(μ)` into the frame at 152; `b1` checks its `Some`; `b2`
calls `memcpy` to copy the table's pairs to 1440. At `b3` (`AtB3`): the pairs at 1440, their
count in R14, the spills, the arguments in callee-saved registers.
-/

namespace NativeRustcVmX64.Whir.EachRowOfNextLevel

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmX64.Vm.EachRowOfNextLevel
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off)

@[expose] public section

/-- **At `b3`.** -/
structure AtB3 (m0 m : MachineData) : Prop where
  fr : FR m0 8 m
  w88 : WordAt m.dmem (fb m0 + BitVec.ofNat 64 88) (UInt64.ofBitVec (reg m0 .r9))
  w96 : WordAt m.dmem (fb m0 + BitVec.ofNat 64 96) (UInt64.ofBitVec (reg m0 .rdi))
  copy : PairsAt m.dmem (fb m0 + BitVec.ofNat 64 1440) (tableOf m0).toList
  tlen : (tableOf m0).size ≤ 31
  r14 : reg m .r14 = BitVec.ofNat 64 (tableOf m0).size
  r13 : reg m .r13 = fb m0 + BitVec.ofNat 64 1440
  r15 : reg m .r15 = reg m0 .rsi
  rbx : reg m .rbx = reg m0 .rdx
  r12 : reg m .r12 = reg m0 .rcx
  bat : EWAt m.dmem (bOf m0) 0

end

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData}

/-- A frame word kept by a step changing memory in `Hit`. -/
theorem keepW {lo hi : Nat} (hl : EachRow.Lay m0 1984 16 eachRowNextStack) (hlh : lo ≤ hi)
    (hhi : hi ≤ 1984) {d d' : DataMem}
    (hs : SameOutside d d' (EachRow.Hit m0 1984 eachRowNextStack lo hi)) {o : Nat} {w : UInt64}
    (h8 : 8 ≤ o) (ho : o + 8 ≤ lo ∨ (hi ≤ o ∧ o + 8 ≤ 2008))
    (h : WordAt d (fb m0 + BitVec.ofNat 64 o) w) : WordAt d' (fb m0 + BitVec.ofNat 64 o) w :=
  EachRow.keep_frame hl hlh hhi hs h8 (by rw [NativeRustcVm.length_wordBytes]; omega) h

variable [Host] {k : Nat}

/-- **From the entry to `b3`.** -/
theorem entry_a (hp : Placed code k)
    (htab : Spec (label NativeRustcVmX64.Vm.SubspaceTable.entryLabel) SubspaceTablePre SubspaceTablePost)
    (hmemcpy : Spec (label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (c : Ctx rows op m0) {R : MachineState → Prop}
    (cont : ∀ m, AtB3 m0 m → Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b3Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b0Offset)⟩ := by
  have hl := lay c
  have hmu : (reg m0 .r8).toNat ≤ stackCap := c.mu
  let env0 := EachRow.envE m0 m0 1984 16 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b0Offset + b0.length)).toBitVec
  have hwf0 : env0.WF := EachRow.envE_wf hl le_rfl (fun _ h ↦ h) (fun _ h ↦ by cases h)
    (List.pairwise_singleton _ _)
  have hm0 : Match env0 entryS m0 :=
    match_ofMachine ⟨rfl, trivial⟩
      ⟨by
        show rspOf m0 = stackBelow m0 1984 + BitVec.ofInt 64 1984
        rw [show (1984 : Int) = ((1984 + 0 : Nat) : Int) from rfl,
          NativeRustcVmX64.Field.frame_rsp]
        simp, trivial⟩ trivial trivial trivial
  have hk0 : b0.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b0Offset) := b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk0 run_b0 hwf0 (fun _ _ ↦ rfl) hm0 fun st1 hm1 hpc1 ↦ ?_
  have hfr1 : FR m0 0 st1.data :=
    EachRow.Fr.ofPrologue hl le_rfl hm1 rfl (by decide) (by decide)
  have hs1 : SameOutside m0.dmem st1.data.dmem (EachRow.Hit m0 1984 eachRowNextStack 8 1984) :=
    EachRow.hit_of_block hl (by decide) (by decide) hm1 hwf0 (by decide)
  have e1rdi : reg st1.data .rdi = fb m0 + BitVec.ofNat 64 152 :=
    (rv hm1 (v := .ptr 0 152) rfl).trans (EachRow.eval_ptr0 152)
  have e1rsi : reg st1.data .rsi = reg m0 .r8 := rv hm1 (v := .reg .r8) rfl
  have w88 : WordAt st1.data.dmem (fb m0 + BitVec.ofNat 64 88) (UInt64.ofBitVec (reg m0 .r9)) :=
    NativeRustcVmX64.Transcript.wordAt_write hm1 (r := 0) (o := 88) rfl (by decide) (v := .reg .r9)
      (by decide)
  have w96 : WordAt st1.data.dmem (fb m0 + BitVec.ofNat 64 96) (UInt64.ofBitVec (reg m0 .rdi)) :=
    NativeRustcVmX64.Transcript.wordAt_write hm1 (r := 0) (o := 96) rfl (by decide) (v := .reg .rdi)
      (by decide)
  -- `subspace_table(μ)`
  have hP1 : SubspaceTablePre st1.data := by
    refine ⟨hfr1.stackOk hl (by decide), ?_, ?_⟩
    · rw [e1rdi]
      exact hfr1.whirIn_frame hl (by decide) (by decide) (by decide)
    · apply hfr1.got_callee hl c.got c.got_nw
        (fun q h => ⟨(bOf m0, 16), by simp, h⟩) (by decide)
      intro a ha
      simp only [List.mem_singleton] at ha
      subst a
      have hsp : 3136 ≤ (rspOf m0).toNat := hl.sp
      have hb : (stackBelow m0 eachRowNextStack).toNat = (rspOf m0).toNat - 3136 := by
        rw [hl.baseN, stack_eq]
      refine ⟨(stackBelow m0 eachRowNextStack, eachRowNextStack + 8), by simp, ?_, ?_⟩
      · change (stackBelow m0 eachRowNextStack).toNat ≤ (reg st1.data .rdi).toNat
        rw [e1rdi, hl.addr (o := 152) (by decide), hb]
        omega
      · change (reg st1.data .rdi).toNat + 512 ≤ (stackBelow m0 eachRowNextStack).toNat + 3144
        rw [e1rdi, hl.addr (o := 152) (by decide), hb]
        omega
  refine call_then hpc1 htab hP1 fun st2 hpc2 hrsp2 hq ↦ ?_
  simp only [SubspaceTablePost] at hq
  obtain ⟨hval, hch, hsv⟩ := hq
  rw [e1rsi, e1rdi] at hval
  simp only [hmu, ↓reduceIte] at hval
  obtain ⟨htag, htabb⟩ := hval
  rw [e1rdi] at hch
  have hs2 : SameOutside st1.data.dmem st2.data.dmem (EachRow.Hit m0 1984 eachRowNextStack 152 664) :=
    EachRow.hit_of_call hl (by decide) (by decide) hfr1.rsp0 (N' := subspaceTableStack)
      (by decide) le_rfl (by decide) hch
  have hfr2 : FR m0 8 st2.data :=
    EachRow.Fr.call hl (by decide) (by decide) hfr1 hrsp2 hsv hs2 (by decide)
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2 hfr2 hs2 hsv htag htabb
  subst hpc2
  -- `b1`, `b2`
  obtain ⟨hwf, hm⟩ := hfr2.got_env hl c.got c.got_nw
    (fun q h => ⟨(bOf m0, 16), by simp, h⟩) (by simp) (by simp : "memcpy" ∈ ["memcpy", "memset"])
    (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b2Offset + b2.length)).toBitVec
  have hk1 : b1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b1Offset) := b1_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hk2 : b2.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b2Offset) := b2_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hl152 : (EachRow.envE m0 d2 1984 16 [(gotAddr "memcpy", 8)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b2Offset + b2.length)).toBitVec).load 0 152 4 = BitVec.ofNat 64 (1 : UInt64).toNat :=
    NativeRustcVmX64.Transcript.load4_of_tag (.inr rfl) htag
  have hlen : (tableOf m0).toList.length = (tableOf m0).size := Array.length_toList
  have hl160 : (EachRow.envE m0 d2 1984 16 [(gotAddr "memcpy", 8)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b2Offset + b2.length)).toBitVec).load 0 160 8 =
        BitVec.ofNat 64 (tableOf m0).size := by
    have := htabb.2.1
    rw [hlen] at this
    rw [show off (fb m0 + BitVec.ofNat 64 152) 8 = fb m0 + BitVec.ofNat 64 160 from
      NativeRustcVm.addr_add_add _ _ _] at this
    exact NativeRustcVmX64.Arrays.load_word this
  rw [show (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b0Offset + b0.length) = k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b1Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.EachRowOfNextLevel.b0_next]]
  refine exec_then hk1 run_b1 hwf (fun _ h ↦ by cases h) hm fun st3 hm3 hpc3 ↦ ?_
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b2Offset) := by
    simp only [PcOk] at hpc3
    split at hpc3
    · rename_i hc
      exact absurd hc (by simp only [SBool.eval, Sym.eval, CmpOp.apply, hl152]; decide)
    · exact hpc3
  refine exec_at hk2 (exec_after run_b1 run_b2) hwf (fun _ _ ↦ rfl) hpc3' hm3
    fun st4 hm4 hpc4 ↦ ?_
  have hs4 : SameOutside d2.dmem st4.data.dmem (EachRow.Hit m0 1984 eachRowNextStack 1432 1432) :=
    EachRow.hit_of_block hl le_rfl (by decide) hm4 hwf (by decide)
  have hfr4 : FR m0 0 st4.data :=
    hfr2.step hl le_rfl (by decide)
      ((rv hm4 (v := .ptr 0 0) rfl).trans (EachRow.eval_ptr0 0)) (hm4.kept hwf) hs4 (by decide)
  have e4rdi : reg st4.data .rdi = fb m0 + BitVec.ofNat 64 1440 :=
    (rv hm4 (v := .ptr 0 1440) rfl).trans (EachRow.eval_ptr0 1440)
  have e4rsi : reg st4.data .rsi = fb m0 + BitVec.ofNat 64 168 :=
    (rv hm4 (v := .ptr 0 168) rfl).trans (EachRow.eval_ptr0 168)
  have e4rdx : (reg st4.data .rdx).toNat = 496 := by rw [rv hm4 (v := .lit 496) rfl]; rfl
  -- `memcpy`
  have hdst := hfr4.whirIn_frame hl (o := 1440) (c := 496) (N' := 0) (by decide) (by decide)
    (by decide)
  have hsrc := hfr4.whirIn_frame hl (o := 168) (c := 496) (N' := 0) (by decide) (by decide)
    (by decide)
  have a1440 := hl.addr (o := 1440) (by decide)
  have a168 := hl.addr (o := 168) (by decide)
  have a0 := hl.addr (o := 0) (by decide)
  have hP4 : MemcpyPre st4.data := by
    unfold MemcpyPre
    simp only
    rw [e4rdi, e4rsi, e4rdx]
    refine ⟨hfr4.stackOk hl (by decide), hdst.1.1, hsrc.1.1, hdst.1.2, hsrc.1.2, ?_, ?_⟩
    · unfold Apart
      rw [a1440, a168]
      omega
    · unfold Apart
      rw [hfr4.rsp, a1440, a0]
      omega
  refine call_then hpc4 hmemcpy hP4 fun st5 hpc5 hrsp5 hq5 ↦ ?_
  simp only [MemcpyPost] at hq5
  obtain ⟨-, hcopy, hsame5, hsv5⟩ := hq5
  rw [e4rdi, e4rdx] at hsame5
  rw [e4rdi, e4rsi, e4rdx] at hcopy
  have hs5 : SameOutside st4.data.dmem st5.data.dmem
      (EachRow.Hit m0 1984 eachRowNextStack 1440 1936) :=
    EachRow.hit_of_call hl (by decide) (by decide) hfr4.rsp0 (N' := 0) (by decide) le_rfl
      (by decide) fun q hq ↦ hsame5 q fun h ↦ hq (.inl ⟨_, List.mem_singleton_self _, h⟩)
  have hfr5 : FR m0 8 st5.data :=
    EachRow.Fr.call hl (by decide) (by decide) hfr4 hrsp5 hsv5 hs5 (by decide)
  obtain ⟨d5, pc5⟩ := st5
  simp only at hpc5 hfr5 hs5 hsv5 hcopy
  subst hpc5
  rw [show k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b2Offset + b2.length = k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b3Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.EachRowOfNextLevel.b2_next]]
  -- the table's pairs, kept to the copy
  have hsrcP : PairsAt st4.data.dmem (fb m0 + BitVec.ofNat 64 168) (tableOf m0).toList := by
    have := htabb.2.2
    rw [show off (off (fb m0 + BitVec.ofNat 64 152) 8) 8 = fb m0 + BitVec.ofNat 64 168 by
      rw [NativeRustcVm.Transcript.off_off]; exact NativeRustcVm.addr_add_add _ _ _] at this
    unfold PairsAt at this ⊢
    refine EachRow.keep_frame hl le_rfl (by decide) hs4 (by decide) (.inl ?_) this
    rw [NativeRustcVm.length_wordsBytes, EachRow.length_pairWords, hlen]
    have := htabb.1
    rw [hlen] at this
    have : rootCap = 31 := rfl
    omega
  have k1 : ∀ r, calleeSaved r = true → (after b2 (after b1 (EachRow.gotFrameS 1984 16 "memcpy"))).reg r = some (.reg r) →
      reg d5 r = reg st1.data r := fun r hc hr ↦ by
    rw [sv hsv5 r hc, rv hm4 (by rw [← after_eq (exec_after run_b1 run_b2)]; exact hr)]
    exact sv hsv r hc
  refine cont d5 ⟨hfr5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact keepW hl (by decide) (by decide) hs5 (by decide) (by decide)
      (keepW hl le_rfl (by decide) hs4 (by decide) (by decide)
        (keepW hl (by decide) (by decide) hs2 (by decide) (by decide) w88))
  · exact keepW hl (by decide) (by decide) hs5 (by decide) (by decide)
      (keepW hl le_rfl (by decide) hs4 (by decide) (by decide)
        (keepW hl (by decide) (by decide) hs2 (by decide) (by decide) w96))
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
  · rw [sv hsv5 .r14 rfl, rv hm4 (v := .load 0 160 8) rfl]
    exact hl160
  · rw [sv hsv5 .r13 rfl, rv hm4 (v := .ptr 0 1440) rfl]
    exact EachRow.eval_ptr0 1440
  · rw [k1 .r15 rfl rfl]; exact rv hm1 (v := .reg .rsi) rfl
  · rw [k1 .rbx rfl rfl]; exact rv hm1 (v := .reg .rdx) rfl
  · rw [k1 .r12 rfl rfl]; exact rv hm1 (v := .reg .rcx) rfl
  · exact bat_hit c (by decide) (by decide) hs5 (bat_hit c le_rfl (by decide) hs4
      (bat_hit c (by decide) (by decide) hs2 (bat_hit c (by decide) le_rfl hs1 c.b0)))

end

end NativeRustcVmX64.Whir.EachRowOfNextLevel
