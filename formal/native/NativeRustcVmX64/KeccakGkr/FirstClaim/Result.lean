module

public import NativeRustcVmX64.KeccakGkr.FirstClaim.Tail
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcX64.Got

/-!
# `first_claim`: the result (x86-64)

`b15` computes the claim's value `committed + last` (R13, RBP, the committed value the stack
arguments `0`, `1`) and copies the instance weights to the result, `b16` copies the point; `b17`
stores `Some`'s tag and the value; `b20` restores the registers and returns (`finish`).
-/

namespace NativeRustcVmX64.KeccakGkr.FirstClaim

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.FirstClaim
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off inRange_iff' Mapped.keeps
  bytesAt_congr inRange_off_self Touch)
open NativeVm.Math.Keccak (bitW)

public section

/-- **A `Buf<EW, N>` at offset `o` of `b` kept** where every byte range of it is kept. -/
theorem BufEWAt.keep_parts {d₁ d₂ : DataMem} {b : BitVec 64} {o N : Nat} {xs : List EW}
    (h : NativeRustcVm.BufEWAt d₁ (off b o) N xs)
    (hk : ∀ {o' : Nat} {bs : List UInt8}, o ≤ o' → o' + bs.length ≤ o + 8 + 16 * N →
      NativeRustcVm.BytesAt d₁ (off b o') bs → NativeRustcVm.BytesAt d₂ (off b o') bs) :
    NativeRustcVm.BufEWAt d₂ (off b o) N xs := by
  obtain ⟨hl, hw, he⟩ := h
  refine ⟨hl, hk le_rfl (by rw [NativeRustcVm.length_wordBytes]; omega) hw, ?_⟩
  rw [show off b o + 8#64 = off b (o + 8) from off_off _ _ _] at he ⊢
  exact hk (by omega) (by rw [ews_len]; omega) he

theorem xor_val (a : BitVec 64) (l : UInt64) :
    UInt64.ofBitVec (BinOp.apply .xor .W64 l.toBitVec a) = UInt64.ofBitVec a ^^^ l := by
  apply UInt64.toBitVec_inj.mp
  simp only [BinOp.apply, low_W64, ext_W64, UInt64.toBitVec_xor]
  exact BitVec.xor_comm _ _

variable {inst segment lanePoint output : Array EW} {m0 : MachineData}

/-- The stack's bytes are apart from the result. -/
theorem out_apart (h : PreOk inst segment lanePoint output m0) {a : BitVec 64} {l : Nat}
    (hal : (rspOf m0).toNat - 1632 ≤ a.toNat ∧ a.toNat + l ≤ (rspOf m0).toNat + 8) :
    a.toNat + l ≤ (outA m0).toNat ∨ (outA m0).toNat + 776 ≤ a.toNat := by
  have := (nums h).os
  omega

/-- The result's bytes `[o, o + n)` are apart from the frame's `[j, j + l)`. -/
theorem out_fb (h : PreOk inst segment lanePoint output m0) {o n j l : Nat} (hon : o + n ≤ 776)
    (hjl : j + l ≤ 1384) :
    (outA m0).toNat + o + n ≤ (rspOf m0).toNat - 1376 + j ∨
      (rspOf m0).toNat - 1376 + j + l ≤ (outA m0).toNat + o := by
  have := (nums h).os
  have := (nums h).r1
  omega

/-- The result's bytes `[o, o + n)` are apart from the frame's base's `8` bytes. -/
theorem out_fb0 (h : PreOk inst segment lanePoint output m0) {o n : Nat} (ho : o < 776)
    (hon : o + n ≤ 776) : NativeRustcVm.Apart (off (outA m0) o) n (fbA m0) 8 := by
  have := (nums h).os
  have := (nums h).r1
  have := (nums h).o
  unfold NativeRustcVm.Apart
  rw [toNat_off (by omega), fbA_toNat h]
  omega

variable [Host] {k : Nat}

/-- **`b15` to `b20`**: from the claim in the frame to the return. -/
theorem finish (hp : Placed code k) (hpre : FirstClaimPre inst segment lanePoint output m0)
    (hmemcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b15Offset)) (hI : PDone m0 inst segment lanePoint output st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = retOf m0 ∧ rspOf s'.data = rspOf m0 + 8#64 ∧
      FirstClaimPost inst segment lanePoint output m0 s'.data) st := by
  have h := preOk hpre
  have hn := nums h
  have hr1 := hn.r1
  have hr2 := hn.r2
  have ho := hn.o
  have hos := hn.os
  have hfb := fbA_toNat h
  have hfmap := frame_mapped h.st (F := 1376) (by rw [stack_eq]; decide)
  have hom : NativeRustcVm.Mapped m0.dmem (outA m0) 776 :=
    (Areas.ok h.areas (List.mem_append_left _ List.mem_cons_self)).1
  -- `b15`: the value, `memcpy` of the instance weights.
  have hgot := hpre.2.2.2.2.2.2.2.2.2.2.2.2
  have hg := hgot.1 "memcpy" (by simp)
  have hgf : NativeRustcVm.Apart (gotAddr "memcpy") 8 (fbA m0) 1384 :=
    apart_frame hg.2.2.1 h.st.1 (by rw [stack_eq]; decide)
  have hga : NativeRustcVm.Apart (gotAddr "memcpy") 8 (argA m0) 24 :=
    apart_iff.mp (hg.2.2.2 (argA m0, 24) (by simp))
  have hgw := hgot.areas (areas' := [(outA m0, 776), (wA m0, 25600)])
    (by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;>
        simp [NativeRustcVm.KeccakGkr.claimBytes, NativeRustcVm.KeccakGkr.weightsBytes])
  have hkeep := hgw.unchanged h.st
    (by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact hn.o
      · exact hn.w)
    (hI.body.same.mono (by
      intro q hq
      rcases hq with ho | hw | hs
      · exact .inr ⟨(outA m0, 776), by simp, inRange_iff.mpr ho⟩
      · exact .inr ⟨(wA m0, 25600), by simp, inRange_iff.mpr hw⟩
      · exact .inl hs))
  have hfnw := frame_noWrap h.st (F := 1376) (by rw [stack_eq]; decide)
  have hargn : NativeRustcVm.NoWrap (argA m0) 24 := by
    change (argA m0).toNat + 24 ≤ 2 ^ 64
    rw [argA_toNat h]; omega
  have hfa : NativeRustcVm.Apart (fbA m0) 1384 (argA m0) 24 := by
    unfold NativeRustcVm.Apart
    rw [fbA_toNat h, argA_toNat h]
    omega
  have hwf : (frameEnv m0 st.data 1376 [(argA m0, 24), (gotAddr "memcpy", 8)]
      (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b15Offset + b15.length)).toBitVec).WF := by
    apply frame_wf ⟨Mapped.keeps hfmap hI.body.frame.kept, hfnw⟩
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨Mapped.keeps h.args.1 hI.body.frame.kept, hargn⟩
      · exact ⟨Mapped.keeps (hgot.mapped (by simp)) hI.body.frame.kept, hg.2.1⟩
    · refine List.pairwise_cons.mpr ⟨?_, List.pairwise_pair.mpr (Apart.symm' hga)⟩
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact hfa
      · exact Apart.symm' hgf
  have halias := arg_alias (m0 := m0) (d := st.data) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b15Offset + b15.length)).toBitVec)
  have hm : Match
      (frameEnv m0 st.data 1376 [(argA m0, 24), (gotAddr "memcpy", 8)] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b15Offset + b15.length)).toBitVec)
      copyS st.data := by
    apply Match.withKnownBytes
    · exact match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hI.body.frame.rsp_eval, trivial⟩
        trivial trivial ⟨halias 0, halias 1, halias 2,
          by simp [Sym.eval, Env.base, gotAddr], trivial⟩
    · intro i hi
      simp only [Nat.zero_add, Sym.eval, Env.base_ofMachine_eq, Env.ofMachine_mem0]
      change st.data.dmem.get? (gotAddr "memcpy" + BitVec.ofNat 64 i) = _
      rw [hkeep "memcpy" (by simp) i hi]
      exact hgot.byte (by simp) hi
  refine exec_at (infix_of b15_in_code (by simp [b15]) hp) exit_b15 hwf (fun _ _ ↦ rfl) hpc
    hm fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hwi1, hrdi, hrsi, hrdx, hr13, hrbp, hat1, hr14⟩ := ok_b15
  have hf1 : Frame m0 1376 slots 0 st1.data := Frame.of_block hI.body.frame hwf hm1 hmid1 slots_le'
  have hs1 := sameOutside_touch hwf hm1 (r := 0) rfl (by decide) (within_spec hwi1)
  have hsp1 : rspOf st1.data = fbA m0 := by rw [hf1.sp, off_zero]
  have hso1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem (Out m0) := fun q hq ↦
    (hs1 q fun ht ↦ hq (touch_out h (fun _ hj ↦ by omega) ht)).trans (hI.body.same q hq)
  have a0 : (frameEnv m0 st.data 1376 [(argA m0, 24), (gotAddr "memcpy", 8)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b15Offset + b15.length)).toBitVec).load 1 0 8 = stackArg m0 0 :=
    load_arg h hI.body.same (i := 0) (by decide) [(gotAddr "memcpy", 8)]
  have a1 : (frameEnv m0 st.data 1376 [(argA m0, 24), (gotAddr "memcpy", 8)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b15Offset + b15.length)).toBitVec).load 1 8 8 = stackArg m0 1 :=
    load_arg h hI.body.same (i := 1) (by decide) [(gotAddr "memcpy", 8)]
  have v13 : UInt64.ofBitVec (reg st1.data .r13) =
      UInt64.ofBitVec (stackArg m0 0) ^^^ (lastOf segment lanePoint output).c0 := by
    rw [show reg st1.data .r13 = _ from hm1.regs .r13 _ hr13]
    show UInt64.ofBitVec (BinOp.apply .xor .W64 (reg st.data .r13) (Env.load _ 1 0 8)) = _
    rw [a0, hI.r13, xor_val]
  have vbp : UInt64.ofBitVec (reg st1.data .rbp) =
      UInt64.ofBitVec (stackArg m0 1) ^^^ (lastOf segment lanePoint output).c1 := by
    rw [show reg st1.data .rbp = _ from hm1.regs .rbp _ hrbp]
    show UInt64.ofBitVec (BinOp.apply .xor .W64 (reg st.data .rbp) (Env.load _ 1 8 8)) = _
    rw [a1, hI.rbp, xor_val]
  have e15 : reg st1.data .r15 = outA m0 := (atoms_eq hm1 hat1 (by simp)).trans hI.r15
  have e7 : reg st1.data .rdi = off (outA m0) 24 := by
    rw [show reg st1.data .rdi = _ from hm1.regs .rdi _ hrdi]
    show BinOp.apply .add .W64 (reg st.data .r15) (BitVec.ofNat 64 24) = _
    simp only [BinOp.apply, low_W64, ext_W64]
    rw [hI.r15]
  have e6 : reg st1.data .rsi = off (fbA m0) 64 := (hm1.regs .rsi _ hrsi).trans (eval_ptr0 64)
  have e2 : (reg st1.data .rdx).toNat = 264 := by
    rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ hrdx]; rfl
  have hf64 : (off (fbA m0) 64).toNat = (rspOf m0).toNat - 1376 + 64 := fb_off h (by decide)
  have ho24 : (off (outA m0) 24).toNat = (outA m0).toNat + 24 := toNat_off (by omega)
  have hpre1 : MemcpyPre st1.data := by
    unfold MemcpyPre
    rw [e7, e6, e2, hsp1]
    refine ⟨stackOk_callee h.st hf1.kept hsp1 (by rw [stack_eq]; decide),
      Mapped.keeps (mapped_off hom (by decide)) hf1.kept,
      Mapped.keeps (mapped_off hfmap (by decide)) hf1.kept, ?_, ?_, ?_, ?_⟩
    · show _ + _ ≤ _; rw [ho24]; omega
    · show _ + _ ≤ _; rw [hf64]; omega
    · show _ + _ ≤ _ ∨ _ + _ ≤ _; rw [ho24, hf64]; omega
    · show _ + _ ≤ _ ∨ _ + _ ≤ _; rw [ho24, hfb]; omega
  refine call_then hpc1 hmemcpy hpre1 fun st2 hpc2 hrsp2 ⟨_, hcp2, hsame2, hsv2⟩ ↦ ?_
  rw [e7, e6, e2] at hcp2
  rw [e7, e2] at hsame2
  obtain ⟨hb2, -⟩ := call_body h hf1 hso1 hsv2 hrsp2 (s := 0) (by decide)
    (NativeRustcVm.Transcript.SameOutside.mono hsame2 fun _ hq ↦ Or.inl hq)
    (out_D h (o := 24) (n := 264) (by decide) (by decide))
  have hmu1 : NativeRustcVm.BufEWAt st1.data.dmem (off (fbA m0) 64) 16
      (eqKernel (inst.extract 0 4)).toList :=
    BufEWAt.keep_parts hI.mu fun h1 h2 hb ↦ keep_touch h hs1 (by omega) (by omega) hb
  have hmuO2 : NativeRustcVm.BufEWAt st2.data.dmem (off (outA m0) 24) 16
      (eqKernel (inst.extract 0 4)).toList :=
    BufEWAt.copy hmu1 (by rw [show 8 + 16 * 16 = 264 from rfl]; exact hcp2)
  have hpt2 : NativeRustcVm.BufEWAt st2.data.dmem (off (fbA m0) 840) 30
      (pointOf inst segment).toList :=
    BufEWAt.keep_parts hI.pt <| by
      intro o' bs h1 h2 hb
      have hr := fb_range h (o := o') (n := bs.length) (by omega)
      exact keep_offout h (o' := 24) (n' := 264) (by decide) (by decide) hsame2 (by omega)
        (out_apart h hr) (keep_touch h hs1 (by omega) (by omega) hb)
  -- `b16`: `memcpy` of the point.
  have hwf2 := wf_body h hb2.frame.kept (d := st2.data) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b16Offset + b16.length)).toBitVec)
  have hm2 : Match (frameEnv m0 st2.data 1376 [(argA m0, 24)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b16Offset + b16.length)).toBitVec)
      copyRetS st2.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨hb2.frame.rsp_eval, (hsv2.1 .r14 rfl).trans (hm1.regs .r14 _ hr14), trivial⟩
      trivial trivial ⟨arg_alias 0, arg_alias 1, arg_alias 2, trivial⟩
  refine exec_at (infix_of b16_in_code (by simp [b16]) hp) exit_b16 hwf2 (fun _ _ ↦ rfl)
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.FirstClaim.b15_next)) hm2
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hwi3, hrdi3, hrsi3, hrdx3, hat3⟩ := ok_b16
  have hf3 : Frame m0 1376 slots 0 st3.data := Frame.of_block hb2.frame hwf2 hm3 hmid3 slots_le'
  have hs3 := sameOutside_touch hwf2 hm3 (r := 0) rfl (by decide) (within_spec hwi3)
  have hsp3 : rspOf st3.data = fbA m0 := by rw [hf3.sp, off_zero]
  have hso3 : NativeRustcVm.SameOutside m0.dmem st3.data.dmem (Out m0) := fun q hq ↦
    (hs3 q fun ht ↦ hq (touch_out h (fun _ hj ↦ by omega) ht)).trans (hb2.same q hq)
  have r3 : ∀ r ∈ [Reg64.rbp, .r13, .r15], reg st3.data r = reg st2.data r :=
    fun r hr ↦ atoms_eq hm3 hat3 hr
  have f7 : reg st3.data .rdi = off (outA m0) 288 := by
    rw [show reg st3.data .rdi = _ from hm3.regs .rdi _ hrdi3]
    show BinOp.apply .add .W64 (reg st2.data .r15) (BitVec.ofNat 64 288) = _
    simp only [BinOp.apply, low_W64, ext_W64]
    rw [show reg st2.data .r15 = outA m0 from (hsv2.1 .r15 rfl).trans e15]
  have f6 : reg st3.data .rsi = off (fbA m0) 840 := (hm3.regs .rsi _ hrsi3).trans (eval_ptr0 840)
  have f2 : (reg st3.data .rdx).toNat = 488 := by
    rw [show reg st3.data .rdx = _ from hm3.regs .rdx _ hrdx3]; rfl
  have hf840 : (off (fbA m0) 840).toNat = (rspOf m0).toNat - 1376 + 840 := fb_off h (by decide)
  have ho288 : (off (outA m0) 288).toNat = (outA m0).toNat + 288 := toNat_off (by omega)
  have hap3 : NativeRustcVm.Apart (off (outA m0) 288) 488 (fbA m0) 8 :=
    out_fb0 h (by decide) (by decide)
  have hpre3 : MemcpyPre st3.data := by
    unfold MemcpyPre
    rw [f7, f6, f2, hsp3]
    refine ⟨stackOk_callee h.st hf3.kept hsp3 (by rw [stack_eq]; decide),
      Mapped.keeps (mapped_off hom (by decide)) hf3.kept,
      Mapped.keeps (mapped_off hfmap (by decide)) hf3.kept, ?_, ?_, ?_, ?_⟩
    · show _ + _ ≤ _; rw [ho288]; omega
    · show _ + _ ≤ _; rw [hf840]; omega
    · show _ + _ ≤ _ ∨ _ + _ ≤ _; rw [ho288, hf840]; exact out_fb h (by decide) (by decide)
    · exact hap3
  refine call_then hpc3 hmemcpy hpre3 fun st4 hpc4 hrsp4 ⟨_, hcp4, hsame4, hsv4⟩ ↦ ?_
  rw [f7, f6, f2] at hcp4
  rw [f7, f2] at hsame4
  obtain ⟨hb4, -⟩ := call_body h hf3 hso3 hsv4 hrsp4 (s := 0) (by decide)
    (NativeRustcVm.Transcript.SameOutside.mono hsame4 fun _ hq ↦ Or.inl hq)
    (out_D h (o := 288) (n := 488) (by decide) (by decide))
  have hpt3 : NativeRustcVm.BufEWAt st3.data.dmem (off (fbA m0) 840) 30
      (pointOf inst segment).toList :=
    BufEWAt.keep_parts hpt2 fun h1 h2 hb ↦ keep_touch h hs3 (by omega) (by omega) hb
  have hptO4 : NativeRustcVm.BufEWAt st4.data.dmem (off (outA m0) 288) 30
      (pointOf inst segment).toList :=
    BufEWAt.copy hpt3 (by rw [show 8 + 16 * 30 = 488 from rfl]; exact hcp4)
  have houtW : ∀ {W : Nat → Prop}, (∀ j, W j → j < 1376) → ∀ {o : Nat} {bs : List UInt8},
      o + bs.length ≤ 776 → ∀ {d₁ d₂ : DataMem},
      NativeRustcVm.SameOutside d₁ d₂ (fun q ↦ Touch (fbA m0) (1376 + 8) W q) →
      NativeRustcVm.BytesAt d₁ (off (outA m0) o) bs →
      NativeRustcVm.BytesAt d₂ (off (outA m0) o) bs := by
    intro W hW o bs hle d₁ d₂ hs hb
    exact bytesAt_congr hb fun i hi ↦ hs _ fun ht ↦ out_not_stk h
      (by rw [NativeRustcVm.Transcript.off_add]; exact inRange_off_self (by omega) (by omega))
      (touch_stk h hW ht)
  have hmuO4 : NativeRustcVm.BufEWAt st4.data.dmem (off (outA m0) 24) 16
      (eqKernel (inst.extract 0 4)).toList :=
    BufEWAt.keep_parts hmuO2 fun h1 h2 hb ↦ keep_outout h (o' := 288) (n' := 488) (by omega)
      (by decide) (by decide) (by omega) hsame4 (houtW (fun _ hj ↦ by omega) (by omega) hs3 hb)
  -- `b17`: `Some`'s tag and the value.
  have hfnw := frame_noWrap h.st (F := 1376) (by rw [stack_eq]; decide)
  have hwf4 : (frameEnv m0 st4.data 1376 [(outA m0, 776)] (fun _ ↦ 0) 0).WF := by
    refine frame_wf ⟨Mapped.keeps hfmap hb4.frame.kept, hfnw⟩ (fun x hx ↦ ?_)
      (List.pairwise_pair.mpr ?_)
    · rw [List.mem_singleton] at hx
      subst hx
      exact ⟨Mapped.keeps hom hb4.frame.kept, by show (outA m0).toNat + 776 ≤ 2 ^ 64; omega⟩
    · show (fbA m0).toNat + (1376 + 8) ≤ (outA m0).toNat ∨
        (outA m0).toNat + 776 ≤ (fbA m0).toNat
      rw [hfb]; omega
  have e15' : reg st4.data .r15 = outA m0 :=
    (hsv4.1 .r15 rfl).trans ((r3 .r15 (by simp)).trans ((hsv2.1 .r15 rfl).trans e15))
  have hm4 : Match (frameEnv m0 st4.data 1376 [(outA m0, 776)] (fun _ ↦ 0) 0) outS st4.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb4.frame.rsp_eval, by
      show reg st4.data .r15 = outA m0 + BitVec.ofInt 64 0
      rw [e15']; exact (BitVec.add_zero _).symm, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b17_in_code (by simp [b17]) hp) exit_b17 hwf4 nofun
    (hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.FirstClaim.b16_next)) hm4 fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hmid5, hws5, hw0, hw8, hw16⟩ := ok_b17
  have hf5 : Frame m0 1376 slots 8 st5.data := Frame.of_block hb4.frame hwf4 hm5 hmid5 slots_le'
  have hs5 := sameOutside_touch hwf4 hm5 (r := 1) rfl (by decide) hws5
  have hT5 : ∀ q, Touch (outA m0) 776 (fun j ↦ 0 ≤ j ∧ j < 24) q →
      NativeRustcVm.InRange (outA m0) 776 q := fun q hq ↦ inRange_of_touch (by omega) hq
  have hb5 : Body m0 st5.data :=
    ⟨hf5, fun q hq ↦ (hs5 q fun ht ↦ hq (Or.inl (hT5 q ht))).trans (hb4.same q hq)⟩
  have htag : NativeRustcVm.WordAt st5.data.dmem (outA m0) 1 := by
    have := wordAt_write hm5 (r := 1) (o := 0) (v := .lit 1) rfl (by decide) hw0
    rw [off_zero] at this
    exact this
  have hval : NativeRustcVm.EWAt st5.data.dmem (off (outA m0) 8)
      (firstCommitted m0 + lastOf segment lanePoint output) := by
    have := Match.ewAt_write hm5 (r := 1) (o := 8) (v0 := .reg .r13) (v1 := .reg .rbp) rfl
      (by decide) hw8 fun i hi ↦ by rw [show 8 + 8 + i = 16 + i by omega]; exact hw16 i hi
    have e13 : reg st4.data .r13 = reg st1.data .r13 :=
      (hsv4.1 .r13 rfl).trans ((r3 .r13 (by simp)).trans (hsv2.1 .r13 rfl))
    have ebp : reg st4.data .rbp = reg st1.data .rbp :=
      (hsv4.1 .rbp rfl).trans ((r3 .rbp (by simp)).trans (hsv2.1 .rbp rfl))
    change NativeRustcVm.EWAt _ _ ⟨UInt64.ofBitVec (reg st4.data .r13),
      UInt64.ofBitVec (reg st4.data .rbp)⟩ at this
    rw [e13, ebp, v13, vbp] at this
    exact this
  -- the results kept
  have hT : ∀ {o : Nat} {bs : List UInt8}, 24 ≤ o → o + bs.length ≤ 776 →
      NativeRustcVm.BytesAt st4.data.dmem (off (outA m0) o) bs →
      NativeRustcVm.BytesAt st5.data.dmem (off (outA m0) o) bs := by
    intro o bs h1 h2 hb
    exact bytesAt_congr hb fun i hi ↦ hs5 _ fun ⟨j, hj, hW, e⟩ ↦ by
      rw [NativeRustcVm.Transcript.off_add] at e
      have := NativeRustcVm.Transcript.off_inj (b := outA m0) (N := 776)
        (by unfold NativeRustcVm.NoWrap; omega) hj (show o + i < 776 by omega) e
      omega
  have hmuO5 := BufEWAt.keep_parts hmuO4 fun h1 h2 hb ↦ hT (by omega) (by omega) hb
  have hptO5 := BufEWAt.keep_parts hptO4 fun h1 h2 hb ↦ hT (by omega) (by omega) hb
  -- the bit weights kept
  have hw5 : ElemsAt st5.data.dmem (wA m0) (bitW (eqKernel lanePoint)) 1600 := by
    have hwo := hn.ow
    have hw := hn.w
    have tk : ∀ q, Touch (fbA m0) (1376 + 8) (fun j ↦ 0 ≤ j ∧ j < 8) q →
        ¬ NativeRustcVm.InRange (wA m0) 25600 q :=
      stk_w h fun _ hq ↦ touch_stk h (fun _ hj ↦ by omega) hq
    have oi : ∀ {o n : Nat}, o < 776 → o + n ≤ 776 → ∀ q,
        NativeRustcVm.InRange (off (outA m0) o) n q →
        ¬ NativeRustcVm.InRange (wA m0) 25600 q := fun ho' hon q hq hw' ↦ by
      have h1 := inR (by omega) hw'
      have h2 := inR (by rw [toNat_off (by omega)]; omega) hq
      rw [toNat_off (by omega)] at h2
      omega
    have w1 := w_keep h hs1 tk hI.w
    have w2 := w_keep h hsame2 (oi (by decide) (by decide)) w1
    have w3 := w_keep h hs3 tk w2
    have w4 := w_keep h hsame4 (oi (by decide) (by decide)) w3
    exact w_keep h hs5 (fun q hq ↦ oi (o := 0) (n := 776) (by decide) (by decide) q
      (by rw [off_zero]; exact hT5 q hq)) w4
  -- `b20`: the epilogue.
  have hpc5' : st5.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b20Offset) := by
    simp only [PcOk] at hpc5
    exact hpc5.trans (label_of_infix hp b20_in_code rfl)
  have hwf5 := wf_body h hb5.frame.kept (d := st5.data) (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b20_in_code (by simp [b20]) hp) exit_b20 hwf5 nofun hpc5'
    (match_callS hb5.frame) fun st6 hm6 hpc6 ↦ .done _ ?_
  obtain ⟨hepi, hmem6⟩ := ok_b20
  obtain ⟨hsv6, hrsp6⟩ := Frame.epilogue hb5.frame hwf5 hm6 hepi
  have hd6 : st6.data.dmem = st5.data.dmem := hm6.dmem_eq hwf5 hmem6
  simp only [PcOk] at hpc6
  have hlen : (keccakFirstClaim inst segment lanePoint output (firstCommitted m0)).weights.toList =
      (List.range 1600).map (bitW (eqKernel lanePoint)) := by
    rw [NativeVm.Math.Keccak.kfc_weights, Array.toList_map, Array.toList_range]
    rfl
  refine ⟨by rw [hpc6]; exact hb5.frame.load_ret h.st (by rw [stack_eq]; decide), hrsp6,
    by rw [hd6]; exact htag, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, fun q hq ↦ ?_, hsv6⟩
  · rw [hd6, NativeVm.Math.Keccak.kfc_value]; exact hval
  · show NativeRustcVm.BufEWAt _ (off (off (outA m0) 8) 16) 16 _
    rw [off_off, hd6]; exact hmuO5
  · show NativeRustcVm.BufEWAt _ (off (off (outA m0) 8) 280) 30 _
    rw [off_off, hd6]; exact hptO5
  · rw [NativeVm.Math.Keccak.kfc_weights, Array.size_map, Array.size_range]
  · rw [hlen, hd6]
    refine ElemsAt.ewsAt ?_
    rw [List.length_map, List.length_range]
    intro i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some]
    exact hw5 i hi
  · rw [hd6]
    refine hb5.same q fun hO ↦ hq ?_
    rcases hO with h1 | h1 | h1
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h1⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), h1⟩
    · exact ⟨_, List.mem_cons_self, h1⟩

end

end NativeRustcVmX64.KeccakGkr.FirstClaim
