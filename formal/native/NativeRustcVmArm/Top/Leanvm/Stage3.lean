module

public import NativeRustcVmArm.Code.Vm.Verify.Names
public import NativeRustcVmArm.Top.Leanvm.VPre
public import NativeRustcVmArm.Top.Leanvm.Model
public import NativeRustcVm.Transcript.Update

/-!
# `leanvm_verify`: the verifier's call

`stage3`: from `C2` at `.LLeanvmVerify_14`, `b17` writes the `Decoded` into the frame and calls
`verify` on the bytecode, the public input in the frame, the `Decoded` and the working area;
`b18` and the epilogue return its verdict, `verdictWord`.
-/

namespace NativeRustcVmArm.Top.Leanvm

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.LeanvmVerify NativeVm
open NativeRustcVm (WordAt WordsAt Region)
open NativeRustcVm.Top (workAreaBytes entryRegions ApartFrom Aligned)
open NativeRustcVm.Wire (streamW openingsW)
open NativeVm.Wire (decodeM PhaseOut)
open LeanVM.Parameters (E)

public section

/-- A word `b17` writes into the frame. -/
theorem wordAt_b17 [Labels] {st st' : MachineData} {m0 : MachineData}
    (hm : Match (Env.ofMachine st [(frameOf m0, 128)]) (after b17 frameS) st') {o : Nat}
    {r : XReg} (hp : (o, r) ∈ decWords) {w : UInt64} (hv : st.regs.getXReg r = w) :
    WordAt st'.dmem (frameOf m0 + BitVec.ofNat 64 o) w := by
  have hw := b17_dec _ hp
  have hle : o + 8 ≤ 128 := by
    simp only [decWords, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    omega
  unfold WordAt
  rw [wordBytes_byteOf, ← hv]
  exact hm.bytesAt_write (r := 0) rfl hle hw

theorem trunc_okWord (b : Bool) :
    UnOp.apply .trunc .W32 (if b then (1 : UInt64) else 0).toBitVec =
      (if b then (1 : UInt64) else 0).toBitVec := by
  cases b <;> rfl

variable [Host] {k : Nat}

/-- **The verifier's call**, from `.LLeanvmVerify_14`. -/
theorem stage3 (hp : Placed code k)
    (hver : ∀ a stream openings, Spec (Labels.label NativeRustcVmArm.Vm.Verify.entryLabel) (VerifyPre a stream openings)
      (VerifyPost stream openings))
    {a : NativeVm.Entry.Areas} {bytes : List UInt8} {bytecode : List UInt64} {pub : Vector UInt64 4}
    {m0 : MachineData} (hpre : LeanvmVerifyPre a bytes bytecode pub m0)
    {r : List E × List PhaseOut} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b17Offset))
    (h2 : C2 a bytes bytecode pub m0 st.data r) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      st'.data.regs.X0 = (if NativeVm.Model.verify bytecode.toArray pub (streamW r.1)
        (openingsW r.2) then 1 else 0) ∧
      SameOutside m0.dmem st'.data.dmem (R2 a bytes.length m0) ∧ Saved m0 st'.data) st := by
  have g := geo_of hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, hmap⟩, -, hin, -, -, -⟩ := hpre'
  have hs := g.s
  have hF := g.F
  have hsb : (m0.regs.SP.toBitVec - BitVec.ofNat 64 leanvmVerifyStack).toNat =
      m0.regs.SP.toBitVec.toNat - 19344 := g.sb
  have hS := leanvmVerifyStack_eq
  have hsl := m0.regs.SP.toBitVec.isLt
  have hs128 : 128 ≤ m0.regs.SP.toBitVec.toNat := by omega
  have hal16 := g.al
  have hn32 := hin.bcSmall
  have hFm0 : Mapped m0.dmem (frameOf m0) 128 :=
    Mapped.within hmap (by rw [hsb]; omega) (by rw [hsb, hF]; omega) (by rw [hsb, hF]; omega)
  obtain ⟨hwf, hm⟩ := frameEnv h2.body hs128 hal16 (Mapped.kept hFm0 h2.body.kept)
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b17Offset hp b17_in_code (by simp [b17])) run_b17 hwf hpc hm
    fun st17 hm17 hpc17 ↦ ?_
  have hk := b17_keeps
  rw [after_eq run_b17] at hk
  have hmem := b17_mem
  rw [after_eq run_b17] at hmem
  have hm17' : Match (Env.ofMachine st.data [(frameOf m0, 128)]) (after b17 frameS) st17.data := by
    rw [after_eq run_b17]; exact hm17
  have hW : ∀ q, Written (Env.ofMachine st.data [(frameOf m0, 128)]) (after b17 frameS) q →
      (frameOf m0).toNat + 40 ≤ q.toNat ∧ q.toNat < (frameOf m0).toNat + 64 := fun q hq ↦
    written_sub (r := 0) rfl hmem hq
  have hsame : SameOutside st.data.dmem st17.data.dmem
      (fun q ↦ (frameOf m0).toNat + 40 ≤ q.toNat ∧ q.toNat < (frameOf m0).toNat + 64) :=
    fun q hq ↦ hm17'.get?_mem0 hwf fun hw ↦ hq (hW q hw)
  have hB : Body m0 128 slots (R2 a bytes.length m0) st17.data :=
    h2.body.block' slotsIn hs128 hm hm17 hwf rfl hk (fun _ hr hn ↦ nonslot hr hn) fun q hq ↦ by
      have := hW q (by rw [after_eq run_b17]; exact hq)
      rw [hF] at this
      exact ⟨Or.inl (by unfold InStack; omega), by omega⟩
  -- The `Decoded`, the decoded proof, the public input, the bytecode.
  have hdecF : NativeRustcVm.Transcript.DecFieldsAt st17.data.dmem
      (frameOf m0 + BitVec.ofNat 64 40) (decArea a bytes.length) := by
    refine ⟨wordAt_b17 hm17' (o := 40) (r := .X23) (by simp [decWords]) h2.x23, ?_, ?_⟩
    · rw [NativeRustcVm.Transcript.off, NativeRustcVm.addr_add_add]
      exact wordAt_b17 hm17' (o := 48) (r := .X21) (by simp [decWords]) h2.x21
    · rw [NativeRustcVm.Transcript.off, NativeRustcVm.addr_add_add]
      exact wordAt_b17 hm17' (o := 56) (r := .X19) (by simp [decWords]) h2.x19
  have hdec : NativeRustcVm.Transcript.DecodedAt st17.data.dmem (decArea a bytes.length)
      (streamW r.1) (openingsW r.2) := by
    refine h2.dec.agree fun j hj _ ↦ hsame _ fun ⟨h1, h3⟩ ↦ ?_
    have gd := g.dec
    have gdN := g.decN
    have ed : a.decoded.toBitVec.toNat = a.decoded.toNat := rfl
    simp only at hj h1 h3
    rw [toNat_addr (by omega), hF] at h1 h3
    omega
  have hF8 : (frameOf m0 + BitVec.ofNat 64 8).toNat = m0.regs.SP.toBitVec.toNat - 120 := by
    rw [toNat_addr (by rw [hF]; omega), hF]; omega
  have hpub : WordsAt st17.data.dmem (frameOf m0 + BitVec.ofNat 64 8) pub.toList :=
    wordsAt_keep h2.pubAt hsame (by rw [Vector.length_toList, hF8]; omega) fun q hq ↦ by
      rw [Vector.length_toList, hF8]; rw [hF] at hq; omega
  have hbc : WordsAt st17.data.dmem a.bytecode.toBitVec bytecode := by
    by_cases hn0 : bytecode.length = 0
    · rw [List.eq_nil_of_length_eq_zero hn0]; exact NativeRustcVm.wordsAt_nil _ _
    · have gb := g.bc (by omega)
      have gbd := g.bcDec
      have gbw := g.bcWork
      have gbN := g.bcN
      have gd := g.dec
      have gdN := g.decN
      have gw := g.work
      have gwN := g.workN
      have eb : a.bytecode.toBitVec.toNat = a.bytecode.toNat := rfl
      have ed : a.decoded.toBitVec.toNat = a.decoded.toNat := rfl
      have ew : a.work.toBitVec.toNat = a.work.toNat := rfl
      refine wordsAt_keep (wordsAt_keep (NativeRustcVm.wordsAt_of_wordView hin.bcWords)
        h2.body.same (by omega) fun q hq ↦ ?_) hsame (by omega) fun q hq ↦ by omega
      rcases hq with hq | hq | hq
      · unfold InStack at hq; rw [hS] at hq; omega
      · rw [inRange_nat gdN] at hq; omega
      · rw [inRange_nat gwN] at hq; omega
  -- `verify`'s arguments.
  have hX20 : (Env.ofMachine st.data [(frameOf m0, 128)]).regs .X20 =
      BitVec.ofNat 64 bytecode.length := congrArg UInt64.toBitVec h2.x20
  have hX0 : 0 < bytecode.length → st17.data.regs.X0 = a.bytecode := fun hn ↦ by
    apply UInt64.toBitVec_inj.mp
    show (st17.data.regs.getXReg .X0).toBitVec = _
    rw [hm17.regs .X0 _ rfl]
    simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64, hX20,
      ofNat_beq (show bytecode.length < 2 ^ 64 by omega) (show 0 < 2 ^ 64 by decide)]
    rw [show decide (bytecode.length = 0) = false from decide_eq_false (by omega)]
    simp only [Bool.false_eq_true, ite_false]
    exact congrArg UInt64.toBitVec h2.x24
  have hX1 : st17.data.regs.X1 = bytecode.length.toUInt64 :=
    (UInt64.toBitVec_inj.mp (hm17.regs .X1 _ rfl)).trans h2.x20
  have hX2 : st17.data.regs.X2.toBitVec = frameOf m0 + BitVec.ofNat 64 8 := hm17.regs .X2 _ rfl
  have hX3 : st17.data.regs.X3.toBitVec = frameOf m0 + BitVec.ofNat 64 40 := hm17.regs .X3 _ rfl
  have hX4 : st17.data.regs.X4 = a.work :=
    (UInt64.toBitVec_inj.mp (hm17.regs .X4 _ rfl)).trans h2.x22
  have hvp := vPre hpre hB hdecF hdec hX0 hX1 hX2 hX3 hX4
  refine call_then hpc17 (hver _ _ _) hvp fun st18 hpc18 hpost ↦ ?_
  obtain ⟨hres, hsame18, hsaved18⟩ := hpost
  have hX1n : st17.data.regs.X1.toNat = bytecode.length := by
    rw [hX1]; exact natToU64 (by omega)
  have hv := hres bytecode hX1n.symm (by
      by_cases hn0 : bytecode.length = 0
      · rw [List.eq_nil_of_length_eq_zero hn0]; exact NativeRustcVm.wordsAt_nil _ _
      · rw [hX0 (by omega)]; exact hbc)
    pub (by rw [hX2]; exact hpub)
  -- After `verify`: the body.
  have hV : verifyStack = 19216 := rfl
  have hsp17 : st17.data.regs.SP.toBitVec = frameOf m0 := hB.sp
  have hsbV : (stackBelow st17.data verifyStack).toNat = m0.regs.SP.toBitVec.toNat - 19344 := by
    show (st17.data.regs.SP.toBitVec - BitVec.ofNat 64 verifyStack).toNat = _
    rw [hsp17, hV, toNat_subAddr (by rw [hF]; omega), hF]; omega
  have gw := g.work
  have gwN := g.workN
  have ew : a.work.toBitVec.toNat = a.work.toNat := rfl
  have hB18 : Body m0 128 slots (R2 a bytes.length m0) st18.data := by
    refine hB.call slotsIn hs128 hsame18 hsaved18 fun q hq ↦ ?_
    simp only [NativeRustcVm.InAny, List.mem_cons, List.mem_nil_iff, or_false, exists_eq_or_imp,
      exists_eq_left, NativeRustcVm.Region.Holds, stackR] at hq
    rcases hq with hq | hq
    · rw [hX4] at hq
      have hq' := (NativeRustcVm.inRange_iff gwN).mp hq
      exact ⟨Or.inr (Or.inr hq), by omega⟩
    · have hq' := (NativeRustcVm.inRange_iff (show (stackBelow st17.data verifyStack).toNat +
        verifyStack ≤ 2 ^ 64 by rw [hsbV, hV]; omega)).mp hq
      rw [hsbV, hV] at hq'
      exact ⟨Or.inl (by unfold InStack; omega), by omega⟩
  rw [show k + NativeRustcVmArm.Vm.LeanvmVerify.b17Offset + b17.length = k + NativeRustcVmArm.Vm.LeanvmVerify.b18Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b17_next]] at hpc18
  -- `b18` and the epilogue.
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b18Offset hp b18_in_code (by simp [b18])) run_b18 (Env.wf_nil _) hpc18
    (match_nil _) fun st19 hm19 hpc19 ↦ ?_
  have hk19 := none_keeps b18 (by simp)
  rw [after_eq run_b18] at hk19
  have hB19 := bodyNo hB18 hs128 (match_nil _) hm19 (Env.wf_nil _) rfl hk19.1 hk19.2
  have hd19 : st19.data.dmem = st18.data.dmem := hm19.dmem_eq (Env.wf_nil _) hk19.2
  have hX8 : st19.data.regs.X8 = (if NativeVm.Model.verify bytecode.toArray pub (streamW r.1)
      (openingsW r.2) then 1 else 0) := by
    apply UInt64.toBitVec_inj.mp
    show (st19.data.regs.getXReg .X8).toBitVec = _
    rw [hm19.regs .X8 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [show st18.data.regs.getXReg .X0 = _ from hv]
    exact trunc_okWord _
  simp only [PcOk] at hpc19
  rw [lbl_2 hp] at hpc19
  exact Eventually.mono (exit2 hp hs128 hal16 hpc19 hB19
      (by rw [hd19]; exact Mapped.kept hFm0 hB18.kept))
    fun st' h ↦ ⟨h.1, h.2.1.trans hX8, h.2.2⟩

end

end NativeRustcVmArm.Top.Leanvm
