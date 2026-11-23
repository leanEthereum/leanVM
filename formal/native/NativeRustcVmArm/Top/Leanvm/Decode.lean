module

public import NativeRustcVmArm.Top.Leanvm.DecPre

/-!
# `leanvm_verify`: the decoder

From `C1` at `.LLeanvmVerify_10`, `b12` (a nonempty wire) or `b15` (an empty one, the dangling
pointer `1`) stores the public input in the frame and calls `decode`; when it refuses the bytes,
`b1` and the epilogue `b2` return `0` (`failExit`), else the decoded proof is in the decoded area
at `.LLeanvmVerify_14` (`C2`): `stage2`.
-/

namespace NativeRustcVmArm.Top.Leanvm

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.LeanvmVerify NativeVm
open NativeRustcVm (WordAt WordsAt Region)
open NativeRustcVm.Top (workAreaBytes entryRegions ApartFrom Aligned)
open NativeRustcVm.Wire (streamW openingsW)
open NativeVm.Wire (decodeM PhaseOut)
open LeanVM.Parameters (E)
open NativeVm.Transcript (wd ctxEnd)

/-- What the verifier may change: its stack, the decoded and the working areas. -/
@[expose] public def R2 (a : NativeVm.Entry.Areas) (L : Nat) (m0 : MachineData) (q : BitVec 64) : Prop :=
  InStack m0 leanvmVerifyStack q ∨ InRange a.decoded.toBitVec (8 * decodedWords L) q ∨
    InRange a.work.toBitVec workAreaBytes q

/-- After `decode`: the frame's body, the public input in the frame, the decoded proof `r` in the
decoded area, the registers the rest uses. -/
public structure C2 (a : NativeVm.Entry.Areas) (bytes : List UInt8) (bytecode : List UInt64)
    (pub : Vector UInt64 4) (m0 st : MachineData) (r : List E × List PhaseOut) : Prop where
  body : Body m0 128 slots (R2 a bytes.length m0) st
  pubAt : WordsAt st.dmem (frameOf m0 + BitVec.ofNat 64 8) pub.toList
  dec : NativeRustcVm.Transcript.DecodedAt st.dmem ⟨a.decoded.toBitVec, decodedWords bytes.length,
    bytes.length⟩ (streamW r.1) (openingsW r.2)
  x19 : st.regs.X19 = bytes.length.toUInt64
  x20 : st.regs.X20 = bytecode.length.toUInt64
  x21 : st.regs.X21 = (decodedWords bytes.length).toUInt64
  x22 : st.regs.X22 = a.work
  x23 : st.regs.X23 = a.decoded
  x24 : st.regs.X24 = a.bytecode

public section

/-- The frame as a block's region. -/
theorem frameEnv [Labels] {m0 st : MachineData} {R : BitVec 64 → Prop}
    (hB : Body m0 128 slots R st) (hs : 128 ≤ m0.regs.SP.toBitVec.toNat)
    (hal : m0.regs.SP.toBitVec.toNat % 16 = 0) (hFm : Mapped st.dmem (frameOf m0) 128) :
    (Env.ofMachine st [(frameOf m0, 128)]).WF ∧
      Match (Env.ofMachine st [(frameOf m0, 128)]) frameS st := by
  have hsl := m0.regs.SP.toBitVec.isLt
  have hF : (frameOf m0).toNat = m0.regs.SP.toBitVec.toNat - 128 := toNat_subAddr hs
  exact ⟨Env.wf_of ⟨⟨hFm, show (frameOf m0).toNat + 128 ≤ 2 ^ 64 by omega⟩, trivial⟩
    (List.pairwise_singleton _ _), match_ofMachine
      ⟨rfl, fun _ ↦ show (frameOf m0).toNat % 16 = 0 by omega, trivial⟩
      (show st.regs.SP.toBitVec = frameOf m0 + BitVec.ofInt 64 0 by rw [hB.sp]; simp [frameOf])
      trivial trivial trivial trivial⟩

/-- The public input's words a block stores in the frame. -/
theorem pubAt_of [Labels] {m0 st : MachineData} {S : SState} {pub : Vector UInt64 4}
    (hw : ∀ p ∈ pubWords, ∀ i < 8, findWrite 0 (p.1 + i) S.mem = some (.reg p.2, i))
    (h13 : st.regs.X13 = pub[0]) (h12 : st.regs.X12 = pub[1]) (h11 : st.regs.X11 = pub[2])
    (h10 : st.regs.X10 = pub[3]) {st' : MachineData}
    (hm' : Match (Env.ofMachine st [(frameOf m0, 128)]) S st') :
    WordsAt st'.dmem (frameOf m0 + BitVec.ofNat 64 8) pub.toList := by
  have one : ∀ (o : Nat) (r : XReg) (w : UInt64), (o, r) ∈ pubWords → st.regs.getXReg r = w →
      WordAt st'.dmem (frameOf m0 + BitVec.ofNat 64 o) w := fun o r w hp hr ↦ by
    have hle : o + 8 ≤ 128 := by
      simp only [pubWords, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
      omega
    unfold WordAt
    rw [wordBytes_byteOf, ← hr]
    exact hm'.bytesAt_write (r := 0) rfl hle (hw _ hp)
  refine NativeRustcVm.wordsAt_iff.mpr fun i hi ↦ ?_
  have hi4 : i < 4 := by simpa using hi
  rw [NativeRustcVm.addr_add_add]
  have e : ∀ j (hj : j < 4), pub.toList[j]'(by simpa using hj) = pub[j] := fun j hj ↦ by simp
  rw [e i hi4]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
  · exact one 8 .X13 _ (by simp [pubWords]) h13
  · exact one 16 .X12 _ (by simp [pubWords]) h12
  · exact one 24 .X11 _ (by simp [pubWords]) h11
  · exact one 32 .X10 _ (by simp [pubWords]) h10

variable [Host] {k : Nat}

/-- **The epilogue** at `.LLeanvmVerify_2`: X0 is X8. -/
theorem exit2 (hp : Placed code k) {m0 : MachineData} {R : BitVec 64 → Prop}
    (hs : 128 ≤ m0.regs.SP.toBitVec.toNat) (hal : m0.regs.SP.toBitVec.toNat % 16 = 0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b2Offset)) (hB : Body m0 128 slots R st.data)
    (hFm : Mapped st.data.dmem (frameOf m0) 128) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      st'.data.regs.X0 = st.data.regs.X8 ∧ SameOutside m0.dmem st'.data.dmem R ∧
      Saved m0 st'.data) st := by
  obtain ⟨hwf, hm⟩ := frameEnv hB hs hal hFm
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b2Offset hp b2_in_code (by simp [b2])) run_b2 hwf hpc hm fun st' hm' hpc' ↦ ?_
  have hr := b2_restores
  rw [after_eq run_b2] at hr
  obtain ⟨hsv, hret, hdm⟩ := hB.ret hm' hwf (by simp [slots]) hr.1 hr.2
  exact Eventually.done _ ⟨hpc'.trans hret, UInt64.toBitVec_inj.mp (hm'.regs .X0 _ rfl),
    fun q hq ↦ by rw [hdm]; exact hB.same q hq, hsv⟩

/-- **A refusal** at `.LLeanvmVerify_1`: `0`. -/
theorem failExit (hp : Placed code k) {m0 : MachineData} {R : BitVec 64 → Prop}
    (hs : 128 ≤ m0.regs.SP.toBitVec.toNat) (hal : m0.regs.SP.toBitVec.toNat % 16 = 0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b1Offset)) (hB : Body m0 128 slots R st.data)
    (hFm : Mapped st.data.dmem (frameOf m0) 128) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧ st'.data.regs.X0 = 0 ∧
      SameOutside m0.dmem st'.data.dmem R ∧ Saved m0 st'.data) st := by
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b1Offset hp b1_in_code (by simp [b1])) run_b1 (Env.wf_nil _) hpc (match_nil _)
    fun st1 hm1 hpc1 ↦ ?_
  have hk := none_keeps b1 (by simp)
  rw [after_eq run_b1] at hk
  have hB1 := bodyNo hB hs (match_nil _) hm1 (Env.wf_nil _) rfl hk.1 hk.2
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq (Env.wf_nil _) hk.2
  have hX8 : st1.data.regs.X8 = 0 := UInt64.toBitVec_inj.mp (hm1.regs .X8 _ rfl)
  simp only [PcOk, show k + NativeRustcVmArm.Vm.LeanvmVerify.b1Offset + b1.length = k + NativeRustcVmArm.Vm.LeanvmVerify.b2Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b1_next]] at hpc1
  exact Eventually.mono (exit2 hp hs hal hpc1 hB1 (by rw [hd1]; exact hFm))
    fun st' h ↦ ⟨h.1, h.2.1.trans hX8, h.2.2⟩

end

end NativeRustcVmArm.Top.Leanvm
