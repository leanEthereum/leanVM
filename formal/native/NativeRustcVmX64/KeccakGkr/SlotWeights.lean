module

public import NativeRustcVmX64.KeccakGkr.SlotWeights.Store
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EqKernel.Names
public import NativeRustcVmX64.Code.Vm.SlotWeights.Names

/-!
# `slot_weights` on x86-64

**`slotWeights_spec`**: the prologue and `eq_kernel` (`prologue`), the rows zeroed (`zero_loop`),
then for each segment `s < count` (`seg_loop`) its start (`seg_start`), its 1600 products
(`bit_loop`: `bit_mul`, `bit_store`) and its end (`seg_end`, `b8`); the epilogue (`b15`) returns
AL = `1`, `eq_kernel`'s result's low bit.
-/

namespace NativeRustcVmX64.KeccakGkr.SlotWeights

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.SlotWeights
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off inRange_iff' not_inRange_of_apart
  Mapped.keeps bytesAt_congr inRange_off_self inRange_off_iff)
open NativeRustcVm.KeccakGkr (rowsFlat rowsBytes weightsBytes WeightsAt)

@[expose] public section

/-- **The segments done**, at the epilogue. -/
structure Done (m0 : MachineData) (c : KeccakClaimW) (st : MachineData) : Prop where
  ctx : Ctx m0 c st
  rows : ElemsAt st.dmem (rowsA m0)
    (prog (reg m0 .rdi).toNat c (reg m0 .r8).toNat
      (1600 * ((reg m0 .r8).toNat + (reg m0 .r9).toNat))) 4096

end

public section

variable {c : KeccakClaimW} {m0 : MachineData} [Host] {k : Nat}

/-- **A segment's bits**: from bit `0` to the segment's end. -/
theorem bit_loop (hp : Placed code k) (h : PreOk m0 c)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {s : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b12Offset)) (hI : Inner m0 c s 0 st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b8Offset) ∧ SegEnd m0 c s s'.data)
      st :=
  loop (fun n st ↦ ∃ j, n = 1600 - j ∧ j < 1600 ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b12Offset) ∧
      Inner m0 c s j st.data)
    (fun _ st ⟨j, hn, hj, hpc, hI⟩ ↦ (bit_mul hp h hmul hpc hI).bind fun s1 ⟨hpc1, hI1⟩ ↦
      (bit_store hp h hpc1 hI1).mono fun s' h' ↦ by
        rcases h' with ⟨hlt, hpc', hI'⟩ | ⟨-, hpc', hE⟩
        · exact Or.inr ⟨1600 - (j + 1), by omega, j + 1, rfl, hlt, hpc', hI'⟩
        · exact Or.inl ⟨hpc', hE⟩)
    ⟨0, rfl, by decide, hpc, hI⟩

/-- `b8`: the next segment, or the segments done. -/
theorem seg_end (hp : Placed code k) (h : PreOk m0 c) {s : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b8Offset)) (hI : SegEnd m0 c s st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ (s + 1 < (reg m0 .r9).toNat ∧
      s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b9Offset) ∧ SegHead m0 c (s + 1) s'.data) ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b15Offset) ∧ Done m0 c s'.data)) st := by
  have hs := hI.s_lt
  have hc2 := h.cnt2
  have hwf := wf_body h hI.ctx.frame.kept (d := st.data) (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) exit_b8 hwf nofun hpc
    (match_callS hI.ctx.frame) fun s' hm' hpc' ↦ ?_
  obtain ⟨hmid, hmem, hrcx⟩ := ok_b8
  have hd : s'.data.dmem = st.data.dmem := hm'.dmem_eq hwf hmem
  have hctx := hI.ctx.of_block hwf hm' hmid hmem
  have h32 : (frameEnv m0 st.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0).load 0 32 8 =
      BitVec.ofNat 64 s := by
    rw [load_of_wordAt hI.segw]; rfl
  have h24 : (frameEnv m0 st.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0).load 0 24 8 =
      BitVec.ofNat 64 (reg m0 .r9).toNat := by
    rw [load_of_wordAt hI.ctx.loc.count]; simp
  simp only [PcOk, SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64] at hpc'
  rw [h32, h24, add_ofNat, beq_ofNat (by omega) (by omega)] at hpc'
  by_cases hlast : s + 1 = (reg m0 .r9).toNat
  · rw [decide_eq_true hlast] at hpc'
    simp only [ite_true] at hpc'
    refine .done _ (Or.inr ⟨hpc'.trans (label_of_infix hp b15_in_code rfl), hctx, ?_⟩)
    rw [hd, ← hlast]; exact hI.rows
  · rw [decide_eq_false hlast] at hpc'
    simp only [Bool.false_eq_true, ite_false] at hpc'
    refine .done _ (Or.inl ⟨by omega, hpc'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SlotWeights.b8_next), hctx, by omega, ?_,
      by rw [hd]; exact hI.rows⟩)
    rw [show reg s'.data .rcx = _ from hm'.regs .rcx _ hrcx]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    rw [h32, add_ofNat]

/-- **The segments**: from segment `0`'s head to the epilogue. -/
theorem seg_loop (hp : Placed code k) (h : PreOk m0 c)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b9Offset)) (hI : SegHead m0 c 0 st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b15Offset) ∧ Done m0 c s'.data) st :=
  loop (fun n st ↦ ∃ s, n = (reg m0 .r9).toNat - s ∧ s < (reg m0 .r9).toNat ∧
      st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b9Offset) ∧ SegHead m0 c s st.data)
    (fun _ st ⟨s, hn, hs, hpc, hI⟩ ↦ (seg_start hp h hpc hI).bind fun s1 ⟨hpc1, hI1⟩ ↦
      (bit_loop hp h hmul hpc1 hI1).bind fun s2 ⟨hpc2, hI2⟩ ↦
        (seg_end hp h hpc2 hI2).mono fun s' h' ↦ by
          rcases h' with ⟨hlt, hpc', hI'⟩ | h'
          · exact Or.inr ⟨(reg m0 .r9).toNat - (s + 1), by omega, s + 1, rfl, hlt, hpc', hI'⟩
          · exact Or.inl h')
    ⟨0, rfl, hI.s_lt, hpc, hI⟩

/-- **`slot_weights` meets its contract**, given `eq_kernel`'s and `EW::mul`'s. -/
theorem slotWeights_spec (hp : Placed code k)
    (heq : Spec (Labels.label NativeRustcVmX64.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (c : KeccakClaimW) :
    Spec (Labels.label NativeRustcVmX64.Vm.SlotWeights.entryLabel) (SlotWeightsPre c) (SlotWeightsPost c) := by
  intro m0 hpre
  have h := preOk hpre
  unfold NativeRustcVmX64.Vm.SlotWeights.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.SlotWeights.entry_at]
  refine (prologue hp hpre heq).bind fun s1 ⟨hpc1, hI1⟩ ↦ ?_
  refine (zero_loop hp h hpc1 hI1).bind fun s2 ⟨hpc2, hI2⟩ ↦ ?_
  refine (seg_loop hp h hmul hpc2 hI2).bind fun s3 ⟨hpc3, hD⟩ ↦ ?_
  have hwf := wf_body h hD.ctx.frame.kept (d := s3.data) (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b15_in_code (by simp [b15]) hp) exit_b15 hwf nofun hpc3
    (match_callS hD.ctx.frame) fun s' hm' hpc' ↦ .done _ ?_
  obtain ⟨hepi, hmem, hrax⟩ := ok_b15
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hD.ctx.frame hwf hm' hepi
  have hd : s'.data.dmem = s3.data.dmem := hm'.dmem_eq hwf hmem
  have h8 : (frameEnv m0 s3.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0).load 0 8 8 = 1#64 := by
    rw [load_of_wordAt hD.ctx.loc.ok]; rfl
  simp only [PcOk] at hpc'
  refine ⟨by rw [hpc']; exact hD.ctx.frame.load_ret h.st (by rw [stack_eq]; decide), hrsp, ?_,
    ?_, ?_, hsv⟩
  · show (reg s'.data .rax).toNat % 256 = 1
    rw [show reg s'.data .rax = _ from hm'.regs .rax _ hrax]
    simp only [Sym.eval]
    rw [h8]
    rfl
  · rw [hd]
    exact rows_final h.cnt2 hD.rows
  · intro q hq
    rw [hd]
    refine hD.ctx.same q fun hO ↦ hq ?_
    rcases hO with hO | hO
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hO⟩
    · exact ⟨_, List.mem_cons_self, hO⟩

end

end NativeRustcVmX64.KeccakGkr.SlotWeights
