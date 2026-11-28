module

public import NativeRustcVmX64.KeccakGkr.SlotWeights.Zero

/-!
# `slot_weights`: a segment's products (x86-64)

At `NativeRustcVmX64.Vm.SlotWeights.label_7` (`b9`) segment `s` starts: its scale (the segment kernel's element `s`) in
R13, RBP, the row base `25 (first + s)` in R14, the bit counter `j` in R15 and its byte offset in
RBX, `s` saved at `32` (`seg_start`, to `Inner` at `j = 0`). Then for each bit `j` (`inner_step`):
`b12` computes the row `25 (first + s) + j / 64` (at most `49`: never past the rows), `b13`
loads the weight `j` and calls `EW::mul`, `b14` stores the product at the row's element `j % 64`
(`p1`, `p2`), `b11` counts. After the last bit, `b8` steps to the next segment or out
(`seg_end`).
-/

namespace NativeRustcVmX64.KeccakGkr.SlotWeights

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.SlotWeights
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off inRange_iff' not_inRange_of_apart
  Mapped.keeps bytesAt_congr inRange_off_self inRange_off_iff)
open NativeRustcVm.KeccakGkr (rowsFlat rowsBytes weightsBytes WeightsAt)

@[expose] public section

/-- The segment's scale. -/
abbrev scale (m0 : MachineData) (c : KeccakClaimW) (s : Nat) : EW :=
  (segK (reg m0 .rdi).toNat c).getD s 0

/-- The flat index of bit `j` of segment `s`. -/
abbrev flat (m0 : MachineData) (s j : Nat) : Nat := 1600 * ((reg m0 .r8).toNat + s) + j

/-- **The bit loop's head** at bit `j` of segment `s`. -/
structure Inner (m0 : MachineData) (c : KeccakClaimW) (s j : Nat) (st : MachineData) : Prop where
  ctx : Ctx m0 c st
  s_lt : s < (reg m0 .r9).toNat
  j_lt : j < 1600
  segw : NativeRustcVm.WordAt st.dmem (off (fbA m0) 32) (UInt64.ofNat s)
  r13 : reg st .r13 = (scale m0 c s).c0.toBitVec
  rbp : reg st .rbp = (scale m0 c s).c1.toBitVec
  r14 : reg st .r14 = BitVec.ofNat 64 (25 * ((reg m0 .r8).toNat + s))
  r15 : reg st .r15 = BitVec.ofNat 64 j
  rbx : reg st .rbx = BitVec.ofNat 64 (16 * j)
  rows : ElemsAt st.dmem (rowsA m0) (prog (reg m0 .rdi).toNat c (reg m0 .r8).toNat (flat m0 s j))
    4096

/-- **A segment done**, at `b8`. -/
structure SegEnd (m0 : MachineData) (c : KeccakClaimW) (s : Nat) (st : MachineData) : Prop where
  ctx : Ctx m0 c st
  s_lt : s < (reg m0 .r9).toNat
  segw : NativeRustcVm.WordAt st.dmem (off (fbA m0) 32) (UInt64.ofNat s)
  rows : ElemsAt st.dmem (rowsA m0)
    (prog (reg m0 .rdi).toNat c (reg m0 .r8).toNat (1600 * ((reg m0 .r8).toNat + (s + 1)))) 4096

end

public section

variable {c : KeccakClaimW} {m0 : MachineData}

/-- **The context kept** by a step that keeps the frame and changes memory only in `Out`, off the
locals. -/
theorem Ctx.step {d d' : MachineData} (hc : Ctx m0 c d) (hf : Frame m0 160 slots 8 d')
    {R : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d.dmem d'.dmem R)
    (hR : ∀ q, R q → Out m0 q)
    (hL : ∀ j, (8 ≤ j ∧ j < 32) ∨ (40 ≤ j ∧ j < 80) → ¬ R (off (fbA m0) j)) : Ctx m0 c d' :=
  ⟨hf, fun q hq ↦ (hs q fun h ↦ hq (hR q h)).trans (hc.same q hq), hc.loc.keep hs hL⟩

theorem segK_two (h : PreOk m0 c) : 2 ≤ (segK (reg m0 .rdi).toNat c).size := by
  rw [segK, NativeVm.Math.Keccak.eqKernel_size, Array.size_extract, Nat.min_self]
  have := h.fit
  unfold SegmentsFit at this
  rcases (show c.point.size - ((reg m0 .rdi).toNat - 4) = 1 ∨
    c.point.size - ((reg m0 .rdi).toNat - 4) = 2 by omega) with e | e <;> rw [e] <;> decide

theorem flat_div {s j : Nat} (hj : j < 1600) :
    flat m0 s j / 1600 - (reg m0 .r8).toNat = s ∧ flat m0 s j % 1600 = j := by
  unfold flat; constructor <;> omega

variable [Host] {k : Nat}

/-- `b9`: segment `s`'s start. -/
theorem seg_start (hp : Placed code k) (h : PreOk m0 c) {s : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b9Offset)) (hI : SegHead m0 c s st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b12Offset) ∧ Inner m0 c s 0 s'.data)
      st := by
  have hs1 := hI.s_lt
  have hc2 := h.cnt2
  have hfnw := frame_noWrap h.st (F := 160) (by rw [stack_eq]; decide)
  have hwf := wf_body h hI.ctx.frame.kept (d := st.data) (vars := fun _ ↦ 0) (ret := 0)
  have hm : Match (frameEnv m0 st.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0) segS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hI.ctx.frame.rsp_eval, trivial⟩ trivial
      ⟨by
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
        rw [show (frameEnv m0 st.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0).regs .rcx = _ from hI.rcx,
          show shiftCount .W64 (BitVec.ofNat 64 4) = 4 by decide, BitVec.toNat_shiftLeft,
          toNat_ofNat_lt (by omega), Nat.shiftLeft_eq]
        show _ % 2 ^ 64 < 17
        omega, trivial⟩
      ⟨arg_alias, trivial⟩
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) exit_b9 hwf nofun hpc hm
    fun s' hm' hpc' ↦ ?_
  obtain ⟨hmid, hws, hw32, hr13, hrbp, hr14, hr15, hrbx⟩ := ok_b9
  have hf' : Frame m0 160 slots 8 s'.data := Frame.of_block hI.ctx.frame hwf hm' hmid slots_le
  have hso : NativeRustcVm.SameOutside st.data.dmem s'.data.dmem
      (NativeRustcVm.InRange (off (fbA m0) 32) 8) := by
    intro q hq
    refine hm'.get?_mem0 hwf fun hW ↦ hq ?_
    obtain ⟨j, -, hj, rfl⟩ := touch_of_written (lo := 32) (hi := 40) hwf (r := 0) rfl (by decide)
      (fun w hw ↦ ⟨(hws w hw).1, (hws w hw).2.1, (hws w hw).2.2⟩) hW
    rw [inRange_off_iff (by omega) (by omega)]
    omega
  have hctx : Ctx m0 c s'.data :=
    hI.ctx.step hf' hso (fun q hq ↦ frame_out h (off_in (hfnw.mono (by omega)) (by decide) hq))
      (fun j hj hq ↦ by rw [inRange_off_iff (by omega) (by omega)] at hq; omega)
  have hsc : ((Sym.reg .rcx).bin .shl .W64 (.lit 4) |>.eval
      (frameEnv m0 st.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0)).toNat = 16 * s := by
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    rw [show (frameEnv m0 st.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0).regs .rcx = _ from hI.rcx,
      show shiftCount .W64 (BitVec.ofNat 64 4) = 4 by decide, BitVec.toNat_shiftLeft,
      toNat_ofNat_lt (by omega), Nat.shiftLeft_eq]
    show _ % 2 ^ 64 = _
    omega
  have hseg := hI.ctx.loc.seg s (by omega)
  have hsg := NativeRustcVm.ewAt_iff.mp hseg
  have hl0 : (frameEnv m0 st.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0).load 0 (48 + 16 * s) 8 =
      (scale m0 c s).c0.toBitVec := load_of_wordAt hsg.1
  have hl1 : (frameEnv m0 st.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0).load 0 (56 + 16 * s) 8 =
      (scale m0 c s).c1.toBitVec := load_of_wordAt (by
        have := hsg.2
        rwa [NativeRustcVm.Transcript.off_add, show 48 + 16 * s + 8 = 56 + 16 * s by omega] at this)
  have hfirst : (frameEnv m0 st.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0).load 0 16 8 =
      BitVec.ofNat 64 (reg m0 .r8).toNat := by
    rw [load_of_wordAt hI.ctx.loc.first]; simp
  simp only [PcOk] at hpc'
  refine .done _ ⟨hpc'.trans (label_of_infix hp b12_in_code rfl),
    ⟨hctx, hs1, by decide, ?_, ?_, ?_, ?_, hm'.regs .r15 _ hr15, ?_, ?_⟩⟩
  · have := wordAt_write hm' (r := 0) (o := 32) rfl (by decide) hw32
    rwa [show UInt64.ofBitVec ((Sym.reg .rcx).eval
      (frameEnv m0 st.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0)) = UInt64.ofNat s from by
        show UInt64.ofBitVec (reg st.data .rcx) = _; rw [hI.rcx]; rfl] at this
  · rw [show reg s'.data .r13 = _ from hm'.regs .r13 _ hr13, Sym.eval, hsc, hl0]
  · rw [show reg s'.data .rbp = _ from hm'.regs .rbp _ hrbp, Sym.eval, hsc, hl1]
  · apply BitVec.eq_of_toNat_eq
    rw [show reg s'.data .r14 = _ from hm'.regs .r14 _ hr14,
      r14S_eval _ (s := s) (f := (reg m0 .r8).toNat)
        (by rw [show (frameEnv m0 st.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0).regs .rcx = _ from hI.rcx,
          toNat_ofNat_lt (by omega)])
        (by rw [hfirst, toNat_ofNat_lt (by omega)]) (by omega),
      toNat_ofNat_lt (by omega)]
    omega
  · exact hm'.regs .rbx _ hrbx
  · rw [show flat m0 s 0 = 1600 * ((reg m0 .r8).toNat + s) by simp [flat]]
    exact hI.rows.keep hso (fun q hq hq' ↦ rows_frame_disj h hq
      (off_in hfnw (by decide) hq')) h.rows.2

end

end NativeRustcVmX64.KeccakGkr.SlotWeights
