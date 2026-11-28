module

public import NativeRustcVmX64.Top.Verify.StageB
public import NativeRustcVmX64.Code.Vm.Verify.Names

/-!
# `verify` after the walk (x86-64)

`stageC`: from `SB`, `b2` returns `0` (`b8`, `b9`) when the walk failed; else `b3`, `b4` compare
the cursor with the stream's count (the area's first word; the area is never empty, so `b7` is not
reached) and return `0` when they differ; else `b5` calls `Decoded::phase_count` and `b6` sets AL
to whether the phase equals it, `b9` returns: AL is `Model.verify`'s verdict.
-/

namespace NativeRustcVmX64.Top.Verify

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Verify NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeRustcVmX64.Top NativeVm.Model
open NativeRustcVm.Top (workAreaBytes)

public section

/-- Two counts below `2 ^ 64` compared as words. -/
theorem toBV_beq {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (x.toUInt64.toBitVec == y.toUInt64.toBitVec) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← BitVec.toNat_inj]
  simp only [UInt64.toNat_toBitVec, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hy]

/-- The verdict on the walk's run. -/
theorem verify_eq (m0 : MachineData) (stream : Array EW) (openings : Array (Array OpeningW)) :
    NativeVm.Model.verify (bcOf m0).toArray (pubOf m0) stream openings =
      match run m0 stream openings with
      | some ((), s) => s.cursor == s.stream.size && s.phase == s.openings.size
      | none => false := rfl

variable [Host] {k : Nat}

theorem lbl_5 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.Verify.label_5 = Host.addrOf (k + NativeRustcVmX64.Vm.Verify.b8Offset) :=
  hp.label NativeRustcVmX64.Vm.Verify.label_5_at
theorem lbl_6 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.Verify.label_6 = Host.addrOf (k + NativeRustcVmX64.Vm.Verify.b9Offset) :=
  hp.label NativeRustcVmX64.Vm.Verify.label_6_at

/-- **The epilogue** (`b9`), AL kept. -/
theorem exit9 (hp : Placed code k) {m0 : MachineData} (hst : StackOk m0 verifyStack)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Verify.b9Offset)) (hf : Frame m0 816 slots 8 st.data)
    {b : Bool} (hok : OkAl st.data b) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      rspOf st'.data = rspOf m0 + 8#64 ∧ OkAl st'.data b ∧ st'.data.dmem = st.data.dmem ∧
      Saved m0 st'.data) st := by
  have hfnw := frame_noWrap (F := 816) hst (by decide)
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 816) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.kept, hfnw⟩ (by simp)
    (List.pairwise_singleton _ _)
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) run_b9 hwf nofun hpc
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st' hm hpc' ↦ ?_
  obtain ⟨hepi, hmem, hrax⟩ := after_eq run_b9 ▸ ok_b9
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hf hwf hm hepi
  simp only [PcOk] at hpc'
  refine .done _ ⟨by rw [hpc']; exact hf.load_ret hst (by decide), hrsp, ?_,
    hm.dmem_eq hwf hmem, hsv⟩
  unfold OkAl boolRet at hok ⊢
  rw [show reg st'.data .rax = reg st.data .rax from hm.regs .rax _ hrax]
  exact hok

/-- **`0`** (`b8`), then the epilogue. -/
theorem exit0 (hp : Placed code k) {m0 : MachineData} (hst : StackOk m0 verifyStack)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Verify.b8Offset)) (hf : Frame m0 816 slots 8 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      rspOf st'.data = rspOf m0 + 8#64 ∧ OkAl st'.data false ∧ st'.data.dmem = st.data.dmem ∧
      Saved m0 st'.data) st := by
  have hfnw := frame_noWrap (F := 816) hst (by decide)
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 816) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.kept, hfnw⟩ (by simp)
    (List.pairwise_singleton _ _)
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8 hwf nofun hpc
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st' hm hpc' ↦ ?_
  obtain ⟨hmid, hmem, hrax⟩ := after_eq run_b8 ▸ ok_b8
  have hf' : Frame m0 816 slots 8 st'.data := Frame.of_block hf hwf hm hmid slots_le
  simp only [PcOk] at hpc'
  refine Eventually.mono (exit9 hp hst (hpc'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Verify.b8_next)) hf' ?_)
    fun s ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, h3, h4.trans (hm.dmem_eq hwf hmem), h5⟩
  unfold OkAl boolRet
  rw [show reg st'.data .rax = BitVec.ofNat 64 0 from hm.regs .rax _ hrax]
  rfl

end

end NativeRustcVmX64.Top.Verify
