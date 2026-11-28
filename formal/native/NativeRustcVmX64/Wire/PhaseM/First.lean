module

public import NativeRustcVmX64.Wire.PhaseM.Reads
public import NativeRustcVmX64.Code.Vm.ReaderLe.Names

/-!
# `phase_m`: the prologue and the query count (x86-64)

`first_run`: the prologue (`b0`, `out` kept at the frame's byte `48`), `Reader::le` for the query
count, its tag and `count ≤ 256` (`b1`, the count at the frame's byte `40`), `8 count` (`b2`), to
the queries' loop (`b3`, `AtQ … 0`), or with no query past it (`At7`), or to `None`.
-/

namespace NativeRustcVmX64.Wire.PhaseM

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeRustcVmX64.Vm.PhaseM
open NativeRustcVmX64.Transcript (Frame frameEnv frame_wf frame_mapped frame_noWrap Frame.of_block
  Frame.of_prologue Frame.entry after after_eq sameOutside_low MidOk match_rsp eval_ptr0
  wordAt_write load_ofMachine)
open NativeRustcVm.Transcript (off off_zero off_off off_add toNat_off Mapped.keeps)
open NativeRustcVmX64.Wire.Decode (eqv_eval)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} [Host] {k : Nat}

/-- **From the entry**: the prologue and the query count. -/
theorem first_run (hp : Placed code k) (G : Geo m0 bp B.length)
    (hle : Spec (Labels.label NativeRustcVmX64.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost)
    (hR0 : ReaderAt m0.dmem (RD m0) bp B c) :
    Eventually (step1 Host.exe) (fun st ↦ Post m0 st ∨
      (∃ count, AtQ m0 bp B c k count 0 st) ∨ ∃ count qs c2, At7 m0 bp B c k count qs c2 st)
      ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b0Offset)⟩ := by
  have hst : StackOk m0 1216 := G.st
  have hsp := G.sp
  have htop := G.top
  have hrn := G.rNw
  have hsR := G.sR
  have hsB := G.sB
  have hS := stackBelow_toNat (m := m0) (n := 160) (by omega)
  -- `b0`: the prologue.
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 160) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b0Offset + b0.length)).toBitVec)
    ⟨frame_mapped hst (by omega), frame_noWrap hst (by omega)⟩ (by simp)
    (List.pairwise_singleton _ _)
  have hm0 : Match (frameEnv m0 m0 160 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b0Offset + b0.length)).toBitVec)
      entryS m0 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 (fun _ _ ↦ rfl) hm0
    fun s1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hw48, hws, hrsi, hrdi, hr12, hr14⟩ := ok_b0
  have hf1 : Frame m0 160 slots 0 s1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le slots_cs
  have hs1 : NativeRustcVm.SameOutside m0.dmem s1.data.dmem
      (fun q ↦ SP0 m0 - 160 ≤ q.toNat ∧ q.toNat < SP0 m0) :=
    (sameOutside_low hwf0 hm1 (r := 0) rfl (hi := 160) (by omega) fun w hw ↦
      ⟨(hws w hw).1, by rcases (hws w hw).2 with h | h | h <;> omega⟩).mono fun q h ↦ by
      have := iv_of_inRange (by rw [hS]; omega) h
      rw [hS] at this; omega
  have hR1 : ReaderAt s1.data.dmem (RD m0) bp B c :=
    reader_keep hR0 hs1 (fun q hq ↦ by omega) (fun q hq ↦ by omega)
  have hout1 : FW m0 s1.data.dmem 48 (UInt64.ofBitVec (OUT m0)) := by
    have := wordAt_write hm1 (r := 0) (o := 48) (b := stackBelow m0 160) (sz := 168) rfl
      (by omega) hw48
    simp only [Sym.eval, Env.ofMachine_regs] at this
    exact this
  have hrdi1 : reg s1.data .rdi = RD m0 := by
    rw [show reg s1.data .rdi = _ from hm1.regs .rdi _ hrdi]; rfl
  have hrsi1 : (reg s1.data .rsi).toNat = 4 := by
    rw [show reg s1.data .rsi = _ from hm1.regs .rsi _ hrsi]; rfl
  refine le4_call hle hst (F := 160) (by omega) (lo := 112) (by omega) slots_lo hf1 hR1 hrdi1
    hrsi1 (by omega) (by omega) hpc1 fun m2 hf2 hcs2 hso2 hr2 ↦ ?_
  have h16 : (off (RD m0) 16).toNat = (RD m0).toNat + 16 := toNat_off (by omega)
  have hso2' : NativeRustcVm.SameOutside s1.data.dmem m2.dmem
      (fun q ↦ (RD m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (RD m0).toNat + 24) := hso2.mono fun q h ↦ by
    have := iv_of_inRange (by rw [h16]; omega) h
    rw [h16] at this; omega
  have hb2 : Bod m0 8 m2 := ⟨hf2, (hs1.trans hso2').mono fun q hq ↦ by
      rcases hq with hq | hq
      · exact .inl (by omega)
      · exact .inr (.inl hq),
    (hcs2 .r12 rfl).trans (hm1.regs .r12 _ hr12), (hcs2 .r14 rfl).trans (hm1.regs .r14 _ hr14),
    hout1.keep G (by omega) hso2' fun q hq ↦ by omega⟩
  -- `b1`: the tag, `count ≤ 256`, the count to the frame's `40`.
  obtain ⟨hmid1, hmem1, hw40, hk1⟩ := ok_b1
  refine wblk hp G b1_in_code (by simp [b1]) exit_b1 hmid1
    (fun w hw ↦ by rw [hmem1] at hw; simp only [List.mem_singleton] at hw; subst hw; decide)
    (hk1 .r12 (by simp)) (hk1 .r14 (by simp)) (st := ⟨m2, _⟩) rfl hb2
    fun s3 hb3 hs3 hkeep3 hm3 hpc3 ↦ ?_
  simp only [PcOk] at hpc3
  have hR2 : ∀ c', ReaderAt m2.dmem (RD m0) bp B c' → ReaderAt s3.data.dmem (RD m0) bp B c' :=
    fun c' h ↦ reader_keep h hs3 (fun q hq ↦ by omega) (fun q hq ↦ by omega)
  have ea : (frameEnv m0 m2 160 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b1Offset + b1.length)).toBitVec).regs
      .rax = reg m2 .rax := rfl
  have ed : (frameEnv m0 m2 160 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b1Offset + b1.length)).toBitVec).regs
      .rdx = reg m2 .rdx := rfl
  rcases read4_cases hr2 with ⟨hn, h0⟩ | ⟨count, hv, h0, hdx, hcl, hR4⟩
  · -- No count: `None`.
    rw [c1_eval _ (by rw [ea]; exact .inl h0), ea, h0] at hpc3
    simp only [show decide ((0 : BitVec 64) = 1) = false by decide, Bool.and_false,
      Bool.not_false, ↓reduceIte] at hpc3
    rw [hp.label NativeRustcVmX64.Vm.PhaseM.label_23_at] at hpc3
    exact Eventually.mono (none_run hp G hR0 hpc3 hb3 (by rw [phaseM_eq, hn])) fun _ h ↦ .inl h
  rw [c1_eval _ (by rw [ea]; exact .inr h0), ea, h0, ed, hdx] at hpc3
  by_cases hbig : 257 ≤ count
  · simp only [show ¬ count < 257 by omega, decide_false, Bool.false_and, Bool.not_false,
      ↓reduceIte] at hpc3
    rw [hp.label NativeRustcVmX64.Vm.PhaseM.label_23_at] at hpc3
    refine Eventually.mono (none_run hp G hR0 hpc3 hb3 ?_) fun _ h ↦ .inl h
    rw [phaseM_eq, hv]
    simp only [show wireMaxQueries < count by unfold wireMaxQueries; omega, ↓reduceIte]
  simp only [show count < 257 by omega, decide_true, Bool.and_self, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte] at hpc3
  have hf40 : FW m0 s3.data.dmem 40 count.toUInt64 := by
    have := wordAt_write hm3 (r := 0) (o := 40) rfl (by omega) hw40
    simp only [Sym.eval, Env.ofMachine_regs] at this
    rw [show m2.regs.get64 .rdx = reg m2 .rdx from rfl, toNat_reg_eq hdx] at this
    exact this
  have hR3 := hR2 _ hR4
  -- `b2`: `8 count`, no query?
  obtain ⟨hok2, h13_2, hk2⟩ := ok_b2
  refine fblk hp G b2_in_code (by simp [b2]) exit_b2 nofun hok2 (hk2 .r12 (by simp))
    (hk2 .r14 (by simp)) (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b1_next)) hb3
    fun s4 hb4 hd4 hm4 hpc4 ↦ ?_
  have hl40 : ((frameEnv m0 s3.data 160 []).load 0 40 8).toNat = count := by
    rw [load_ofMachine (o := 40) rfl hf40, UInt64.toNat_toBitVec, toNat_toUInt64 (by omega)]
  have h13 : (reg s4.data .r13).toNat = 8 * count := by
    rw [show reg s4.data .r13 = _ from hm4.regs .r13 _ h13_2]
    exact eight_eval _ hl40 (by omega)
  have hf40' : FW m0 s4.data.dmem 40 count.toUInt64 := by rw [hd4]; exact hf40
  have hR4' : ReaderAt s4.data.dmem (RD m0) bp B (c + 4) := by rw [hd4]; exact hR3
  simp only [PcOk] at hpc4
  have hz : (SBool.cmp .eq .W64 (.bin .and .W64 (.load 0 40 8) (.load 0 40 8)) (.lit 0)).eval
      (frameEnv m0 s3.data 160 []) = decide (count = 0) := by
    show CmpOp.apply .eq .W64 (BinOp.apply .and .W64 ((frameEnv m0 s3.data 160 []).load 0 40 8)
      ((frameEnv m0 s3.data 160 []).load 0 40 8)) (BitVec.ofNat 64 0) = _
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.and_self]
    rw [eqv_eval, hl40]
    rfl
  rw [hz] at hpc4
  by_cases hc0 : count = 0
  · -- No query: past the loop.
    subst hc0
    simp only [decide_true, ↓reduceIte] at hpc4
    exact .done _ (.inr (.inr ⟨0, [], c + 4, ⟨hpc4.trans (hp.label NativeRustcVmX64.Vm.PhaseM.label_5_at), hb4, hv,
      by omega, rfl, hf40', h13, NativeRustcVm.wordsAt_nil _ _, hR4'⟩⟩))
  simp only [hc0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc4
  -- `b3`: the loop's index.
  obtain ⟨hok3, h15_3, hk3⟩ := ok_b3
  refine fblk hp G b3_in_code (by simp [b3]) exit_b3 nofun hok3 (hk3 .r12 (by simp))
    (hk3 .r14 (by simp)) (hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b2_next)) hb4
    fun s5 hb5 hd5 hm5 hpc5 ↦ ?_
  refine .done _ (.inr (.inl ⟨count, ⟨hpc5.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b3_next), hb5, hv,
    by omega, by omega, by rw [hd5]; exact hf40', ?_, ?_, [], rfl, NativeRustcVm.wordsAt_nil _ _,
    by rw [hd5]; simpa using hR4'⟩⟩))
  · rw [show reg s5.data .r13 = _ from hm5.regs .r13 _ (hk3 .r13 (by simp))]; exact h13
  · rw [show reg s5.data .r15 = _ from hm5.regs .r15 _ h15_3]; rfl

end

end NativeRustcVmX64.Wire.PhaseM
