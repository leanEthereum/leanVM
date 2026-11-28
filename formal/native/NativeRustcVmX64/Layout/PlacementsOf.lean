module

public import NativeRustcVmX64.Layout.PlacementsOf.Turn3
public import NativeRustcVmX64.Code.Vm.Memset.Names
public import NativeRustcVmX64.Code.Vm.PlacementsOf.Names
public import NativeRustcVmX64.Code.Vm.StackOffsets.Names

/-!
# `placements_of` on x86-64

**`placementsOf_spec`**: rustc's `placements_of(kappas, placements)`, placed anywhere in the
program, meets `PlacementsOfPre`/`PlacementsOfPost` given `memset`'s and `stack_offsets`'
contracts. The prologue zeroes `block_cols` and `block_sizes` (`entry`); the first loop gathers the
stacked columns and their sizes (`loop1`); `stack_offsets` places them (`mid`); the second loop
copies their offsets into `offsets` (`loop2`, `to3`); the third writes every column's placement
(`loop3`, `turn3`); `b32` returns `Some(max(16, total_log))` (`finish`). Column by column the
placements are the model's (`NativeVm.Math.Layout.placementsOf_spec`, `plF`).
-/

namespace NativeRustcVmX64.Layout.PlacementsOf

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.PlacementsOf NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeRustcVmX64.Layout.BuildFrame
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout

public section

variable [Host] {k : Nat}

/-- **`b32` and the epilogue**: `Some(max(16, total_log))`, the placements the model's. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b32Offset)) (hI : I3 m0 158 st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧
      PlacementsOfPost m0 s.data) st := by
  set L := log2Ceil (sumF (κ m0) 0) with hL
  have hL64 : L < 2 ^ 64 := by
    have := hF.sumF_le' 0
    have : L ≤ sumF (κ m0) 0 := by
      rw [hL]; unfold log2Ceil bitLength
      split
      · omega
      · have := Nat.log2_le_self (sumF (κ m0) 0 - 1); omega
    omega
  obtain ⟨hok, hmem, h15, hdx⟩ := ok_b32
  refine step0 hF (b32_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b32 nofun hpc hI.b hok hmem
    fun st1 hm1 hpc1 hb1 hd1 ↦ ?_
  have hld : ((Sym.load 0 8 8).eval (frameEnv m0 st.data 5120 [] (fun _ ↦ 0) 0)).toNat = L := by
    show ((frameEnv m0 st.data 5120 [] (fun _ ↦ 0) 0).load 0 8 8).toNat = _
    rw [load_ofMachine (o := 8) rfl hI.tot, UInt64.toNat_toBitVec, toNat_toUInt64 hL64]
  have hrdx1 : (reg st1.data .rdx).toNat = max 16 L := by
    show (st1.data.regs.get64 .rdx).toNat = _
    rw [hm1.regs .rdx _ hdx]
    show (if (SBool.not (SBool.cmp .ult .W64 (.load 0 8 8) (.lit 17))).eval _ = true then
      (Sym.load 0 8 8).eval _ else BitVec.ofNat 64 16).toNat = _
    rw [SBool.eval, ult_eval, hld]
    by_cases h : L < 17
    · rw [decide_eq_true (show L < ((Sym.lit 17).eval (frameEnv m0 st.data 5120 []
        (fun _ ↦ 0) 0)).toNat from h)]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [lit_toNat (by decide)]; omega
    · rw [decide_eq_false (show ¬ L < ((Sym.lit 17).eval (frameEnv m0 st.data 5120 []
        (fun _ ↦ 0) 0)).toNat from h)]
      simp only [Bool.not_false, ↓reduceIte]
      rw [hld]; omega
  have hr15 : reg st1.data .r15 = 1#64 := hm1.regs .r15 _ h15
  obtain ⟨hepi, hmem31, hax31, hK31⟩ := ok_b31
  refine hb1.done hF.stack (by decide) ((infix_drop b31 1).trans b31_in_code (by simp [b31]) |>.trans
    hp.1 (by simp [b31])) exit_b31 (hpc1.trans (hp.label NativeRustcVmX64.Vm.PlacementsOf.label_26_at)) (match0 hb1) hepi hmem31
    fun st2 hm2 hpc2 hrsp2 hsv2 hd2 ↦ ⟨hpc2, hrsp2, ?_⟩
  have hsz : (natsOf m0 (reg m0 .rdi) columnCountW).size = 158 := by
    simp [natsOf, columnCountW, NativeRustcVm.wordsOf]
  obtain ⟨r2, r1s, r1⟩ := NativeVm.Math.Layout.placementsOf_spec _ hsz
  refine ⟨(hm2.regs .rax _ hax31).trans hr15, ?_, r1s, fun c hc ↦ ?_,
    fun q hq ↦ by rw [hd2, hd1]; exact hI.b.same q hq, hsv2⟩
  · rw [kreg hm2 hK31 (by simp), hrdx1, r2]; rfl
  · have hc' : c < 158 := by rw [r1s] at hc; exact hc
    have := r1 c hc'
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hc, Option.getD_some] at this
    rw [this, hd2, hd1]
    exact hI.pl c hc'

/-- **`placements_of` meets its contract.** -/
theorem placementsOf_spec (hp : Placed code k)
    (hms : Spec (label NativeRustcVmX64.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    (hso : Spec (label NativeRustcVmX64.Vm.StackOffsets.entryLabel) StackOffsetsPre StackOffsetsPost) :
    Spec (label NativeRustcVmX64.Vm.PlacementsOf.entryLabel) PlacementsOfPre PlacementsOfPost := by
  intro m0 hpre
  have hF := Facts.of_pre hpre
  refine Eventually.bind (entry hp hms hF) fun s1 ⟨hpc1, hI1⟩ ↦ ?_
  refine Eventually.bind (loop1 hp hF (by decide) hpc1 hI1) fun s2 ⟨hpc2, hI2⟩ ↦ ?_
  refine Eventually.bind (mid hp hms hso hF hpc2 hI2) fun s3 ⟨hpc3, hI3⟩ ↦ ?_
  refine Eventually.bind (loop2 hp hF (by decide) hpc3 hI3) fun s4 ⟨hpc4, hI4⟩ ↦ ?_
  refine Eventually.bind (to3 hp hF hpc4 hI4) fun s5 ⟨hpc5, hI5⟩ ↦ ?_
  refine Eventually.bind (loop3 hp hF (by decide) hpc5 hI5) fun s6 ⟨hpc6, hI6⟩ ↦ ?_
  exact finish hp hF hpc6 hI6

end

end NativeRustcVmX64.Layout.PlacementsOf
