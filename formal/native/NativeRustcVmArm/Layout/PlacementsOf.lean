module

public import NativeRustcVmArm.Code.Vm.Memset.Names
public import NativeRustcVmArm.Code.Vm.PlacementsOf.Names
public import NativeRustcVmArm.Code.Vm.StackOffsets.Names
public import NativeRustcVmArm.Layout.PlacementsOf.Turn3

/-!
# `placements_of` on AArch64

**`placementsOf_spec`**: rustc's `placements_of(kappas, placements)`, placed anywhere in the
program, meets `PlacementsOfPre`/`PlacementsOfPost` given `memset`'s and `stack_offsets`'
contracts. The prologue zeroes `block_cols` and `block_sizes` (`entry`); the first loop gathers the
stacked columns and their sizes (`loop1`); `stack_offsets` places them (`mid`); the second loop
writes their offsets into `offsets` (`loop2`); the third writes every column's placement
(`loop3`, `turn3`); `b28` returns `Some(max(16, total_log))` (`finish`). Column by column the
placements are the model's (`NativeVm.Math.Layout.placementsOf_spec`, `plF`).
-/

namespace NativeRustcVmArm.Layout.PlacementsOf

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PlacementsOf
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt wordOf addr_add_add addr_add_zero toNat_add_ofNat)

public section

variable [Host] {k : Nat}

/-- **The third loop**, from `.L17` at column `c` to `.L22` with every placement written. -/
theorem loop3 (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {c : Nat} (hc : c < 158)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b22Offset)) (hI : I3 m0 c st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b28Offset) ∧ I3 m0 158 s.data) st := by
  refine Sym.loop (fun n s ↦ ∃ c, c < 158 ∧ 158 - c = n ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b22Offset) ∧
      I3 m0 c s.data) (fun n s ⟨c, hc, hn, hpc, hI⟩ ↦ ?_) ⟨c, hc, rfl, hpc, hI⟩
  refine Eventually.mono (turn3 hp hF hc hpc hI) fun s h ↦ ?_
  rcases h with ⟨hlt, hpc', hI'⟩ | ⟨_, hpc', hI'⟩
  · exact Or.inr ⟨158 - (c + 1), by omega, c + 1, hlt, rfl, hpc', hI'⟩
  · exact Or.inl ⟨hpc', hI'⟩

/-- **`b28` and the epilogue**: `Some(max(16, total_log))`, the placements the model's. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b28Offset)) (hI : I3 m0 158 st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = retOf m0 ∧ PlacementsOfPost m0 s.data) st := by
  refine regs_step (infix_of b28_in_code (by simp [b28]) hp) run_b28 (rk run_b28) hI.body hpc
    fun st1 hm1 hpc1 hb1 hd1 hr1 ↦ ?_
  have g0 := hm1.regs .X0 _ rfl
  have g1 := hm1.regs .X1 _ rfl
  sym_simp at g0 g1
  have hx21 : st.data.regs.X21.toNat = log2Ceil (sumF (κ m0) 0) := hI.x21
  have hL64 : log2Ceil (sumF (κ m0) 0) < 2 ^ 64 := by rw [← hx21]; exact UInt64.toNat_lt _
  set L := log2Ceil (sumF (κ m0) 0) with hL
  have e21 : (Env.ofMachine st.data []).regs .X21 = BitVec.ofNat 64 L := by
    apply BitVec.eq_of_toNat_eq
    show st.data.regs.X21.toNat = _
    rw [hx21, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL64]
  rw [e21, ofNat_ult' hL64 (by decide), ofNat_beq' hL64 (by decide)] at g1
  have x1 : st1.data.regs.X1.toNat = max 16 L := by
    show (st1.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [g1]
    by_cases h : L < 16
    · simp [h, show ¬L = 16 by omega, show max 16 L = 16 by omega]
    · by_cases h' : L = 16
      · simp [h']
      · simp [h, h', show max 16 L = L by omega]
        omega
  have x0 : st1.data.regs.X0 = 1 := UInt64.toBitVec_inj.mp g0
  simp only [PcOk] at hpc1
  refine Eventually.mono (epi hp hF (hpc1.trans (hp.label (j := NativeRustcVmArm.Vm.PlacementsOf.b30Offset) NativeRustcVmArm.Vm.PlacementsOf.label_24_at)) hb1)
    fun s ⟨hs1, hs0, hsx1, hch, hsv, hsd⟩ ↦ ⟨hs1, ?_⟩
  have hsz : (natsOf m0 m0.regs.X0 columnCountW).size = 158 := by simp [natsOf, columnCountW]
  obtain ⟨r2, r1s, r1⟩ := NativeVm.Math.Layout.placementsOf_spec _ hsz
  refine ⟨hs0.trans x0, ?_, r1s, fun c hc ↦ ?_, hch, hsv⟩
  · rw [hsx1, x1, r2]; rfl
  · have hc' : c < 158 := by rw [r1s] at hc; exact hc
    have := r1 c hc'
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hc, Option.getD_some] at this
    rw [this, hsd, hd1]
    exact hI.pl c hc'

/-- **`placements_of` meets its contract.** -/
theorem placementsOf_spec (hp : Placed code k)
    (hms : Spec (Labels.label NativeRustcVmArm.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    (hso : Spec (Labels.label NativeRustcVmArm.Vm.StackOffsets.entryLabel) StackOffsetsPre StackOffsetsPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.PlacementsOf.entryLabel) PlacementsOfPre PlacementsOfPost := by
  intro m0 hpre
  have hF := Facts.of_pre hpre
  rw [show Labels.label NativeRustcVmArm.Vm.PlacementsOf.entryLabel = Host.addrOf k from hp.label (j := NativeRustcVmArm.Vm.PlacementsOf.entryOffset) NativeRustcVmArm.Vm.PlacementsOf.entry_at]
  refine Eventually.bind (entry hp hms hF) fun s1 ⟨hpc1, hI1⟩ ↦ ?_
  refine Eventually.bind (loop1 hp hF (by decide) hpc1 hI1) fun s2 ⟨hpc2, hI2⟩ ↦ ?_
  refine Eventually.bind (mid hp hms hso hF hpc2 hI2) fun s3 ⟨hpc3, hI3⟩ ↦ ?_
  refine Eventually.bind (loop2 hp hF (by decide) hpc3 hI3) fun s4 ⟨hpc4, hI4⟩ ↦ ?_
  refine Eventually.bind (to3 hp hF hpc4 hI4) fun s5 ⟨hpc5, hI5⟩ ↦ ?_
  refine Eventually.bind (loop3 hp hF (by decide) hpc5 hI5) fun s6 ⟨hpc6, hI6⟩ ↦ ?_
  exact finish hp hF hpc6 hI6

end

end NativeRustcVmArm.Layout.PlacementsOf
