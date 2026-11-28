module

public import NativeRustcVmX64.Keccak.WordsHash.Entry

/-!
# `keccak256_words::<hash_words's closure>` (x86-64): the whole blocks

In whole block `b < nb` (its words region 1, the 136 bytes from word `17 b` of the slice, at R15
plus RBX words), every word is in the slice, so each lane's branch goes on to the next lane's
loaded block (`full_step`, `laneL_step`). `full_lanes`: from the block's first lane to lane 16's
word in RAX (`full16`). `fullEnd`: lane 16's XOR and the call of `keccak_f` (`fullXor`,
`call_kf`), then the next block's branch (`fullNext`), to the next block's head or, after the
last, the last block's head. `full_loop`: by induction on the blocks left.
-/

namespace NativeRustcVmX64.WordsHash

open NativeRustcX64 NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcX64.KeccakF (WordAt wordAt_of_eq load_of_wordAt)
open NativeRustcVm.Keccak (wordBlocks)
open Vm.Keccak256WordsOfHashWords

public section

variable [Host]

/-- **A lane of a whole block**: word `17 b + j` is in the slice. -/
theorem full_step {k : Nat} {m0 : MachineData} (g : Geo m0) {b j : Nat} (hb : b < nb m0)
    (hj : j < 16) {sL sZ : Nat} {blk : List Directive} {S : SState} {x : Exit}
    (hk : blk.IsInfixAt Host.prog (k + sL)) (hx : exec blk (startL .rbx 136) = some (S, x))
    (hmem : S.mem =
      [⟨0, 40 + 8 * j, 8, .bin .xor .W64 (.load 0 (40 + 8 * j) 8) (.load 1 (8 * j) 8)⟩])
    (hrsp : S.reg .rsp = some (.ptr 0 8))
    (hkeep : keepsRegs S [.r12, .r15, .rbx, .r13, .rbp, .r14] = true)
    {pos : Bool} {lbl : Label}
    (hexit : x = .cond (if pos then cmpB .rbx (j + 1) else .not (cmpB .rbx (j + 1))) lbl)
    {sL' sZ' : Nat} (hlab : Labels.label lbl = Host.addrOf (k + if pos then sL' else sZ'))
    (hnext : sL + blk.length = if pos then sZ' else sL') {st : MachineState}
    (h : LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) j sL sZ st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) (j + 1) sL' sZ') st := by
  obtain ⟨hc, hl, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hpc
  have hle := nb_le g
  have hin : 17 * b + j < nW m0 := by omega
  simp only [hin, ↓reduceIte] at hpc
  subst hpc
  exact laneL_step g hj hin (by omega) (by omega) rfl hc hl hk hx hmem hrsp rfl hkeep hexit hlab
    hnext

theorem fullStep0 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0) {b : Nat}
    (hb : b < nb m0) {st : MachineState}
    (h : LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 0 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b11Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b29Offset st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 1 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b30Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b12Offset) st :=
  full_step g hb (j := 0) (by decide) (b11_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullL0 rfl rfl
    (by decide +kernel) (pos := true) rfl (label_at hp b30_in_code rfl) rfl h

theorem fullStep1 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0) {b : Nat}
    (hb : b < nb m0) {st : MachineState}
    (h : LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 1 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b30Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b12Offset st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 2 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b31Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b13Offset) st :=
  full_step g hb (j := 1) (by decide) (b30_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullL1 rfl rfl
    (by decide +kernel) (pos := false) rfl (label_at hp b13_in_code rfl) rfl h

theorem fullStep2 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0) {b : Nat}
    (hb : b < nb m0) {st : MachineState}
    (h : LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 2 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b31Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b13Offset st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 3 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b32Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b14Offset) st :=
  full_step g hb (j := 2) (by decide) (b31_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullL2 rfl rfl
    (by decide +kernel) (pos := false) rfl (label_at hp b14_in_code rfl) rfl h

theorem fullStep3 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0) {b : Nat}
    (hb : b < nb m0) {st : MachineState}
    (h : LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 3 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b32Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b14Offset st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 4 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b33Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b15Offset) st :=
  full_step g hb (j := 3) (by decide) (b32_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullL3 rfl rfl
    (by decide +kernel) (pos := false) rfl (label_at hp b15_in_code rfl) rfl h

theorem fullStep4 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0) {b : Nat}
    (hb : b < nb m0) {st : MachineState}
    (h : LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 4 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b33Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b15Offset st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 5 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b34Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b16Offset) st :=
  full_step g hb (j := 4) (by decide) (b33_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullL4 rfl rfl
    (by decide +kernel) (pos := false) rfl (label_at hp b16_in_code rfl) rfl h

theorem fullStep5 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0) {b : Nat}
    (hb : b < nb m0) {st : MachineState}
    (h : LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 5 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b34Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b16Offset st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 6 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b35Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b17Offset) st :=
  full_step g hb (j := 5) (by decide) (b34_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullL5 rfl rfl
    (by decide +kernel) (pos := false) rfl (label_at hp b17_in_code rfl) rfl h

theorem fullStep6 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0) {b : Nat}
    (hb : b < nb m0) {st : MachineState}
    (h : LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 6 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b35Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b17Offset st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 7 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b36Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b18Offset) st :=
  full_step g hb (j := 6) (by decide) (b35_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullL6 rfl rfl
    (by decide +kernel) (pos := false) rfl (label_at hp b18_in_code rfl) rfl h

theorem fullStep7 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0) {b : Nat}
    (hb : b < nb m0) {st : MachineState}
    (h : LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 7 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b36Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b18Offset st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 8 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b37Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b19Offset) st :=
  full_step g hb (j := 7) (by decide) (b36_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullL7 rfl rfl
    (by decide +kernel) (pos := false) rfl (label_at hp b19_in_code rfl) rfl h

theorem fullStep8 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0) {b : Nat}
    (hb : b < nb m0) {st : MachineState}
    (h : LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 8 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b37Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b19Offset st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 9 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b38Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b20Offset) st :=
  full_step g hb (j := 8) (by decide) (b37_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullL8 rfl rfl
    (by decide +kernel) (pos := false) rfl (label_at hp b20_in_code rfl) rfl h

theorem fullStep9 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0) {b : Nat}
    (hb : b < nb m0) {st : MachineState}
    (h : LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 9 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b38Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b20Offset st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 10 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b39Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b21Offset) st :=
  full_step g hb (j := 9) (by decide) (b38_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullL9 rfl rfl
    (by decide +kernel) (pos := false) rfl (label_at hp b21_in_code rfl) rfl h

theorem fullStep10 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0) {b : Nat}
    (hb : b < nb m0) {st : MachineState}
    (h : LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 10 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b39Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b21Offset st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 11 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b40Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b22Offset) st :=
  full_step g hb (j := 10) (by decide) (b39_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullL10 rfl rfl
    (by decide +kernel) (pos := false) rfl (label_at hp b22_in_code rfl) rfl h

theorem fullStep11 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0) {b : Nat}
    (hb : b < nb m0) {st : MachineState}
    (h : LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 11 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b40Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b22Offset st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 12 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b41Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b23Offset) st :=
  full_step g hb (j := 11) (by decide) (b40_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullL11 rfl rfl
    (by decide +kernel) (pos := false) rfl (label_at hp b23_in_code rfl) rfl h

theorem fullStep12 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0) {b : Nat}
    (hb : b < nb m0) {st : MachineState}
    (h : LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 12 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b41Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b23Offset st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 13 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b42Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b24Offset) st :=
  full_step g hb (j := 12) (by decide) (b41_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullL12 rfl rfl
    (by decide +kernel) (pos := false) rfl (label_at hp b24_in_code rfl) rfl h

theorem fullStep13 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0) {b : Nat}
    (hb : b < nb m0) {st : MachineState}
    (h : LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 13 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b42Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b24Offset st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 14 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b43Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b25Offset) st :=
  full_step g hb (j := 13) (by decide) (b42_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullL13 rfl rfl
    (by decide +kernel) (pos := false) rfl (label_at hp b25_in_code rfl) rfl h

theorem fullStep14 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0) {b : Nat}
    (hb : b < nb m0) {st : MachineState}
    (h : LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 14 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b43Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b25Offset st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 15 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b44Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b26Offset) st :=
  full_step g hb (j := 14) (by decide) (b43_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullL14 rfl rfl
    (by decide +kernel) (pos := false) rfl (label_at hp b26_in_code rfl) rfl h

theorem fullStep15 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0) {b : Nat}
    (hb : b < nb m0) {st : MachineState}
    (h : LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 15 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b44Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b26Offset st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 16 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b7Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b45Offset) st :=
  full_step g hb (j := 15) (by decide) (b44_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullL15 rfl rfl
    (by decide +kernel) (pos := true) rfl (label_at hp b7_in_code rfl) rfl h

/-- **A whole block's 16 lanes**, then lane 16's word in RAX. -/
theorem full_lanes {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0) {b : Nat}
    (hb : b < nb m0) {st : MachineState}
    (h : LaneAt m0 k .rbx (fullR m0) (wordBlocks (word m0) b) (17 * b) 0 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b11Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b29Offset st) :
    Eventually (step1 Host.exe)
      (ValAt m0 k ((.rbx, BitVec.ofNat 64 (17 * b)) :: fullR m0) (wordBlocks (word m0) b) (17 * b) 16
        .rax NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b8Offset) st := by
  refine Eventually.bind (fullStep0 hp g hb h) fun st h => ?_
  refine Eventually.bind (fullStep1 hp g hb h) fun st h => ?_
  refine Eventually.bind (fullStep2 hp g hb h) fun st h => ?_
  refine Eventually.bind (fullStep3 hp g hb h) fun st h => ?_
  refine Eventually.bind (fullStep4 hp g hb h) fun st h => ?_
  refine Eventually.bind (fullStep5 hp g hb h) fun st h => ?_
  refine Eventually.bind (fullStep6 hp g hb h) fun st h => ?_
  refine Eventually.bind (fullStep7 hp g hb h) fun st h => ?_
  refine Eventually.bind (fullStep8 hp g hb h) fun st h => ?_
  refine Eventually.bind (fullStep9 hp g hb h) fun st h => ?_
  refine Eventually.bind (fullStep10 hp g hb h) fun st h => ?_
  refine Eventually.bind (fullStep11 hp g hb h) fun st h => ?_
  refine Eventually.bind (fullStep12 hp g hb h) fun st h => ?_
  refine Eventually.bind (fullStep13 hp g hb h) fun st h => ?_
  refine Eventually.bind (fullStep14 hp g hb h) fun st h => ?_
  refine Eventually.bind (fullStep15 hp g hb h) fun st h => ?_
  obtain ⟨hc, hl, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hpc
  have hle := nb_le g
  have hin : 17 * b + 16 < nW m0 := by omega
  simp only [hin, ↓reduceIte] at hpc
  subst hpc
  exact regL_step g hin (by omega) (by omega) rfl hc hl (b7_in_code.trans hp.1 (List.cons_ne_nil _ _))
    full16 rfl rfl rfl (fun _ hm => regsAt_keep hm hc.regs
      (names := [.r12, .r15, .rbx, .r13, .rbp, .r14]) rfl (by decide +kernel)) (Or.inl ⟨rfl, rfl⟩)

end

end NativeRustcVmX64.WordsHash
