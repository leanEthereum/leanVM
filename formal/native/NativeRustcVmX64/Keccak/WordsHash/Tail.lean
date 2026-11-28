module

public import NativeRustcVmX64.Keccak.WordsHash.FullEnd

/-!
# `keccak256_words::<hash_words's closure>` (x86-64): the last block's words

From the last block's first lane (`tail_head`), lane `j < 16` is `lane2_step` (`tail{j}`), but
lanes 1, 13, 14, 15, 16, whose word goes into a register first (`val2_step`, `tailV{j}`) and is
XORed by a later block (`xorReg_step`, `tailX{j}`), which also computes the padding's values: RDX
`mhi` (`b48`), then `128 nb` (`b73`), RCX `136 nb` (`b76`), R14 `len % 136` (`b79`; the
registers `tailR1` to `tailR4`). `tail_run`: to the padding block with lane 16's word in RAX.
-/

namespace NativeRustcVmX64.WordsHash

open NativeRustcX64 NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcX64.KeccakF (load_of_wordAt)
open Vm.Keccak256WordsOfHashWords

@[expose] public section

/-- RDX `mhi`, then the last block's registers. -/
def tailR1 (m0 : MachineData) : List (Reg64 × BitVec 64) := (.rdx, mhi m0) :: tailR m0

/-- RDX `128 nb`, then the last block's registers. -/
def tailR2 (m0 : MachineData) : List (Reg64 × BitVec 64) :=
  (.rdx, BitVec.ofNat 64 (128 * nb m0)) :: tailR m0

/-- RCX `136 nb`, then the last block's registers. -/
def tailR3 (m0 : MachineData) : List (Reg64 × BitVec 64) :=
  (.rcx, BitVec.ofNat 64 (136 * nb m0)) :: tailR m0

/-- RSI `nb`, R14 the bytes past the whole blocks. -/
def tailR4 (m0 : MachineData) : List (Reg64 × BitVec 64) :=
  [(.rsi, BitVec.ofNat 64 (nb m0)), (.r14, BitVec.ofNat 64 ((m0.regs.get64 .rdx).toNat % 136))]

end

public section

theorem mhi_nb (m0 : MachineData) : (mhi m0).toNat / 128 = nb m0 := mhi_div _

theorem rcx_val (n : Nat) :
    BitVec.ofNat 64 (128 * n) + BitVec.ofNat 64 n * 8#64 = BitVec.ofNat 64 (136 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem r14_val (m0 : MachineData) :
    BinOp.apply .sub .W64 (m0.regs.get64 .rdx) (BitVec.ofNat 64 (136 * nb m0)) =
      BitVec.ofNat 64 ((m0.regs.get64 .rdx).toNat % 136) := by
  have hx : (m0.regs.get64 .rdx).toNat < 2 ^ 64 := (m0.regs.get64 .rdx).isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_sub, BitVec.toNat_ofNat]
  unfold nb
  omega

variable [Host]

theorem tail0 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .rax (tailR m0) (stA m0) (17 * nb m0) 0 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b3Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b46Offset st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .rax (tailR m0) (stA m0) (17 * nb m0) 1 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b47Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b4Offset) st :=
  lane2_step g (j := 0) (sz := 8) (by decide) (nb_le g) (by decide) (by intro; omega) rfl
    (names := [.r12, .r15, .rax, .rsi, .r14]) rfl
    (b3_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL0 rfl rfl (by decide +kernel) (posL := true) rfl (label_at hp b47_in_code rfl) rfl
    (b46_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ0 rfl rfl (by decide +kernel) (posZ := false) rfl (label_at hp b4_in_code rfl) rfl h

theorem tailV1 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .rax (tailR m0) (stA m0) (17 * nb m0) 1 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b47Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b4Offset st) :
    Eventually (step1 Host.exe) (ValAt m0 k ((.rax, BitVec.ofNat 64 (17 * nb m0)) :: tailR m0) (stA m0) (17 * nb m0) 1 .rcx NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b48Offset) st :=
  val2_step g (sz := 16) (by decide) (by intro; omega) rfl (fun _ h => h) (names := [.r12, .r15, .rax, .rsi, .r14]) rfl
    (b47_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL1 rfl rfl rfl (by decide +kernel) (.inl ⟨rfl, rfl⟩)
    (b4_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ1 rfl rfl rfl (by decide +kernel) (.inr ⟨_, rfl, label_at hp b48_in_code rfl⟩) h

theorem tail2 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 2 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b49Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b61Offset st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 3 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b62Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b50Offset) st :=
  lane2_step g (j := 2) (sz := 24) (by decide) (nb_le g) (by decide) (by intro; omega) rfl
    (names := [.r12, .r15, .rax, .rdx, .rsi, .r14]) rfl
    (b49_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL2 rfl rfl (by decide +kernel) (posL := true) rfl (label_at hp b62_in_code rfl) rfl
    (b61_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ2 rfl rfl (by decide +kernel) (posZ := false) rfl (label_at hp b50_in_code rfl) rfl h

theorem tail3 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 3 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b62Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b50Offset st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 4 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b63Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b51Offset) st :=
  lane2_step g (j := 3) (sz := 32) (by decide) (nb_le g) (by decide) (by intro; omega) rfl
    (names := [.r12, .r15, .rax, .rdx, .rsi, .r14]) rfl
    (b62_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL3 rfl rfl (by decide +kernel) (posL := false) rfl (label_at hp b51_in_code rfl) rfl
    (b50_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ3 rfl rfl (by decide +kernel) (posZ := true) rfl (label_at hp b63_in_code rfl) rfl h

theorem tail4 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 4 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b63Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b51Offset st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 5 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b64Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b52Offset) st :=
  lane2_step g (j := 4) (sz := 40) (by decide) (nb_le g) (by decide) (by intro; omega) rfl
    (names := [.r12, .r15, .rax, .rdx, .rsi, .r14]) rfl
    (b63_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL4 rfl rfl (by decide +kernel) (posL := false) rfl (label_at hp b52_in_code rfl) rfl
    (b51_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ4 rfl rfl (by decide +kernel) (posZ := true) rfl (label_at hp b64_in_code rfl) rfl h

theorem tail5 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 5 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b64Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b52Offset st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 6 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b65Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b53Offset) st :=
  lane2_step g (j := 5) (sz := 48) (by decide) (nb_le g) (by decide) (by intro; omega) rfl
    (names := [.r12, .r15, .rax, .rdx, .rsi, .r14]) rfl
    (b64_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL5 rfl rfl (by decide +kernel) (posL := false) rfl (label_at hp b53_in_code rfl) rfl
    (b52_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ5 rfl rfl (by decide +kernel) (posZ := true) rfl (label_at hp b65_in_code rfl) rfl h

theorem tail6 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 6 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b65Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b53Offset st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 7 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b66Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b54Offset) st :=
  lane2_step g (j := 6) (sz := 56) (by decide) (nb_le g) (by decide) (by intro; omega) rfl
    (names := [.r12, .r15, .rax, .rdx, .rsi, .r14]) rfl
    (b65_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL6 rfl rfl (by decide +kernel) (posL := false) rfl (label_at hp b54_in_code rfl) rfl
    (b53_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ6 rfl rfl (by decide +kernel) (posZ := true) rfl (label_at hp b66_in_code rfl) rfl h

theorem tail7 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 7 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b66Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b54Offset st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 8 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b67Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b55Offset) st :=
  lane2_step g (j := 7) (sz := 64) (by decide) (nb_le g) (by decide) (by intro; omega) rfl
    (names := [.r12, .r15, .rax, .rdx, .rsi, .r14]) rfl
    (b66_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL7 rfl rfl (by decide +kernel) (posL := false) rfl (label_at hp b55_in_code rfl) rfl
    (b54_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ7 rfl rfl (by decide +kernel) (posZ := true) rfl (label_at hp b67_in_code rfl) rfl h

theorem tail8 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 8 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b67Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b55Offset st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 9 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b68Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b56Offset) st :=
  lane2_step g (j := 8) (sz := 72) (by decide) (nb_le g) (by decide) (by intro; omega) rfl
    (names := [.r12, .r15, .rax, .rdx, .rsi, .r14]) rfl
    (b67_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL8 rfl rfl (by decide +kernel) (posL := false) rfl (label_at hp b56_in_code rfl) rfl
    (b55_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ8 rfl rfl (by decide +kernel) (posZ := true) rfl (label_at hp b68_in_code rfl) rfl h

theorem tail9 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 9 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b68Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b56Offset st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 10 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b69Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b57Offset) st :=
  lane2_step g (j := 9) (sz := 80) (by decide) (nb_le g) (by decide) (by intro; omega) rfl
    (names := [.r12, .r15, .rax, .rdx, .rsi, .r14]) rfl
    (b68_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL9 rfl rfl (by decide +kernel) (posL := false) rfl (label_at hp b57_in_code rfl) rfl
    (b56_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ9 rfl rfl (by decide +kernel) (posZ := true) rfl (label_at hp b69_in_code rfl) rfl h

theorem tail10 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 10 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b69Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b57Offset st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 11 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b70Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b58Offset) st :=
  lane2_step g (j := 10) (sz := 88) (by decide) (nb_le g) (by decide) (by intro; omega) rfl
    (names := [.r12, .r15, .rax, .rdx, .rsi, .r14]) rfl
    (b69_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL10 rfl rfl (by decide +kernel) (posL := false) rfl (label_at hp b58_in_code rfl) rfl
    (b57_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ10 rfl rfl (by decide +kernel) (posZ := true) rfl (label_at hp b70_in_code rfl) rfl h

theorem tail11 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 11 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b70Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b58Offset st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 12 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b71Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b59Offset) st :=
  lane2_step g (j := 11) (sz := 96) (by decide) (nb_le g) (by decide) (by intro; omega) rfl
    (names := [.r12, .r15, .rax, .rdx, .rsi, .r14]) rfl
    (b70_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL11 rfl rfl (by decide +kernel) (posL := false) rfl (label_at hp b59_in_code rfl) rfl
    (b58_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ11 rfl rfl (by decide +kernel) (posZ := true) rfl (label_at hp b71_in_code rfl) rfl h

theorem tail12 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 12 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b71Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b59Offset st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 13 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b72Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b60Offset) st :=
  lane2_step g (j := 12) (sz := 104) (by decide) (nb_le g) (by decide) (by intro; omega) rfl
    (names := [.r12, .r15, .rax, .rdx, .rsi, .r14]) rfl
    (b71_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL12 rfl rfl (by decide +kernel) (posL := false) rfl (label_at hp b60_in_code rfl) rfl
    (b59_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ12 rfl rfl (by decide +kernel) (posZ := true) rfl (label_at hp b72_in_code rfl) rfl h

theorem tailV13 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 13 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b72Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b60Offset st) :
    Eventually (step1 Host.exe) (ValAt m0 k ((.rax, BitVec.ofNat 64 (17 * nb m0)) :: tailR1 m0) (stA m0) (17 * nb m0) 13 .rcx NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b73Offset) st :=
  val2_step g (sz := 112) (by decide) (by intro; omega) rfl (fun _ h => h) (names := [.r12, .r15, .rax, .rdx, .rsi, .r14]) rfl
    (b72_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL13 rfl rfl rfl (by decide +kernel) (.inl ⟨rfl, rfl⟩)
    (b60_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ13 rfl rfl rfl (by decide +kernel) (.inr ⟨_, rfl, label_at hp b73_in_code rfl⟩) h

theorem tailV14 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .rax (tailR2 m0) (stA m0) (17 * nb m0) 14 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b74Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b75Offset st) :
    Eventually (step1 Host.exe) (ValAt m0 k ((.rax, BitVec.ofNat 64 (17 * nb m0)) :: tailR2 m0) (stA m0) (17 * nb m0) 14 .rcx NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b76Offset) st :=
  val2_step g (sz := 120) (by decide) (by intro; omega) rfl (fun _ h => h) (names := [.r12, .r15, .rax, .rdx, .rsi, .r14]) rfl
    (b74_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL14 rfl rfl rfl (by decide +kernel) (.inr ⟨_, rfl, label_at hp b76_in_code rfl⟩)
    (b75_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ14 rfl rfl rfl (by decide +kernel) (.inl ⟨rfl, rfl⟩) h

theorem tailV15 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .rax (tailR3 m0) (stA m0) (17 * nb m0) 15 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b77Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b78Offset st) :
    Eventually (step1 Host.exe) (ValAt m0 k ((.rax, BitVec.ofNat 64 (17 * nb m0)) :: tailR3 m0) (stA m0) (17 * nb m0) 15 .rdx NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b79Offset) st :=
  val2_step g (sz := 128) (by decide) (by intro; omega) rfl (fun _ h => h) (names := [.r12, .r15, .rax, .rcx, .rsi, .r14]) rfl
    (b77_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL15 rfl rfl rfl (by decide +kernel) (.inr ⟨_, rfl, label_at hp b79_in_code rfl⟩)
    (b78_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ15 rfl rfl rfl (by decide +kernel) (.inl ⟨rfl, rfl⟩) h

theorem tailV16 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .rax (tailR4 m0) (stA m0) (17 * nb m0) 16 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b80Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b81Offset st) :
    Eventually (step1 Host.exe) (ValAt m0 k (tailR4 m0) (stA m0) (17 * nb m0) 16 .rax NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b82Offset) st :=
  val2_step g (sz := 136) (by decide) (by intro; omega) rfl (fun _ h => ⟨h.1, h.2.1, h.2.2.2⟩) (names := [.r12, .r15, .rsi, .r14]) rfl
    (b80_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL16 rfl rfl rfl (by decide +kernel) (.inr ⟨_, rfl, label_at hp b82_in_code rfl⟩)
    (b81_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ16 rfl rfl rfl (by decide +kernel) (.inl ⟨rfl, rfl⟩) h

theorem tailXor1 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0) {st : MachineState}
    (h : ValAt m0 k ((.rax, BitVec.ofNat 64 (17 * nb m0)) :: tailR m0) (stA m0) (17 * nb m0) 1
      .rcx NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b48Offset st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .rax (tailR1 m0) (stA m0) (17 * nb m0) 2 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b49Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b61Offset) st := by
  have hc := h.1
  exact xorReg_step g (j := 1) (R' := tailR1 m0) (by decide) (nb_le g) h (b48_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailX1 rfl rfl
    (fun _ hm => ⟨(hm.regs .r12 _ rfl).trans hc.regs.1, (hm.regs .r15 _ rfl).trans hc.regs.2.1,
      (hm.regs .rax _ rfl).trans hc.regs.2.2.1,
      (hm.regs .rdx _ rfl).trans (load_of_wordAt (r := 0) (off := 16) hc.slots.1),
      (hm.regs .rsi _ rfl).trans hc.regs.2.2.2.1, (hm.regs .r14 _ rfl).trans hc.regs.2.2.2.2.1,
      trivial⟩)
    (pos := false) rfl (label_at hp b61_in_code rfl) rfl

theorem tailXor13 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState}
    (h : ValAt m0 k ((.rax, BitVec.ofNat 64 (17 * nb m0)) :: tailR1 m0) (stA m0) (17 * nb m0) 13
      .rcx NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b73Offset st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .rax (tailR2 m0) (stA m0) (17 * nb m0) 14 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b74Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b75Offset)
      st := by
  have hc := h.1
  exact xorReg_step g (j := 13) (R' := tailR2 m0) (by decide) (nb_le g) h (b73_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailX13 rfl rfl
    (fun _ hm => ⟨(hm.regs .r12 _ rfl).trans hc.regs.1, (hm.regs .r15 _ rfl).trans hc.regs.2.1,
      (hm.regs .rax _ rfl).trans hc.regs.2.2.1,
      (hm.regs .rdx _ rfl).trans (by
        show BinOp.apply .and .W64 (st.data.regs.get64 .rdx) (BitVec.ofNat 64 18446744073709551488) =
          BitVec.ofNat 64 (128 * nb m0)
        rw [hc.regs.2.2.2.1, and128_val, mhi_nb]),
      (hm.regs .rsi _ rfl).trans hc.regs.2.2.2.2.1, (hm.regs .r14 _ rfl).trans hc.regs.2.2.2.2.2.1,
      trivial⟩)
    (pos := false) rfl (label_at hp b75_in_code rfl) rfl

theorem tailXor14 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState}
    (h : ValAt m0 k ((.rax, BitVec.ofNat 64 (17 * nb m0)) :: tailR2 m0) (stA m0) (17 * nb m0) 14
      .rcx NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b76Offset st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .rax (tailR3 m0) (stA m0) (17 * nb m0) 15 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b77Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b78Offset)
      st := by
  have hc := h.1
  exact xorReg_step g (j := 14) (R' := tailR3 m0) (by decide) (nb_le g) h (b76_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailX14 rfl rfl
    (fun _ hm => ⟨(hm.regs .r12 _ rfl).trans hc.regs.1, (hm.regs .r15 _ rfl).trans hc.regs.2.1,
      (hm.regs .rax _ rfl).trans hc.regs.2.2.1,
      (hm.regs .rcx _ rfl).trans (by
        show BinOp.apply .add .W64 (st.data.regs.get64 .rdx)
          (BinOp.apply .mul .W64 (st.data.regs.get64 .rsi) (BitVec.ofNat 64 8)) =
          BitVec.ofNat 64 (136 * nb m0)
        rw [add64, mul8, hc.regs.2.2.2.1, hc.regs.2.2.2.2.1, rcx_val]),
      (hm.regs .rsi _ rfl).trans hc.regs.2.2.2.2.1, (hm.regs .r14 _ rfl).trans hc.regs.2.2.2.2.2.1,
      trivial⟩)
    (pos := false) rfl (label_at hp b78_in_code rfl) rfl

theorem tailXor15 {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState}
    (h : ValAt m0 k ((.rax, BitVec.ofNat 64 (17 * nb m0)) :: tailR3 m0) (stA m0) (17 * nb m0) 15
      .rdx NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b79Offset st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .rax (tailR4 m0) (stA m0) (17 * nb m0) 16 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b80Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b81Offset)
      st := by
  have hc := h.1
  exact xorReg_step g (j := 15) (R' := tailR4 m0) (by decide) (nb_le g) h (b79_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailX15 rfl rfl
    (fun _ hm => ⟨(hm.regs .r12 _ rfl).trans hc.regs.1, (hm.regs .r15 _ rfl).trans hc.regs.2.1,
      (hm.regs .rax _ rfl).trans hc.regs.2.2.1, (hm.regs .rsi _ rfl).trans hc.regs.2.2.2.2.1,
      (hm.regs .r14 _ rfl).trans (by
        show BinOp.apply .sub .W64 (st.data.regs.get64 .r14) (st.data.regs.get64 .rcx) =
          BitVec.ofNat 64 ((m0.regs.get64 .rdx).toNat % 136)
        rw [hc.regs.2.2.2.2.2.1, hc.regs.2.2.2.1, r14_val]),
      trivial⟩)
    (pos := false) rfl (label_at hp b81_in_code rfl) rfl

/-- **The last block's words**: from its first lane to the padding block, lane 16's word in
RAX. -/
theorem tail_run {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState}
    (h : LaneAt m0 k .rax (tailR m0) (stA m0) (17 * nb m0) 0 NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b3Offset NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b46Offset st) :
    Eventually (step1 Host.exe) (ValAt m0 k (tailR4 m0) (stA m0) (17 * nb m0) 16 .rax NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b82Offset) st := by
  refine Eventually.bind (tail0 hp g h) fun st h => ?_
  refine Eventually.bind (tailV1 hp g h) fun st h => ?_
  refine Eventually.bind (tailXor1 hp g h) fun st h => ?_
  refine Eventually.bind (tail2 hp g h) fun st h => ?_
  refine Eventually.bind (tail3 hp g h) fun st h => ?_
  refine Eventually.bind (tail4 hp g h) fun st h => ?_
  refine Eventually.bind (tail5 hp g h) fun st h => ?_
  refine Eventually.bind (tail6 hp g h) fun st h => ?_
  refine Eventually.bind (tail7 hp g h) fun st h => ?_
  refine Eventually.bind (tail8 hp g h) fun st h => ?_
  refine Eventually.bind (tail9 hp g h) fun st h => ?_
  refine Eventually.bind (tail10 hp g h) fun st h => ?_
  refine Eventually.bind (tail11 hp g h) fun st h => ?_
  refine Eventually.bind (tail12 hp g h) fun st h => ?_
  refine Eventually.bind (tailV13 hp g h) fun st h => ?_
  refine Eventually.bind (tailXor13 hp g h) fun st h => ?_
  refine Eventually.bind (tailV14 hp g h) fun st h => ?_
  refine Eventually.bind (tailXor14 hp g h) fun st h => ?_
  refine Eventually.bind (tailV15 hp g h) fun st h => ?_
  refine Eventually.bind (tailXor15 hp g h) fun st h => ?_
  exact tailV16 hp g h

end

end NativeRustcVmX64.WordsHash
