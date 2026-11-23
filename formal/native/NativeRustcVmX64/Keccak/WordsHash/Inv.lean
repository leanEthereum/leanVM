module

public import NativeRustcVmX64.Keccak.WordsHash.Call
public import NativeRustcVmX64.Keccak.WordsHash.Two
public import NativeRustcVmX64.Keccak.WordsHash.Blocks

/-!
# `keccak256_words::<hash_words's closure>` (x86-64): what holds between its blocks

From the machine state `m0` at the entry (`out`, `count`, `len`, the slice `ws` of `n` words in
RDI, RSI, RDX, RCX, R8): the slice's words at entry (`word`, zero past `n`), the whole blocks'
count `nb = len / 136`, the high word `mhi` of `len · 0xF0F0F0F0F0F0F0F1`. `HCtx m0 R o m`: `Ctx`
with the slots `out`, `mhi`, `nb` (`slotsH`) and R12 the bound `min(count, n) = n`, R15 the slice,
then the registers `R`. `LaneAt m0 k x R A B j sL sZ`: before lane `j` of the block whose first
word `B` is in `x`, the lanes `A` with words `B` to `B + j - 1` XORed into the first `j`, at lane
`j`'s loaded block `sL` if word `B + j` is in the slice, else at its zero block `sZ`. `ValAt`:
lane `j`'s word in a register, at the block that XORs it, the registers `R`.
-/

namespace NativeRustcVmX64.WordsHash

open NativeRustcX64 NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
  LeanVM.Protocol.KeccakHash
open NativeRustcX64.KeccakF (WordAt load_eq_of_bytes)

@[expose] public section

/-- The slice's word count `n`. -/
def nW (m0 : MachineData) : Nat := (m0.regs.get64 .r8).toNat

/-- The slice. -/
def ws (m0 : MachineData) : BitVec 64 := m0.regs.get64 .rcx

/-- Word `i` of the slice at entry, zero past it. -/
def word (m0 : MachineData) (i : Nat) : UInt64 :=
  littleEndianLane (NativeRustcX64.bytesOf m0.dmem (ws m0) (8 * nW m0)) i

/-- The whole blocks' count. -/
def nb (m0 : MachineData) : Nat := (m0.regs.get64 .rdx).toNat / 136

/-- The high word of `len · 0xF0F0F0F0F0F0F0F1`. -/
def mhi (m0 : MachineData) : BitVec 64 :=
  BinOp.apply .mulhi .W64 (m0.regs.get64 .rdx) (BitVec.ofNat 64 17361641481138401521)

/-- The function's slots: `mhi`, `nb`, `out`. -/
def slotsH (m0 : MachineData) : List (Nat × BitVec 64) :=
  [(16, mhi m0), (24, BitVec.ofNat 64 (nb m0)), (32, m0.regs.get64 .rdi)]

/-- **What holds throughout the body**: R12 the bound, R15 the slice, then `R`. -/
abbrev HCtx (m0 : MachineData) (R : List (Reg64 × BitVec 64)) (o : Nat) (m : MachineData) :
    Prop :=
  Ctx m0 (slotsH m0) ((.r12, BitVec.ofNat 64 (nW m0)) :: (.r15, ws m0) :: R) o m

/-- Word `B + j` (`B` in `x`) is below the bound R12. -/
def cmpB (x : Reg64) (j : Nat) : SBool :=
  .cmp .ult .W64 (.bin .add .W64 (.reg x) (.lit j)) (.reg .r12)

/-- The facts of the precondition the steps use. -/
structure Geo [Labels] (m0 : MachineData) : Prop where
  stk : StackOk m0 NativeRustcVmX64.keccak256WordsStack
  rc : NativeRustcVmX64.RcAt m0 NativeRustcVmX64.keccak256WordsStack
  cnt : (m0.regs.get64 .rsi).toNat = nW m0
  len : (m0.regs.get64 .rdx).toNat = 8 * nW m0
  map : Mapped m0.dmem (ws m0) (8 * nW m0)
  nw : NoWrap (ws m0) (8 * nW m0)
  ap : 0 < nW m0 → Apart (ws m0) (8 * nW m0) (stackBelow m0 NativeRustcVmX64.keccak256WordsStack)
    (NativeRustcVmX64.keccak256WordsStack + 8)
  got : GotAt m0 NativeRustcVmX64.keccak256WordsStack
    [(m0.regs.get64 .rdi, 32), (NativeRustcVmX64.rcAddr, 192)] ["memcpy", "memset"]

variable [Host]

/-- **Before lane `j`** of the block whose first word `B` is in `x` (`LaneG`). -/
abbrev LaneAt (m0 : MachineData) (k : Nat) (x : Reg64) (R : List (Reg64 × BitVec 64))
    (A : KeccakState) (B j sL sZ : Nat) : MachineState → Prop :=
  LaneG m0 k (slotsH m0) ((.r12, BitVec.ofNat 64 (nW m0)) :: (.r15, ws m0) ::
    (x, BitVec.ofNat 64 B) :: R) (word m0) (nW m0) A B j sL sZ

/-- **Lane `j`'s word in `t`**, at `s`, the registers `R`. -/
def ValAt (m0 : MachineData) (k : Nat) (R : List (Reg64 × BitVec 64)) (A : KeccakState)
    (B j : Nat) (t : Reg64) (s : Nat) (st : MachineState) : Prop :=
  HCtx m0 R 8 st.data ∧ Lanes m0 st.data.dmem (pre A (word m0) B j) ∧
    st.data.regs.get64 t = (word m0 (B + j)).toBitVec ∧ st.pc = Host.addrOf (k + s)

end

public section

theorem slotsH_low (m0 : MachineData) : LowSlots (slotsH m0) := by
  simp [LowSlots, AllOf, slotsH]

theorem n_lt [Labels] {m0 : MachineData} (g : Geo m0) : 8 * nW m0 < 2 ^ 64 := by
  have := g.len
  have h : (m0.regs.get64 .rdx).toNat < 2 ^ 64 := (m0.regs.get64 .rdx).isLt
  omega

theorem nb_le [Labels] {m0 : MachineData} (g : Geo m0) : 17 * nb m0 ≤ nW m0 := by
  have := g.len
  unfold nb
  omega

/-- Past the slice, a word is zero. -/
theorem word_ge {m0 : MachineData} {i : Nat} (hi : nW m0 ≤ i) : word m0 i = 0 := by
  rw [word, Native.Keccak.Proof.littleEndianLane_eq]
  rw [Native.Keccak.Proof.laneOf_congr (g := fun _ => 0) fun t ht => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
      rw [Hasher.length_bytesOf]; omega)]
    rfl]
  exact Native.Keccak.Proof.laneOf_zero

/-- An unsigned comparison of a sum that does not wrap. -/
theorem ult_ofNat {a b c : Nat} (hab : a + b < 2 ^ 64) (hc : c < 2 ^ 64) :
    (BitVec.ofNat 64 a + BitVec.ofNat 64 b).ult (BitVec.ofNat 64 c) = decide (a + b < c) := by
  rw [BitVec.ult, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [decide_eq_decide]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt hc]

theorem add64 (x y : BitVec 64) : BinOp.apply .add .W64 x y = x + y := by
  simp [BinOp.apply, low_W64, ext_W64]

theorem xor64 (x y : BitVec 64) : BinOp.apply .xor .W64 x y = x ^^^ y := by
  simp [BinOp.apply, low_W64, ext_W64]

theorem mul8 (x : BitVec 64) : BinOp.apply .mul .W64 x (BitVec.ofNat 64 8) = x * 8#64 := by
  simp [BinOp.apply, low_W64, ext_W64]

/-- The comparison of word `B + j` with the bound. -/
theorem cmpB_eval [Labels] {m0 : MachineData} (g : Geo m0) {env : Env} {x : Reg64} {B j : Nat}
    (hx : env.regs x = BitVec.ofNat 64 B) (h12 : env.regs .r12 = BitVec.ofNat 64 (nW m0))
    (hB : B ≤ nW m0) (hj : j ≤ 17) : (cmpB x j).eval env = decide (B + j < nW m0) := by
  have := n_lt g
  simp only [cmpB, SBool.eval, Sym.eval, CmpOp.apply, low_W64, add64, hx, h12]
  exact ult_ofNat (by omega) (by omega)

/-- The address of word `B` of the slice. -/
theorem addrW_eval [Labels] {m0 : MachineData} {env : Env} {x : Reg64} {B : Nat}
    (h15 : env.regs .r15 = ws m0) (hx : env.regs x = BitVec.ofNat 64 B) :
    (addrW x).eval env = ws m0 + BitVec.ofNat 64 (8 * B) := by
  simp only [addrW, Sym.eval, add64, mul8, h15, hx]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul]
  omega

/-- **A word of the slice**: where region `r` is at word `i0` of the slice, unchanged since the
entry, its word `q` is word `i0 + q`. -/
theorem load_word {m0 : MachineData} {env : Env} {r i0 q sz : Nat}
    (hb : env.regions[r]? = some (ws m0 + BitVec.ofNat 64 (8 * i0), sz))
    (hi : i0 + q < nW m0)
    (hsame : ∀ t < 8, env.mem0.get? (ws m0 + BitVec.ofNat 64 (8 * (i0 + q) + t)) =
      m0.dmem.get? (ws m0 + BitVec.ofNat 64 (8 * (i0 + q) + t))) :
    env.load r (8 * q) 8 = (word m0 (i0 + q)).toBitVec := by
  apply load_eq_of_bytes
  intro t ht
  rw [Env.base_eq hb, addr_add, show 8 * i0 + (8 * q + t) = 8 * (i0 + q) + t by omega, hsame t ht,
    word, Native.Keccak.Proof.littleEndianLane_eq, Hasher.laneOf_byte _ ht,
    Hasher.getD_bytesOf _ _ (by omega)]

/-- Bytes of the slice are the entry's. -/
theorem slice_same [Labels] {m0 : MachineData} (g : Geo m0) {d : DataMem}
    (hs : SameOutside m0.dmem d (InRange (stackBelow m0 NativeRustcVmX64.keccak256WordsStack)
      NativeRustcVmX64.keccak256WordsStack)) {p : Nat} (hp : p < 8 * nW m0) :
    d.get? (ws m0 + BitVec.ofNat 64 p) = m0.dmem.get? (ws m0 + BitVec.ofNat 64 p) := by
  have hst := g.stk
  have hsf := stack_facts hst
  have hap := g.ap (by omega)
  have hnw := g.nw
  refine hs _ ?_
  rw [stk_eq] at hap ⊢
  unfold NoWrap at hnw
  unfold Apart at hap
  rw [inRange_iff (by omega), Hasher.toNat_add_ofNat' (by omega)]
  omega

/-- Words `i0` to `i0 + c` of the slice: mapped, apart from the frame. -/
theorem slice_region [Labels] {m0 : MachineData} (g : Geo m0) {d : DataMem} (hk : Kept m0.dmem d)
    {i0 c : Nat} (hi : i0 + c ≤ nW m0) (hc0 : 0 < c) :
    (Mapped d (ws m0 + BitVec.ofNat 64 (8 * i0)) (8 * c) ∧
      NoWrap (ws m0 + BitVec.ofNat 64 (8 * i0)) (8 * c)) ∧
      Apart (frame m0) 296 (ws m0 + BitVec.ofNat 64 (8 * i0)) (8 * c) := by
  have hnw := g.nw
  have hap := g.ap (by omega)
  have hsf := stack_facts g.stk
  unfold NoWrap at hnw
  rw [stk_eq] at hap
  unfold Apart at hap
  have ha : (ws m0 + BitVec.ofNat 64 (8 * i0)).toNat = (ws m0).toNat + 8 * i0 :=
    Hasher.toNat_add_ofNat' (by omega)
  refine ⟨⟨fun t ht => ?_, ?_⟩, ?_⟩
  · rw [addr_add]
    exact hk _ (g.map _ (by omega))
  · unfold NoWrap
    omega
  · unfold Apart
    omega

end

end NativeRustcVmX64.WordsHash
