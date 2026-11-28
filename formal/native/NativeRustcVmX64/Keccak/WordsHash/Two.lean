module

public import NativeRustcVmX64.Keccak.WordsHash.Frame
public import NativeRustcVm.Keccak.Words

/-!
# `keccak256_words` (x86-64): a lane of a block, either way

Both instances absorb lane `j` of a block, whose first word is `B`, one of two ways on whether
word `B + j` is below the count `cnt` (`index < bound`): from its word (loaded, or `iv_word`'s), or
with zero. `LaneG m0 k L R w cnt A B j sL sZ`: before lane `j`, `Ctx` with the slots `L` and the
registers `R`, the lanes `A` with the words `w (B + i)` XORed into the first `j`, at lane `j`'s
first block `sL` if word `B + j` is below the count, else at its zero block `sZ`.

- `lane_two`: the two ways, from `LaneG`: each from `Ctx`, the lanes and the comparison.
- `lane_block`: a block that writes lane `j` with its word and branches on word `B + j + 1`, to
  `LaneG … (j + 1)`; both ways end in one.
- `branch_pc`: where a block's branch on word `B + j + 1` goes.
- `lane_lastG`: the lanes before the last permutation, the last block's 17 words and the
  padding XORed into the rate.
-/

namespace NativeRustcVmX64.WordsHash

open NativeRustcX64 NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcX64.KeccakF (WordAt load_of_wordAt)
open NativeRustcVm.Keccak (padLane)

@[expose] public section

/-- **Before lane `j`** of the block whose first word is `B`. -/
def LaneG [Host] (m0 : MachineData) (k : Nat) (L : List (Nat × BitVec 64))
    (R : List (Reg64 × BitVec 64)) (w : Nat → UInt64) (cnt : Nat) (A : KeccakState)
    (B j sL sZ : Nat) (st : MachineState) : Prop :=
  Ctx m0 L R 8 st.data ∧ Lanes m0 st.data.dmem (pre A w B j) ∧
    st.pc = if B + j < cnt then Host.addrOf (k + sL) else Host.addrOf (k + sZ)

end

public section

/-- A comparison or its negation, as `pos == …`. -/
theorem eval_posCmp [Labels] {env : Env} {c : SBool} {P : Prop} [Decidable P] (h : c.eval env = decide P)
    (pos : Bool) : (if pos then c else .not c).eval env = (pos == decide P) := by
  cases pos <;> simp [SBool.eval, h]

/-- **The lanes before the last permutation**: `A`'s with words `B` to `B + 15` XORed into the
first 16 (`pre … 17` with word `B + 16` in lane 16), the padding word into lane
`t = len % 136 / 8` and `PAD_LAST` into lane 16. -/
theorem lane_lastG (A : KeccakState) (w : Nat → UInt64) (B len : Nat) {t : Nat}
    (ht : t = len % 136 / 8) {i : Nat} (hi : i < 25) :
    (let pw : UInt64 := 1 <<< (8 * (len % 136 % 8)).toUInt64
     let f2 := fun i => if i = t then pre A w B 17 t ^^^ pw else pre A w B 17 i
     if i = 16 then f2 16 ^^^ 0x8000000000000000 else f2 i) =
      Keccak.lane (Native.Keccak.Proof.xorRate A fun k => w (B + k) ^^^ padLane len k) i := by
  have ht17 : t < 17 := by omega
  simp only []
  rw [Native.Keccak.Proof.lane_xorRate _ _ hi, padLane, ← ht]
  simp only [pre]
  by_cases h16 : i = 16
  · subst h16
    by_cases ht16 : t = 16
    · subst ht16
      simp [UInt64.xor_assoc]
    · simp [Ne.symm ht16, UInt64.xor_assoc]
  · by_cases hit : i = t
    · subst hit
      simp [h16, ht17, UInt64.xor_assoc]
    · by_cases h17 : i < 17
      · simp [h16, hit, h17]
      · simp [h16, hit, h17]

variable [Host]

/-- **The two ways of a lane.** -/
theorem lane_two {m0 : MachineData} {k : Nat} {L : List (Nat × BitVec 64)}
    {R : List (Reg64 × BitVec 64)} {w : Nat → UInt64} {cnt : Nat} {A : KeccakState}
    {B j sL sZ : Nat} {P : MachineState → Prop}
    (hL : ∀ m, Ctx m0 L R 8 m → Lanes m0 m.dmem (pre A w B j) → B + j < cnt →
      Eventually (step1 Host.exe) P ⟨m, Host.addrOf (k + sL)⟩)
    (hZ : ∀ m, Ctx m0 L R 8 m → Lanes m0 m.dmem (pre A w B j) → cnt ≤ B + j →
      Eventually (step1 Host.exe) P ⟨m, Host.addrOf (k + sZ)⟩)
    {st : MachineState} (h : LaneG m0 k L R w cnt A B j sL sZ st) :
    Eventually (step1 Host.exe) P st := by
  obtain ⟨hc, hl, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hpc
  by_cases hin : B + j < cnt
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact hL m hc hl hin
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact hZ m hc hl (by omega)

/-- **A block's branch on a comparison** `P`: to `sL` where it holds, else `sZ`. -/
theorem branch_pc {env : Env} {c : SBool} {pos : Bool} {P : Prop} [Decidable P]
    (hev : c.eval env = (pos == decide P)) {lbl : Label} {k s n sL sZ : Nat}
    (hlab : Labels.label lbl = Host.addrOf (k + if pos then sL else sZ))
    (hnext : s + n = if pos then sZ else sL) {st : MachineState}
    (hpc : PcOk env (.cond c lbl) (Host.addrOf (k + s + n)) st) :
    st.pc = if P then Host.addrOf (k + sL) else Host.addrOf (k + sZ) := by
  simp only [PcOk, hev] at hpc
  rw [hpc, Nat.add_assoc, hnext]
  cases pos <;> simp only [Bool.false_eq_true, ↓reduceIte] at hlab ⊢ <;> rw [hlab] <;>
    by_cases h : P <;> simp [h]

/-- **A block that writes lane `j`** with `A`'s lane XOR word `B + j`, and branches on word
`B + j + 1`. -/
theorem lane_block {k : Nat} {m0 m : MachineData}
    (hstk : StackOk m0 NativeRustcVmX64.keccak256WordsStack) {L : List (Nat × BitVec 64)}
    (hL : LowSlots L) {R R' : List (Reg64 × BitVec 64)} {w : Nat → UInt64} {cnt : Nat}
    {A : KeccakState} {B j : Nat} (hj : j < 25) (hc : Ctx m0 L R 8 m)
    (hl : Lanes m0 m.dmem (pre A w B j)) {rs : List (BitVec 64 × Nat)}
    (hb : rs[0]? = some (frame m0, 296)) (hwf : (Env.ofMachine m rs).WF) {S0 : SState}
    (hm0 : Match (Env.ofMachine m rs) S0 m) {blk : List Directive} {s : Nat} {S : SState}
    {xx : Exit} (hk : blk.IsInfixAt Host.prog (k + s)) (hx : exec blk S0 = some (S, xx))
    {v : Sym} (hmem : S.mem = [⟨0, 40 + 8 * j, 8, v⟩])
    (hv : v.eval (Env.ofMachine m rs) = (Keccak.lane A j ^^^ w (B + j)).toBitVec)
    (hrsp : S.reg .rsp = some (.ptr 0 8))
    (hR : ∀ m', Match (Env.ofMachine m rs) S m' → RegsAt m' R')
    {c : SBool} {lbl : Label} (hexit : xx = .cond c lbl) {pos : Bool}
    (hev : c.eval (Env.ofMachine m rs) = (pos == decide (B + (j + 1) < cnt)))
    {sL sZ : Nat} (hlab : Labels.label lbl = Host.addrOf (k + if pos then sL else sZ))
    (hnext : s + blk.length = if pos then sZ else sL) :
    Eventually (step1 Host.exe) (LaneG m0 k L R' w cnt A B (j + 1) sL sZ)
      ⟨m, Host.addrOf (k + s)⟩ := by
  refine exec_then hk hx hwf (fun l h => by rw [hexit] at h; cases h) hm0
    fun st hm hpc => .done _ ⟨?_, ?_, ?_⟩
  · exact ctx_step hstk hL hc hm hwf hb hrsp
      (by rw [hmem]; simp [bodyW]; omega) (hR _ hm)
  · have := lanes_step hm hb (j := j) (v := v) (by rw [hmem]; simp [firstOverlap])
      (fun w hw _ => by rw [hmem, List.mem_singleton] at hw; subst hw; exact .inr ⟨rfl, rfl⟩) hl hv
    rwa [pre_succ] at this
  · rw [hexit] at hpc
    exact branch_pc hev hlab hnext hpc

end

end NativeRustcVmX64.WordsHash
