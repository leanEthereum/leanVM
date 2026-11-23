module

public import NativeRustcVmArm.Code.Vm.KeccakF.Names
public import NativeRustcVmArm.Keccak.WordsHash.Tail
public import NativeRustcVmArm.Keccak.WordsHash.Call
public import NativeRustcVmArm.Keccak.WordsHash.PadVals

/-!
# `keccak256_words::<hash_words's closure>`: the padding and the last permutation

`pad_run`: from the padding block (`PadAt`), the machine inevitably reaches the epilogue
(`EpiAt`) with the lanes `keccakF1600 (lastB m0)`, `lastB` the whole blocks' state with the last
block's words and the padding XORed into the rate (`finalState`'s argument). The padding block
(`b76`, run as `pad{t}` for the padded lane `t = (len % 136) / 8`, `pad_exec`) XORs word `base + 16`
and `PAD_LAST` into lane 16 and `PAD_FIRST` into lane `t` (`pad_lanes`), then calls `keccak_f`
(`call_kf`).
-/

namespace NativeRustcVmArm.WordsHash

open NativeRustcArm NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcArm.KeccakF (WordAt wordAt_of_eq wordAt_write wordAt_keep load_of_wordAt)
open NativeRustcVm.Keccak Vm.Keccak256WordsOfHashWords

@[expose] public section

/-- The padding word's shift, `(r & 7) << 3`. -/
def padU : Sym :=
  .un (.ubfm 61 2) .W64 (.bin .sub .W64 (.reg .X20) (.bin .mul .W64 (.reg .X24) (.lit 136)))

/-- The padding word `1 << ((r & 7) << 3)`. -/
def padLow : Sym := .bin .lslv .W64 (.lit 1) padU

/-- Lane 16 after the padding, the padded lane another. -/
def v16 : Sym := .bin .eor .W64 (.bin .eor .W64 (.load 0 136 8) (.reg .X8)) (.lit 9223372036854775808)

/-- The padded lane `t < 16`. -/
def vt (t : Nat) : Sym := .bin .eor .W64 (.load 0 (8 + 8 * t) 8) padLow

/-- Lane 16 after the padding, the padded lane lane 16. -/
def v16c : Sym :=
  .bin .eor .W64 (.bin .eor .W64 (.bin .eor .W64 (.load 0 136 8) (.reg .X8)) padLow)
    (.lit 9223372036854775808)

/-- The padding block's writes for the padded lane `t`. -/
def padMem (t : Nat) : List Write :=
  if t = 16 then [⟨0, 136, 8, v16c⟩] else [⟨0, 136, 8, v16⟩, ⟨0, 8 + 8 * t, 8, vt t⟩]

/-- The lanes before the last permutation. -/
def lastB (m0 : MachineData) : KeccakState :=
  Native.Keccak.Proof.xorRate (stA m0) fun k => word m0 (base m0 + k) ^^^ padLane m0.regs.X2.toNat k

/-- **At the epilogue**: the lanes `keccakF1600 (lastB m0)`. -/
def EpiAt [Host] (m0 : MachineData) (k : Nat) (st : MachineState) : Prop :=
  Ctx m0 st.data ∧ Lanes m0 st.data (Keccak.lane (keccakF1600 (lastB m0))) ∧
    st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b77Offset)

end

public section

/-- The padding block from the padded lane `t`. -/
theorem pad_exec (t : Nat) (ht : t < 17) : ∃ S, exec b76 (startPad t) =
    some (S, .call NativeRustcVmArm.Vm.KeccakF.entryLabel) ∧ S.mem = padMem t ∧ S.sp = .ptr 0 0 ∧
    S.reg .X0 = some (.ptr 0 8) ∧ AllOf (fun r => S.reg r = some (.reg r)) ctxRegs := by
  match t, ht with
  | 0, _ => exact ⟨_, pad0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 1, _ => exact ⟨_, pad1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 2, _ => exact ⟨_, pad2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 3, _ => exact ⟨_, pad3, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 4, _ => exact ⟨_, pad4, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 5, _ => exact ⟨_, pad5, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 6, _ => exact ⟨_, pad6, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 7, _ => exact ⟨_, pad7, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 8, _ => exact ⟨_, pad8, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 9, _ => exact ⟨_, pad9, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 10, _ => exact ⟨_, pad10, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 11, _ => exact ⟨_, pad11, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 12, _ => exact ⟨_, pad12, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 13, _ => exact ⟨_, pad13, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 14, _ => exact ⟨_, pad14, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 15, _ => exact ⟨_, pad15, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 16, _ => exact ⟨_, pad16, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | _ + 17, h => exact absurd h (by omega)

theorem fo_neg {r o n : Nat} {w : Write} {ws : List Write}
    (h : ¬ (w.r = r ∧ w.off < o + n ∧ o < w.off + w.n)) :
    firstOverlap r o n (w :: ws) = firstOverlap r o n ws := by
  simp [firstOverlap, h]

theorem fo_pos {r o n : Nat} {w : Write} {ws : List Write}
    (h : w.r = r ∧ w.off < o + n ∧ o < w.off + w.n) : firstOverlap r o n (w :: ws) = some w := by
  simp [firstOverlap, h]

theorem lit_hi : BitVec.ofNat 64 9223372036854775808 = (0x8000000000000000 : UInt64).toBitVec :=
  rfl

theorem xor_toBitVec (a b : UInt64) : a.toBitVec ^^^ b.toBitVec = (a ^^^ b).toBitVec := rfl

variable [Labels] {env : Env} {S : SState} {m : MachineData}

/-- **The lanes after the padding block.** -/
theorem pad_lanes {m0 : MachineData} (hm : Match env S m)
    (hb : env.regions[0]? = some (frame m0, 288)) {t : Nat} (ht : t < 17) (hmem : S.mem = padMem t)
    {f : Nat → UInt64}
    (hl : ∀ i < 25, WordAt env.mem0 (frame m0 + BitVec.ofNat 64 (8 + 8 * i)) (f i).toBitVec)
    {x8 low : UInt64} (h8 : env.regs .X8 = x8.toBitVec) (hlow : padLow.eval env = low.toBitVec) :
    Lanes m0 m (fun i => if i = 16 then f 16 ^^^ x8 ^^^ (if t = 16 then low else 0) ^^^
      0x8000000000000000 else if i = t then f i ^^^ low else f i) := by
  have hbase : env.base 0 = frame m0 := Env.base_eq hb
  have hload : ∀ i < 25, env.load 0 (8 + 8 * i) 8 = (f i).toBitVec := fun i hi =>
    load_of_wordAt (r := 0) (by rw [hbase]; exact hl i hi)
  intro i hi
  by_cases h16 : t = 16
  · subst h16
    simp only [padMem, ↓reduceIte] at hmem
    by_cases hi16 : i = 16
    · subst hi16
      simp only [↓reduceIte]
      refine wordAt_of_eq (wordAt_write hm hb (by omega) (by rw [hmem]; rfl)) ?_
      simp only [v16c, Sym.eval, eor64]
      rw [show env.load 0 136 8 = (f 16).toBitVec from hload 16 (by omega), h8, hlow, lit_hi]
      rfl
    · simp only [hi16, ↓reduceIte]
      refine wordAt_keep hm hb (by omega) ?_ (hl i hi)
      rw [hmem, fo_neg (by dsimp only; omega)]
      rfl
  · have hmem' : S.mem = [⟨0, 136, 8, v16⟩, ⟨0, 8 + 8 * t, 8, vt t⟩] := by
      rw [hmem]
      simp only [padMem, h16, ↓reduceIte]
    by_cases hi16 : i = 16
    · subst hi16
      simp only [↓reduceIte, h16]
      refine wordAt_of_eq (wordAt_write hm hb (by omega) (by rw [hmem']; rfl)) ?_
      simp only [v16, Sym.eval, eor64]
      rw [show env.load 0 136 8 = (f 16).toBitVec from hload 16 (by omega), h8, lit_hi]
      simp only [UInt64.xor_zero]
      rfl
    · by_cases hit : i = t
      · subst hit
        simp only [hi16, ↓reduceIte]
        refine wordAt_of_eq (wordAt_write hm hb (by omega) (by
          rw [hmem', fo_neg (by dsimp only; omega), fo_pos (by dsimp only; omega)])) ?_
        simp only [vt, Sym.eval, eor64]
        rw [hload i hi, hlow]
        rfl
      · simp only [hi16, hit, ↓reduceIte]
        refine wordAt_keep hm hb (by omega) ?_ (hl i hi)
        rw [hmem', fo_neg (by dsimp only; omega), fo_neg (by dsimp only; omega)]
        rfl

end

end NativeRustcVmArm.WordsHash
