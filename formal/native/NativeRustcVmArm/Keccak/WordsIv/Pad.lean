module

public import NativeRustcVmArm.Code.Vm.KeccakF.Names
public import NativeRustcVmArm.Keccak.WordsIv.Tail
public import NativeRustcVmArm.Keccak.WordsIv.BlocksPad
public import NativeRustcVmArm.Keccak.WordsHash.Pad

/-!
# `keccak256_words::<fiat_shamir_iv's closure>`: the padding and the last permutation

`pad_run`: from the padding block with lane 16's word in X0 (`X0At … 631`), the machine
inevitably reaches the epilogue (`EpiAt`) with the lanes `keccakF1600 (lastI m0)`, `lastI` the
whole blocks' state with the last block's words and the padding XORed into the rate. The padding
block (`b108`, run as `pad{t}` for the padded lane `t = (len % 136) / 8`, `pad_exec`) XORs X0 and
`PAD_LAST` into lane 16 and `PAD_FIRST` into lane `t` (`pad_lanes`), then calls `keccak_f`
(`call_kf`).
-/

namespace NativeRustcVmArm.WordsIv

open NativeRustcArm NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcArm.KeccakF (WordAt wordAt_of_eq wordAt_write wordAt_keep load_of_wordAt)
open NativeRustcVmArm.WordsHash (frame nb Lanes pre lanes_congr eor64 add64 fo_neg fo_pos lit_hi
  sub_mul_val low_val_aux memExtE0 nb_val)
open NativeRustcVm.Keccak (wordBlocks padLane)
open Vm.Keccak256WordsOfFiatShamirIv

@[expose] public section

/-- The padding word `1 << ((r & 7) << 3)`. -/
def padLow : Sym := .bin .lslv .W64 (.lit 1) (.un (.ubfm 61 2) .W64 remS)

/-- Lane 16 after the padding, the padded lane another. -/
def v16 : Sym := .bin .eor .W64 (.bin .eor .W64 (.load 0 136 8) (.reg .X0)) (.lit 9223372036854775808)

/-- The padded lane `t < 16`. -/
def vt (t : Nat) : Sym := .bin .eor .W64 (.load 0 (8 + 8 * t) 8) padLow

/-- Lane 16 after the padding, the padded lane lane 16. -/
def v16c : Sym :=
  .bin .eor .W64 (.bin .eor .W64 (.bin .eor .W64 (.load 0 136 8) (.reg .X0)) padLow)
    (.lit 9223372036854775808)

/-- The padding block's writes for the padded lane `t`. -/
def padMem (t : Nat) : List Write :=
  if t = 16 then [⟨0, 136, 8, v16c⟩] else [⟨0, 136, 8, v16⟩, ⟨0, 8 + 8 * t, 8, vt t⟩]

/-- The lanes before the last permutation. -/
def lastI (m0 : MachineData) : KeccakState :=
  Native.Keccak.Proof.xorRate (stI m0) fun k => wv m0 (base m0 + k) ^^^ padLane m0.regs.X2.toNat k

/-- **At the epilogue**: the lanes `keccakF1600 (lastI m0)`. -/
def EpiAt [Host] (m0 : MachineData) (k : Nat) (st : MachineState) : Prop :=
  Ctx m0 st.data ∧ Lanes m0 st.data (Keccak.lane (keccakF1600 (lastI m0))) ∧
    st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.b109Offset)

end

public section

theorem and248_aux : ∀ r < 136,
    BinOp.apply .and .W64 (BitVec.ofNat 64 r) (BitVec.ofNat 64 248) =
      BitVec.ofNat 64 (8 * (r / 8)) := by
  decide +kernel

/-- The padding block from the padded lane `t`. -/
theorem pad_exec (t : Nat) (ht : t < 17) : ∃ S, exec b108 (startPad t) =
    some (S, .call NativeRustcVmArm.Vm.KeccakF.entryLabel) ∧ S.mem = padMem t ∧ S.sp = .ptr 0 0 ∧
    S.reg .X0 = some (.ptr 0 8) ∧ AllOf (fun r => S.reg r = some (.reg r)) ctxRegs := by
  match t, ht with
  | 0, _ => exact ⟨_, pad0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 1, _ => exact ⟨_, pad1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 2, _ => exact ⟨_, pad2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 3, _ => exact ⟨_, pad3, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 4, _ => exact ⟨_, pad4, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 5, _ => exact ⟨_, pad5, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 6, _ => exact ⟨_, pad6, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 7, _ => exact ⟨_, pad7, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 8, _ => exact ⟨_, pad8, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 9, _ => exact ⟨_, pad9, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 10, _ => exact ⟨_, pad10, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 11, _ => exact ⟨_, pad11, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 12, _ => exact ⟨_, pad12, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 13, _ => exact ⟨_, pad13, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 14, _ => exact ⟨_, pad14, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 15, _ => exact ⟨_, pad15, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | 16, _ => exact ⟨_, pad16, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | _ + 17, h => exact absurd h (by omega)

/-- **The lanes before the last permutation.** -/
theorem lane_lastI (m0 : MachineData) {t : Nat} (ht : t = m0.regs.X2.toNat % 136 / 8) {i : Nat}
    (hi : i < 25) :
    (if i = 16 then pre (stI m0) (wv m0) (base m0) 16 16 ^^^ wv m0 (base m0 + 16) ^^^
        (if t = 16 then (1 : UInt64) <<< (8 * (m0.regs.X2.toNat % 136 % 8)).toUInt64 else 0) ^^^
        0x8000000000000000
      else if i = t then pre (stI m0) (wv m0) (base m0) 16 i ^^^
        (1 : UInt64) <<< (8 * (m0.regs.X2.toNat % 136 % 8)).toUInt64
      else pre (stI m0) (wv m0) (base m0) 16 i) = Keccak.lane (lastI m0) i := by
  have ht17 : t < 17 := by omega
  rw [lastI, Native.Keccak.Proof.lane_xorRate _ _ hi, padLane, ← ht]
  simp only [pre]
  by_cases h16 : i = 16
  · subst h16
    by_cases ht16 : t = 16
    · simp [ht16, UInt64.xor_assoc]
    · simp [ht16, Ne.symm ht16, UInt64.xor_assoc]
  · by_cases hit : i = t
    · subst hit
      simp [h16, show i < 17 by omega, show i < 16 by omega, UInt64.xor_assoc]
    · by_cases h17 : i < 17
      · simp [h16, hit, h17, show i < 16 by omega]
      · simp [h16, hit, h17, show ¬ i < 16 by omega]

variable [Labels] {env : Env} {S : SState} {m : MachineData}

/-- **The lanes after the padding block.** -/
theorem pad_lanes {m0 : MachineData} (hm : Match env S m)
    (hb : env.regions[0]? = some (frame m0, 288)) {t : Nat} (ht : t < 17) (hmem : S.mem = padMem t)
    {f : Nat → UInt64}
    (hl : ∀ i < 25, WordAt env.mem0 (frame m0 + BitVec.ofNat 64 (8 + 8 * i)) (f i).toBitVec)
    {x0 low : UInt64} (h0 : env.regs .X0 = x0.toBitVec) (hlow : padLow.eval env = low.toBitVec) :
    Lanes m0 m (fun i => if i = 16 then f 16 ^^^ x0 ^^^ (if t = 16 then low else 0) ^^^
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
      rw [show env.load 0 136 8 = (f 16).toBitVec from hload 16 (by omega), h0, hlow, lit_hi]
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
      rw [show env.load 0 136 8 = (f 16).toBitVec from hload 16 (by omega), h0, lit_hi]
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

public section

variable [Host]

/-- **From the padding to the epilogue.** -/
theorem pad_run (hkf : Spec (label NativeRustcVmArm.Vm.KeccakF.entryLabel) NativeRustcVmArm.KeccakFPre
      NativeRustcVmArm.KeccakFPost) {k : Nat} (hp : Placed code k)
    {m0 : MachineData} (g : Geo m0)
    (hrc : NativeRustcVmArm.RcAt m0 NativeRustcVmArm.keccak256WordsStack)
    {st : MachineState} (h : X0At m0 k .X24 (stI m0) (base m0) NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.b108Offset st) :
    Eventually (step1 Host.exe) (EpiAt m0 k) st := by
  obtain ⟨hc, hl, -, hx0, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hx0 hpc
  subst hpc
  have hlen := m0.regs.X2.toNat_lt
  have hnb : 136 * nb m0 ≤ m0.regs.X2.toNat := by unfold nb; omega
  have hr : m0.regs.X2.toNat - 136 * nb m0 = m0.regs.X2.toNat % 136 := by unfold nb; omega
  obtain ⟨t, ht⟩ : ∃ t, t = m0.regs.X2.toNat % 136 / 8 := ⟨_, rfl⟩
  have ht17 : t < 17 := by omega
  obtain ⟨S, hx, hmem, hsp, hS0, hregs⟩ := pad_exec t ht17
  let env := Env.ofMachine m [(frame m0, 288)]
  obtain ⟨hwf, -⟩ := frame_env g hc
  have hx20 : (m.regs.getXReg .X20).toBitVec = BitVec.ofNat 64 m0.regs.X2.toNat := by
    rw [hc.x20]; simp
  have hrem : remS.eval env = BitVec.ofNat 64 (m0.regs.X2.toNat % 136) := by
    show BinOp.apply .sub .W64 (m.regs.getXReg .X20).toBitVec
      (BinOp.apply .mul .W64 (UnOp.apply (.ubfm 7 63) .W64 (BinOp.apply .umulh .W64
        (m.regs.getXReg .X20).toBitVec (BitVec.ofNat 64 17361641481138401521)))
        (BitVec.ofNat 64 136)) = _
    rw [hx20, nb_val _ hlen, show m0.regs.X2.toNat / 136 = nb m0 from rfl, sub_mul_val hnb, hr]
  have hm : Match env (startPad t) m := by
    refine match_ofMachine ⟨rfl, fun _ => WordsHash.frame_aligned g.stk, trivial⟩
      (by rw [hc.sp]; simp [Sym.eval]) trivial trivial trivial ⟨?_, trivial⟩
    show BinOp.apply .add .W64 (env.base 0 + BitVec.ofInt 64 8)
      (UnOp.apply (.memExtend ⟨.UXTX, .E0⟩) .W64 (BinOp.apply .and .W64 (remS.eval env)
        (BitVec.ofNat 64 248))) = env.base 0 + BitVec.ofInt 64 (8 + 8 * (t : Int))
    rw [hrem, and248_aux _ (by omega), memExtE0, add64, ← ht,
      show (8 + 8 * (t : Int)) = ((8 + 8 * t : Nat) : Int) by omega, BitVec.ofInt_natCast,
      show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, BitVec.add_assoc, BitVec.ofNat_add]
  refine exec_then (ic hp b108_in_code (List.cons_ne_nil _ _)) hx hwf hm fun st1 hm1 hpc1 => ?_
  have hc1 : Ctx m0 st1.data := ctx_step g.stk hc hm1 hwf rfl hsp hregs fun w hw => by
    rw [hmem, padMem] at hw
    split at hw
    · rw [List.mem_singleton] at hw
      subst hw
      exact ⟨rfl, by decide⟩
    · rcases List.mem_pair.mp hw with rfl | rfl
      · exact ⟨rfl, by decide⟩
      · exact ⟨rfl, by simp only; omega⟩
  have hl1 : Lanes m0 st1.data (Keccak.lane (lastI m0)) := by
    refine lanes_congr (pad_lanes hm1 rfl ht17 hmem (fun i hi => hl i hi)
      (x0 := wv m0 (base m0 + 16)) hx0 ?_) fun i hi => lane_lastI m0 ht hi
    show BinOp.apply .lslv .W64 (BitVec.ofNat 64 1) (UnOp.apply (.ubfm 61 2) .W64 (remS.eval env)) = _
    rw [hrem, low_val_aux _ (by omega)]
  have hx0' : st1.data.regs.X0.toBitVec = frame m0 + BitVec.ofNat 64 8 :=
    (hm1.regs .X0 _ hS0).trans (by simp [Sym.eval])
  refine call_kf hkf g.stk hrc hc1 hl1 hx0' hpc1 fun st2 hpc2 hc2 hl2 _ => .done _ ⟨hc2, hl2, ?_⟩
  rw [hpc2, Nat.add_assoc, b108_next]

end

end NativeRustcVmArm.WordsIv
