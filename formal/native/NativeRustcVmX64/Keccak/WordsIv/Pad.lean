module

public import NativeRustcVmX64.Keccak.WordsIv.Tail
public import NativeRustcVmX64.Keccak.WordsHash.Pad
public import NativeRustcVmX64.Code.Vm.KeccakF.Names

/-!
# `keccak256_words::<fiat_shamir_iv's closure>` (x86-64): the padding and the last permutation

`pad_run`: from the padding block (`b110`, lane 16's word in RAX), the machine inevitably reaches
the epilogue (`EpiAt`) with the lanes `keccakF1600 (lastI m0)`, `lastI` the whole blocks' state
with the last block's words and the padding XORed into the rate (`finalState`'s argument). The
block runs in three parts: `padA` XORs lane 16's word and computes, from `len` in the frame, the
bytes past the whole blocks `r = len % 136` (`remF_val`), the padding word `1 << 8 (r % 8)`
(`WordsHash.padWord_val`) and the padded lane's offset `8 t`, `t = r / 8` (`and248_val`); `padB t`
XORs the padding word into lane `t`; `padC` XORs `0x80` into byte 135 (`WordsHash.lanes_xorb`)
and calls `keccak_f` (`WordsHash.call_kf`).
-/

namespace NativeRustcVmX64.WordsIv

open NativeRustcX64 NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcX64.KeccakF (WordAt wordAt_of_eq load_of_wordAt)
open NativeRustcVm.Keccak (padLane wordBlocks)
open NativeRustcVmX64.WordsHash (frame Ctx Lanes pre RegsAt ctx_step lanes_stepB lanes_congr
  laneW bodyW pre_succ lane_lastG lanes_xorb call_kf oct32 padWord_val xor64 add64)
open Vm.Keccak256WordsOfFiatShamirIv

@[expose] public section

/-- The bytes past the whole blocks, as rustc computes them from `len` at 32 bits. -/
def remF (x : BitVec 64) : BitVec 64 :=
  BinOp.apply .sub .W32 x (UnOp.apply .trunc .W32 (BinOp.apply .add .W64
    (BinOp.apply .shl .W32 (BinOp.apply .shr .W64 (BinOp.apply .mul .W64
      (BitVec.ofNat 64 4042322161) (UnOp.apply .trunc .W32 x)) (BitVec.ofNat 64 39))
      (BitVec.ofNat 64 7))
    (BinOp.apply .mul .W64 (UnOp.apply .trunc .W32 (BinOp.apply .shr .W64 (BinOp.apply .mul .W64
      (BitVec.ofNat 64 4042322161) (UnOp.apply .trunc .W32 x)) (BitVec.ofNat 64 39)))
      (BitVec.ofNat 64 8))))

/-- The lanes before the last permutation. -/
def lastI (m0 : MachineData) : KeccakState :=
  Native.Keccak.Proof.xorRate (stA m0) fun k => wv m0 (17 * nb m0 + k) ^^^ padLane (lenI m0) k

/-- **At the epilogue**: the lanes `keccakF1600 (lastI m0)`. -/
def EpiAt [Host] (m0 : MachineData) (k : Nat) (st : MachineState) : Prop :=
  Ctx m0 (slotsI m0) [] 8 st.data ∧ Lanes m0 st.data.dmem (Keccak.lane (keccakF1600 (lastI m0))) ∧
    st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b111Offset)

end

public section

/-- **The bytes past the whole blocks**, `len % 136`. -/
theorem remF_val {len : Nat} (h : len < 2 ^ 32) :
    remF (BitVec.ofNat 64 len) = BitVec.ofNat 64 (len % 136) := by
  unfold remF
  rw [nb_val h, rem_val h]

/-- The padding word's XOR into lane `t`. -/
theorem padB_exec (t : Nat) (ht : t < 17) : ∃ S, exec padBCode (startPad t) = some (S, .fall) ∧
    S.mem = [⟨0, 40 + 8 * t, 8, .bin .xor .W64 (.load 0 (40 + 8 * t) 8) (.reg .rax)⟩] ∧
    S.reg .rsp = some (.ptr 0 8) := by
  match t, ht with
  | 0, _ => exact ⟨_, padB0, rfl, rfl⟩
  | 1, _ => exact ⟨_, padB1, rfl, rfl⟩
  | 2, _ => exact ⟨_, padB2, rfl, rfl⟩
  | 3, _ => exact ⟨_, padB3, rfl, rfl⟩
  | 4, _ => exact ⟨_, padB4, rfl, rfl⟩
  | 5, _ => exact ⟨_, padB5, rfl, rfl⟩
  | 6, _ => exact ⟨_, padB6, rfl, rfl⟩
  | 7, _ => exact ⟨_, padB7, rfl, rfl⟩
  | 8, _ => exact ⟨_, padB8, rfl, rfl⟩
  | 9, _ => exact ⟨_, padB9, rfl, rfl⟩
  | 10, _ => exact ⟨_, padB10, rfl, rfl⟩
  | 11, _ => exact ⟨_, padB11, rfl, rfl⟩
  | 12, _ => exact ⟨_, padB12, rfl, rfl⟩
  | 13, _ => exact ⟨_, padB13, rfl, rfl⟩
  | 14, _ => exact ⟨_, padB14, rfl, rfl⟩
  | 15, _ => exact ⟨_, padB15, rfl, rfl⟩
  | 16, _ => exact ⟨_, padB16, rfl, rfl⟩
  | _ + 17, h => exact absurd h (by omega)

variable [Host]

/-- **From the padding to the epilogue.** -/
theorem pad_run (hkf : Spec (label NativeRustcVmX64.Vm.KeccakF.entryLabel) NativeRustcVmX64.KeccakFPre
      NativeRustcVmX64.KeccakFPost) {k : Nat} (hp : Placed code k) {m0 : MachineData}
    (g : Geo m0) {R : List (Reg64 × BitVec 64)} {st : MachineState}
    (h : ValAt m0 k R (stA m0) (bT m0) 16 NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b110Offset st) :
    Eventually (step1 Host.exe) (EpiAt m0 k) st := by
  obtain ⟨hc, hl, hrax, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hrax hpc
  subst hpc
  have hb := ic hp b110_in_code (List.cons_ne_nil _ _)
  rw [show b110 = padACode ++ (padBCode ++ padCCode) from rfl] at hb
  obtain ⟨hkA, hkBC⟩ := List.IsInfixAt.append hb
  obtain ⟨hkB, hkC⟩ := List.IsInfixAt.append hkBC
  rw [show k + NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b110Offset + padACode.length = k + NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b110Offset + padACode.length from rfl] at hkB hkC
  rw [show k + NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b110Offset + padACode.length + padBCode.length = k + NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b110Offset + padACode.length + padBCode.length from rfl] at hkC
  have hlen := len_small g
  have hr136 : lenI m0 % 136 < 136 := Nat.mod_lt _ (by decide)
  obtain ⟨t, ht⟩ : ∃ t, t = lenI m0 % 136 / 8 := ⟨_, rfl⟩
  have ht17 : t < 17 := by omega
  -- `padA`
  obtain ⟨hwf, hm⟩ := main_env g.stk hc (vars := fun _ => 0) (ret := 0)
  have hlen8 : (Env.ofMachine m [(frame m0, 296)] (fun _ => 0) 0).load 0 24 8 =
      BitVec.ofNat 64 (lenI m0) := by
    rw [load_of_wordAt (r := 0) (off := 24) hc.slots.2.1]
    exact bv_eq_ofNat _
  refine exec_then hkA padA hwf (fun _ h => by cases h) hm fun st1 hm1 hpc1 => ?_
  have hc1 : Ctx m0 (slotsI m0) [] 8 st1.data :=
    ctx_step g.stk (slotsI_low m0) hc hm1 hwf rfl rfl rfl trivial
  have hl1 : Lanes m0 st1.data.dmem (pre (stA m0) (wv m0) (bT m0) 17) := by
    have := lanes_stepB hm1 rfl (j := 16) rfl rfl hl
      (x := Keccak.lane (stA m0) 16 ^^^ wv m0 (bT m0 + 16)) (by
        show BinOp.apply .xor .W64
          ((Env.ofMachine m [(frame m0, 296)]).load 0 168 8) (m.regs.get64 .rax) = _
        rw [xor64, hrax, load_of_wordAt (r := 0) (off := 168) (hl 16 (by omega))]
        simp [pre])
    rwa [pre_succ] at this
  have hrdx : st1.data.regs.get64 .rdx = BitVec.ofNat 64 (8 * t) := by
    rw [hm1.regs .rdx _ rfl]
    show BinOp.apply .and .W32 (remF ((Env.ofMachine m [(frame m0, 296)]).load 0 24 8))
      (BitVec.ofNat 64 248) = _
    rw [hlen8, remF_val (len := lenI m0) hlen, and248_val _ hr136, ht]
  have hax : st1.data.regs.get64 .rax =
      ((1 : UInt64) <<< (8 * (lenI m0 % 136 % 8)).toUInt64).toBitVec := by
    rw [hm1.regs .rax _ rfl]
    show BinOp.apply .shl .W64 (BitVec.ofNat 64 1)
      (oct32 (remF ((Env.ofMachine m [(frame m0, 296)]).load 0 24 8))) = _
    rw [hlen8, remF_val (len := lenI m0) hlen, padWord_val _ hr136]
  simp only [PcOk] at hpc1
  -- `padB t`
  obtain ⟨SB, hxB, hmemB, hrspB⟩ := padB_exec t ht17
  let env2 := Env.ofMachine st1.data [(frame m0, 296)]
  have hwf2 : env2.WF := WordsHash.frame_wf g.stk hc1.kept
  have hm2 : Match env2 (startPad t) st1.data := by
    refine match_ofMachine ⟨rfl, trivial⟩ ⟨WordsHash.rsp_eval hc1.rsp rfl, trivial⟩ trivial trivial
      ⟨?_, trivial⟩
    show BinOp.apply .add .W64 (env2.base 0 + BitVec.ofInt 64 8) (st1.data.regs.get64 .rdx) =
      env2.base 0 + BitVec.ofInt 64 (8 + 8 * (t : Int))
    rw [hrdx, add64, show (8 + 8 * (t : Int)) = ((8 + 8 * t : Nat) : Int) by omega,
      BitVec.ofInt_natCast, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, BitVec.add_assoc,
      BitVec.ofNat_add]
  refine exec_at hkB hxB hwf2 (fun _ h => by cases h) hpc1 hm2 fun st2 hm2' hpc2 => ?_
  have hc2 : Ctx m0 (slotsI m0) [] 8 st2.data :=
    ctx_step g.stk (slotsI_low m0) hc1 hm2' hwf2 rfl hrspB (by rw [hmemB]; simp [bodyW]; omega)
      trivial
  have hl2 := lanes_stepB hm2' rfl (j := t)
    (v := .bin .xor .W64 (.load 0 (40 + 8 * t) 8) (.reg .rax)) (by rw [hmemB]; simp [firstOverlap])
    (by rw [hmemB]; simp [laneW]) hl1
    (x := pre (stA m0) (wv m0) (bT m0) 17 t ^^^
      (1 : UInt64) <<< (8 * (lenI m0 % 136 % 8)).toUInt64) (by
      show BinOp.apply .xor .W64 (env2.load 0 (40 + 8 * t) 8) (st1.data.regs.get64 .rax) = _
      rw [xor64, hax, load_of_wordAt (r := 0) (hl1 t (by omega))]
      rfl)
  simp only [PcOk] at hpc2
  -- `padC`, and the call
  obtain ⟨hwf3, hm3⟩ := main_env g.stk hc2 (vars := fun _ => 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b110Offset + padACode.length + padBCode.length + padCCode.length)).toBitVec)
  refine exec_at hkC padC hwf3 (fun _ _ => rfl) hpc2 hm3 fun st3 hm3' hpc3 => ?_
  have hc3 : Ctx m0 (slotsI m0) [] 0 st3.data :=
    ctx_step g.stk (slotsI_low m0) hc2 hm3' hwf3 rfl rfl (by decide) trivial
  have hl3 := lanes_xorb hm3' rfl rfl hl2
  have hrdi : st3.data.regs.get64 .rdi = frame m0 + BitVec.ofNat 64 40 := by
    rw [hm3'.regs .rdi _ rfl]
    simp [Sym.eval]
  refine call_kf hkf g.stk g.rc g.got (slotsI_low m0) hc3 (lanes_congr hl3 fun i hi =>
    lane_lastG _ _ _ _ ht hi) hrdi hpc3 fun st4 hpc4 hc4 hl4 _ => .done _ ⟨hc4, hl4, ?_⟩
  rw [hpc4]
  rfl

end

end NativeRustcVmX64.WordsIv
