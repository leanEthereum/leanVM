module

public import NativeRustcVmArm.KeccakGkr.Common
public import NativeRustcVmArm.KeccakGkr.LinearTranspose.Exec
public import NativeRustcVm.KeccakGkr.Transpose
import Mathlib.Tactic.IntervalCases

/-!
# `linear_transpose`: the body's context

The entry's arguments (`wA` the weights, `gA` `g`, `cA` the columns, `oA` the output), the regions
it writes (`wsR`) and reads (`rsR`), the prologue's slots, the body (`Body`: `Frame` of the
80-byte frame) and the registers holding the arguments (`Ctx`). What the loops fill, by linear
index (`gF`, `cF`, `oF`, after `NativeRustcVm.KeccakGkr.gW`, `colW`, `outW`). Reading the weights
(`w_at`) and `KECCAK_RHO` (`load_rho`).
-/

namespace NativeRustcVmArm.KeccakGkr.LinearTranspose

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVm (Region)
open NativeRustcVm.KeccakGkr (gW colW outW weightsBytes)

@[expose] public section

/-- The weights `w`. -/
abbrev wA (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
/-- `g`. -/
abbrev gA (m0 : MachineData) : BitVec 64 := m0.regs.X1.toBitVec
/-- The columns. -/
abbrev cA (m0 : MachineData) : BitVec 64 := m0.regs.X2.toBitVec
/-- The output. -/
abbrev oA (m0 : MachineData) : BitVec 64 := m0.regs.X3.toBitVec

/-- The regions `linear_transpose` writes. -/
def wsR (m0 : MachineData) : List Region :=
  [⟨gA m0, weightsBytes⟩, ⟨cA m0, 5120⟩, ⟨oA m0, weightsBytes⟩]

/-- The regions it reads. -/
def rsR [Labels] (m0 : MachineData) : List Region := [⟨wA m0, weightsBytes⟩, rhoRegion]

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(72, .X19), (64, .X20), (56, .X21), (48, .X22), (40, .X23), (32, .X24), (24, .X25), (16, .X26),
    (0, .X30)]

/-- The body: the 80-byte frame. -/
abbrev Body (m0 st : MachineData) : Prop := Frame m0 80 linearTransposeStack slots (wsR m0) st

/-- `g`'s entry `i`. -/
def gF (ws : Array EW) (i : Nat) : EW := gW ws (i / 64) (i % 64)
/-- The columns' entry `i`. -/
def cF (ws : Array EW) (i : Nat) : EW := colW ws (i / 64) (i % 64)
/-- The output's entry `i`. -/
def oF (ws : Array EW) (i : Nat) : EW := outW ws (i / 64) (i % 64)

/-- **The body's context**: a body, the arguments in X19 to X22. -/
structure Ctx (m0 st : MachineData) : Prop where
  body : Body m0 st
  x19 : st.regs.X19 = m0.regs.X2
  x20 : st.regs.X20 = m0.regs.X1
  x21 : st.regs.X21 = m0.regs.X3
  x22 : st.regs.X22 = m0.regs.X0

end

public section

variable [Labels] {ws : Array EW} {m0 st : MachineData}

omit [Labels] in
/-- The callee-saved registers the prologue does not save. -/
theorem free_ok : ∀ r, calleeSaved r = true → r ∉ slots.map (·.2) → r ∈ [XReg.X27, .X28, .X29] := by
  intro r hr hn
  cases r <;> simp_all [calleeSaved, slots]

omit [Labels] in
theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 80 := by decide

theorem pre_areas (hpre : LinearTransposePre ws m0) :
    Areas m0 linearTransposeStack (wsR m0) (rsR m0) := hpre.2.2.2.2

theorem wsOff (hpre : LinearTransposePre ws m0) : WsOff m0 linearTransposeStack (wsR m0) :=
  wsOff_of_areas (pre_areas hpre) hpre.1

/-- **An element of the weights**, in a body. -/
theorem w_at (hpre : LinearTransposePre ws m0) (hb : Body m0 st) {i : Nat} (hi : i < 1600) :
    NativeRustcVm.EWAt st.dmem (wA m0 + BitVec.ofNat 64 (16 * i)) (ws.getD i 0) := by
  obtain ⟨hS, -, hsz, hw, hA⟩ := hpre
  have hi' : i < ws.toList.length := by simp [hsz, LeanVM.Protocol.Verifier.keccakBits]; omega
  have h := NativeRustcVm.EWsAt.getElem hw hi'
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hi'), Option.getD_some]
  simp only [Array.getElem_toList] at h
  exact hb.bytesAt hA hS (r := ⟨wA m0, weightsBytes⟩) (by simp)
    (by rw [NativeRustcVm.length_ewBytes]; show 16 * i + 16 ≤ 25600; omega) h

/-! ## `KECCAK_RHO` -/

omit [Labels] in
theorem rhoBytes_length : rhoBytes.length = 100 := by decide

omit [Labels] in
theorem rho_lt {l : Nat} (hl : l < 25) : keccakRhoW.getD l 0 < 64 := by
  interval_cases l <;> decide

omit [Labels] in
theorem rho_word {l : Nat} (hl : l < 25) :
    BitVec.ofInt 64 (Int.ofBytes ((List.range 4).map fun i ↦ rhoBytes.getD (4 * l + i) 0)) =
      BitVec.ofNat 64 (keccakRhoW.getD l 0) := by
  interval_cases l <;> decide

/-- `KECCAK_RHO` in a body. -/
theorem rho_at (hpre : LinearTransposePre ws m0) (hb : Body m0 st) :
    NativeRustcVm.BytesAt st.dmem rhoAddr rhoBytes := by
  obtain ⟨hS, hrho, -, -, hA⟩ := hpre
  have h := hb.bytesAt hA hS (r := rhoRegion) (o := 0) (by simp)
    (by rw [rhoBytes_length]; rfl) (by rw [NativeRustcVm.addr_add_zero]; exact hrho)
  rwa [NativeRustcVm.addr_add_zero] at h

/-- **ρ of a lane**, loaded as a `u32`. -/
theorem load_rho {env : Env} {r : Nat} (hb : env.base r = rhoAddr)
    (h : NativeRustcVm.BytesAt env.mem0 rhoAddr rhoBytes) {l : Nat} (hl : l < 25) :
    env.load r (4 * l) 4 = BitVec.ofNat 64 (keccakRhoW.getD l 0) := by
  rw [← rho_word hl]
  unfold Env.load
  congr 2
  refine List.map_congr_left fun i hi ↦ ?_
  have hi : i < 4 := List.mem_range.mp hi
  have hlt : 4 * l + i < rhoBytes.length := by rw [rhoBytes_length]; omega
  rw [hb, h _ hlt, Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
    Option.getD_some]

omit [Labels] in
/-- An index scaled by `4` (`[xn, xm, lsl #2]`). -/
theorem memExtend2_toNat (x : BitVec 64) :
    (BitVec.ofInt 64 (x.apply_mem_extend ⟨.UXTX, .E2⟩)).toNat = x.toNat * 4 % 2 ^ 64 := by
  simp only [BitVec.apply_mem_extend, BitVec.unsigned]
  rw [Int.shiftLeft_eq, BitVec.toNat_ofInt]
  push_cast
  omega

end

end NativeRustcVmArm.KeccakGkr.LinearTranspose
