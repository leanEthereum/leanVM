module

public import NativeRustcVmX64.Keccak.KeccakF.Inv
public import NativeRustcVmX64.Keccak.KeccakF.Blocks
public import NativeRustcX64.KeccakF.RoundLanes

/-!
# The loop body computes a round (x86-64)

`body_lanes`: where the loop body runs (`body`) in an environment whose registers and frame slots
hold the lanes `a` where the loop head keeps them (`laneRegs`, `laneSlots`) and whose round-constant
load (`rcSym`, the frame's copy indexed by the counter) is `rc`, the machine after it holds the
round's lanes (`roundCL a (parOf a) rc`, the column parities computed from the lanes) in the same
places. Each is an identity of XORs, AND-NOTs and rotations of the inputs, matched by `ac_nf` after
the round's lanes are written as 64-bit vectors; a few lanes per theorem (`laneRegsA`, …).
-/

namespace NativeRustcVmX64.KeccakF

open NativeRustcX64 NativeRustcX64.Sym NativeRustc.Keccak LeanVM.Semantics
open NativeRustcX64.KeccakF (WordAt wordAt_of_eq wordAt_write)

@[expose] public section

/-- θ's column parities of the lanes `a`. -/
def parOf (a : Nat → UInt64) (x : Nat) : UInt64 :=
  a x ^^^ a (x + 5) ^^^ a (x + 10) ^^^ a (x + 15) ^^^ a (x + 20)

theorem par_eq (A : KeccakState) : par A = parOf (Keccak.lane A) := rfl

/-- The round constant the body loads: the frame's copy at 224 plus 8 times the counter. -/
def rcSym : Sym := .loadx 0 224 (.bin .mul .W64 (.var 0) (.lit 8)) 8

/-- Lanes of `laneRegs`, part A. -/
def laneRegsA : List (Reg64 × Nat) := [(.r12, 3), (.r15, 6), (.r14, 7), (.r13, 8)]

/-- Lanes of `laneRegs`, part B. -/
def laneRegsB : List (Reg64 × Nat) := [(.r11, 11), (.rbp, 12), (.rdi, 13), (.r8, 15)]

/-- Lanes of `laneRegs`, part C. -/
def laneRegsC : List (Reg64 × Nat) := [(.rsi, 16), (.r9, 17), (.r10, 18)]

/-- Lanes of `laneSlots`, part A. -/
def laneSlotsA : List (Nat × Nat) := [(40, 0), (112, 1), (104, 2), (120, 4)]

/-- Lanes of `laneSlots`, part B. -/
def laneSlotsB : List (Nat × Nat) := [(56, 5), (48, 9), (32, 10), (8, 14)]

/-- Lanes of `laneSlots`, part C. -/
def laneSlotsC : List (Nat × Nat) := [(16, 19), (96, 20), (72, 21)]

/-- Lanes of `laneSlots`, part D. -/
def laneSlotsD : List (Nat × Nat) := [(88, 22), (80, 23), (24, 24)]

end

/-! The 64-bit operations of the body at the type `BitVec 64` (`sym_simp` leaves them at
`BitVec Width.W64.bits`, which `ac_nf` tells apart from the round's), and the rotations and
complements as irreducible atoms (`rotl`, `cmpl`): `ac_nf` compares atoms by unification, which
otherwise unfolds `rotateLeft` of large XORs. -/

@[expose] public section

/-- `x` rotated left by `n`, an atom for `ac_nf`. -/
@[irreducible] def rotl (x : BitVec 64) (n : Nat) : BitVec 64 := x.rotateLeft n

/-- `x`'s complement, an atom for `ac_nf`. -/
@[irreducible] def cmpl (x : BitVec 64) : BitVec 64 := ~~~x

end

public section

theorem rotl_eq (x : BitVec 64) (n : Nat) : x.rotateLeft n = rotl x n := by
  unfold rotl
  rfl
theorem cmpl_eq (x : BitVec 64) : ~~~x = cmpl x := by
  unfold cmpl
  rfl

theorem xor64 (x y : BitVec 64) : BinOp.apply .xor .W64 x y = x ^^^ y := by
  simp [BinOp.apply]
theorem and64 (x y : BitVec 64) : BinOp.apply .and .W64 x y = x &&& y := by
  simp [BinOp.apply]
theorem not64 (x : BitVec 64) : UnOp.apply .not .W64 x = ~~~x := by
  simp [UnOp.apply]
theorem rol64 (x y : BitVec 64) :
    BinOp.apply .rol .W64 x y = x.rotateLeft (shiftCount .W64 y) := by
  simp [BinOp.apply]

end

-- The common preparation: the body's result, the round constant and the lanes as hypotheses
-- `h0` to `h24`.
set_option hygiene false in
macro "body_prep" : tactic => `(tactic| (
  rw [body] at hx
  cases hx
  simp only [rcSym, Sym.eval] at hrc
  simp only [AllOf, laneRegs, laneSlots] at hregs hslots
  obtain ⟨h3, h6, h7, h8, h11, h12, h13, h15, h16, h17, h18, -⟩ := hregs
  obtain ⟨h0, h1, h2, h4, h5, h9, h10, h14, h19, h20, h21, h22, h23, h24, -⟩ := hslots))

-- One lane: the body's value written as the round's.
set_option hygiene false in
macro "body_lane" : tactic => `(tactic| (
  clear hm
  change @Eq (BitVec 64) _ _
  simp only [Sym.eval, xor64, and64, not64, rol64, hrc]
  simp (disch := omega) only [NativeRustcX64.KeccakF.shiftCount_lit]
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24]
  round_simp
  simp only [parOf, UInt64.toBitVec_xor, Nat.reduceAdd, rotl_eq, cmpl_eq]
  ac_nf <;> ac_nf))

public section

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem body_regsA [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec Vm.KeccakF.b2 startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 488)) {a : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hrc : rcSym.eval env = rc.toBitVec) :
    AllOf (fun p : Reg64 × Nat =>
      m.regs.get64 p.1 = (roundCL a (parOf a) rc p.2).toBitVec) laneRegsA := by
  body_prep
  simp only [AllOf, laneRegsA]
  refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> refine (hm.regs _ _ rfl).trans ?_
  all_goals body_lane

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem body_regsB [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec Vm.KeccakF.b2 startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 488)) {a : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hrc : rcSym.eval env = rc.toBitVec) :
    AllOf (fun p : Reg64 × Nat =>
      m.regs.get64 p.1 = (roundCL a (parOf a) rc p.2).toBitVec) laneRegsB := by
  body_prep
  simp only [AllOf, laneRegsB]
  refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> refine (hm.regs _ _ rfl).trans ?_
  all_goals body_lane

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem body_regsC [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec Vm.KeccakF.b2 startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 488)) {a : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hrc : rcSym.eval env = rc.toBitVec) :
    AllOf (fun p : Reg64 × Nat =>
      m.regs.get64 p.1 = (roundCL a (parOf a) rc p.2).toBitVec) laneRegsC := by
  body_prep
  simp only [AllOf, laneRegsC]
  refine ⟨?_, ?_, ?_, trivial⟩ <;> refine (hm.regs _ _ rfl).trans ?_
  all_goals body_lane

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem body_slotsA [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec Vm.KeccakF.b2 startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 488)) {a : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hrc : rcSym.eval env = rc.toBitVec) :
    AllOf (fun p : Nat × Nat =>
      WordAt m.dmem (b + BitVec.ofNat 64 p.1) (roundCL a (parOf a) rc p.2).toBitVec)
      laneSlotsA := by
  body_prep
  simp only [AllOf, laneSlotsA]
  refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> refine wordAt_of_eq (wordAt_write hm hb (by decide) rfl) ?_
  all_goals body_lane

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem body_slotsB [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec Vm.KeccakF.b2 startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 488)) {a : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hrc : rcSym.eval env = rc.toBitVec) :
    AllOf (fun p : Nat × Nat =>
      WordAt m.dmem (b + BitVec.ofNat 64 p.1) (roundCL a (parOf a) rc p.2).toBitVec)
      laneSlotsB := by
  body_prep
  simp only [AllOf, laneSlotsB]
  refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> refine wordAt_of_eq (wordAt_write hm hb (by decide) rfl) ?_
  all_goals body_lane

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem body_slotsC [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec Vm.KeccakF.b2 startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 488)) {a : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hrc : rcSym.eval env = rc.toBitVec) :
    AllOf (fun p : Nat × Nat =>
      WordAt m.dmem (b + BitVec.ofNat 64 p.1) (roundCL a (parOf a) rc p.2).toBitVec)
      laneSlotsC := by
  body_prep
  simp only [AllOf, laneSlotsC]
  refine ⟨?_, ?_, ?_, trivial⟩ <;> refine wordAt_of_eq (wordAt_write hm hb (by decide) rfl) ?_
  all_goals body_lane

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem body_slotsD [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec Vm.KeccakF.b2 startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 488)) {a : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hrc : rcSym.eval env = rc.toBitVec) :
    AllOf (fun p : Nat × Nat =>
      WordAt m.dmem (b + BitVec.ofNat 64 p.1) (roundCL a (parOf a) rc p.2).toBitVec)
      laneSlotsD := by
  body_prep
  simp only [AllOf, laneSlotsD]
  refine ⟨?_, ?_, ?_, trivial⟩ <;> refine wordAt_of_eq (wordAt_write hm hb (by decide) rfl) ?_
  all_goals body_lane

/-- **The loop body is a round.** -/
theorem body_lanes [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec Vm.KeccakF.b2 startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 488)) {a : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hrc : rcSym.eval env = rc.toBitVec) :
    AllOf (fun p : Reg64 × Nat =>
      m.regs.get64 p.1 = (roundCL a (parOf a) rc p.2).toBitVec) laneRegs ∧
    AllOf (fun p : Nat × Nat =>
      WordAt m.dmem (b + BitVec.ofNat 64 p.1) (roundCL a (parOf a) rc p.2).toBitVec) laneSlots := by
  constructor
  · simpa only [laneRegs, laneRegsA, laneRegsB, laneRegsC, AllOf, and_assoc, and_true] using
      And.intro (body_regsA hx hm hb hregs hslots hrc)
        (And.intro (body_regsB hx hm hb hregs hslots hrc) (body_regsC hx hm hb hregs hslots hrc))
  · simpa only [laneSlots, laneSlotsA, laneSlotsB, laneSlotsC, laneSlotsD, AllOf, and_assoc,
      and_true] using
      And.intro (body_slotsA hx hm hb hregs hslots hrc)
        (And.intro (body_slotsB hx hm hb hregs hslots hrc)
          (And.intro (body_slotsC hx hm hb hregs hslots hrc) (body_slotsD hx hm hb hregs hslots hrc)))

end

end NativeRustcVmX64.KeccakF
