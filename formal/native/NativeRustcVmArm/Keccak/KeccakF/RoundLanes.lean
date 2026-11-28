module

public import NativeRustcVmArm.Keccak.KeccakF.Inv
public import NativeRustcVmArm.Keccak.KeccakF.Blocks
public import NativeRustcArm.KeccakF.RoundLanes

/-!
# The loop body computes a round

`body_lanes`: where the loop body runs (`body`) in an environment whose registers and frame slots
hold the lanes `a` where the loop head keeps them (`laneRegs`, `laneSlots`) and whose round-constant
load is `rc`, the machine after it holds the round's lanes (`roundCL a (parOf a) rc`, the column
parities computed from the lanes) in the same places. Each is an identity of XORs, AND-NOTs and
rotations of the inputs, matched by `ac_nf` after the round's lanes are written as 64-bit vectors.
-/

namespace NativeRustcVmArm.KeccakF

open NativeRustcArm NativeRustcArm.Sym NativeRustc.Keccak LeanVM.Semantics
open NativeRustcArm.KeccakF (WordAt wordAt_of_eq wordAt_write)

@[expose] public section

/-- θ's column parities of the lanes `a`. -/
def parOf (a : Nat → UInt64) (x : Nat) : UInt64 :=
  a x ^^^ a (x + 5) ^^^ a (x + 10) ^^^ a (x + 15) ^^^ a (x + 20)

theorem par_eq (A : KeccakState) : par A = parOf (Keccak.lane A) := rfl

end

public section

/-! The 64-bit operations of the body at the type `BitVec 64` (`sym_simp` leaves them at
`RegWidth.W64.type`, which `ac_nf` tells apart from the round's). -/

theorem eor64 (x y : BitVec 64) : BinOp.apply .eor .W64 x y = x ^^^ y := by
  simp [BinOp.apply]
theorem bic64 (x y : BitVec 64) : BinOp.apply .bic .W64 x y = x &&& ~~~y := by
  simp [BinOp.apply]
theorem ror64 (x : BitVec 64) (n : Nat) :
    UnOp.apply (.shift .ROR n) .W64 x = x.rotateRight n := by
  simp [UnOp.apply, shiftW]

/-- **The loop body is a round.** -/
theorem body_lanes [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec Vm.KeccakF.b2 startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 400)) {a : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : XReg × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hrc : env.load 0 (96 + (UnOp.apply (.memExtend { type := .UXTX, amount := .E0 }) .W64
      (env.vars 0)).toNat) 8 = rc.toBitVec) :
    AllOf (fun p : XReg × Nat =>
      (m.regs.getXReg p.1).toBitVec = (roundCL a (parOf a) rc p.2).toBitVec) laneRegs ∧
    AllOf (fun p : Nat × Nat =>
      WordAt m.dmem (b + BitVec.ofNat 64 p.1) (roundCL a (parOf a) rc p.2).toBitVec) laneSlots := by
  rw [body] at hx
  cases hx
  simp only [AllOf, laneRegs, laneSlots] at hregs hslots ⊢
  obtain ⟨h0, h1, h4, h5, h6, h8, h10, h11, h12, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, -⟩ := hregs
  obtain ⟨h7, h9, h3, h13, h2, -⟩ := hslots
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩,
    ⟨?_, ?_, ?_, ?_, ?_, trivial⟩⟩
  all_goals first
    | refine (hm.regs _ _ rfl).trans ?_
    | refine wordAt_of_eq (wordAt_write hm hb (by decide) rfl) ?_
  all_goals
    clear hm
    simp only [Sym.eval, eor64, bic64, ror64]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
      h18, h19, h20, h21, h22, h23, h24, hrc]
    round_simp
    simp only [parOf, UInt64.toBitVec_xor, Nat.reduceAdd]
    -- one `ac_nf` leaves some arguments of rotations unsorted; the second sorts them
    ac_nf
    ac_nf

end

end NativeRustcVmArm.KeccakF
