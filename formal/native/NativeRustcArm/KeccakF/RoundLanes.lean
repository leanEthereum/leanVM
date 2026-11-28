module

public import NativeRustcArm.KeccakF.Inv
public import NativeRustcArm.KeccakF.Blocks

/-!
# The loop body computes `permute`'s round

`body_lanes`: where the loop body runs (`body`) in an environment whose registers and frame slots
hold the lanes `a` and the parities `c` where the loop head keeps them (`laneRegs`, `laneSlots`,
`parRegs`) and whose round-constant load is `rc`, the machine after it holds the round's lanes
(`roundCL a c rc`) and new parities (`newPar a c rc`) in the same places. Each is an identity of
XORs, AND-NOTs and rotations of the inputs: rustc's reassociation and operand order, matched by
`ac_rfl` after the round's lanes are written as 64-bit vectors.
-/

namespace NativeRustcArm.KeccakF

open NativeRustcArm.Sym NativeRustc.Keccak LeanVM.Semantics

public section

/-- Unfolds a lane of `permute`'s round to 64-bit vector operations on its inputs. -/
macro "round_simp" : tactic => `(tactic| simp only [roundCL, newPar, bC, tC, thetaD, chi,
  UInt64.toBitVec_xor, UInt64.toBitVec_and, UInt64.toBitVec_not, rot_zero, Nat.reduceMod,
  Nat.reduceAdd, Nat.reduceSub, reduceIte, OfNat.ofNat_ne_zero, Nat.succ_ne_zero, toBitVec_rot,
  Nat.reduceLT, Nat.lt_irrefl, Nat.zero_lt_succ])

/-- **The loop body is `permute`'s round.** -/
theorem body_lanes [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec Common.KeccakF.b1 startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 192)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : XReg × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : XReg × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 (0 + (BitVec.ofInt 64
      ((env.vars 0).apply_mem_extend { type := .UXTX, amount := .E0 })).toNat) 8 = rc.toBitVec) :
    AllOf (fun p : XReg × Nat =>
      (m.regs.getXReg p.1).toBitVec = (roundCL a c rc p.2).toBitVec) laneRegs ∧
    AllOf (fun p : Nat × Nat =>
      WordAt m.dmem (b + BitVec.ofNat 64 p.1) (roundCL a c rc p.2).toBitVec) laneSlots ∧
    AllOf (fun p : XReg × Nat =>
      (m.regs.getXReg p.1).toBitVec = (newPar a c rc p.2).toBitVec) parRegs := by
  rw [body] at hx
  cases hx
  simp only [AllOf, laneRegs, laneSlots, parRegs] at hregs hslots hpar ⊢
  obtain ⟨h4, h6, h8, h9, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, -⟩ :=
    hregs
  obtain ⟨h0, h1, h2, h3, h5, h7, h10, -⟩ := hslots
  obtain ⟨c0, c1, c2, c3, c4, -⟩ := hpar
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩, ⟨?_, ?_, ?_, ?_, ?_, trivial⟩⟩
  all_goals first
    | refine (hm.regs _ _ rfl).trans ?_
    | refine wordAt_of_eq (wordAt_write hm hb (by decide) rfl) ?_
  all_goals
    clear hm
    sym_simp
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
      h18, h19, h20, h21, h22, h23, h24, c0, c1, c2, c3, c4, hrc]
    round_simp
    ac_rfl

end

end NativeRustcArm.KeccakF
