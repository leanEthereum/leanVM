import Rv64Verifier.Proofs.Walk.Tl12
import Rv64Verifier.Proofs.Pcs.Contracts

/-!
# `walk` at `0x800033f0`: `placements` built (end of R13)

`plc A k` is `placementsRust` over `kappas`: the placements, `q_keccak`'s placement and
`stack_log`. `AtR14` is the state after the placements' loop: `Base12`, the placements' buffer
`PL` (165 entries of 24 bytes) holding `(plc A k).1`, and in registers the stacked size's log
(`s0`, before `max 15`), `stack_log` (`s1`), `q_keccak`'s index (`s3`), `PL` and its capacity
(`s5`, `s6`), and `kappas`' length (`s8`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror

/-- `placementsRust` over `kappas`: placements, `q_keccak`'s placement, `stack_log`. -/
abbrev plc (A : List E) (k : Nat) : List (Option PlacementRust) × PlacementRust × Nat :=
  placementsRust (kapPre A k 6) ((hts A).getD 5 0 + 6)

/-- At `0x800033f0`. -/
structure AtR14 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) (lo lo2 lo3 : Nat) (PL : Word) : Prop where
  base : Base12 OI s u A k R Q B lo lo2 lo3
  plal : PL.toNat % 8 = 0
  pllo : lo3 ≤ PL.toNat
  plhi : PL.toNat + 24 * 165 ≤ heapNext u
  plvals : PcsContracts.placementsAt u PL 165 = (plc A k).1
  /-- `s0`: the stacked size's log, of which `stack_log` is the `max` with `15`. -/
  x8 : max 15 (u.getReg .x8).toNat = (plc A k).2.2
  x9 : (u.getReg .x9).toNat = (plc A k).2.2
  x19 : u.getReg .x19 = (plc A k).2.1.index
  x21 : u.getReg .x21 = PL
  x22 : u.getReg .x22 = 165
  x24 : u.getReg .x24 = 165
  x18 : u.getReg .x18 = BitVec.ofNat 64 ((hts A).getD 5 0)
  x23 : u.getReg .x23 = BitVec.ofNat 64 (k - 4)
  x26 : u.getReg .x26 = BitVec.ofNat 64 ((hts A).getD 5 0 + 6)

end Rv64Verifier.Proofs.Walk
