import Rv64Verifier.Proofs.Walk.TailT

/-!
# `walk` at `0x80003ff8`: `ring_switch`'s call setup

`AtR21`: `verify_keccak` has returned `Ok`, its outputs' claim is pushed (or there was none), and
the code is about to pass `ring_switch` the openings' point (the `Vec` moved to `S - 1728`, `sp +
928`) and slices (`a2`/`a3`). The claims `Vec`'s buffer `P` holds `cl`, `L` of them (`s2` = `P`,
`s9` = `L`; the length slot is stale); `s6` is the rate exponent, `s7` the result's address, `s8`
= `sp + 2144`. The code runs `ring_switch` on `pt`, `sl`, then `afterRing`: the mirror from
`TailStages` on, the keccak phase's stream positions `ks`, `ke` in the summary.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript

/-- At `0x80003ff8`. -/
structure AtR21 (OI : MachineState → Word → List (List Opening) → Prop)
    (s u₀ w t u : MachineState) (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64))
    (lir : BitVec 64) (bus : BusResultRust) (evs : List (List E × List E)) (P C L : Word)
    (cl : List ColumnClaim) (pt sl : List E) (ks ke : ℕ) : Prop
    extends CoreT OI s u₀ w t u layout lir evs P C L.toNat cl
      (Pcs.ringSwitchRust pt sl >>= afterRing layout rows lir bus cl ks ke) where
  pc : u.pc = 0x80003ff8
  x18 : u.getReg .x18 = P
  x22 : u.getReg .x22 = lir
  x23 : u.getReg .x23 = s.getReg .x10
  x24 : u.getReg .x24 = s.getReg .x2 - 512
  x25 : u.getReg .x25 = L
  /-- The point's `Vec` at `S - 1728`, allocated by `walk` (its pointer below `NEXT` when empty). -/
  point : NewVecE s u (s.getReg .x2 - 1728) pt
  pointOld : Old s u (vecPtr u (s.getReg .x2 - 1728)) (24 * (vecLen u (s.getReg .x2 - 1728)).toNat)
  /-- The slices: `a2` the pointer, `a3` the length. -/
  slices : Old s u (u.getReg .x12) (24 * (u.getReg .x13).toNat)
  slicesVal : eListAt u (u.getReg .x12) (u.getReg .x13).toNat = sl

end Rv64Verifier.Proofs.Walk
