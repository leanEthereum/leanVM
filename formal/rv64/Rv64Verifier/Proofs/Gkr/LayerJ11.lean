import Rv64Verifier.Proofs.Gkr.LayerStart

/-!
# `keccak::verify_layer`: after the second check

The state at `0x8000fb34`, once `check2` has passed: `beta` still to sample, then the lane
weights, the next weights and `linear_transpose` (`stage7`). Slot `f + k` is `sp - (1712 - k)`.

* `mu` (the instance weights): capacity at `f + 40`, pointer at `f + 64`, length in `s10`.
* the packed point: the `Vec` at `f + 864`.
* `eq_z`: pointer at `f + 80`, length at `f + 72`.
* `eq_lane`: pointer in `s9` and at `f + 112`, length in `s2` and at `f + 88`.
* `t` (the three scalars): pointer in `s8`, length in `s3`, `&t[2]` at `f + 32`.
* the result's address at `f + 48`, the sponge's at `f + 96`, the transcript in `s4`.
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr

/-- At `0x8000fb34`, the second check passed. -/
structure J11 (s u : MachineState) (mu point eqZ eqLane t : List E) : Prop where
  pc : u.pc = 0x8000fb34
  base : Base s u
  out : u.getMem (s.getReg .x2 - 1664) = s.getReg .x10
  sponge : u.getMem (s.getReg .x2 - 1616) = s.getReg .x11 + 8
  x20 : u.getReg .x20 = s.getReg .x11
  muLen : (u.getReg .x26).toNat ≤ (u.getMem (s.getReg .x2 - 1672)).toNat
  muBuf : NewBuf s u (u.getMem (s.getReg .x2 - 1648))
    ((u.getMem (s.getReg .x2 - 1672)).toNat * 24) 8
  muE : eListAt u (u.getMem (s.getReg .x2 - 1648)) (u.getReg .x26).toNat = mu
  ptV : NewVecE s u (s.getReg .x2 - 848) point
  ezBuf : NewBuf s u (u.getMem (s.getReg .x2 - 1632)) (24 * (u.getMem (s.getReg .x2 - 1640)).toNat) 8
  ezE : eListAt u (u.getMem (s.getReg .x2 - 1632)) (u.getMem (s.getReg .x2 - 1640)).toNat = eqZ
  x25 : u.getReg .x25 = u.getMem (s.getReg .x2 - 1600)
  x18 : u.getReg .x18 = u.getMem (s.getReg .x2 - 1624)
  elBuf : NewBuf s u (u.getReg .x25) (24 * (u.getReg .x18).toNat) 8
  elE : eListAt u (u.getReg .x25) (u.getReg .x18).toNat = eqLane
  t2 : u.getMem (s.getReg .x2 - 1680) = u.getReg .x24 + 48
  tBuf : NewBuf s u (u.getReg .x24) (24 * (u.getReg .x19).toNat) 8
  tE : eListAt u (u.getReg .x24) (u.getReg .x19).toNat = t
  rest : Rest s u (stage7 mu point eqZ eqLane t)

end Rv64Verifier.Gkr.Layer
