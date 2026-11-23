module

public import NativeRustcVm.Arrays.Read
public import NativeVm.Model.KeccakGkr

/-!
# Phase 6's working areas in memory

The crate's structs of `keccak_gkr.rs` (`#[repr(C)]`, offsets local to the crate's layout test):

- `KeccakOutW` (`KeccakOutAt`, 1608 bytes): `q_keccak`'s point, a `Buf<EW, 36>` at `0`, and its
  64 slices from byte `584`. Ring switching and the WHIR basis read it.
- `KeccakClaimW` (`ClaimAt`, 768 bytes): a model `KeccakClaimW` but its bit weights: the value at
  `0`, the instance weights `mu`, a `Buf<EW, 16>` at `16`, the point, a `Buf<EW, 30>` at `280`.
- `KeccakScratch` (`scratchBytes`): the first claim's bit weights at `0`, the running claim's at
  `25600`, a layer's weights before the transpose at `51200`, `linear_transpose`'s `g` at `76800`
  and columns at `102400`, the local equality kernel (2048 elements) at `107520`, the slot weights
  (64 rows of 64) at `140288`. A claim's bit weights are 1600 elements end to end (`WeightsAt`).
-/

namespace NativeRustcVm.KeccakGkr

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- The address `n` bytes past `a`. -/
abbrev off (a : BitVec 64) (n : Nat) : BitVec 64 := a + BitVec.ofNat 64 n

/-! ## `KeccakOutW` -/

/-- `POINT_CAP`: a column claim's point. -/
def outPointCap : Nat := 36

/-- The offset of `KeccakOutW.slices`. -/
def slicesOff : Nat := 584

/-- `KeccakOutW`'s bytes. -/
def outBytes : Nat := 1608

/-- **`KeccakOutW`** at `p` holds `q_keccak`'s point and its 64 slices (`verifyKeccak`'s second and
third results). -/
def KeccakOutAt (d : Mem 64) (p : BitVec 64) (point slices : Array EW) : Prop :=
  BufEWAt d p outPointCap point.toList ∧ slices.size = 64 ∧ EWsAt d (off p slicesOff) slices.toList

/-! ## `KeccakClaimW` -/

/-- `MU`: the instance weights' capacity. -/
def muCap : Nat := 16

/-- `CLAIM_POINT_CAP`: a claim's point. -/
def claimPointCap : Nat := 30

/-- The offsets of `KeccakClaimW.mu` and `KeccakClaimW.point`. -/
def muOff : Nat := 16
/-- The offset of `KeccakClaimW.point`. -/
def pointOff : Nat := 280

/-- `KeccakClaimW`'s bytes. -/
def claimBytes : Nat := 768

/-- **A claim but its bit weights** at `p`: the value, the instance weights, the point. -/
def ClaimAt (d : Mem 64) (p : BitVec 64) (c : KeccakClaimW) : Prop :=
  EWAt d p c.value ∧ BufEWAt d (off p muOff) muCap c.mu.toList ∧
    BufEWAt d (off p pointOff) claimPointCap c.point.toList

/-- A claim's bit weights at `p`: its 1600 elements. -/
def WeightsAt (d : Mem 64) (p : BitVec 64) (c : KeccakClaimW) : Prop :=
  c.weights.size = keccakBits ∧ EWsAt d p c.weights.toList

/-! ## `KeccakScratch` -/

/-- The bytes of 1600 elements. -/
def weightsBytes : Nat := 25600

/-- The offsets of `KeccakScratch`'s fields. -/
def firstWeightsOff : Nat := 0
/-- `KeccakScratch.weights`. -/
def weightsOff : Nat := 25600
/-- `KeccakScratch.layer_weights`. -/
def layerWeightsOff : Nat := 51200
/-- `KeccakScratch.g`. -/
def gOff : Nat := 76800
/-- `KeccakScratch.columns`. -/
def columnsOff : Nat := 102400
/-- `KeccakScratch.eq`. -/
def eqOff : Nat := 107520
/-- `KeccakScratch.rows`. -/
def rowsOff : Nat := 140288

/-- The bytes of the slot weights: 64 rows of 64 elements. -/
def rowsBytes : Nat := 65536

/-- `KeccakScratch`'s bytes. -/
def scratchBytes : Nat := 205824

/-- The slot weights' rows end to end. -/
def rowsFlat (rows : Array (Array EW)) : List EW := rows.toList.flatMap (·.toList)

end

end NativeRustcVm.KeccakGkr
