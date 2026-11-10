import Rv64Verifier.Proofs.Hash.Run
import Rv64Verifier.Blocks.F50

/-!
# `keccak_hash`'s padding and digest blocks

The padding (`0x8000c9c4`): `block[tail.len()] ^= 0x01; block[RATE - 1] ^= 0x80`, the block at
`sp + 208`. The tail's length `tl < 136` decides which doublewords the two byte stores hit, so the
block runs once per `tl` from a symbolic state in which `s1` is the constant `tl` and `s3` is
`sp + 208` (`padSig`); `padX tl` lists its two writes (one when both bytes are in the last
doubleword). The digest (`0x8000c9fc`): each byte the block writes into the digest is the
lane's (`digest_bytes`, read with `byteOf`).
-/

namespace Rv64Verifier.Hash.KeccakHash
open RiscvZkvm.Rv64 Rv64Verifier.Sym Rv64Verifier.Blocks.F50

def cfg : Config := { noAlias := true }

/-- `sp + off`. -/
def spE (off : Nat) : E := .bin .add (.reg .x2) (.c (BitVec.ofNat 64 off))

def spKey (off : Nat) : Addr := ⟨some (.reg .x2), BitVec.ofNat 64 off⟩

def padSig (tl : Nat) : SymState :=
  { SymState.init with
    regs := (SymState.init.regs.set .x9 (.c (BitVec.ofNat 64 tl))).set .x19 (spE 208) }

/-- The doubleword of `block[tl]`. -/
def lowOff (tl : Nat) : Nat := 208 + tl - tl % 8

/-- A byte of `v` XORed with `c`, stored back. -/
def flipE (v : E) (bo : Nat) (c : Word) : E :=
  .bin (.st .b bo) v (.bin .xor (.un (.ld .bu bo) v) (.c c))

def padLow (tl : Nat) : E := flipE (.ld (spE (lowOff tl))) (tl % 8) 1

def padHigh (tl : Nat) : E :=
  flipE (if 128 ≤ tl then padLow tl else .ld (spE 336)) 7 0x80

def padX (tl : Nat) : Expect where
  steps := 11
  pc := .c 0x8000e5c8
  regs := [(.x1, .c 0x8000c9f0), (.x2, .reg .x2), (.x8, .reg .x8), (.x10, spE 8), (.x11, spE 208)]
  mem := if 128 ≤ tl then [(spKey 336, padHigh tl)] else
    [(spKey 336, padHigh tl), (spKey (lowOff tl), padLow tl)]
  writes := [spKey 336, spKey (lowOff tl)]
  obl := [.valid (spKey 343) 1, .align8 (.reg .x2), .valid (spKey (208 + tl)) 1]

theorem pad_run : (List.range 136).all (fun tl ↦
    (symRunCodeAux cfg (codeWindow Image.code 12913 11) 0x8000c9c4 11 (padSig tl)).any
      (meetsR cfg [] [] · (padX tl))) = true := by decide +kernel

/-! ## The whole blocks -/

def mulE : E := .bin .mulhu (.reg .x19) (.c 0xf0f0f0f0f0f0f0f1)

/-- `len / 136 * 136`, as `0x8000c938` computes it. -/
def blocksE : E :=
  .bin .add (.bin .and mulE (.c 0xffffffffffffff80))
    (.bin .and (.bin .srl mulE (.c 4)) (.c 0xfffffffffffffff8))

theorem blocks_regs : (regOk b8000c938 .x20 blocksE && regOk b8000c938 .x9
    (.bin .sub (.reg .x19) blocksE) && regOk b8000c938 .x18 (.bin .add (.reg .x9) blocksE)) = true := by
  decide +kernel

/-! ## The digest -/

/-- Byte `j` of the doubleword a chain of byte stores `e` leaves. -/
def byteOf : E → Nat → Option E
  | .bin (.st .b bo) old v, j => if bo = j then some v else if bo < 8 then byteOf old j else none
  | _, _ => none

/-- Byte `j` of lane `i`, as the block shifts it out. -/
def laneByteE (i j : Nat) : E :=
  if j = 0 then .ld (spE (8 + 8 * i)) else .bin .srl (.ld (spE (8 + 8 * i))) (.c (BitVec.ofNat 64 (8 * j)))

theorem digest_bytes : (List.range 4).all (fun i ↦ (List.range 8).all fun j ↦
    b8000c9fc.mem.any fun p ↦ Addr.beq p.1 ⟨some (.reg .x8), BitVec.ofNat 64 (8 * i)⟩ &&
      match byteOf p.2 j with
      | some v => E.acEq v (laneByteE i j)
      | none => false) = true := by decide +kernel

def outR : Region := ⟨.x8, 0, 4⟩
def frameR : Region := ⟨.x2, 0, 56⟩
def outB : BRegion := ⟨.x8, 0, 32⟩

theorem digest_obl : b8000c9fc.obl.all (oblCheck [outR, frameR] [outB] [.align8 (.reg .x8)]) = true := by
  decide +kernel

end Rv64Verifier.Hash.KeccakHash
