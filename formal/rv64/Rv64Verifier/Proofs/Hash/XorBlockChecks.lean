import Rv64Verifier.Proofs.Hash.Run
import Rv64Verifier.Image

/-!
# `xor_block` against the lanes

The kernel check of `Proofs/Hash/XorBlock.lean`: `xor_block` (`0x8000e5c8`, 567 instructions, no
branch) runs as one block, from a symbolic state in which `a1`, the block, is `a1 + r` with
`r < 8` and `a1` aligned (`xsig r`), so that every byte load is a byte of an aligned doubleword.
It writes `laneE r i` to lane `i < 17`: the lane XORed with the block's bytes `8i .. 8i + 8`
(`byteE r`) as `u64::from_le_bytes` assembles them (`wordE`).
-/

set_option Elab.async false

namespace Rv64Verifier.Hash.XorBlock
open RiscvZkvm.Rv64 Rv64Verifier.Sym

def cfg : Config := { noAlias := true }

def key (r : Reg) (off : Nat) : Addr := ⟨some (.reg r), BitVec.ofNat 64 off⟩

/-- `a1 + r`. -/
def xsig (r : Nat) : SymState :=
  { SymState.init with regs := SymState.init.regs.set .x11 (mkAdd (.reg .x11) (.c (BitVec.ofNat 64 r))) }

/-- Byte `j` of the block, its doubleword at `a1` plus a multiple of 8. -/
def byteE (r j : Nat) : E :=
  .un (.ld .bu (byteOffset (BitVec.ofNat 64 (r + j))))
    (.ld (Addr.toE ⟨some (.reg .x11), alignToDword (BitVec.ofNat 64 (r + j))⟩))

/-- Four bytes, little-endian. -/
def halfE (b0 b1 b2 b3 : E) : E :=
  .bin .or (.bin .or (.bin .sll b3 (.c 24)) (.bin .sll b2 (.c 16))) (.bin .or (.bin .sll b1 (.c 8)) b0)

/-- Eight bytes, little-endian. -/
def wordE (b : Nat → E) : E :=
  .bin .or (.bin .sll (halfE (b 4) (b 5) (b 6) (b 7)) (.c 32)) (halfE (b 0) (b 1) (b 2) (b 3))

def laneE (r i : Nat) : E :=
  .bin .xor (.ld (Addr.toE (key .x10 (8 * i)))) (wordE fun k ↦ byteE r (8 * i + k))

def stateR : Region := ⟨.x10, 0, 25⟩
def stackR : Region := ⟨.x2, 0 - 512, 64⟩
/-- The doublewords holding the block. -/
def blockR (r : Nat) : Region := ⟨.x11, 0, (r + 143) / 8⟩
def bytesR (r : Nat) : BRegion := ⟨.x11, BitVec.ofNat 64 r, 136⟩

def saved : List Reg := [.x1, .x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26,
  .x27]

def xorX (r : Nat) : Expect where
  steps := 567
  pc := .bin .and (.reg .x1) (.c 0xfffffffffffffffe)
  regs := saved.map fun r ↦ (r, .reg r)
  mem := (List.range 17).map fun i ↦ (key .x10 (8 * i), laneE r i)
  writes := (List.range 17).map (key .x10 <| 8 * ·) ++
    (List.range 64).map fun i ↦ ⟨some (.reg .x2), 0 - 512 + BitVec.ofNat 64 (8 * i)⟩
  obl := [.align8 (.reg .x11)]

/-- The run from `xsig r` meets `xorX r`. -/
def xorCheck (r : Nat) : Bool :=
  (symRunCodeAux cfg (codeWindow Image.code 14706 567) 0x8000e5c8 567 (xsig r)).any
    (meetsR cfg [stateR, stackR, blockR r] [bytesR r] · (xorX r))

theorem xor_run0 : xorCheck 0 = true := by decide +kernel
theorem xor_run1 : xorCheck 1 = true := by decide +kernel
theorem xor_run2 : xorCheck 2 = true := by decide +kernel
theorem xor_run3 : xorCheck 3 = true := by decide +kernel
theorem xor_run4 : xorCheck 4 = true := by decide +kernel
theorem xor_run5 : xorCheck 5 = true := by decide +kernel
theorem xor_run6 : xorCheck 6 = true := by decide +kernel
theorem xor_run7 : xorCheck 7 = true := by decide +kernel

theorem xor_run {r : Nat} (hr : r < 8) : xorCheck r = true := by
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact xor_run0
  · exact xor_run1
  · exact xor_run2
  · exact xor_run3
  · exact xor_run4
  · exact xor_run5
  · exact xor_run6
  · exact xor_run7

theorem xor_writes : (xorX 0).writes.all (fun k ↦ [stateR, stackR].any (Region.has k)) = true := by
  decide +kernel

end Rv64Verifier.Hash.XorBlock
