/-
  Rv64mc.Proof.Field.ESumWinT

  What the total contracts of the `E::sum` closures share: a table of `E`s (`16` bytes each) at a pointer with a
  length word, in a window and 8-byte aligned unless it is empty (`TabW`), and an entry the code reads after checking
  its index against that length in a window and aligned (`TabW.entry`).

  ## Main definitions

  * `TabW`

  ## Main results

  * `TabW.entry`, `TabW.entry'`, `shl4_add_toNat`
-/

import Rv64mc.Proof.Runtime.WinT

namespace Rv64mc.Proof.Field.ESumWinT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV
open Rv64mc.Proof.Runtime.MemsetT (InWin)

/-- A table of `len` `E`s at `q`: empty, or in a window and 8-byte aligned. -/
def TabW (env : Env) (q len : Word) : Prop :=
  len.toNat = 0 ∨ (InWin env q (16 * len.toNat) ∧ q.toNat % 8 = 0)

/-- An entry below the length: both its doublewords in a window and aligned. -/
theorem TabW.entry {env : Env} {q x len top : Word} {m : MachineState} (hd : TabW env q len)
    (hW : Windows env top m) (hx : x < len) :
    (inWindow (q + x <<< 4) 8 = true ∧ (q + x <<< 4).toNat % 8 = 0) ∧
      (inWindow (q + x <<< 4 + 8#64) 8 = true ∧ (q + x <<< 4 + 8#64).toNat % 8 = 0) := by
  have hxl : x.toNat < len.toNat := hx
  rcases hd with h0 | ⟨hw, hal⟩
  · omega
  have := hw.lt
  have he : (q + x <<< 4).toNat = q.toNat + 16 * x.toNat := Runtime.WinT.elem_toNat (s := 4) (by omega)
  exact ⟨hw.dword hW hal he (by omega) (by omega), hw.dword_add (k := 8) hW hal he (by omega) (by omega)⟩

/-- `TabW.entry` with the offset first, as the code adds it. -/
theorem TabW.entry' {env : Env} {q x len top : Word} {m : MachineState} (hd : TabW env q len)
    (hW : Windows env top m) (hx : x < len) :
    (inWindow (x <<< 4 + q) 8 = true ∧ (x <<< 4 + q).toNat % 8 = 0) ∧
      (inWindow (x <<< 4 + q + 8#64) 8 = true ∧ (x <<< 4 + q + 8#64).toNat % 8 = 0) := by
  rw [BitVec.add_comm (x <<< 4) q]; exact hd.entry hW hx

/-- An offset `16 x` from `q`, as the code computes it, as a number, when it does not wrap. -/
theorem shl4_add_toNat {q x : Word} (h : q.toNat + 16 * x.toNat < 2 ^ 64) :
    (x <<< 4 + q).toNat = 16 * x.toNat + q.toNat := by
  rw [BitVec.add_comm, Runtime.WinT.elem_toNat (s := 4) h]; omega

end Rv64mc.Proof.Field.ESumWinT
