/-
  Rv64mc.Proof.Whir.VecWordT

  What the WHIR functions' total contracts that build a vector of words (`Vec<u64>`, `Vec<K>`) share: a header stored
  into a slot is `VecReprT.VecT` with the length stored (`vecT_stores`), and the offset `8 x` the code computes by a
  shift (`shl3`).

  ## Main results

  * `vecT_stores`, `shl3`
-/

import Rv64mc.Proof.Runtime.VecReprT
import Rv64mc.Tactic.Heap

namespace Rv64mc.Proof.Whir.VecWordT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT BufT)

/-- **A `Vec` header stored into a slot** in a window, 8-byte aligned, from a buffer `BufT` of `s`-byte
    elements. -/
theorem vecT_stores {env : Env} {M : MachineState} {a c q l : Word} {s : Nat} (hw : InWin env a 24)
    (ha : a.toNat % 8 = 0) (hb : BufT env M c q s) (hc : c.toNat * s < 2 ^ 63) (hl : l.toNat ≤ c.toNat) :
    VecT env (((M.setMem a c).setMem (a + 8#64) q).setMem (a + 16#64) l) a s ∧
      vecLen (((M.setMem a c).setMem (a + 8#64) q).setMem (a + 16#64) l) a = l := by
  have hlt := hw.lt
  have e8 : (a + 8#64).toNat = a.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (a + 16#64).toNat = a.toNat + 16 := toNat_add_ofNat (by omega)
  have n1 : a ≠ a + 16#64 := Tactic.ne_of_toNat (by rw [e16]; omega)
  have n2 : a ≠ a + 8#64 := Tactic.ne_of_toNat (by rw [e8]; omega)
  have n3 : a + 8#64 ≠ a + 16#64 := Tactic.ne_of_toNat (by rw [e8, e16]; omega)
  have hna : ∀ x : Word, x.toNat = a.toNat ∨ x.toNat = a.toNat + 8 ∨ x.toNat = a.toNat + 16 → x ≠ env.nextAddr :=
    fun x hx => hw.ne_next (by omega) (by omega)
  have hn : env.next (((M.setMem a c).setMem (a + 8#64) q).setMem (a + 16#64) l) = env.next M := by
    rw [Tactic.next_setMem (hna _ (by omega)), Tactic.next_setMem (hna _ (by omega)),
      Tactic.next_setMem (hna _ (by omega))]
  have r0 : (((M.setMem a c).setMem (a + 8#64) q).setMem (a + 16#64) l).getMem (a + BitVec.ofNat 64 0) = c := by
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, MachineState.getMem_setMem_ne n1,
      MachineState.getMem_setMem_ne n2, MachineState.getMem_setMem_eq]
  have r8 : (((M.setMem a c).setMem (a + 8#64) q).setMem (a + 16#64) l).getMem (a + BitVec.ofNat 64 8) = q := by
    rw [show BitVec.ofNat 64 8 = 8#64 from rfl, MachineState.getMem_setMem_ne n3, MachineState.getMem_setMem_eq]
  have r16 : (((M.setMem a c).setMem (a + 8#64) q).setMem (a + 16#64) l).getMem (a + BitVec.ofNat 64 16) = l := by
    rw [show BitVec.ofNat 64 16 = 16#64 from rfl, MachineState.getMem_setMem_eq]
  refine ⟨⟨hw, ⟨hw.sub (Nat.le_refl _) (by simp only [Layouts.RawVecInner.byteSize]; omega), ha, ?_, ?_⟩, ?_⟩, ?_⟩
  · simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, r0, r8]
    exact hb.mono (by rw [hn])
  · simp only [rvCapAt, Layouts.RawVecInner.cap, r0]; exact hc
  · simp only [vecCap, vecLen, Layouts.Vec.cap, Layouts.Vec.len, r0, r16]; exact hl
  · simp only [vecLen, Layouts.Vec.len, r16]

/-- `8 x` as the code computes it. -/
theorem shl3 {x : Word} (h : 8 * x.toNat < 2 ^ 64) : (x <<< 3).toNat = 8 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

end Rv64mc.Proof.Whir.VecWordT
