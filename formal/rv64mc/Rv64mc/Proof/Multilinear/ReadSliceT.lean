/-
  Rv64mc.Proof.Multilinear.ReadSliceT

  The total contracts of `ring_psi` (`RingPsiT.specT`) and `poly_eval` (`PolyEvalT.specT`), for every value and
  slice, as contracts on the registers and the slice's bytes alone, for callers whose safety does not depend on the
  values: each returns from a slice allocated before the call (`Live`), none or in a window and 8-byte aligned. The
  slice's elements are the ones memory holds (`rdList`), the value the one the limbs in the registers name
  (`Model.ofLimbsW`).

  ## Main definitions

  * `rdList`

  ## Main results

  * `sliceArgs_rdList`, `ringPsiSafe`, `polyEvalSafe`
-/

import Rv64mc.Proof.Whir.RingPsiT
import Rv64mc.Proof.Multilinear.PolyEvalT
import Rv64mc.Proof.Whir.Frobenius8SafeT

namespace Rv64mc.Proof.Multilinear.ReadSliceT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Whir.Frobenius8SafeT (limbs_ofLimbsW)

/-- The `n` elements of `E` memory holds from `ptr`. -/
def rdList (m : MachineState) (ptr : Word) (n : Nat) : List E :=
  (List.range n).map fun k => Model.ofLimbsW
    (m.getMem (ptr + BitVec.ofNat 64 (Layouts.E.byteSize * k) + BitVec.ofNat 64 Layouts.E.c0),
      m.getMem (ptr + BitVec.ofNat 64 (Layouts.E.byteSize * k) + BitVec.ofNat 64 Layouts.E.c1))

theorem length_rdList (m : MachineState) (ptr : Word) (n : Nat) : (rdList m ptr n).length = n := by
  simp [rdList]

/-- **A slice holds the elements memory holds**, when it does not wrap. -/
theorem sliceArgs_rdList {m : MachineState} {ptr len : Word} (h : ptr.toNat + 16 * len.toNat < 2 ^ 64) :
    SliceArgs EListAt m ptr len ((rdList m ptr len.toNat).map Model.limbs) := by
  refine ⟨by simp [length_rdList], by simpa [length_rdList] using h, fun k hk => ?_⟩
  simp only [List.length_map, length_rdList] at hk
  simp only [rdList, List.getElem_map, List.getElem_range, limbs_ofLimbsW]
  exact ⟨rfl, rfl⟩

variable {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat}

/-- **`ring_psi` returns** from any value and a slice `g` (`a2`, `a3`) allocated before, none or in a window and
    8-byte aligned. -/
theorem ringPsiSafe (h : Whir.RingPsiT.specT env p i need) :
    HoldsT env p i need (fun regs m => env.Live m (regs .x12) (16 * (regs .x13).toNat) ∧
      ((regs .x13).toNat = 0 ∨ InWin env (regs .x12) (16 * (regs .x13).toNat) ∧ (regs .x12).toNat % 8 = 0))
      (fun _ _ _ _ => True) :=
  fun Q ret top rest regs m ⟨⟨he, hs, hst, hn, ⟨hl, hw⟩, ha⟩, hW⟩ hstop hk =>
    have hv := limbs_ofLimbsW (regs .x10, regs .x11)
    have hb : (regs .x12).toNat + 16 * (regs .x13).toNat < 2 ^ 64 := by
      have := env.layout; have := env.stackLimit.isLt; unfold Env.Live at hl; omega
    h (Model.ofLimbsW (regs .x10, regs .x11)) (rdList m (regs .x12) (regs .x13).toNat) Q ret top rest regs m
      ⟨⟨he, hs, hst, hn, ⟨⟨by rw [hv], by rw [hv], sliceArgs_rdList hb, by
        simpa [length_rdList] using hl⟩, by simpa [length_rdList] using hw⟩, ha⟩, hW⟩ hstop
      fun r' m' ⟨⟨h1, h2, h3, _⟩, h5⟩ => hk r' m' ⟨⟨h1, h2, h3, trivial⟩, h5⟩

/-- **`poly_eval` returns** from any point and a slice (`a0`, `a1`) allocated before, none or in a window and
    8-byte aligned. -/
theorem polyEvalSafe (h : PolyEvalT.specT env p i need) :
    HoldsT env p i need (fun regs m => env.Live m (regs .x10) (16 * (regs .x11).toNat) ∧
      ((regs .x11).toNat = 0 ∨ InWin env (regs .x10) (16 * (regs .x11).toNat) ∧ (regs .x10).toNat % 8 = 0))
      (fun _ _ _ _ => True) :=
  fun Q ret top rest regs m ⟨⟨he, hs, hst, hn, ⟨hl, hw⟩, ha⟩, hW⟩ hstop hk =>
    have hv := limbs_ofLimbsW (regs .x12, regs .x13)
    have hb : (regs .x10).toNat + 16 * (regs .x11).toNat < 2 ^ 64 := by
      have := env.layout; have := env.stackLimit.isLt; unfold Env.Live at hl; omega
    h (rdList m (regs .x10) (regs .x11).toNat) (Model.ofLimbsW (regs .x12, regs .x13)) Q ret top rest regs m
      ⟨⟨he, hs, hst, hn, ⟨⟨sliceArgs_rdList hb, by simpa [length_rdList] using hl, by rw [hv], by rw [hv]⟩,
        by simpa [length_rdList] using hw⟩, ha⟩, hW⟩ hstop
      fun r' m' ⟨⟨h1, h2, h3, _⟩, h5⟩ => hk r' m' ⟨⟨h1, h2, h3, trivial⟩, h5⟩

end Rv64mc.Proof.Multilinear.ReadSliceT
