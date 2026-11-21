module

public import NativeVm.Code.Phase3.GkrRounds

/-!
# The sumcheck's loop

`roundsC_spec`: the rounds' loop against `sumcheck claim (N + 1) (point.map some)`, from `RInv` after
no round to `RInv` after all of them.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript NativeVm.Field

variable {env : Env} {inp : Input} {s0 : QState} {rem N : Nat} {point : Array EW}

theorem toUInt64_ne_zero {n : Nat} (h : n < 2 ^ 64) : n.toUInt64 ≠ 0 ↔ 0 < n := by
  constructor
  · intro h0; by_contra h1; exact h0 (by rw [show n = 0 by omega]; rfl)
  · intro h1 h0; have := Field.toUInt64_eq_zero h h0; omega

/-- **The rounds.** -/
theorem roundsC_spec (hcap : rem + point.size ≤ 64) (hN4 : N ≤ 4) (claim : EW) :
    Refines (RInv env inp s0 rem N point 0 (#[], claim)) roundsC
      (sumcheck claim (N + 1) (point.map some))
      (fun r t s ↦ RInv env inp s0 rem N point point.size r t s)
      (fun s' ↦ Step3 env allRegs (roundWs rem point.size) s0 s') := by
  refine Refines.of_run (m := (point.toList.map some).foldlM (roundF (N + 1)) (#[], claim))
    (fun t ↦ by rw [sumcheck_eq, Array.toList_map]) ?_
  refine Refines.mono (Refines.foldlM (Inv := fun k acc t s ↦ RInv env inp s0 rem N point k acc t s)
    (fun k acc t s hI ↦ ?_) (fun k hk acc ↦ ?_)) (fun _ _ h ↦ h)
    (fun _ _ _ h ↦ by simpa using h) (fun _ h ↦ h)
  · have := hI.kn
    simp only [Cond.eval, Rhs.eval, hI.r14, List.length_map, Array.length_toList, bne_iff_ne, ne_eq,
      int64Zero_toUInt64]
    rw [← ne_eq, toUInt64_ne_zero (by omega)]
    omega
  · simp only [List.length_map, Array.length_toList] at hk
    simp only [List.getElem_map, Array.getElem_toList]
    exact roundC_spec hcap hN4 hk acc

end NativeVm.Code.P3
