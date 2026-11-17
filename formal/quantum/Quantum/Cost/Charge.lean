module

public import PolyFun.IPFunctor.Free.Bound

@[expose] public section

/-!
# Rescaling charge bounds

Path-wise charge bounds (`IPFunctor.IFreeM.IsChargeBound`) under a change of charge: a pointwise
smaller charge keeps every bound, and a charge scaled by `k` within `n` is the charge within
`n / k`. Together: if every command costs at least `k` times its charge `c` under the cost `κ`,
a tree within `n` under `κ` is within `n / k` under `c`. This turns a gate budget into a call
budget (`Quantum.Cost.calls_le_of_gates`).

## Main statements

* `IsChargeBound.mono_charge`: a pointwise smaller charge keeps every bound.
* `IsChargeBound.div`: `k · c` within `n` gives `c` within `n / k`.
* `IsChargeBound.of_scaled_le`: `k · c ≤ κ` pointwise and `κ` within `n` give `c` within `n / k`.
-/

namespace IPFunctor.IFreeM

variable {I : Type*} {P : IPFunctor.Endo I} {X : I → Type*} {s : I}
  {c c' κ : (s : I) → P.A s → ℕ}

/-- **A pointwise smaller charge keeps every bound.** -/
theorem IsChargeBound.mono_charge (hc : ∀ s a, c s a ≤ c' s a) {x : IFreeM P X s} {n : ℕ}
    (h : x.IsChargeBound c' n) : x.IsChargeBound c n := by
  induction x using IFreeM.inductionOn generalizing n with
  | pure _ _ => exact isChargeBound_pure _ _
  | liftBind s a next ih =>
      rw [isChargeBound_liftBind_iff] at h ⊢
      exact ⟨(hc s a).trans h.1, fun b ↦ (ih b (h.2 b)).mono (Nat.sub_le_sub_left (hc s a) n)⟩

/-- **Dividing a scaled charge.** `k · c` within `n` gives `c` within `n / k`. -/
theorem IsChargeBound.div {k : ℕ} (hk : 0 < k) {x : IFreeM P X s} {n : ℕ}
    (h : x.IsChargeBound (fun s a ↦ k * c s a) n) : x.IsChargeBound c (n / k) := by
  induction x using IFreeM.inductionOn generalizing n with
  | pure _ _ => exact isChargeBound_pure _ _
  | liftBind s a next ih =>
      rw [isChargeBound_liftBind_iff] at h ⊢
      have h1 : k * c s a ≤ n := h.1
      refine ⟨(Nat.le_div_iff_mul_le hk).2 ((Nat.mul_comm _ _).trans_le h1), fun b ↦ ?_⟩
      rw [← Nat.sub_mul_div]
      exact ih b (h.2 b)

/-- **A charge dominated by a scaled cost.** If `k · c ≤ κ` pointwise and `κ` is within `n`,
then `c` is within `n / k`. -/
theorem IsChargeBound.of_scaled_le {k : ℕ} (hk : 0 < k) (hc : ∀ s a, k * c s a ≤ κ s a)
    {x : IFreeM P X s} {n : ℕ} (h : x.IsChargeBound κ n) : x.IsChargeBound c (n / k) :=
  (h.mono_charge (c := fun s a ↦ k * c s a) hc).div hk

end IPFunctor.IFreeM

end
