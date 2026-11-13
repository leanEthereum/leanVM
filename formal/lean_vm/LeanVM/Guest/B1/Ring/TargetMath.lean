/-
  LeanVM.Guest.B1.Ring.TargetMath

  The algebra of `ring_switch_target`: its eight Horner sums in `w_p = 1/z_p`, raised and
  recombined, are the statement's `ringTarget`.
-/

module

public import LeanVM.Protocol.RingVerifier

/-!
# `ring_switch_target`'s algebra

`ring_switch_target` runs eight Horner chains over the slices' images `ψ_i = Ψ(s_i)`, chain `p` in
`w_p = RING_W[p]` (`ringWK`), so that it ends at `Σ_i w_p^(63 - i) ψ_i` (`wHorner`); it returns
`(Σ_p f_p (Σ_i w_p^(63 - i) ψ_i)^(2^(8p))) · x^63`. As `w_p^(2^(8p)) · x = 1` (`ringWK_frob`,
decided in `K`), each chain raised to `2^(8p)` and scaled by `x^63` is `Σ_i x^i ψ_i^(2^(8p))`,
so the result is `Σ_i x^i Φ(s_i)`, the statement's `ringTarget` (`Ring.ringTarget_eq`):
`guest_target_eq`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Ring Finset

@[expose] public section

/-- `RING_W`: `w_p = z_p⁻¹`, `z_p = x^(2^(64 - 8p))`, the points of the guest's Horner chains. -/
def ringWK : List K :=
  [K.ofBits 9223372036854775821, K.ofBits 3553348109046704045, K.ofBits 6991530515271458276,
    K.ofBits 8630512066575425152, K.ofBits 8543422393626980591, K.ofBits 2539607212871081783,
    K.ofBits 4576227429734584387, K.ofBits 15746294976420764300]

/-- `n` squarings in `K`. -/
def sqK : ℕ → K → K
  | 0, a => a
  | n + 1, a => sqK n (a * a)

theorem sqK_eq : ∀ (n : ℕ) (a : K), sqK n a = a ^ 2 ^ n
  | 0, a => by simp [sqK]
  | n + 1, a => by rw [sqK, sqK_eq n, ← pow_two, ← pow_mul, ← pow_succ']

theorem ringWK_sq : ∀ p < 8, sqK (8 * p) (ringWK.getD p 0) * g = 1 := by decide +kernel

/-- `w_p^(2^(8p)) · x = 1`. -/
theorem ringWK_frob {p : ℕ} (hp : p < 8) : ofK (ringWK.getD p 0) ^ 2 ^ (8 * p) * genE = 1 := by
  have h := ringWK_sq p hp
  rw [sqK_eq] at h
  change (algebraMap K E _) ^ _ * algebraMap K E g = 1
  rw [← map_pow, ← map_mul, h, map_one]

/-- Chain `p`: Horner in `w` over `ψ`. -/
def wHorner (w : E) (ψ : List E) : E := ψ.foldl (fun acc c ↦ acc * w + c) 0

theorem wHorner_eq (w : E) (l : List E) : wHorner w l = hornerEval l.reverse w := by
  rw [wHorner, hornerEval, List.foldr_reverse]

theorem reverse_ofFn64 (ψ : Fin 64 → E) : (List.ofFn ψ).reverse = List.ofFn fun i ↦ ψ i.rev := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]
  congr 1
  ext
  simp only [Fin.val_rev]
  simp only [List.length_reverse, List.length_ofFn] at h1
  omega

theorem wHorner_ofFn (w : E) (ψ : Fin 64 → E) :
    wHorner w (List.ofFn ψ) = ∑ i : Fin 64, ψ i * w ^ (63 - (i : ℕ)) := by
  rw [wHorner_eq, reverse_ofFn64, hornerEval_ofFn]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i ↦ ?_
  simp only [Fin.revPerm_apply, Fin.val_rev]
  congr 2
  omega

theorem ringW_eq (i : Fin 64) : ringW i = genE ^ (i : ℕ) := by
  unfold ringW genE
  rw [map_pow]
  rfl

/-- **The guest's target is the statement's.** -/
theorem guest_target_eq (s : Fin 64 → E) (f g' : Fin 8 → E) :
    (∑ p : Fin 8, f p * wHorner (ofK (ringWK.getD p 0))
        (List.ofFn fun i ↦ Verifier.ringPsi (s i) (List.ofFn g')) ^ 2 ^ (8 * (p : ℕ))) *
        genE ^ 63 =
      Verifier.ringTarget (List.ofFn s) (List.ofFn f) (List.ofFn g') := by
  rw [verifier_ringTarget, ringTarget_eq]
  simp only [frobPhi, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [wHorner_ofFn, sum_pow_char_pow, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hw := ringWK_frob p.isLt
  have hi : (i : ℕ) ≤ 63 := by omega
  rw [verifier_ringPsi, ringPsi_ofFn, mul_pow, ← pow_mul, mul_comm (63 - (i : ℕ)), pow_mul]
  have e : genE ^ 63 = genE ^ (i : ℕ) * genE ^ (63 - (i : ℕ)) := by
    rw [← pow_add]; congr 1; omega
  rw [e, ringW_eq]
  have hp : (ofK (ringWK.getD p 0) ^ 2 ^ (8 * (p : ℕ))) ^ (63 - (i : ℕ)) *
      genE ^ (63 - (i : ℕ)) = 1 := by rw [← mul_pow, hw, one_pow]
  rw [show 2 ^ (8 * (p : ℕ)) = (2 ^ 8) ^ (p : ℕ) from pow_mul 2 8 p] at hp
  generalize (2 ^ 8) ^ (p : ℕ) = N at hp ⊢
  generalize 63 - (i : ℕ) = M at hp ⊢
  linear_combination (f p * frobPsi g' (s i) ^ N * genE ^ (i : ℕ)) * hp

end
end LeanVM.Guest.B1.VerifySub
