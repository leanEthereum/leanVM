/-
  LeanVM.Protocol.Whir.Sound.LowMsgC

  A polynomial's low part from its values on `U_κ`: the inverse additive transform, limb by limb.
-/

module

public import LeanVM.Protocol.Whir.Sound.Tuple
import LeanVM.Protocol.Extraction.Novel
public import LeanVM.Protocol.Extraction.Extractor
public import CompPoly.Fields.Binary.AdditiveNTT.Coset

/-!
# The low part, computed

`lowMsg κ P` (`Tuple.lean`) is the message whose polynomial is `P mod W_κ`. On `U_κ`, where `W_κ`
vanishes, `P` and `P mod W_κ` agree, and the message's polynomial takes the values
`Σ_j c_j·X_j(x_v)`; the inverse additive transform (`Extraction.novelInv`, over `K`) recovers the
coefficients from those values. Over `E` it runs on each limb, the basis values being in `K`
(`novelInvE`, `lowMsg_eq_novelInvE`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Whir Polynomial

@[expose] public section

theorem limb_mul_ofK (a : E) (k : K) (i : Fin 2) : (a * ofK k).limb i = a.limb i * k := by
  rw [← ofLimbs_limb a, ofK_eq_ofLimbs, mul_limbs]
  fin_cases i <;> simp

theorem limb_sum {ι : Type*} (s : Finset ι) (f : ι → E) (i : Fin 2) :
    (∑ j ∈ s, f j).limb i = ∑ j ∈ s, (f j).limb i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [limb_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, limb_add, ih]

theorem eval_vanE_ofBits {κ v : ℕ} (hv : v < 2 ^ κ) : (vanE κ).eval (ofK (K.ofBits v)) = 0 := by
  rw [vanE, eval_map, show ofK (K.ofBits v) = algebraMap K E (K.ofBits v) from rfl, eval₂_hom,
    eval_vanishing, (vanishingAt_eq_zero_iff κ _).mpr (Finset.mem_image.mpr
      ⟨v, Finset.mem_range.mpr hv, rfl⟩), map_zero]

theorem eval_modByMonic_vanE {κ v : ℕ} (hv : v < 2 ^ κ) (P : E[X]) :
    (P %ₘ vanE κ).eval (ofK (K.ofBits v)) = P.eval (ofK (K.ofBits v)) := by
  conv_rhs => rw [← modByMonic_add_div P (vanE κ)]
  rw [eval_add, eval_mul, eval_vanE_ofBits hv, zero_mul, add_zero]

theorem eval_msgPoly (κ : ℕ) (g : (Fin κ → Bool) → E) (x : K) :
    (msgPoly κ g).eval (ofK x) = ∑ u, g u * ofK (novelAt (bitsToNat u) x) := by
  simp only [msgPoly, LinearMap.coe_mk, AddHom.coe_mk, eval_finsetSum, eval_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [eval_map, show ofK x = algebraMap K E x from rfl, eval₂_hom, eval_novel]
  rfl

/-- The coefficients of a message, by index. -/
def coeffOf {κ : ℕ} (g : (Fin κ → Bool) → E) (j : ℕ) : E :=
  if h : j < 2 ^ κ then g ((bitsEquiv κ).symm ⟨j, h⟩) else 0

theorem sum_cube_eq_range {κ : ℕ} (f : ℕ → E) :
    ∑ u : Fin κ → Bool, f (bitsToNat u) = ∑ j ∈ Finset.range (2 ^ κ), f j := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv (bitsEquiv κ) _ _ fun u ↦ by rw [bitsEquiv_val]

theorem coeffOf_bitsToNat {κ : ℕ} (g : (Fin κ → Bool) → E) (u : Fin κ → Bool) :
    coeffOf g (bitsToNat u) = g u := by
  have hu := bitsToNat_lt u
  rw [coeffOf, dite_eq_left hu]
  have h : (⟨bitsToNat u, hu⟩ : Fin (2 ^ κ)) = bitsEquiv κ u := Fin.ext (bitsEquiv_val u).symm
  rw [h, Equiv.symm_apply_apply]

/-- The limbs of an array over `E`. -/
def limbArr (i : Fin 2) (y : Array E) : Array K := y.map (·.limb i)

/-- **The inverse additive transform over `E`**, limb by limb. -/
def novelInvE (κ : ℕ) (y : Array E) : Array E :=
  let a := Extraction.novelInv κ (limbArr 0 y)
  let b := Extraction.novelInv κ (limbArr 1 y)
  Array.ofFn fun j : Fin (2 ^ κ) ↦ E.ofLimbs (a.getD j 0) (b.getD j 0)

/-- A polynomial's values on `U_κ`. -/
noncomputable def valsU (κ : ℕ) (P : E[X]) : Array E :=
  Array.ofFn fun v : Fin (2 ^ κ) ↦ P.eval (ofK (K.ofBits v.val))

/-- **The low part from the values on `U_κ`.** -/
theorem lowMsg_eq_novelInvE {κ : ℕ} (hκ : κ ≤ 64) (P : E[X]) (u : Fin κ → Bool) :
    lowMsg κ P u = (novelInvE κ (valsU κ P)).getD (bitsToNat u) 0 := by
  set g := lowMsg κ P
  have hy : ∀ v < 2 ^ κ, P.eval (ofK (K.ofBits v)) =
      ∑ j ∈ Finset.range (2 ^ κ), coeffOf g j * ofK (novelAt j (K.ofBits v)) := by
    intro v hv
    rw [← eval_modByMonic_vanE hv, ← msgPoly_lowMsg hκ, eval_msgPoly]
    rw [← sum_cube_eq_range (fun j ↦ coeffOf g j * ofK (novelAt j (K.ofBits v)))]
    exact Finset.sum_congr rfl fun u' _ ↦ by rw [coeffOf_bitsToNat]
  have hlimb : ∀ i : Fin 2, Extraction.novelInv κ (limbArr i (valsU κ P)) =
      Array.ofFn fun j : Fin (2 ^ κ) ↦ (coeffOf g j).limb i := by
    intro i
    refine Extraction.NovelProofs.novelInv_eval hκ (fun j ↦ (coeffOf g j).limb i) _
      (by simp [limbArr, valsU]) fun v hv ↦ ?_
    simp only [limbArr, valsU, Array.getD_eq_getD_getElem?, Array.getElem?_map,
      Array.getElem?_ofFn, hv, ↓reduceDIte, Option.map_some, Option.getD_some]
    rw [hy v hv, limb_sum]
    exact Finset.sum_congr rfl fun j _ ↦ limb_mul_ofK _ _ _
  have hu := bitsToNat_lt u
  simp only [novelInvE, hlimb, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hu,
    ↓reduceDIte, Option.getD_some]
  rw [ofLimbs_limb, coeffOf_bitsToNat]

end
end LeanVM.Protocol.Whir.Sound
