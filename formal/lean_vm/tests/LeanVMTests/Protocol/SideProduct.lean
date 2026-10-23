import LeanVM.Protocol.Fingerprint

/-!
# Fingerprint and side-product tests

Over `E`, on concrete tuples:

* **Bit order.** At a Boolean `α` the fingerprint reads one coordinate, `α_k` the bit `k` of its
  index, low bit first: `α = (1, 0, 1, 0)` reads coordinate 5, `α = (1, 0, 0, 0)` coordinate 1
  and not 8. At a point off the cube it is the tuple's extension (`fingerprint_eq_eval₂Mle`).
* **The separator enters.** Two tuples equal but at coordinate 0 have different fingerprints:
  the fingerprint reads coordinate 0, where the bus puts the domain separator.
* **Multiplicities.** The product counts a tuple pushed twice twice, in characteristic two too:
  `{t}` and `{t, t}` give different products at a challenge, and different polynomials
  (`sideProduct_poly_eq_iff`). A sum of fingerprints, the shape a balance summed in the field
  takes, gives `0` for `{t, t}` and for `∅` alike.
* **Order.** The product of a list of tuples does not depend on its order.
* **The collision bound** applies to `{t}` and `{t, t}` with `N = 2`: at most `8·|E|⁴`
  challenges collide.
* **The factor 4 is needed.** The zero tuple and `e₁₅`, whose fingerprint is `α₀α₁α₂α₃`, collide
  exactly where `α₀α₁α₂α₃ = 0`, at more than `3·|E|⁴` challenges: no bound `c·N·|E|⁴` with
  `c ≤ 3` holds, so the fingerprint's degree four cannot be counted as one.

A plain file, so `#guard` evaluates the compiled definitions. Values of `E` written with numerals
are named as definitions before a guard uses them.
-/

namespace LeanVMTests.Protocol.SideProduct

open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval OracleComp
open scoped ENNReal

/-- A tuple with distinct coordinates: coordinate `i` is the polynomial whose bits are `i + 1`. -/
def t : Vector K 16 := Vector.ofFn fun i ↦ K.ofBits (i.val + 1)

/-- The same tuple with another separator. -/
def t' : Vector K 16 := t.set 0 (K.ofBits 100)

/-- `0` and `1` in `E`. -/
def e0 : E := 0
def e1 : E := 1

/-- Two challenges off the cube. -/
def α : Fin 4 → E := ![y, y + 1, y * y, y * y + 1]
def β : E := y * y * y + y

-- At a Boolean point the fingerprint reads one coordinate, low bit first.
#guard fingerprint ![e1, e0, e1, e0] t = ofK t[5]
#guard fingerprint ![e1, e0, e0, e0] t = ofK t[1]
#guard fingerprint ![e1, e0, e0, e0] t ≠ ofK t[8]

-- Off the cube it is the tuple's extension at `α`.
#guard fingerprint α t = eval₂Mle (n := 4) t (algebraMap K E) (Vector.ofFn α)

-- The separator is read: tuples differing only at coordinate 0 have different fingerprints.
#guard t'[1] = t[1] ∧ t'[15] = t[15]
#guard fingerprint α t ≠ fingerprint α t'

-- A tuple pushed twice is not a tuple pushed once.
#guard sideProduct α β {t} ≠ sideProduct α β {t, t}
#guard sideProduct α β {t, t} = (β - fingerprint α t) * (β - fingerprint α t)

-- A sum of fingerprints in characteristic two forgets the pair.
#guard fingerprint α t + fingerprint α t = e0

-- The polynomials differ: the product polynomial determines the multiset.
example : grandProductPoly (n := 4) ({t} : Multiset (Vector K 16)) ≠
    grandProductPoly (n := 4) ({t, t} : Multiset (Vector K 16)) := fun h ↦ by
  have := congrArg Multiset.card ((sideProduct_poly_eq_iff _ _).mp h)
  simp at this

-- The product does not depend on the order of the tuples.
example (a : Fin 4 → E) (b : E) (u v : Vector K 16) :
    sideProduct a b ↑[u, v] = sideProduct a b ↑[v, u] := by
  rw [Multiset.coe_eq_coe.mpr (List.Perm.swap v u [])]

-- The collision bound on `{t}` and `{t, t}`: at most `4·2·|E|⁴` challenges collide.
example : Nat.card {ab : (Fin 4 → E) × E //
      sideProduct ab.1 ab.2 {t} = sideProduct ab.1 ab.2 {t, t}} ≤ 4 * 2 * Nat.card E ^ 4 :=
  card_sideProduct_collision_le (by simp) (by simp) (by simp)

-- Its probability form: a uniform challenge collides with probability at most `8 / |E|`.
example : Pr{let ab ← $ᵗ ((Fin 4 → E) × E)}[
      sideProduct ab.1 ab.2 {t} = sideProduct ab.1 ab.2 {t, t}] ≤
    (4 * 2 : ℕ) / (Fintype.card E : ℝ≥0∞) :=
  sideProduct_collision (by simp) (by simp) (by simp)

/-! ## The factor 4 is needed -/

/-- The tuple with `1` at coordinate 15 and `0` elsewhere. -/
def e15 : Vector K 16 := Vector.ofFn fun i ↦ if i.val = 15 then 1 else 0

/-- The zero tuple. -/
def zero16 : Vector K 16 := Vector.replicate 16 0

/-- Coordinate 15's weight is the product of the four coordinates of `α`: all its bits are set. -/
theorem fingerprint_e15 (a : Fin 4 → E) : fingerprint a e15 = a 0 * a 1 * a 2 * a 3 := by
  simp only [fingerprint, fingerprintWeights]
  rw [Finset.sum_eq_single (15 : Fin 16)]
  · have h15 : (e15[(15 : Fin 16)] : K) = 1 := by simp [e15]
    rw [h15, show ofK (1 : K) = 1 from _root_.map_one (algebraMap K E), mul_one,
      lagrangeBasis_getElem_nat _ (by norm_num), Fin.prod_univ_four]
    simp (config := { decide := true })
  · intro i _ hi
    have hi' : (i : ℕ) ≠ 15 := fun h ↦ hi (Fin.ext h)
    have : (e15[i] : K) = 0 := by simp [e15, hi']
    simp [this]
  · simp

theorem fingerprint_zero16 (a : Fin 4 → E) : fingerprint a zero16 = 0 := by
  simp [fingerprint, zero16]

/-- The colliding challenges of `{0}` and `{e₁₅}` are those where `α₀α₁α₂α₃ = 0`. -/
theorem collide_iff (ab : (Fin 4 → E) × E) :
    sideProduct ab.1 ab.2 {zero16} = sideProduct ab.1 ab.2 {e15} ↔ ¬ ∀ i, ab.1 i ≠ 0 := by
  simp only [sideProduct, Multiset.map_singleton, Multiset.prod_singleton, fingerprint_zero16,
    fingerprint_e15, sub_zero, not_forall, not_not]
  constructor
  · intro h
    have h0 : ab.1 0 * ab.1 1 * ab.1 2 * ab.1 3 = 0 := by linear_combination h
    simp only [mul_eq_zero] at h0
    rcases h0 with ((h | h) | h) | h <;> exact ⟨_, h⟩
  · rintro ⟨i, hi⟩
    have h0 : ∏ j, ab.1 j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [Fin.prod_univ_four] at h0
    rw [h0, sub_zero]

-- More than `3·|E|⁴` challenges collide, against the bound's `4·|E|⁴`.
example : 3 * 1 * Nat.card E ^ 4 <
    Nat.card {ab : (Fin 4 → E) × E // sideProduct ab.1 ab.2 {zero16} = sideProduct ab.1 ab.2 {e15}} := by
  classical
  have hnz : Fintype.card {ab : (Fin 4 → E) × E // ∀ i, ab.1 i ≠ 0} =
      (Fintype.card E - 1) ^ 4 * Fintype.card E := by
    rw [Fintype.card_congr (β := (Fin 4 → {e : E // e ≠ 0}) × E)
      { toFun := fun ab ↦ (fun i ↦ ⟨ab.1.1 i, ab.2 i⟩, ab.1.2)
        invFun := fun p ↦ ⟨(fun i ↦ (p.1 i).1, p.2), fun i ↦ (p.1 i).2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }]
    simp [Fintype.card_subtype_compl, Fintype.card_prod, Fintype.card_pi]
  rw [Nat.card_congr (Equiv.subtypeEquivRight collide_iff),
    Nat.card_eq_fintype_card (α := {ab : (Fin 4 → E) × E // ¬ ∀ i, ab.1 i ≠ 0}),
    Fintype.card_subtype_compl, hnz, Nat.card_eq_fintype_card (α := E)]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, card_E]
  norm_num

end LeanVMTests.Protocol.SideProduct
