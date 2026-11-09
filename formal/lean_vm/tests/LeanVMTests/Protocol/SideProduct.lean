import LeanVM.Protocol.Fingerprint

/-!
# Fingerprint and side-product tests

Over `E`, on concrete tuples:

* **One weight per slot.** At the indicator of slot `k` the fingerprint reads coordinate `k`.
* **The separator enters.** Two tuples equal but at slot 0 have different fingerprints: the
  fingerprint reads slot 0, where the bus puts the domain separator.
* **Multiplicities.** The product counts a tuple pushed twice twice, in characteristic two too:
  `{t}` and `{t, t}` give different products at a challenge, and different polynomials
  (`sideProduct_poly_eq_iff`). A sum of fingerprints, the shape a balance summed in the field
  takes, gives `0` for `{t, t}` and for `∅` alike.
* **Order.** The product of a list of tuples does not depend on its order.
* **The collision bound** applies to `{t}` and `{t, t}` with `N = 2`: at most `2·|E|^16`
  challenges collide.
* **The bound is attained.** The zero tuple and `e₀`, whose fingerprint is `α₀`, collide exactly
  where `α₀ = 0`, at `|E|^16` challenges: the bound `N·|E|^16` at `N = 1`.

A plain file, so `#guard` evaluates the compiled definitions. Values of `E` written with numerals
are named as definitions before a guard uses them.
-/

namespace LeanVMTests.Protocol.SideProduct

open LeanVM.Parameters LeanVM.Protocol CompPoly.Extension

/-- A tuple with distinct coordinates: coordinate `i` is the polynomial whose bits are `i + 1`. -/
def t : Vector K 16 := Vector.ofFn fun i ↦ K.ofBits (i.val + 1)

/-- The same tuple with another separator. -/
def t' : Vector K 16 := t.set 0 (K.ofBits 100)

/-- `0` and `1` in `E`. -/
def e0 : E := 0
def e1 : E := 1

/-- A challenge off `K`: slot `i`'s weight is `x^(3i + 7)`-ish plus `y` times another word. -/
def α : Fin 16 → E := fun i ↦ ofK (K.ofBits (3 * i.val + 7)) + Ext.gen * ofK (K.ofBits (i.val + 1))
def β : E := Ext.gen * Ext.gen + ofK (K.ofBits 5)

/-- The indicator of slot `k`. -/
def ind (k : Fin 16) : Fin 16 → E := fun i ↦ if i = k then 1 else 0

-- At the indicator of slot `k` the fingerprint reads coordinate `k`.
#guard fingerprint (ind 5) t = ofK t[5]
#guard fingerprint (ind 1) t ≠ ofK t[8]

-- The separator is read: tuples differing only at slot 0 have different fingerprints.
#guard t'[1] = t[1] ∧ t'[15] = t[15]
#guard fingerprint α t ≠ fingerprint α t'

-- A tuple pushed twice is not a tuple pushed once.
#guard sideProduct α β {t} ≠ sideProduct α β {t, t}
#guard sideProduct α β {t, t} = (β - fingerprint α t) * (β - fingerprint α t)

-- A sum of fingerprints in characteristic two forgets the pair.
#guard fingerprint α t + fingerprint α t = e0

-- An honest padding row's leaf is `1`, whatever `β`.
#guard β - fingerprint α t + (1 - (β - fingerprint α t)) = e1

-- The polynomials differ: the product polynomial determines the multiset.
example : grandProductPoly ({t} : Multiset (Vector K 16)) ≠
    grandProductPoly ({t, t} : Multiset (Vector K 16)) := fun h ↦ by
  have := congrArg Multiset.card ((sideProduct_poly_eq_iff _ _).mp h)
  simp at this

-- The product does not depend on the order of the tuples.
example (a : Fin 16 → E) (b : E) (u v : Vector K 16) :
    sideProduct a b ↑[u, v] = sideProduct a b ↑[v, u] := by
  rw [Multiset.coe_eq_coe.mpr (List.Perm.swap v u [])]

-- The collision bound on `{t}` and `{t, t}`: at most `2·|E|^16` challenges collide.
example : Nat.card {ab : (Fin 16 → E) × E //
      sideProduct ab.1 ab.2 {t} = sideProduct ab.1 ab.2 {t, t}} ≤ 2 * Nat.card E ^ 16 :=
  card_sideProduct_collision_le (by simp) (by simp) (by simp)

/-! ## The bound is attained -/

/-- The tuple with `1` at slot 0 and `0` elsewhere. -/
def e₀ : Vector K 16 := Vector.ofFn fun i ↦ if i.val = 0 then 1 else 0

/-- The zero tuple. -/
def zero16 : Vector K 16 := Vector.replicate 16 0

theorem fingerprint_e₀ (a : Fin 16 → E) : fingerprint a e₀ = a 0 := by
  simp only [fingerprint, fingerprintWeights]
  rw [Finset.sum_eq_single (0 : Fin 16)]
  · have h0 : (e₀[(0 : Fin 16)] : K) = 1 := by simp [e₀]
    rw [h0, show ofK (1 : K) = 1 from _root_.map_one (algebraMap K E), mul_one]
    simp
  · intro i _ hi
    have : (e₀[i] : K) = 0 := by simp [e₀, hi]
    simp [this]
  · simp

theorem fingerprint_zero16 (a : Fin 16 → E) : fingerprint a zero16 = 0 := by
  simp [fingerprint, zero16]

/-- The colliding challenges of `{0}` and `{e₀}` are those where `α₀ = 0`. -/
theorem collide_iff (ab : (Fin 16 → E) × E) :
    sideProduct ab.1 ab.2 {zero16} = sideProduct ab.1 ab.2 {e₀} ↔ ab.1 0 = 0 := by
  simp only [sideProduct, Multiset.map_singleton, Multiset.prod_singleton, fingerprint_zero16,
    fingerprint_e₀, sub_zero]
  constructor
  · intro h
    exact sub_eq_self.mp h.symm
  · intro h
    rw [h, sub_zero]

/-- The challenges with `α₀ = 0` are the other coordinates. -/
def zeroFirst : {ab : (Fin 16 → E) × E // ab.1 0 = 0} ≃ (Fin 15 → E) × E where
  toFun ab := (Fin.tail ab.1.1, ab.1.2)
  invFun p := ⟨(Fin.cons 0 p.1, p.2), rfl⟩
  left_inv ab := by
    obtain ⟨⟨a, b⟩, h⟩ := ab
    refine Subtype.ext (Prod.ext (funext fun i ↦ ?_) rfl)
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact h.symm
    · rfl
  right_inv p := Prod.ext (by simp) rfl

-- Exactly `1·|E|^16` challenges collide: the bound at `N = 1`.
example : Nat.card {ab : (Fin 16 → E) × E //
    sideProduct ab.1 ab.2 {zero16} = sideProduct ab.1 ab.2 {e₀}} = 1 * Nat.card E ^ 16 := by
  rw [Nat.card_congr ((Equiv.subtypeEquivRight collide_iff).trans zeroFirst), Nat.card_prod,
    Nat.card_fun, Nat.card_fin, one_mul]
  ring

end LeanVMTests.Protocol.SideProduct
