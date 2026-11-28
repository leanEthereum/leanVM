/-
  LeanVM.Protocol.Hotwire.Mirror

  The mirror test of Emile Wambsgans: in characteristic two, a chunk is one-hot exactly when
  `ẽ(r)·ẽ(1 + r) + Π_h r_h·(1 + r_h)` vanishes as a polynomial in `r`; and the batched check the
  verifier runs over every chunk of every used pointer.
-/

module

public import LeanVM.Protocol.Hotwire.Window
public import ToMathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The mirror test

Hotwire commits each chunk of a pointer as a table `e` over `2^w` values that should be one-hot
(`OneHot`, `Window.lean`). The verifier (`crates/verifier/src/link.rs`) reads chunk `i` at its part
`r_i` of the index point and at the mirror point `1 + r_i` (`Functionals`: the tables `D_i` at `r`
and at `1 + r`, the latter `eq_kernel(r_i)` reversed), and adds the certificate term
`Σ_i certs_i·(D_i(r_i)·D_i(1 + r_i) + π_i)` to the summand (`Functionals::summand`), where
`π_i = Π_h r_h·(1 + r_h)` over chunk `i`'s coordinates (`Functionals::mirrors`). Here, for a point
`r` (a list, as in `Eq.lean`):

* `mirrorCert r e = ẽ(r)·ẽ(1 + r) + π_w(r)`, `ẽ = chunkEval` (`mirrorPt`, `mirror`);
* **completeness** (`mirrorCert_eq_zero_of_oneHot`): in characteristic two a one-hot chunk gives
  `0` at every point, over any commutative ring;
* **the mirror identity** (`mirrorPoly_eq_zero_iff`): over a field of characteristic two, the
  certificate is the zero polynomial in `r` exactly when `e` is one-hot at some `σ < 2^w`. No
  booleanity and no Hamming weight are needed: `e` may take any values in `F` (a chunk with three
  ones fails). The proof splits off `r_0`: with `e = (1 + r_0)·e_even + r_0·e_odd`, the identity at
  `r_0 = 0` and `r_0 = 1` gives `ẽ_even·ẽ_odd(1 + ·) = 0` and `ẽ_odd·ẽ_even(1 + ·) = 0`, so one half
  vanishes (the polynomials form a domain, and `r ↦ 1 + r` is an involution), and the
  `r_0·(1 + r_0)` part is the identity for the other half;
* **Schwartz-Zippel** (`card_mirrorCert_eq_zero_le`): a chunk that is not one-hot passes at no more
  than `2w·|F|^(w − 1)` of the `|F|^w` points (`totalDegree_mirrorPoly`);
* **the batched check** (`batchedCert`, the paper's identity (6) in characteristic two, its
  Lemma 3.2): `θ·Σ_{u : b(u)} eq(τ, u)·Σ_q ε_q·Σ_i ν_i·(ẽ_{q,i,u}(ρ_i)·ẽ_{q,i,u}(1 + ρ_i) + π_{w_i}(ρ_i))`
  over the rows `u < 2^m` the public gate `b` marks, the pointer columns `q` and the chunks `i`
  (the verifier's certificate coefficients `certs`, `ε_q·ν_i` for column `q`'s chunk `i`, with the
  row weight `θ·eq(τ, u)` that the row sum-check carries). If some chunk of a gated row is not
  one-hot, it is a nonzero polynomial of total degree at most `m + 3 + 2·w_max` in
  `(θ, τ, ε, ν, ρ)` (`batchedPoly_ne_zero`, `totalDegree_batchedPoly`), so it vanishes at no more
  than that many `|F|`-ths of the points (`card_batchedCert_eq_zero_le`).
-/

namespace LeanVM.Protocol.Hotwire

open Finset MvPolynomial

@[expose] public section

/-! ## Over a commutative ring -/

section Ring

variable {R : Type*} [CommRing R]

/-- The mirror point `1 + r`, coordinate-wise: in characteristic two `eq(1 + r, v) = eq(r, v̄)`,
`v̄` the value with its bits flipped (the verifier's reversed `eq_kernel`, `Functionals::new`). -/
def mirrorPt (r : List R) : List R := r.map (1 + ·)

/-- `π_w(r) = Π_h r_h·(1 + r_h)`, the verifier's `Functionals::mirrors`. -/
def mirror (r : List R) : R := (r.map fun z => z * (1 + z)).prod

/-- The mirror certificate `ẽ(r)·ẽ(1 + r) + π_w(r)` of a chunk's table `e` at `r`: the chunk's term
`D_i(r_i)·D_i(1 + r_i) + π_i` of `Functionals::summand`. -/
def mirrorCert (r : List R) (e : ℕ → R) : R := chunkEval r e * chunkEval (mirrorPt r) e + mirror r

@[simp] theorem length_mirrorPt (r : List R) : (mirrorPt r).length = r.length := List.length_map _

theorem mirrorPt_cons (z : R) (r : List R) : mirrorPt (z :: r) = (1 + z) :: mirrorPt r := rfl

@[simp] theorem mirror_nil : mirror ([] : List R) = 1 := rfl

theorem mirror_cons (z : R) (r : List R) : mirror (z :: r) = z * (1 + z) * mirror r := by
  simp [mirror]

/-- Splitting off the first coordinate: the even values pair with `1 − r_0`, the odd with `r_0`. -/
theorem chunkEval_cons (z : R) (r : List R) (e : ℕ → R) :
    chunkEval (z :: r) e =
      (1 - z) * chunkEval r (fun v => e (2 * v)) + z * chunkEval r (fun v => e (2 * v + 1)) := by
  simp only [chunkEval, List.length_cons]
  rw [show 2 ^ (r.length + 1) = 2 * 2 ^ r.length by ring, sum_range_two_mul, mul_sum, mul_sum,
    ← sum_add_distrib]
  refine sum_congr rfl fun v _ => ?_
  rw [eqAt_cons_two_mul, eqAt_cons_two_mul_add_one]
  ring

section Map

variable {S G : Type*} [CommRing S] [FunLike G R S] [RingHomClass G R S]

theorem map_eqAt (f : G) : ∀ (r : List R) (j : ℕ), f (eqAt r j) = eqAt (r.map f) j
  | [], _ => by simp
  | z :: r, j => by
    rw [eqAt_cons, List.map_cons, eqAt_cons, map_mul, map_eqAt f r]
    split_ifs <;> simp

theorem map_chunkEval (f : G) (r : List R) (e : ℕ → R) :
    f (chunkEval r e) = chunkEval (r.map f) (fun v => f (e v)) := by
  simp only [chunkEval, map_sum, map_mul, map_eqAt, List.length_map]

theorem map_mirrorPt (f : G) (r : List R) : (mirrorPt r).map f = mirrorPt (r.map f) := by
  simp [mirrorPt, Function.comp_def]

theorem map_mirror (f : G) (r : List R) : f (mirror r) = mirror (r.map f) := by
  simp [mirror, map_list_prod, Function.comp_def]

theorem map_mirrorCert (f : G) (r : List R) (e : ℕ → R) :
    f (mirrorCert r e) = mirrorCert (r.map f) (fun v => f (e v)) := by
  rw [mirrorCert, mirrorCert, map_add, map_mul, map_chunkEval, map_chunkEval, map_mirrorPt,
    map_mirror]

end Map

/-- `eq(r, y)·eq(1 + r, y) = π_w(r)` in characteristic two: each coordinate's factor is
`r_h·(1 + r_h)` whichever bit `y` has there. -/
theorem eqAt_mul_eqAt_mirrorPt (h2 : (2 : R) = 0) :
    ∀ (r : List R) (y : ℕ), eqAt r y * eqAt (mirrorPt r) y = mirror r
  | [], _ => by simp [mirrorPt]
  | z :: r, y => by
    rw [mirrorPt_cons, eqAt_cons, eqAt_cons, mirror_cons, ← eqAt_mul_eqAt_mirrorPt h2 r (y / 2)]
    split_ifs
    · ring
    · linear_combination (-z) * eqAt r (y / 2) * eqAt (mirrorPt r) (y / 2) * h2

/-- **Completeness of the mirror test.** In characteristic two, a chunk one-hot at `σ < 2^w` has
certificate `0` at every point `r ∈ R^w`. -/
theorem mirrorCert_eq_zero_of_oneHot (h2 : (2 : R) = 0) (r : List R) (e : ℕ → R) (σ : ℕ)
    (he : OneHot r.length e σ) (hσ : σ < 2 ^ r.length) : mirrorCert r e = 0 := by
  rw [mirrorCert, chunkEval_oneHot r e σ he hσ,
    chunkEval_oneHot (mirrorPt r) e σ (by rwa [length_mirrorPt]) (by rwa [length_mirrorPt]),
    eqAt_mul_eqAt_mirrorPt h2]
  linear_combination mirror r * h2

/-- The Boolean point of `v < 2^w`, bits lowest first. -/
def boolPt (w v : ℕ) : Fin w → R := fun i => if v.testBit i then 1 else 0

/-- `eq(·, j)` at the Boolean point of `v` is `[j = v]`, for `j, v < 2^w`. -/
theorem eqAt_ofFn_boolPt : ∀ (w : ℕ) {j v : ℕ}, j < 2 ^ w → v < 2 ^ w →
    eqAt (List.ofFn (boolPt (R := R) w v)) j = if j = v then 1 else 0
  | 0, j, v, hj, hv => by
    simp only [pow_zero, Nat.lt_one_iff] at hj hv
    subst hj hv
    simp
  | w + 1, j, v, hj, hv => by
    have hj2 : j / 2 < 2 ^ w := by rw [pow_succ] at hj; omega
    have hv2 : v / 2 < 2 ^ w := by rw [pow_succ] at hv; omega
    have hrest : (fun i : Fin w => boolPt (R := R) (w + 1) v i.succ) = boolPt w (v / 2) := by
      funext i
      simp [boolPt, Fin.val_succ, Nat.testBit_add_one]
    have h0 : boolPt (R := R) (w + 1) v 0 = if v % 2 = 1 then 1 else 0 := by simp [boolPt]
    rw [List.ofFn_succ, hrest, eqAt_cons, eqAt_ofFn_boolPt w hj2 hv2, h0]
    by_cases hjv : j = v
    · subst hjv
      rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [h]
    · rw [ite_eq_right hjv]
      by_cases hq : j / 2 = v / 2
      · rw [ite_eq_left hq, mul_one]
        rcases Nat.mod_two_eq_zero_or_one j with hj1 | hj1 <;>
          rcases Nat.mod_two_eq_zero_or_one v with hv1 | hv1
        · omega
        · simp [hj1, hv1]
        · simp [hj1, hv1]
        · omega
      · rw [ite_eq_right hq, mul_zero]

/-- A chunk read at the Boolean point of `v` is its value at `v`. -/
theorem chunkEval_ofFn_boolPt {w v : ℕ} (hv : v < 2 ^ w) (e : ℕ → R) :
    chunkEval (List.ofFn (boolPt (R := R) w v)) e = e v := by
  rw [chunkEval, List.length_ofFn,
    sum_congr rfl fun j hj => by rw [eqAt_ofFn_boolPt w (mem_range.mp hj) hv]]
  simp [hv]

end Ring

/-! ## The mirror identity over a field -/

section Field

variable {F : Type*} [Field F]

/-- The coordinates `r_0, …, r_{w−1}` of a chunk's part of the index point, as polynomials. -/
noncomputable def coords (w : ℕ) : List (MvPolynomial (Fin w) F) := List.ofFn X

/-- The mirror certificate `ẽ(r)·ẽ(1 + r) + π_w(r)` as a polynomial in `r ∈ F^w`. -/
noncomputable def mirrorPoly (w : ℕ) (e : ℕ → F) : MvPolynomial (Fin w) F :=
  mirrorCert (coords w) (fun v => C (e v))

theorem eval_mirrorPoly (w : ℕ) (e : ℕ → F) (r : Fin w → F) :
    eval r (mirrorPoly w e) = mirrorCert (List.ofFn r) e := by
  rw [mirrorPoly, map_mirrorCert]
  simp [coords, List.map_ofFn, Function.comp_def]

theorem two_eq_zero_mv [CharP F 2] {σ : Type*} : (2 : MvPolynomial σ F) = 0 := by
  rw [← map_ofNat (C : F →+* MvPolynomial σ F) 2, CharTwo.two_eq_zero, map_zero]

/-- A table whose polynomial `ẽ` is zero vanishes on the cube. -/
theorem eq_zero_of_chunkEval_coords {w : ℕ} {e : ℕ → F}
    (h : chunkEval (coords w) (fun v => C (e v)) = 0) : ∀ v < 2 ^ w, e v = 0 := by
  intro v hv
  have h' := congrArg (eval (boolPt w v)) h
  have hpt : (coords (F := F) w).map (eval (boolPt w v)) = List.ofFn (boolPt w v) := by
    simp [coords, List.map_ofFn, Function.comp_def]
  rw [map_chunkEval, hpt, map_zero] at h'
  simp only [eval_C] at h'
  rwa [chunkEval_ofFn_boolPt hv] at h'

/-- The substitution `r ↦ 1 + r` takes `ẽ(r)` to `ẽ(1 + r)`. -/
theorem aeval_mirror_chunkEval (w : ℕ) (e : ℕ → F) :
    aeval (fun i : Fin w => 1 + X i) (chunkEval (coords w) fun v => C (e v)) =
      chunkEval (mirrorPt (coords w)) fun v => C (e v) := by
  rw [map_chunkEval]
  simp [coords, mirrorPt, List.map_ofFn, Function.comp_def]

/-- In characteristic two the substitution `r ↦ 1 + r` is an involution: it takes `ẽ(1 + r)` back
to `ẽ(r)`. -/
theorem aeval_mirror_chunkEval_mirrorPt [CharP F 2] (w : ℕ) (e : ℕ → F) :
    aeval (fun i : Fin w => 1 + X i) (chunkEval (mirrorPt (coords w)) fun v => C (e v)) =
      chunkEval (coords w) fun v => C (e v) := by
  have hl : (mirrorPt (coords (F := F) w)).map (aeval fun i : Fin w => (1 + X i : MvPolynomial (Fin w) F)) = coords w := by
    simp only [mirrorPt, coords, List.map_ofFn]
    congr 1
    funext i
    simp only [Function.comp_apply, map_add, map_one, aeval_X]
    linear_combination (two_eq_zero_mv (F := F) (σ := Fin w))
  rw [map_chunkEval, hl]
  simp

/-- `r_0` split off a polynomial point: `coords (w + 1) = r_0 :: (coords w renamed)`. -/
theorem coords_succ (w : ℕ) :
    coords (F := F) (w + 1) = X 0 :: (coords w).map (rename Fin.succ) := by
  simp [coords, List.ofFn_succ, List.map_ofFn, Function.comp_def]

/-- The certificate of `w + 1` coordinates in `r_0` and the halves' certificates' pieces. -/
theorem mirrorPoly_succ (w : ℕ) (e : ℕ → F) :
    mirrorPoly (w + 1) e =
      ((1 - X 0) * rename Fin.succ (chunkEval (coords w) fun v => C (e (2 * v))) +
          X 0 * rename Fin.succ (chunkEval (coords w) fun v => C (e (2 * v + 1)))) *
        ((1 - (1 + X 0)) * rename Fin.succ (chunkEval (mirrorPt (coords w)) fun v => C (e (2 * v))) +
          (1 + X 0) * rename Fin.succ (chunkEval (mirrorPt (coords w)) fun v => C (e (2 * v + 1)))) +
      X 0 * (1 + X 0) * rename Fin.succ (mirror (coords w)) := by
  have hρ : ∀ (r : List (MvPolynomial (Fin w) F)) (g : ℕ → F),
      chunkEval (r.map (rename Fin.succ)) (fun v => C (g v)) =
        rename Fin.succ (chunkEval r fun v => C (g v)) := by
    intro r g
    rw [map_chunkEval]
    simp only [rename_C]
  rw [mirrorPoly, coords_succ, mirrorCert, mirrorPt_cons, chunkEval_cons, chunkEval_cons, mirror_cons,
    hρ, hρ, ← map_mirrorPt, hρ, hρ, ← map_mirror]

/-- Evaluating `r_0` at `c` and keeping the other coordinates undoes the renaming. -/
theorem aeval_cons_rename (w : ℕ) (c : MvPolynomial (Fin w) F) (p : MvPolynomial (Fin w) F) :
    aeval (Fin.cons c X : Fin (w + 1) → MvPolynomial (Fin w) F) (rename Fin.succ p) = p := by
  rw [aeval_rename]
  have : (Fin.cons c X : Fin (w + 1) → MvPolynomial (Fin w) F) ∘ Fin.succ = X := by
    funext i
    simp
  rw [this, aeval_X_left_apply]

theorem aeval_cons_X_zero (w : ℕ) (c : MvPolynomial (Fin w) F) :
    aeval (Fin.cons c X : Fin (w + 1) → MvPolynomial (Fin w) F) (X 0 : MvPolynomial (Fin (w + 1)) F) = c := by
  simp

/-- **The mirror identity, soundness.** Over a field of characteristic two, a table whose mirror
certificate is the zero polynomial is one-hot, whatever values it holds. -/
theorem oneHot_of_mirrorPoly_eq_zero [CharP F 2] :
    ∀ (w : ℕ) (e : ℕ → F), mirrorPoly w e = 0 → ∃ σ < 2 ^ w, OneHot w e σ
  | 0, e, h => by
    have h0 := congrArg (eval (0 : Fin 0 → F)) h
    rw [eval_mirrorPoly, map_zero] at h0
    simp [mirrorCert, chunkEval, mirrorPt, mirror] at h0
    have hsq : (e 0 + 1) ^ 2 = 0 := by
      linear_combination h0 + e 0 * (CharTwo.two_eq_zero (R := F))
    have h1' : e 0 + 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp hsq
    have h1 : e 0 = 1 := by linear_combination h1' - CharTwo.two_eq_zero (R := F)
    refine ⟨0, by simp, fun v hv => ?_⟩
    simp only [pow_zero, Nat.lt_one_iff] at hv
    subst hv
    simp [h1]
  | w + 1, e, h => by
    rw [mirrorPoly_succ] at h
    set p0 := chunkEval (coords w) fun v => C (e (2 * v)) with hp0d
    set p1 := chunkEval (coords w) fun v => C (e (2 * v + 1)) with hp1d
    set m0 := chunkEval (mirrorPt (coords w)) fun v => C (e (2 * v)) with hm0d
    set m1 := chunkEval (mirrorPt (coords w)) fun v => C (e (2 * v + 1)) with hm1d
    set π' := mirror (coords (F := F) w) with hπd
    have h2S : (2 : MvPolynomial (Fin w) F) = 0 := two_eq_zero_mv
    have h2T : (2 : MvPolynomial (Fin (w + 1)) F) = 0 := two_eq_zero_mv
    -- `r_0 = 0` and `r_0 = 1`
    have hz := congrArg (aeval (Fin.cons 0 X : Fin (w + 1) → MvPolynomial (Fin w) F)) h
    have ho := congrArg (aeval (Fin.cons 1 X : Fin (w + 1) → MvPolynomial (Fin w) F)) h
    simp only [map_add, map_mul, map_sub, map_one, map_zero, aeval_cons_rename,
      aeval_cons_X_zero] at hz ho
    have h01 : p0 * m1 = 0 := by linear_combination hz
    have h10 : p1 * m0 = 0 := by linear_combination -ho + (p1 * m1 + π') * h2S
    -- the `r_0·(1 + r_0)` part
    have hρ01 : rename Fin.succ p0 * rename Fin.succ m1 = (0 : MvPolynomial (Fin (w + 1)) F) := by
      rw [← map_mul, h01, map_zero]
    have hρ10 : rename Fin.succ p1 * rename Fin.succ m0 = (0 : MvPolynomial (Fin (w + 1)) F) := by
      rw [← map_mul, h10, map_zero]
    have hmain : X 0 * (1 + X 0) * rename Fin.succ (p0 * m0 + p1 * m1 + π') = 0 := by
      rw [map_add, map_add, map_mul, map_mul]
      linear_combination h + (X 0 * rename Fin.succ p0 * rename Fin.succ m0) * h2T -
        (1 - X 0 ^ 2) * hρ01 + X 0 ^ 2 * hρ10
    have hne : (X 0 * (1 + X 0) : MvPolynomial (Fin (w + 1)) F) ≠ 0 := by
      refine mul_ne_zero (X_ne_zero _) fun h1 => ?_
      have := congrArg (aeval (Fin.cons 0 X : Fin (w + 1) → MvPolynomial (Fin w) F)) h1
      simp at this
    have hsum : p0 * m0 + p1 * m1 + π' = 0 :=
      rename_injective _ (Fin.succ_injective _)
        (((mul_eq_zero.mp hmain).resolve_left hne).trans (map_zero _).symm)
    have hlt : ∀ v < 2 ^ (w + 1), v / 2 < 2 ^ w := fun v hv => by rw [pow_succ] at hv; omega
    rcases mul_eq_zero.mp h01 with hp0 | hm1
    · -- the even half vanishes: the odd half is one-hot
      have hm0 : m0 = 0 := by
        rw [hm0d, ← aeval_mirror_chunkEval, ← hp0d, hp0, map_zero]
      have he1 : mirrorPoly w (fun v => e (2 * v + 1)) = 0 := by
        have : p1 * m1 + π' = 0 := by linear_combination hsum - m0 * hp0
        exact this
      have he0 := eq_zero_of_chunkEval_coords (e := fun v => e (2 * v)) hp0
      obtain ⟨σ, hσ, hoh⟩ := oneHot_of_mirrorPoly_eq_zero w _ he1
      refine ⟨2 * σ + 1, by rw [pow_succ]; omega, fun v hv => ?_⟩
      have hv2 := hlt v hv
      rcases Nat.mod_two_eq_zero_or_one v with hv1 | hv1
      · have hv' : v = 2 * (v / 2) := by omega
        have he : e (2 * (v / 2)) = 0 := he0 _ hv2
        rw [hv', he, ite_eq_right (by omega)]
      · have hv' : v = 2 * (v / 2) + 1 := by omega
        have he : e (2 * (v / 2) + 1) = if v / 2 = σ then 1 else 0 := hoh _ hv2
        rw [hv', he]
        by_cases hq : v / 2 = σ
        · rw [ite_eq_left hq, ite_eq_left (by omega)]
        · rw [ite_eq_right hq, ite_eq_right (by omega)]
    · -- the odd half vanishes: the even half is one-hot
      have hp1 : p1 = 0 := by
        rw [hp1d, ← aeval_mirror_chunkEval_mirrorPt, ← hm1d, hm1, map_zero]
      have he0 : mirrorPoly w (fun v => e (2 * v)) = 0 := by
        have : p0 * m0 + π' = 0 := by linear_combination hsum - m1 * hp1
        exact this
      have he1 := eq_zero_of_chunkEval_coords (e := fun v => e (2 * v + 1)) hp1
      obtain ⟨σ, hσ, hoh⟩ := oneHot_of_mirrorPoly_eq_zero w _ he0
      refine ⟨2 * σ, by rw [pow_succ]; omega, fun v hv => ?_⟩
      have hv2 := hlt v hv
      rcases Nat.mod_two_eq_zero_or_one v with hv1 | hv1
      · have hv' : v = 2 * (v / 2) := by omega
        have he : e (2 * (v / 2)) = if v / 2 = σ then 1 else 0 := hoh _ hv2
        rw [hv', he]
        by_cases hq : v / 2 = σ
        · rw [ite_eq_left hq, ite_eq_left (by omega)]
        · rw [ite_eq_right hq, ite_eq_right (by omega)]
      · have hv' : v = 2 * (v / 2) + 1 := by omega
        have he : e (2 * (v / 2) + 1) = 0 := he1 _ hv2
        rw [hv', he, ite_eq_right (by omega)]

/-- **The mirror identity** (the paper's Lemma 3.1 in characteristic two). Over a field of
characteristic two, `ẽ(r)·ẽ(1 + r) + Π_h r_h·(1 + r_h)` is the zero polynomial in `r ∈ F^w`
exactly when `e` is one-hot at some `σ < 2^w`. `e` is any table of values in `F`: neither
booleanity nor the Hamming weight is assumed. -/
theorem mirrorPoly_eq_zero_iff [CharP F 2] (w : ℕ) (e : ℕ → F) :
    mirrorPoly w e = 0 ↔ ∃ σ < 2 ^ w, OneHot w e σ := by
  refine ⟨oneHot_of_mirrorPoly_eq_zero w e, fun ⟨σ, hσ, he⟩ => ?_⟩
  have hlen : (coords (F := F) w).length = w := List.length_ofFn
  refine mirrorCert_eq_zero_of_oneHot two_eq_zero_mv _ _ σ (fun v hv => ?_) (by rwa [hlen])
  rw [hlen] at hv
  rw [he v hv]
  split_ifs <;> simp

/-! ## Degrees and Schwartz-Zippel -/

section Degree

variable {σ : Type*}

theorem totalDegree_eqAt :
    ∀ (r : List (MvPolynomial σ F)) (j : ℕ), (∀ z ∈ r, z.totalDegree ≤ 1) →
      (eqAt r j).totalDegree ≤ r.length
  | [], _, _ => by simp
  | z :: r, j, h => by
    rw [eqAt_cons, List.length_cons]
    have hz : z.totalDegree ≤ 1 := h z (by simp)
    have hr := totalDegree_eqAt r (j / 2) fun y hy => h y (by simp [hy])
    have h1 : (if j % 2 = 1 then z else 1 - z).totalDegree ≤ 1 := by
      split_ifs
      · exact hz
      · exact (totalDegree_sub _ _).trans (max_le (by simp) hz)
    have := (totalDegree_mul _ _).trans (add_le_add h1 hr)
    omega

theorem totalDegree_chunkEval (r : List (MvPolynomial σ F)) (e : ℕ → F)
    (h : ∀ z ∈ r, z.totalDegree ≤ 1) : (chunkEval r fun v => C (e v)).totalDegree ≤ r.length := by
  rw [chunkEval]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  simpa [totalDegree_C] using totalDegree_eqAt r j h

theorem totalDegree_mirror :
    ∀ (r : List (MvPolynomial σ F)), (∀ z ∈ r, z.totalDegree ≤ 1) →
      (mirror r).totalDegree ≤ 2 * r.length
  | [], _ => by simp
  | z :: r, h => by
    rw [mirror_cons, List.length_cons]
    have hz : z.totalDegree ≤ 1 := h z (by simp)
    have hr := totalDegree_mirror r fun y hy => h y (by simp [hy])
    have h1 : (1 + z).totalDegree ≤ 1 := (totalDegree_add _ _).trans (max_le (by simp) hz)
    have := (totalDegree_mul _ _).trans
      (add_le_add ((totalDegree_mul z (1 + z)).trans (add_le_add hz h1)) hr)
    omega

theorem totalDegree_mirrorPt_le (r : List (MvPolynomial σ F)) (h : ∀ z ∈ r, z.totalDegree ≤ 1) :
    ∀ z ∈ mirrorPt r, z.totalDegree ≤ 1 := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
  exact (totalDegree_add _ _).trans (max_le (by simp) (h y hy))

/-- The certificate has total degree at most `2w` in a point of degree-one coordinates. -/
theorem totalDegree_mirrorCert (r : List (MvPolynomial σ F)) (e : ℕ → F)
    (h : ∀ z ∈ r, z.totalDegree ≤ 1) :
    (mirrorCert r fun v => C (e v)).totalDegree ≤ 2 * r.length := by
  rw [mirrorCert]
  refine (totalDegree_add _ _).trans (max_le ?_ (totalDegree_mirror r h))
  have h1 := totalDegree_chunkEval r e h
  have h2 := totalDegree_chunkEval (mirrorPt r) e (totalDegree_mirrorPt_le r h)
  rw [length_mirrorPt] at h2
  have := (totalDegree_mul _ _).trans (add_le_add h1 h2)
  omega

theorem totalDegree_ofFn_X_le {n : ℕ} (f : Fin n → σ) :
    ∀ z ∈ List.ofFn (fun k => (X (f k) : MvPolynomial σ F)), z.totalDegree ≤ 1 := by
  intro z hz
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hz
  exact (totalDegree_X _).le

end Degree

theorem totalDegree_mirrorPoly (w : ℕ) (e : ℕ → F) : (mirrorPoly w e).totalDegree ≤ 2 * w := by
  have h := totalDegree_mirrorCert (coords (F := F) w) e (totalDegree_ofFn_X_le id)
  rwa [coords, List.length_ofFn] at h

/-- **Schwartz-Zippel for the mirror test.** Over a finite field of characteristic two, a table
that is not one-hot passes the mirror test at no more than `2w·|F|^(w − 1)` of the `|F|^w` points
`r` (VCVio's `MvPolynomial.card_zeros_le_of_totalDegree_le`). -/
theorem card_mirrorCert_eq_zero_le [CharP F 2] [Fintype F] [DecidableEq F] {w : ℕ} {e : ℕ → F}
    (hbad : ¬ ∃ σ < 2 ^ w, OneHot w e σ) :
    (univ.filter fun r : Fin w → F => mirrorCert (List.ofFn r) e = 0).card ≤
      2 * w * Fintype.card F ^ (w - 1) := by
  have h := card_zeros_le_of_totalDegree_le _ (mt (mirrorPoly_eq_zero_iff w e).mp hbad)
    (totalDegree_mirrorPoly w e)
  simp only [Fintype.card_fin] at h
  refine le_of_eq_of_le (congrArg Finset.card (Finset.filter_congr fun r _ => ?_)) h
  rw [eval_mirrorPoly]

end Field

/-! ## The batched check -/

section Batched

variable {R : Type*} [CommRing R] {m Q d : ℕ}

/-- The left side of the batched one-hot check, the paper's identity (6) in characteristic two:
`θ·Σ_{u < 2^m, b(u)} eq(τ, u)·Σ_q ε_q·Σ_i ν_i·(ẽ_{q,i,u}(ρ_i)·ẽ_{q,i,u}(1 + ρ_i) + π_{w_i}(ρ_i))`.
Row `u`'s chunk `i` of pointer column `q` is the table `e q i u`; `b` is the public gate of the
rows whose pointers are used. Column `q`'s chunk `i` takes the coefficient `ε_q·ν_i`, as the
verifier's `certs` (`verify_link`, read by `Functionals::summand`). -/
def batchedCert (b : ℕ → Bool) (e : Fin Q → Fin d → ℕ → ℕ → R) (θ : R) (τ : List R)
    (ε : Fin Q → R) (ν : Fin d → R) (ρ : Fin d → List R) : R :=
  θ * ∑ u ∈ (range (2 ^ τ.length)).filter (fun u => b u = true),
    eqAt τ u * ∑ q, ε q * ∑ i, ν i * mirrorCert (ρ i) (e q i u)

theorem map_batchedCert {S G : Type*} [CommRing S] [FunLike G R S] [RingHomClass G R S] (f : G)
    (b : ℕ → Bool) (e : Fin Q → Fin d → ℕ → ℕ → R) (θ : R) (τ : List R) (ε : Fin Q → R)
    (ν : Fin d → R) (ρ : Fin d → List R) :
    f (batchedCert b e θ τ ε ν ρ) =
      batchedCert b (fun q i u v => f (e q i u v)) (f θ) (τ.map f) (fun q => f (ε q))
        (fun i => f (ν i)) (fun i => (ρ i).map f) := by
  simp only [batchedCert, map_mul, map_sum, map_eqAt, map_mirrorCert, List.length_map]

/-- With `θ = 1`, `τ` the Boolean point of a gated row `u_0` and `ε`, `ν` unit vectors at `q_0`,
`i_0`, the batched check is the certificate of that one chunk. -/
theorem batchedCert_pick (b : ℕ → Bool) (e : Fin Q → Fin d → ℕ → ℕ → R) (ρ : Fin d → List R)
    {u0 : ℕ} (hu0 : u0 < 2 ^ m) (hb : b u0 = true) (q0 : Fin Q) (i0 : Fin d) :
    batchedCert b e 1 (List.ofFn (boolPt m u0)) (fun q => if q = q0 then 1 else 0)
        (fun i => if i = i0 then 1 else 0) ρ = mirrorCert (ρ i0) (e q0 i0 u0) := by
  simp only [batchedCert, one_mul, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    List.length_ofFn]
  rw [Finset.sum_eq_single u0]
  · rw [eqAt_ofFn_boolPt m hu0 hu0, ite_eq_left rfl, one_mul]
  · intro u hu hne
    rw [eqAt_ofFn_boolPt m (mem_range.mp (mem_filter.mp hu).1) hu0, ite_eq_right hne, zero_mul]
  · intro h
    exact absurd (mem_filter.mpr ⟨mem_range.mpr hu0, hb⟩) h

end Batched

section BatchedField

variable {F : Type*} [Field F] {m Q d : ℕ}

/-- The batched check's variables: `θ`, the row point `τ ∈ F^m`, the column coefficients `ε`, the
chunk coefficients `ν`, and each chunk's part `ρ_i ∈ F^{w_i}` of the index point. -/
abbrev BatchVar (m Q d : ℕ) (w : Fin d → ℕ) : Type :=
  Unit ⊕ Fin m ⊕ Fin Q ⊕ Fin d ⊕ (Σ i, Fin (w i))

/-- The batched check as a polynomial in `(θ, τ, ε, ν, ρ)`. -/
noncomputable def batchedPoly (m : ℕ) (w : Fin d → ℕ) (b : ℕ → Bool)
    (e : Fin Q → Fin d → ℕ → ℕ → F) : MvPolynomial (BatchVar m Q d w) F :=
  batchedCert b (fun q i u v => C (e q i u v)) (X (Sum.inl ()))
    (List.ofFn fun k => X (Sum.inr (Sum.inl k))) (fun q => X (Sum.inr (Sum.inr (Sum.inl q))))
    (fun i => X (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))
    (fun i => List.ofFn fun h => X (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨i, h⟩)))))

theorem aeval_batchedPoly {A : Type*} [CommRing A] [Algebra F A] (w : Fin d → ℕ) (b : ℕ → Bool)
    (e : Fin Q → Fin d → ℕ → ℕ → F) (x : BatchVar m Q d w → A) :
    aeval x (batchedPoly m w b e) =
      batchedCert b (fun q i u v => algebraMap F A (e q i u v)) (x (Sum.inl ()))
        (List.ofFn fun k => x (Sum.inr (Sum.inl k))) (fun q => x (Sum.inr (Sum.inr (Sum.inl q))))
        (fun i => x (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))
        (fun i => List.ofFn fun h => x (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨i, h⟩))))) := by
  rw [batchedPoly, map_batchedCert]
  simp [List.map_ofFn, Function.comp_def]

theorem eval_batchedPoly (w : Fin d → ℕ) (b : ℕ → Bool) (e : Fin Q → Fin d → ℕ → ℕ → F)
    (x : BatchVar m Q d w → F) :
    eval x (batchedPoly m w b e) =
      batchedCert b e (x (Sum.inl ())) (List.ofFn fun k => x (Sum.inr (Sum.inl k)))
        (fun q => x (Sum.inr (Sum.inr (Sum.inl q)))) (fun i => x (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))
        (fun i => List.ofFn fun h => x (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨i, h⟩))))) := by
  rw [batchedPoly, map_batchedCert]
  simp [List.map_ofFn, Function.comp_def]

theorem totalDegree_mul_le_of {σ : Type*} {a b : MvPolynomial σ F} {A B : ℕ}
    (ha : a.totalDegree ≤ A) (hb : b.totalDegree ≤ B) : (a * b).totalDegree ≤ A + B :=
  (totalDegree_mul a b).trans (add_le_add ha hb)

theorem totalDegree_sum_le_of {σ ι : Type*} {s : Finset ι} {f : ι → MvPolynomial σ F} {D : ℕ}
    (h : ∀ j ∈ s, (f j).totalDegree ≤ D) : (∑ j ∈ s, f j).totalDegree ≤ D :=
  (totalDegree_finsetSum _ _).trans (Finset.sup_le h)

/-- The batched check has total degree at most `m + 3 + 2·w_max`: `1` in `θ`, `m` in `τ`, `2` in
`(ε, ν)` and `2·w_i` in `ρ_i`. -/
theorem totalDegree_batchedPoly (w : Fin d → ℕ) (b : ℕ → Bool) (e : Fin Q → Fin d → ℕ → ℕ → F)
    {wmax : ℕ} (hw : ∀ i, w i ≤ wmax) :
    (batchedPoly m w b e).totalDegree ≤ m + 3 + 2 * wmax := by
  have hX : ∀ s : BatchVar m Q d w, (X s : MvPolynomial _ F).totalDegree ≤ 1 :=
    fun s => (totalDegree_X s).le
  have hrow : ∀ u, (eqAt (List.ofFn fun k => (X (Sum.inr (Sum.inl k)) :
      MvPolynomial (BatchVar m Q d w) F)) u).totalDegree ≤ m := fun u =>
    (totalDegree_eqAt _ u (totalDegree_ofFn_X_le _)).trans (by simp)
  have hcert : ∀ q i u, (mirrorCert (List.ofFn fun h => (X (Sum.inr (Sum.inr (Sum.inr
      (Sum.inr ⟨i, h⟩)))) : MvPolynomial (BatchVar m Q d w) F)) (fun v => C (e q i u v))).totalDegree
        ≤ 2 * wmax := fun q i u =>
    (totalDegree_mirrorCert _ _ (totalDegree_ofFn_X_le _)).trans (by simpa using hw i)
  unfold batchedPoly batchedCert
  calc _ ≤ 1 + (m + (1 + (1 + 2 * wmax))) :=
        totalDegree_mul_le_of (hX _) (totalDegree_sum_le_of fun u _ =>
          totalDegree_mul_le_of (hrow u) (totalDegree_sum_le_of fun q _ =>
            totalDegree_mul_le_of (hX _) (totalDegree_sum_le_of fun i _ =>
              totalDegree_mul_le_of (hX _) (hcert q i u))))
    _ = m + 3 + 2 * wmax := by ring

/-- **The batched check is nonzero** (the paper's Lemma 3.2 in characteristic two). If some chunk of
some pointer column in a gated row is not one-hot, the batched check is a nonzero polynomial:
setting `θ = 1`, `τ` to that row's Boolean point and `ε`, `ν` to unit vectors leaves that chunk's
certificate, nonzero by the mirror identity. -/
theorem batchedPoly_ne_zero [CharP F 2] (w : Fin d → ℕ) (b : ℕ → Bool)
    (e : Fin Q → Fin d → ℕ → ℕ → F)
    (hbad : ∃ u < 2 ^ m, b u = true ∧ ∃ q i, ¬ ∃ σ < 2 ^ w i, OneHot (w i) (e q i u) σ) :
    batchedPoly m w b e ≠ 0 := by
  obtain ⟨u0, hu0, hb, q0, i0, hne⟩ := hbad
  intro hz
  let x : BatchVar m Q d w → MvPolynomial (Fin (w i0)) F :=
    Sum.elim (fun _ => 1) (Sum.elim (boolPt m u0) (Sum.elim (fun q => if q = q0 then 1 else 0)
      (Sum.elim (fun i => if i = i0 then 1 else 0)
        (fun p => if hp : p.1 = i0 then X (Fin.cast (congrArg w hp) p.2) else 0))))
  have h := congrArg (aeval x) hz
  rw [map_zero, aeval_batchedPoly] at h
  have hρ : (List.ofFn fun h => x (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨i0, h⟩))))) = coords (w i0) := by
    simp [x, coords]
  have hpick := batchedCert_pick (R := MvPolynomial (Fin (w i0)) F) b
    (fun q i u v => algebraMap F _ (e q i u v))
    (fun i => List.ofFn fun h => x (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨i, h⟩))))) hu0 hb q0 i0
  rw [hρ] at hpick
  simp only [algebraMap_eq] at h hpick
  have hpoly : mirrorPoly (w i0) (e q0 i0 u0) = 0 := by
    rw [← h, mirrorPoly, ← hpick]
    rfl
  exact hne ((mirrorPoly_eq_zero_iff _ _).mp hpoly)

theorem card_batchVar (w : Fin d → ℕ) :
    Fintype.card (BatchVar m Q d w) = 1 + m + Q + d + ∑ i, w i := by
  simp [Fintype.card_sum, Fintype.card_sigma]
  omega

/-- **Schwartz-Zippel for the batched check.** Over a finite field of characteristic two, if some
chunk of some pointer column in a gated row is not one-hot, the batched check vanishes at no more
than `(m + 3 + 2·w_max)·|F|^(N − 1)` of the `|F|^N` points `(θ, τ, ε, ν, ρ)`,
`N = 1 + m + Q + d + Σ_i w_i`: a fraction `(m + 3 + 2·w_max)/|F|`, the paper's term. -/
theorem card_batchedCert_eq_zero_le [CharP F 2] [Fintype F] [DecidableEq F] (w : Fin d → ℕ)
    (b : ℕ → Bool) (e : Fin Q → Fin d → ℕ → ℕ → F) {wmax : ℕ} (hw : ∀ i, w i ≤ wmax)
    (hbad : ∃ u < 2 ^ m, b u = true ∧ ∃ q i, ¬ ∃ σ < 2 ^ w i, OneHot (w i) (e q i u) σ) :
    (univ.filter fun x : BatchVar m Q d w → F =>
        batchedCert b e (x (Sum.inl ())) (List.ofFn fun k => x (Sum.inr (Sum.inl k)))
          (fun q => x (Sum.inr (Sum.inr (Sum.inl q)))) (fun i => x (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))
          (fun i => List.ofFn fun h => x (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨i, h⟩))))) = 0).card ≤
      (m + 3 + 2 * wmax) * Fintype.card F ^ (1 + m + Q + d + ∑ i, w i - 1) := by
  have h := card_zeros_le_of_totalDegree_le _ (batchedPoly_ne_zero w b e hbad)
    (totalDegree_batchedPoly w b e hw)
  rw [card_batchVar] at h
  refine le_of_eq_of_le (congrArg Finset.card (Finset.filter_congr fun x _ => ?_)) h
  rw [eval_batchedPoly]

end BatchedField

end

end LeanVM.Protocol.Hotwire

/-! The mirror test's theorems use Lean's three standard axioms only. -/

/-- info: 'LeanVM.Protocol.Hotwire.mirrorPoly_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.mirrorPoly_eq_zero_iff

/-- info: 'LeanVM.Protocol.Hotwire.card_mirrorCert_eq_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.card_mirrorCert_eq_zero_le

/-- info: 'LeanVM.Protocol.Hotwire.card_batchedCert_eq_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.card_batchedCert_eq_zero_le
