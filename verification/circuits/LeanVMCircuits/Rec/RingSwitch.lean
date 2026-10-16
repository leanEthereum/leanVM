module

public import LeanVMCircuits.Rec.Bind
public import LeanVMCircuits.Rec.Run
public import LeanVMCircuits.Rec.GkrInst
public import Mathlib.Algebra.CharP.Two
public import Mathlib.RingTheory.MvPolynomial.Basic

@[expose] public section

/-!
Ring switching (`pcs::ring_switch`, Annex A) for the one `HASH` slice claim of the recursion's flock.

A packed region `q : {0,1}^n → K` holds 64 bit slices, `q(u) = Σ_i bit_i(q(u)) x^i` (`pack`). Flock's lincheck leaves
64 claims `s_i ?= MLE(bit_i ∘ q)(r)` (`sliceMle`) at one point `r = R ++ x_outer`. The verifier draws `γ_rs` and six map
challenges `f_0..f_5`, and `Φ` (`Phi`) composes the six stages `a ← a + f_p a^(2^d_p)`, `d = 32, 16, 8, 4, 2, 1`. The
target is `T = Σ_i x^i Φ(s_i)`; the weighted opening `Σ_u Φ(eq(r, u)) q(u) = T` (`RingOpening`) is what WHIR proves.

* `weighted_sum_eq`: the honest weighted sum is `Σ_i x^i Φ(MLE(bit_i ∘ q)(r))`, so honest slices meet the opening.
* `phi_expand`: `Φ(a) = Σ_{k<64} c_k a^(2^k)`, `c_k` the evaluation of the monomial `coef 6 k` in the challenges.
* `exists_pair_ne_zero`: a nonzero error `δ` leaves some `Σ_i x^i δ_i^(2^k) ≠ 0`, as the 64 conjugates `x^(2^j)` are
  distinct (`root_frob_inj`).
* `ringBad_card`: a nonzero error survives `Σ_i x^i Φ(δ_i) = 0` for at most `phiDeg · |E|^5` challenge vectors,
  `phiDeg = 2^31 + 2^15 + 2^7 + 2^3 + 2 + 1` (`phiDeg_eq`), by Schwartz-Zippel; `ringBad_frac` is Annex A's
  `2^32 / 2^192`.
* `ring_switch_sound`: if some slice claim is false, the challenges at which the target equals the honest weighted sum
  are at most that many.
* `weight_mle`, `weight_mle_moved`: the opening's weight `W(u) = Φ(eq(r, u))` at a point `r'` of WHIR is
  `Σ_k c_k eq(r^(2^k), r')`, which `RingShare::weight_at` computes as
  `Σ_k (c̄_k Π_j (1 + r_j + r'_j^(2^-k)))^(2^k)` from any `c̄_k` with `c̄_k^(2^k) = c_k`.

`Bind.RingCert` names the calls `RingFamily::draw`, `RingFamily::share` and `RingShare::target` make: the seven draws,
`powers(γ_rs, 1)`, `RingMap::new`'s inverse Frobenius ladders (`frobenius2`, then squarings) and prefix products, the
family's slices `mul_add(1, s_i, 0)`, each term's Horner sum `mul_const_add(acc, x^(2^-k), s_i)` and coefficient
product, and the linearized Horner `mul_add(acc, acc, term)` that closes the target. `RingCert.coef_sem`: the
coefficient wires are the `c̄_k`, which `weight_at` reuses (`RingCert.weight_sem`). `RingCert.target_sem`: the target
wire is `Σ_i x^i Φ(s_i)` at the drawn challenges. `RingCert.sound`: if the weighted opening holds at the target wire,
every slice wire is its true bit-slice MLE, or the drawn challenges lie in `ringBad` of the slices' errors.
`RingCert.find` reads the certificates off a replay.
-/

namespace LeanVMCircuits.Rec.RingSwitch

open LeanVMCircuits.Rec MvPolynomial Finset Sumcheck

/-! Characteristic two and the Frobenius of `K` and `E`. -/

instance charP_K : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero two_K

instance charP_E : CharP E 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero two_E

/-- `x` as an element of `E`. -/
noncomputable def xE : E := emb root

theorem emb_pow (a : K) (n : ℕ) : emb (a ^ n) = emb a ^ n := map_pow _ a n

theorem emb_one : emb 1 = 1 := map_one _

theorem emb_inj : Function.Injective emb := (AdjoinRoot.of extModulus).injective

theorem frob_inj {F : Type} [Field F] [CharP F 2] (n : ℕ) {a b : F} (h : a ^ 2 ^ n = b ^ 2 ^ n) : a = b := by
  have h0 : (a - b) ^ 2 ^ n = 0 := by rw [sub_pow_char_pow, h, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp h0)

/-- `K` has `2^64` elements. -/
theorem frobK (t : ℕ) (a : K) : a ^ 2 ^ (64 * t) = a := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h := FiniteField.pow_card a
    rw [card_K] at h
    rw [show 64 * (t + 1) = 64 * t + 64 by ring, pow_add, pow_mul, ih, h]

theorem y_pow_eight : y ^ 8 = y := by
  linear_combination (y ^ 5 - y ^ 3 - y ^ 2 + y + 2) * y_cubed - (2 * y + 1) * two_E

/-- `y` lies in the field of eight elements. -/
theorem y_frob (m : ℕ) : ∀ t : ℕ, y ^ 2 ^ (m + 3 * t) = y ^ 2 ^ m
  | 0 => by simp
  | t + 1 => by
    rw [show 2 ^ (m + 3 * (t + 1)) = 8 * 2 ^ (m + 3 * t) by
      rw [show m + 3 * (t + 1) = m + 3 * t + 3 by ring, pow_add]; ring, pow_mul, y_pow_eight, y_frob m t]

theorem toE_frob (c0 c1 c2 : K) (n : ℕ) : toE c0 c1 c2 ^ 2 ^ n =
    emb (c0 ^ 2 ^ n) + emb (c1 ^ 2 ^ n) * y ^ 2 ^ n + emb (c2 ^ 2 ^ n) * (y ^ 2 ^ n) ^ 2 := by
  simp only [toE, add_pow_char_pow, mul_pow, emb_pow]
  ring

/-- `E` has `2^192` elements. -/
theorem frobE (a : E) : a ^ 2 ^ 192 = a := by
  obtain ⟨c0, c1, c2, rfl⟩ := toE_surjective a
  rw [toE_frob, show (192 : ℕ) = 64 * 3 by rfl, frobK, frobK, frobK, show 64 * 3 = 0 + 3 * 64 by rfl, y_frob 0 64]
  simp [toE]

/-- `frobenius2`: `a^(2^128)` from the coordinates, `v + c2 (y + y^2) + c1 y^2`. -/
theorem frob2 (c0 c1 c2 : K) : toE c0 c1 c2 ^ 2 ^ 128 = toE c0 c1 c2 + toE 0 1 1 * emb c2 + toE 0 0 1 * emb c1 := by
  rw [toE_frob, show (128 : ℕ) = 64 * 2 by rfl, frobK, frobK, frobK, show 64 * 2 = 2 + 3 * 42 by rfl, y_frob 2 42]
  simp only [toE, emb_zero, emb_one]
  linear_combination (emb c1 * y) * y_cubed + emb c2 * y_pow_eight -
    (emb c1 * (y ^ 2 + y) + emb c2 * y ^ 2) * two_E

/-! The map. -/

/-- Stage `p`'s shift exponent `d_p = 2^(5-p)`: `32, 16, 8, 4, 2, 1`. -/
def dsh (p : ℕ) : ℕ := 2 ^ (5 - p)

/-- Challenge `p`'s variable. -/
def vr (p : ℕ) : Fin 6 := ⟨p % 6, Nat.mod_lt _ (by norm_num)⟩

theorem vr_val {p : ℕ} (hp : p < 6) : ((vr p : Fin 6) : ℕ) = p := Nat.mod_eq_of_lt hp

/-- The first `p` stages, `a ← a + f_p a^(2^d_p)`. -/
noncomputable def phiN (f : Fin 6 → E) : ℕ → E → E
  | 0, a => a
  | p + 1, a => phiN f p a + f (vr p) * phiN f p a ^ 2 ^ dsh p

/-- `Φ`, the six stages (`RingFamily::apply`). -/
noncomputable def Phi (f : Fin 6 → E) (a : E) : E := phiN f 6 a

theorem phiN_add (f : Fin 6 → E) : ∀ (p : ℕ) (a b : E), phiN f p (a + b) = phiN f p a + phiN f p b
  | 0, _, _ => rfl
  | p + 1, a, b => by simp only [phiN, phiN_add f p, add_pow_char_pow]; ring

theorem phiN_zero (f : Fin 6 → E) : ∀ p : ℕ, phiN f p 0 = 0
  | 0 => rfl
  | p + 1 => by rw [phiN, phiN_zero f p, zero_pow (by positivity), mul_zero, add_zero]

/-- `Φ` is additive. -/
noncomputable def phiHom (f : Fin 6 → E) : E →+ E where
  toFun := Phi f
  map_zero' := phiN_zero f 6
  map_add' := phiN_add f 6

theorem phiHom_apply (f : Fin 6 → E) (a : E) : phiHom f a = Phi f a := rfl

/-- `c_k` after `p` stages, as a polynomial in the challenges: stage `p` adds `X_p c_{k - d_p}^(2^d_p)` at `k`. -/
noncomputable def coef : ℕ → ℕ → MvPolynomial (Fin 6) E
  | 0, k => if k = 0 then 1 else 0
  | p + 1, k => coef p k + X (vr p) * (if dsh p ≤ k then coef p (k - dsh p) ^ 2 ^ dsh p else 0)

theorem two_pow_six_sub {p : ℕ} (hp : p < 6) : 2 ^ (6 - p) = 2 * dsh p := by
  rw [dsh, show 6 - p = (5 - p) + 1 by omega, pow_succ]; ring

theorem six_sub_succ {p : ℕ} (hp : p < 6) : 2 ^ (6 - (p + 1)) = dsh p := by
  rw [dsh, show 6 - (p + 1) = 5 - p by omega]

theorem dsh_pos (p : ℕ) : 0 < dsh p := by unfold dsh; positivity

theorem dsh_le (p : ℕ) : dsh p ≤ 32 := by
  unfold dsh
  calc 2 ^ (5 - p) ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 32 := by norm_num

/-- After `p` stages the exponents are multiples of `2^(6-p)` below `64`. -/
theorem coef_support : ∀ p ≤ 6, ∀ k, coef p k ≠ 0 → 2 ^ (6 - p) ∣ k ∧ k + 2 ^ (6 - p) ≤ 64
  | 0, _, k, h => by
    simp only [coef] at h
    split_ifs at h with hk
    · subst hk; norm_num
    · exact absurd rfl h
  | p + 1, hp, k, h => by
    have ih := coef_support p (by omega)
    have h2 := two_pow_six_sub (show p < 6 by omega)
    rw [six_sub_succ (show p < 6 by omega)]
    simp only [coef] at h
    by_cases hA : coef p k = 0
    · rw [hA, zero_add] at h
      split_ifs at h with hd
      · have hB : coef p (k - dsh p) ≠ 0 := fun h0 => h (by rw [h0, zero_pow (by positivity), mul_zero])
        obtain ⟨hdv, hle⟩ := ih (k - dsh p) hB
        rw [h2] at hdv hle
        refine ⟨?_, by omega⟩
        have h3 : dsh p ∣ k - dsh p := (dvd_mul_left (dsh p) 2).trans hdv
        have h4 := Nat.dvd_add h3 (dvd_refl (dsh p))
        rwa [Nat.sub_add_cancel hd] at h4
      · exact absurd (by rw [mul_zero]) h
    · obtain ⟨hdv, hle⟩ := ih k hA
      rw [h2] at hdv hle
      exact ⟨(dvd_mul_left (dsh p) 2).trans hdv, by omega⟩

theorem coef_zero_of_ge {p : ℕ} (hp : p < 6) {j : ℕ} (hj : 64 - dsh p ≤ j) : coef p j = 0 := by
  by_contra h
  have := (coef_support p hp.le j h).2
  rw [two_pow_six_sub hp] at this
  have := dsh_pos p
  omega

theorem eval_coef_succ (f : Fin 6 → E) (p k : ℕ) : eval f (coef (p + 1) k) =
    eval f (coef p k) + f (vr p) * (if dsh p ≤ k then eval f (coef p (k - dsh p)) ^ 2 ^ dsh p else 0) := by
  simp only [coef, map_add, map_mul, eval_X]
  split_ifs <;> simp

/-- The Frobenius form of the first `p` stages. -/
theorem phiN_expand (f : Fin 6 → E) : ∀ p ≤ 6, ∀ a : E,
    phiN f p a = ∑ k ∈ range 64, eval f (coef p k) * a ^ 2 ^ k
  | 0, _, a => by
    rw [sum_eq_single 0 (fun k _ hk => by simp [coef, hk]) (by simp)]
    simp [coef, phiN]
  | p + 1, hp, a => by
    have hp6 : p < 6 := by omega
    rw [phiN, phiN_expand f p (by omega)]
    simp only [eval_coef_succ, add_mul, sum_add_distrib]
    congr 1
    set D := dsh p with hD
    have hD64 : D ≤ 64 := by have := dsh_le p; omega
    rw [sum_pow_char_pow, mul_sum]
    have hL : ∑ k ∈ range 64, f (vr p) * (eval f (coef p k) * a ^ 2 ^ k) ^ 2 ^ D =
        ∑ j ∈ range (64 - D), f (vr p) * eval f (coef p j) ^ 2 ^ D * a ^ 2 ^ (D + j) := by
      rw [← sum_range_add_sum_Ico _ (show 64 - D ≤ 64 by omega)]
      rw [sum_eq_zero (s := Ico (64 - D) 64) (fun j hj => by
        rw [coef_zero_of_ge hp6 (mem_Ico.mp hj).1]; simp), add_zero]
      refine sum_congr rfl fun j _ => ?_
      rw [mul_pow, ← pow_mul, ← pow_add, add_comm j D]; ring
    have hR : ∑ k ∈ range 64, f (vr p) * (if D ≤ k then eval f (coef p (k - D)) ^ 2 ^ D else 0) * a ^ 2 ^ k =
        ∑ j ∈ range (64 - D), f (vr p) * eval f (coef p j) ^ 2 ^ D * a ^ 2 ^ (D + j) := by
      rw [← sum_range_add_sum_Ico _ hD64, sum_eq_zero (s := range D) (fun k hk => by
        rw [if_neg (by have := mem_range.mp hk; omega)]; simp), zero_add, sum_Ico_eq_sum_range]
      refine sum_congr rfl fun j _ => ?_
      rw [if_pos (by omega), show D + j - D = j by omega]
    rw [hL, hR]

/-- `Φ(a) = Σ_{k<64} c_k a^(2^k)`. -/
theorem phi_expand (f : Fin 6 → E) (a : E) : Phi f a = ∑ k ∈ range 64, eval f (coef 6 k) * a ^ 2 ^ k :=
  phiN_expand f 6 le_rfl a

/-! The `c_k` are 64 distinct monomials. -/

open Classical in
theorem coef_vars : ∀ p ≤ 6, ∀ k, ∀ i ∈ (coef p k).vars, (i : ℕ) < p
  | 0, _, k, i, hi => by
    simp only [coef] at hi
    split_ifs at hi <;> simp at hi
  | p + 1, hp, k, i, hi => by
    have hv := vr_val (show p < 6 by omega)
    simp only [coef] at hi
    rcases mem_union.mp (vars_add_subset _ _ hi) with h | h
    · exact (coef_vars p (by omega) k i h).trans (by omega)
    · rcases mem_union.mp (vars_mul _ _ h) with h | h
      · rw [vars_X, mem_singleton] at h
        rw [h, hv]; omega
      · split_ifs at h
        · exact (coef_vars p (by omega) _ i (vars_pow _ _ h)).trans (by omega)
        · simp at h

/-- `A + X_i B` with `A` not reading `X_i` vanishes only if `A` and `B` do: `X_i B` has no monomial free of `X_i`. -/
theorem sep_zero (i : Fin 6) {A B : MvPolynomial (Fin 6) E} (hA : i ∉ A.vars) (h : A + X i * B = 0) :
    A = 0 ∧ B = 0 := by
  classical
  have hA0 : A = 0 := by
    rw [MvPolynomial.eq_zero_iff]
    intro m
    have hm := congrArg (MvPolynomial.coeff m) h
    rw [MvPolynomial.coeff_add, coeff_X_mul', MvPolynomial.coeff_zero] at hm
    by_cases hs : i ∈ m.support
    · by_contra hne
      exact hA ((mem_vars_iff_mem_support i).mpr ⟨m, MvPolynomial.mem_support_iff.mpr hne, hs⟩)
    · rwa [if_neg hs, add_zero] at hm
  refine ⟨hA0, ?_⟩
  rw [hA0, zero_add] at h
  exact (mul_eq_zero.mp h).resolve_left (X_ne_zero i)

open Classical in
theorem not_mem_vars_sum {s : Finset ℕ} {g : ℕ → MvPolynomial (Fin 6) E} {i : Fin 6}
    (h : ∀ j ∈ s, i ∉ (g j).vars) : i ∉ (∑ j ∈ s, g j).vars := fun hi => by
  obtain ⟨j, hj, hij⟩ := mem_biUnion.mp (vars_sum_subset s g hi)
  exact h j hj hij

open Classical in
theorem not_mem_vars_C_mul {a : E} {Q : MvPolynomial (Fin 6) E} {i : Fin 6} (h : i ∉ Q.vars) :
    i ∉ (C a * Q).vars := fun hi => by
  rcases mem_union.mp (vars_mul _ _ hi) with h' | h'
  · simp [vars_C] at h'
  · exact h h'

open Classical in
theorem vr_not_mem {p : ℕ} (hp : p < 6) (k : ℕ) : vr p ∉ (coef p k).vars := fun h => by
  have := coef_vars p hp.le k _ h
  rw [vr_val hp] at this
  omega

/-- A combination of distinct `c_k` with a nonzero weight on a nonzero `c_k` is a nonzero polynomial. -/
theorem sum_coef_ne_zero : ∀ p ≤ 6, ∀ (s : Finset ℕ) (β : ℕ → E) (κ : ℕ → ℕ), Set.InjOn κ s →
    (∃ i ∈ s, β i ≠ 0 ∧ coef p (κ i) ≠ 0) → ∑ i ∈ s, C (β i) * coef p (κ i) ≠ 0
  | 0, _, s, β, κ, hinj, ⟨i0, hi0, hb, hc⟩ => by
    have hk0 : κ i0 = 0 := by by_contra h; simp [coef, h] at hc
    rw [sum_eq_single i0 (fun j hj hne => by
      have : κ j ≠ 0 := fun h => hne (hinj hj hi0 (h.trans hk0.symm))
      simp [coef, this]) (fun h => absurd hi0 h)]
    simp [coef, hk0, hb]
  | p + 1, hp, s, β, κ, hinj, ⟨i0, hi0, hb, hc⟩ => by
    have hp6 : p < 6 := by omega
    set D := dsh p with hD
    have hD32 : D ≤ 32 := by rw [hD]; exact dsh_le p
    have hγD : ∀ i, (β i ^ 2 ^ (192 - D)) ^ 2 ^ D = β i := fun i => by
      rw [← pow_mul, ← pow_add, show 192 - D + D = 192 by omega, frobE]
    let γ : ℕ → E := fun i => β i ^ 2 ^ (192 - D)
    have hγ : ∀ i, γ i ^ 2 ^ D = β i := hγD
    set A := ∑ i ∈ s, C (β i) * coef p (κ i) with hA
    set inner := ∑ i ∈ s.filter (fun i => D ≤ κ i), C (γ i) * coef p (κ i - D) with hinner
    have hsplit : ∑ i ∈ s, C (β i) * coef (p + 1) (κ i) = A + X (vr p) * inner ^ 2 ^ D := by
      rw [hinner, sum_pow_char_pow, sum_filter, mul_sum, hA, ← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      simp only [coef, ← hD]
      split_ifs
      · rw [mul_pow, ← map_pow, hγ]; ring
      · simp
    rw [hsplit]
    have hvA : vr p ∉ A.vars := not_mem_vars_sum fun j _ => not_mem_vars_C_mul (vr_not_mem hp6 _)
    intro hz
    obtain ⟨hA0, hB0⟩ := sep_zero (vr p) hvA hz
    by_cases hc0 : coef p (κ i0) = 0
    · simp only [coef, hc0, zero_add, ← hD] at hc
      have hle : D ≤ κ i0 := by by_contra h; simp [h] at hc
      have hQ : coef p (κ i0 - D) ≠ 0 := fun h => hc (by simp [hle, h, zero_pow (pow_ne_zero _ two_ne_zero)])
      have hin : inner ≠ 0 := sum_coef_ne_zero p (by omega) _ γ (fun i => κ i - D)
        (fun a ha b hb' hab => hinj (mem_filter.mp ha).1 (mem_filter.mp hb').1 (by
          have := (mem_filter.mp ha).2; have := (mem_filter.mp hb').2; simp only at hab; omega))
        ⟨i0, mem_filter.mpr ⟨hi0, hle⟩, fun h => hb (by rw [← hγ, h, zero_pow (by positivity)]), hQ⟩
      exact hin (pow_eq_zero_iff (by positivity) |>.mp hB0)
    · exact sum_coef_ne_zero p (by omega) s β κ hinj ⟨i0, hi0, hb, hc0⟩ hA0

/-- Position `t` of `RingMap::new`'s prefix list after `p` stages holds exponent `kk p t`. -/
def kk : ℕ → ℕ → ℕ
  | 0, _ => 0
  | p + 1, t => if t < 2 ^ p then kk p t else kk p (t - 2 ^ p) + dsh p

/-- The six-bit reversal: the position of exponent `k` in `RingMap::new`'s prefix list. -/
def rev6 (k : ℕ) : ℕ := (List.range 6).foldl (fun acc q => acc + if k.testBit q then 2 ^ (5 - q) else 0) 0

theorem kk_rev6 : ∀ k < 64, kk 6 (rev6 k) = k ∧ rev6 k < 64 := by decide

theorem kk_dvd : ∀ p ≤ 6, ∀ t < 2 ^ p, 2 ^ (6 - p) ∣ kk p t ∧ kk p t + 2 ^ (6 - p) ≤ 64
  | 0, _, t, _ => by simp [kk]
  | p + 1, hp, t, ht => by
    have hp6 : p < 6 := by omega
    rw [six_sub_succ hp6]
    have h2 := two_pow_six_sub hp6
    simp only [kk]
    split_ifs with h
    · obtain ⟨hd, hl⟩ := kk_dvd p (by omega) t h
      rw [h2] at hd hl
      exact ⟨(dvd_mul_left _ _).trans hd, by omega⟩
    · obtain ⟨hd, hl⟩ := kk_dvd p (by omega) (t - 2 ^ p) (by rw [pow_succ] at ht; omega)
      rw [h2] at hd hl
      exact ⟨Nat.dvd_add ((dvd_mul_left _ _).trans hd) (dvd_refl _), by omega⟩

/-- `kk p t` is never `D` past another prefix exponent: `c_{kk p t - d_p}` is zero. -/
theorem coef_kk_sub {p : ℕ} (hp : p < 6) {t : ℕ} (ht : t < 2 ^ p) (hd : dsh p ≤ kk p t) :
    coef p (kk p t - dsh p) = 0 := by
  by_contra h
  have h1 := (coef_support p hp.le _ h).1
  have h2 := (kk_dvd p hp.le t ht).1
  rw [two_pow_six_sub hp] at h1 h2
  have h3 := Nat.dvd_sub h2 h1
  rw [show kk p t - (kk p t - dsh p) = dsh p by omega] at h3
  have := Nat.le_of_dvd (dsh_pos p) h3
  have := dsh_pos p
  omega

/-- `kk p t + d_p` is not a prefix exponent: `c_{kk p t + d_p}` is zero after `p` stages. -/
theorem coef_kk_add {p : ℕ} (hp : p < 6) {t : ℕ} (ht : t < 2 ^ p) : coef p (kk p t + dsh p) = 0 := by
  by_contra h
  have h1 := (coef_support p hp.le _ h).1
  have h2 := (kk_dvd p hp.le t ht).1
  rw [two_pow_six_sub hp] at h1 h2
  have h3 := (Nat.dvd_add_right h2).mp h1
  have := Nat.le_of_dvd (dsh_pos p) h3
  have := dsh_pos p
  omega

theorem coef_kk_ne_zero : ∀ p ≤ 6, ∀ t < 2 ^ p, coef p (kk p t) ≠ 0
  | 0, _, t, _ => by simp [kk, coef]
  | p + 1, hp, t, ht => by
    have hp6 : p < 6 := by omega
    intro hz
    simp only [coef] at hz
    obtain ⟨hA, hB⟩ := sep_zero (vr p) (vr_not_mem hp6 _) hz
    by_cases h : t < 2 ^ p
    · have hk : kk (p + 1) t = kk p t := by simp [kk, h]
      rw [hk] at hA
      exact coef_kk_ne_zero p (by omega) t h hA
    · have ht' : t - 2 ^ p < 2 ^ p := by rw [pow_succ] at ht; omega
      have hk : kk (p + 1) t = kk p (t - 2 ^ p) + dsh p := by simp [kk, h]
      rw [hk, if_pos (by omega), show kk p (t - 2 ^ p) + dsh p - dsh p = kk p (t - 2 ^ p) by omega] at hB
      exact coef_kk_ne_zero p (by omega) _ ht' (pow_eq_zero_iff (by positivity) |>.mp hB)

theorem coef_ne_zero {k : ℕ} (hk : k < 64) : coef 6 k ≠ 0 := by
  have h := coef_kk_ne_zero 6 le_rfl (rev6 k) (kk_rev6 k hk).2
  rwa [(kk_rev6 k hk).1] at h

/-- The total degree bound after `p` stages: stage `p` raises to `2^d_p` and multiplies by `X_p`. -/
def degB : ℕ → ℕ
  | 0 => 0
  | p + 1 => 1 + 2 ^ dsh p * degB p

/-- The degree of `c_63`, Annex A's bound. -/
def phiDeg : ℕ := degB 6

theorem phiDeg_eq : phiDeg = 2 ^ 31 + 2 ^ 15 + 2 ^ 7 + 2 ^ 3 + 2 + 1 := by decide

theorem phiDeg_lt : phiDeg < 2 ^ 32 := by rw [phiDeg_eq]; norm_num

theorem coef_totalDegree : ∀ p k, (coef p k).totalDegree ≤ degB p
  | 0, k => by simp only [coef]; split_ifs <;> simp [degB]
  | p + 1, k => by
    simp only [coef, degB]
    have hle : degB p ≤ 1 + 2 ^ dsh p * degB p := le_add_left (Nat.le_mul_of_pos_left _ (by positivity))
    refine (totalDegree_add _ _).trans (max_le ((coef_totalDegree p k).trans hle) ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X]
    split_ifs
    · exact Nat.add_le_add_left ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (coef_totalDegree p _))) 1
    · simp

/-! A nonzero error leaves a nonzero pairing (Annex A, sixty-four terms). -/

theorem root_ne_frob32 : root ^ 2 ^ 32 ≠ root := fun h => by
  have := root_pow_two_pow_32_sub_unit
  rw [h, sub_self, mul_zero] at this
  exact zero_ne_one this

theorem frobS_mul {m : ℕ} (h : root ^ 2 ^ m = root) : ∀ c, root ^ 2 ^ (m * c) = root
  | 0 => by simp
  | c + 1 => by rw [mul_add, mul_one, pow_add, pow_mul, frobS_mul h c, h]

theorem frobS_sub {a b : ℕ} (ha : root ^ 2 ^ a = root) (hb : root ^ 2 ^ b = root) (hab : b ≤ a) :
    root ^ 2 ^ (a - b) = root := by
  apply frob_inj b
  rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hab, ha, hb]

theorem frobS_gcd (a b : ℕ) : root ^ 2 ^ a = root → root ^ 2 ^ b = root → root ^ 2 ^ Nat.gcd a b = root :=
  Nat.gcd.induction (P := fun a b => root ^ 2 ^ a = root → root ^ 2 ^ b = root → root ^ 2 ^ Nat.gcd a b = root) a b
    (fun n _ hn => by simpa using hn)
    (fun m n _ ih ha hb => by
      rw [Nat.gcd_rec]
      refine ih ?_ ha
      have hmul := frobS_mul ha (n / m)
      have := frobS_sub hb hmul (Nat.mul_div_le n m)
      rwa [← Nat.eq_sub_of_add_eq (Nat.mod_add_div n m)] at this)

/-- The 64 conjugates `x^(2^j)`, `j < 64`, are distinct. -/
theorem root_frob_inj {a b : ℕ} (ha : a < 64) (hb : b < 64) (h : root ^ 2 ^ a = root ^ 2 ^ b) : a = b := by
  have key : ∀ a b : ℕ, a < b → b < 64 → root ^ 2 ^ a = root ^ 2 ^ b → False := fun a b hab hb h => by
    have h1 : root ^ 2 ^ (b - a) = root := by
      apply (frob_inj a ?_).symm
      rw [h, ← pow_mul, ← pow_add, Nat.sub_add_cancel hab.le]
    have hg := frobS_gcd _ _ h1 root_pow_two_pow_64
    have hdiv : ∀ m < 64, 0 < m → 32 % Nat.gcd m 64 = 0 := by decide
    have h32 := frobS_mul hg (32 / Nat.gcd (b - a) 64)
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (hdiv _ (by omega) (by omega)))] at h32
    exact root_ne_frob32 h32
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (key a b hab hb h).elim
  · exact hab
  · exact (key b a hab ha h.symm).elim

/-- The node `x^(2^-k) = x^(2^((64 - k) mod 64))` of term `k`'s Horner sum. -/
noncomputable def node (k : ℕ) : E := emb (root ^ 2 ^ ((64 - k) % 64))

theorem node_frob {k : ℕ} (hk : k < 64) : node k ^ 2 ^ k = xE := by
  rw [node, ← emb_pow, ← pow_mul, ← pow_add, xE]
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp
  · rw [show (64 - k) % 64 + k = 64 by omega, root_pow_two_pow_64]

theorem node_inj : Function.Injective fun k : Fin 64 => node k := fun a b h => by
  have h1 := emb_inj h
  have := root_frob_inj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h1
  have ha := a.isLt; have hb := b.isLt
  exact Fin.ext (by omega)

/-- `Σ_i x^i δ_i^(2^k)`, the coefficient of `c_k` in the error `Σ_i x^i Φ(δ_i)`. -/
noncomputable def pair (δ : Fin 64 → E) (k : ℕ) : E := ∑ i : Fin 64, xE ^ (i : ℕ) * δ i ^ 2 ^ k

theorem pair_eq (δ : Fin 64 → E) {k : ℕ} (hk : k < 64) :
    pair δ k = (∑ i : Fin 64, node k ^ (i : ℕ) * δ i) ^ 2 ^ k := by
  rw [sum_pow_char_pow, pair]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_pow, ← pow_mul, mul_comm (i : ℕ), pow_mul, node_frob hk]

theorem exists_pair_ne_zero (δ : Fin 64 → E) (hδ : δ ≠ 0) : ∃ k < 64, pair δ k ≠ 0 := by
  by_contra hall
  have hall' : ∀ k < 64, pair δ k = 0 := fun k hk => by
    by_contra h
    exact hall ⟨k, hk, h⟩
  apply hδ
  set R : Polynomial E := ∑ i : Fin 64, Polynomial.C (δ i) * Polynomial.X ^ (i : ℕ) with hR
  have hev : ∀ k : Fin 64, R.eval (node k) = 0 := fun k => by
    have := hall' k k.isLt
    rw [pair_eq δ k.isLt] at this
    have h0 := pow_eq_zero_iff (by positivity) |>.mp this
    rw [hR, Polynomial.eval_finsetSum, ← h0]
    refine sum_congr rfl fun i _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
  have hdeg : R.natDegree < Fintype.card (Fin 64) := by
    rw [Fintype.card_fin]
    exact lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ =>
      (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt_succ i.isLt)) (by norm_num)
  have hR0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero R node_inj hev hdeg
  funext j
  have hc := congrArg (fun P => Polynomial.coeff P (j : ℕ)) hR0
  simp only [hR, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
  rw [sum_eq_single j (fun i _ hne => if_neg (fun h => hne (Fin.ext h.symm))) (by simp), if_pos rfl] at hc
  exact hc

/-! Schwartz-Zippel over the six challenges. -/

/-- The error polynomial `Σ_k pair_k c_k`. -/
noncomputable def errPoly (δ : Fin 64 → E) : MvPolynomial (Fin 6) E := ∑ k ∈ range 64, C (pair δ k) * coef 6 k

theorem eval_errPoly (δ : Fin 64 → E) (f : Fin 6 → E) :
    eval f (errPoly δ) = ∑ i : Fin 64, xE ^ (i : ℕ) * Phi f (δ i) := by
  simp only [errPoly, map_sum, map_mul, eval_C, pair, phi_expand, mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun k _ => by ring

theorem errPoly_ne_zero (δ : Fin 64 → E) (h : ∃ k < 64, pair δ k ≠ 0) : errPoly δ ≠ 0 := by
  obtain ⟨k, hk, hp⟩ := h
  exact sum_coef_ne_zero 6 le_rfl (range 64) (pair δ) id (fun _ _ _ _ h => h)
    ⟨k, mem_range.mpr hk, hp, coef_ne_zero hk⟩

theorem errPoly_totalDegree (δ : Fin 64 → E) : (errPoly δ).totalDegree ≤ phiDeg :=
  totalDegree_finsetSum_le fun k _ => (totalDegree_mul _ _).trans (by
    rw [totalDegree_C, zero_add]; exact coef_totalDegree 6 k)

/-- The challenge vectors at which an error `δ` cancels in the target. -/
noncomputable def ringBad (δ : Fin 64 → E) : Finset (Fin 6 → E) :=
  open Classical in univ.filter fun f => ∑ i : Fin 64, xE ^ (i : ℕ) * Phi f (δ i) = 0

/-- Annex A: a nonzero error cancels at at most `phiDeg · |E|^5` of the `|E|^6` challenge vectors. -/
theorem ringBad_card (δ : Fin 64 → E) (hδ : δ ≠ 0) : (ringBad δ).card ≤ phiDeg * Fintype.card E ^ 5 := by
  classical
  have hP := errPoly_ne_zero δ (exists_pair_ne_zero δ hδ)
  have hsz := schwartz_zippel_totalDegree hP (univ : Finset E)
  have hset : (ringBad δ).card = (#{f ∈ Fintype.piFinset fun _ : Fin 6 => (univ : Finset E) |
      eval f (errPoly δ) = 0}) := by
    rw [ringBad, Fintype.piFinset_univ]
    congr 1
    ext f
    simp [eval_errPoly]
  rw [← hset, card_univ] at hsz
  have hq : (0 : ℚ≥0) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have hd : ((errPoly δ).totalDegree : ℚ≥0) / Fintype.card E ≤ (phiDeg : ℚ≥0) / Fintype.card E :=
    div_le_div_of_nonneg_right (by exact_mod_cast errPoly_totalDegree δ) hq.le
  have h := hsz.trans hd
  rw [div_le_div_iff₀ (by positivity) hq] at h
  have h' : ((ringBad δ).card : ℚ≥0) ≤ phiDeg * (Fintype.card E : ℚ≥0) ^ 5 := by
    have h6 : (phiDeg : ℚ≥0) * (Fintype.card E : ℚ≥0) ^ 6 = (phiDeg * (Fintype.card E : ℚ≥0) ^ 5) *
        Fintype.card E := by ring
    rw [h6] at h
    exact le_of_mul_le_mul_right h hq
  exact_mod_cast h'

/-- `|E| = 2^192`: three coordinates over `K`. -/
theorem card_E : Fintype.card E = 2 ^ 192 := by
  rw [← Fintype.card_of_bijective (f := fun p : K × K × K => toE p.1 p.2.1 p.2.2)
    ⟨fun p q h => by
      obtain ⟨h0, h1, h2⟩ := toE_injective _ _ _ _ _ _ h
      exact Prod.ext h0 (Prod.ext h1 h2),
     fun e => by obtain ⟨a, b, c, h⟩ := toE_surjective e; exact ⟨(a, b, c), h⟩⟩]
  rw [Fintype.card_prod, Fintype.card_prod, card_K]
  norm_num

/-- The same as a fraction of the challenge vectors: below `2^32 / 2^192 = 2^-160`. -/
theorem ringBad_frac (δ : Fin 64 → E) (hδ : δ ≠ 0) :
    ((ringBad δ).card : ℚ≥0) / Fintype.card E ^ 6 ≤ 2 ^ 32 / 2 ^ 192 := by
  have h := ringBad_card δ hδ
  rw [card_E] at h ⊢
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : ((ringBad δ).card : ℚ≥0) ≤ phiDeg * (2 ^ 192 : ℚ≥0) ^ 5 := by exact_mod_cast h
  have h2 : (phiDeg : ℚ≥0) ≤ 2 ^ 32 := by exact_mod_cast phiDeg_lt.le
  calc ((ringBad δ).card : ℚ≥0) * 2 ^ 192 ≤ phiDeg * (2 ^ 192 : ℚ≥0) ^ 5 * 2 ^ 192 := by gcongr
    _ ≤ 2 ^ 32 * (2 ^ 192 : ℚ≥0) ^ 5 * 2 ^ 192 := by gcongr
    _ = 2 ^ 32 * ((2 : ℕ) ^ 192 : ℚ≥0) ^ 6 := by push_cast; ring

/-! The packed region, its bit slices and the weighted opening. -/

/-- Bit `i` of a word, in `E`. -/
noncomputable def bitE (w : K) (i : ℕ) : E := if coeff w i = 1 then 1 else 0

theorem bitZ_toWord (w : K) {i : ℕ} (hi : i < 64) : bitZ (toWord w) i = coeff w i := by
  rw [bitZ, toWord, testBit_num _ _ _ hi]
  rcases zmod2_cases (coeff w i) with h | h <;> simp [h]

/-- The bit-packing identity: a word is the sum of its 64 bits times `x^i`. -/
theorem pack (w : K) : emb w = ∑ i : Fin 64, bitE w i * xE ^ (i : ℕ) := by
  have hlt : toWord w < 2 ^ 64 := num_lt _ _
  have h1 : w = ev (toWord w) := by
    have h0 : ofWord (toWord w) = w := toWord_injective (toWord_ofWord _ hlt)
    calc w = ofWord (toWord w) := h0.symm
      _ = ev (toWord w) := by rw [ofWord, Nat.mod_eq_of_lt hlt]
  rw [show emb w = emb (ev (toWord w)) from congrArg emb h1, ev_eq_sum 64 _ hlt]
  rw [show emb (∑ i : Fin 64, bitZ (toWord w) i • root ^ (i : ℕ)) =
    ∑ i : Fin 64, emb (bitZ (toWord w) i • root ^ (i : ℕ)) from map_sum (AdjoinRoot.of extModulus) _ _]
  refine sum_congr rfl fun i _ => ?_
  rw [bitZ_toWord w i.isLt, bitE, xE, ← emb_pow]
  rcases zmod2_cases (coeff w i) with h | h <;> simp [h, emb_zero]

/-- The multilinear extension of bit slice `i` of `q` at `r`. -/
noncomputable def sliceMle {n : ℕ} (q : (Fin n → E) → K) (r : Fin n → E) (i : ℕ) : E :=
  ∑ u ∈ cube n, eqv r u * bitE (q u) i

/-- The weighted opening WHIR proves: `Σ_u Φ(eq(r, u)) q(u) = T` over the region's cube. -/
def RingOpening {n : ℕ} (q : (Fin n → E) → K) (r : Fin n → E) (f : Fin 6 → E) (T : E) : Prop :=
  ∑ u ∈ cube n, Phi f (eqv r u) * emb (q u) = T

theorem phi_sum {ι : Type} (f : Fin 6 → E) (s : Finset ι) (g : ι → E) : Phi f (∑ u ∈ s, g u) = ∑ u ∈ s, Phi f (g u) :=
  map_sum (phiHom f) g s

theorem phi_bit (f : Fin 6 → E) (a : E) (w : K) (i : ℕ) : Phi f (a * bitE w i) = bitE w i * Phi f a := by
  unfold bitE
  split_ifs
  · simp
  · rw [mul_zero, zero_mul]; exact phiN_zero f 6

/-- Completeness (Annex A, equation `complete`): the honest weighted sum is the target of the true slices. -/
theorem weighted_sum_eq {n : ℕ} (q : (Fin n → E) → K) (r : Fin n → E) (f : Fin 6 → E) :
    ∑ u ∈ cube n, Phi f (eqv r u) * emb (q u) = ∑ i : Fin 64, xE ^ (i : ℕ) * Phi f (sliceMle q r i) := by
  simp only [sliceMle, phi_sum, phi_bit, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [pack, mul_sum]
  exact sum_congr rfl fun i _ => by ring

/-- Non-vacuity: honest slices meet the opening at their target. -/
example {n : ℕ} (q : (Fin n → E) → K) (r : Fin n → E) (f : Fin 6 → E) :
    RingOpening q r f (∑ i : Fin 64, xE ^ (i : ℕ) * Phi f (sliceMle q r i)) := weighted_sum_eq q r f

theorem target_sub (f : Fin 6 → E) (s t : Fin 64 → E) :
    ∑ i : Fin 64, xE ^ (i : ℕ) * Phi f (s i - t i) =
      ∑ i : Fin 64, xE ^ (i : ℕ) * Phi f (s i) - ∑ i : Fin 64, xE ^ (i : ℕ) * Phi f (t i) := by
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun i _ => by rw [← phiHom_apply, map_sub, phiHom_apply, phiHom_apply, mul_sub]

/-- An opening at the target of slices `s` puts the challenges in `ringBad` of their errors. -/
theorem mem_ringBad {n : ℕ} (q : (Fin n → E) → K) (r : Fin n → E) (s : Fin 64 → E) (f : Fin 6 → E)
    (h : RingOpening q r f (∑ i : Fin 64, xE ^ (i : ℕ) * Phi f (s i))) :
    f ∈ ringBad fun i => s i - sliceMle q r i := by
  classical
  have h' : ∑ u ∈ cube n, Phi f (eqv r u) * emb (q u) = ∑ i : Fin 64, xE ^ (i : ℕ) * Phi f (s i) := h
  rw [ringBad, mem_filter, target_sub, ← h', weighted_sum_eq, sub_self]
  exact ⟨mem_univ _, rfl⟩

/-- Ring switching's soundness for one claim: if some slice claim is not its bit-slice MLE, the challenge vectors at
which the target equals the honest weighted sum are at most `phiDeg · |E|^5`. -/
theorem ring_switch_sound {n : ℕ} (q : (Fin n → E) → K) (r : Fin n → E) (s : Fin 64 → E)
    (hs : s ≠ fun i : Fin 64 => sliceMle q r i) :
    (open Classical in (univ.filter fun f : Fin 6 → E =>
      RingOpening q r f (∑ i : Fin 64, xE ^ (i : ℕ) * Phi f (s i)))).card ≤ phiDeg * Fintype.card E ^ 5 := by
  classical
  refine (card_le_card fun f hf => mem_ringBad q r s f (mem_filter.mp hf).2).trans (ringBad_card _ ?_)
  intro h0
  apply hs
  funext i
  exact sub_eq_zero.mp (congrFun h0 i)

/-! The weight at WHIR's point (`RingShare::weight_at`). -/

/-- The weight the opening puts on the region: `W(u) = Φ(eq(r, u))`. -/
noncomputable def ringWeight {n : ℕ} (r : Fin n → E) (f : Fin 6 → E) (u : Fin n → E) : E := Phi f (eqv r u)

theorem eqv_frob {n : ℕ} (r u : Fin n → E) (hu : u ∈ cube n) (k : ℕ) :
    eqv r u ^ 2 ^ k = eqv (fun j => r j ^ 2 ^ k) u := by
  rw [eqv, eqv, ← prod_pow]
  refine prod_congr rfl fun j _ => ?_
  have hj := Fintype.mem_piFinset.mp hu j
  rcases mem_insert.mp hj with h | h
  · rw [h]; simp [sub_pow_char_pow]
  · rw [mem_singleton.mp h]; simp

theorem sum_eqv_mul : ∀ (n : ℕ) (a b : Fin n → E), ∑ u ∈ cube n, eqv a u * eqv b u = eqv a b
  | 0, a, b => by rw [sum_cube_zero]; simp [eqv]
  | n + 1, a, b => by
    rw [sum_cube_succ]
    simp only [eqv_cons]
    have h := sum_eqv_mul n (Fin.tail a) (Fin.tail b)
    have hb : eqv a b = ((1 - a 0) * (1 - b 0) + a 0 * b 0) * eqv (Fin.tail a) (Fin.tail b) := by
      conv_lhs => rw [← Fin.cons_self_tail b]
      rw [eqv_cons]
    rw [hb, ← h, mul_sum]
    exact sum_congr rfl fun u _ => by ring

/-- The weight's multilinear extension at `r'`: `Σ_k c_k eq(r^(2^k), r')` (Annex A, evaluating the weight). -/
theorem weight_mle {n : ℕ} (r r' : Fin n → E) (f : Fin 6 → E) :
    ∑ u ∈ cube n, ringWeight r f u * eqv r' u =
      ∑ k ∈ range 64, eval f (coef 6 k) * eqv (fun j => r j ^ 2 ^ k) r' := by
  simp only [ringWeight, phi_expand, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [← sum_eqv_mul n (fun j => r j ^ 2 ^ k) r', mul_sum]
  refine sum_congr rfl fun u hu => ?_
  have h1 := eqv_frob r u hu k
  have h2 : eqv r' u = eqv u r' := by simp only [eqv]; exact prod_congr rfl fun j _ => by ring
  rw [h1, h2]; ring

/-- In characteristic two `eq(a, b) = Π_j (1 + a_j + b_j)`. -/
theorem eqv_char2 {n : ℕ} (a b : Fin n → E) : eqv a b = ∏ j, (1 + a j + b j) := by
  simp only [eqv]
  exact prod_congr rfl fun j _ => by linear_combination (a j * b j - a j - b j) * two_E

/-- `weight_at`'s form: the Frobenius moved onto `r'`, `c̄_k` any coefficients with `c̄_k^(2^k) = c_k`. -/
theorem weight_mle_moved {n : ℕ} (r r' : Fin n → E) (f : Fin 6 → E) (cb : ℕ → E)
    (hcb : ∀ k < 64, cb k ^ 2 ^ k = eval f (coef 6 k)) :
    ∑ u ∈ cube n, ringWeight r f u * eqv r' u =
      ∑ k ∈ range 64, (cb k * ∏ j, (1 + r j + r' j ^ 2 ^ (192 - k))) ^ 2 ^ k := by
  rw [weight_mle]
  refine sum_congr rfl fun k hk => ?_
  have hk' := mem_range.mp hk
  rw [mul_pow, hcb k hk', eqv_char2, ← prod_pow]
  congr 1
  refine prod_congr rfl fun j _ => ?_
  rw [add_pow_char_pow, add_pow_char_pow, one_pow, ← pow_mul, ← pow_add, Nat.sub_add_cancel (by omega), frobE]

end LeanVMCircuits.Rec.RingSwitch

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model RingSwitch Finset

/-- The calls of the ring-switched target of one opening with one claim (`pcs::stack` verify, `RingFamily::draw`,
`RingFamily::share`, `RingShare::target`): the draws' `k_to_e` calls, `γ_rs` then `f_0..f_5` (`drawAt`), the first
`one` of `RingMap::new` (`mapAt`, after `powers(γ_rs, 1)`'s `one` and `mul(1, γ_rs)`), and the 64 slice wires (`s`). The
rest is laid out from `mapAt` as the code makes it: per stage `p`, `frobenius2(f_p)` (`e_to_k`, two `e_const`, two
`mul_k_add`), `64 - d_p` squarings (`mul(a, a)`), and `2^p` prefix products `mul(c, ladder[k + d_p])`; then the
coefficients' `one`, the target's `zero`, the family's `mul_add(1, s_i, 0)`, per term `k` a Horner chain of 63
`mul_const_add(acc, x^(2^-k), s_i)` from the last slice down and `mul(c̄_k, acc)`, and 63 `mul_add(acc, acc, term)`
from the last term down. -/
structure RingCert where
  drawAt : List ℕ := []
  mapAt : ℕ := 0
  s : List ℕ := []
  deriving Inhabited, Repr, DecidableEq

namespace RingCert

variable (os : Array (List ℕ)) (c : RingCert)

/-- `powers(γ_rs, 1)`'s `one`: the claim's scale `γ_rs^0`. -/
def scaleAt : ℕ := c.mapAt - 2

def gammaW : ℕ := o os (c.drawAt.getD 0 0)

/-- Map challenge `f_p`'s wire. -/
def fW (p : ℕ) : ℕ := o os (c.drawAt.getD (p + 1) 0)

/-- Stage `p`'s first call, its `e_to_k`. -/
def stageAt : ℕ → ℕ
  | 0 => c.mapAt + 1
  | p + 1 => stageAt p + 5 + (64 - dsh p) + 2 ^ p

/-- Stage `p`'s first prefix product. -/
def prodAt (p : ℕ) : ℕ := c.stageAt p + 5 + (64 - dsh p)

/-- Stage `p`'s ladder entry `f_p^(2^-j)` for `d_p ≤ j < 64`: the output of its `(64 - j)`-th squaring. -/
def ladW (p j : ℕ) : ℕ := o os (c.stageAt p + 4 + (64 - j))

/-- The coefficient at position `t` of the prefix list after `p` stages. -/
def cw : ℕ → ℕ → ℕ
  | 0, _ => o os c.mapAt
  | p + 1, t => if t < 2 ^ p then cw p t else o os (c.prodAt p + (t - 2 ^ p))

/-- The target's `zero`. -/
def zeroAt : ℕ := c.mapAt + 416

/-- The family's slice `i`. -/
def famW (i : ℕ) : ℕ := o os (c.zeroAt + 1 + i)

/-- Term `k`'s first Horner call. -/
def hornAt (k : ℕ) : ℕ := c.zeroAt + 65 + 64 * k

/-- Term `k`'s node `x^(2^-k)` as a word. -/
def word (k : ℕ) : ℕ := LeanVMCircuits.Rec.chain.getD ((64 - k) % 64) 0

/-- Term `k`'s Horner accumulator before step `t`. -/
def hIn (k t : ℕ) : ℕ := if t = 0 then c.famW os 63 else o os (c.hornAt k + (t - 1))

/-- The coefficient `c̄_k`: position `rev6 k` of the prefix list. -/
def coefW (k : ℕ) : ℕ := c.cw os 6 (rev6 k)

/-- Term `k`, `c̄_k · S(x^(2^-k))`. -/
def termW (k : ℕ) : ℕ := o os (c.hornAt k + 63)

/-- The closing chain's first call. -/
def closeAt : ℕ := c.zeroAt + 65 + 64 * 64

/-- The closing accumulator before step `t`. -/
def cIn (t : ℕ) : ℕ := if t = 0 then c.termW os 63 else o os (c.closeAt + (t - 1))

/-- The target `Σ_k term_k^(2^k)`. -/
def target : ℕ := o os (c.closeAt + 62)

def powCalls : List (ℕ × Call) := [(c.scaleAt, .one), (c.scaleAt + 1, .mul (o os c.scaleAt) (c.gammaW os))]

/-- `frobenius2(f_p)`: `e_to_k`, `e_const(y + y^2)`, `e_const(y^2)`, `mul_k_add(y + y^2, c2, f)`,
`mul_k_add(y^2, c1, u)`. -/
def frobCalls (p : ℕ) : List (ℕ × Call) :=
  [(c.stageAt p, .eToK (c.fW os p)), (c.stageAt p + 1, .eConst 0 1 1), (c.stageAt p + 2, .eConst 0 0 1),
    (c.stageAt p + 3, .mulKAdd (o os (c.stageAt p + 1)) (outAt os (c.stageAt p) 2) (c.fW os p)),
    (c.stageAt p + 4, .mulKAdd (o os (c.stageAt p + 2)) (outAt os (c.stageAt p) 1) (o os (c.stageAt p + 3)))]

def sqCalls (p : ℕ) : List (ℕ × Call) :=
  (List.range (64 - dsh p)).map fun t =>
    (c.stageAt p + 5 + t, .mul (o os (c.stageAt p + 4 + t)) (o os (c.stageAt p + 4 + t)))

def prodCalls (p : ℕ) : List (ℕ × Call) :=
  (List.range (2 ^ p)).map fun t => (c.prodAt p + t, .mul (c.cw os p t) (c.ladW os p (kk p t + dsh p)))

def famCalls : List (ℕ × Call) :=
  (List.range 64).map fun i => (c.zeroAt + 1 + i, .mulAdd (o os c.scaleAt) (c.s.getD i 0) (o os c.zeroAt))

def hornCalls (k : ℕ) : List (ℕ × Call) :=
  (List.range 63).map (fun t =>
      (c.hornAt k + t, .mulConstAdd (c.hIn os k t) (RingCert.word k) 0 0 (c.famW os (62 - t)))) ++
    [(c.hornAt k + 63, .mul (c.coefW os k) (o os (c.hornAt k + 62)))]

def closeCalls : List (ℕ × Call) :=
  (List.range 63).map fun t => (c.closeAt + t, .mulAdd (c.cIn os t) (c.cIn os t) (c.termW os (62 - t)))

def isKToE : Call → Bool
  | .kToE .. => true
  | _ => false

/-- Seven draws, each a `k_to_e`, in order and before the scale. -/
def drawsOk (cs : Array Call) : Bool :=
  c.drawAt.length == 7 && c.drawAt.all (fun j => (cs[j]?.map isKToE).getD false) &&
    (List.range 6).all (fun j => decide (c.drawAt.getD j 0 < c.drawAt.getD (j + 1) 0)) &&
    decide (c.drawAt.getD 6 0 < c.scaleAt)

/-- The check: the draws, 64 slices, and every call of the layout in the replay. Seven increasing draws before the
scale put `mapAt` past 8, so `scaleAt = mapAt - 2` does not wrap. -/
def okIn (cs : Array Call) (rl : Array Bool) : Bool :=
  c.drawsOk cs && c.s.length == 64 && callsOk cs rl (c.powCalls os) &&
    callsOk cs rl [(c.mapAt, .one)] &&
    (List.range 6).all (fun p => callsOk cs rl (c.frobCalls os p) && callsOk cs rl (c.sqCalls os p) &&
      callsOk cs rl (c.prodCalls os p)) &&
    callsOk cs rl [(c.zeroAt, .zero)] && callsOk cs rl (c.famCalls os) &&
    (List.range 64).all (fun k => callsOk cs rl (c.hornCalls os k)) && callsOk cs rl (c.closeCalls os)

/-- The drawn map challenges. -/
noncomputable def fV (val : Val) : Fin 6 → E := fun q => Model.ev val (c.fW os q)

/-- Slice `i`'s value. -/
noncomputable def sV (val : Val) : Fin 64 → E := fun i => Model.ev val (c.s.getD i 0)

/-- Every ring-switched target in a replay: a `one` with a `zero` 416 calls on and a `mul(1, γ_rs)` before it, its
draws the makers of `γ_rs` and of each stage's `e_to_k` input, its slices the family's `mul_add` inputs; kept where
`okIn` passes. -/
def find (rp : Replay) (rl : Array Bool) : List RingCert :=
  (List.range rp.calls.size).filterMap fun j =>
    if rp.calls[j]? == some Call.one && rp.calls[j + 416]? == some Call.zero then
      match (rp.calls[j - 1]? : Option Call) with
      | some (Call.mul _ g) =>
        let fs := (List.range 6).map fun p =>
          match (rp.calls[({ mapAt := j } : RingCert).stageAt p]? : Option Call) with
          | some (Call.eToK f) => f
          | _ => 0
        let s := (List.range 64).map fun i =>
          match (rp.calls[j + 417 + i]? : Option Call) with
          | some (Call.mulAdd _ b _) => b
          | _ => 0
        let c : RingCert := { drawAt := (g :: fs).map fun w => rp.maker.getD w 0, mapAt := j, s }
        if c.okIn rp.outs rp.calls rl then some c else none
      | _ => none
    else none

end RingCert

/-! The target's value where the calls hold. -/

section Sem

variable {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}

theorem ofWord_zero_rs : ofWord 0 = 0 := by simp [ofWord, ev_zero]

theorem ofWord_one_rs : ofWord 1 = 1 := by simp [ofWord, ev_one]

/-- `frobenius2`'s calls give `f_p^(2^128)`. -/
theorem RingCert.frob_sem (hF : Facts cs rl os st val) {c : RingCert} {p : ℕ}
    (h : callsOk cs rl (c.frobCalls os p) = true) :
    Model.ev val (o os (c.stageAt p + 4)) = Model.ev val (c.fW os p) ^ 2 ^ 128 := by
  have h0 : Call.Holds st val (os.getD (c.stageAt p) []) (.eToK (c.fW os p)) :=
    holds_of_mem hF h (by simp [RingCert.frobCalls])
  have h1 : Call.Holds st val (os.getD (c.stageAt p + 1) []) (.eConst 0 1 1) :=
    holds_of_mem hF h (by simp [RingCert.frobCalls])
  have h2 : Call.Holds st val (os.getD (c.stageAt p + 2) []) (.eConst 0 0 1) :=
    holds_of_mem hF h (by simp [RingCert.frobCalls])
  have h3 : Call.Holds st val (os.getD (c.stageAt p + 3) [])
      (.mulKAdd (o os (c.stageAt p + 1)) (outAt os (c.stageAt p) 2) (c.fW os p)) :=
    holds_of_mem hF h (by simp [RingCert.frobCalls])
  have h4 : Call.Holds st val (os.getD (c.stageAt p + 4) [])
      (.mulKAdd (o os (c.stageAt p + 2)) (outAt os (c.stageAt p) 1) (o os (c.stageAt p + 3))) :=
    holds_of_mem hF h (by simp [RingCert.frobCalls])
  simp only [Call.Holds] at h0 h1 h2 h3 h4
  have e1 : val (outAt os (c.stageAt p) 1) 0 = val (c.fW os p) 1 := h0 1 (by decide)
  have e2 : val (outAt os (c.stageAt p) 2) 0 = val (c.fW os p) 2 := h0 2 (by decide)
  rw [getD_o] at h1 h2 h3 h4
  rw [h4, h2, h3, h1, e1, e2, ofWord_zero_rs, ofWord_one_rs]
  rw [show Model.ev val (c.fW os p) = toE (val (c.fW os p) 0) (val (c.fW os p) 1) (val (c.fW os p) 2) from rfl,
    frob2]
  ring

/-- The squarings: after `t + 1` of them, `f_p^(2^128 · 2^(t+1))`. -/
theorem RingCert.sq_sem (hF : Facts cs rl os st val) {c : RingCert} {p : ℕ}
    (h : callsOk cs rl (c.sqCalls os p) = true) :
    ∀ t < 64 - dsh p, Model.ev val (o os (c.stageAt p + 5 + t)) = Model.ev val (o os (c.stageAt p + 4)) ^ 2 ^ (t + 1)
  | 0, ht => by
    have h0 : Call.Holds st val (os.getD (c.stageAt p + 5 + 0) [])
        (.mul (o os (c.stageAt p + 4 + 0)) (o os (c.stageAt p + 4 + 0))) :=
      holds_of_mem hF h (List.mem_map.mpr ⟨0, List.mem_range.mpr ht, rfl⟩)
    simp only [Call.Holds, getD_o, add_zero] at h0
    rw [add_zero, h0]; ring
  | t + 1, ht => by
    have h0 : Call.Holds st val (os.getD (c.stageAt p + 5 + (t + 1)) [])
        (.mul (o os (c.stageAt p + 4 + (t + 1))) (o os (c.stageAt p + 4 + (t + 1)))) :=
      holds_of_mem hF h (List.mem_map.mpr ⟨t + 1, List.mem_range.mpr ht, rfl⟩)
    simp only [Call.Holds, getD_o] at h0
    rw [h0, show c.stageAt p + 4 + (t + 1) = c.stageAt p + 5 + t by omega,
      RingCert.sq_sem hF h t (by omega), ← sq, ← pow_mul, ← pow_succ]

/-- The ladder: entry `j` raised to `2^j` is `f_p`. -/
theorem RingCert.lad_sem (hF : Facts cs rl os st val) {c : RingCert} {p : ℕ}
    (hf : callsOk cs rl (c.frobCalls os p) = true) (hs : callsOk cs rl (c.sqCalls os p) = true) {j : ℕ}
    (hj : dsh p ≤ j) (hj64 : j < 64) : Model.ev val (c.ladW os p j) ^ 2 ^ j = Model.ev val (c.fW os p) := by
  have e : 2 ^ 128 * 2 ^ (63 - j + 1) * 2 ^ j = 2 ^ 192 := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  rw [RingCert.ladW, show c.stageAt p + 4 + (64 - j) = c.stageAt p + 5 + (63 - j) by omega,
    RingCert.sq_sem hF hs (63 - j) (by omega), RingCert.frob_sem hF hf, ← pow_mul, ← pow_mul, ← mul_assoc, e,
    frobE]

theorem RingCert.fV_vr {c : RingCert} {p : ℕ} (hp : p < 6) : c.fV os val (vr p) = Model.ev val (c.fW os p) := by
  simp only [RingCert.fV, vr_val hp]

/-- The stages' calls. -/
def RingCert.stagesOk (os : Array (List ℕ)) (c : RingCert) (cs : Array Call) (rl : Array Bool) (p : ℕ) : Bool :=
  callsOk cs rl (c.frobCalls os p) && callsOk cs rl (c.sqCalls os p) && callsOk cs rl (c.prodCalls os p)

/-- The prefix coefficients: position `t` after `p` stages, raised to `2^(kk p t)`, is `c_(kk p t)` at the drawn
challenges. -/
theorem RingCert.cw_sem (hF : Facts cs rl os st val) {c : RingCert}
    (hst : ∀ p < 6, c.stagesOk os cs rl p = true) (hm : callsOk cs rl [(c.mapAt, .one)] = true) :
    ∀ p ≤ 6, ∀ t < 2 ^ p, Model.ev val (c.cw os p t) ^ 2 ^ kk p t = MvPolynomial.eval (c.fV os val) (coef p (kk p t))
  | 0, _, t, _ => by
    have h0 : Call.Holds st val (os.getD c.mapAt []) .one := holds_of_mem hF hm (List.mem_singleton_self _)
    simp only [Call.Holds, getD_o] at h0
    simp [RingCert.cw, kk, coef, h0]
  | p + 1, hp, t, ht => by
    have hp6 : p < 6 := by omega
    have hs := hst p hp6
    simp only [RingCert.stagesOk, Bool.and_eq_true] at hs
    obtain ⟨⟨hf, hq⟩, hpr⟩ := hs
    by_cases h : t < 2 ^ p
    · have hk : kk (p + 1) t = kk p t := by simp [kk, h]
      have hc : c.cw os (p + 1) t = c.cw os p t := by simp [RingCert.cw, h]
      rw [hk, hc, eval_coef_succ, RingCert.cw_sem hF hst hm p (by omega) t h]
      split_ifs with hd
      · rw [coef_kk_sub hp6 h hd]; simp
      · simp
    · obtain ⟨t', rfl⟩ : ∃ t', t = 2 ^ p + t' := ⟨t - 2 ^ p, by omega⟩
      have ht' : t' < 2 ^ p := by rw [pow_succ] at ht; omega
      have hk : kk (p + 1) (2 ^ p + t') = kk p t' + dsh p := by simp [kk]
      have hc : c.cw os (p + 1) (2 ^ p + t') = o os (c.prodAt p + t') := by simp [RingCert.cw]
      have h0 : Call.Holds st val (os.getD (c.prodAt p + t') [])
          (.mul (c.cw os p t') (c.ladW os p (kk p t' + dsh p))) :=
        holds_of_mem hF hpr (List.mem_map.mpr ⟨t', List.mem_range.mpr ht', rfl⟩)
      simp only [Call.Holds, getD_o] at h0
      have hb := (kk_dvd p hp6.le t' ht').2
      rw [two_pow_six_sub hp6] at hb
      have hd0 := dsh_pos p
      rw [hk, hc, h0, mul_pow, RingCert.lad_sem hF hf hq (by omega) (by omega), pow_add, pow_mul,
        RingCert.cw_sem hF hst hm p (by omega) t' ht', eval_coef_succ, coef_kk_add hp6 ht', if_pos (by omega),
        show kk p t' + dsh p - dsh p = kk p t' by omega, RingCert.fV_vr hp6]
      simp only [map_zero, zero_add]
      ring

/-- The coefficient wires: `c̄_k^(2^k) = c_k` at the drawn challenges, for the target and for `weight_at`. -/
theorem RingCert.coef_sem (hF : Facts cs rl os st val) {c : RingCert}
    (hst : ∀ p < 6, c.stagesOk os cs rl p = true) (hm : callsOk cs rl [(c.mapAt, .one)] = true) {k : ℕ}
    (hk : k < 64) : Model.ev val (c.coefW os k) ^ 2 ^ k = MvPolynomial.eval (c.fV os val) (coef 6 k) := by
  have h := RingCert.cw_sem hF hst hm 6 le_rfl (rev6 k) (kk_rev6 k hk).2
  rwa [(kk_rev6 k hk).1] at h

theorem RingCert.word_sem (k : ℕ) :
    toE (ofWord (RingCert.word k)) (ofWord 0) (ofWord 0) = RingSwitch.node k := by
  have hm : (64 - k) % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hlt := (chain_squares _ hm).2
  rw [ofWord_zero_rs, toE_emb, RingCert.word, ofWord, Nat.mod_eq_of_lt hlt, ev_chain _ hm.le, RingSwitch.node]

/-- Term `k`'s Horner chain: after `t` steps, `Σ_{i ≤ t} s_(63 - t + i) x^(i 2^-k)`. -/
theorem RingCert.horn_sem (hF : Facts cs rl os st val) {c : RingCert} {k : ℕ}
    (h : callsOk cs rl (c.hornCalls os k) = true) :
    ∀ t ≤ 63, Model.ev val (c.hIn os k t) =
      ∑ i ∈ range (t + 1), Model.ev val (c.famW os (63 - t + i)) * RingSwitch.node k ^ i
  | 0, _ => by simp [RingCert.hIn]
  | t + 1, ht => by
    have h0 : Call.Holds st val (os.getD (c.hornAt k + t) [])
        (.mulConstAdd (c.hIn os k t) (RingCert.word k) 0 0 (c.famW os (62 - t))) :=
      holds_of_mem hF h (List.mem_append_left _ (List.mem_map.mpr ⟨t, List.mem_range.mpr (by omega), rfl⟩))
    simp only [Call.Holds, getD_o] at h0
    rw [show c.hIn os k (t + 1) = o os (c.hornAt k + t) by simp [RingCert.hIn], h0, RingCert.word_sem,
      RingCert.horn_sem hF h t (by omega), sum_range_succ' _ (t + 1), sum_mul]
    have e0 : 63 - (t + 1) + 0 = 62 - t := by omega
    have e1 : ∀ i, 63 - (t + 1) + (i + 1) = 63 - t + i := fun i => by omega
    simp only [e0, e1, pow_zero, mul_one]
    congr 1
    exact sum_congr rfl fun i _ => by ring

/-- Term `k`: `c̄_k · Σ_i s_i x^(i 2^-k)`. -/
theorem RingCert.term_sem (hF : Facts cs rl os st val) {c : RingCert} {k : ℕ}
    (h : callsOk cs rl (c.hornCalls os k) = true) :
    Model.ev val (c.termW os k) = Model.ev val (c.coefW os k) *
      ∑ i ∈ range 64, Model.ev val (c.famW os i) * RingSwitch.node k ^ i := by
  have h0 : Call.Holds st val (os.getD (c.hornAt k + 63) []) (.mul (c.coefW os k) (o os (c.hornAt k + 62))) :=
    holds_of_mem hF h (List.mem_append_right _ (List.mem_singleton_self _))
  simp only [Call.Holds, getD_o] at h0
  have hh := RingCert.horn_sem hF h 63 le_rfl
  rw [show c.hIn os k 63 = o os (c.hornAt k + 62) by simp [RingCert.hIn]] at hh
  rw [RingCert.termW, h0, hh]
  simp only [Nat.sub_self, zero_add]

/-- The closing chain: after `t` steps, `Σ_{i ≤ t} term_(63 - t + i)^(2^i)`. -/
theorem RingCert.close_sem (hF : Facts cs rl os st val) {c : RingCert}
    (h : callsOk cs rl (c.closeCalls os) = true) :
    ∀ t ≤ 63, Model.ev val (c.cIn os t) = ∑ i ∈ range (t + 1), Model.ev val (c.termW os (63 - t + i)) ^ 2 ^ i
  | 0, _ => by simp [RingCert.cIn]
  | t + 1, ht => by
    have h0 : Call.Holds st val (os.getD (c.closeAt + t) [])
        (.mulAdd (c.cIn os t) (c.cIn os t) (c.termW os (62 - t))) :=
      holds_of_mem hF h (List.mem_map.mpr ⟨t, List.mem_range.mpr (by omega), rfl⟩)
    simp only [Call.Holds, getD_o] at h0
    have hsq : ∀ a : E, a * a = a ^ 2 ^ 1 := fun a => by ring
    rw [show c.cIn os (t + 1) = o os (c.closeAt + t) by simp [RingCert.cIn], h0,
      RingCert.close_sem hF h t (by omega), sum_range_succ' _ (t + 1), hsq, sum_pow_char_pow]
    have e0 : 63 - (t + 1) + 0 = 62 - t := by omega
    have e1 : ∀ i, 63 - (t + 1) + (i + 1) = 63 - t + i := fun i => by omega
    simp only [e0, e1, pow_zero, pow_one]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [← pow_mul, ← pow_succ]

/-- The target wire is `Σ_i x^i Φ(s_i)` at the drawn challenges. -/
theorem RingCert.target_sem (hF : Facts cs rl os st val) {c : RingCert} (h : c.okIn os cs rl = true) :
    Model.ev val (c.target os) = ∑ i : Fin 64, xE ^ (i : ℕ) * Phi (c.fV os val) (c.sV val i) := by
  simp only [RingCert.okIn, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hpow⟩, hm⟩, hst⟩, hz⟩, hfam⟩, hhorn⟩, hclose⟩ := h
  have hst' : ∀ p < 6, c.stagesOk os cs rl p = true := fun p hp => by
    have := hst p hp
    simp only [RingCert.stagesOk, Bool.and_eq_true]
    exact this
  have hone : Model.ev val (o os c.scaleAt) = 1 := by
    have := holds_of_mem hF hpow (List.mem_cons_self ..)
    simp only [Call.Holds, getD_o] at this
    exact this
  have hzero : Model.ev val (o os c.zeroAt) = 0 := by
    have := holds_of_mem hF hz (List.mem_singleton_self _)
    simp only [Call.Holds, getD_o] at this
    exact this
  have hfamv : ∀ i : Fin 64, Model.ev val (c.famW os i) = c.sV val i := fun i => by
    have h0 : Call.Holds st val (os.getD (c.zeroAt + 1 + i) [])
        (.mulAdd (o os c.scaleAt) (c.s.getD i 0) (o os c.zeroAt)) :=
      holds_of_mem hF hfam (List.mem_map.mpr ⟨i, List.mem_range.mpr i.isLt, rfl⟩)
    simp only [Call.Holds, getD_o] at h0
    rw [RingCert.famW, h0, hone, hzero, one_mul, add_zero]
    rfl
  have hc := RingCert.close_sem hF hclose 63 le_rfl
  rw [show c.cIn os 63 = o os (c.closeAt + 62) by simp [RingCert.cIn], show 63 + 1 = 64 from rfl] at hc
  rw [RingCert.target, hc]
  have hterm : ∀ k ∈ range 64, Model.ev val (c.termW os (63 - 63 + k)) ^ 2 ^ k =
      ∑ i : Fin 64, xE ^ (i : ℕ) * (MvPolynomial.eval (c.fV os val) (coef 6 k) * c.sV val i ^ 2 ^ k) :=
      fun k hk => by
    have hk' := mem_range.mp hk
    rw [Nat.sub_self, zero_add, RingCert.term_sem hF (hhorn k hk'), mul_pow,
      RingCert.coef_sem hF hst' hm hk', sum_pow_char_pow, mul_sum, ← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun i _ => ?_
    rw [hfamv i, mul_pow, ← pow_mul, mul_comm (i : ℕ), pow_mul, node_frob hk']
    ring
  rw [sum_congr rfl hterm, sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [← mul_sum, phi_expand]

/-- The ring switch's part: if the weighted opening holds at the target wire, every slice wire is its bit-slice MLE,
or the drawn challenges lie in `ringBad` of the slices' errors (`ringBad_card`: at most `phiDeg · |E|^5` of the
`|E|^6`). -/
theorem RingCert.sound (hF : Facts cs rl os st val) {c : RingCert} (h : c.okIn os cs rl = true) {n : ℕ}
    (q : (Fin n → E) → K) (r : Fin n → E) (hop : RingOpening q r (c.fV os val) (Model.ev val (c.target os))) :
    (∀ i : Fin 64, c.sV val i = sliceMle q r i) ∨
      c.fV os val ∈ ringBad fun i => c.sV val i - sliceMle q r i := by
  by_cases hall : ∀ i : Fin 64, c.sV val i = sliceMle q r i
  · exact Or.inl hall
  · right
    rw [RingCert.target_sem hF h] at hop
    exact mem_ringBad q r (c.sV val) (c.fV os val) hop

theorem RingCert.coefs_of_okIn {c : RingCert} (h : c.okIn os cs rl = true) :
    (∀ p < 6, c.stagesOk os cs rl p = true) ∧ callsOk cs rl [(c.mapAt, .one)] = true := by
  simp only [RingCert.okIn, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hm⟩, hst⟩, _⟩, _⟩, _⟩, _⟩ := h
  exact ⟨fun p hp => by simp only [RingCert.stagesOk, Bool.and_eq_true]; exact hst p hp, hm⟩

/-- The opening's weight at WHIR's point `r'` from the same coefficient wires (`RingShare::weight_at`'s closed form):
`Σ_k (c̄_k Π_j (1 + r_j + r'_j^(2^-k)))^(2^k)`. -/
theorem RingCert.weight_sem (hF : Facts cs rl os st val) {c : RingCert} (h : c.okIn os cs rl = true) {n : ℕ}
    (r r' : Fin n → E) :
    ∑ u ∈ Sumcheck.cube n, ringWeight r (c.fV os val) u * Sumcheck.eqv r' u =
      ∑ k ∈ range 64, (Model.ev val (c.coefW os k) * ∏ j, (1 + r j + r' j ^ 2 ^ (192 - k))) ^ 2 ^ k :=
  weight_mle_moved r r' _ _ fun _ hk =>
    RingCert.coef_sem hF (RingCert.coefs_of_okIn h).1 (RingCert.coefs_of_okIn h).2 hk

end Sem

/-! Mutation tests of `RingCert.okIn`'s rules, on calls whose call `j` outputs wire `100 + j` (`ringOuts`). The arrays
are built with `Array.mk`, which the kernel reads in one step, not by pushing. -/

/-- Call `j` outputs wire `100 + j`. -/
def ringOuts (n : ℕ) : Array (List ℕ) := Array.mk ((List.range n).map fun j => [100 + j])

/-- Draws at calls 0 to 6, `RingMap::new` at call 9 (the scale's `one` at 7), slices at wires `1000 + i`. -/
def mutRing : RingCert := { drawAt := List.range 7, mapAt := 9, s := (List.range 64).map (1000 + ·) }

/-- A run of calls from its first index, `free_e` before it. -/
def callRun (l : List (ℕ × Call)) : Array Call :=
  Array.mk (List.replicate (l.headD (0, .freeE)).1 Call.freeE ++ l.map (·.2))

def mutDraws : Array Call := Array.mk (List.replicate 7 (Call.kToE 0 0 0))

/-- Seven `k_to_e` draws in order before the scale pass; six draws, a draw that is not a `k_to_e`, draws out of order,
or a draw at the scale fail. -/
example : mutRing.drawsOk mutDraws = true := by decide +kernel

example : ({ mutRing with drawAt := List.range 6 } : RingCert).drawsOk mutDraws = false := by decide +kernel

example : mutRing.drawsOk (mutDraws.set! 3 .freeE) = false := by decide +kernel

example : ({ mutRing with drawAt := [0, 1, 2, 4, 3, 5, 6] } : RingCert).drawsOk mutDraws = false := by decide +kernel

example : ({ mutRing with drawAt := [0, 1, 2, 3, 4, 5, 7] } : RingCert).drawsOk (mutDraws.push (.kToE 0 0 0)) =
    false := by decide +kernel

/-- 63 slices fail. -/
example : ({ mutRing with s := List.range 63 } : RingCert).okIn (ringOuts 10) mutDraws #[] = false := by
  decide +kernel

/-- `powers(γ_rs, 1)`: a `one`, then `mul(1, γ_rs)` (`γ_rs` the first draw, wire 100); scaling by `f_0` fails. -/
example : callsOk (callRun [(7, .one), (8, .mul 107 100)]) #[] (mutRing.powCalls (ringOuts 9)) = true := by
  decide +kernel

example : callsOk (callRun [(7, .one), (8, .mul 107 101)]) #[] (mutRing.powCalls (ringOuts 9)) = false := by
  decide +kernel

/-- Stage 0's `frobenius2(f_0)` (`f_0` wire 101, its coordinates `e_to_k` outputs 201, 202): `mul_k_add(y + y^2, c2,
f)` then `mul_k_add(y^2, c1, u)`; swapping the coordinates fails, and so does `f_1`. -/
def mutFrobOuts : Array (List ℕ) := (ringOuts 16).set! 10 [110, 201, 202]

example : callsOk (callRun [(10, .eToK 101), (11, .eConst 0 1 1), (12, .eConst 0 0 1), (13, .mulKAdd 111 202 101),
    (14, .mulKAdd 112 201 113)]) #[] (mutRing.frobCalls mutFrobOuts 0) = true := by decide +kernel

example : callsOk (callRun [(10, .eToK 101), (11, .eConst 0 1 1), (12, .eConst 0 0 1), (13, .mulKAdd 111 201 101),
    (14, .mulKAdd 112 202 113)]) #[] (mutRing.frobCalls mutFrobOuts 0) = false := by decide +kernel

example : callsOk (callRun [(10, .eToK 102), (11, .eConst 0 1 1), (12, .eConst 0 0 1), (13, .mulKAdd 111 202 102),
    (14, .mulKAdd 112 201 113)]) #[] (mutRing.frobCalls mutFrobOuts 0) = false := by decide +kernel

/-- Stage 0's 32 squarings, each of the previous output; squaring one output twice fails. -/
example : callsOk (callRun ((List.range 32).map fun t => (15 + t, .mul (114 + t) (114 + t)))) #[]
    (mutRing.sqCalls (ringOuts 47) 0) = true := by decide +kernel

example : callsOk (callRun ((List.range 32).map fun t => (15 + t, .mul (114 + t - if t = 9 then 1 else 0)
    (114 + t - if t = 9 then 1 else 0)))) #[] (mutRing.sqCalls (ringOuts 47) 0) = false := by decide +kernel

/-- Stage 0's product `mul(1, f_0^(2^-32))` reads the last squaring (call 46); its 31st (slot 33) fails. -/
example : callsOk (callRun [(47, .mul 109 146)]) #[] (mutRing.prodCalls (ringOuts 48) 0) = true := by decide +kernel

example : callsOk (callRun [(47, .mul 109 145)]) #[] (mutRing.prodCalls (ringOuts 48) 0) = false := by
  decide +kernel

/-- Stage 1's products (calls 101, 102): the prefix `[0, 32]`'s coefficients `1` and stage 0's product (wire 147)
against `f_1^(2^-16)` (wire 200) and `f_1^(2^-48)` (wire 168); swapping the coefficients fails. -/
example : callsOk (callRun [(101, .mul 109 200), (102, .mul 147 168)]) #[] (mutRing.prodCalls (ringOuts 103) 1) =
    true := by decide +kernel

example : callsOk (callRun [(101, .mul 147 200), (102, .mul 109 168)]) #[] (mutRing.prodCalls (ringOuts 103) 1) =
    false := by decide +kernel

/-- The family's slices `mul_add(1, s_i, 0)` (the scale's `one` wire 107, the target's `zero` wire 525); scaling by
`γ_rs` (wire 100) fails. -/
example : callsOk (callRun ((List.range 64).map fun i => (426 + i, .mulAdd 107 (1000 + i) 525))) #[]
    (mutRing.famCalls (ringOuts 490)) = true := by decide +kernel

example : callsOk (callRun ((List.range 64).map fun i => (426 + i, .mulAdd 100 (1000 + i) 525))) #[]
    (mutRing.famCalls (ringOuts 490)) = false := by decide +kernel

/-- The coefficient of term 1 is stage 5's first product (call 392, position `rev6 1 = 32` of the prefix list), and
that of term 32 is stage 0's product (call 47, position 1). -/
example : mutRing.coefW (ringOuts 400) 1 = 492 ∧ mutRing.coefW (ringOuts 400) 32 = 147 := by decide +kernel

/-- Term 1's Horner chain at `x^(2^63)` from the last slice down: the node `x^2`, or the slices from the first up,
fail. -/
def mutHorn (w : ℕ) (down : Bool) : Array Call :=
  callRun ((List.range 63).map (fun t => (554 + t, .mulConstAdd (if t = 0 then 589 else 653 + t) w 0 0
    (if down then 588 - t else 527 + t))) ++ [(617, .mul 492 716)])

example : callsOk (mutHorn (LeanVMCircuits.Rec.chain.getD 1 0) true) #[] (mutRing.hornCalls (ringOuts 618) 1) =
    false := by decide +kernel

example : callsOk (mutHorn (LeanVMCircuits.Rec.chain.getD 63 0) false) #[] (mutRing.hornCalls (ringOuts 618) 1) =
    false := by decide +kernel

/-- The closing chain `mul_add(acc, acc, term_k)` from term 63 down: from term 0 up fails. -/
example : callsOk (callRun ((List.range 63).map fun t => (4586 + t, .mulAdd (4685 + t) (4685 + t) (653 + 64 * t))))
    #[] (mutRing.closeCalls (ringOuts 4649)) = false := by decide +kernel

end LeanVMCircuits.Rec.Bind
