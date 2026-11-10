/-
  LeanVM.Protocol.RingMap

  The verifier's ring-switching computations over F128 (the drawn map's inner stage, its
  Frobenius coefficients and the target by Horner sums at `z_p = x^(2^(64 - 8p))`), proved equal
  to the two-stage map `Φ` of `ToArkLib/FrobeniusMap.lean`; the weight `W(u) = Φ(eq(r, u))` and its
  multilinear extension; completeness and soundness of the reduction, as field lemmas.
-/

module

public import LeanVM.Protocol.RingFields

/-!
# Ring switching's map, target and weight

Annex A of the specification (`doc/leanvm/body/a-ring-switching.tex`, §A.2 to §A.6) and
`crates/verifier/src/ring_switch.rs` at leanVM `f128`. The verifier draws `f_0, …, f_7` then
`g_0, …, g_7` in `E` and uses

```text
Ψ(a) = Σ_{b < 8} g_b a^(2^b)                      ring_psi            ringPsi
Φ(a) = Σ_{p < 8} f_p Ψ(a)^(2^(8p))                                    frobPhi 8 f g
c_(8p + b) = f_p g_b^(2^(8p))                      ring_coefficients   ringCoefficients
T = Σ_p f_p (Σ_i z_p^i Ψ(s_i))^(2^(8p))            ring_target         ringTarget
W(r') = Σ_k c_k Π_n (1 + r_n^(2^k) + r'_n)         ring_weight
```

with `z_p = x^(2^(64 - 8p))`. The definitions below transcribe the Rust functions on lists
(`frobenius8`, `ringPsi`, `ringCoefficients`, `ringTarget`, with `hornerEval` the verifier's
`poly_eval`). Proved here, for challenges `f g : Fin 8 → E` read as the lists `List.ofFn f`,
`List.ofFn g`:

* `ringPsi_ofFn`: the inner stage is `frobPsi g`;
* `ringCoefficients_idxSum`, `frobPhi_eq_idxSum`: the coefficients, `64` of them
  (`length_ringCoefficients`), are those of `Φ` as a Frobenius sum,
  `Φ(a) = Σ_k c_k a^(2^k)`, `idxSum` being the weighted sum over a list's positions;
* `ringTarget_eq`: the target is `Σ_i x^i Φ(s_i)` (equation `eq:complete`): the `p`-th Horner sum
  raised to `2^(8p)` is `Σ_i x^i Ψ(s_i)^(2^(8p))`, since `z_p^(2^(8p)) = x^(2^64) = x`;
* `frobPhi_eqP`, `sum_eqP_mul_eqP`, `ringWeight_mle`: on the cube `Φ(eq(r, u)) = Σ_k c_k eq(r^(2^k), u)`,
  the Frobenius passing through `eq` at a bit, and the extension of `u ↦ Φ(eq(r, u))` at `r'` is
  `Σ_k c_k eq(r^(2^k), r')`, what `ring_weight` computes;
* `ring_complete`: for a column `q(u) = Σ_i Q_i(u) x^i`, `Σ_u Φ(eq(r, u)) q(u) = Σ_i x^i Φ(Q̂_i(r))`
  (equation `eq:complete`): the opening's honest value is the target at honest slice claims;
* `card_ringTarget_bad_le`, `ringTarget_bad_ratio_le`: slice claims `s ≠ ẑ` give the honest
  target at no more than `2·|E|^15` of the challenges, a fraction `2/|E|` (§A.4).

Point coordinates are `Fin μ → E`, a cube point `bitV u` for `u : Fin μ → Bool`.
-/

namespace LeanVM.Protocol.Ring

open LeanVM.Parameters Finset
open scoped ENNReal

@[expose] public section

/-! ## The verifier's computations -/

/-- `RING_MAP_WIDTH`: the challenges come in two rows of eight, `f_p` then `g_b`
(`ring_switch.rs:10`). -/
def ringMapWidth : ℕ := 8

/-- `GEN = E::new(2, 0)`, `x` in `E`. -/
def genE : E := ofK g

/-- `frobenius_8(value, p)`: `value^(2^(8p))` by `8p` squarings (`ring_switch.rs:13-15`). -/
def frobenius8 (value : E) (p : ℕ) : E :=
  (List.range (ringMapWidth * p)).foldl (fun v _ ↦ v * v) value

/-- `ring_psi(value, g)`: `Σ_b g_b value^(2^b)` (`ring_switch.rs:18-26`). -/
def ringPsi (value : E) (g : List E) : E :=
  (g.foldl (fun (acc : E × E) gb ↦ (acc.1 + gb * acc.2, acc.2 * acc.2)) (0, value)).1

/-- `poly_eval(coefficients, point)`: Horner's rule over the coefficients, constant first. -/
def hornerEval (coefficients : List E) (point : E) : E :=
  coefficients.foldr (fun c acc ↦ acc * point + c) 0

/-- `ring_target(s, f, g)`: `Σ_p f_p (Σ_i z_p^i Ψ(s_i))^(2^(8p))`, `p` from `7` down, `z` squared
eight times before each (`ring_switch.rs:28-38`). -/
def ringTarget (s f g : List E) : E :=
  let images := s.map (ringPsi · g)
  ((List.range ringMapWidth).reverse.foldl (fun (acc : E × E) p ↦
    let z := frobenius8 acc.2 1
    (acc.1 + f.getD p 0 * frobenius8 (hornerEval images z) p, z)) (0, genE)).1

/-- `ring_coefficients(f, g)`: `c_(8p + b) = f_p g_b^(2^(8p))`, block `p` after block `p - 1`
(`ring_switch.rs:40-49`). -/
def ringCoefficients (f g : List E) : List E :=
  (f.foldl (fun (acc : List E × List E) fp ↦
    (acc.1 ++ acc.2.map (fp * ·), acc.2.map (frobenius8 · 1))) ([], g)).1

/-! ## Weighted sums over a list's positions -/

/-- `Σ_j c_j F(j)` over the positions of a list. -/
def idxSum : List E → (ℕ → E) → E
  | [], _ => 0
  | c :: cs, F => c * F 0 + idxSum cs fun k ↦ F (k + 1)

theorem idxSum_append (l₁ l₂ : List E) (F : ℕ → E) :
    idxSum (l₁ ++ l₂) F = idxSum l₁ F + idxSum l₂ fun k ↦ F (l₁.length + k) := by
  induction l₁ generalizing F with
  | nil => simp [idxSum]
  | cons c l ih =>
    simp only [List.cons_append, idxSum, ih, List.length_cons, add_assoc]
    congr 3
    funext k
    congr 1
    omega

theorem idxSum_map_mul (c : E) (l : List E) (F : ℕ → E) :
    idxSum (l.map (c * ·)) F = c * idxSum l F := by
  induction l generalizing F with
  | nil => simp [idxSum]
  | cons a l ih => simp only [List.map_cons, idxSum, ih]; ring

theorem idxSum_ofFn {n : ℕ} (v : Fin n → E) (F : ℕ → E) :
    idxSum (List.ofFn v) F = ∑ b : Fin n, v b * F b := by
  induction n generalizing F with
  | zero => simp [idxSum]
  | succ n ih => rw [List.ofFn_succ, idxSum, ih, Fin.sum_univ_succ]; simp

/-- The positions' sum as a sum over `range`, the shape of `ring_weight`'s unrolled form. -/
theorem idxSum_eq_sum_range (l : List E) (F : ℕ → E) :
    idxSum l F = ∑ k ∈ range l.length, l.getD k 0 * F k := by
  induction l generalizing F with
  | nil => simp [idxSum]
  | cons c l ih =>
    rw [idxSum, ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

/-! ## Squarings -/

private theorem foldl_square (l : List ℕ) (v : E) :
    l.foldl (fun v _ ↦ v * v) v = v ^ 2 ^ l.length := by
  induction l generalizing v with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, List.length_cons, ← sq, ← pow_mul, pow_succ', mul_comm]

/-- `frobenius_8(value, p) = value^(2^(8p))`. -/
theorem frobenius8_eq (v : E) (p : ℕ) : frobenius8 v p = v ^ 2 ^ (8 * p) := by
  rw [frobenius8, foldl_square, List.length_range]
  rfl

/-! ## The inner stage -/

private theorem foldl_psi (g : List E) (a w : E) :
    g.foldl (fun (acc : E × E) gb ↦ (acc.1 + gb * acc.2, acc.2 * acc.2)) (a, w) =
      (a + idxSum g (fun b ↦ w ^ 2 ^ b), w ^ 2 ^ g.length) := by
  induction g generalizing a w with
  | nil => simp [idxSum]
  | cons c g ih =>
    rw [List.foldl_cons, ih, idxSum, List.length_cons]
    have h : ∀ k : ℕ, (w * w) ^ 2 ^ k = w ^ 2 ^ (k + 1) := fun k ↦ by
      rw [← sq, ← pow_mul, pow_succ', mul_comm 2]
    simp only [h, pow_zero, pow_one, Prod.mk.injEq, and_true]
    ring

/-- **The inner stage**: `ring_psi(a, g) = Ψ(a) = Σ_b g_b a^(2^b)`. -/
theorem ringPsi_ofFn {m : ℕ} (a : E) (g : Fin m → E) : ringPsi a (List.ofFn g) = frobPsi g a := by
  rw [ringPsi, foldl_psi, zero_add, idxSum_ofFn, frobPsi]

/-! ## The coefficients -/

/-- The coefficients' weighted sum, block by block: block `p` is `f_p` times the row, the row
raised by `2^8` from one block to the next. -/
def blockSum : List E → List E → (ℕ → E) → E
  | [], _, _ => 0
  | fp :: fl, pw, G => fp * idxSum pw G +
      blockSum fl (pw.map (frobenius8 · 1)) fun k ↦ G (pw.length + k)

private theorem idxSum_foldl_coeff (F : ℕ → E) :
    ∀ (fl acc pw : List E),
      idxSum (fl.foldl (fun (acc : List E × List E) fp ↦
        (acc.1 ++ acc.2.map (fp * ·), acc.2.map (frobenius8 · 1))) (acc, pw)).1 F =
      idxSum acc F + blockSum fl pw fun k ↦ F (acc.length + k)
  | [], acc, pw => by simp [blockSum]
  | fp :: fl, acc, pw => by
    rw [List.foldl_cons]
    dsimp only
    rw [idxSum_foldl_coeff F fl, idxSum_append, idxSum_map_mul, blockSum, List.length_append,
      List.length_map, add_assoc]
    simp only [Nat.add_assoc]

private theorem blockSum_ofFn {m : ℕ} (g : Fin m → E) :
    ∀ (n : ℕ) (f : Fin n → E) (t : ℕ) (G : ℕ → E),
      blockSum (List.ofFn f) (List.ofFn fun b ↦ g b ^ 2 ^ (8 * t)) G =
        ∑ p : Fin n, ∑ b : Fin m, f p * g b ^ 2 ^ (8 * (t + p)) * G (m * p + b)
  | 0, _, _, _ => by simp [blockSum]
  | n + 1, f, t, G => by
    rw [List.ofFn_succ, blockSum, idxSum_ofFn, List.map_ofFn, List.length_ofFn]
    have hrow : ((fun x ↦ frobenius8 x 1) ∘ fun b ↦ g b ^ 2 ^ (8 * t)) =
        fun b ↦ g b ^ 2 ^ (8 * (t + 1)) := by
      funext b
      simp only [Function.comp, frobenius8_eq, ← pow_mul, ← pow_add]
      congr 2
    rw [hrow, blockSum_ofFn g n (fun p ↦ f p.succ) (t + 1), Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Fin.val_zero, add_zero, mul_zero, zero_add, Fin.val_succ]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun b _ ↦ by ring) ?_
    · refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
      rw [show t + 1 + (p : ℕ) = t + ((p : ℕ) + 1) by ring,
        show m + (m * (p : ℕ) + b) = m * ((p : ℕ) + 1) + b by ring]

/-- **The coefficients are `Φ`'s**: `Σ_j c_j F(j) = Σ_{p, b} f_p g_b^(2^(8p)) F(8p + b)`. -/
theorem ringCoefficients_idxSum (f g : Fin 8 → E) (F : ℕ → E) :
    idxSum (ringCoefficients (List.ofFn f) (List.ofFn g)) F =
      ∑ p : Fin 8, ∑ b : Fin 8, f p * g b ^ 2 ^ (8 * (p : ℕ)) * F (8 * p + b) := by
  rw [ringCoefficients, idxSum_foldl_coeff]
  have hg : List.ofFn g = List.ofFn fun b ↦ g b ^ 2 ^ (8 * 0) := by simp
  rw [hg, blockSum_ofFn g 8 f 0]
  simp [idxSum]

/-- The drawn map's coefficients are sixty-four. -/
theorem length_ringCoefficients (f g : Fin 8 → E) :
    (ringCoefficients (List.ofFn f) (List.ofFn g)).length = 64 := by
  have h : ∀ (fl acc pw : List E), (fl.foldl (fun (acc : List E × List E) fp ↦
      (acc.1 ++ acc.2.map (fp * ·), acc.2.map (frobenius8 · 1))) (acc, pw)).1.length =
      acc.length + fl.length * pw.length := by
    intro fl
    induction fl with
    | nil => simp
    | cons fp fl ih =>
      intro acc pw
      rw [List.foldl_cons, ih, List.length_append, List.length_map, List.length_map,
        List.length_cons]
      ring
  rw [ringCoefficients, h]
  simp

/-- **`Φ` is the Frobenius sum with the verifier's coefficients**: `Φ(a) = Σ_k c_k a^(2^k)`. -/
theorem frobPhi_eq_idxSum (f g : Fin 8 → E) (a : E) :
    frobPhi 8 f g a =
      idxSum (ringCoefficients (List.ofFn f) (List.ofFn g)) fun k ↦ a ^ 2 ^ k := by
  rw [ringCoefficients_idxSum, frobPhi_eq_sum]

/-! ## The target -/

theorem hornerEval_cons (c : E) (cs : List E) (z : E) :
    hornerEval (c :: cs) z = hornerEval cs z * z + c := rfl

/-- `poly_eval` is `Σ_i c_i z^i`. -/
theorem hornerEval_ofFn {n : ℕ} (c : Fin n → E) (z : E) :
    hornerEval (List.ofFn c) z = ∑ i : Fin n, c i * z ^ (i : ℕ) := by
  induction n with
  | zero => simp [hornerEval]
  | succ n ih =>
    rw [List.ofFn_succ, hornerEval_cons, ih, Fin.sum_univ_succ, Finset.sum_mul]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    rw [add_comm]
    exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun i _ ↦ by ring)

/-- `x^(2^64) = x` in `E`. -/
theorem genE_pow_two_pow_sixtyFour : genE ^ 2 ^ 64 = genE := by
  change (algebraMap K E g) ^ 2 ^ 64 = algebraMap K E g
  rw [← map_pow, K.pow_two_pow_sixtyFour]

/-- The target's fold, `p` from `k - 1` down to `0`, starting at `z = x^(2^(8(8 - k)))`. -/
private theorem foldl_target (images f : List E) :
    ∀ k ≤ 8, ∀ acc : E,
      ((List.range k).reverse.foldl (fun (acc : E × E) p ↦
        let z := frobenius8 acc.2 1
        (acc.1 + f.getD p 0 * frobenius8 (hornerEval images z) p, z))
        (acc, genE ^ 2 ^ (8 * (8 - k)))).1 =
      acc + ∑ p ∈ range k, f.getD p 0 * hornerEval images (genE ^ 2 ^ (8 * (8 - p))) ^ 2 ^ (8 * p)
  | 0, _, acc => by simp
  | k + 1, hk, acc => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons]
    have hz : frobenius8 (genE ^ 2 ^ (8 * (8 - (k + 1)))) 1 = genE ^ 2 ^ (8 * (8 - k)) := by
      rw [frobenius8_eq, ← pow_mul, ← pow_add]
      congr 2
      omega
    simp only [hz]
    rw [foldl_target images f k (by omega), Finset.sum_range_succ, frobenius8_eq]
    ring

/-- The `p`-th Horner sum raised to `2^(8p)` is `Σ_i x^i Ψ_i^(2^(8p))`. -/
private theorem horner_frob (ψ : Fin 64 → E) {p : ℕ} (hp : p < 8) :
    hornerEval (List.ofFn ψ) (genE ^ 2 ^ (8 * (8 - p))) ^ 2 ^ (8 * p) =
      ∑ i : Fin 64, ringW i * ψ i ^ 2 ^ (8 * p) := by
  rw [hornerEval_ofFn, sum_pow_char_pow]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hexp : 2 ^ (8 * (8 - p)) * ((i : ℕ) * 2 ^ (8 * p)) = 2 ^ 64 * (i : ℕ) := by
    rw [mul_comm (i : ℕ), ← mul_assoc, ← pow_add, show 8 * (8 - p) + 8 * p = 64 by omega]
  rw [mul_pow, ← pow_mul (genE ^ 2 ^ (8 * (8 - p))) (i : ℕ) (2 ^ (8 * p)),
    ← pow_mul genE (2 ^ (8 * (8 - p))) ((i : ℕ) * 2 ^ (8 * p)), hexp, pow_mul genE (2 ^ 64) (i : ℕ),
    genE_pow_two_pow_sixtyFour, mul_comm]
  change _ = algebraMap K E (g ^ (i : ℕ)) * _
  rw [map_pow]
  rfl

/-- **The target is `Σ_i x^i Φ(s_i)`** (§A.6): the verifier's Horner sums at
`z_p = x^(2^(64 - 8p))`. -/
theorem ringTarget_eq (s : Fin 64 → E) (f g : Fin 8 → E) :
    ringTarget (List.ofFn s) (List.ofFn f) (List.ofFn g) =
      ∑ i : Fin 64, ringW i * frobPhi 8 f g (s i) := by
  have h := foldl_target ((List.ofFn s).map (ringPsi · (List.ofFn g))) (List.ofFn f) 8 le_rfl 0
  rw [show 8 * (8 - 8) = 0 from rfl, pow_zero, pow_one] at h
  rw [ringTarget, ringMapWidth, h, zero_add, List.map_ofFn, Finset.sum_range]
  simp only [frobPhi, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have hf : (List.ofFn f).getD p 0 = f p := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [p.isLt]
  rw [horner_frob _ p.isLt, Finset.mul_sum, hf]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Function.comp_apply, ringPsi_ofFn]
  ring

/-! ## The weight -/

/-- `eq(a, b) = Π_n (1 + a_n + b_n)`. -/
def eqP {μ : ℕ} (a b : Fin μ → E) : E := ∏ n, (1 + a n + b n)

/-- The cube point of `u`. -/
def bitV {μ : ℕ} (u : Fin μ → Bool) : Fin μ → E := fun n ↦ if u n then 1 else 0

/-- A point raised coordinatewise to `2^k`. -/
def frobPt {μ : ℕ} (r : Fin μ → E) (k : ℕ) : Fin μ → E := fun n ↦ r n ^ 2 ^ k

private theorem bit_frob (b : Bool) (k : ℕ) : (if b then (1 : E) else 0) ^ 2 ^ k = if b then 1 else 0 := by
  cases b <;> simp

/-- **The Frobenius passes through `eq` at a cube point**: `eq(r, u)^(2^k) = eq(r^(2^k), u)`. -/
theorem eqP_frob {μ : ℕ} (r : Fin μ → E) (u : Fin μ → Bool) (k : ℕ) :
    eqP r (bitV u) ^ 2 ^ k = eqP (frobPt r k) (bitV u) := by
  simp only [eqP, ← Finset.prod_pow, add_pow_char_pow, one_pow, frobPt, bitV, bit_frob]

/-- **The weight on the cube**: `Φ(eq(r, u)) = Σ_k c_k eq(r^(2^k), u)`, what `ring_weight` sums. -/
theorem frobPhi_eqP {μ : ℕ} (f g : Fin 8 → E) (r : Fin μ → E) (u : Fin μ → Bool) :
    frobPhi 8 f g (eqP r (bitV u)) =
      idxSum (ringCoefficients (List.ofFn f) (List.ofFn g)) fun k ↦ eqP (frobPt r k) (bitV u) := by
  rw [frobPhi_eq_idxSum]
  simp only [eqP_frob]

/-- **`eq` is its own multilinear extension**: `Σ_u eq(a, u) eq(u, b) = eq(a, b)`. -/
theorem sum_eqP_mul_eqP {μ : ℕ} (a b : Fin μ → E) :
    ∑ u : Fin μ → Bool, eqP a (bitV u) * eqP (bitV u) b = eqP a b := by
  simp only [eqP, bitV, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun n (x : Bool) ↦
    (1 + a n + if x then 1 else 0) * (1 + (if x then 1 else 0) + b n))]
  refine Finset.prod_congr rfl fun n _ ↦ ?_
  rw [Fintype.sum_bool]
  simp only [↓reduceIte, Bool.false_eq_true, add_zero]
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  linear_combination (a n * b n + a n + b n + 2) * h2

/-- **The ring weight is the extension of `u ↦ Φ(eq(r, u))`**: at `r'` it is
`Σ_k c_k eq(r^(2^k), r')`, what `ring_weight(r, r', c)` computes. -/
theorem ringWeight_mle {μ : ℕ} (f g : Fin 8 → E) (r r' : Fin μ → E) :
    ∑ u : Fin μ → Bool, frobPhi 8 f g (eqP r (bitV u)) * eqP (bitV u) r' =
      idxSum (ringCoefficients (List.ofFn f) (List.ofFn g)) fun k ↦ eqP (frobPt r k) r' := by
  simp only [frobPhi_eqP, idxSum_eq_sum_range, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [mul_assoc, ← Finset.mul_sum, sum_eqP_mul_eqP]

/-! ## Completeness and soundness -/

/-- Bit `i` of a word, in `E`. -/
def bitOf (a : K) (i : Fin 64) : E := if a.toBitVec.getLsbD i then 1 else 0

/-- Slice `i` of a column `q`, extended at `r`: `Q̂_i(r) = Σ_u eq(r, u) Q_i(u)`. -/
def sliceExt {μ : ℕ} (q : (Fin μ → Bool) → K) (r : Fin μ → E) (i : Fin 64) : E :=
  ∑ u : Fin μ → Bool, eqP r (bitV u) * bitOf (q u) i

/-- A word of `K` in `E` is its bits packed by the powers of `x`. -/
theorem ofK_eq_sum_bitOf (a : K) : ofK a = ∑ i : Fin 64, ringW i * bitOf a i := by
  conv_lhs => rw [K.eq_sum_bits a]
  change algebraMap K E _ = _
  rw [map_sum (algebraMap K E)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  unfold ringW bitOf
  split <;> simp

/-- An `F_2`-linear map commutes with a bit. -/
private theorem frobPhi_mul_bit (f g : Fin 8 → E) (e : E) (b : Bool) :
    frobPhi 8 f g (e * if b then 1 else 0) = (if b then 1 else 0) * frobPhi 8 f g e := by
  cases b <;> simp [frobPhi_zero]

/-- **Completeness** (equation `eq:complete`): for a column `q(u) = Σ_i Q_i(u) x^i`,
`Σ_u Φ(eq(r, u)) q(u) = Σ_i x^i Φ(Q̂_i(r))`: the honest opening value is the target at the
honest slice claims. -/
theorem ring_complete {μ : ℕ} (f g : Fin 8 → E) (q : (Fin μ → Bool) → K) (r : Fin μ → E) :
    ∑ u : Fin μ → Bool, frobPhi 8 f g (eqP r (bitV u)) * ofK (q u) =
      ∑ i : Fin 64, ringW i * frobPhi 8 f g (sliceExt q r i) := by
  simp only [ofK_eq_sum_bitOf, Finset.mul_sum, sliceExt, frobPhi_sum, bitOf, frobPhi_mul_bit]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun u _ ↦ by ring

/-- The target at claims `s` against the honest value: the gap is `Σ_i x^i Φ(s_i - ẑ_i)`. -/
theorem ringTarget_sub (s z : Fin 64 → E) (f g : Fin 8 → E) :
    ringTarget (List.ofFn s) (List.ofFn f) (List.ofFn g) -
        ∑ i : Fin 64, ringW i * frobPhi 8 f g (z i) =
      ∑ i : Fin 64, ringW i * frobPhi 8 f g (s i - z i) := by
  rw [ringTarget_eq, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [frobPhi_sub]; ring

/-- **Soundness, counting form** (§A.4): slice claims `s ≠ z` meet the honest value `Σ_i x^i Φ(z_i)`
at no more than `2·|E|^15` of the challenges `(f, g)`. -/
theorem card_ringTarget_bad_le {s z : Fin 64 → E} (h : s ≠ z) :
    Nat.card {fg : (Fin 8 → E) × (Fin 8 → E) //
      ringTarget (List.ofFn s) (List.ofFn fg.1) (List.ofFn fg.2) =
        ∑ i : Fin 64, ringW i * frobPhi 8 fg.1 fg.2 (z i)} ≤ 2 * Nat.card E ^ 15 := by
  have hδ : (fun i ↦ s i - z i) ≠ 0 := fun h0 ↦
    h (funext fun i ↦ sub_eq_zero.mp (congrFun h0 i))
  refine le_trans (Nat.card_mono (Set.toFinite _) fun fg (hfg : _ = _) ↦ ?_)
    (card_ringSwitch_zero_le hδ)
  change ∑ i, ringW i * frobPhi 8 fg.1 fg.2 (s i - z i) = 0
  rw [← ringTarget_sub, hfg, sub_self]

/-- **Soundness** (§A.4): slice claims `s ≠ z` meet the honest value at a fraction `2/|E|` of the
challenges at most. -/
theorem ringTarget_bad_ratio_le {s z : Fin 64 → E} (h : s ≠ z) :
    (Nat.card {fg : (Fin 8 → E) × (Fin 8 → E) //
        ringTarget (List.ofFn s) (List.ofFn fg.1) (List.ofFn fg.2) =
          ∑ i : Fin 64, ringW i * frobPhi 8 fg.1 fg.2 (z i)} : ℝ≥0∞) /
      (Nat.card ((Fin 8 → E) × (Fin 8 → E)) : ℝ≥0∞) ≤ 2 / (Nat.card E : ℝ≥0∞) := by
  have hδ : (fun i ↦ s i - z i) ≠ 0 := fun h0 ↦
    h (funext fun i ↦ sub_eq_zero.mp (congrFun h0 i))
  refine le_trans ?_ (ringSwitch_zero_ratio_le hδ)
  gcongr
  exact Nat.card_mono (Set.toFinite _) fun fg (hfg : _ = _) ↦ by
    change ∑ i, ringW i * frobPhi 8 fg.1 fg.2 (s i - z i) = 0
    rw [← ringTarget_sub, hfg, sub_self]

end
end LeanVM.Protocol.Ring
