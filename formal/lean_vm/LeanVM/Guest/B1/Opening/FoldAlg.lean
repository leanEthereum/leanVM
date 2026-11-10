/-
  LeanVM.Guest.B1.Opening.FoldAlg

  The algebra of a query's fold and of the final check: the Spec's `foldRow` at a point of `E`,
  the guest's fold by `θ + 1/t` with the `t`'s multiplied back once, and `novel_eval`'s tree.
-/

module

public import Statement.LeanVmVerifier
public import LeanVM.Guest.Value.Tower

/-!
# A query's fold, algebraically

`foldRow` (`Statement/LeanVmVerifier.lean`) folds adjacent lanes `(f, g)` to `g + t·(f + θ·g)`,
`t = α + β·x`. The guest (`opening_query`) folds by `r = θ + t⁻¹` instead: `f + r·g` is
`(g + t·(f + θ·g)) / t`, so round `j`'s lanes are the Spec's divided by `Π_(i ≤ j) t_i`, and the
product of the `t`'s times the last lane is the Spec's (`guestFold_eq`).

`novel_eval` folds the coefficients the lowest bit first (`nvPair`, `nvTree`, `novelSum`); the
unnormalized subspace chain is `wsChain`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The Spec's fold at a point of `E` -/

/-- `foldLanes` at a point of `E`. -/
def foldLanesE (x : E) (r : FoldRound) : List E → List E
  | f :: g :: rest => (g + (r.alpha + r.beta * x) * (f + r.theta * g)) :: foldLanesE x r rest
  | _ => []

/-- `foldRow` at a point of `E`. -/
def foldRowE (values : List E) (x : E) (rounds : List FoldRound) : E :=
  (rounds.foldl (fun values round ↦ foldLanesE x round values) values).headD 0

theorem foldLanes_eq (x : K) (r : FoldRound) :
    ∀ l : List E, foldLanes x r l = foldLanesE (ofK x) r l
  | f :: g :: rest => by rw [foldLanes, foldLanesE, foldLanes_eq x r rest]
  | [] => rfl
  | [_] => rfl

theorem foldRow_eq (values : List E) (x : K) (rounds : List FoldRound) :
    foldRow values x rounds = foldRowE values (ofK x) rounds := by
  simp only [foldRow, foldRowE, foldLanes_eq]

theorem length_foldLanesE (x : E) (r : FoldRound) :
    ∀ l : List E, (foldLanesE x r l).length = l.length / 2
  | f :: g :: rest => by
    rw [foldLanesE, List.length_cons, length_foldLanesE x r rest]
    simp only [List.length_cons]
    omega
  | [] => rfl
  | [_] => by simp [foldLanesE]

theorem getD_foldLanesE (x : E) (r : FoldRound) :
    ∀ (l : List E) (m : ℕ), 2 * m + 1 < l.length →
      (foldLanesE x r l).getD m 0 =
        l.getD (2 * m + 1) 0 + (r.alpha + r.beta * x) * (l.getD (2 * m) 0 + r.theta * l.getD (2 * m + 1) 0)
  | f :: g :: rest, 0, _ => by simp [foldLanesE]
  | f :: g :: rest, m + 1, h => by
    rw [foldLanesE, List.getD_cons_succ, getD_foldLanesE x r rest m (by simp at h; omega)]
    simp only [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, List.getD_cons_succ]
  | [], _, h => by simp at h
  | [_], _, h => by simp at h

/-- The lanes after the first `j` rounds. -/
def lanesAt (x : E) (rounds : List FoldRound) (l : List E) (j : ℕ) : List E :=
  (rounds.take j).foldl (fun values round ↦ foldLanesE x round values) l

theorem lanesAt_succ (x : E) (rounds : List FoldRound) (l : List E) {j : ℕ} (hj : j < rounds.length) :
    lanesAt x rounds l (j + 1) = foldLanesE x (rounds.getD j ⟨0, 0, 0⟩) (lanesAt x rounds l j) := by
  rw [lanesAt, lanesAt, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
    List.foldl_append, List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj, Option.getD_some]

theorem length_lanesAt (x : E) (rounds : List FoldRound) (l : List E) {n : ℕ}
    (hl : l.length = 2 ^ n) : ∀ j ≤ rounds.length, (lanesAt x rounds l j).length = 2 ^ n / 2 ^ j
  | 0, _ => by simp [lanesAt, hl]
  | j + 1, hj => by
    rw [lanesAt_succ x rounds l (by omega), length_foldLanesE, length_lanesAt x rounds l hl j (by omega),
      Nat.div_div_eq_div_mul, pow_succ]

theorem foldRowE_eq_lanesAt (values : List E) (x : E) (rounds : List FoldRound) :
    foldRowE values x rounds = (lanesAt x rounds values rounds.length).headD 0 := by
  rw [foldRowE, lanesAt, List.take_length]

/-! ## The guest's fold -/

/-- One guest round's outputs: `f + (θ + t⁻¹)·g` is the Spec's output over `t`. -/
theorem guest_lane {t f g θ α β x : E} (ht : t = α + β * x) (h0 : t ≠ 0) :
    t * (f + (θ + t⁻¹) * g) = g + (α + β * x) * (f + θ * g) := by
  rw [← ht]
  have h : t * (θ + t⁻¹) = t * θ + 1 := by rw [mul_add, mul_inv_cancel₀ h0]
  rw [mul_add, ← mul_assoc, h]
  ring

/-- **The guest's fold** of `2^n` lanes over `n ≥ 1` rounds: round `j`'s outputs `acc j m`
(`m < 2^(n - 1 - j)`) fold the previous round's (the lanes at `j = 0`) by `r j = θ_j + t_j⁻¹`,
`t_j = α_j + β_j·x ≠ 0`, and `scale j` is `Π_(i ≤ j) t_i`; then `scale j · acc j m` is lane `m`
after `j + 1` Spec rounds, and `scale (n - 1) · acc (n - 1) 0` is `foldRowE`. -/
theorem guestFold_eq {x : E} {rounds : List FoldRound} {n : ℕ} (hn : rounds.length = n)
    {lanes : List E} (hl : lanes.length = 2 ^ n) {acc : ℕ → ℕ → E} {scale ts rs : ℕ → E}
    (ht : ∀ j < n, ts j = (rounds.getD j ⟨0, 0, 0⟩).alpha + (rounds.getD j ⟨0, 0, 0⟩).beta * x)
    (h0 : ∀ j < n, ts j ≠ 0) (hr : ∀ j < n, rs j = (rounds.getD j ⟨0, 0, 0⟩).theta + (ts j)⁻¹)
    (hs0 : scale 0 = ts 0) (hs : ∀ j, j + 1 < n → scale (j + 1) = scale j * ts (j + 1))
    (ha0 : ∀ m < 2 ^ (n - 1), acc 0 m = lanes.getD (2 * m) 0 + rs 0 * lanes.getD (2 * m + 1) 0)
    (ha : ∀ j, j + 1 < n → ∀ m < 2 ^ (n - 2 - j),
      acc (j + 1) m = acc j (2 * m) + rs (j + 1) * acc j (2 * m + 1)) :
    ∀ j < n, ∀ m < 2 ^ (n - 1 - j), scale j * acc j m = (lanesAt x rounds lanes (j + 1)).getD m 0 := by
  have hlen : ∀ j ≤ n, (lanesAt x rounds lanes j).length = 2 ^ (n - j) := fun j hj ↦ by
    rw [length_lanesAt x rounds lanes hl j (by omega), Nat.pow_div hj (by decide)]
  intro j
  induction j with
  | zero =>
    intro hj m hm
    have hL := hlen 0 (by omega)
    simp only [Nat.sub_zero] at hm hL
    have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
    rw [lanesAt_succ x rounds lanes (by omega), getD_foldLanesE _ _ _ _ (by rw [hL]; omega),
      hs0, ha0 m hm, hr 0 hj]
    simp only [lanesAt, List.take_zero, List.foldl_nil]
    exact guest_lane (ht 0 hj) (h0 0 hj)
  | succ j ih =>
    intro hj m hm
    have hL := hlen (j + 1) (by omega)
    have e1 : n - (j + 1) = n - 1 - j := by omega
    have e2 : n - 2 - j = n - 1 - (j + 1) := by omega
    have h2 : 2 ^ (n - 1 - j) = 2 * 2 ^ (n - 1 - (j + 1)) := by rw [← pow_succ']; congr 1; omega
    have hm2 : 2 * m + 1 < 2 ^ (n - 1 - j) := by omega
    rw [lanesAt_succ x rounds lanes (by omega), getD_foldLanesE _ _ _ _ (by rw [hL, e1]; exact hm2),
      hs j hj, ha j hj m (by rw [e2]; exact hm), ← ih (by omega) (2 * m) (by omega),
      ← ih (by omega) (2 * m + 1) hm2, hr (j + 1) hj]
    have key := guest_lane (f := scale j * acc j (2 * m)) (g := scale j * acc j (2 * m + 1))
      (θ := (rounds.getD (j + 1) ⟨0, 0, 0⟩).theta) (ht (j + 1) hj) (h0 (j + 1) hj)
    rw [← key]
    ring

/-- The guest's fold's value is `foldRowE`. -/
theorem guestFold_value {x : E} {rounds : List FoldRound} {n : ℕ} (hn : rounds.length = n)
    (h1 : 1 ≤ n) {lanes : List E} (hl : lanes.length = 2 ^ n) {acc : ℕ → ℕ → E} {scale ts rs : ℕ → E}
    (ht : ∀ j < n, ts j = (rounds.getD j ⟨0, 0, 0⟩).alpha + (rounds.getD j ⟨0, 0, 0⟩).beta * x)
    (h0 : ∀ j < n, ts j ≠ 0) (hr : ∀ j < n, rs j = (rounds.getD j ⟨0, 0, 0⟩).theta + (ts j)⁻¹)
    (hs0 : scale 0 = ts 0) (hs : ∀ j, j + 1 < n → scale (j + 1) = scale j * ts (j + 1))
    (ha0 : ∀ m < 2 ^ (n - 1), acc 0 m = lanes.getD (2 * m) 0 + rs 0 * lanes.getD (2 * m + 1) 0)
    (ha : ∀ j, j + 1 < n → ∀ m < 2 ^ (n - 2 - j),
      acc (j + 1) m = acc j (2 * m) + rs (j + 1) * acc j (2 * m + 1)) :
    scale (n - 1) * acc (n - 1) 0 = foldRowE lanes x rounds := by
  rw [guestFold_eq hn hl ht h0 hr hs0 hs ha0 ha (n - 1) (by omega) 0 (by positivity),
    foldRowE_eq_lanesAt, hn, Nat.sub_add_cancel h1, List.headD_eq_getD]

/-! ## `novel_eval` -/

/-- One level of `novel_eval`: the pairs `lo + w·hi`, an odd last value kept. -/
def nvPair (w : E) : List E → List E
  | lo :: hi :: rest => (lo + w * hi) :: nvPair w rest
  | l => l

/-- Levels `i .. i + c` of `novel_eval`, level `i` folding by `ws i`. -/
def nvTree (ws : ℕ → E) : ℕ → ℕ → List E → List E
  | 0, _, l => l
  | c + 1, i, l => nvTree ws c (i + 1) (nvPair (ws i) l)

/-- **`novel_eval(hs, ws, n, nbits)`**: the first `n` coefficients folded the lowest bit first,
`nbits` levels, level `i` by `ws i`: `Σ_(c < n) hs_c Π_(i < nbits, c_i = 1) ws_i` for
`n ≤ 2^nbits`. -/
def novelSum (hs : List E) (ws : ℕ → E) (n nbits : ℕ) : E :=
  (nvTree ws nbits 0 (hs.take n)).headD 0

/-- The guest's unnormalized subspace chain at `x` (`opening_query`'s `ws`): `W_0 = x`,
`W_(i+1) = W_i·(W_i + vs_i)`. -/
def wsChain (vs : List K) (x : E) : ℕ → E
  | 0 => x
  | i + 1 => wsChain vs x i * (wsChain vs x i + ofK (vs.getD i 0))

end
end LeanVM.Guest.B1
