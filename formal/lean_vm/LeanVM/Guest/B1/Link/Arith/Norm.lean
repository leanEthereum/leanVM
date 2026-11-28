/-
  LeanVM.Guest.B1.Link.Arith.Norm

  Expressions over named variables in `E`, a normal form the kernel computes (a sorted list of
  monomials with word coefficients), and its soundness: expressions with equal normal forms are
  equal at every valuation.
-/

module

public import LeanVM.Guest.B1.Link.Arith
public import LeanVM.Guest.Value.Tower
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# A normalizer for the link's arithmetic

`Ex`: variables `v i`, constants `c x` of `E`, sums and products; `Ex.eval ρ` its value at the
valuation `ρ`. It is an `LOps`, so the generic definitions of `LeanVM.Guest.B1.Link.Arith` build
`Ex` terms.

`Ex.norm`: a polynomial, a list of monomials (sorted lists of variables) with nonzero
coefficients (the two limbs of a word, `limbsOf`), sorted by the lexicographic order on sorted
variable lists in which a list comes before its prefixes (`mcmp`; the order of exponent vectors,
so multiplying by a monomial keeps a polynomial sorted). Sums merge (`padd`), products
distribute (`pmul`), coefficients add by `XOR` and multiply in `E`, read back by `limbsOf`.

`eval_eq_of_norm`: equal normal forms give equal values. Soundness does not rest on the order:
any merge is sound; the order only makes equal polynomials' normal forms equal, which the
kernel then checks by `decide +kernel`.
-/

namespace LeanVM.Guest.B1.Link.Arith

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Value

@[expose] public section

/-! ## Expressions -/

/-- An expression over variables `v i` and the field's constants. -/
inductive Ex where
  | v (i : ℕ)
  | c (x : E)
  | add (x y : Ex)
  | mul (x y : Ex)
  deriving Inhabited

/-- The value of an expression at a valuation. -/
def Ex.eval (ρ : ℕ → E) : Ex → E
  | .v i => ρ i
  | .c x => x
  | .add x y => x.eval ρ + y.eval ρ
  | .mul x y => x.eval ρ * y.eval ρ

instance : LOps Ex where
  add := .add
  mul := .mul
  zero := .c 0
  one := .c 1
  ofE := .c

/-! ## Coefficients -/

/-- A coefficient: the two limbs of a word. -/
abbrev Cf := ℕ × ℕ

/-- The word a coefficient spells. -/
def cw (c : Cf) : E := word c.1 c.2

/-- A constant's coefficient. -/
def cOf (x : E) : Cf := limbsOf x

/-- Coefficients add limb by limb. -/
def cAdd (a b : Cf) : Cf := (a.1 ^^^ b.1, a.2 ^^^ b.2)

/-- Coefficients multiply in `E`, `1` passed through. -/
def cMul (a b : Cf) : Cf :=
  if a = (1, 0) then b else if b = (1, 0) then a else cOf (cw a * cw b)

theorem cw_cOf (x : E) : cw (cOf x) = x := by
  simp only [cw, cOf, limbsOf, word, K.ofBits_toNat]
  exact ofLimbs_limb x

theorem cw_zero : cw (0, 0) = 0 := by
  simp only [cw, word, K.ofBits_zero]
  exact zero_eq_ofLimbs.symm

theorem cw_one : cw (1, 0) = 1 := by
  simp only [cw, word, K.ofBits_zero, K.ofBits_one]
  exact one_eq_ofLimbs.symm

theorem cw_cAdd (a b : Cf) : cw (cAdd a b) = cw a + cw b := by
  simp only [cw, cAdd, word, ofLimbs_add, K.ofBits_xor]

theorem cw_cMul (a b : Cf) : cw (cMul a b) = cw a * cw b := by
  unfold cMul
  split_ifs with ha hb
  · rw [ha, cw_one, one_mul]
  · rw [hb, cw_one, mul_one]
  · exact cw_cOf _

/-! ## Monomials -/

/-- Merge two sorted lists of variables, by recursion on the first (the second's recursion is
`mmergeAux`'s, the first's tail merged by `rec`). -/
def mmergeAux (a : ℕ) (as : List ℕ) (rec : List ℕ → List ℕ) : List ℕ → List ℕ
  | [] => a :: as
  | b :: bs => if a ≤ b then a :: rec (b :: bs) else b :: mmergeAux a as rec bs

def mmerge : List ℕ → List ℕ → List ℕ
  | [], l => l
  | a :: as, l => mmergeAux a as (mmerge as) l

/-- The order of monomials: lexicographic on the sorted lists, a list before its prefixes. -/
def mcmp : List ℕ → List ℕ → Ordering
  | [], [] => .eq
  | [], _ :: _ => .gt
  | _ :: _, [] => .lt
  | a :: as, b :: bs => if a < b then .lt else if b < a then .gt else mcmp as bs

theorem mcmp_eq : ∀ {a b : List ℕ}, mcmp a b = .eq → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [mcmp] at h
  | _ :: _, [], h => by simp [mcmp] at h
  | a :: as, b :: bs, h => by
    unfold mcmp at h
    split_ifs at h with h1 h2
    rw [mcmp_eq h, show a = b by omega]

/-- A monomial's value. -/
def mEval (ρ : ℕ → E) : List ℕ → E
  | [] => 1
  | i :: m => ρ i * mEval ρ m

theorem mEval_mmergeAux (ρ : ℕ → E) (a : ℕ) (as : List ℕ) (rec : List ℕ → List ℕ)
    (hrec : ∀ l, mEval ρ (rec l) = mEval ρ as * mEval ρ l) :
    ∀ l, mEval ρ (mmergeAux a as rec l) = ρ a * mEval ρ as * mEval ρ l
  | [] => by simp [mmergeAux, mEval]
  | b :: bs => by
    unfold mmergeAux
    split_ifs
    · rw [mEval, hrec]; ring
    · rw [mEval, mEval_mmergeAux ρ a as rec hrec bs, mEval]; ring

theorem mEval_mmerge (ρ : ℕ → E) : ∀ a b, mEval ρ (mmerge a b) = mEval ρ a * mEval ρ b
  | [], l => by simp [mmerge, mEval]
  | a :: as, l => by
    rw [mmerge, mEval_mmergeAux ρ a as _ (mEval_mmerge ρ as), mEval]

/-! ## Polynomials -/

/-- A polynomial: monomials with their coefficients. -/
abbrev Poly := List (List ℕ × Cf)

/-- A polynomial's value. -/
def pEval (ρ : ℕ → E) : Poly → E
  | [] => 0
  | (m, c) :: p => cw c * mEval ρ m + pEval ρ p

/-- The sum of two sorted polynomials, merged, like terms' coefficients added and dropped at
zero. -/
def paddAux (x : List ℕ × Cf) (p : Poly) (rec : Poly → Poly) : Poly → Poly
  | [] => x :: p
  | y :: q =>
    match mcmp x.1 y.1 with
    | .lt => x :: rec (y :: q)
    | .gt => y :: paddAux x p rec q
    | .eq => if cAdd x.2 y.2 = (0, 0) then rec q else (x.1, cAdd x.2 y.2) :: rec q

def padd : Poly → Poly → Poly
  | [], q => q
  | x :: p, q => paddAux x p (padd p) q

/-- A polynomial times a monomial. -/
def pscale (m : List ℕ) (c : Cf) (q : Poly) : Poly :=
  q.map fun mc ↦ (mmerge m mc.1, cMul c mc.2)

/-- The product of two polynomials. -/
def pmul (p q : Poly) : Poly := p.foldr (fun mc acc ↦ padd (pscale mc.1 mc.2 q) acc) []

/-- The normal form of an expression. -/
def Ex.norm : Ex → Poly
  | .v i => [([i], (1, 0))]
  | .c x => if cOf x = (0, 0) then [] else [([], cOf x)]
  | .add x y => padd x.norm y.norm
  | .mul x y => pmul x.norm y.norm

theorem pEval_paddAux (ρ : ℕ → E) (x : List ℕ × Cf) (p : Poly) (rec : Poly → Poly)
    (hrec : ∀ q, pEval ρ (rec q) = pEval ρ p + pEval ρ q) :
    ∀ q, pEval ρ (paddAux x p rec q) = pEval ρ (x :: p) + pEval ρ q
  | [] => by obtain ⟨m, c⟩ := x; simp [paddAux, pEval]
  | y :: q => by
    obtain ⟨m, c⟩ := x
    obtain ⟨m', c'⟩ := y
    unfold paddAux
    dsimp only
    split
    · rw [pEval, hrec]; simp only [pEval]; ring
    · rw [pEval, pEval_paddAux ρ (m, c) p rec hrec q]; simp only [pEval]; ring
    · rename_i h
      obtain rfl := mcmp_eq h
      split_ifs with hz
      · have h0 : cw c + cw c' = 0 := by rw [← cw_cAdd, hz, cw_zero]
        rw [hrec]; simp only [pEval]
        linear_combination (-mEval ρ m) * h0
      · rw [pEval, hrec, cw_cAdd]; simp only [pEval]; ring

theorem pEval_padd (ρ : ℕ → E) : ∀ p q, pEval ρ (padd p q) = pEval ρ p + pEval ρ q
  | [], q => by simp [padd, pEval]
  | x :: p, q => by rw [padd, pEval_paddAux ρ x p _ (pEval_padd ρ p)]

theorem pEval_pscale (ρ : ℕ → E) (m : List ℕ) (c : Cf) :
    ∀ q, pEval ρ (pscale m c q) = cw c * mEval ρ m * pEval ρ q
  | [] => by simp [pscale, pEval]
  | (m', c') :: q => by
    have ih := pEval_pscale ρ m c q
    simp only [pscale, List.map_cons] at ih ⊢
    rw [pEval, ih, cw_cMul, mEval_mmerge, pEval]
    ring

theorem pEval_pmul (ρ : ℕ → E) (q : Poly) : ∀ p, pEval ρ (pmul p q) = pEval ρ p * pEval ρ q
  | [] => by simp [pmul, pEval]
  | (m, c) :: p => by
    have ih := pEval_pmul ρ q p
    simp only [pmul, List.foldr_cons] at ih ⊢
    rw [pEval_padd, pEval_pscale, ih, pEval]
    ring

/-- **The normal form's value is the expression's.** -/
theorem pEval_norm (ρ : ℕ → E) : ∀ e : Ex, pEval ρ e.norm = e.eval ρ
  | .v i => by simp [Ex.norm, pEval, mEval, cw_one, Ex.eval]
  | .c x => by
    unfold Ex.norm
    split_ifs with h
    · rw [pEval, Ex.eval, ← cw_cOf x, h, cw_zero]
    · simp only [pEval, mEval, mul_one, add_zero, Ex.eval]
      exact cw_cOf x
  | .add x y => by rw [Ex.norm, pEval_padd, pEval_norm ρ x, pEval_norm ρ y, Ex.eval]
  | .mul x y => by rw [Ex.norm, pEval_pmul, pEval_norm ρ x, pEval_norm ρ y, Ex.eval]

/-- **Equal normal forms, equal values.** -/
theorem eval_eq_of_norm {a b : Ex} (h : a.norm = b.norm) (ρ : ℕ → E) : a.eval ρ = b.eval ρ := by
  rw [← pEval_norm ρ a, ← pEval_norm ρ b, h]

end

end LeanVM.Guest.B1.Link.Arith
