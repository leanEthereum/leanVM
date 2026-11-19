module

public import Statement.LeanVmVerifier

/-!
# Ring switching's arithmetic in the order the code computes it

The statement's functions (`ringCoefficients`, `ringWeight`, `eqEval` of a stack point) restated as
the code's loops compute them: `ringCoefficients_getD` gives each coefficient `f_p · g_b^(2^(8p))`
by its index, `ringWeight_eq` folds `c_k · eqEval V r'` over the coefficients with `V` squared
between them, `eqEval_take_drop` splits an equality weight at any coordinate and
`eqEval_append_selector` evaluates a point followed by a selector's bits in two runs, each of the
right length.
-/

@[expose] public section

namespace NativeVm.Code.Ring

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-! ## `eqEval` -/

theorem eqEval_nil_left (b : List E) : eqEval [] b = 1 := by simp [eqEval]

theorem eqEval_nil_right (a : List E) : eqEval a [] = 1 := by simp [eqEval]

theorem foldl_mul_one (L : List E) (a : E) : L.foldl (· * ·) a = a * L.foldl (· * ·) 1 := by
  induction L generalizing a with
  | nil => simp
  | cons x L ih => rw [List.foldl_cons, List.foldl_cons, ih, ih (1 * x), one_mul, mul_assoc]

theorem eqEval_cons' (x y : E) (xs ys : List E) :
    eqEval (x :: xs) (y :: ys) = (1 + x + y) * eqEval xs ys := by
  rw [eqEval, eqEval, List.zipWith_cons_cons, List.foldl_cons, foldl_mul_one, one_mul]

/-- **An equality weight splits at any coordinate.** -/
theorem eqEval_take_drop (k : Nat) : ∀ a b : List E,
    eqEval a b = eqEval (a.take k) (b.take k) * eqEval (a.drop k) (b.drop k) := by
  induction k with
  | zero => intro a b; simp [eqEval_nil_left]
  | succ k ih =>
    intro a b
    rcases a with _ | ⟨x, a⟩
    · simp [eqEval_nil_left]
    rcases b with _ | ⟨y, b⟩
    · simp [eqEval_nil_right]
    rw [List.take_succ_cons, List.take_succ_cons, List.drop_succ_cons, List.drop_succ_cons,
      eqEval_cons', eqEval_cons', ih a b, mul_assoc]

/-- An equality weight only reads the common length. -/
theorem eqEval_take_min (a b : List E) {k : Nat} (hk : a.length ≤ k ∨ b.length ≤ k) :
    eqEval a b = eqEval (a.take k) (b.take k) := by
  rw [eqEval_take_drop k a b]
  rcases hk with h | h
  · rw [List.drop_eq_nil_of_le h, eqEval_nil_left, mul_one]
  · rw [List.drop_eq_nil_of_le (as := b) h, eqEval_nil_right, mul_one]

/-! ## Selector points -/

theorem selectorPoint_length (sel n : Nat) : (selectorPoint sel n).length = n := by
  simp [selectorPoint]

theorem selectorPoint_zero (sel : Nat) : selectorPoint sel 0 = [] := rfl

theorem selectorPoint_succ (sel n : Nat) :
    selectorPoint sel (n + 1) = eOfNat (sel % 2) :: selectorPoint (sel / 2) n := by
  simp only [selectorPoint, List.range_succ_eq_map, List.map_cons, List.map_map,
    Nat.shiftRight_zero, List.cons.injEq, true_and]
  refine List.map_congr_left fun i _ ↦ ?_
  simp only [Function.comp_apply]
  rw [Nat.succ_eq_add_one, show i + 1 = 1 + i by omega, Nat.shiftRight_add, Nat.shiftRight_one]

theorem selectorPoint_take (sel n k : Nat) (h : k ≤ n) :
    (selectorPoint sel n).take k = selectorPoint sel k := by
  simp only [selectorPoint, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-- **A point followed by a selector's bits**, as the code evaluates it: the point's run, then the
selector's, each cut to what the other side has. -/
theorem eqEval_append_selector (pt x : List E) (sel len : Nat) :
    eqEval (pt ++ selectorPoint sel len) x =
      eqEval (pt.take (min pt.length x.length)) (x.take (min pt.length x.length)) *
        eqEval (selectorPoint sel (min len (x.length - min pt.length x.length)))
          ((x.drop (min pt.length x.length)).take (min len (x.length - min pt.length x.length))) := by
  set n1 := min pt.length x.length with hn1
  set n2 := min len (x.length - n1) with hn2
  rw [eqEval_take_drop n1, List.take_append_of_le_length (by omega),
    List.drop_append_of_le_length (by omega)]
  congr 1
  rcases Nat.le_total pt.length x.length with h | h
  · rw [List.drop_eq_nil_of_le (show pt.length ≤ n1 by omega), List.nil_append,
      eqEval_take_min _ _ (k := n2) (by
        rw [selectorPoint_length, List.length_drop]; omega),
      selectorPoint_take _ _ _ (by omega)]
  · have hx : x.drop n1 = [] := List.drop_eq_nil_of_le (by omega)
    rw [hx, eqEval_nil_right, List.take_nil, eqEval_nil_right]

/-! ## `ringWeight` -/

/-- The product of `ringWeight`'s inner loop is `c · eqEval V r'`. -/
theorem zip_foldl_eq : ∀ (V rP : List E) (c : E),
    (List.zip V rP).foldl (fun product (p : E × E) ↦ product * (1 + p.1 + p.2)) c =
      c * eqEval V rP
  | [], _, c => by simp [eqEval_nil_left]
  | _ :: _, [], c => by simp [eqEval_nil_right]
  | v :: V, r :: rP, c => by
    rw [List.zip_cons_cons, List.foldl_cons, zip_foldl_eq V rP, eqEval_cons', mul_assoc]

/-- One coefficient of `ringWeight`: its product added, the point squared. -/
def rwStep (rP : List E) (acc : E × List E) (c : E) : E × List E :=
  (acc.1 + c * eqEval acc.2 rP, acc.2.map fun v ↦ v * v)

/-- **`ringWeight`** as the code folds it. -/
theorem ringWeight_eq (r rP c : List E) : ringWeight r rP c = (c.foldl (rwStep rP) (0, r)).1 := by
  unfold ringWeight rwStep
  congr 2
  funext acc ck
  rw [← zip_foldl_eq]

theorem rwStep_foldl_length (rP : List E) : ∀ (c : List E) (acc : E × List E),
    (c.foldl (rwStep rP) acc).2.length = acc.2.length
  | [], _ => rfl
  | ck :: c, acc => by
    rw [List.foldl_cons, rwStep_foldl_length rP c]
    simp [rwStep]

/-! ## `ringCoefficients` -/

theorem ringCoefficients_foldl (f : List E) : ∀ (acc G : List E),
    (f.foldl (fun (acc : List E × List E) fP ↦
      (acc.1 ++ acc.2.map (fP * ·), acc.2.map (frobenius8 · 1))) (acc, G)).1 =
      acc ++ ringCoefficients f G := by
  induction f with
  | nil => intro acc G; simp [ringCoefficients]
  | cons a f ih =>
    intro acc G
    unfold ringCoefficients
    rw [List.foldl_cons, List.foldl_cons, ih, ih, List.nil_append, List.append_assoc]

theorem ringCoefficients_cons (a : E) (f g : List E) :
    ringCoefficients (a :: f) g =
      g.map (a * ·) ++ ringCoefficients f (g.map (frobenius8 · 1)) := by
  conv_lhs => unfold ringCoefficients
  rw [List.foldl_cons, ringCoefficients_foldl, List.nil_append]

theorem ringCoefficients_length : ∀ (f g : List E),
    (ringCoefficients f g).length = f.length * g.length
  | [], g => by simp [ringCoefficients]
  | a :: f, g => by
    rw [ringCoefficients_cons, List.length_append, ringCoefficients_length, List.length_map,
      List.length_map, List.length_cons]
    ring

theorem frobenius8_zero (x : E) : frobenius8 x 0 = x := by simp [frobenius8]

theorem frobenius8_succ (x : E) (p : Nat) :
    frobenius8 (frobenius8 x 1) p = frobenius8 x (p + 1) := by
  simp only [frobenius8, ← pow_mul, ← pow_add, ringMapWidth]
  congr 2
  ring

/-- **Coefficient `p · |g| + b`** is `f_p · g_b^(2^(8p))`. -/
theorem ringCoefficients_getD : ∀ (f g : List E) (p b : Nat), p < f.length → b < g.length →
    (ringCoefficients f g).getD (p * g.length + b) 0 = f.getD p 0 * frobenius8 (g.getD b 0) p
  | [], _, _, _, hp, _ => absurd hp (Nat.not_lt_zero _)
  | a :: f, g, 0, b, _, hb => by
    rw [ringCoefficients_cons]
    simp only [List.getD_eq_getElem?_getD, Nat.zero_mul, Nat.zero_add,
      List.getElem?_append_left (show b < (g.map (a * ·)).length by simpa),
      List.getElem?_map, List.getElem?_eq_getElem hb, Option.map_some, Option.getD_some,
      List.getElem?_cons_zero, frobenius8_zero]
  | a :: f, g, p + 1, b, hp, hb => by
    have h := ringCoefficients_getD f (g.map (frobenius8 · 1)) p b (by simpa using hp)
      (by simpa using hb)
    rw [List.length_map] at h
    rw [ringCoefficients_cons, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp; nlinarith), List.length_map,
      show (p + 1) * g.length + b - g.length = p * g.length + b by rw [Nat.succ_mul]; omega,
      ← List.getD_eq_getElem?_getD, h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_map,
      List.getElem?_eq_getElem hb, Option.map_some, Option.getD_some, frobenius8_succ]


theorem map_frobenius8_succ (g : List E) (n : Nat) :
    (g.map (frobenius8 · 1)).map (frobenius8 · n) = g.map (frobenius8 · (n + 1)) := by
  simp [Function.comp_def, frobenius8_succ]

/-- **One more challenge `f_p`** appends its eight coefficients. -/
theorem ringCoefficients_snoc (a : E) : ∀ (f g : List E),
    ringCoefficients (f ++ [a]) g =
      ringCoefficients f g ++ (g.map (frobenius8 · f.length)).map (· * a)
  | [], g => by
    rw [List.nil_append, ringCoefficients_cons]
    simp [ringCoefficients, frobenius8_zero, mul_comm]
  | b :: f, g => by
    rw [List.cons_append, ringCoefficients_cons, ringCoefficients_cons, ringCoefficients_snoc a f,
      map_frobenius8_succ, List.append_assoc, List.length_cons]

/-! ## Folds over indices -/

theorem map_getD_range (l : List E) : (List.range l.length).map (l.getD · 0) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

end NativeVm.Code.Ring
