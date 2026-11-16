/-
  LeanVM.Guest.Backend.Guest.Cpl.Eval.Places

  The places conjunct of the per-function completeness test (`Cpl.placesOk`) decided by parts for
  the largest functions: the codes by chunks of the row, the core function's values by runs of
  top-level statements and of a `match`'s arms.
-/

module

public import LeanVM.Guest.Backend.Guest.Cpl.Eval.Split

/-!
# The places by parts

`Cpl.placesOk f locs row` is three tests: the places' keys (`keysNumbered`), the code of each value
below the row (`codesFrom`), and the values the core function `f` names (`valsBelow`). For a large
function the codes are decided by chunks of the row (`codesFrom_part`, `codesFrom_end`) and the
values by runs of top-level statements (`all_part`, `all_end` with `valsList_append`), a large
`match` by runs of its arms (`vals_match`, `valsArms_part`, `valsArms_end`); `places_big` puts
them together.
-/

namespace LeanVM.Guest.Backend.CplEval

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Backend LeanVM.Guest.Backend.Cpl GuestPiece Complete

@[expose] public section

/-- Value `v` is `⟨[], 0, k⟩` with `k < n`. -/
def valBelow (n : ℕ) (v : V) : Bool := v.path.isEmpty && v.tag == 0 && Nat.blt v.idx n

theorem valsList_append : ∀ a b : List Stmt,
    Stmt.valsList (a ++ b) = Stmt.valsList a ++ Stmt.valsList b
  | [], _ => rfl
  | s :: a, b => by rw [List.cons_append, Stmt.valsList, Stmt.valsList, valsList_append a b, List.append_assoc]

theorem valsArms_append : ∀ a b : List (List Stmt),
    Stmt.valsArms (a ++ b) = Stmt.valsArms a ++ Stmt.valsArms b
  | [], _ => rfl
  | s :: a, b => by rw [List.cons_append, Stmt.valsArms, Stmt.valsArms, valsArms_append a b, List.append_assoc]

theorem codesFrom_append {locs : VMap Loc} : ∀ (k : ℕ) (a b : List ℕ),
    codesFrom locs k (a ++ b) = (codesFrom locs k a && codesFrom locs (k + a.length) b)
  | _, [], _ => by simp [codesFrom]
  | k, c :: a, b => by
    rw [List.cons_append, codesFrom, codesFrom, codesFrom_append (k + 1) a b, List.length_cons,
      show k + 1 + a.length = k + (a.length + 1) by omega, Bool.and_assoc]

/-- **The codes from value `a` on, by a chunk of `m` and the rest.** -/
theorem codesFrom_part {locs : VMap Loc} {row : List ℕ} {a m : ℕ}
    (h₁ : codesFrom locs a ((row.drop a).take m) = true)
    (h₂ : codesFrom locs (a + m) (row.drop (a + m)) = true) : codesFrom locs a (row.drop a) = true := by
  by_cases hm : m ≤ (row.drop a).length
  · rw [← List.take_append_drop m (row.drop a), codesFrom_append, h₁, List.length_take,
      Nat.min_eq_left hm, drop_drop', h₂]
    rfl
  · rw [List.take_of_length_le (by omega)] at h₁
    exact h₁

theorem codesFrom_end {locs : VMap Loc} {row : List ℕ} {k : ℕ} (hk : row.length ≤ k) :
    codesFrom locs k (row.drop k) = true := by
  rw [List.drop_eq_nil_of_le hk]
  rfl

theorem valsArms_part {p : V → Bool} {A : List (List Stmt)} {a m : ℕ}
    (h₁ : (Stmt.valsArms ((A.drop a).take m)).all p = true)
    (h₂ : (Stmt.valsArms (A.drop (a + m))).all p = true) : (Stmt.valsArms (A.drop a)).all p = true := by
  rw [← List.take_append_drop m (A.drop a), valsArms_append, List.all_append, h₁, drop_drop', h₂]
  rfl

theorem valsArms_end {p : V → Bool} {A : List (List Stmt)} {k : ℕ} (hk : A.length ≤ k) :
    (Stmt.valsArms (A.drop k)).all p = true := by
  rw [List.drop_eq_nil_of_le hk]
  rfl

/-- **A `match` statement's values from its selector's and its arms'.** -/
theorem vals_match {b : List Stmt} {p : ℕ} {n : ℕ} (hm : isMatchAt b p = true)
    (hx : valBelow n (selOf (b.getD p default)) = true)
    (ha : (Stmt.valsArms ((armsOf (b.getD p default)).drop 0)).all (valBelow n) = true) :
    (Stmt.valsList ((b.drop p).take 1)).all (valBelow n) = true := by
  rw [take_one_match hm]
  rw [List.drop_zero] at ha
  show ((selOf (b.getD p default) :: Stmt.valsArms (armsOf (b.getD p default))) ++ []).all _ = true
  rw [List.append_nil, List.all_cons, hx, ha]
  rfl

/-- **A large function's places conjunct from its parts**: the keys, the codes from value `0`, and
the values its core function names (`hp`, `hb`) below the row's length `N`. -/
theorem places_big {j N : ℕ} {pf : Placed} (hk : keysNumbered pf.locs.t = true)
    (hc : codesFrom pf.locs 0 ((placesRow j).drop 0) = true) (hn : (placesRow j).length = N)
    (hp : (guestTraced.getD j default).core.params.all (valBelow N) = true)
    (hb : (Stmt.valsList ((guestTraced.getD j default).core.body.drop 0)).all (valBelow N) = true) :
    partsOk [8] j pf = true := by
  rw [List.drop_zero] at hc hb
  have h : placesOk (guestTraced.getD j default).core pf.locs (placesRow j) = true := by
    simp only [placesOk, valsBelow, hk, hc, hn, Bool.true_and, List.all_append, Bool.and_eq_true]
    exact ⟨hp, hb⟩
  simp only [partsOk, cplParts, List.all_cons, List.all_nil, List.getD_cons_succ, List.getD_cons_zero,
    h, Bool.and_true]

end
end LeanVM.Guest.Backend.CplEval
