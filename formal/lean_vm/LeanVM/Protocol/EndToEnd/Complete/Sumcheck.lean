/-
  LeanVM.Protocol.EndToEnd.Complete.Sumcheck

  The honest prover of the verifier program's sumcheck rounds: the coefficients of the true round
  polynomial, sent with the one coefficient the verifier derives left out, and the simulation of
  the program's `sumcheck` by it, in both of the program's modes.
-/

module

public import LeanVM.Protocol.Whir.Complete.Script
public import LeanVM.Protocol.Whir.Complete.Tables
public import LeanVM.Protocol.Verifier
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Honest sumcheck rounds on the wire

The verifier program's `sumcheck claim count modes` (`LeanVM.Protocol.Verifier.sumcheck`,
`python-verifier/verifier.py:405-426` at leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`) reads,
per round, a polynomial of `count` coefficients with one coefficient left out: in plain mode
(`none`) the linear one, in equality mode (`some r`) the constant one, which it derives from the
running claim. Then it samples the challenge and moves to the polynomial's value there.

The honest prover is given the *claims* as a function `claimOf` of the challenges drawn so far:
the running claim after the challenges `pre`. It is honest for the rounds `modes` from `pre` when

* every next claim is a polynomial of degree below `count` in the next challenge (`PolyLE`), and
* the next claims at `0` and `1` split the current one as the mode's check reads it
  (`RoundSplit`): `c(0) + c(1) = c` in plain mode, `(1 + r)·c(0) + r·c(1) = c` in equality mode.

Its round message (`coeffsOf`) is then the coefficient list of the next claim as a polynomial; the
wire carries it without the coefficient the verifier derives (`wire`), and the verifier rebuilds
it exactly (`follows_sumcheckRoundPoly`), in characteristic two. `follows_sumcheck`: the honest
script `hSumcheck` follows the program from `claimOf pre`, to the challenges drawn and the final
claim `claimOf (pre ++ challenges)`.

Nothing here is specific to a phase: the bus's GKR layers (equality mode), the table sumcheck,
the Flock rounds and the lincheck all instantiate it.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Whir.Complete Polynomial

@[expose] public section

/-! ## Polynomial functions of bounded degree -/

/-- `f` is a polynomial function of degree at most `d`. -/
def PolyLE (d : ℕ) (f : E → E) : Prop :=
  ∃ P : E[X], P.natDegree ≤ d ∧ ∀ x, f x = P.eval x

namespace PolyLE

variable {d d' : ℕ} {f g : E → E}

/-- A constant is a polynomial of every degree. -/
theorem const (d : ℕ) (a : E) : PolyLE d fun _ ↦ a :=
  ⟨C a, by simp, fun x ↦ by simp⟩

/-- The identity has degree one. -/
theorem id : PolyLE 1 fun x ↦ x :=
  ⟨X, natDegree_X_le, fun x ↦ by simp⟩

/-- An affine function has degree one. -/
theorem affine (a b : E) : PolyLE 1 fun x ↦ a + b * x :=
  ⟨C a + C b * X, natDegree_add_le_of_degree_le (by simp)
    ((natDegree_C_mul_le _ _).trans natDegree_X_le), fun x ↦ by simp⟩

/-- A larger degree bound. -/
theorem mono (h : PolyLE d f) (hd : d ≤ d') : PolyLE d' f := by
  obtain ⟨P, hP, hf⟩ := h
  exact ⟨P, hP.trans hd, hf⟩

/-- A function equal to a polynomial function is one. -/
theorem congr (h : PolyLE d f) (hfg : ∀ x, f x = g x) : PolyLE d g := by
  obtain ⟨P, hP, hf⟩ := h
  exact ⟨P, hP, fun x ↦ (hfg x).symm.trans (hf x)⟩

/-- Sums. -/
theorem add (hf : PolyLE d f) (hg : PolyLE d g) : PolyLE d fun x ↦ f x + g x := by
  obtain ⟨P, hP, hfP⟩ := hf
  obtain ⟨Q, hQ, hgQ⟩ := hg
  exact ⟨P + Q, natDegree_add_le_of_degree_le hP hQ, fun x ↦ by simp [hfP, hgQ]⟩

/-- Products add degrees. -/
theorem mul (hf : PolyLE d f) (hg : PolyLE d' g) : PolyLE (d + d') fun x ↦ f x * g x := by
  obtain ⟨P, hP, hfP⟩ := hf
  obtain ⟨Q, hQ, hgQ⟩ := hg
  exact ⟨P * Q, natDegree_mul_le_of_le hP hQ, fun x ↦ by simp [hfP, hgQ]⟩

/-- A constant multiple. -/
theorem const_mul (hf : PolyLE d f) (a : E) : PolyLE d fun x ↦ a * f x :=
  ((mul (const 0 a) hf).mono (by omega)).congr fun _ ↦ rfl

/-- Finite sums. -/
theorem sum {ι : Type} (s : Finset ι) {F : ι → E → E} (h : ∀ i ∈ s, PolyLE d (F i)) :
    PolyLE d fun x ↦ ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (const d 0).congr fun x ↦ by simp
  | insert a s ha ih =>
    refine (add (h a (by simp)) (ih fun i hi ↦ h i (by simp [hi]))).congr fun x ↦ ?_
    rw [Finset.sum_insert ha]

/-- Finite products: the degrees add. -/
theorem prod {ι : Type} (s : Finset ι) {F : ι → E → E} (h : ∀ i ∈ s, PolyLE d (F i)) :
    PolyLE (s.card * d) fun x ↦ ∏ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (const _ 1).congr fun x ↦ by simp
  | insert a s ha ih =>
    refine ((mul (h a (by simp)) (ih fun i hi ↦ h i (by simp [hi]))).mono ?_).congr fun x ↦ ?_
    · rw [Finset.card_insert_of_notMem ha]; nlinarith
    · rw [Finset.prod_insert ha]

end PolyLE

/-! ## Coefficient lists -/

/-- `polyEval` is the sum of the coefficients times the powers. -/
theorem polyEval_eq_sum : ∀ (l : List E) (x : E),
    polyEval l x = ∑ i ∈ Finset.range l.length, l.getD i 0 * x ^ i
  | [], x => by simp [polyEval]
  | c :: l, x => by
    have h : polyEval (c :: l) x = polyEval l x * x + c := rfl
    rw [h, polyEval_eq_sum l x, List.length_cons, Finset.sum_range_succ', Finset.sum_mul]
    refine congrArg₂ (· + ·) ?_ ?_
    · exact Finset.sum_congr rfl fun i _ ↦ by
        rw [List.getD_cons_succ, pow_succ]; ring
    · rw [List.getD_cons_zero, pow_zero, mul_one]

/-- The value of a coefficient list at `0` is its first coefficient. -/
theorem polyEval_zero_cons (c : E) (l : List E) : polyEval (c :: l) 0 = c := by
  show polyEval l 0 * 0 + c = c
  simp

/-- The value of a coefficient list at `1` is the sum of its coefficients. -/
theorem polyEval_one : ∀ l : List E, polyEval l 1 = l.sum
  | [] => rfl
  | c :: l => by
    show polyEval l 1 * 1 + c = _
    rw [mul_one, polyEval_one l, List.sum_cons, add_comm]

/-- The coefficient list of a polynomial function of degree at most `d`, `d + 1` coefficients,
constant first (zeros if `f` is not one). -/
noncomputable def coeffsOf (d : ℕ) (f : E → E) : List E :=
  open Classical in
  if h : PolyLE d f then (List.range (d + 1)).map (Classical.choose h).coeff
  else List.replicate (d + 1) 0

theorem length_coeffsOf (d : ℕ) (f : E → E) : (coeffsOf d f).length = d + 1 := by
  unfold coeffsOf
  split <;> simp

/-- The coefficient list evaluates as the function. -/
theorem polyEval_coeffsOf {d : ℕ} {f : E → E} (h : PolyLE d f) (x : E) :
    polyEval (coeffsOf d f) x = f x := by
  classical
  have hc : coeffsOf d f = (List.range (d + 1)).map (Classical.choose h).coeff := by
    simp [coeffsOf, h]
  obtain ⟨hdeg, hev⟩ := Classical.choose_spec h
  rw [hc, polyEval_eq_sum, hev, eval_eq_sum_range' (Nat.lt_succ_of_le hdeg)]
  simp only [List.length_map, List.length_range]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

/-! ## One round on the wire -/

/-- The round's check, as the mode reads it: `c(0) + c(1) = claim` in plain mode,
`(1 + r)·c(0) + r·c(1) = claim` in equality mode. -/
def RoundSplit (mode : Option E) (claim v0 v1 : E) : Prop :=
  match mode with
  | none => v0 + v1 = claim
  | some r => (1 + r) * v0 + r * v1 = claim

/-- The coefficients the wire carries: all but the linear one in plain mode, all but the constant
one in equality mode. -/
def wire : Option E → List E → List E
  | none, c => c.headD 0 :: c.drop 2
  | some _, c => c.drop 1

/-- **One round.** A coefficient list whose values at `0` and `1` pass the mode's check meets the
verifier's `sumcheckRoundPoly`, which rebuilds it from the wire. -/
theorem follows_sumcheckRoundPoly (count : ℕ) (claim : E) (mode : Option E) (coeffs : List E)
    (hlen : coeffs.length = count) (hcount : 2 ≤ count)
    (hsplit : RoundSplit mode claim (polyEval coeffs 0) (polyEval coeffs 1)) (cs : Commits) :
    Follows (fun cs' _ b ↦ cs' = cs ∧ b = coeffs) (Script.sendList (wire mode coeffs))
      (sumcheckRoundPoly count claim mode) cs := by
  obtain ⟨c0, c1, rest, rfl⟩ : ∃ c0 c1 rest, coeffs = c0 :: c1 :: rest := by
    match coeffs, hlen with
    | c0 :: c1 :: rest, _ => exact ⟨c0, c1, rest, rfl⟩
    | [], h => simp at h; omega
    | [_], h => simp at h; omega
  have hrest : rest.length = count - 2 := by simp at hlen; omega
  rw [polyEval_zero_cons, polyEval_one] at hsplit
  cases mode with
  | none =>
    simp only [RoundSplit, List.sum_cons] at hsplit
    simp only [wire, List.headD_cons, List.drop_succ_cons, List.drop_zero, Script.sendList,
      sumcheckRoundPoly, Prog.readE, Prog.bind_eq, Prog.bind, Follows]
    rw [← hrest, ← Script.bind_ret (Script.sendList rest)]
    refine Follows.bind (fun cs' _ b h ↦ ?_) _ _ _ (Follows.sendList_readN cs rest)
    obtain ⟨rfl, hb⟩ := h
    subst hb
    refine ⟨rfl, ?_⟩
    simp only [List.cons.injEq, true_and, and_true]
    rw [sumE_eq, ← hsplit]
    linear_combination (CharTwo.two_eq_zero (R := E)) * (c0 + b.sum)
  | some r =>
    simp only [RoundSplit, List.sum_cons] at hsplit
    simp only [wire, List.drop_succ_cons, List.drop_zero, sumcheckRoundPoly, Prog.bind_eq]
    have hl : (c1 :: rest).length = count - 1 := by simp; omega
    rw [← hl, ← Script.bind_ret (Script.sendList (c1 :: rest))]
    refine Follows.bind (fun cs' _ b h ↦ ?_) _ _ _ (Follows.sendList_readN cs (c1 :: rest))
    obtain ⟨rfl, hb⟩ := h
    subst hb
    refine ⟨rfl, ?_⟩
    simp only [List.cons.injEq, and_true]
    rw [sumE_eq, List.sum_cons, ← hsplit]
    linear_combination (CharTwo.two_eq_zero (R := E)) * (r * c0 + r * c1 + r * rest.sum)

/-! ## The rounds -/

/-- **The honest sumcheck prover** for the rounds `modes`, after the challenges `pre`: per round,
the coefficients of the next claim as a polynomial of degree below `count`, on the wire; then the
challenge. Returns the challenges drawn and the final claim. -/
noncomputable def hSumcheck (count : ℕ) (claimOf : List E → E) :
    List (Option E) → List E → Script (List E × E)
  | [], pre => .ret ([], claimOf pre)
  | mode :: modes, pre =>
    (Script.sendList (wire mode (coeffsOf (count - 1) fun x ↦ claimOf (pre ++ [x])))).bind
      fun _ ↦ Script.sampleE.bind fun c ↦
        (hSumcheck count claimOf modes (pre ++ [c])).bind fun r ↦ .ret (c :: r.1, r.2)

/-- **The honest rounds follow the program's.** If every next claim is a polynomial of degree
below `count` in the next challenge and the next claims at `0, 1` split the current one as the
round's mode checks it, the honest prover follows `sumcheck (claimOf pre) count modes` to the
challenges it draws and the final claim `claimOf (pre ++ challenges)`. -/
theorem follows_sumcheck (count : ℕ) (hcount : 2 ≤ count) (claimOf : List E → E) :
    ∀ (modes : List (Option E)) (pre : List E) (cs : Commits),
      (∀ ext : List E, ext.length < modes.length →
        PolyLE (count - 1) fun x ↦ claimOf (pre ++ ext ++ [x])) →
      (∀ ext : List E, (h : ext.length < modes.length) →
        RoundSplit modes[ext.length] (claimOf (pre ++ ext)) (claimOf (pre ++ ext ++ [0]))
          (claimOf (pre ++ ext ++ [1]))) →
      Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ b.1.length = modes.length ∧
          b.2 = claimOf (pre ++ b.1))
        (hSumcheck count claimOf modes pre) (sumcheck (claimOf pre) count modes) cs
  | [], pre, cs, _, _ => by
    simp [hSumcheck, sumcheck, Follows]
  | mode :: modes, pre, cs, hdeg, hsplit => by
    have hd := hdeg [] (by simp)
    simp only [List.append_nil] at hd
    have hround := follows_sumcheckRoundPoly count (claimOf pre) mode
      (coeffsOf (count - 1) fun x ↦ claimOf (pre ++ [x])) (by rw [length_coeffsOf]; omega) hcount
      (by
        have h := hsplit [] (by simp)
        simp only [List.append_nil, List.length_nil, List.getElem_cons_zero] at h
        rwa [polyEval_coeffsOf hd, polyEval_coeffsOf hd]) cs
    simp only [hSumcheck, sumcheck, Prog.bind_eq]
    refine Follows.bind (fun cs₁ _ msg h₁ ↦ ?_) _ _ _ hround
    obtain ⟨rfl, rfl⟩ := h₁
    refine Follows.bind (fun cs₂ c c' h₂ ↦ ?_) _ _ _ (Follows.sampleE_sampleE cs₁)
    obtain ⟨rfl, rfl⟩ := h₂
    rw [polyEval_coeffsOf hd]
    have ih := follows_sumcheck count hcount claimOf modes (pre ++ [c]) cs₂
      (fun ext hext ↦ by simpa using hdeg (c :: ext) (by simpa using hext))
      (fun ext hext ↦ by simpa using hsplit (c :: ext) (by simpa using hext))
    refine Follows.bind (fun cs₃ r r' h₃ ↦ ?_) _ _ _ ih
    obtain ⟨rfl, rfl, hl, hf⟩ := h₃
    obtain ⟨pt, fin⟩ := r
    simp only at hl hf ⊢
    refine ⟨rfl, rfl, by simp [hl], ?_⟩
    simpa using hf

end
end LeanVM.Protocol.EndToEnd.Complete
