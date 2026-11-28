/-
  LeanVM.Protocol.Link.Sumcheck

  The statement's plain sum-check (`sumcheck` with no equality factor, `transcript.rs`) in the
  sample model: its challenges are uniform whatever the prover sends, and a false claim survives
  its rounds only with probability `rounds·(count − 1)/|E|`.
-/

module

public import LeanVM.Protocol.Link.Sample
public import Mathlib.Algebra.Polynomial.Roots
import LeanVM.Parameters.Field
import LeanVM.Facts.Hotwire

/-!
# The plain sum-check, sound

`sumcheck claim count equalities` (`Statement/Verifier/Sumcheck.lean`, `Transcript::sumcheck`) runs one
round per entry of `equalities`; with no equality factor (`none`, every round of `verify_link`'s
sum-checks), a round reads the constant coefficient and the `count − 2` top ones, derives the linear
one as `claim + Σ tail` (`sumcheckRoundPoly`), so that in characteristic two the round polynomial
`m` always satisfies `m(0) + m(1) = claim`, then samples `c` and moves to `m(c)`.

A sum-check proves a claim on a table of partial sums `g` (`RoundPolys g n deg`): `g p` is the sum,
over the Boolean completions of the prefix `p` of challenges, of the summand, and each round's
`c ↦ g (p ++ [c])` is a polynomial `q` of degree at most `deg |p|` with `q(0) + q(1) = g p`.

* `win_sumcheck_le`: whatever the claim, the challenges are uniform: the best prover's chance is at
  most the average, over the `n` challenges, of its best chance from each final claim.
* `win_sumcheck_le_of_ne` (**soundness**): if the claim is not `g []`, a final claim equal to the
  summand at the challenges is reached with probability at most `n·(count − 1)/|E|`: in each round
  the prover's `m` differs from `q` (their sums at `0` and `1` differ), two distinct polynomials of
  degree at most `count − 1` agree at no more than `count − 1` points (`card_agree_le`), and off
  those the next claim is false again.
-/

namespace LeanVM.Protocol.Link

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier Finset
open scoped ENNReal

@[expose] public section

/-! ## Round polynomials -/

/-- A coefficient list, constant first, as a polynomial. -/
noncomputable def toPoly : List E → Polynomial E
  | [] => 0
  | c :: cs => Polynomial.C c + Polynomial.X * toPoly cs

theorem eval_toPoly (x : E) : ∀ l : List E, (toPoly l).eval x = polyEval l x
  | [] => by simp [toPoly, polyEval]
  | c :: cs => by
    have ih := eval_toPoly x cs
    simp only [toPoly, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X, ih]
    simp only [polyEval, List.foldr_cons]
    ring

theorem eval_one_toPoly : ∀ l : List E, (toPoly l).eval 1 = l.sum
  | [] => by simp [toPoly]
  | c :: cs => by simp [toPoly, eval_one_toPoly cs]

theorem eval_zero_toPoly (c : E) (cs : List E) : (toPoly (c :: cs)).eval 0 = c := by
  simp [toPoly]

theorem natDegree_toPoly : ∀ l : List E, (toPoly l).natDegree ≤ l.length - 1
  | [] => by simp [toPoly]
  | [c] => by simp [toPoly]
  | c :: d :: cs => by
    have ih := natDegree_toPoly (d :: cs)
    simp only [List.length_cons, Nat.add_sub_cancel] at ih ⊢
    refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
    refine (Polynomial.natDegree_mul_le).trans ?_
    have hX : (Polynomial.X : Polynomial E).natDegree ≤ 1 := Polynomial.natDegree_X_le
    omega

/-- `sumE` is the list's sum. -/
theorem sumE_eq_sum (l : List E) : sumE l = l.sum := by
  unfold sumE
  rw [Hotwire.foldl_add_eq]
  simp

/-- The message a plain round reads, `[c_0, claim + Σ tail, tail…]`, sums to the claim at `0` and
`1`, in characteristic two. -/
theorem roundMessage_sum (claim c0 : E) (tail : List E) :
    (toPoly (c0 :: (claim + sumE tail) :: tail)).eval 0 +
      (toPoly (c0 :: (claim + sumE tail) :: tail)).eval 1 = claim := by
  rw [eval_zero_toPoly, eval_one_toPoly, sumE_eq_sum]
  simp only [List.sum_cons]
  have h1 : c0 + c0 = 0 := CharTwo.add_self_eq_zero c0
  have h2 : tail.sum + tail.sum = 0 := CharTwo.add_self_eq_zero _
  linear_combination h1 + h2

/-- Two distinct polynomials of degree at most `D` agree at no more than `D` points. -/
theorem card_agree_le (m q : Polynomial E) (hne : m ≠ q) {D : ℕ} (hm : m.natDegree ≤ D)
    (hq : q.natDegree ≤ D) :
    (univ.filter fun c : E ↦ m.eval c = q.eval c).card ≤ D := by
  classical
  have hsub : m - q ≠ 0 := sub_ne_zero.mpr hne
  calc _ ≤ (m - q).roots.toFinset.card := by
        refine card_le_card fun c hc ↦ ?_
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hsub, Polynomial.IsRoot,
          Polynomial.eval_sub, sub_eq_zero]
        exact (mem_filter.mp hc).2
    _ ≤ (m - q).roots.card := Multiset.toFinset_card_le _
    _ ≤ (m - q).natDegree := Polynomial.card_roots' _
    _ ≤ D := (Polynomial.natDegree_sub_le _ _).trans (max_le hm hq)

/-- An average over one challenge with at most `D` bad values: at most `D/|E|` plus the average of
the bounds off them. -/
theorem sum_div_le_bad {h b : E → ℝ≥0∞} (B : E → Prop) [DecidablePred B] {D : ℕ}
    (hB : (univ.filter B).card ≤ D) (h1 : ∀ c, h c ≤ 1) (hb : ∀ c, ¬ B c → h c ≤ b c) :
    (∑ c, h c) / cardE ≤ (D : ℝ≥0∞) / cardE + (∑ c, b c) / cardE := by
  rw [← ENNReal.add_div]
  refine ENNReal.div_le_div_right ?_ _
  calc ∑ c, h c ≤ ∑ c, ((if B c then 1 else 0) + b c) := sum_le_sum fun c _ ↦ by
        by_cases hc : B c
        · simp only [hc, ite_true]; exact (h1 c).trans le_self_add
        · simp only [hc, ite_false, zero_add]; exact hb c hc
    _ = ((univ.filter B).card : ℝ≥0∞) + ∑ c, b c := by
        rw [sum_add_distrib, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
    _ ≤ D + ∑ c, b c := by gcongr

/-! ## Tables of partial sums -/

/-- `g` is a sum-check's table of partial sums over `n` rounds of degrees `deg`: for each prefix
`p` of fewer than `n` challenges, `c ↦ g (p ++ [c])` is a polynomial `q` of degree at most
`deg |p|` whose values at `0` and `1` sum to `g p`. -/
def RoundPolys (g : List E → E) (n : ℕ) (deg : ℕ → ℕ) : Prop :=
  ∀ p : List E, p.length < n → ∃ q : Polynomial E, q.natDegree ≤ deg p.length ∧
    q.eval 0 + q.eval 1 = g p ∧ ∀ c, q.eval c = g (p ++ [c])

/-- After the first challenge `c`, the rest of the table. -/
theorem RoundPolys.tail {g : List E → E} {n : ℕ} {deg : ℕ → ℕ} (h : RoundPolys g (n + 1) deg)
    (c : E) : RoundPolys (fun p ↦ g (c :: p)) n (fun i ↦ deg (i + 1)) := by
  intro p hp
  obtain ⟨q, hq, hsum, hval⟩ := h (c :: p) (by simp; omega)
  exact ⟨q, by simpa using hq, hsum, fun c' ↦ by simpa using hval c'⟩

/-- The first `n` rounds of a longer table. -/
theorem RoundPolys.take {g : List E → E} {n m : ℕ} {deg : ℕ → ℕ} (h : RoundPolys g (n + m) deg) :
    RoundPolys g n deg :=
  fun p hp ↦ h p (by omega)

/-- After `n` challenges `a`, the rest of a longer table. -/
theorem RoundPolys.drop {g : List E → E} {n m : ℕ} {deg : ℕ → ℕ} (h : RoundPolys g (n + m) deg)
    (a : List E) (ha : a.length = n) : RoundPolys (fun p ↦ g (a ++ p)) m (fun i ↦ deg (n + i)) := by
  intro p hp
  obtain ⟨q, hq, hsum, hval⟩ := h (a ++ p) (by simp [ha]; omega)
  exact ⟨q, by simpa [ha] using hq, hsum, fun c ↦ by simpa using hval c⟩

/-! ## The program -/

section Program

variable {α : Type} (W : α → Prop)

/-- A plain round's message: the best prover's chance is at most its best over the constant
coefficient and the `count − 2` top ones, the linear one derived. -/
theorem win_roundPoly_bind (count : ℕ) (claim : E) (K : List E → VerifierProgram α) :
    win W ((sumcheckRoundPoly count claim none).bind K) ≤
      ⨆ (c0 : E) (tail : List E) (_ : tail.length = count - 2),
        win W (K (c0 :: (claim + sumE tail) :: tail)) := by
  show (⨆ c0, win W (((VerifierProgram.readScalars (count - 2)).bind fun tail ↦
      (VerifierProgram.grindProofOfWork (grindingBits (count - 1))).bind fun _ ↦
        VerifierProgram.ret (c0 :: (claim + sumE tail) :: tail)).bind K)) ≤ _
  refine iSup_le fun c0 ↦ le_iSup_of_le c0 ?_
  rw [bind_assoc]
  refine (win_readScalars_bind W _ _).trans (iSup₂_le fun tail htail ↦ ?_)
  refine le_iSup₂_of_le tail htail ?_
  rw [bind_assoc]
  exact (win_grindProofOfWork_bind W _ _).le

/-- One round, then the rest: the round's message, its challenge, the remaining rounds. -/
theorem sumcheck_cons_bind (claim : E) (count : ℕ) (e : Option E) (es : List (Option E))
    (k : List E × E → VerifierProgram α) :
    (sumcheck claim count (e :: es)).bind k =
      (sumcheckRoundPoly count claim e).bind fun msg ↦ VerifierProgram.sample fun c ↦
        (sumcheck (polyEval msg c) count es).bind fun x ↦ k (c :: x.1, x.2) := by
  show (((sumcheckRoundPoly count claim e).bind fun message ↦
      (VerifierProgram.sample VerifierProgram.ret).bind fun challenge ↦
        (sumcheck (polyEval message challenge) count es).bind fun x ↦
          VerifierProgram.ret (challenge :: x.1, x.2))).bind k = _
  simp only [bind_assoc]
  rfl

/-- **The challenges are uniform.** Whatever the claim, the best prover's chance through a plain
sum-check is at most the average over its `n` challenges of its best chance from any final claim. -/
theorem win_sumcheck_le (count : ℕ) :
    ∀ (n : ℕ) (claim : E) (k : List E × E → VerifierProgram α),
      win W ((sumcheck claim count (List.replicate n none)).bind k) ≤
        avgL n fun r ↦ ⨆ f, win W (k (r, f))
  | 0, claim, k => le_iSup (fun f ↦ win W (k ([], f))) claim
  | n + 1, claim, k => by
    rw [List.replicate_succ, sumcheck_cons_bind]
    refine (win_roundPoly_bind W count claim _).trans (iSup_le fun c0 ↦ iSup₂_le fun tail _ ↦ ?_)
    rw [win_sample, avgL_succ]
    exact ENNReal.div_le_div_right (sum_le_sum fun c _ ↦ win_sumcheck_le count n _ _) _

/-- **Soundness of the plain sum-check.** If the claim is not the table's total `g []`, the best
prover reaches a final claim equal to the summand `g r` at the challenges `r` with probability at
most `n·(count − 1)/|E|`: the bound is that error plus the average of its best chance from a false
final claim. -/
theorem win_sumcheck_le_of_ne (count : ℕ) (hcount : 2 ≤ count) :
    ∀ (n : ℕ) (deg : ℕ → ℕ) (g : List E → E) (claim : E) (k : List E × E → VerifierProgram α),
      RoundPolys g n deg → (∀ i < n, deg i ≤ count - 1) → claim ≠ g [] →
      win W ((sumcheck claim count (List.replicate n none)).bind k) ≤
        ((n * (count - 1) : ℕ) : ℝ≥0∞) / cardE +
          avgL n fun r ↦ ⨆ (f : E) (_ : f ≠ g r), win W (k (r, f))
  | 0, _, g, claim, k, _, _, hne => by
    refine le_add_left (le_iSup₂_of_le claim hne le_rfl)
  | n + 1, deg, g, claim, k, hg, hdeg, hne => by
    classical
    rw [List.replicate_succ, sumcheck_cons_bind]
    refine (win_roundPoly_bind W count claim _).trans (iSup_le fun c0 ↦ iSup₂_le fun tail htail ↦ ?_)
    obtain ⟨q, hq, hqsum, hqval⟩ := hg [] (by simp)
    have hmq : toPoly (c0 :: (claim + sumE tail) :: tail) ≠ q := fun h ↦ hne (by
      rw [← hqsum, ← h]; exact (roundMessage_sum claim c0 tail).symm)
    have hmdeg : (toPoly (c0 :: (claim + sumE tail) :: tail)).natDegree ≤ count - 1 :=
      (natDegree_toPoly _).trans (by simp [htail]; omega)
    have hbad := card_agree_le _ q hmq hmdeg (hq.trans (hdeg 0 (by omega)))
    rw [win_sample, avgL_succ (n := n) (f := fun r ↦ ⨆ (f : E) (_ : f ≠ g r), win W (k (r, f)))]
    refine (sum_div_le_bad (b := fun c ↦ ((n * (count - 1) : ℕ) : ℝ≥0∞) / cardE +
        avgL n fun r ↦ ⨆ (f : E) (_ : f ≠ g (c :: r)), win W (k (c :: r, f)))
      (fun c ↦ (toPoly (c0 :: (claim + sumE tail) :: tail)).eval c = q.eval c) hbad
      (fun _ ↦ win_le_one W _) (fun c hc ↦ ?_)).trans ?_
    · refine win_sumcheck_le_of_ne count hcount n (fun i ↦ deg (i + 1)) (fun p ↦ g (c :: p))
        (polyEval (c0 :: (claim + sumE tail) :: tail) c) (fun x ↦ k (c :: x.1, x.2)) (hg.tail c)
        (fun i hi ↦ hdeg (i + 1) (by omega)) ?_
      exact fun h ↦ hc (by rw [eval_toPoly, h, hqval c]; rfl)
    · rw [sum_add_distrib, ENNReal.add_div, sum_const_div_cardE, ← add_assoc, ← ENNReal.add_div,
        ← Nat.cast_add, show count - 1 + n * (count - 1) = (n + 1) * (count - 1) by ring]

end Program

end

end LeanVM.Protocol.Link
