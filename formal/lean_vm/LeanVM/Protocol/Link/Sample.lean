/-
  LeanVM.Protocol.Link.Sample

  The verifier language read as a public-coin protocol: the best prover's chance of making a
  program return a value with a given property, every challenge uniform in `E`; and the counting
  lemmas the link's soundness reads.
-/

module

public import Statement.Verifier.Lib
public import LeanVM.Protocol.Field
public import ToMathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Algebra.MvPolynomial.Rename
import LeanVM.Parameters.Field

/-!
# The sample model

`Statement/Verifier/`'s verifier is a program (`VerifierProgram`) over the transcript's
operations; the deployed verifier draws its challenges from a sponge (`run`). Here it is read as an
interactive public-coin protocol against an unbounded, adaptive prover: every challenge is uniform
in `E` and independent of what came before, and every prover message is the prover's choice.
`win W P` is the best prover's probability of making `P` return a value satisfying `W`:

* a challenge (`sample`, and the `n` challenges of a packed draw) averages over its values
  (`avgL`, the average over the lists of `n` uniform challenges);
* a prover message (`read`, a packed message of any length, an opening's rows) takes the supremum
  over its values, the best choice given everything before it;
* a proof of work and a commitment's root cost the prover nothing: the bound holds whatever the
  grind's difficulty, and the committed data is fixed beforehand, so `W` may speak of it.

This is the model a per-phase soundness statement lives in; the Fiat-Shamir transform, the sponge's
challenges in place of uniform ones, is a separate step. The counting lemmas
(`avgL_le_card`, `card_eval_comp_le`, `card_affine_le`) turn Schwartz-Zippel counts into bounds on
averages.
-/

namespace LeanVM.Protocol.Link

open LeanVM.Parameters LeanVM.Protocol.Compile Finset MvPolynomial
open scoped ENNReal

@[expose] public section

/-- `|E|` in `ℝ≥0∞`. -/
noncomputable abbrev cardE : ℝ≥0∞ := (Fintype.card E : ℝ≥0∞)

theorem cardE_ne_zero : cardE ≠ 0 := by
  simp only [cardE, ne_eq, Nat.cast_eq_zero]
  exact Fintype.card_ne_zero

theorem cardE_ne_top : cardE ≠ ⊤ := ENNReal.natCast_ne_top _

/-! ## Averages over uniform challenges -/

/-- The average of `f` over the lists of `n` independent uniform challenges, the first one first. -/
noncomputable def avgL : ℕ → (List E → ℝ≥0∞) → ℝ≥0∞
  | 0, f => f []
  | n + 1, f => (∑ c : E, avgL n fun l ↦ f (c :: l)) / cardE

theorem avgL_zero (f : List E → ℝ≥0∞) : avgL 0 f = f [] := rfl

theorem avgL_succ (n : ℕ) (f : List E → ℝ≥0∞) :
    avgL (n + 1) f = (∑ c : E, avgL n fun l ↦ f (c :: l)) / cardE := rfl

/-- The average of a sum over `E` divided by `|E|` is at most `b` when each term is. -/
theorem sum_div_cardE_le {f : E → ℝ≥0∞} {b : ℝ≥0∞} (h : ∀ c, f c ≤ b) :
    (∑ c : E, f c) / cardE ≤ b := by
  rw [ENNReal.div_le_iff cardE_ne_zero cardE_ne_top]
  calc ∑ c : E, f c ≤ ∑ _c : E, b := sum_le_sum fun c _ ↦ h c
    _ = b * cardE := by rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]

/-- A constant's average over `E` is itself. -/
theorem sum_const_div_cardE (b : ℝ≥0∞) : (∑ _c : E, b) / cardE = b := by
  rw [sum_const, card_univ, nsmul_eq_mul, mul_comm,
    ENNReal.mul_div_cancel_right cardE_ne_zero cardE_ne_top]

theorem avgL_mono {n : ℕ} {f g : List E → ℝ≥0∞} (h : ∀ l, l.length = n → f l ≤ g l) :
    avgL n f ≤ avgL n g := by
  induction n generalizing f g with
  | zero => exact h [] rfl
  | succ n ih =>
    rw [avgL_succ, avgL_succ]
    exact ENNReal.div_le_div_right (sum_le_sum fun c _ ↦
      ih fun l hl ↦ h (c :: l) (by simp [hl])) _

theorem avgL_const (n : ℕ) (b : ℝ≥0∞) : avgL n (fun _ ↦ b) = b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [avgL_succ]; simp only [ih]; exact sum_const_div_cardE b

theorem avgL_le_of_le {n : ℕ} {f : List E → ℝ≥0∞} {b : ℝ≥0∞} (h : ∀ l, l.length = n → f l ≤ b) :
    avgL n f ≤ b :=
  (avgL_mono h).trans_eq (avgL_const n b)

theorem avgL_add (n : ℕ) (f g : List E → ℝ≥0∞) :
    avgL n (fun l ↦ f l + g l) = avgL n f + avgL n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [avgL_succ, ih, sum_add_distrib, ENNReal.add_div]

/-- Splitting the challenges in two runs. -/
theorem avgL_append (n m : ℕ) (f : List E → ℝ≥0∞) :
    avgL (n + m) f = avgL n fun a ↦ avgL m fun b ↦ f (a ++ b) := by
  induction n generalizing f with
  | zero => simp [avgL_zero]
  | succ n ih =>
    rw [Nat.succ_add, avgL_succ, avgL_succ]
    simp only [ih, List.cons_append]

/-- A bad set and a bound off it: the average is at most the bad set's average plus the bound. -/
theorem avgL_le_bad {n : ℕ} {f : List E → ℝ≥0∞} (B : List E → Prop) [DecidablePred B] {b : ℝ≥0∞}
    (h1 : ∀ l, f l ≤ 1) (hb : ∀ l, l.length = n → ¬ B l → f l ≤ b) :
    avgL n f ≤ avgL n (fun l ↦ if B l then 1 else 0) + b := by
  rw [← avgL_const n b, ← avgL_add]
  refine avgL_mono fun l hl ↦ ?_
  by_cases hB : B l
  · simp only [hB, ite_true]
    exact (h1 l).trans le_self_add
  · simp only [hB, ite_false, zero_add]
    exact hb l hl hB

/-- The average is the sum over the challenge vectors over their number. -/
theorem avgL_eq_sum (n : ℕ) (f : List E → ℝ≥0∞) :
    avgL n f = (∑ v : Fin n → E, f (List.ofFn v)) / cardE ^ n := by
  induction n generalizing f with
  | zero => simp [avgL_zero]
  | succ n ih =>
    rw [avgL_succ]
    simp only [ih]
    have hsplit : ∑ v : Fin (n + 1) → E, f (List.ofFn v) =
        ∑ c : E, ∑ v : Fin n → E, f (c :: List.ofFn v) := by
      rw [← (Fin.consEquiv fun _ : Fin (n + 1) ↦ E).sum_comp, Fintype.sum_prod_type]
      refine sum_congr rfl fun c _ ↦ sum_congr rfl fun v _ ↦ ?_
      simp [Fin.consEquiv, List.ofFn_succ]
    rw [hsplit, pow_succ, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, Finset.mul_sum,
      ENNReal.mul_inv (Or.inr cardE_ne_top) (Or.inr cardE_ne_zero)]
    simp only [ENNReal.div_eq_inv_mul, Finset.mul_sum, mul_assoc]
    refine sum_congr rfl fun c _ ↦ sum_congr rfl fun v _ ↦ ?_
    ring

/-- An indicator's average is its set's size over `|E|^n`. -/
theorem avgL_indicator (n : ℕ) (B : List E → Prop) [DecidablePred B] :
    avgL n (fun l ↦ if B l then 1 else 0) =
      ((univ.filter fun v : Fin n → E ↦ B (List.ofFn v)).card : ℝ≥0∞) / cardE ^ n := by
  rw [avgL_eq_sum, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]

/-- **The counting bound.** A set of at most `D·|E|^(n-1)` of the `|E|^n` challenge vectors has
average at most `D/|E|`. -/
theorem avgL_le_card {n D : ℕ} (hn : 1 ≤ n) (B : List E → Prop) [DecidablePred B]
    (hc : (univ.filter fun v : Fin n → E ↦ B (List.ofFn v)).card ≤ D * Fintype.card E ^ (n - 1)) :
    avgL n (fun l ↦ if B l then 1 else 0) ≤ (D : ℝ≥0∞) / cardE := by
  rw [avgL_indicator]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hc
  rw [ENNReal.div_le_iff (pow_ne_zero _ cardE_ne_zero) (ENNReal.pow_ne_top cardE_ne_top),
    pow_succ, ← mul_assoc, mul_right_comm, ENNReal.div_mul_cancel cardE_ne_zero cardE_ne_top]
  exact_mod_cast hc

/-! ## Sequencing -/

/-- Sequencing is associative. -/
theorem bind_assoc {α β γ : Type} (p : VerifierProgram α) (f : α → VerifierProgram β)
    (g : β → VerifierProgram γ) : (p.bind f).bind g = p.bind fun a ↦ (f a).bind g := by
  induction p with
  | ret a => rfl
  | fail => rfl
  | read k ih => simp only [VerifierProgram.bind, ih]
  | sample k ih => simp only [VerifierProgram.bind, ih]
  | readPacked n k ih => simp only [VerifierProgram.bind, ih]
  | samplePacked n k ih => simp only [VerifierProgram.bind, ih]
  | grind b k ih => simp only [VerifierProgram.bind, ih]
  | commit h w k ih => simp only [VerifierProgram.bind, ih]
  | query i ps k ih => simp only [VerifierProgram.bind, ih]

/-! ## The best prover's chance -/

/-- **The sample model**: the best prover's probability of making `P` return a value satisfying
`W`, every challenge uniform and every prover message the prover's best choice. A packed message
ranges over every list (the program reads exactly its length; the supremum over more is an upper
bound), a proof of work and a commitment cost nothing, and an opening's rows are the prover's. -/
noncomputable def win {α : Type} (W : α → Prop) : VerifierProgram α → ℝ≥0∞
  | .ret a => @ite _ (W a) (Classical.propDecidable _) 1 0
  | .fail => 0
  | .read k => ⨆ x, win W (k x)
  | .sample k => (∑ c : E, win W (k c)) / cardE
  | .readPacked _ k => ⨆ xs, win W (k xs)
  | .samplePacked n k => avgL n fun l ↦ win W (k l)
  | .grind _ k => win W k
  | .commit _ _ k => win W k
  | .query _ _ k => ⨆ rows, win W (k rows)

section Win

variable {α β : Type} (W : α → Prop)

theorem win_ret_of {a : α} (h : W a) : win W (.ret a) = 1 := by
  simp [win, h]

theorem win_ret_of_not {a : α} (h : ¬ W a) : win W (.ret a) = 0 := by
  simp [win, h]

theorem win_fail : win W (.fail : VerifierProgram α) = 0 := rfl

theorem win_read (k : E → VerifierProgram α) : win W (.read k) = ⨆ x, win W (k x) := rfl

theorem win_sample (k : E → VerifierProgram α) :
    win W (.sample k) = (∑ c : E, win W (k c)) / cardE := rfl

theorem win_readPacked (n : ℕ) (k : List E → VerifierProgram α) :
    win W (.readPacked n k) = ⨆ xs, win W (k xs) := rfl

theorem win_samplePacked (n : ℕ) (k : List E → VerifierProgram α) :
    win W (.samplePacked n k) = avgL n fun l ↦ win W (k l) := rfl

theorem win_grind (b : ℕ) (k : VerifierProgram α) : win W (.grind b k) = win W k := rfl

/-- The best prover wins with probability at most one. -/
theorem win_le_one (P : VerifierProgram α) : win W P ≤ 1 := by
  induction P with
  | ret a => by_cases h : W a <;> simp [win, h]
  | fail => exact zero_le
  | read k ih => exact iSup_le ih
  | sample k ih => exact sum_div_cardE_le ih
  | readPacked n k ih => exact iSup_le ih
  | samplePacked n k ih => exact avgL_le_of_le fun l _ ↦ ih l
  | grind b k ih => exact ih
  | commit h w k ih => exact ih
  | query i ps k ih => exact iSup_le ih

/-- A program that never returns a winning value is never won. -/
theorem win_eq_zero_of {P : VerifierProgram α} (h : ∀ a, ¬ W a) : win W P = 0 := by
  induction P with
  | ret a => exact win_ret_of_not W (h a)
  | fail => rfl
  | read k ih => simp [win_read, ih]
  | sample k ih => simp [win_sample, ih]
  | readPacked n k ih => simp [win_readPacked, ih]
  | samplePacked n k ih => simp only [win_samplePacked, ih]; exact avgL_const n 0
  | grind b k ih => exact ih
  | commit h w k ih => exact ih
  | query i ps k ih => simp [win, ih]

/-- Reading one scalar and continuing. -/
theorem win_readScalar_bind (k : E → VerifierProgram α) :
    win W (VerifierProgram.readScalar.bind k) = ⨆ x, win W (k x) := rfl

/-- Sampling one challenge and continuing. -/
theorem win_sampleChallenge_bind (k : E → VerifierProgram α) :
    win W (VerifierProgram.sampleChallenge.bind k) = (∑ c : E, win W (k c)) / cardE := rfl

/-- Sampling `n` packed challenges and continuing. -/
theorem win_sampleChallengesPacked_bind (n : ℕ) (k : List E → VerifierProgram α) :
    win W ((VerifierProgram.sampleChallengesPacked n).bind k) = avgL n fun l ↦ win W (k l) := rfl

/-- Reading a packed message and continuing: at most the best message. -/
theorem win_readScalarsPacked_bind (n : ℕ) (k : List E → VerifierProgram α) :
    win W ((VerifierProgram.readScalarsPacked n).bind k) = ⨆ xs, win W (k xs) := rfl

/-- A proof of work costs the prover nothing. -/
theorem win_grindProofOfWork_bind (b : ℕ) (k : Unit → VerifierProgram α) :
    win W ((VerifierProgram.grindProofOfWork b).bind k) = win W (k ()) := by
  unfold VerifierProgram.grindProofOfWork
  split <;> rfl

/-- A check and a return of `s`: won at most as `k s`. -/
theorem win_require_bind (c : Prop) [Decidable c] (k : Unit → VerifierProgram α) :
    win W ((VerifierProgram.require c).bind k) ≤ win W (k ()) := by
  unfold VerifierProgram.require
  split
  · exact le_rfl
  · show (0 : ℝ≥0∞) ≤ _
    exact zero_le

/-- `n` prover scalars, then `k`: at most the best list of `n` scalars. -/
theorem win_readScalars_bind (n : ℕ) (k : List E → VerifierProgram α) :
    win W ((VerifierProgram.readScalars n).bind k) ≤
      ⨆ (xs : List E) (_ : xs.length = n), win W (k xs) := by
  induction n generalizing k with
  | zero => exact le_iSup₂_of_le [] rfl le_rfl
  | succ n ih =>
    show (⨆ x, win W (((VerifierProgram.readScalars n).bind fun xs ↦
        VerifierProgram.ret (x :: xs)).bind k)) ≤ _
    refine iSup_le fun x ↦ ?_
    have hassoc : ((VerifierProgram.readScalars n).bind fun xs ↦ VerifierProgram.ret (x :: xs)).bind k =
        (VerifierProgram.readScalars n).bind fun xs ↦ k (x :: xs) := by
      rw [bind_assoc]; rfl
    rw [hassoc]
    exact (ih _).trans (iSup₂_le fun xs hxs ↦ le_iSup₂_of_le (x :: xs) (by simp [hxs]) le_rfl)

end Win

/-! ## Counting zeros -/

/-- **Schwartz-Zippel at the challenges' positions.** A nonzero polynomial of total degree at most
`D`, its variables placed injectively among `n` challenges, vanishes at no more than `D·|E|^(n-1)`
of the `|E|^n` challenge vectors. -/
theorem card_eval_comp_le {σ : Type} [Fintype σ] [DecidableEq σ] {n : ℕ} (ι : σ → Fin n)
    (hι : Function.Injective ι) (P : MvPolynomial σ E) (hP : P ≠ 0) {D : ℕ} (hD : P.totalDegree ≤ D) :
    (univ.filter fun v : Fin n → E ↦ eval (v ∘ ι) P = 0).card ≤ D * Fintype.card E ^ (n - 1) := by
  classical
  have hR : rename ι P ≠ 0 := fun h ↦ hP (rename_injective ι hι (h.trans (map_zero _).symm))
  have h := card_zeros_le_of_totalDegree_le (rename ι P) hR ((totalDegree_rename_le ι P).trans hD)
  rw [Fintype.card_fin] at h
  refine le_of_eq_of_le (congrArg card (filter_congr fun v _ ↦ ?_)) h
  rw [eval_rename]

/-- **An affine form's zeros.** `a + Σ_i x_i·b_i`, not identically zero (`a ≠ 0` or some
`b_i ≠ 0`), vanishes at no more than `|E|^(n-1)` of the `|E|^n` points. -/
theorem card_affine_le {n : ℕ} (a : E) (b : Fin n → E) (h : a ≠ 0 ∨ ∃ i, b i ≠ 0) :
    (univ.filter fun v : Fin n → E ↦ a + ∑ i, v i * b i = 0).card ≤ Fintype.card E ^ (n - 1) := by
  classical
  let P : MvPolynomial (Fin n) E := C a + ∑ i, X i * C (b i)
  have hev : ∀ v, eval v P = a + ∑ i, v i * b i := fun v ↦ by simp [P]
  have hP : P ≠ 0 := by
    intro h0
    rcases h with ha | ⟨i, hi⟩
    · have := congrArg (eval 0) h0
      rw [hev] at this
      simp at this
      exact ha this
    · have h1 := congrArg (eval 0) h0
      have h2 := congrArg (eval (Pi.single i 1)) h0
      rw [hev] at h1 h2
      simp only [Pi.zero_apply, zero_mul, sum_const_zero, add_zero, map_zero] at h1
      rw [h1, zero_add, map_zero, sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)] at h2
      simp at h2
      exact hi h2
  have hD : P.totalDegree ≤ 1 := by
    refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ ↦ ?_)
    refine (totalDegree_mul _ _).trans ?_
    simp [totalDegree_X]
  have h := card_eval_comp_le (σ := Fin n) id Function.injective_id P hP hD
  simpa [hev] using h

end

end LeanVM.Protocol.Link
