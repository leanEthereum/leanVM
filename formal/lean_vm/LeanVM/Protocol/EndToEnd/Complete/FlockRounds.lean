/-
  LeanVM.Protocol.EndToEnd.Complete.FlockRounds

  The honest rounds of the Flock argument on the wire: the zerocheck's normalized rounds and the
  lincheck's plain rounds, as instances of the generic honest sumcheck, their claims the Flock
  argument's partial sums.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.Sumcheck
public import LeanVM.Protocol.EndToEnd.Front.FlockLin
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# The Flock rounds on the wire

The verifier program's Flock phase (`verifyFlockZerocheck`, `verifyFlockLincheck`,
`python-verifier/verifier.py:1125-1176` at leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`)
runs two sumchecks of three coefficients a round: the zerocheck's, in equality mode against the
zerocheck point, lowest coordinate first; and the lincheck's, in plain mode, highest coordinate
first. The Flock argument (`LeanVM.Protocol.ToArkLib.Flock.Rounds`) names their running claims:
`partialSum (prodSub A B C) r j c` and `highSum (linFun M Z) j c`, and its honest round messages
evaluate to the next claims (`evaluate_normRound`, `evaluate_highRound`) and pass the round's
check (`weightedSum_normRound`, `weightedSum_highRound`).

The generic honest sumcheck (`Complete.Sumcheck`) reads claims off lists of challenges;
`claimL G l` is the claim `G` at the challenges `l` as a vector. `follows_normSumcheck` and
`follows_highSumcheck` are the two sumchecks' simulations: the honest prover follows the
program's rounds to the challenges it draws and the claim at their end, the summand at the
challenges (`partialSum_self`) or at the reversed challenges (`highSum_self`).
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir.Complete
open LeanVM.Protocol CompPoly CMlPolynomialEval

@[expose] public section

/-! ## Claims read off lists -/

/-- A claim on vectors of challenges, read at a list of challenges. -/
def claimL (G : (j : ℕ) → Vector E j → E) (l : List E) : E :=
  G l.length (Front.toVec l.length l)

/-- One more challenge pushes it on the vector. -/
theorem claimL_append_singleton (G : (j : ℕ) → Vector E j → E) (l : List E) (x : E) :
    claimL G (l ++ [x]) = G (l.length + 1) ((Front.toVec l.length l).push x) := by
  unfold claimL
  rw [← Front.toVec_append_singleton rfl x]
  have h : (l ++ [x]).length = l.length + 1 := by simp
  rw [h]

/-- A claim at a list of known length. -/
theorem claimL_of_length (G : (j : ℕ) → Vector E j → E) {l : List E} {n : ℕ}
    (h : l.length = n) : claimL G l = G n (Front.toVec n l) := by
  subst h
  rfl

/-- The empty list is the empty vector. -/
theorem claimL_nil (G : (j : ℕ) → Vector E j → E) : claimL G [] = G 0 #v[] := by
  unfold claimL
  rw [List.length_nil, Front.toVec_zero]

/-- A vector's list read back as a vector. -/
theorem toVec_toList {n : ℕ} (v : Vector E n) : Front.toVec n v.toList = v := by
  apply Vector.ext
  intro i hi
  simp [Front.toVec, List.getD_eq_getElem?_getD]

/-- A list of the right length is its vector's list. -/
theorem toList_toVec {n : ℕ} {l : List E} (h : l.length = n) : (Front.toVec n l).toList = l := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [Front.toVec, List.getD_eq_getElem?_getD]

/-- A round message of degree two is a polynomial function of degree two. -/
theorem polyLE_evaluate (q : SumcheckRound.Message E 2) :
    PolyLE 2 fun x ↦ SumcheckRound.evaluate 2 q x := by
  refine ⟨Polynomial.C q[2] * Polynomial.X ^ 2 + Polynomial.C q[1] * Polynomial.X +
    Polynomial.C q[0], Polynomial.natDegree_quadratic_le, fun x ↦ ?_⟩
  simp [SumcheckRound.evaluate, Fin.sum_univ_succ]
  ring

/-! ## The zerocheck's rounds -/

/-- **The zerocheck's rounds.** In equality mode against the point `r`, the honest prover of the
partial sums of `Ã·B̃ - C̃` follows the program's rounds from the full sum, to `n` challenges and
the summand there. -/
theorem follows_normSumcheck {n : ℕ} (tA tB tC : CMlPolynomialEval E n) (r : Vector E n)
    (modes : List (Option E)) (hlen : modes.length = n)
    (hm : ∀ k (hk : k < modes.length), modes[k] = some (r[k]'(by omega))) (cs : Commits) :
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ b.1.length = n ∧
        b.2 = Flock.prodSub tA tB tC (Front.toVec n b.1))
      (hSumcheck 3 (claimL (partialSum (Flock.prodSub tA tB tC) r)) modes [])
      (Verifier.sumcheck (partialSum (Flock.prodSub tA tB tC) r 0 #v[]) 3 modes) cs := by
  have h := follows_sumcheck 3 (by norm_num) (claimL (partialSum (Flock.prodSub tA tB tC) r))
    modes [] cs (fun ext hext ↦ ?_) (fun ext hext ↦ ?_)
  · rw [claimL_nil] at h
    refine Follows.mono (fun cs' a b hb ↦ ?_) _ _ _ h
    obtain ⟨h1, h2, h3, h4⟩ := hb
    refine ⟨h1, h2, h3.trans hlen, ?_⟩
    rw [h4, List.nil_append, claimL_of_length _ (h3.trans hlen), partialSum_self]
  · have hj : ext.length < n := by omega
    refine (polyLE_evaluate (Flock.normRound tA tB tC r ext.length
      (Front.toVec ext.length ext))).congr fun x ↦ ?_
    rw [List.nil_append, claimL_append_singleton, Flock.evaluate_normRound _ _ _ _ hj]
  · have hj : ext.length < n := by omega
    have hw := Flock.weightedSum_normRound tA tB tC (fun _ : Unit ↦ r) () hj
      (Front.toVec ext.length ext)
    simp only [SumcheckRound.normalizedWeights, dite_eq_left hj, SumcheckRound.weightedSum,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Flock.evaluate_normRound _ _ _ _ hj] at hw
    simp only [List.nil_append, hm _ hext, RoundSplit, claimL_append_singleton]
    rw [claimL, ← hw, CharTwo.sub_eq_add]

/-! ## The lincheck's rounds -/

/-- **The lincheck's rounds.** In plain mode, the honest prover of the high sums of
`Σ_i M̃_i · Z̃_i` follows the program's rounds from the full sum, to `m` challenges and the
summand at the reversed challenges. -/
theorem follows_highSumcheck {s m : ℕ} (M Z : CMlPolynomialEval E (s + m)) (cs : Commits) :
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ b.1.length = m ∧
        b.2 = Flock.linFun M Z (Front.toVec m b.1).reverse)
      (hSumcheck 3 (claimL (highSum (Flock.linFun M Z))) (List.replicate m none) [])
      (Verifier.sumcheck (highSum (Flock.linFun M Z) 0 #v[]) 3 (List.replicate m none)) cs := by
  have h := follows_sumcheck 3 (by norm_num) (claimL (highSum (Flock.linFun M Z)))
    (List.replicate m none) [] cs (fun ext hext ↦ ?_) (fun ext hext ↦ ?_)
  · rw [claimL_nil] at h
    refine Follows.mono (fun cs' a b hb ↦ ?_) _ _ _ h
    obtain ⟨h1, h2, h3, h4⟩ := hb
    rw [List.length_replicate] at h3
    refine ⟨h1, h2, h3, ?_⟩
    rw [h4, List.nil_append, claimL_of_length _ h3, highSum_self]
  · rw [List.length_replicate] at hext
    refine (polyLE_evaluate (Flock.highRound M Z ext.length
      (Front.toVec ext.length ext))).congr fun x ↦ ?_
    rw [List.nil_append, claimL_append_singleton, Flock.evaluate_highRound _ _ hext]
  · have hj : ext.length < m := by simpa using hext
    have hw := Flock.weightedSum_highRound M Z hj (Front.toVec ext.length ext)
    simp only [SumcheckRound.weightedSum, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, one_mul, Flock.evaluate_highRound _ _ hj] at hw
    simp only [List.nil_append, List.getElem_replicate, RoundSplit, claimL_append_singleton]
    rw [claimL, ← hw]

end
end LeanVM.Protocol.EndToEnd.Complete
