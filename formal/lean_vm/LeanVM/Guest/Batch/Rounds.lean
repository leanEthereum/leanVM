/-
  LeanVM.Guest.Batch.Rounds

  The batching sumcheck's soundness, round by round: a false claim and a true final value leave
  a round whose challenge is a root of a nonzero quadratic that the round's prefix fixes.
-/

module

public import LeanVM.Guest.Batch.Run

/-!
# The batching sumcheck, round by round

`Node.batchRounds` runs a sumcheck's rounds on the duplex sponge (`rsRun`, `rsSt`): round `j`
absorbs `g(1)` and `g(∞)`, squeezes the challenge `r_j`, and folds the claim to `g(r_j)`, the
round polynomial (`roundPoly`) with `g(0) = claim + g(1)`, so `g(0) + g(1)` is the claim.

`rounds_sound`: if the first claim is not the cube sum of `f`, and the final claim is `f` at the
challenges, then some round `j` is bad (`BadRound`): the round's polynomial is not the cube sum of
`f` along the round's coordinate after the earlier challenges, and `r_j` is a root of their
difference. That difference is fixed before `r_j` is squeezed (it depends on the claim before the
round, the round's message and the earlier challenges), and for `f` quadratic along each
coordinate it is a nonzero quadratic, with at most two roots (`badRound_roots`).
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The rounds' challenges from `claim` at the sponge `sp`. -/
def roundChallenges (rounds : List (E × E)) (claim : E) (sp : Sponge) : List E :=
  (rsRun rounds claim sp).1.1

/-- The gap of round `j` at `x`: the round's polynomial less the cube sum of `f` along the
round's coordinate after the earlier challenges. -/
def roundGap (n : ℕ) (f : List E → E) (rounds : List (E × E)) (claim : E) (sp : Sponge) (j : ℕ)
    (x : E) : E :=
  sumcheckRoundPolynomial (rsSt rounds claim sp j).1 (rounds.getD j (0, 0)) x -
    cubeSum n f ((roundChallenges rounds claim sp).take j ++ [x])

/-- **Round `j` is bad** for `f`: its gap is not zero, and the round's challenge is a root of it. -/
def BadRound (n : ℕ) (f : List E → E) (rounds : List (E × E)) (claim : E) (sp : Sponge) (j : ℕ) :
    Prop :=
  (∃ x, roundGap n f rounds claim sp j x ≠ 0) ∧
    roundGap n f rounds claim sp j ((roundChallenges rounds claim sp).getD j 0) = 0

/-- **The sumcheck's soundness, round by round**: a first claim that is not the cube sum, and a
final claim that is `f` at the challenges, leave a bad round. -/
theorem rounds_sound {n : ℕ} {f : List E → E} {rounds : List (E × E)} {claim : E} {sp : Sponge}
    (hn : rounds.length = n)
    (hfinal : (rsRun rounds claim sp).1.2 = f (roundChallenges rounds claim sp))
    (hclaim : claim ≠ cubeSum n f []) :
    ∃ j < n, BadRound n f rounds claim sp j := by
  set rs := roundChallenges rounds claim sp with hrs
  have hrsl : rs.length = n := by simp [hrs, roundChallenges, rsRun_eq, hn]
  have hrj : ∀ j < n, rs.getD j 0 = challengeOf (rsSt rounds claim sp (j + 1)).2.state := by
    intro j hj
    simp [hrs, roundChallenges, rsRun_eq, hn, hj]
  by_contra hno'
  have hno : ∀ j < n, ¬BadRound n f rounds claim sp j := fun j hj hb ↦ hno' ⟨j, hj, hb⟩
  have key : ∀ j ≤ n, (rsSt rounds claim sp j).1 ≠ cubeSum n f (rs.take j) := by
    intro j
    induction j with
    | zero => intro _; simpa [rsSt] using hclaim
    | succ j ih =>
      intro hj
      have hj' : j < n := by omega
      have hne : ∃ x, roundGap n f rounds claim sp j x ≠ 0 := by
        by_contra hz'
        have hz : ∀ x, roundGap n f rounds claim sp j x = 0 := fun x ↦ by
          by_contra hx
          exact hz' ⟨x, hx⟩
        apply ih hj'.le
        have h0 := hz 0
        have h1 := hz 1
        simp only [roundGap, sumcheckRoundPolynomial, sub_eq_zero] at h0 h1
        rw [cubeSum_split (by simp; omega), ← h0, ← h1]
        linear_combination (-((rsSt rounds claim sp j).1 + (rounds.getD j (0, 0)).2 +
          2 * (rounds.getD j (0, 0)).1)) * Whir.Complete.two_eq_zero_E
      have hg : roundGap n f rounds claim sp j (rs.getD j 0) ≠ 0 := fun h ↦ hno j hj' ⟨hne, h⟩
      rw [roundGap, sub_ne_zero, hrj j hj'] at hg
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
        ← List.getD_eq_getElem (d := 0)]
      rw [hrj j hj']
      exact hg
  apply key n le_rfl
  rw [List.take_of_length_le hrsl.le, cubeSum_full hrsl, ← hfinal, rsRun_eq, hn]

end
end LeanVM.Guest.Batch
