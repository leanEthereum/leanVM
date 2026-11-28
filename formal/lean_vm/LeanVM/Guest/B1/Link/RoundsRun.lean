/-
  LeanVM.Guest.B1.Link.RoundsRun

  A chain of the guest's sum-check rounds is a run of the Statement's `sumcheck`.
-/

module

public import LeanVM.Guest.B1.Link.RoundRun

/-!
# Chains of rounds

A round's state is the carried capacity, the cursor and the claim (`RSt`, the records
`link_rounds` keeps). `RoundStep` is what one `link_round` establishes (`lrRound_sound`'s
conclusion); `RoundChain` a sequence of them. `chain_runsTo`: a chain of `k` rounds reads the
words at the cursor, one after the other, and is a run of `sumcheck claim (nt + 2) (replicate k
none)` from the first capacity to the last, its point the rounds' challenges.
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- A round's state: the carried capacity, the cursor, the claim. -/
structure RSt where
  cap : List E
  cur : E
  cl : E

/-- **One round** of `nt` tail coefficients and `bits` of grind, from `st` to `st'` with the
challenge `y`. -/
def RoundStep (rd : Reader) (nt bits : ℕ) (st : RSt) (y : E) (st' : RSt) : Prop :=
  ∃ (c0 : E) (tail : List E) (n : E), tail.length = nt ∧
    ReadsAt rd st.cur (c0 :: tail ++ grindWords bits n) ∧
    (((⟨st.cap, []⟩ : Fs).absorb c0 dsObserve).absorbAll tail dsObserve).GrindOk bits n ∧
    (((⟨st.cap, []⟩ : Fs).absorb c0 dsObserve).absorbAll tail dsObserve).grindSqueeze bits n =
      (y, ⟨st'.cap, []⟩) ∧
    st'.cur = st.cur * gen ^ (nt + 1 + (grindWords bits n).length) ∧
    st'.cl = polyEval (c0 :: (st.cl + sumE tail) :: tail) y

/-- A chain of rounds, each challenge with the state after it. -/
def RoundChain (rd : Reader) (nt bits : ℕ) : RSt → List (E × RSt) → Prop
  | _, [] => True
  | st, (y, st') :: l => RoundStep rd nt bits st y st' ∧ RoundChain rd nt bits st' l

/-- The state after a chain. -/
def chainLast : RSt → List (E × RSt) → RSt
  | st, [] => st
  | _, (_, st') :: l => chainLast st' l

theorem readsAt_append_shift {rd : Reader} {p : E} {l1 l2 : List E} (h1 : ReadsAt rd p l1)
    (h2 : ReadsAt rd (p * gen ^ l1.length) l2) : ReadsAt rd p (l1 ++ l2) := by
  intro k hk
  rcases Nat.lt_or_ge k l1.length with h | h
  · rw [List.getElem_append_left h]; exact h1 k h
  · rw [List.getElem_append_right h]
    have := h2 (k - l1.length) (by simp at hk; omega)
    rwa [loadHolds_mul_gen_pow, Nat.add_sub_cancel' h] at this

theorem chainLast_append (st : RSt) (l : List (E × RSt)) (y : E) (st' : RSt) :
    chainLast st (l ++ [(y, st')]) = st' := by
  induction l generalizing st with
  | nil => rfl
  | cons p l ih => exact ih p.2

theorem roundChain_append {rd : Reader} {nt bits : ℕ} : ∀ {st : RSt} {l1 l2 : List (E × RSt)},
    RoundChain rd nt bits st l1 → RoundChain rd nt bits (chainLast st l1) l2 →
      RoundChain rd nt bits st (l1 ++ l2)
  | _, [], _, _, h2 => h2
  | _, (_, _) :: _, _, ⟨hs, h1⟩, h2 => ⟨hs, roundChain_append h1 h2⟩

theorem chainLast_append' (st : RSt) (l1 l2 : List (E × RSt)) :
    chainLast st (l1 ++ l2) = chainLast (chainLast st l1) l2 := by
  induction l1 generalizing st with
  | nil => rfl
  | cons p l ih => exact ih p.2

/-- **A chain of rounds is a run of `sumcheck`.** -/
theorem chain_runsTo {rd : Reader} {nt bits : ℕ} (hbits : grindingBits (nt + 1) = bits) :
    ∀ {st : RSt} {l : List (E × RSt)}, RoundChain rd nt bits st l →
      ∃ ws : List E, ReadsAt rd st.cur ws ∧ (chainLast st l).cur = st.cur * gen ^ ws.length ∧
        RunsTo (sumcheck st.cl (nt + 2) (List.replicate l.length none)) ⟨st.cap, []⟩ ws
          (l.map Prod.fst, (chainLast st l).cl) ⟨(chainLast st l).cap, []⟩
  | st, [], _ => ⟨[], readsAt_nil _ _, by simp [chainLast], runsTo_ret _ _⟩
  | st, (y, st') :: l, ⟨⟨c0, tail, n, htl, hr, hok, hgs, hcur, hcl⟩, hc⟩ => by
    obtain ⟨ws, hws, hlast, hrun⟩ := chain_runsTo hbits hc
    have e2 : nt + 2 - 1 = nt + 1 := rfl
    rw [← hbits, ← e2] at hok hgs
    have hround := runsTo_sumcheck_round ⟨st.cap, []⟩ st.cl c0 tail (nt + 2) (by rw [htl]; rfl) n hok
      (rest := List.replicate l.length none) (h2 := by rw [hgs]; rw [← hcl]; exact hrun)
    rw [hgs] at hround
    refine ⟨c0 :: tail ++ grindWords (grindingBits (nt + 2 - 1)) n ++ ws, ?_, ?_, ?_⟩
    · refine readsAt_append_shift (by rw [e2, hbits]; exact hr) ?_
      rw [e2, hbits]
      have : (c0 :: tail ++ grindWords bits n).length = nt + 1 + (grindWords bits n).length := by
        simp [htl]; ring
      rw [this, ← hcur]
      exact hws
    · show (chainLast st' l).cur = _
      rw [hlast, hcur, e2, hbits, mul_assoc, ← pow_add]
      congr 2
      simp [htl]
      ring
    · exact hround

end
end LeanVM.Guest.B1.Link
