/-
  LeanVM.Guest.B1.VerifySub.Inv1

  The phases `verify_sub` hands to its callees neither commit nor open (`QFree`).
-/

module

public import LeanVM.Guest.B1.VerifySub.Inv0

/-!
# The callees' phases are `QFree`

`gkrPhase`, `tablesSeg` and `verifyFlock` read and sample only, at the claimed values of the fixed
polynomials: their runs read a prefix of the stream, from any openings and roots (`qfree_frame`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- A leaf of a `QFree` proof. -/
syntax "qf_leaf" : tactic

macro_rules | `(tactic| qf_leaf) => `(tactic| exact QFree.ret _)
macro_rules | `(tactic| qf_leaf) => `(tactic| exact QFree.fail)
macro_rules | `(tactic| qf_leaf) => `(tactic| exact qfree_readE)
macro_rules | `(tactic| qf_leaf) => `(tactic| exact qfree_sampleE)
macro_rules | `(tactic| qf_leaf) => `(tactic| exact qfree_readN _)
macro_rules | `(tactic| qf_leaf) => `(tactic| exact qfree_sampleN _)
macro_rules | `(tactic| qf_leaf) => `(tactic| exact qfree_require _)
macro_rules | `(tactic| qf_leaf) => `(tactic| exact qfree_liftOption _)

/-- A `QFree` proof through binds, lets and pattern matches. -/
macro "qf" : tactic => `(tactic| repeat (first
  | qf_leaf
  | (refine QFree.bind' ?_ fun _ => ?_)
  | (refine QFree.bind ?_ fun _ => ?_)
  | (intro _)
  | split))

theorem qfree_roundPoly (count : ℕ) (claim : E) : ∀ o, QFree (sumcheckRoundPoly count claim o)
  | none => by unfold sumcheckRoundPoly; qf
  | some _ => by unfold sumcheckRoundPoly; qf

macro_rules | `(tactic| qf_leaf) => `(tactic| exact qfree_roundPoly _ _ _)

theorem qfree_sumcheck (count : ℕ) : ∀ (eqs : List (Option E)) (claim : E),
    QFree (sumcheck claim count eqs)
  | [], _ => by unfold sumcheck; qf
  | e :: es, claim => by
    unfold sumcheck
    refine QFree.bind' (qfree_roundPoly _ _ _) fun _ => QFree.bind' qfree_sampleE fun _ =>
      QFree.bind' (qfree_sumcheck count es _) fun _ => ?_
    qf

macro_rules | `(tactic| qf_leaf) => `(tactic| exact qfree_sumcheck _ _ _)

theorem qfree_gkrStep (step : ℕ) (s : GkrState) : QFree (gkrStep step s) := by
  unfold gkrStep; qf

macro_rules | `(tactic| qf_leaf) => `(tactic| exact qfree_gkrStep _ _)

theorem qfree_gkrLayers : ∀ (n : ℕ) (s : GkrState), QFree (gkrLayers n s)
  | 0, _ => by unfold gkrLayers; qf
  | 1, _ => by
    unfold gkrLayers
    exact QFree.bind' (qfree_gkrStep _ _) fun _ => qfree_gkrLayers 0 _
  | n + 2, _ => by
    unfold gkrLayers
    split
    · exact QFree.bind' (qfree_gkrStep _ _) fun _ => qfree_gkrLayers (n + 1) _
    · exact QFree.bind' (qfree_gkrStep _ _) fun _ => qfree_gkrLayers n _

macro_rules | `(tactic| qf_leaf) => `(tactic| exact qfree_gkrLayers _ _)

theorem qfree_gkrPhase (depth : ℕ) : QFree (gkrPhase depth) := by
  unfold gkrPhase verifyGkrGrandProducts; qf

theorem qfree_claimed_bytecode (c : FixedClaims) (w : List K) (pt : List E) :
    QFree ((Evaluations.claimed c).bytecode w pt) := by
  unfold Evaluations.claimed; qf

theorem qfree_claimed_matrices (c : FixedClaims) (alpha zSkip : E) (chiIn chiInPrime s : List E) :
    QFree ((Evaluations.claimed c).matrices alpha zSkip chiIn chiInPrime s) := by
  unfold Evaluations.claimed; qf

macro_rules | `(tactic| qf_leaf) => `(tactic| exact qfree_claimed_bytecode _ _ _)
macro_rules | `(tactic| qf_leaf) => `(tactic| exact qfree_claimed_matrices _ _ _ _ _ _)

theorem qfree_tableTerms (cp fp pt : List E) : ∀ (rows : List (Table × ℕ × List Form × E))
    (cursor : ℕ) (final : E) (claims : List ColumnClaim),
    QFree (tableTerms cp fp pt rows cursor final claims)
  | [], _, _, _ => by unfold tableTerms; qf
  | (_, _, _, _) :: rest, _, _, _ => by
    unfold tableTerms
    exact QFree.bind' (qfree_readN _) fun _ => qfree_tableTerms cp fp pt rest _ _ _

macro_rules | `(tactic| qf_leaf) => `(tactic| exact qfree_tableTerms _ _ _ _ _ _ _)

theorem qfree_tablesSeg (c : FixedClaims) (layout : Layout) (pi : Digest) (alphas : List E)
    (beta : E) (point values : List E) :
    QFree (tablesSeg (.claimed c) layout pi alphas beta point values) := by
  unfold tablesSeg busRest tablePhase tableSumcheck publicInputPhase; qf

theorem qfree_verifyFlock (c : FixedClaims) (logN : ℕ) : QFree (verifyFlock (.claimed c) logN) := by
  unfold verifyFlock verifyFlockZerocheck verifyFlockLincheck; qf

end
end LeanVM.Guest.B1.VerifySub
