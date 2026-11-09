/-
  LeanVM.Protocol.EndToEnd.Front.BusGkrArk

  The grand-product argument's step-level facts the verifier program's doom uses: the escape of a
  combination challenge, the hand-over from a step's output relation to the next step's input
  relation or to the argument's output relation, and the sumcheck family's consistency and
  soundness, stated publicly.
-/

module

public import LeanVM.Protocol.ToArkLib.GrandProductSecurity

/-!
# The grand product's relations, step by step

`gkrSecurity` (`LeanVM.Protocol.ToArkLib.GrandProductSecurity`) is appended from the steps'
securities, some of whose facts are private there. The verifier program's doom is stated on the
same relations (`familyT`'s stages, `childRelT`, `stepOutT`, `layerRel`, `relOut`), and needs:

* `familyT_consistent'`, `familyT_sound'`: the layer's tracked family is consistent and sound, so
  `SumcheckRound.drawChallengeSecurity` applies to its rounds;
* `card_interpNext_le'`: a combination challenge restores `childRelT` at one value at most;
* `interpDone_mem_stepOutT_iff'`: the interpolated statement is in the step's output relation
  exactly when the statement before it is in `childRelT` after all the challenges;
* `stepOutT_constTrack_iff`: inside the argument, the step's output relation is the next layer's
  relation; `stepOutT_progTrack_iff`: at the last step, it is the argument's output relation.

The first four restate private facts of `GrandProductSecurity` with the same proofs.
-/

namespace LeanVM.Protocol.Gkr

open CompPoly CMlPolynomialEval OracleComp OracleSpec
open scoped NNReal ENNReal

@[expose] public section

variable {F : Type} [Field F] [Finite F] [BEq F] [LawfulBEq F] [DecidableEq F]
  [SampleableType F] {X : Type} {ι : Type} {O : ι → Type} [∀ i, OracleInterface (O i)]
  (nside μ : ℕ) (leaves : X → (∀ i, O i) → Fin nside → CMlPolynomialEval F μ)
  (riders : X → (∀ i, O i) → List (Σ τ : Fin (μ + 1), CMlPolynomialEval F τ)) (ρ m : ℕ)

omit [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)] in
/-- The honest polynomials of the tracked family are consistent. -/
theorem familyT_consistent' (T : RiderTrack μ riders ρ m) :
    (familyT nside μ leaves riders ρ m T).Consistent m :=
  ⟨(family_honest nside μ leaves riders ρ m).check, (family_honest nside μ leaves riders ρ m).next⟩

omit [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)] in
/-- The tracked family's invariant is sound. -/
theorem familyT_sound' (T : RiderTrack μ riders ρ m) :
    (familyT nside μ leaves riders ρ m T).Sound m :=
  fun _ _ cv _ hinv ↦ (T.inv_escape _ _ _ cv hinv).trans Nat.one_le_two_pow

omit [BEq F] [LawfulBEq F] [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)] in
/-- A statement outside the relation after `i` combination challenges is inside it after one more
at one challenge at most. -/
theorem card_interpNext_le' (T : RiderTrack μ riders ρ m) {i : ℕ}
    (s : InterpStmt X F nside m ρ i) (o : ∀ j, O j)
    (hs : ((s, o), ()) ∉ childRelT nside μ leaves riders ρ m T i) :
    Nat.card {c // ((interpNext nside ρ m s c, o), ()) ∈
      childRelT nside μ leaves riders ρ m T (i + 1)} ≤ 1 := by
  have := Fintype.ofFinite F
  classical
  rw [natCard_subtype_eq_card_filter]
  by_cases hinv : T.invU s.1.1 o s.1.2.1 i s.2
  · have hne : ∃ t, ¬ RestrictedZero
        (diffTable (s.1.2.2 t) (children nside μ leaves ρ m s.1.1 o s.1.2.1 t))
        (combPartial s.2) := by
      by_contra h
      exact hs ⟨hinv, fun t ↦ by_contra fun ht ↦ h ⟨t, ht⟩⟩
    obtain ⟨t, ht⟩ := hne
    refine (Finset.card_le_card fun c hc ↦ ?_).trans
      (card_filter_restrictedZero_update_le _ (combPartial s.2) i ht)
    rw [Finset.mem_filter] at hc ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have := hc.2.2 t
    simp only [show (interpNext nside ρ m s c).2 = s.2.push c from rfl, combPartial,
      Partial.ofVector_push, Nat.zero_add] at this
    exact this
  · refine (Finset.card_le_card fun c hc ↦ ?_).trans
      ((natCard_subtype_eq_card_filter _).symm.trans_le
        (T.invU_escape _ _ _ i s.2 hinv))
    rw [Finset.mem_filter] at hc ⊢
    exact ⟨Finset.mem_univ _, hc.2.1⟩

omit [BEq F] [LawfulBEq F] [DecidableEq F] [SampleableType F]
  [∀ i, OracleInterface (O i)] in
/-- The interpolated statement is in the step's output relation exactly when the statement before
it is in the relation after all `ρ` combination challenges. -/
theorem interpDone_mem_stepOutT_iff' (T : RiderTrack μ riders ρ m)
    (s : InterpStmt X F nside m ρ ρ) (o : ∀ i, O i) :
    ((interpDone nside ρ m s, o), ()) ∈ stepOutT nside μ leaves riders ρ m T ↔
      ((s, o), ()) ∈ childRelT nside μ leaves riders ρ m T ρ := by
  show (T.out s.1.1 o (Vector.cast (Nat.add_comm ρ m) (s.2 ++ s.1.2.1)) ∧
    ∀ t, evalMle (layerTable (leaves s.1.1 o t) (m + ρ))
      (Vector.cast (Nat.add_comm ρ m) (s.2 ++ s.1.2.1)) = evalMle (s.1.2.2 t) s.2) ↔
    (T.invU s.1.1 o s.1.2.1 ρ s.2 ∧ ∀ t, RestrictedZero
      (diffTable (s.1.2.2 t) (children nside μ leaves ρ m s.1.1 o s.1.2.1 t)) (combPartial s.2))
  rw [T.out_iff]
  refine and_congr Iff.rfl (forall_congr' fun t ↦ ?_)
  rw [restrictedZero_of_all _ (combPartial s.2) s.2
      (fun k hk ↦ by simp [combPartial, Partial.ofVector, hk]), evalMle_diffTable,
    sub_eq_zero, evalMle_cast_append, eq_comm]
  exact Iff.rfl

omit [BEq F] [LawfulBEq F] [DecidableEq F] [SampleableType F]
  [∀ i, OracleInterface (O i)] in
/-- Inside the argument, a step's output relation is the next layer's relation. -/
theorem stepOutT_constTrack_iff (s : LayerStmt X F nside (m + ρ)) (o : ∀ i, O i) :
    ((s, o), ()) ∈ stepOutT nside μ leaves riders ρ m (constTrack μ riders ρ m) ↔
      ((s, o), ()) ∈ layerRel nside μ leaves riders (m + ρ) :=
  Iff.rfl

omit [BEq F] [LawfulBEq F] [DecidableEq F] [SampleableType F]
  [∀ i, OracleInterface (O i)] in
/-- At the last step, a step's output relation is the argument's output relation, across the
equality of layers. -/
theorem stepOutT_progTrack_iff (h : m + ρ = μ) (s : LayerStmt X F nside (m + ρ)) (o : ∀ i, O i) :
    ((s, o), ()) ∈ stepOutT nside μ leaves riders ρ m (progTrack μ riders ρ m h) ↔
      (((s.1, (Vector.cast h s.2.1, s.2.2)), o), ()) ∈ relOut nside μ leaves riders := by
  show ((∀ r ∈ riders s.1 o, evalMle r.2 (lowPoint (Vector.cast h s.2.1) r.1) = 0) ∧
    ∀ t, evalMle (layerTable (leaves s.1 o t) (m + ρ)) s.2.1 = s.2.2 t) ↔
    ((∀ t, evalMle (leaves s.1 o t) (Vector.cast h s.2.1) = s.2.2 t) ∧
      ∀ r ∈ riders s.1 o, evalMle r.2 (lowPoint (Vector.cast h s.2.1) r.1) = 0)
  rw [and_comm]
  refine and_congr (forall_congr' fun t ↦ ?_) Iff.rfl
  subst h
  simp

end
end LeanVM.Protocol.Gkr
