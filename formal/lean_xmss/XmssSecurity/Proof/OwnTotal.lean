module

public import XmssSecurity.Proof.OwnBudget

@[expose] public section

/-!
# The whole game's hash calls from the adversary's own

A static bound on the adversary's own hash calls and on its signing requests bounds the hash calls of
its run against a signing oracle, each request charged the signer's worst case (`OwnReal.lean` applies
it to the real game).
-/

open OracleComp OracleSpec

namespace XmssSecurity

/-- The world queries of a computation that also asks a second oracle. -/
def OnWorld {ιW ιS : Type} (pW : ιW → Prop) : ιW ⊕ ιS → Prop
  | .inl w => pW w
  | .inr _ => False

instance {ιW ιS : Type} (pW : ιW → Prop) [DecidablePred pW] : DecidablePred (OnWorld (ιS := ιS) pW) :=
  fun t => match t with
    | .inl w => inferInstanceAs (Decidable (pW w))
    | .inr _ => isFalse id

/-- The requests to the second oracle. -/
def OnSecond {ιW ιS : Type} : ιW ⊕ ιS → Prop := fun t => t matches .inr _

instance {ιW ιS : Type} : DecidablePred (OnSecond (ιW := ιW) (ιS := ιS)) := fun t => by
  unfold OnSecond; infer_instance

theorem onWorld_inl {ιW ιS : Type} (pW : ιW → Prop) (w : ιW) : OnWorld (ιS := ιS) pW (.inl w) ↔ pW w :=
  Iff.rfl

theorem not_onWorld_inr {ιW ιS : Type} (pW : ιW → Prop) (r : ιS) : ¬OnWorld pW (.inr r : ιW ⊕ ιS) := id

theorem not_onSecond_inl {ιW ιS : Type} (w : ιW) : ¬OnSecond (.inl w : ιW ⊕ ιS) := by
  simp [OnSecond]

theorem onSecond_inr {ιW ιS : Type} (r : ιS) : OnSecond (.inr r : ιW ⊕ ιS) := by
  simp [OnSecond]

/-- **Static composition.** A computation making at most `q` world queries in `pW` and `s` requests,
run against a handler that forwards world queries and answers a request with at most `B` queries in
`pW`, makes at most `q + s * B` of them. -/
theorem isQueryBoundP_simulateQ_writer_run {ιW ιS : Type} {W : OracleSpec ιW} {S : OracleSpec ιS}
    (pW : ιW → Prop) [DecidablePred pW] {ι₀ : Type} {S₀ : OracleSpec ι₀}
    (so : QueryImpl (W + S) (WriterT (QueryLog S₀) (OracleComp W))) (B : ℕ)
    (hfwd : ∀ t, IsQueryBoundP (so (.inl t)).run pW (if pW t then 1 else 0))
    (hsign : ∀ t, IsQueryBoundP (so (.inr t)).run pW B) {α : Type} (comp : OracleComp (W + S) α) :
    ∀ (q s : ℕ), IsQueryBoundP comp (OnWorld pW) q → IsQueryBoundP comp OnSecond s →
      IsQueryBoundP (simulateQ so comp).run pW (q + s * B) := by
  induction comp using OracleComp.inductionOn with
  | pure value =>
      intro q s _ _
      exact isQueryBoundP_pure (p := pW) _ _
  | query_bind t next ih =>
      intro q s hq hs
      rw [isQueryBoundP_query_bind_iff] at hq hs
      rw [simulateQ_query_bind]
      change IsQueryBoundP ((so t).run >>= fun x => (fun y => (y.1, x.2 ++ y.2)) <$>
        (simulateQ so (next x.1)).run) pW _
      cases t with
      | inl w =>
          rw [ite_eq_right (not_onSecond_inl w)] at hs
          by_cases hw : pW w
          · rw [ite_eq_left ((onWorld_inl pW w).2 hw)] at hq
            have hq1 := hq.1.resolve_left (not_not.2 ((onWorld_inl pW w).2 hw))
            refine (isQueryBoundP_bind (ob := fun x => (fun y => (y.1, x.2 ++ y.2)) <$>
              (simulateQ so (next x.1)).run) (hfwd w) fun x _ =>
                (isQueryBoundP_map_iff _ _ _).2 (ih x.1 _ _ (hq.2 x.1) (hs.2 x.1))).mono ?_
            rw [ite_eq_left hw]
            omega
          · rw [ite_eq_right (fun h => hw ((onWorld_inl pW w).1 h))] at hq
            refine (isQueryBoundP_bind (ob := fun x => (fun y => (y.1, x.2 ++ y.2)) <$>
              (simulateQ so (next x.1)).run) (hfwd w) fun x _ =>
                (isQueryBoundP_map_iff _ _ _).2 (ih x.1 _ _ (hq.2 x.1) (hs.2 x.1))).mono ?_
            rw [ite_eq_right hw]
            omega
      | inr r =>
          rw [ite_eq_right (not_onWorld_inr pW r)] at hq
          rw [ite_eq_left (onSecond_inr r)] at hs
          have hs1 := hs.1.resolve_left (not_not.2 (onSecond_inr r))
          refine (isQueryBoundP_bind (ob := fun x => (fun y => (y.1, x.2 ++ y.2)) <$>
            (simulateQ so (next x.1)).run) (hsign r) fun x _ =>
              (isQueryBoundP_map_iff _ _ _).2 (ih x.1 _ _ (hq.2 x.1) (hs.2 x.1))).mono ?_
          obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
          simp only [Nat.add_sub_cancel, Nat.add_mul, one_mul]
          omega

/-! ## Lifted computations -/

theorem isQueryBoundP_liftM_probComp {α : Type} (computation : ProbComp α) (n : ℕ) :
    IsQueryBoundP (liftM computation : OracleComp OracleWorld α) IsWorldHashQuery n := by
  have hall : IsQueryBoundP computation (fun _ => False) n :=
    ((isQueryBoundP_congr_pred (fun _ => by simp)).mp ((isQueryBoundP_zero_iff computation (fun _ => True)).2
      (allQueriesSatisfy_of_forall (fun _ => trivial) _))).mono
      (Nat.zero_le _)
  exact IsQueryBoundP.liftComp_subSpec (q := IsWorldHashQuery) (fun _ => iff_of_false not_false
    (by simp [IsWorldHashQuery])) hall

theorem isAdvHashAction_iff (t : (OracleWorld + SigningSpec).Domain) :
    IsAdvHashAction t ↔ OnWorld IsWorldHashQuery t := by
  rcases t with (_ | _) | _ <;> simp [IsAdvHashAction, OnWorld, IsWorldHashQuery]

end XmssSecurity
