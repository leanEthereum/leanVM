module

public import LeanDa.Birthday

@[expose] public section

/-!
# Wagner's adversary with `H` as an oracle

Wagner's adversary for a table `h` of `H` (`advH h`) answers `H` from `h` on short strings. The
same adversary with those answers left as queries of `XS` (`advX`) gives it back when they are
answered by `h` (`advH_eq`), and makes at most `Q + 1` of them for an RPM adversary of `Q`
permutation calls (`isWeightBound_advX`): one for the label, at most one per call of the RPM
adversary.

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA: it bounds his
collision terms.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.SeedDuplex LeanDa.Fork PFunctor PqDas
open Common.Duplex (GSpec hP gaP VSpec toV)
open scoped ENNReal

namespace LeanDa

/-- **`H` from a table in Wagner's world, short strings as queries of `XS`** (`tImpl`). -/
noncomputable def tImplX :
    QueryImpl (unifSpec + TSpec) (StateT HCache (OracleComp (WSpec + XS)))
  | .inl k => StateT.mk fun c ↦ (·, c) <$> liftL (liftM (WSpec.query (.inl k)))
  | .inr (.inl d) => StateT.mk fun c ↦ (·, c) <$> liftL (liftM (WSpec.query (.inr d)))
  | .inr (.inr a) =>
      if ha : shortP a then
        StateT.mk fun c ↦ (·, c) <$> FreeM.lift (P := (WSpec + XS).toPFunctor) (.inr ⟨a, ha⟩)
      else StateT.mk fun c ↦ liftL (liftM (((roSpec (List UInt8) DigestBytes).randomOracle a).run c))

theorem col_tImplX (h : HTab) (t : (unifSpec + TSpec).Domain) (s : HCache) :
    simulateQ (col h) ((tImplX t).run s) = (tImpl h t).run s := by
  rcases t with k | d | a
  · change simulateQ (col h) ((·, s) <$> liftL _) = _
    rw [simulateQ_map, simulateQ_col_liftL]
    rfl
  · change simulateQ (col h) ((·, s) <$> liftL _) = _
    rw [simulateQ_map, simulateQ_col_liftL]
    rfl
  · by_cases ha : shortP a
    · simp only [tImplX, tImpl, ha, ↓reduceDIte, StateT.run_mk]
      rfl
    · simp only [tImplX, tImpl, ha, ↓reduceDIte, StateT.run_mk]
      exact simulateQ_col_liftL h _

section Adversary

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
      Proof rel)

/-- **Wagner's adversary with `H` on short strings as queries of `XS`** (`advH`). -/
noncomputable def advX (A : CodeBindingAdvB r Crs Proof) (ck : Unit × Crs) :
    OracleComp (WSpec + XS) ((Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)) :=
  (simulateQ tImplX (simulateQ (swapImpl ∘ₛ toV) (advSim r A (fixCrs r ps ck.2)))).run' ∅

/-- **Answered by `h`, it is Wagner's adversary for the table `h`.** -/
theorem advH_eq (A : CodeBindingAdvB r Crs Proof) (h : HTab) (ck : Unit × Crs) :
    advH r ps A h ck = simulateQ (col h) (advX r ps A ck) := by
  rw [advH, advX, phiG, QueryImpl.simulateQ_compose, StateT.run'_eq, StateT.run'_eq,
    simulateQ_map, run_simulateQ_col_of h _ _ (col_tImplX h)]

/-- Calls of `H` in the simulated world. -/
def hCallsG : (unifSpec + GSpec (List UInt8) DigestBytes Common.DigestBytes Draw nLabels).Domain → ℕ
  | .inr (.inl _) => 1
  | _ => 0

/-- Calls of `H` in Wagner's world with `H` a table. -/
def tCalls : (unifSpec + TSpec).Domain → ℕ
  | .inr (.inr _) => 1
  | _ => 0

/-- **The simulated adversary calls `H` at most `Q` times**, for an RPM adversary of `Q`
permutation calls. -/
theorem isWeightBound_advS2_h (A : CodeBindingAdvB r Crs Proof) (Q : ℕ)
    (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) (crs : Crs)
    (hcrs : crs ∈ support ps.setup) :
    QueryCostAtMost (advS2 keccakPadding KState.zero (A ((), crs))) hCalls Q := by
  rw [permCalls2_eq] at hQ
  have hX : QueryCostAtMost (simulateQ (hInF (E := KRest) (C := KCap)) (liftM ps.setup) >>= fun x ↦
      advS2 keccakPadding KState.zero (A ((), x)) >>= fun a ↦ codeBindingPost r ps x a)
      hCalls Q := by
    rw [← shadow_rpmGame2, StateT.run'_eq]
    exact isWeightBound_map _ (isWeightBound_run_simulateQ _ _ _ isWeightBound_shadowImpl hQ _)
  rw [simulateQ_liftM_of_coins _ (fun _ ↦ rfl)] at hX
  have hmem : crs ∈ support (liftM ps.setup : OracleComp Rom2 Crs) := by
    change crs ∈ support (OracleComp.liftComp ps.setup _)
    rwa [OracleComp.support_liftComp]
  exact (hX.of_bind_mem_support hmem).of_bind

theorem isWeightBound_simImpl_h (t : Rom2.Domain) (s : SimSt Common.DigestBytes KState Common.DigestBytes nLabels) :
    QueryCostAtMost ((simImpl daDuplex hP gaP t).run s) hCallsG (hCalls t) := by
  have hu : ∀ {β : Type} (p : ProbComp β),
      QueryCostAtMost (liftM p : OracleComp (unifSpec + GSpec (List UInt8) DigestBytes Common.DigestBytes Draw nLabels) β)
        hCallsG 0 :=
    fun p ↦ isWeightBound_liftM_probComp hCallsG (fun _ ↦ rfl) p
  rcases t with k | m | x
  · simp only [simImpl, StateT.run_monadLift, monadLift_self]
    exact (hu _).bind fun _ ↦ isWeightBound_pure _ _ 0
  · simp only [simImpl, StateT.run_mk]
    exact ((isWeightBound_query hCallsG (.inr (.inl m))).bind fun _ ↦ isWeightBound_pure _ _ 0)
  · simp only [simImpl, StateT.run_mk]
    split
    · trivial
    · refine (QueryCostAtMost.bind (b := 0) ?_ fun _ ↦ isWeightBound_pure _ _ 0)
      unfold freshAns
      split
      · split
        · exact (isWeightBound_map _ (hu _)).mono (Nat.zero_le _)
        · exact ((isWeightBound_query hCallsG (.inr (.inr _))).bind fun _ ↦
            (hu _).bind fun _ ↦ isWeightBound_pure _ _ 0).mono (Nat.zero_le _)
      · exact (isWeightBound_map _ (hu _)).mono (Nat.zero_le _)

/-- **Wagner's adversary with `H` as queries makes at most `Q + 1` of them.** -/
theorem isWeightBound_advX (A : CodeBindingAdvB r Crs Proof) (Q : ℕ)
    (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) (ck : Unit × Crs) :
    QueryCostAtMost (advX r ps A ck) xCalls (Q + 1) := by
  have hB := isWeightBound_advS2_h r ps A Q hQ _ (fixCrs_mem r ps ck.2)
  have hP : QueryCostAtMost (Common.SeedDuplex.hQ (St := KState) daDuplex.label >>= fun _ ↦
      advS2 keccakPadding KState.zero (A ((), fixCrs r ps ck.2))) hCalls (1 + Q) :=
    (isWeightBound_query hCalls (.inr (.inl daDuplex.label))).bind fun _ ↦ hB
  have hS := isWeightBound_run_simulateQ _ _ _ isWeightBound_simImpl_h hP SimSt.init
  have hV : QueryCostAtMost (simulateQ (swapImpl ∘ₛ toV) (advSim r A (fixCrs r ps ck.2))) tCalls
      (1 + Q) := by
    refine isWeightBound_simulateQ _ hCallsG tCalls (fun t ↦ ?_) ?_
    · rcases t with k | m | ⟨d, j⟩
      · simp only [QueryImpl.apply_compose, toV, simulateQ_spec_query, swapImpl]
        exact isWeightBound_query tCalls (.inl k)
      · simp only [QueryImpl.apply_compose, toV, simulateQ_spec_query, swapImpl]
        exact isWeightBound_query tCalls (.inr (.inr m))
      · simp only [QueryImpl.apply_compose, toV, simulateQ_map, simulateQ_spec_query, swapImpl]
        exact (isWeightBound_map _ (isWeightBound_query tCalls (.inr (.inl d)))).mono (Nat.zero_le _)
    · rw [advSim, StateT.run'_eq]
      exact isWeightBound_map _ hS
  rw [advX, StateT.run'_eq]
  refine isWeightBound_map _ ((isWeightBound_run_simulateQ _ tCalls xCalls (fun t s ↦ ?_) hV ∅).mono
    (by omega))
  rcases t with k | d | a
  · exact isWeightBound_map _ (isWeightBound_liftL _)
  · exact isWeightBound_map _ (isWeightBound_liftL _)
  · simp only [tImplX]
    split
    · exact isWeightBound_map _ (isWeightBound_query (spec := WSpec + XS) xCalls (.inr _))
    · exact (isWeightBound_liftL _).mono (Nat.zero_le _)

end Adversary

end LeanDa
