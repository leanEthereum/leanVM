module

public import LeanDa.RpmDuplex
public import LeanDa.RpmSecurity
public import LeanDa.WithHash

@[expose] public section

/-!
# Code binding in the random-permutation model, through the duplex lemma

The two-oracle code-binding game (`codeBindingExpRom2`: `H` a random oracle, the challenge's sponge
over an independent random function `F`) is brought to the form of the duplex lemma
(`Common.SeedDuplex.duplex_le`): the adversary, then the challenges of its root, computed once
(`chalP daDuplex`), then the verification of the openings with `H` alone (`postV`). The verifier
recomputes the same challenges for every opening; flipping no coins, they are recomputed from the
cache (`Common.run_rerun`), so computing them once changes nothing (`prob_codeBindingPost`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.SeedDuplex PqDas
open Common.Duplex (GSpec hP gaP VSpec toV)
open scoped ENNReal

namespace LeanDa

/-! ## The verification with `H` alone -/

/-- `H` among coins and `H`. -/
abbrev hH (a : List UInt8) : OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) Common.DigestBytes :=
  liftM ((unifSpec + roSpec (List UInt8) DigestBytes).query (.inr a))

section Post

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
      Proof rel)

/-- The win of a code-binding adversary from its openings' verdicts and the argument's. -/
noncomputable def cbWin (out : (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell ×
    CellOpening))
    (vs : List Bool) (b : Bool) : Bool :=
  (vs.all id && b) && !decide ((leanDaErasureCode r).Consistent (out.2.map fun o ↦ (o.1, o.2.1)))

/-- **The verification of the openings with the challenges `l`**, hashing with `H`. -/
noncomputable def postV (crs : Crs) (out : (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening))
    (l : MembershipChallenge) : OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) Bool := do
  let vs ← out.2.mapM fun o ↦ verifyCellMWithHash hH r out.1.1 o.1 o.2.1 o.2.2
  pure (cbWin r out vs (ps.verify crs ((), out.1.1, l) out.1.2))

theorem simulateQ_embH_hH (a : List UInt8) :
    simulateQ (embH (Msg := List UInt8) (Dg := DigestBytes) (St := KState)) (hH a) = hR a := by
  rw [hH, simulateQ_spec_query]
  rfl

theorem simulateQ_embH_postV (crs : Crs)
    (out : (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)) (l :
        MembershipChallenge) :
    simulateQ (embH (Msg := List UInt8) (Dg := DigestBytes) (St := KState)) (postV r ps crs out l) =
      (do
        let vs ← out.2.mapM fun o ↦ verifyCellMWithHash hR r out.1.1 o.1 o.2.1 o.2.2
        pure (cbWin r out vs (ps.verify crs ((), out.1.1, l) out.1.2))) := by
  have hp : ∀ {α} (a : α), simulateQ (embH (Msg := List UInt8) (Dg := DigestBytes) (St := KState))
      (pure a) = pure a := fun a ↦ simulateQ_pure _ a
  have hb : ∀ {α β} (x : OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) α)
      (f : α → OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) β),
      simulateQ (embH (Msg := List UInt8) (Dg := DigestBytes) (St := KState)) (x >>= f) =
        simulateQ embH x >>= fun a ↦ simulateQ embH (f a) := fun x f ↦ simulateQ_bind _ x f
  simp only [postV, hb, hp, mapM_map (fun x ↦ simulateQ embH x) hp hb,
    verifyCellM_map (fun x ↦ simulateQ embH x) hp hb, simulateQ_embH_hH]

/-- The challenges of the root, the duplex's. -/
noncomputable abbrev chalR (root : Common.DigestBytes) : OracleComp Rom2 (List E) := chalP daDuplex root

theorem all_cons_map_and (b v : Bool) (vs : List Bool) :
    ((b && v) :: vs.map (b && ·)).all id = ((v :: vs).all id && b) := by
  cases b <;> simp

/-- Recomputed challenges, from a cache extending one where they were computed. -/
theorem run_mapM_rerun (crs : Crs) (out : (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening))
    {c₀ : Cache2} {w : List E × Cache2}
    (hw : w ∈ support ((simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl
      (chalR out.1.1)).run c₀))
    (l : List (Fin (r * 128) × Cell × CellOpening)) (c : Cache2) (hc : w.2 ≤ c) :
    (simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl
        (l.mapM fun o ↦ verifyRpm hR pR r ps crs out.1 o.1 o.2.1 o.2.2)).run c =ᵈ
      (fun z ↦ (z.1.map (ps.verify crs ((), out.1.1, toVec w.1) out.1.2 && ·), z.2)) <$>
        (simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl
          (l.mapM fun o ↦ verifyCellMWithHash hR r out.1.1 o.1 o.2.1 o.2.2)).run c := by
  induction l generalizing c with
  | nil => simp only [List.mapM_nil, simulateQ_pure, StateT.run_pure, map_pure, List.map_nil]; exact EvalDistEq.rfl
  | cons o l ih =>
    simp only [List.mapM_cons, verifyRpm, simulateQ_bind, StateT.run_bind, simulateQ_pure,
      StateT.run_pure, membershipChallengePairM_eq_chalP, bind_map_left]
    rw [run_rerun _ (noCoins_chalP out.1.1) c₀ hw c hc, pure_bind]
    simp only [map_bind, bind_assoc, pure_bind, map_pure]
    refine EvalDistEq.bind_congr_of_support _ fun w₁ hw₁ ↦ ?_
    have hc1 := le_of_mem_support_run _ c hw₁
    have := ih w₁.2 (hc.trans hc1)
    simp only [verifyRpm, membershipChallengePairM_eq_chalP, bind_map_left] at this
    refine (EvalDistEq.bind_left this _).trans ?_
    rw [bind_map_left]
    simp only [List.map_cons]
    exact EvalDistEq.rfl

theorem consistent_nil : (leanDaErasureCode r).Consistent [] := ⟨fun _ ↦ 0, fun _ h ↦ by cases h⟩

/-- **The verifier computes the challenges once.** -/
theorem prob_codeBindingPost (crs : Crs)
    (out : (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)) (c : Cache2) :
    Pr{let b ← (simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl
        (codeBindingPost r ps crs out)).run' c}[b = true] =
      Pr{let b ← (simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl
        (chalR out.1.1 >>= fun zs ↦ simulateQ embH (postV r ps crs out (toVec zs)))).run' c}[
          b = true] := by
  obtain ⟨com, l⟩ := out
  rcases l with _ | ⟨o, l⟩
  · have hnc : !decide ((leanDaErasureCode r).Consistent ([] : List (Fin (r * 128) × Cell))) =
      false := by
      simp [consistent_nil]
    rw [prEvent_eq_zero_of_forall_mem_support _ _ fun b hb ↦ ?_,
      prEvent_eq_zero_of_forall_mem_support _ _ fun b hb ↦ ?_]
    · simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, simulateQ_embH_postV,
        List.mapM_nil, pure_bind, simulateQ_pure, StateT.run_pure, map_bind, map_pure,
        support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hb
      obtain ⟨_, -, rfl⟩ := hb
      simp [cbWin, consistent_nil]
    · simp only [codeBindingPost, StateT.run'_eq,
        List.mapM_nil, pure_bind, simulateQ_pure, StateT.run_pure, map_pure, support_pure,
        Set.mem_singleton_iff] at hb
      subst hb
      simp [consistent_nil]
  · refine EvalDistEq.prEvent_eq ?_ _
    simp only [codeBindingPost, List.mapM_cons, verifyRpm, simulateQ_bind, StateT.run'_eq,
      StateT.run_bind, simulateQ_pure, StateT.run_pure, membershipChallengePairM_eq_chalP,
      bind_map_left,
      simulateQ_embH_postV, map_bind, bind_assoc, pure_bind, map_pure]
    refine EvalDistEq.bind_congr_of_support _ fun w hw ↦ ?_
    refine EvalDistEq.bind_congr_of_support _ fun w₁ hw₁ ↦ ?_
    have hc1 := le_of_mem_support_run _ _ hw₁
    have h := run_mapM_rerun r ps crs (com, o :: l) hw l w₁.2 hc1
    simp only [verifyRpm, membershipChallengePairM_eq_chalP, bind_map_left] at h
    refine (EvalDistEq.bind_left h _).trans ?_
    rw [bind_map_left]
    refine EvalDistEq.bind_right _ fun z ↦ ?_
    simp only [cbWin, all_cons_map_and]
    exact EvalDistEq.rfl

end Post

/-! ## Calls of `F` -/

/-- **Each step of the shadow world makes at most one call of `F`**, and only for a query of `π`
or a direct call. -/
theorem isWeightBound_shadowImpl_f (t : (dSpec2 (List UInt8) DigestBytes KState).Domain)
    (s : SimState DigestBytes KRest KCap) :
    QueryCostAtMost ((shadowImpl keccakPadding t).run s)
      (fCalls (Msg := List UInt8) (Dg := DigestBytes) (St := KState))
      (queryCost2 (Dg := DigestBytes) keccakPadding t) := by
  have hu : ∀ {β : Type} (p : ProbComp β), QueryCostAtMost (liftM p : OracleComp Rom2 β)
      (fCalls (Msg := List UInt8) (Dg := DigestBytes) (St := KState)) 0 :=
    fun p ↦ isWeightBound_liftM_probComp _ (fun _ ↦ rfl) p
  have hF : ∀ x : KState, QueryCostAtMost (fQuery (Msg := List UInt8) (Dg := DigestBytes) x)
      (fCalls (Msg := List UInt8) (Dg := DigestBytes) (St := KState)) 1 :=
    fun x ↦ isWeightBound_query (spec := Rom2) _ (.inr (.inr x))
  have hH : ∀ a : List UInt8, QueryCostAtMost (hR a)
      (fCalls (Msg := List UInt8) (Dg := DigestBytes) (St := KState)) 0 :=
    fun a ↦ isWeightBound_query (spec := Rom2) _ (.inr (.inl a))
  rcases t with n | m | q | x
  · simp only [shadowImpl, StateT.run_monadLift, monadLift_self]
    exact (hu _).bind fun _ ↦ isWeightBound_pure _ _ 0
  · simp only [shadowImpl, StateT.run_monadLift, monadLift_self]
    exact ((hH m).bind fun _ ↦ isWeightBound_pure _ _ 0).mono (Nat.zero_le _)
  · cases q with
    | forward x =>
      simp only [shadowImpl, simulator2, StateT.run_mk]
      split
      · trivial
      · split
        · refine (QueryCostAtMost.bind (b := 0) ?_ fun _ ↦ isWeightBound_pure _ _ 0)
          unfold rootedAnswer2
          split
          · exact (((hH _).bind fun _ ↦ (hu _).bind fun _ ↦ isWeightBound_pure _ _ 0)).mono
              (Nat.zero_le _)
          · exact hF _
        · exact ((hF _).bind fun _ ↦ isWeightBound_pure _ _ 0)
    | inverse y =>
      simp only [shadowImpl, simulator2, StateT.run_mk]
      split
      · trivial
      · exact ((hu _).bind fun _ ↦ isWeightBound_pure _ _ 0).mono (Nat.zero_le _)
  · simp only [shadowImpl, StateT.run_mk]
    exact ((hF _).bind fun _ ↦ isWeightBound_pure _ _ 0)

section CodeBinding

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
      Proof rel)

/-- **The simulated adversary calls `F` at most `Q` times** for every crs the setup can output,
when the RPM game makes at most `Q` permutation calls. -/
theorem isWeightBound_advS2 (A : CodeBindingAdvB r Crs Proof) (Q : ℕ)
    (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) (crs : Crs)
    (hcrs : crs ∈ support ps.setup) :
    QueryCostAtMost (advS2 keccakPadding KState.zero (A ((), crs)))
      (fCalls (Msg := List UInt8) (Dg := DigestBytes) (St := KState)) Q := by
  rw [permCalls2_eq] at hQ
  have hX : QueryCostAtMost (simulateQ (hInF (E := KRest) (C := KCap)) (liftM ps.setup) >>= fun x ↦
      advS2 keccakPadding KState.zero (A ((), x)) >>= fun a ↦ codeBindingPost r ps x a)
      (fCalls (Msg := List UInt8) (Dg := DigestBytes) (St := KState)) Q := by
    rw [← shadow_rpmGame2, StateT.run'_eq]
    exact isWeightBound_map _ (isWeightBound_run_simulateQ _ _ _ isWeightBound_shadowImpl_f hQ _)
  rw [simulateQ_liftM_of_coins _ (fun _ ↦ rfl)] at hX
  have hmem : crs ∈ support (liftM ps.setup : OracleComp Rom2 Crs) := by
    change crs ∈ support (OracleComp.liftComp ps.setup _)
    rwa [OracleComp.support_liftComp]
  exact (hX.of_bind_mem_support hmem).of_bind

/-- **The simulated world of code binding** for a crs: `H` a random oracle, the challenges a
random oracle `G` on `(root, j)`, the adversary's direct calls of `F` answered by the duplex
lemma's simulator from `H` and `G` (`simImpl`), then the openings verified with `H` and the
challenges `G (root, ·)`. -/
noncomputable def cbIdealG (A : CodeBindingAdvB r Crs Proof) (crs : Crs) : ProbComp Bool :=
  (simulateQ (GSpec (List UInt8) DigestBytes Common.DigestBytes E 2).romImpl
    ((simulateQ (simImpl daDuplex hP gaP) (hQ (St := KState) daDuplex.label >>= fun _ ↦
        advS2 keccakPadding KState.zero (A ((), crs)))).run' SimSt.init >>= fun out ↦
      readVec (Msg := List UInt8) (Dg := DigestBytes) out.1.1 >>= fun l ↦
        simulateQ embG (postV r ps crs out l))).run' ∅

/-- The simulated code-binding experiment: the argument's setup, then `cbIdealG`. -/
noncomputable def codeBindingExpG (A : CodeBindingAdvB r Crs Proof) : ProbComp Bool :=
  ps.setup >>= cbIdealG r ps A

/-- **From the random-permutation model to the simulated world**: for an adversary whose game
makes at most `Q` permutation calls, the RPM code-binding probability is at most the simulated
one plus `Q² / 2^508` (the two-oracle transfer) plus `N · 2N / 2^576` with `N = Q + 3` (the
duplex lemma: collisions of the 576-bit capacity among at most `Q + 3` calls of `F`). -/
theorem codeBindingExpRpm_le_G (A : CodeBindingAdvB r Crs Proof) (Q : ℕ)
    (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) :
    Pr{let b ← codeBindingExpRpm r ps A}[b = true] ≤
      Pr{let b ← codeBindingExpG r ps A}[b = true] + (Q ^ 2 : ℝ≥0∞) / 2 ^ 508 +
        ((Q + 2 + 1 : ℕ) : ℝ≥0∞) * (2 * ((Q + 2 + 1 : ℕ) : ℝ≥0∞) * (2 ^ 576 : ℝ≥0∞)⁻¹) := by
  refine (leanDa_codeBinding_rpm r ps A Q hQ).1.trans ?_
  rw [add_right_comm]
  refine add_le_add ?_ le_rfl
  have hsplit : Pr{let b ← codeBindingExpRom2 r ps A}[b = true] =
      Pr{let b ← ps.setup >>= fun crs ↦ romRun2 (advS2 keccakPadding KState.zero (A ((), crs)) >>=
        fun out ↦ codeBindingPost r ps crs out)}[b = true] := by
    rw [codeBindingExpRom2, romRun2, simulateQ_liftM_of_coins _ (fun _ ↦ rfl), simulateQ_bind,
      StateT.run'_eq, StateT.run_bind, simulateQ_romImpl_liftM_run, bind_map_left, map_bind]
    rfl
  rw [hsplit, codeBindingExpG]
  refine prEvent_bind_le_add_const_of_support _ _ _ _ _ _ fun crs hcrs ↦ ?_
  have hB := isWeightBound_advS2 r ps A Q hQ crs hcrs
  have h1 : Pr{let b ← romRun2 (advS2 keccakPadding KState.zero (A ((), crs)) >>=
        fun out ↦ codeBindingPost r ps crs out)}[b = true] =
      Pr{let b ← (simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl
        (advS2 keccakPadding KState.zero (A ((), crs)) >>= fun out ↦ chalR out.1.1 >>= fun zs ↦
          simulateQ embH (postV r ps crs out (toVec zs)))).run' ∅}[b = true] := by
    have e : ∀ (K : ((Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)) →
        OracleComp Rom2 Bool),
        (simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl
          (advS2 keccakPadding KState.zero (A ((), crs)) >>= K)).run' ∅ =
        (simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl
          (advS2 keccakPadding KState.zero (A ((), crs)))).run ∅ >>= fun z ↦
            (simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl (K z.1)).run' z.2 := by
      intro K
      simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind]
    rw [romRun2, e, e]
    exact Common.prEvent_bind_congr _ _ _ _ _ fun z ↦ prob_codeBindingPost r ps crs z.1 z.2
  rw [h1]
  exact duplex_le (D := daDuplex) daDuplex_cap _ Q hB (fun out ↦ out.1.1)
    (fun out l ↦ postV r ps crs out l)

end CodeBinding

end LeanDa
