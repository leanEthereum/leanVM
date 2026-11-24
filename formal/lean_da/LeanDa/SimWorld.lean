module

public import LeanDa.RpmDuplex
public import LeanDa.RomHash
public import LeanDa.WithHash

@[expose] public section

/-!
# The simulated world: the root's challenges and the adversary's calls

Helpers of the straight-line argument's simulated world (`LeanDa.StraightBound`): `H` among coins
(`hH`), the root's challenges computed once by the duplex (`chalR`), the calls of `F` and of `H`
the simulated adversary makes (`isWeightBound_shadowImpl_f`, `isWeightBound_advS2`,
`isWeightBound_advS2_h`, `isWeightBound_simImpl_h`), and the probability of `true` (`prT`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.SeedDuplex PqDas
open Common.Duplex (GSpec hP gaP)
open scoped ENNReal

namespace LeanDa

/-! ## The verification with `H` alone -/

/-- `H` among coins and `H`. -/
abbrev hH (a : List UInt8) : OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) Common.DigestBytes :=
  liftM ((unifSpec + roSpec (List UInt8) DigestBytes).query (.inr a))

section Post

variable (r : ℕ) {Crs Proof : Type}

theorem simulateQ_embH_hH (a : List UInt8) :
    simulateQ (embH (Msg := List UInt8) (Dg := DigestBytes) (St := KState)) (hH a) = hR a := by
  rw [hH, simulateQ_spec_query]
  rfl

/-- The challenges of the root, the duplex's. -/
noncomputable abbrev chalR (root : Common.DigestBytes) : OracleComp Rom2 (List Draw) := chalP daDuplex root

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

section Calls

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

/-! ## Calls of `H` -/

/-- Calls of `H` in the simulated world. -/
def hCallsG : (unifSpec + GSpec (List UInt8) DigestBytes Common.DigestBytes Draw nLabels).Domain → ℕ
  | .inr (.inl _) => 1
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

end Calls

/-- The probability that a computation returns `true`. -/
noncomputable abbrev prT (x : ProbComp Bool) : ℝ≥0∞ := Pr{let b ← x}[b = true]

end LeanDa
