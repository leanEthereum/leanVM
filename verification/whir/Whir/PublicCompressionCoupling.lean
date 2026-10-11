import Whir.PublicMerkleProbability
import Whir.DuplexPublicSimulator

/-! Actual finite-table collision probabilities for the public compression game.
The complete construction paths are included. These estimates alone do not
assert a real/ideal simulator coupling or the DMV distinguishing endpoint. -/
namespace Whir.PublicCompressionCoupling
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open PublicCompressionProgram TypedOracleCompiler
open scoped BigOperators

attribute [local instance] PublicMerkleLog.instDecidableEqNode

private theorem average_fintype {α : Type*} (old new : Fintype α) (f : α → ℚ) :
    @average α old f = @average α new f := by
  cases Subsingleton.elim old new
  rfl

@[instance_reducible]
private noncomputable def tableFintype : Fintype PrimitiveOracle :=
  @Pi.instFintype Node (fun _ => Digest32) inferInstance inferInstance (fun _ => inferInstance)

abbrev Log := PublicMerkleLog.PublicLog

def outputs (log : Log) : Finset Digest32 := (log.map Prod.snd).toFinset

theorem outputs_card (log : Log) : (outputs log).card ≤ log.length := by
  exact (List.toFinset_card_le _).trans_eq (List.length_map ..)

/-- Every continuation is monitored, including internal construction calls and
repeated public requests. Only genuinely fresh inputs can cause a collision. -/
noncomputable def collisionAlarm {R : Type} (C : PrimitiveOracle) {Q : Nat} :
    Computation R Q → Log → Bool
  | .ret _, _ => false
  | .draw n next, log =>
      decide (PublicMerkleLog.lookup log n = none ∧ C n ∈ outputs log) ||
        collisionAlarm C (next (C n)) ((n,C n)::log)

noncomputable def collisionRisk {R : Type} {Q : Nat} : Computation R Q → Log → ℚ
  | .ret _, _ => 0
  | .draw n next, log =>
      match PublicMerkleLog.lookup log n with
      | some d => collisionRisk (next d) ((n,d)::log)
      | none => average (fun d => if d ∈ outputs log then 1
          else collisionRisk (next d) ((n,d)::log))

/-- The exact remaining birthday ledger, retaining the exposed history length. -/
def collisionLedger (remaining previous : Nat) : ℚ :=
  ((remaining : ℚ)*previous + remaining*(remaining-1)/2) / 2^256

private theorem collisionLedger_nonneg (remaining previous : Nat) :
    0 ≤ collisionLedger remaining previous := by
  cases remaining with
  | zero => simp [collisionLedger]
  | succ n =>
    unfold collisionLedger
    simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right]
    positivity

private theorem collisionLedger_step (remaining previous : Nat) :
    collisionLedger (remaining+1) previous =
      (previous : ℚ)/2^256 + collisionLedger remaining (previous+1) := by
  unfold collisionLedger
  push_cast
  ring

theorem collisionRisk_bound {R : Type} {Q : Nat} (p : Computation R Q) (log : Log) :
    collisionRisk p log ≤ collisionLedger Q log.length := by
  classical
  induction p generalizing log with
  | ret value => exact collisionLedger_nonneg _ _
  | @draw n input next ih =>
    have hstep := collisionLedger_step n log.length
    cases hit : PublicMerkleLog.lookup log input with
    | some d =>
      simp only [collisionRisk,hit]
      have ht := ih d ((input,d)::log)
      simp only [List.length_cons] at ht
      rw [hstep]
      have hnon : (0 : ℚ) ≤ (log.length : ℚ)/2^256 := by positivity
      linarith
    | none =>
      simp only [collisionRisk,hit]
      calc
        _ ≤ average (fun d : Digest32 =>
            (if d ∈ outputs log then (1:ℚ) else 0) +
              collisionLedger n (log.length+1)) := by
          apply average_mono
          intro d
          have hn := collisionLedger_nonneg n (log.length+1)
          have ht := ih d ((input,d)::log)
          simp only [List.length_cons] at ht
          by_cases bad : d ∈ outputs log
          · simp only [bad,↓reduceIte]
            linarith
          · simpa only [bad,↓reduceIte,zero_add] using ht
        _ = (outputs log).card / (2^256 : ℚ) +
            collisionLedger n (log.length+1) := by
          rw [average_add,PublicMerkleProbability.uniform_target_probability,average_const]
        _ ≤ (log.length : ℚ)/2^256 + collisionLedger n (log.length+1) := by
          apply add_le_add_left
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact_mod_cast outputs_card log
        _ = _ := hstep.symm

/-- Exact lazy sampling of the actual finite compression table. No stochastic
oracle premise or assumed bad-event certificate is used. -/
theorem table_collisionAlarm_eq_risk {R : Type} {Q : Nat}
    (p : Computation R Q) (log : Log) :
    average (fun C : PrimitiveOracle =>
      if collisionAlarm (RawOracleCoupling.overlay (PublicMerkleLog.lookup log) C) p log
      then 1 else 0) = collisionRisk p log := by
  classical
  rw [average_fintype _ tableFintype]
  let _ := tableFintype
  induction p generalizing log with
  | ret value => simp [collisionAlarm,collisionRisk,average_const]
  | draw n next ih =>
    cases hit : PublicMerkleLog.lookup log n with
    | some d =>
      have cache := PublicMerkleProbability.lookup_cons_hit log n d hit
      simp only [collisionRisk,hit]
      rw [← ih d ((n,d)::log),cache]
      apply congrArg average
      funext C
      simp [collisionAlarm,RawOracleCoupling.overlay,hit]
    | none =>
      rw [RawOracleCoupling.overlay_average (PublicMerkleLog.lookup log) n hit
        (fun oracle => if collisionAlarm oracle (.draw n next) log then (1:ℚ) else 0)]
      simp only [collisionRisk,hit]
      apply congrArg average
      funext d
      have cache := PublicMerkleProbability.lookup_cons log n d
      by_cases bad : d ∈ outputs log
      · simp [collisionAlarm,RawOracleCoupling.overlay,hit,bad,average_const]
      · rw [← ih d ((n,d)::log),cache]
        simp only [bad,↓reduceIte]
        apply congrArg average
        funext C
        simp only [collisionAlarm,RawOracleCoupling.overlay,hit,
          TypedFiatShamirGame.put_self,Option.getD_some,true_and,bad,
          decide_false,Bool.false_or]
        apply congrArg (fun oracle : PrimitiveOracle =>
          if collisionAlarm oracle (next d) ((n,d)::log) then (1:ℚ) else 0)
        funext j
        simp [RawOracleCoupling.overlay,TypedFiatShamirGame.put,Function.update]

theorem actual_compression_collision_bound {R : Type} {Q : Nat}
    (p : Computation R Q) :
    average (fun C : PrimitiveOracle => if collisionAlarm C p [] then 1 else 0) ≤
      collisionLedger Q 0 := by
  rw [average_fintype _ tableFintype]
  let _ := tableFintype
  have he := table_collisionAlarm_eq_risk p []
  rw [average_fintype _ tableFintype] at he
  have hb := collisionRisk_bound p []
  have he' : average (fun C : PrimitiveOracle => if collisionAlarm C p [] then 1 else 0) =
      collisionRisk p [] := by
    trans average (fun C : PrimitiveOracle =>
      if collisionAlarm (RawOracleCoupling.overlay (PublicMerkleLog.lookup []) C) p []
      then (1:ℚ) else 0)
    · apply congrArg average
      funext C
      have hc : RawOracleCoupling.overlay (PublicMerkleLog.lookup []) C = C := by
        funext j
        simp [RawOracleCoupling.overlay,PublicMerkleLog.lookup]
      rw [hc]
    · exact he
  exact he'.trans_le hb

/-- All counted adaptive mode continuations, with the actual complete uncached
construction path cost, are covered by the finite-table estimate. -/
theorem actual_mode_collision_bound {R : Type} (iv : Digest32) (p : Program R)
    (Q : Nat) (counted : Counts Q p) :
    average (fun C : PrimitiveOracle =>
      if collisionAlarm C (compile iv p Q counted) [] then 1 else 0) ≤
      collisionLedger Q 0 := actual_compression_collision_bound _

theorem collisionLedger_zero (Q : Nat) :
    collisionLedger Q 0 = (Q.choose 2 : ℚ) / 2^256 := by
  rw [Nat.cast_choose_two]
  simp [collisionLedger]

theorem actual_mode_collision_bound_capped {R : Type} (iv : Digest32) (p : Program R)
    (Q : Nat) (counted : Counts Q p) :
    average (fun C : PrimitiveOracle =>
      if collisionAlarm C (compile iv p Q counted) [] then 1 else 0) ≤ compressionBirthdayLoss Q := by
  apply le_min
  · calc
      _ ≤ average (fun _ : PrimitiveOracle => (1:ℚ)) := by
        apply average_mono
        intro C
        split <;> norm_num
      _ = 1 := average_const _
  · simpa only [collisionLedger_zero] using actual_mode_collision_bound iv p Q counted

/-- A finite full-view coupling inequality. The actual pinned simulator coupling
is constructed in `PublicCompressionCouplingActualJoint`. -/
theorem full_view_coupling_bound {Coins V : Type*} [Fintype Coins] [Nonempty Coins]
    (real ideal : Coins → V) (bad : Coins → Prop) [DecidablePred bad]
    (equal : ∀ coins, ¬bad coins → real coins = ideal coins) (D : V → Bool) :
    |distinguishProbability real D - distinguishProbability ideal D| ≤
      average (fun coins => if bad coins then (1:ℚ) else 0) := by
  rw [distinguish_average (inferInstance : Fintype Coins),
    distinguish_average (inferInstance : Fintype Coins)]
  apply abs_le.mpr
  constructor
  · have h : average (fun coins => if D (ideal coins) then (1:ℚ) else 0) ≤
        average (fun coins => if D (real coins) then (1:ℚ) else 0) +
          average (fun coins => if bad coins then (1:ℚ) else 0) := by
      rw [← average_add]
      apply average_mono
      intro coins
      by_cases hb : bad coins
      · simp only [hb,↓reduceIte]
        cases D (real coins) <;> cases D (ideal coins) <;> norm_num
      · rw [equal coins hb]
        simp [hb]
    linarith
  · have h : average (fun coins => if D (real coins) then (1:ℚ) else 0) ≤
        average (fun coins => if D (ideal coins) then (1:ℚ) else 0) +
          average (fun coins => if bad coins then (1:ℚ) else 0) := by
      rw [← average_add]
      apply average_mono
      intro coins
      by_cases hb : bad coins
      · simp only [hb,↓reduceIte]
        cases D (real coins) <;> cases D (ideal coins) <;> norm_num
      · rw [equal coins hb]
        simp [hb]
    linarith

#print axioms actual_mode_collision_bound_capped
#print axioms full_view_coupling_bound

#print axioms table_collisionAlarm_eq_risk
#print axioms actual_mode_collision_bound
end Whir.PublicCompressionCoupling
