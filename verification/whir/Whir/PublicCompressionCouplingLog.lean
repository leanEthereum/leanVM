import Whir.PublicCompressionCoupling

/-! The birthday monitor's event is connected to the actual simulator's
output-collision predicate, for the complete finite compression trace. Hidden
construction calls are retained in this proof log, not in the public View.
This still does not charge missed recognition or construct the DMV coupling. -/
namespace Whir.PublicCompressionCoupling
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open PublicCompressionProgram TypedOracleCompiler
attribute [local instance] PublicMerkleLog.instDecidableEqNode

noncomputable def completedLog {R : Type} (C : PrimitiveOracle) {Q : Nat} :
    Computation R Q → Log → Log
  | .ret _, log => log
  | .draw input next, log => completedLog C (next (C input)) ((input,C input)::log)

theorem completedLog_length {R : Type} (C : PrimitiveOracle) {Q : Nat}
    (p : Computation R Q) (log : Log) : (completedLog C p log).length ≤ Q+log.length := by
  induction p generalizing log with
  | ret => simp [completedLog]
  | @draw n input next ih =>
    have ht := ih (C input) ((input,C input)::log)
    simp only [completedLog,List.length_cons] at *
    omega

theorem completedLog_authentic {R : Type} (C : PrimitiveOracle) {Q : Nat}
    (p : Computation R Q) (log : Log) (auth : PublicMerkleLog.AuthenticLog C log) :
    PublicMerkleLog.AuthenticLog C (completedLog C p log) := by
  induction p generalizing log with
  | ret => exact auth
  | draw input next ih =>
    apply ih (C input) ((input,C input)::log)
    intro n d member
    rcases List.mem_cons.mp member with member | member
    · cases member; rfl
    · exact auth n d member

theorem clean_observe (C : PrimitiveOracle) (log : Log)
    (auth : PublicMerkleLog.AuthenticLog C log)
    (clean : ¬DuplexPublicSimulator.OutputCollision log) (input : Node)
    (noFreshCollision : ¬(PublicMerkleLog.lookup log input = none ∧ C input ∈ outputs log)) :
    ¬DuplexPublicSimulator.OutputCollision ((input,C input)::log) := by
  have same : ∀ n, (n,C input) ∈ log → n = input := by
    intro n member
    cases hit : PublicMerkleLog.lookup log input with
    | none =>
      exfalso
      apply noFreshCollision ⟨hit,?_⟩
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(n,C input),member,rfl⟩)
    | some d =>
      have hi := PublicMerkleLog.lookup_mem hit
      have hd := auth input d hi
      have hi' : (input,C input) ∈ log := by simpa only [hd] using hi
      by_contra different
      exact clean ⟨n,input,C input,member,hi',different⟩
  rintro ⟨a,b,d,ha,hb,different⟩
  rcases List.mem_cons.mp ha with ha | ha
  · cases ha
    rcases List.mem_cons.mp hb with hb | hb
    · cases hb; exact different rfl
    · exact different (same b hb).symm
  · rcases List.mem_cons.mp hb with hb | hb
    · cases hb; exact different (same a ha)
    · exact clean ⟨a,b,d,ha,hb,different⟩

theorem collisionAlarm_false_clean {R : Type} (C : PrimitiveOracle) {Q : Nat}
    (p : Computation R Q) (log : Log) (auth : PublicMerkleLog.AuthenticLog C log)
    (clean : ¬DuplexPublicSimulator.OutputCollision log)
    (noAlarm : collisionAlarm C p log = false) :
    ¬DuplexPublicSimulator.OutputCollision (completedLog C p log) := by
  induction p generalizing log with
  | ret => exact clean
  | draw input next ih =>
    have alarms := Bool.or_eq_false_iff.mp noAlarm
    have fresh := of_decide_eq_false alarms.1
    apply ih (C input) ((input,C input)::log)
    · intro n d member
      rcases List.mem_cons.mp member with member | member
      · cases member; rfl
      · exact auth n d member
    · exact clean_observe C log auth clean input fresh
    · exact alarms.2

theorem completedLog_collision_alarm {R : Type} (C : PrimitiveOracle) {Q : Nat}
    (p : Computation R Q) (collision : DuplexPublicSimulator.OutputCollision (completedLog C p [])) :
    collisionAlarm C p [] = true := by
  cases h : collisionAlarm C p [] with
  | true => rfl
  | false =>
    exact False.elim ((collisionAlarm_false_clean C p []
      (by intro n d member; simp at member)
      (by simp [DuplexPublicSimulator.OutputCollision]) h) collision)

open Classical in
/-- Exactly the collision predicate appearing in radicalExtend's recognition
lemma is covered by the sampled-table birthday bound, not assumed separately. -/
theorem actual_completedLog_collision_bound {R : Type} (iv : Digest32) (program : Program R)
    (Q : Nat) (counted : Counts Q program) :
    average (fun C : PrimitiveOracle =>
      if DuplexPublicSimulator.OutputCollision (completedLog C (compile iv program Q counted) [])
      then (1:ℚ) else 0) ≤ compressionBirthdayLoss Q := by
  classical
  apply le_trans _ (actual_mode_collision_bound_capped iv program Q counted)
  apply average_mono
  intro C
  by_cases bad : DuplexPublicSimulator.OutputCollision
      (completedLog C (compile iv program Q counted) [])
  · simp only [bad,↓reduceIte,completedLog_collision_alarm C _ bad]
    norm_num
  · simp only [bad,↓reduceIte]
    split <;> norm_num

#print axioms collisionAlarm_false_clean
#print axioms actual_completedLog_collision_bound
end Whir.PublicCompressionCoupling
