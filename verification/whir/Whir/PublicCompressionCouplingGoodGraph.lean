import Whir.PublicCompressionCouplingTerminalSupport
import Whir.PublicCompressionCouplingTerminalSeedOrigin
import Whir.PublicCompressionCouplingLateRecognition
import Whir.PublicCompressionCouplingCausalRisk
import Whir.PublicCompressionCouplingRelabelCache

/-! Actual good-path full-key correspondence. Terminal fallback cells cannot
alias consumed RO cells, including cached missed recognition. Chosen seed CVs
are retained throughout; all public primitive observers remain admitted. -/
namespace Whir.PublicCompressionCouplingRecognition
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame DuplexPublicSimulator
open PublicCompressionCouplingMixed PublicCompressionCouplingJoint RawOracleCoupling
open TypedOracleCompiler (Sampling)
set_option backward.isDefEq.respectTransparency false

open Classical in
 theorem actual_terminal_seed_ne_raw_label {R : Type} (Q : Nat) (iv : Digest32) (p : Program R)
    (counted : Counts Q p) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (quiet : causalBad Q iv p counted (oracle seedTable ro)=false)
    {node : Node} {key : RawKey Q} {seedAnswer rawAnswer : Digest32}
    (seedStored : (Sampling.eval (oracle seedTable ro)
      (memo (causalCompile Q iv [] p Q (by rfl) counted) (fun _ => none))).2 (.inl node)=some seedAnswer)
    (rawStored : (Sampling.eval (oracle seedTable ro)
      (memo (causalCompile Q iv [] p Q (by rfl) counted) (fun _ => none))).2 (.inr key)=some rawAnswer) :
    node ≠ terminalLabel seedTable key := by
  simp only [causalBad,Bool.or_eq_false_eq_eq_false_and_eq_false] at quiet
  have birthday := quiet.1.1
  have late := quiet.1.2
  have hidden := quiet.2
  obtain ⟨input,rest,complete,tree,extracted,stored,exposed⟩ :=
    actual_terminal_support Q iv p counted seedTable ro hidden rawStored
  have label := terminalLabel_witness (CoordinateWitness.terminal key rest complete tree extracted)
  intro same
  have nodes : node=input := same.trans label
  clear label
  subst input
  have parsed := (complete?_correct _).mpr complete
  simp only [complete?,Bool.and_eq_true,decide_eq_true_eq] at parsed
  have terminal : isTerminal node := parsed.1
  have publicStored := actual_terminal_seed_public_cache Q iv p counted seedTable ro terminal seedStored
  have publicTrace := PublicCompressionCouplingTargetCache.memo_empty_trace _ _ publicStored
  have publicRecord := compile_seed_record Q seedTable ro iv [] p Q (by rfl) counted node seedAnswer publicTrace
  have target := publicCVTargets_contains _ publicRecord
  have body := exposed target
  have clean := actual_causal_public_noOutputCollision Q iv p counted seedTable ro birthday
  have functional := finalLog_functional ro iv ⟨seedTable,[]⟩ p Q (by rfl) counted
    (by intro a b d e impossible; cases impossible)
  rw [← compile_actual Q seedTable ro iv [] p Q (by rfl) counted] at functional
  have recognized := recognized_complete functional clean terminal body
  have missedLaw := PublicCompressionCouplingLateRecognition.actual_cached_fallback_unrecognized
    Q seedTable ro iv p counted late clean
  have rawEq : (fun a b : RawKey Q => Classical.propDecidable (a=b)) =
      (inferInstance : DecidableEq (RawKey Q)) := Subsingleton.elim _ _
  rw [rawEq] at missedLaw
  have missed := missedLaw node seedAnswer publicStored terminal
  rw [missed] at recognized
  cases recognized

open Classical in
 theorem actual_good_cache_label_injective {R : Type} (Q : Nat) (iv : Digest32) (p : Program R)
    (counted : Counts Q p) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (quiet : causalBad Q iv p counted (oracle seedTable ro)=false) :
    PublicCompressionCouplingRelabelCache.InjectiveOn (coordinateLabel seedTable)
      (Sampling.eval (oracle seedTable ro)
        (memo (causalCompile Q iv [] p Q (by rfl) counted) (fun _ => none))).2 := by
  intro left right d e leftStored rightStored same
  cases left with
  | inl node =>
    cases right with
    | inl other => exact congrArg Sum.inl same
    | inr key =>
      exact False.elim (actual_terminal_seed_ne_raw_label Q iv p counted seedTable ro quiet
        leftStored rightStored same)
  | inr key =>
    cases right with
    | inl node =>
      exact False.elim (actual_terminal_seed_ne_raw_label Q iv p counted seedTable ro quiet
        rightStored leftStored same.symm)
    | inr other =>
      have events := quiet
      simp only [causalBad,Bool.or_eq_false_eq_eq_false_and_eq_false] at events
      obtain ⟨input,rest,complete,tree,extracted,stored,exposed⟩ :=
        actual_terminal_support Q iv p counted seedTable ro events.2 leftStored
      obtain ⟨input',rest',complete',tree',extracted',stored',exposed'⟩ :=
        actual_terminal_support Q iv p counted seedTable ro events.2 rightStored
      have label := terminalLabel_witness (CoordinateWitness.terminal key rest complete tree extracted)
      have label' := terminalLabel_witness (CoordinateWitness.terminal other rest' complete' tree' extracted')
      have nodes : input=input' := label.symm.trans (same.trans label')
      clear label label'
      subst input'
      have rawEq : (fun a b : RawKey Q => Classical.propDecidable (a=b)) =
          (inferInstance : DecidableEq (RawKey Q)) := Subsingleton.elim _ _
      rw [rawEq] at events
      have injective := PublicCompressionCouplingBirthdayCache.birthday_cache_injective
        (oracle seedTable ro) (causalCompile Q iv [] p Q (by rfl) counted) events.1.1
      exact congrArg Sum.inr (terminal_rawKey_unique tree tree' extracted extracted' _ stored stored' injective)

#print axioms actual_terminal_seed_ne_raw_label
#print axioms actual_good_cache_label_injective
end Whir.PublicCompressionCouplingRecognition
