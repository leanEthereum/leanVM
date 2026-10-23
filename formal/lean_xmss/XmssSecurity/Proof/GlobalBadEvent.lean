import XmssSecurity.Proof.CappedSigningLogReplay

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-- The five cryptographic failure mechanisms of the bottom layer, without coordinate indices, and
any bad event of the top layer. -/
inductive GlobalBadEvent where
  | encoding
  | chain
  | suffixCollision
  | leaf
  | merkle
  | top
deriving DecidableEq

instance : Fintype GlobalBadEvent where
  elems := ⟨([.encoding, .chain, .suffixCollision, .leaf, .merkle, .top] : List GlobalBadEvent),
    by decide⟩
  complete event := by cases event <;> decide

def GlobalOutcomeBadEventOccurs
    (cache : QueryCache HashSpec) (outcome : GameOutcome) :
    GlobalBadEvent → Prop
  | .encoding => OutcomeBadEventOccurs cache outcome .encoding
  | .chain => ∃ chain, OutcomeBadEventOccurs cache outcome (.chain chain)
  | .suffixCollision =>
      ∃ slot, OutcomeBadEventOccurs cache outcome (.suffixCollision slot)
  | .leaf => OutcomeBadEventOccurs cache outcome .leaf
  | .merkle => ∃ level, OutcomeBadEventOccurs cache outcome (.merkle level)
  | .top => ∃ event, OutcomeTopBadEventOccurs cache outcome event

def WinningGlobalBadEventOccurs
    (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (event : GlobalBadEvent) : Prop :=
  outcome.won = true ∧ GlobalOutcomeBadEventOccurs cache outcome event

theorem outcomeBadEventOccurs_implies_global
    {cache : QueryCache HashSpec} {outcome : GameOutcome} {event : BadEvent}
    (hevent : OutcomeBadEventOccurs cache outcome event) :
    ∃ globalEvent, GlobalOutcomeBadEventOccurs cache outcome globalEvent := by
  cases event with
  | encoding => exact ⟨.encoding, hevent⟩
  | chain chain => exact ⟨.chain, chain, hevent⟩
  | suffixCollision slot => exact ⟨.suffixCollision, slot, hevent⟩
  | leaf => exact ⟨.leaf, hevent⟩
  | merkle level => exact ⟨.merkle, level, hevent⟩

theorem winning_outcome_has_globalBadEvent
    (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (hconsistent : ConcreteOutcomeConsistent cache outcome)
    (hwin : outcome.won = true) :
    ∃ event, WinningGlobalBadEventOccurs cache outcome event := by
  obtain ⟨event, hbottom | htop⟩ := winning_outcome_has_badEvent cache outcome hconsistent hwin
  · obtain ⟨globalEvent, hglobal⟩ := outcomeBadEventOccurs_implies_global hbottom
    exact ⟨globalEvent, hwin, hglobal⟩
  · exact ⟨.top, hwin, event, htop⟩
end XmssSecurity
