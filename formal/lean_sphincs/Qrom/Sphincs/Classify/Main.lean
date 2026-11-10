module

public import Qrom.Sphincs.Classify.Canon

@[expose] public section

/-!
# The classification of a winning forgery in the hidden game

In side state `s` of the hidden game, with an honest log, a forgery that verifies on the game's
hash and that the log does not hold makes the verifier read a protected input, or an input that is
no honest input at which `G` hits the honest value of its address; or an encoding input whose
data value collides with the key's word; or the forgery's digest comes from `G` at a fresh randomizer and is covered by the logged
digests (`Qrom.Sphincs.classify`).
-/

open OracleComp OracleSpec FORS FORS.Security FORS.Security.Graph FORS.Security.GraphCorrectness
  FORS.Security.GraphView Concrete

noncomputable section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Qrom.Sphincs

variable [Params]

/-- **The classification.** -/
theorem classify (d : Data) (s : Log) (G : Input → HashOutput) (message : Message)
    (signature : Signature) (hlog : HonestLog d s)
    (hver : evalWithAnswerFn (QueryImpl.ofFn (hidFun d s G))
      (Concrete.verify (pkD d) message signature : OracleComp HashSpec Bool) = true)
    (hfresh : ¬ s.Contains ⟨message, signature⟩) :
    (∃ l ∈ queriedInputs (QueryImpl.ofFn (hidFun d s G))
        (Concrete.verify (pkD d) message signature : OracleComp HashSpec Bool),
      ∃ x : Input, x.1 = l ∧ Prot d s x) ∨
    (∃ l ∈ queriedInputs (QueryImpl.ofFn (hidFun d s G))
        (Concrete.verify (pkD d) message signature : OracleComp HashSpec Bool), HitAt d G l) ∨
    (∃ l ∈ queriedInputs (QueryImpl.ofFn (hidFun d s G))
        (Concrete.verify (pkD d) message signature : OracleComp HashSpec Bool),
      ∃ x : Input, x.1 = l ∧ EncAt d x) ∨ CoverE d s G message signature.randomness := by
  set f₂ := QueryImpl.ofFn (hidFun d s G)
  by_cases hp : ∃ l ∈ queriedInputs f₂ (Concrete.verify (pkD d) message signature : OracleComp HashSpec Bool),
      ∃ x : Input, x.1 = l ∧ Prot d s x
  · exact Or.inl hp
  push Not at hp
  -- off the protected inputs the verifier runs as on the full hash
  obtain ⟨heval, htrace⟩ := eval_congr_trace (fD d G) f₂ (Concrete.verify (pkD d) message signature)
    fun l hl ↦ (hidAnswer_eq d s G l fun x hx hprot ↦ hp l hl x (val_of_embed hx) hprot).symm
  have hverified : evalWithAnswerFn (fD d G)
      (Concrete.verify (pkD d) message signature : OracleComp HashSpec Bool) = true := heval.trans hver
  have htr : SignatureWitness.trace (fD d G) (pkD d) message signature =
      queriedInputs f₂ (Concrete.verify (pkD d) message signature : OracleComp HashSpec Bool) := htrace
  have hb : 0 < keptHeight topLayer := keptHeight_top_full ▸ maxLayerHeight_pos
  have hroot := (dataCorrect_ovFun (d none) (hOf d) G).root
  rcases SignatureWitness.accepted_full_classification (fD d G) (pkD d) (d none) message signature hb
      hroot hverified with ⟨counter, hcount, hcanon⟩ | ⟨j, -, htree⟩ | ⟨-, ⟨lay, hwots⟩ | hfors⟩
  · rcases canonical_out d s G message signature hlog hfresh counter hcount hcanon with
      ⟨l, hl, x, hx, hpx⟩ | hcov
    · exact absurd hpx (hp l (htr ▸ hl) x hx)
    · exact Or.inr (Or.inr (Or.inr hcov))
  · obtain ⟨l, hl, hhit⟩ := treeHit_hit d G message signature j htree
    exact Or.inr (Or.inl ⟨l, htr ▸ hl, hhit⟩)
  · rcases wotsException_out d s G message signature lay hwots with ⟨l, hl, hhit⟩ |
      ⟨l, hl, x, hx, hpx⟩ | ⟨l, hl, x, hx, hbad⟩
    · exact Or.inr (Or.inl ⟨l, htr ▸ hl, hhit⟩)
    · exact absurd hpx (hp l (htr ▸ hl) x hx)
    · exact Or.inr (Or.inr (Or.inl ⟨l, htr ▸ hl, x, hx, hbad⟩))
  · obtain ⟨l, hl, hhit⟩ := forsException_hit d G message signature hfors.1
    exact Or.inr (Or.inl ⟨l, htr ▸ hl, hhit⟩)

end Qrom.Sphincs
