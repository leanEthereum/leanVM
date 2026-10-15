import Sphincs.SecurityTreeWitness

/-! Chain divergence and prefix-inversion contacts on the actual verifier query trace.
Adapted from leanVM b7a107256. No hash-injectivity assumption is used. -/

open OracleComp OracleSpec

namespace Sphincs.Security
open Concrete

theorem queriedInputs_mono_bind_left {α β : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec α) (next : α → OracleComp HashSpec β)
    {input : HashInput} (hinput : input ∈ queriedInputs f oa) :
    input ∈ queriedInputs f (oa >>= next) := by
  rw [queriedInputs_bind]
  exact List.mem_append_left _ hinput

theorem queriedInputs_mono_bind_right {α β : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec α) (next : α → OracleComp HashSpec β)
    {input : HashInput} (hinput : input ∈ queriedInputs f (next (evalWithAnswerFn f oa))) :
    input ∈ queriedInputs f (oa >>= next) := by
  rw [queriedInputs_bind]
  exact List.mem_append_right _ hinput

theorem queriedInputs_sequenceFin_component {α : Type} {n : Nat}
    (f : QueryImpl HashSpec Id) (computation : Fin n → OracleComp HashSpec α)
    (index : Fin n) {input : HashInput} (hinput : input ∈ queriedInputs f (computation index)) :
    input ∈ queriedInputs f (sequenceFin computation) := by
  induction n with
  | zero => exact index.elim0
  | succ n ih =>
      cases index using Fin.cases with
      | zero =>
          rw [sequenceFin]
          exact queriedInputs_mono_bind_left f (computation 0) _ hinput
      | succ index =>
          rw [sequenceFin]
          apply queriedInputs_mono_bind_right f (computation 0)
          apply queriedInputs_mono_bind_left
          exact ih (fun index : Fin n => computation index.succ) index hinput

/-- A trace contains all queries of a fixed-function execution. -/
def ContainsRun {α : Type} (f : QueryImpl HashSpec Id) (trace : List HashInput)
    (oa : OracleComp HashSpec α) : Prop := ∀ input ∈ queriedInputs f oa, input ∈ trace

theorem ContainsRun.bind_left {α β : Type} {f : QueryImpl HashSpec Id} {trace : List HashInput}
    {oa : OracleComp HashSpec α} {next : α → OracleComp HashSpec β}
    (h : ContainsRun f trace (oa >>= next)) : ContainsRun f trace oa :=
  fun _ hi => h _ (queriedInputs_mono_bind_left f oa next hi)

theorem ContainsRun.bind_right {α β : Type} {f : QueryImpl HashSpec Id} {trace : List HashInput}
    {oa : OracleComp HashSpec α} {next : α → OracleComp HashSpec β}
    (h : ContainsRun f trace (oa >>= next)) :
    ContainsRun f trace (next (evalWithAnswerFn f oa)) :=
  fun _ hi => h _ (queriedInputs_mono_bind_right f oa next hi)

theorem ContainsRun.sequenceFin_component {α : Type} {n : Nat} {f : QueryImpl HashSpec Id}
    {trace : List HashInput} (computation : Fin n → OracleComp HashSpec α)
    (h : ContainsRun f trace (sequenceFin computation)) (index : Fin n) :
    ContainsRun f trace (computation index) :=
  fun _ hi => h _ (queriedInputs_sequenceFin_component f computation index hi)

namespace Chain
open Concrete

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
  (leaf : LeafIndex) (chainIdx : ChainIndex) (secret : Digest)

/-- The honest chain value at a position. -/
def honestChain (position : Nat) : Digest :=
  evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 position secret)

/-- What the walk has reached after `steps` steps from `start`. -/
def walkValue (start : Nat) (value : Digest) (steps : Nat) : Digest :=
  evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start steps value)

theorem honestChain_succ (position : Nat) (hposition : position < chainLength - 1) :
    honestChain f parameter lay tree leaf chainIdx secret (position + 1)
      = truncateHash (f (tweakableHashInput parameter
          (.chain lay tree leaf chainIdx ⟨position, hposition⟩)
          ((bytesLE 16) (honestChain f parameter lay tree leaf chainIdx secret position)))) := by
  simp only [honestChain, chainWalk, evalWithAnswerFn_bind, Nat.zero_add, dif_pos hposition,
    Completeness.eval_tweakableHash]

theorem walkValue_succ (start : Nat) (value : Digest) (steps : Nat)
    (hrange : start + steps < chainLength - 1) :
    walkValue f parameter lay tree leaf chainIdx start value (steps + 1)
      = truncateHash (f (tweakableHashInput parameter
          (.chain lay tree leaf chainIdx ⟨start + steps, hrange⟩)
          ((bytesLE 16) (walkValue f parameter lay tree leaf chainIdx start value steps)))) := by
  simp only [walkValue, chainWalk, evalWithAnswerFn_bind, dif_pos hrange, Completeness.eval_tweakableHash]

/-- A hit at a chain step: something other than the honest value at `position` hashing to the honest
value at `position + 1`. -/
def ChainHit (position : Nat) (hposition : position < chainLength - 1) (payload : Digest) : Prop :=
  payload ≠ honestChain f parameter lay tree leaf chainIdx secret position
    ∧ truncateHash (f (tweakableHashInput parameter
        (.chain lay tree leaf chainIdx ⟨position, hposition⟩) ((bytesLE 16) payload)))
      = honestChain f parameter lay tree leaf chainIdx secret (position + 1)

theorem chainWalk_extract_above (start : Nat) (value : Digest) (steps cutoff : Nat)
    (hrange : start + steps ≤ chainLength - 1) (hcutoff : cutoff ≤ steps)
    (hwalk : walkValue f parameter lay tree leaf chainIdx start value steps
      = honestChain f parameter lay tree leaf chainIdx secret (start + steps)) :
    walkValue f parameter lay tree leaf chainIdx start value cutoff
        = honestChain f parameter lay tree leaf chainIdx secret (start + cutoff)
      ∨ ∃ (offset : Nat) (hoffset : start + offset < chainLength - 1),
          cutoff ≤ offset ∧ offset < steps ∧
          ChainHit f parameter lay tree leaf chainIdx secret (start + offset) hoffset
            (walkValue f parameter lay tree leaf chainIdx start value offset) := by
  induction steps with
  | zero =>
      have : cutoff = 0 := by omega
      subst cutoff
      exact Or.inl hwalk
  | succ steps ih =>
      by_cases heq : cutoff = steps + 1
      · subst cutoff
        exact Or.inl hwalk
      have hlt : start + steps < chainLength - 1 := by omega
      by_cases hagree : walkValue f parameter lay tree leaf chainIdx start value steps
          = honestChain f parameter lay tree leaf chainIdx secret (start + steps)
      · rcases ih (by omega) (by omega) hagree with hvalue | ⟨offset, hoffset, hcut, ho, hhit⟩
        · exact Or.inl hvalue
        · exact Or.inr ⟨offset, hoffset, hcut, by omega, hhit⟩
      · refine Or.inr ⟨steps, hlt, by omega, by omega, hagree, ?_⟩
        rw [← walkValue_succ f parameter lay tree leaf chainIdx start value steps hlt, hwalk,
          show start + (steps + 1) = start + steps + 1 by omega]

theorem chainWalk_query_mem (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (start steps : Nat) (value : Digest) (offset : Nat)
    (hoffset : offset < steps) (hrange : start + offset < chainLength - 1) :
    tweakableHashInput parameter (.chain lay tree leafIdx chainIdx ⟨start + offset, hrange⟩)
        ((bytesLE 16) (walkValue f parameter lay tree leafIdx chainIdx start value offset))
      ∈ queriedInputs f (chainWalk parameter lay tree leafIdx chainIdx start steps value) := by
  induction steps generalizing offset with
  | zero => omega
  | succ steps ih =>
      rw [chainWalk]
      split_ifs with hstep
      · rw [queriedInputs_bind]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hoffset with hlt | heq
        · exact List.mem_append_left _ (ih offset hlt hrange)
        · subst offset
          apply List.mem_append_right _
          simp only [walkValue, queriedInputs_tweakableHash, List.mem_singleton]
      · rw [queriedInputs_bind]
        apply List.mem_append_left
        exact ih offset (by omega) hrange

/-- A different predecessor queried at or above the published chain position. -/
def ForwardMatch (reference : Digit) (trace : List HashInput) : Prop :=
  ∃ (step : ChainStep) (payload : Digest), reference.val ≤ step.val ∧
    tweakableHashInput parameter (.chain lay tree leaf chainIdx step) (bytesLE 16 payload) ∈ trace ∧
    ChainHit f parameter lay tree leaf chainIdx secret step.val step.isLt payload

/-- One queried edge immediately below a published chain position reaches that frontier. -/
def Contact (reference : Digit) (frontier : Digest) (trace : List HashInput) : Prop :=
  ∃ (step : ChainStep) (payload : Digest), step.val + 1 = reference.val ∧
    tweakableHashInput parameter (.chain lay tree leaf chainIdx step) (bytesLE 16 payload) ∈ trace ∧
    truncateHash (f (tweakableHashInput parameter (.chain lay tree leaf chainIdx step)
      (bytesLE 16 payload))) = frontier

/-- Two consecutive queried edges below a published position reach its frontier. -/
def TwoEdge (reference : Digit) (frontier : Digest) (trace : List HashInput) : Prop :=
  ∃ (first second : ChainStep) (payload middle : Digest),
    first.val + 1 = second.val ∧ second.val + 1 = reference.val ∧
    tweakableHashInput parameter (.chain lay tree leaf chainIdx first) (bytesLE 16 payload) ∈ trace ∧
    tweakableHashInput parameter (.chain lay tree leaf chainIdx second) (bytesLE 16 middle) ∈ trace ∧
    truncateHash (f (tweakableHashInput parameter (.chain lay tree leaf chainIdx first)
      (bytesLE 16 payload))) = middle ∧
    truncateHash (f (tweakableHashInput parameter (.chain lay tree leaf chainIdx second)
      (bytesLE 16 middle))) = frontier

attribute [local irreducible] chainWalk

/-- Without a forward distinct-input hit, endpoint agreement propagates back to every position
at or above the published frontier. -/
theorem recover_canonical_above (reference digit : Digit) (value : Digest) (trace : List HashInput)
    (cutoff : Nat) (hcut : cutoff ≤ chainLength - 1 - digit.val)
    (habove : reference.val ≤ digit.val + cutoff)
    (hendpoint : evalWithAnswerFn f (recoverChain parameter lay tree leaf chainIdx digit value)
      = honestChain f parameter lay tree leaf chainIdx secret (chainLength - 1))
    (hrun : ContainsRun f trace (recoverChain parameter lay tree leaf chainIdx digit value))
    (hforward : ¬ForwardMatch f parameter lay tree leaf chainIdx secret reference trace) :
    walkValue f parameter lay tree leaf chainIdx digit.val value cutoff =
      honestChain f parameter lay tree leaf chainIdx secret (digit.val + cutoff) := by
  have hd : digit.val ≤ chainLength - 1 := Nat.le_pred_of_lt digit.isLt
  have hwalk : walkValue f parameter lay tree leaf chainIdx digit.val value
      (chainLength - 1 - digit.val) = honestChain f parameter lay tree leaf chainIdx secret
        (digit.val + (chainLength - 1 - digit.val)) := by
    simpa only [walkValue, recoverChain, Nat.add_sub_of_le hd] using hendpoint
  rcases chainWalk_extract_above f parameter lay tree leaf chainIdx secret digit.val value
      (chainLength - 1 - digit.val) cutoff (by omega) hcut hwalk with h | ⟨offset, ho, hc, hs, hh⟩
  · exact h
  · exact False.elim (hforward ⟨⟨digit.val + offset, ho⟩, _, by dsimp; omega,
      hrun _ (chainWalk_query_mem f parameter lay tree leaf chainIdx digit.val
        (chainLength - 1 - digit.val) value offset hs ho), hh⟩)

theorem recover_frontier (reference digit : Digit) (value : Digest) (trace : List HashInput)
    (hbelow : digit.val ≤ reference.val)
    (hendpoint : evalWithAnswerFn f (recoverChain parameter lay tree leaf chainIdx digit value)
      = honestChain f parameter lay tree leaf chainIdx secret (chainLength - 1))
    (hrun : ContainsRun f trace (recoverChain parameter lay tree leaf chainIdx digit value))
    (hforward : ¬ForwardMatch f parameter lay tree leaf chainIdx secret reference trace) :
    walkValue f parameter lay tree leaf chainIdx digit.val value (reference.val - digit.val) =
      honestChain f parameter lay tree leaf chainIdx secret reference.val := by
  have hd : reference.val ≤ chainLength - 1 := Nat.le_pred_of_lt reference.isLt
  simpa only [Nat.add_sub_of_le hbelow] using recover_canonical_above f parameter lay tree leaf
    chainIdx secret reference digit value trace (reference.val - digit.val)
    (by omega) (by omega) hendpoint hrun hforward

theorem recover_value (reference digit : Digit) (value : Digest) (trace : List HashInput)
    (habove : reference.val ≤ digit.val)
    (hendpoint : evalWithAnswerFn f (recoverChain parameter lay tree leaf chainIdx digit value)
      = honestChain f parameter lay tree leaf chainIdx secret (chainLength - 1))
    (hrun : ContainsRun f trace (recoverChain parameter lay tree leaf chainIdx digit value))
    (hforward : ¬ForwardMatch f parameter lay tree leaf chainIdx secret reference trace) :
    value = honestChain f parameter lay tree leaf chainIdx secret digit.val := by
  simpa only [walkValue, chainWalk, evalWithAnswerFn_pure, Nat.add_zero] using
    recover_canonical_above f parameter lay tree leaf chainIdx secret reference digit value trace
      0 (by omega) (by omega) hendpoint hrun hforward

/-- The last verifier query before a lower digit reaches the reference frontier. -/
theorem recover_contact (reference digit : Digit) (value frontier : Digest) (trace : List HashInput)
    (hbelow : digit.val < reference.val)
    (hfrontier : walkValue f parameter lay tree leaf chainIdx digit.val value
      (reference.val - digit.val) = frontier)
    (hrun : ContainsRun f trace (recoverChain parameter lay tree leaf chainIdx digit value)) :
    Contact f parameter lay tree leaf chainIdx reference frontier trace := by
  have hd : reference.val ≤ chainLength - 1 := Nat.le_pred_of_lt reference.isLt
  let offset := reference.val - digit.val - 1
  have ho : digit.val + offset < chainLength - 1 := by dsimp [offset]; omega
  refine ⟨⟨digit.val + offset, ho⟩, walkValue f parameter lay tree leaf chainIdx digit.val value offset,
    by dsimp [offset]; omega, ?_, ?_⟩
  · exact hrun _ (chainWalk_query_mem f parameter lay tree leaf chainIdx digit.val
      (chainLength - 1 - digit.val) value offset (by dsimp [offset]; omega) ho)
  · rw [← walkValue_succ f parameter lay tree leaf chainIdx digit.val value offset ho,
      show offset + 1 = reference.val - digit.val by dsimp [offset]; omega]
    exact hfrontier

/-- A two-step deficit produces both linked queries, not merely the terminal preimage. -/
theorem recover_twoEdge (reference digit : Digit) (value frontier : Digest) (trace : List HashInput)
    (hbelow : digit.val + 2 ≤ reference.val)
    (hfrontier : walkValue f parameter lay tree leaf chainIdx digit.val value
      (reference.val - digit.val) = frontier)
    (hrun : ContainsRun f trace (recoverChain parameter lay tree leaf chainIdx digit value)) :
    TwoEdge f parameter lay tree leaf chainIdx reference frontier trace := by
  have hd : reference.val ≤ chainLength - 1 := Nat.le_pred_of_lt reference.isLt
  let first := reference.val - digit.val - 2
  let second := reference.val - digit.val - 1
  have hf : digit.val + first < chainLength - 1 := by dsimp [first]; omega
  have hs : digit.val + second < chainLength - 1 := by dsimp [second]; omega
  refine ⟨⟨digit.val + first, hf⟩, ⟨digit.val + second, hs⟩,
    walkValue f parameter lay tree leaf chainIdx digit.val value first,
    walkValue f parameter lay tree leaf chainIdx digit.val value second,
    by dsimp [first, second]; omega, by dsimp [second]; omega, ?_, ?_, ?_, ?_⟩
  · exact hrun _ (chainWalk_query_mem f parameter lay tree leaf chainIdx digit.val
      (chainLength - 1 - digit.val) value first (by dsimp [first]; omega) hf)
  · exact hrun _ (chainWalk_query_mem f parameter lay tree leaf chainIdx digit.val
      (chainLength - 1 - digit.val) value second (by dsimp [second]; omega) hs)
  · rw [← walkValue_succ f parameter lay tree leaf chainIdx digit.val value first hf,
      show first + 1 = second by dsimp [first, second]; omega]
  · rw [← walkValue_succ f parameter lay tree leaf chainIdx digit.val value second hs,
      show second + 1 = reference.val - digit.val by dsimp [second]; omega]
    exact hfrontier

/-- The actual byte layout separates all 64 chain addresses (the field `hi`) and their three step
addresses (the step bits of the type byte). -/
theorem chain_input_address_injective (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) {chain chain' : ChainIndex}
    {step step' : ChainStep} (payload payload' : Digest)
    (heq : tweakableHashInput parameter (.chain lay tree leaf chain step) (bytesLE 16 payload) =
      tweakableHashInput parameter (.chain lay tree leaf chain' step') (bytesLE 16 payload')) :
    chain = chain' ∧ step = step' := by
  obtain ⟨hprefix, _⟩ := List.append_inj heq (by
    simp [tweakBytes, fieldBytes, bytesLE_length])
  obtain ⟨_, htweak⟩ := List.append_inj hprefix (by simp [bytesLE_length])
  have hfields := fieldBytes_injective htweak
  have hhi := congrArg TweakFields.hi hfields
  have hstep := congrArg TweakFields.step hfields
  change BitVec.ofNat 24 chain.val = BitVec.ofNat 24 chain'.val at hhi
  change BitVec.ofNat 3 step.val = BitVec.ofNat 3 step'.val at hstep
  have hc : chain.val < 64 := chain.isLt
  have hc' : chain'.val < 64 := chain'.isLt
  have hs : step.val < 3 := step.isLt
  have hs' : step'.val < 3 := step'.isLt
  exact ⟨Fin.ext (ofNat_inj_of_lt (by omega) (by omega) hhi),
    Fin.ext (ofNat_inj_of_lt (by omega) (by omega) hstep)⟩

end Chain
end Sphincs.Security
