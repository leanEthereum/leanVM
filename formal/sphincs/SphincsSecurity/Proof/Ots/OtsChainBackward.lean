import SphincsSecurity.Proof.Ots.OtsTwoEdgeTrace
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
  (leaf : LeafIndex) (chainIdx : ChainIndex) (secret : Digest)

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

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete.OtsContactTrace

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] chainWalk

def ContainsRun {Result : Type} (f : QueryImpl HashSpec Id) (trace : Trace)
    (computation : OracleComp HashSpec Result) : Prop :=
  ∀ input ∈ queriedInputs f computation, (input, f input) ∈ trace.toList

theorem ContainsRun.bind_left {Result Next : Type} {f : QueryImpl HashSpec Id} {trace : Trace}
    {computation : OracleComp HashSpec Result} {next : Result → OracleComp HashSpec Next}
    (h : ContainsRun f trace (computation >>= next)) : ContainsRun f trace computation :=
  fun _ hi => h _ (queriedInputs_mono_bind_left f computation next hi)

theorem ContainsRun.bind_right {Result Next : Type} {f : QueryImpl HashSpec Id} {trace : Trace}
    {computation : OracleComp HashSpec Result} {next : Result → OracleComp HashSpec Next}
    (h : ContainsRun f trace (computation >>= next)) : ContainsRun f trace (next (evalWithAnswerFn f computation)) :=
  fun _ hi => h _ (queriedInputs_mono_bind_right f computation next hi)

theorem ContainsRun.sequenceFin_component {Result : Type} {n : Nat} {f : QueryImpl HashSpec Id} {trace : Trace}
    (computation : Fin n → OracleComp HashSpec Result) (h : ContainsRun f trace (sequenceFin computation)) (index : Fin n) :
    ContainsRun f trace (computation index) :=
  fun _ hi => h _ (sequenceFin_component_query_mem f computation index hi)

def ForwardChainMatch (f : QueryImpl HashSpec Id) (segment : OtsPrefix) (secret : Digest) (trace : Trace) : Prop :=
  ∃ (step : ChainStep) (payload : Digest), segment.digit.val ≤ step.val ∧
    (tweakableHashInput segment.parameter (.chain segment.lay segment.tree segment.leaf segment.chainIdx step) (digestBytes payload),
      f (tweakableHashInput segment.parameter (.chain segment.lay segment.tree segment.leaf segment.chainIdx step) (digestBytes payload)))
        ∈ trace.toList ∧
    ChainHit f segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx secret step.val step.isLt payload

variable (f : QueryImpl HashSpec Id) (segment : OtsPrefix) (secret value : Digest) (digit : Digit) (trace : Trace)

theorem recover_canonical_above (cutoff : Nat) (hcut : cutoff ≤ chainLength - 1 - digit.val)
    (habove : segment.digit.val ≤ digit.val + cutoff)
    (hendpoint : evalWithAnswerFn f (recoverChain segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx digit value)
      = honestChain f segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx secret (chainLength - 1))
    (hrun : ContainsRun f trace (recoverChain segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx digit value))
    (hforward : ¬ForwardChainMatch f segment secret trace) :
    walkValue f segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx digit.val value cutoff
      = honestChain f segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx secret (digit.val + cutoff) := by
  have hd : digit.val ≤ chainLength - 1 := Nat.le_pred_of_lt digit.isLt
  have hwalk : walkValue f segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx digit.val value
      (chainLength - 1 - digit.val) = honestChain f segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx secret
        (digit.val + (chainLength - 1 - digit.val)) := by
    simpa only [walkValue, recoverChain, Nat.add_sub_of_le hd] using hendpoint
  rcases chainWalk_extract_above f segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx secret digit.val value
      (chainLength - 1 - digit.val) cutoff (by omega) hcut hwalk with h | ⟨offset, ho, hc, hs, hh⟩
  · exact h
  · exact False.elim (hforward ⟨⟨digit.val + offset, ho⟩, _, by dsimp; omega,
      hrun _ (chainWalk_query_mem f segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx digit.val
        (chainLength - 1 - digit.val) value offset hs ho), hh⟩)

theorem recover_frontier (hbelow : digit.val ≤ segment.digit.val)
    (hendpoint : evalWithAnswerFn f (recoverChain segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx digit value)
      = honestChain f segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx secret (chainLength - 1))
    (hrun : ContainsRun f trace (recoverChain segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx digit value))
    (hforward : ¬ForwardChainMatch f segment secret trace) :
    walkValue f segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx digit.val value (segment.digit.val - digit.val)
      = honestChain f segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx secret segment.digit.val := by
  have hd : segment.digit.val ≤ chainLength - 1 := Nat.le_pred_of_lt segment.digit.isLt
  simpa only [Nat.add_sub_of_le hbelow] using
    recover_canonical_above f segment secret value digit trace (segment.digit.val - digit.val) (by omega) (by omega) hendpoint hrun hforward

theorem recover_value (habove : segment.digit.val ≤ digit.val)
    (hendpoint : evalWithAnswerFn f (recoverChain segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx digit value)
      = honestChain f segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx secret (chainLength - 1))
    (hrun : ContainsRun f trace (recoverChain segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx digit value))
    (hforward : ¬ForwardChainMatch f segment secret trace) :
    value = honestChain f segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx secret digit.val := by
  simpa only [walkValue, chainWalk, evalWithAnswerFn_pure, Nat.add_zero] using
    recover_canonical_above f segment secret value digit trace 0 (by omega) (by omega) hendpoint hrun hforward

theorem recover_row (offset : Nat) (hprefix : digit.val + offset < segment.digit.val)
    (hrun : ContainsRun f trace (recoverChain segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx digit value)) :
    SeenRow segment ⟨⟨digit.val + offset, hprefix⟩,
      walkValue f segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx digit.val value offset⟩
      (walkValue f segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx digit.val value (offset + 1)) trace := by
  have hd : segment.digit.val ≤ chainLength - 1 := Nat.le_pred_of_lt segment.digit.isLt
  have ho : digit.val + offset < chainLength - 1 := by omega
  refine ⟨_, hrun _ (chainWalk_query_mem f segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx digit.val
    (chainLength - 1 - digit.val) value offset (by omega) ho), ?_, ?_⟩
  · exact segment.parse_input ⟨⟨digit.val + offset, hprefix⟩,
      walkValue f segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx digit.val value offset⟩
  · exact (walkValue_succ f segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx digit.val value offset ho).symm

theorem recover_contact (hbelow : digit.val < segment.digit.val) (endpoint : Digest)
    (hfrontier : walkValue f segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx digit.val value
      (segment.digit.val - digit.val) = endpoint)
    (hrun : ContainsRun f trace (recoverChain segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx digit value)) :
    Seen segment endpoint trace := by
  have ho : digit.val + (segment.digit.val - digit.val - 1) < segment.digit.val := by omega
  have hr := recover_row f segment value digit trace (segment.digit.val - digit.val - 1) ho hrun
  rw [show segment.digit.val - digit.val - 1 + 1 = segment.digit.val - digit.val by omega, hfrontier] at hr
  obtain ⟨entry, he, hp, hv⟩ := hr
  exact ⟨entry, he, _, hp, by dsimp; omega, hv⟩

theorem recover_twoEdge (hbelow : digit.val + 2 ≤ segment.digit.val) (endpoint : Digest)
    (hfrontier : walkValue f segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx digit.val value
      (segment.digit.val - digit.val) = endpoint)
    (hrun : ContainsRun f trace (recoverChain segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx digit value)) :
    SeenTwoEdge segment endpoint trace := by
  have hf : digit.val + (segment.digit.val - digit.val - 2) < segment.digit.val := by omega
  have hl : digit.val + (segment.digit.val - digit.val - 1) < segment.digit.val := by omega
  refine ⟨⟨⟨_, hf⟩, walkValue f segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx digit.val value
    (segment.digit.val - digit.val - 2)⟩,
    ⟨⟨_, hl⟩, walkValue f segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx digit.val value
      (segment.digit.val - digit.val - 1)⟩, ?_, ?_, ?_, ?_⟩
  · dsimp; omega
  · dsimp; omega
  · simpa only [show segment.digit.val - digit.val - 2 + 1 = segment.digit.val - digit.val - 1 by omega] using
      recover_row f segment value digit trace (segment.digit.val - digit.val - 2) hf hrun
  · have hr := recover_row f segment value digit trace (segment.digit.val - digit.val - 1) hl hrun
    rw [show segment.digit.val - digit.val - 1 + 1 = segment.digit.val - digit.val by omega, hfrontier] at hr
    simpa only [show segment.digit.val - digit.val - 2 + 1 = segment.digit.val - digit.val - 1 by omega] using hr

end SphincsSecurity.Concrete.OtsContactTrace
