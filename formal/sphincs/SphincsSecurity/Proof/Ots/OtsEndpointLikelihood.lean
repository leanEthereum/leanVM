import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Chains.AdaptiveChainEndpoint
import SphincsSecurity.Proof.Hypertree.Extract
import SphincsSecurity.Proof.Ots.OneTime
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] chainWalk
noncomputable local instance instDecidableEqQueryImplHashInputHashSpecId : DecidableEq (QueryImpl HashSpec Id) := Classical.decEq _

noncomputable def otsChainFunctions (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start steps : Nat) (f : QueryImpl HashSpec Id) :
    Fin steps → Digest → Digest :=
  fun step value => evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx (start + step.val) 1 value)

theorem otsChainFunctions_tail (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start steps : Nat) (f : QueryImpl HashSpec Id) :
    Fin.tail (otsChainFunctions parameter lay tree leaf chainIdx start (steps + 1) f) =
      otsChainFunctions parameter lay tree leaf chainIdx (start + 1) steps f := by
  funext step value
  simp only [Fin.tail, otsChainFunctions, Fin.val_succ, Nat.add_right_comm start 1 step.val,
    Nat.add_assoc]

theorem otsChainFunctions_apply (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start steps : Nat) (f : QueryImpl HashSpec Id)
    (step : Fin steps) (hstep : start + step.val < chainLength - 1) (value : Digest) :
    otsChainFunctions parameter lay tree leaf chainIdx start steps f step value =
      truncateHash (f (tweakableHashInput parameter (.chain lay tree leaf chainIdx ⟨start + step.val, hstep⟩)
        (digestBytes value))) := by
  simp only [otsChainFunctions, chainWalk, Nat.add_zero, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    dif_pos hstep, eval_tweakableHash]

theorem otsChainFunctions_evaluate (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start steps : Nat) (f : QueryImpl HashSpec Id) (value : Digest) :
    PartialChainEndpoint.evaluate (otsChainFunctions parameter lay tree leaf chainIdx start steps f) value =
      evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start steps value) := by
  induction steps generalizing start value with
  | zero => simp only [PartialChainEndpoint.evaluate, chainWalk, evalWithAnswerFn_pure]
  | succ steps ih =>
      rw [PartialChainEndpoint.evaluate, otsChainFunctions_tail, ih]
      change evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx (start + 1) steps
        (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start 1 value))) = _
      simpa only [Nat.add_comm 1 steps] using
        (eval_chainWalk_add f parameter lay tree leaf chainIdx start 1 steps value).symm

end SphincsSecurity.Concrete
