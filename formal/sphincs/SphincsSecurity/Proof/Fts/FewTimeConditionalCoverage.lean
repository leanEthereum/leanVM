import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeProbability
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def CoveredFewTimeView {n : Nat} (views : Fin n → Option FewTimeView) (target : FewTimeView) : Prop :=
  ∀ tree, ∃ slot view, views slot = some view ∧ view.1 = target.1 ∧ view.2 tree = target.2 tree

noncomputable def signingSlotsAtIndex {n : Nat} (views : Fin n → Option FewTimeView) (index : Index) : Finset (Fin n) :=
  Finset.univ.filter (fun slot => ∃ view, views slot = some view ∧ view.1 = index)

end SphincsSecurity.Concrete
