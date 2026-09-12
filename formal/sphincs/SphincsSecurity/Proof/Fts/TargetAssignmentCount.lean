import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeProbability
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def targetTreeMatchCount {n : Nat} (views : Fin n → Option FewTimeView) (target : FewTimeView) (tree : FtsTree) : Nat :=
  ∑ slot : Fin n, if ∃ view, views slot = some view ∧ view.1 = target.1 ∧ view.2 tree = target.2 tree then 1 else 0

noncomputable def sourceTreeMatch (target source : FewTimeView) (tree : FtsTree) : Nat :=
  if source.1 = target.1 ∧ source.2 tree = target.2 tree then 1 else 0

theorem targetTreeMatchCount_pos_iff {n : Nat} (views : Fin n → Option FewTimeView) (target : FewTimeView) (tree : FtsTree) :
    0 < targetTreeMatchCount views target tree ↔ ∃ slot view, views slot = some view ∧ view.1 = target.1 ∧ view.2 tree = target.2 tree := by
  simp only [targetTreeMatchCount, Finset.sum_pos_iff, Finset.mem_univ, true_and]
  apply exists_congr
  intro slot
  split_ifs <;> simp_all

end SphincsSecurity.Concrete
