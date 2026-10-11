import Whir.PublicCompressionCouplingPublicTrace
import Whir.PublicCompressionCouplingHidden

/-! Backward public-body closure of actual seed trees. A target-matching private
seed answer is exposed only through an actual earlier public seed coordinate;
chosen CVs themselves are never forbidden. -/
namespace Whir.PublicCompressionCouplingRecognition
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame DuplexPublicSimulator
open PublicCompressionCouplingMixed

/-- Once target-matching nodes have been recovered from actual cache support,
closure is a deterministic induction on the actual seed compression tree. -/
 theorem Tree.publicBody_of_exposure {seedTable : Seed} {cv : Digest32} {ns : List Node}
    (tree : Tree (compressionOf seedTable) cv ns) (log : PublicLog) (targets : Finset Digest32)
    (publicInputs : ∀ n d, (n,d) ∈ log → n.cv ∈ targets)
    (exposed : ∀ n ∈ ns, seedTable n ∈ targets → (n,seedTable n) ∈ log)
    (rootTarget : cv ∈ targets) : PublicBody log cv ns := by
  induction tree with
  | seed node valid =>
    exact PublicBody.seed (exposed node (by simp) rootTarget) valid
  | step node rest internal child ih =>
    have member := exposed node (by simp) rootTarget
    apply PublicBody.step member internal
    apply ih
    · intro n hn hit
      exact exposed n (List.mem_cons_of_mem _ hn) hit
    · exact publicInputs node (seedTable node) member

 theorem publicCVTargets_contains (observations : List Observation) {input : Node} {answer : Digest32}
    (member : (input,answer) ∈ finalLog [] observations) : input.cv ∈ publicCVTargets observations := by
  suffices generalized : ∀ (log : PublicLog) (observations : List Observation),
      (input,answer) ∈ finalLog log observations →
      (input,answer) ∈ log ∨ input.cv ∈ publicCVTargets observations by
    exact (generalized [] observations member).resolve_left (by simp)
  intro log observations
  induction observations generalizing log with
  | nil => exact fun member => Or.inl member
  | cons observation rest ih =>
    rcases observation with ⟨query,digest⟩
    cases query with
    | primitive purpose node =>
      intro member
      rcases ih (observe log node digest) member with prior | later
      · rcases List.mem_cons.mp prior with equal | old
        · have nodes := congrArg Prod.fst equal
          dsimp only at nodes
          subst node
          exact Or.inr (Finset.mem_insert_self _ _)
        · exact Or.inl old
      · exact Or.inr (Finset.mem_insert_of_mem later)
    | construction coordinate valid => exact ih log

#print axioms Tree.publicBody_of_exposure
#print axioms publicCVTargets_contains
end Whir.PublicCompressionCouplingRecognition
