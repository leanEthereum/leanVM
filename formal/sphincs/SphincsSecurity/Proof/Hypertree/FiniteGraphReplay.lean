import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.FiniteGraphSampling
namespace SphincsSecurity.Concrete.FiniteGraphSampling

open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false

variable {Node Cell Answer State : Type} [DecidableEq Node] [DecidableEq Cell]

def replay (input : Node → State → Cell) (advance : Node → Answer → State → State)
    (answers : Node → Answer) (table : Cell → Answer) : List Node → State → State × (Cell → Answer)
  | [], state => (state, table)
  | node :: nodes, state =>
      let result := replay input advance answers table nodes (advance node (answers node) state)
      (result.1, Function.update result.2 (input node state) (answers node))

omit [DecidableEq Node] in
theorem replay_congr (input : Node → State → Cell) (advance : Node → Answer → State → State)
    (left right : Node → Answer) (table : Cell → Answer) (nodes : List Node)
    (hagrees : ∀ node ∈ nodes, left node = right node) (state : State) :
    replay input advance left table nodes state = replay input advance right table nodes state := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node nodes ih =>
      have hfirst := hagrees node List.mem_cons_self
      have hrest := ih (fun other hother => hagrees other (List.mem_cons_of_mem _ hother))
      simp only [replay, hfirst, hrest]

theorem replay_update_of_not_mem (input : Node → State → Cell) (advance : Node → Answer → State → State)
    (answers : Node → Answer) (table : Cell → Answer) (nodes : List Node)
    (node : Node) (hnode : node ∉ nodes) (answer : Answer) (state : State) :
    replay input advance (Function.update answers node answer) table nodes state =
      replay input advance answers table nodes state := by
  apply replay_congr
  intro other hother
  have hne : other ≠ node := by
    intro heq
    subst other
    exact hnode hother
  rw [Function.update_of_ne hne]

def patch (input : Node → Cell) (answers : Node → Answer) (table : Cell → Answer) : List Node → Cell → Answer
  | [] => table
  | node :: nodes => Function.update (patch input answers table nodes) (input node) (answers node)

omit [DecidableEq Node] in
theorem patch_of_forall_ne (input : Node → Cell) (answers : Node → Answer) (table : Cell → Answer)
    (nodes : List Node) (cell : Cell) (hne : ∀ node ∈ nodes, cell ≠ input node) :
    patch input answers table nodes cell = table cell := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih =>
      rw [patch, Function.update_of_ne (hne node List.mem_cons_self)]
      exact ih (fun other hother => hne other (List.mem_cons_of_mem _ hother))

theorem patch_at (input : Node → Cell) (hinjective : Function.Injective input)
    (answers : Node → Answer) (table : Cell → Answer) (nodes : List Node) (node : Node) (hnode : node ∈ nodes) :
    patch input answers table nodes (input node) = answers node := by
  induction nodes with
  | nil => cases hnode
  | cons first rest ih =>
      by_cases heq : node = first
      · subst node
        exact Function.update_self _ _ _
      · rw [patch, Function.update_of_ne (fun h => heq (hinjective h))]
        exact ih ((List.mem_cons.mp hnode).resolve_left heq)

variable [_root_.Finite Node] [_root_.Finite Cell] [_root_.Finite Answer] [Nonempty Answer]
  [SampleableType Answer] [SampleableType (Node → Answer)] [SampleableType (Cell → Answer)]

omit [_root_.Finite Cell] in
theorem evalDist_plant_eq_replay (input : Node → State → Cell) (advance : Node → Answer → State → State)
    (nodes : List Node) (hnodes : nodes.Nodup) (state : State) :
    𝒟[plant input advance nodes state] =
      𝒟[do
        let answers ← ($ᵗ (Node → Answer) : ProbComp _)
        let table ← ($ᵗ (Cell → Answer) : ProbComp _)
        pure (replay input advance answers table nodes state)] := by
  induction nodes generalizing state with
  | nil =>
      simp only [plant, replay]
      exact (evalDist_bind_const_neverFails _ (by simp) _).symm
  | cons node nodes ih =>
      obtain ⟨hnode, hnodes⟩ := List.nodup_cons.mp hnodes
      have hextract := evalDist_table_extract node (fun answers answer => do
        let table ← ($ᵗ (Cell → Answer) : ProbComp _)
        let result := replay input advance answers table nodes (advance node answer state)
        pure (result.1, Function.update result.2 (input node state) answer))
      change 𝒟[plant input advance (node :: nodes) state] =
        𝒟[do
          let answers ← ($ᵗ (Node → Answer) : ProbComp _)
          let table ← ($ᵗ (Cell → Answer) : ProbComp _)
          let result := replay input advance answers table nodes (advance node (answers node) state)
          pure (result.1, Function.update result.2 (input node state) (answers node))]
      rw [hextract]
      simp_rw [replay_update_of_not_mem input advance _ _ nodes node hnode]
      simp only [plant]
      apply evalDist_bind_congr_left
      intro answer
      have h := congrArg (fun distribution : SPMF (State × (Cell → Answer)) =>
        distribution >>= fun result => pure (result.1, Function.update result.2 (input node state) answer))
        (ih hnodes (advance node answer state))
      simpa only [evalDist_bind, evalDist_pure, bind_assoc, pure_bind] using h

end SphincsSecurity.Concrete.FiniteGraphSampling
