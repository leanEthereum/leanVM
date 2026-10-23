import SphincsBase.Proof.Base.Prelude
import SphincsBase.Proof.Hypertree.FiniteGraphSampling
namespace SphincsBase.Concrete.FiniteGraphSampling

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
    plant input advance nodes state =ᵈ (do
        let answers ← ($ᵗ (Node → Answer) : ProbComp _)
        let table ← ($ᵗ (Cell → Answer) : ProbComp _)
        pure (replay input advance answers table nodes state)) := by
  induction nodes generalizing state with
  | nil =>
      simp only [plant, replay]
      exact (OracleComp.EvalDistEq.bind_const _ _).symm
  | cons node nodes ih =>
      obtain ⟨hnode, hnodes⟩ := List.nodup_cons.mp hnodes
      have hextract := evalDist_table_extract node (fun answers answer => do
        let table ← ($ᵗ (Cell → Answer) : ProbComp _)
        let result := replay input advance answers table nodes (advance node answer state)
        pure (result.1, Function.update result.2 (input node state) answer))
      change plant input advance (node :: nodes) state =ᵈ (do
          let answers ← ($ᵗ (Node → Answer) : ProbComp _)
          let table ← ($ᵗ (Cell → Answer) : ProbComp _)
          let result := replay input advance answers table nodes (advance node (answers node) state)
          pure (result.1, Function.update result.2 (input node state) (answers node)))
      refine EvalDistEq.trans ?_ hextract.symm
      simp_rw [replay_update_of_not_mem input advance _ _ nodes node hnode]
      simp only [plant]
      refine EvalDistEq.bind_right _ fun answer => ?_
      have h := (ih hnodes (advance node answer state)).map
        (fun result : State × (Cell → Answer) => (result.1, Function.update result.2 (input node state) answer))
      simpa only [map_bind, map_pure, bind_pure_comp, Functor.map_map] using h

end SphincsBase.Concrete.FiniteGraphSampling
