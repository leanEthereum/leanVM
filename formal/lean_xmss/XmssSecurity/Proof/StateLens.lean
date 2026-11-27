module

public import VCVio.OracleComp.SimSemantics.StateT.Basic

@[expose] public section

/-!
# Simulating through a state lens

A `StateLens` views one component of a state. If every query of an implementation runs a base
query on the viewed component and overwrites only it, so does the simulation of every computation
(`StateLens.simulateQ_run_eq`).
-/

open OracleComp OracleSpec

namespace XmssSecurity

/-- A view of one state component that can be overwritten without changing the rest of the state. -/
structure StateLens (State BaseState : Type) where
  get : State → BaseState
  set : State → BaseState → State
  set_get : ∀ state, set state (get state) = state
  get_set : ∀ state baseState, get (set state baseState) = baseState
  set_set : ∀ state left right, set (set state left) right = set state right

def StateLens.fst {BaseState : Type _} {AuxState : Type _} : StateLens (BaseState × AuxState) BaseState where
  get := Prod.fst
  set state nextBase := (nextBase, state.2)
  set_get := by simp
  get_set := by simp
  set_set := by simp

/-- If every decorated query runs a base query and only overwrites the viewed state component, the same description holds for every oracle computation. -/
theorem StateLens.simulateQ_run_eq {ι : Type _} {α : Type _}
    {spec : OracleSpec ι} {m : Type → Type*} [Monad m] [LawfulMonad m]
    {State BaseState : Type}
    (lens : StateLens State BaseState)
    (decorated : QueryImpl spec (StateT State m))
    (base : QueryImpl spec (StateT BaseState m))
    (hquery : ∀ input state,
      (decorated input).run state =
        (fun result => (result.1, lens.set state result.2)) <$>
          (base input).run (lens.get state))
    (computation : OracleComp spec α) (initialState : State) :
    (simulateQ decorated computation).run initialState =
      (fun result => (result.1, lens.set initialState result.2)) <$>
        (simulateQ base computation).run (lens.get initialState) := by
  induction computation using OracleComp.inductionOn generalizing initialState with
  | pure value => simp [lens.set_get]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, StateT.run_bind, map_bind, id_map]
      rw [hquery input initialState, bind_map_left]
      apply bind_congr
      intro head
      rw [ih head.1 (lens.set initialState head.2), lens.get_set]
      simp [lens.set_set]

end XmssSecurity
