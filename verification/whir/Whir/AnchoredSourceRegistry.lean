import Whir.AnchoredHeaderRoots
import Whir.WHIRSourceChronology

/-! First registration is source-derived from the exact raw key before its first group reply. The underlying root snapshot and historical first-record table are the existing causal state, not a second Merkle verifier convention. Shape/statement identities index immutable header captures while equal roots reuse their earlier frozen table. -/
namespace Whir.AnchoredSourceRegistry
open Concrete FiatShamirGame DuplexModeGame
open MerkleTransport.Commitments
open AnchoredHeaderRoots

structure Frozen where
  snapshot : Snapshot
  records : Records
  log : PublicMerkleLog.PublicLog

structure State (cap : Nat) where
  binding : CausalBindingState.State cap := CausalBindingState.empty cap
  headers : Header → Option Frozen := fun _ => none

/-- No answer, point, value or acceptance evidence is an argument. Every output-block index uses this same first header identity. -/
def register (state : State cap) (header : Header) : State cap :=
  match state.headers header with
  | some _ => state
  | none =>
    let binding := CausalBindingState.registerRoot state.binding header.root
    { binding
      headers := Function.update state.headers header (some
        ⟨(lookup header.root binding.registry).getD (CausalBindingState.snapshot []),
          (binding.frozen header.root).getD [],(binding.frozenLog header.root).getD []⟩) }

def beforeRaw (registry : Public) (state : State cap) {Q : Nat} (key : RawKey Q) : State cap :=
  match rawHeader registry key with
  | none => state
  | some header => register state header

/-- The native step receives the key before allocating its reply. This order prevents a later root, caller-output marker, or original-point value from changing the registered capture. -/
def allocate (registry : Public) (state : State cap) {Q : Nat} (key : RawKey Q)
    (answer : State cap → Digest32 × State cap) : Digest32 × State cap :=
  answer (beforeRaw registry state key)

theorem register_known (state : State cap) (header : Header) :
    ∃ frozen, (register state header).headers header = some frozen := by
  unfold register
  split
  next frozen known => exact ⟨frozen,known⟩
  next unknown => simp

theorem register_root_known (state : State cap) (header : Header)
    (new : state.headers header = none) :
    ∃ snapshot, lookup header.root (register state header).binding.registry = some snapshot := by
  simp only [register,new]
  exact CausalBindingState.registerRoot_known state.binding header.root

theorem register_preserves (state : State cap) (header other : Header) (frozen : Frozen)
    (known : state.headers header = some frozen) :
    (register state other).headers header = some frozen := by
  unfold register
  split
  · exact known
  · rename_i absent
    by_cases same : header = other
    · subst other; rw [known] at absent; contradiction
    · simpa [Function.update_of_ne same] using known

theorem register_binding_extends (state : State cap) (header : Header) :
    CausalBindingState.Extends state.binding (register state header).binding := by
  unfold register
  split
  · exact .refl _
  · exact CausalBindingState.registerRoot_extends _ _

theorem beforeRaw_known (registry : Public) (state : State cap) {Q : Nat} (key : RawKey Q)
    (header : Header) (parsed : rawHeader registry key = some header) :
    ∃ frozen, (beforeRaw registry state key).headers header = some frozen := by
  simp only [beforeRaw,parsed]
  exact register_known state header

theorem beforeRaw_preserves (registry : Public) (state : State cap) {Q : Nat} (key : RawKey Q)
    (header : Header) (frozen : Frozen) (known : state.headers header = some frozen) :
    (beforeRaw registry state key).headers header = some frozen := by
  unfold beforeRaw
  split
  · exact known
  · exact register_preserves state header _ frozen known

theorem beforeRaw_binding_extends (registry : Public) (state : State cap) {Q : Nat} (key : RawKey Q) :
    CausalBindingState.Extends state.binding (beforeRaw registry state key).binding := by
  unfold beforeRaw
  split
  · exact .refl _
  · exact register_binding_extends state _

/-- Replaying more raw requests cannot overwrite root or shape captures. Each first group is prepared at its query, not after a requested block or an adaptive advertised value. -/
def prepareHistory (registry : Public) : State cap → List (RawKey Q) → State cap
  | state,[] => state
  | state,key::rest => prepareHistory registry (beforeRaw registry state key) rest

theorem prepareHistory_preserves (registry : Public) (state : State cap) (keys : List (RawKey Q))
    (header : Header) (frozen : Frozen) (known : state.headers header = some frozen) :
    (prepareHistory registry state keys).headers header = some frozen := by
  induction keys generalizing state with
  | nil => exact known
  | cons key rest ih => exact ih _ (beforeRaw_preserves registry state key header frozen known)

theorem first_query_freezes (registry : Public) (state : State cap) (key : RawKey Q)
    (rest : List (RawKey Q)) (header : Header) (parsed : rawHeader registry key = some header) :
    ∃ frozen, (beforeRaw registry state key).headers header = some frozen ∧
      (prepareHistory registry state (key::rest)).headers header = some frozen := by
  obtain ⟨frozen,known⟩ := beforeRaw_known registry state key header parsed
  exact ⟨frozen,known,prepareHistory_preserves registry _ rest header frozen known⟩

end Whir.AnchoredSourceRegistry
