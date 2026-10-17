import XmssSecurity.Proof.AdaptiveLeafIndexCollision

open OracleComp ENNReal
open scoped BigOperators

namespace XmssSecurity.AdaptiveRevealMonitor

variable {Index : Type} [Fintype Index] [DecidableEq Index]

structure State (Index : Type) where
  pending : Index → Finset Digest
  revealed : Index → Option Digest

def State.pendingCount (state : State Index) : Nat :=
  ∑ index, (state.pending index).card

def State.addPending (state : State Index) (index : Index) (digest : Digest) : State Index :=
  { state with pending := Function.update state.pending index (insert digest (state.pending index)) }

def State.install (state : State Index) (index : Index) (digest : Digest) : State Index :=
  { pending := Function.update state.pending index ∅
    revealed := Function.update state.revealed index (some digest) }

theorem State.pendingCount_addPending_le
    (state : State Index) (index : Index) (digest : Digest) :
    (state.addPending index digest).pendingCount ≤ state.pendingCount + 1 := by
  classical
  unfold pendingCount addPending
  change (∑ candidate,
      (Function.update state.pending index
        (insert digest (state.pending index)) candidate).card) ≤ _
  have hupdate :
      (fun candidate =>
        (Function.update state.pending index
          (insert digest (state.pending index)) candidate).card) =
        Function.update (fun candidate => (state.pending candidate).card) index
          (insert digest (state.pending index)).card := by
    funext candidate
    by_cases heq : candidate = index <;> simp [heq]
  rw [hupdate, Finset.sum_update_of_mem (Finset.mem_univ index)]
  have hsum := Finset.sum_erase_add Finset.univ
    (fun candidate => (state.pending candidate).card) (Finset.mem_univ index)
  calc
    (insert digest (state.pending index)).card +
        ∑ candidate ∈ Finset.univ \ {index}, (state.pending candidate).card ≤
      ((state.pending index).card + 1) +
        ∑ candidate ∈ Finset.univ \ {index}, (state.pending candidate).card := by
          gcongr
          exact Finset.card_insert_le digest (state.pending index)
    _ = (∑ candidate ∈ Finset.univ \ {index},
          (state.pending candidate).card) + (state.pending index).card + 1 := by
      omega
    _ = (∑ candidate, (state.pending candidate).card) + 1 := by
      rw [Finset.sdiff_singleton_eq_erase, hsum]

theorem State.pendingCount_install_add
    (state : State Index) (index : Index) (digest : Digest) :
    (state.install index digest).pendingCount + (state.pending index).card =
      state.pendingCount := by
  classical
  unfold pendingCount install
  change (∑ candidate,
      (Function.update state.pending index ∅ candidate).card) +
        (state.pending index).card = _
  have hupdate :
      (fun candidate =>
        (Function.update state.pending index ∅ candidate).card) =
        Function.update (fun candidate => (state.pending candidate).card) index 0 := by
    funext candidate
    by_cases heq : candidate = index <;> simp [heq]
  rw [hupdate, Finset.sum_update_of_mem (Finset.mem_univ index), zero_add,
    Finset.sdiff_singleton_eq_erase]
  exact Finset.sum_erase_add Finset.univ
    (fun candidate => (state.pending candidate).card) (Finset.mem_univ index)

def State.empty : State Index :=
  { pending := fun _ => ∅
    revealed := fun _ => none }

omit [DecidableEq Index] in
@[simp]
theorem State.pendingCount_empty : (State.empty : State Index).pendingCount = 0 := by
  simp [State.empty, State.pendingCount]

end XmssSecurity.AdaptiveRevealMonitor
