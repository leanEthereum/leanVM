import XmssSecurity.Proof.AdaptiveFreshTarget
import VCVio.OracleComp.Constructions.SampleableType

open OracleComp ENNReal
open scoped BigOperators

namespace XmssSecurity.EncodingMonitor

set_option maxRecDepth 100000

structure State where
  pending : LeafIndex → Finset Digest
  signed : LeafIndex → Option Digest

def State.pendingCount (state : State) : Nat :=
  ∑ leafIndex, (state.pending leafIndex).card

def State.addPending (state : State) (leafIndex : LeafIndex) (digest : Digest) : State :=
  { state with pending := Function.update state.pending leafIndex (insert digest (state.pending leafIndex)) }

def State.install (state : State) (leafIndex : LeafIndex) (digest : Digest) : State :=
  { pending := Function.update state.pending leafIndex ∅
    signed := Function.update state.signed leafIndex (some digest) }

theorem State.pendingCount_addPending_le (state : State) (leafIndex : LeafIndex)
    (digest : Digest) :
    (state.addPending leafIndex digest).pendingCount ≤ state.pendingCount + 1 := by
  classical
  unfold pendingCount addPending
  change (∑ candidate,
      (Function.update state.pending leafIndex
        (insert digest (state.pending leafIndex)) candidate).card) ≤ _
  have hupdate :
      (fun candidate =>
        (Function.update state.pending leafIndex
          (insert digest (state.pending leafIndex)) candidate).card) =
        Function.update (fun candidate => (state.pending candidate).card) leafIndex
          (insert digest (state.pending leafIndex)).card := by
    funext candidate
    by_cases heq : candidate = leafIndex <;> simp [heq]
  rw [hupdate]
  rw [Finset.sum_update_of_mem (Finset.mem_univ leafIndex)]
  have hsum := Finset.sum_erase_add Finset.univ
    (fun candidate => (state.pending candidate).card) (Finset.mem_univ leafIndex)
  calc
    (insert digest (state.pending leafIndex)).card +
        ∑ candidate ∈ Finset.univ \ {leafIndex}, (state.pending candidate).card ≤
      ((state.pending leafIndex).card + 1) +
        ∑ candidate ∈ Finset.univ \ {leafIndex}, (state.pending candidate).card := by
          gcongr
          exact Finset.card_insert_le digest (state.pending leafIndex)
    _ = (∑ candidate ∈ Finset.univ \ {leafIndex},
          (state.pending candidate).card) + (state.pending leafIndex).card + 1 := by
      omega
    _ = (∑ candidate, (state.pending candidate).card) + 1 := by
      rw [Finset.sdiff_singleton_eq_erase, hsum]

theorem State.pendingCount_install_add (state : State) (leafIndex : LeafIndex)
    (digest : Digest) :
    (state.install leafIndex digest).pendingCount + (state.pending leafIndex).card =
      state.pendingCount := by
  classical
  unfold pendingCount install
  change (∑ candidate,
      (Function.update state.pending leafIndex ∅ candidate).card) +
        (state.pending leafIndex).card = _
  have hupdate :
      (fun candidate =>
        (Function.update state.pending leafIndex ∅ candidate).card) =
        Function.update (fun candidate => (state.pending candidate).card) leafIndex 0 := by
    funext candidate
    by_cases heq : candidate = leafIndex <;> simp [heq]
  rw [hupdate]
  rw [Finset.sum_update_of_mem (Finset.mem_univ leafIndex)]
  rw [zero_add, Finset.sdiff_singleton_eq_erase]
  exact Finset.sum_erase_add Finset.univ
    (fun candidate => (state.pending candidate).card) (Finset.mem_univ leafIndex)

theorem State.pendingCount_install_eq (state : State) (leafIndex : LeafIndex)
    (left right : Digest) :
    (state.install leafIndex left).pendingCount =
      (state.install leafIndex right).pendingCount := by
  rfl

def State.empty : State :=
  { pending := fun _ => ∅
    signed := fun _ => none }

@[simp]
theorem State.pendingCount_empty : State.empty.pendingCount = 0 := by
  unfold empty pendingCount
  simp

attribute [irreducible] State.pendingCount

inductive ObservedAction where
  | query (leafIndex : LeafIndex) (output : HashOutput)
  | sign (leafIndex : LeafIndex) (output : HashOutput)

def ObservedAction.IsSignAt (target : LeafIndex) : ObservedAction → Prop
  | .query _ _ => False
  | .sign leafIndex _ => leafIndex = target

def observedSignLeafIndices : List ObservedAction → List LeafIndex
  | [] => []
  | .query _ _ :: actions => observedSignLeafIndices actions
  | .sign leafIndex _ :: actions => leafIndex :: observedSignLeafIndices actions

@[simp]
theorem observedSignLeafIndices_append (left right : List ObservedAction) :
    observedSignLeafIndices (left ++ right) =
      observedSignLeafIndices left ++ observedSignLeafIndices right := by
  induction left with
  | nil => rfl
  | cons action left ih =>
      cases action <;> simp [observedSignLeafIndices, ih]

def State.applyObserved (state : State) : ObservedAction → Option (State × Bool)
  | .query leafIndex output =>
      let digest := truncateHash output
      match state.signed leafIndex with
      | some target => some (state, digest = target)
      | none => some (state.addPending leafIndex digest, false)
  | .sign leafIndex output =>
      match state.signed leafIndex with
      | some _ => none
      | none =>
          let digest := truncateHash output
          some (state.install leafIndex digest, digest ∈ state.pending leafIndex)

def runObserved : State → List ObservedAction → Bool
  | _state, [] => false
  | state, action :: actions =>
      match state.applyObserved action with
      | none => false
      | some (nextState, hit) => hit || runObserved nextState actions

@[simp]
theorem runObserved_cons (state : State) (action : ObservedAction)
    (actions : List ObservedAction) :
    runObserved state (action :: actions) =
      match state.applyObserved action with
      | none => false
      | some (nextState, hit) => hit || runObserved nextState actions := rfl

structure ReplayResult where
  state : State
  hit : Bool
  valid : Bool

def State.applyObservedTotal (state : State) : ObservedAction → ReplayResult
  | .query leafIndex output =>
      let digest := truncateHash output
      match state.signed leafIndex with
      | some target => ⟨state, digest = target, true⟩
      | none => ⟨state.addPending leafIndex digest, false, true⟩
  | .sign leafIndex output =>
      match state.signed leafIndex with
      | some _ => ⟨state, false, false⟩
      | none =>
          let digest := truncateHash output
          ⟨state.install leafIndex digest, digest ∈ state.pending leafIndex, true⟩

def replayObserved : State → List ObservedAction → ReplayResult
  | state, [] => ⟨state, false, true⟩
  | state, action :: actions =>
      let head := state.applyObservedTotal action
      let tail := replayObserved head.state actions
      ⟨tail.state, head.hit || tail.hit, head.valid && tail.valid⟩

@[simp]
theorem replayObserved_cons (state : State) (action : ObservedAction)
    (actions : List ObservedAction) :
    replayObserved state (action :: actions) =
      let head := state.applyObservedTotal action
      let tail := replayObserved head.state actions
      ⟨tail.state, head.hit || tail.hit, head.valid && tail.valid⟩ := rfl

theorem replayObserved_valid_iff (state : State) (actions : List ObservedAction) :
    (replayObserved state actions).valid = true ↔
      (∀ leafIndex ∈ observedSignLeafIndices actions, state.signed leafIndex = none) ∧
        (observedSignLeafIndices actions).Nodup := by
  induction actions generalizing state with
  | nil => simp [replayObserved, observedSignLeafIndices]
  | cons action actions ih =>
      cases action with
      | query leafIndex output =>
          cases hsigned : state.signed leafIndex <;>
            simp [replayObserved, State.applyObservedTotal, observedSignLeafIndices,
              hsigned, ih, State.addPending]
      | sign leafIndex output =>
          cases hsigned : state.signed leafIndex with
          | none =>
              rw [replayObserved_cons]
              simp only [State.applyObservedTotal, hsigned, Bool.true_and, ih,
                observedSignLeafIndices, List.mem_cons, forall_eq_or_imp, List.nodup_cons]
              have htail :
                  (∀ candidate ∈ observedSignLeafIndices actions,
                      (state.install leafIndex (truncateHash output)).signed candidate = none) ↔
                    leafIndex ∉ observedSignLeafIndices actions ∧
                      ∀ candidate ∈ observedSignLeafIndices actions,
                        state.signed candidate = none := by
                constructor
                · intro hall
                  constructor
                  · intro hleafIndex
                    have := hall leafIndex hleafIndex
                    simp [State.install] at this
                  · intro candidate hcandidate
                    have hnone := hall candidate hcandidate
                    have hne : candidate ≠ leafIndex := by
                      intro heq
                      subst candidate
                      have := hall leafIndex hcandidate
                      simp [State.install] at this
                    simpa [State.install, hne] using hnone
                · rintro ⟨hleafIndex, hall⟩ candidate hcandidate
                  have hne : candidate ≠ leafIndex := by
                    intro heq
                    subst candidate
                    exact hleafIndex hcandidate
                  simpa [State.install, hne] using
                    hall candidate hcandidate
              rw [htail]
              simp [and_assoc, and_comm]
          | some target =>
              rw [replayObserved_cons]
              simp only [State.applyObservedTotal, hsigned, Bool.false_and,
                Bool.false_eq_true, false_iff, observedSignLeafIndices, List.mem_cons,
                forall_eq_or_imp]
              simp

@[simp]
theorem replayObserved_empty_valid_iff (actions : List ObservedAction) :
    (replayObserved State.empty actions).valid = true ↔
      (observedSignLeafIndices actions).Nodup := by
  rw [replayObserved_valid_iff]
  simp [State.empty]

theorem runObserved_eq_replayObserved_hit_of_valid
    (state : State) (actions : List ObservedAction)
    (hvalid : (replayObserved state actions).valid = true) :
    runObserved state actions = (replayObserved state actions).hit := by
  induction actions generalizing state with
  | nil => rfl
  | cons action actions ih =>
      cases action with
      | query leafIndex output =>
          cases hsigned : state.signed leafIndex <;>
            simp only [runObserved, State.applyObserved, hsigned, replayObserved,
              State.applyObservedTotal, Bool.true_and] at hvalid ⊢
          · rw [ih _ hvalid]
          · rw [ih _ hvalid]
      | sign leafIndex output =>
          cases hsigned : state.signed leafIndex with
          | none =>
              simp only [runObserved, State.applyObserved, hsigned, replayObserved,
                State.applyObservedTotal, Bool.true_and] at hvalid ⊢
              rw [ih _ hvalid]
          | some target =>
              simp [replayObserved, State.applyObservedTotal, hsigned] at hvalid

theorem replayObserved_append (state : State)
    (left right : List ObservedAction) :
    replayObserved state (left ++ right) =
      let firstResult := replayObserved state left
      let secondResult := replayObserved firstResult.state right
      ⟨secondResult.state, firstResult.hit || secondResult.hit,
        firstResult.valid && secondResult.valid⟩ := by
  induction left generalizing state with
  | nil => rfl
  | cons action left ih =>
      simp only [List.cons_append, replayObserved_cons]
      rw [ih]
      simp [Bool.or_assoc, Bool.and_assoc]

theorem replayObserved_state_signed_eq_of_not_mem
    (state : State) (actions : List ObservedAction) (leafIndex : LeafIndex)
    (hnot : leafIndex ∉ observedSignLeafIndices actions) :
    (replayObserved state actions).state.signed leafIndex = state.signed leafIndex := by
  induction actions generalizing state with
  | nil => rfl
  | cons action actions ih =>
      cases action with
      | query queriedLeafIndex output =>
          have htail : leafIndex ∉ observedSignLeafIndices actions := by
            simpa [observedSignLeafIndices] using hnot
          cases hsigned : state.signed queriedLeafIndex with
          | some target =>
              rw [replayObserved_cons]
              simp only [State.applyObservedTotal, hsigned]
              exact ih state htail
          | none =>
              rw [replayObserved_cons]
              simp only [State.applyObservedTotal, hsigned]
              exact (ih (state.addPending queriedLeafIndex (truncateHash output)) htail).trans
                (by rfl)
      | sign signedLeafIndex output =>
          have hsignedNe : signedLeafIndex ≠ leafIndex := by
            intro heq
            subst signedLeafIndex
            exact hnot (by simp [observedSignLeafIndices])
          have htail : leafIndex ∉ observedSignLeafIndices actions := by
            intro hmem
            exact hnot (by simp [observedSignLeafIndices, hmem])
          cases hsigned : state.signed signedLeafIndex with
          | none =>
              rw [replayObserved_cons]
              simp only [State.applyObservedTotal, hsigned]
              rw [ih (state.install signedLeafIndex (truncateHash output)) htail]
              simp [State.install, Ne.symm hsignedNe]
          | some target =>
              rw [replayObserved_cons]
              simp only [State.applyObservedTotal, hsigned]
              exact ih state htail

theorem replayObserved_pending_mono_of_not_mem
    (state : State) (actions : List ObservedAction) (leafIndex : LeafIndex)
    (hnot : leafIndex ∉ observedSignLeafIndices actions) :
    state.pending leafIndex ⊆ (replayObserved state actions).state.pending leafIndex := by
  induction actions generalizing state with
  | nil => exact fun _ hmem => hmem
  | cons action actions ih =>
      cases action with
      | query queriedLeafIndex output =>
          have htail : leafIndex ∉ observedSignLeafIndices actions := by
            simpa [observedSignLeafIndices] using hnot
          cases hsigned : state.signed queriedLeafIndex with
          | some target =>
              rw [replayObserved_cons]
              simp only [State.applyObservedTotal, hsigned]
              exact ih state htail
          | none =>
              rw [replayObserved_cons]
              simp only [State.applyObservedTotal, hsigned]
              refine fun digest hdigest => ih (state.addPending queriedLeafIndex
                (truncateHash output)) htail ?_
              by_cases heq : queriedLeafIndex = leafIndex
              · subst queriedLeafIndex
                simpa [State.addPending] using Finset.mem_insert_of_mem hdigest
              · simpa [State.addPending, Ne.symm heq] using hdigest
      | sign signedLeafIndex output =>
          have hsignedNe : signedLeafIndex ≠ leafIndex := by
            intro heq
            subst signedLeafIndex
            exact hnot (by simp [observedSignLeafIndices])
          have htail : leafIndex ∉ observedSignLeafIndices actions := by
            intro hmem
            exact hnot (by simp [observedSignLeafIndices, hmem])
          cases hsigned : state.signed signedLeafIndex with
          | some target =>
              rw [replayObserved_cons]
              simp only [State.applyObservedTotal, hsigned]
              exact ih state htail
          | none =>
              rw [replayObserved_cons]
              simp only [State.applyObservedTotal, hsigned]
              refine fun digest hdigest => ih (state.install signedLeafIndex
                (truncateHash output)) htail ?_
              simpa [State.install, Ne.symm hsignedNe] using hdigest

theorem replayObserved_hit_of_query_before_sign
    (state : State) (leafIndex : LeafIndex) (queriedOutput signedOutput : HashOutput)
    (middle after : List ObservedAction)
    (hsigned : state.signed leafIndex = none)
    (hnoMiddleSign : leafIndex ∉ observedSignLeafIndices middle)
    (hcollision : truncateHash queriedOutput = truncateHash signedOutput) :
    (replayObserved state
      (.query leafIndex queriedOutput :: middle ++ .sign leafIndex signedOutput :: after)).hit =
        true := by
  simp only [List.cons_append]
  rw [congrArg ReplayResult.hit (replayObserved_cons state
    (.query leafIndex queriedOutput) (middle ++ .sign leafIndex signedOutput :: after))]
  simp only [State.applyObservedTotal, hsigned, Bool.false_or]
  rw [replayObserved_append]
  let middleResult := replayObserved
    (state.addPending leafIndex (truncateHash queriedOutput)) middle
  have hmiddleSigned : middleResult.state.signed leafIndex = none := by
    calc
      middleResult.state.signed leafIndex =
          (state.addPending leafIndex (truncateHash queriedOutput)).signed leafIndex :=
        replayObserved_state_signed_eq_of_not_mem _ middle leafIndex hnoMiddleSign
      _ = none := hsigned
  have hinitialPending : truncateHash queriedOutput ∈
      (state.addPending leafIndex (truncateHash queriedOutput)).pending leafIndex := by
    simp [State.addPending]
  have hmiddlePending : truncateHash signedOutput ∈ middleResult.state.pending leafIndex := by
    rw [← hcollision]
    exact replayObserved_pending_mono_of_not_mem _ middle leafIndex hnoMiddleSign
      hinitialPending
  change (middleResult.hit ||
    (replayObserved middleResult.state (.sign leafIndex signedOutput :: after)).hit) = true
  rw [congrArg ReplayResult.hit (replayObserved_cons middleResult.state
    (.sign leafIndex signedOutput) after)]
  simp [State.applyObservedTotal, hmiddleSigned, hmiddlePending]

theorem replayObserved_hit_of_sign_before_query
    (state : State) (leafIndex : LeafIndex) (signedOutput queriedOutput : HashOutput)
    (middle after : List ObservedAction)
    (hsigned : state.signed leafIndex = none)
    (hnoMiddleSign : leafIndex ∉ observedSignLeafIndices middle)
    (hcollision : truncateHash signedOutput = truncateHash queriedOutput) :
    (replayObserved state
      (.sign leafIndex signedOutput :: middle ++ .query leafIndex queriedOutput :: after)).hit =
        true := by
  simp only [List.cons_append]
  rw [congrArg ReplayResult.hit (replayObserved_cons state
    (.sign leafIndex signedOutput) (middle ++ .query leafIndex queriedOutput :: after))]
  simp only [State.applyObservedTotal, hsigned]
  rw [replayObserved_append]
  let middleResult := replayObserved
    (state.install leafIndex (truncateHash signedOutput)) middle
  have hmiddleSigned : middleResult.state.signed leafIndex =
      some (truncateHash signedOutput) := by
    calc
      middleResult.state.signed leafIndex =
          (state.install leafIndex (truncateHash signedOutput)).signed leafIndex :=
        replayObserved_state_signed_eq_of_not_mem _ middle leafIndex hnoMiddleSign
      _ = some (truncateHash signedOutput) := by simp [State.install]
  change (decide (truncateHash signedOutput ∈ state.pending leafIndex) ||
    (middleResult.hit ||
      (replayObserved middleResult.state (.query leafIndex queriedOutput :: after)).hit)) = true
  rw [congrArg ReplayResult.hit (replayObserved_cons middleResult.state
    (.query leafIndex queriedOutput) after)]
  simp [State.applyObservedTotal, hmiddleSigned, hcollision]

theorem runObserved_empty_eq_true_of_query_before_sign
    (leafIndex : LeafIndex) (queriedOutput signedOutput : HashOutput)
    (before middle after : List ObservedAction)
    (hnoBeforeSign : leafIndex ∉ observedSignLeafIndices before)
    (hnoMiddleSign : leafIndex ∉ observedSignLeafIndices middle)
    (hcollision : truncateHash queriedOutput = truncateHash signedOutput)
    (hvalid : (observedSignLeafIndices
      (before ++ [.query leafIndex queriedOutput] ++ middle ++
        [.sign leafIndex signedOutput] ++ after)).Nodup) :
    runObserved State.empty
      (before ++ [.query leafIndex queriedOutput] ++ middle ++
        [.sign leafIndex signedOutput] ++ after) = true := by
  let tail := .query leafIndex queriedOutput :: middle ++ .sign leafIndex signedOutput :: after
  have hlist : before ++ [.query leafIndex queriedOutput] ++ middle ++
      [.sign leafIndex signedOutput] ++ after = before ++ tail := by
    simp [tail, List.append_assoc]
  rw [hlist]
  have hreplayValid : (replayObserved State.empty (before ++ tail)).valid = true :=
    replayObserved_empty_valid_iff (before ++ tail) |>.2 (by simpa [← hlist] using hvalid)
  rw [runObserved_eq_replayObserved_hit_of_valid _ _ hreplayValid]
  rw [replayObserved_append]
  let beforeResult := replayObserved State.empty before
  have hbeforeSigned : beforeResult.state.signed leafIndex = none := by
    calc
      beforeResult.state.signed leafIndex = State.empty.signed leafIndex :=
        replayObserved_state_signed_eq_of_not_mem State.empty before leafIndex hnoBeforeSign
      _ = none := rfl
  have htailHit : (replayObserved beforeResult.state tail).hit = true := by
    exact replayObserved_hit_of_query_before_sign beforeResult.state leafIndex queriedOutput
      signedOutput middle after hbeforeSigned hnoMiddleSign hcollision
  change (beforeResult.hit || (replayObserved beforeResult.state tail).hit) = true
  simp [htailHit]

theorem runObserved_empty_eq_true_of_sign_before_query
    (leafIndex : LeafIndex) (signedOutput queriedOutput : HashOutput)
    (before middle after : List ObservedAction)
    (hnoBeforeSign : leafIndex ∉ observedSignLeafIndices before)
    (hnoMiddleSign : leafIndex ∉ observedSignLeafIndices middle)
    (hcollision : truncateHash signedOutput = truncateHash queriedOutput)
    (hvalid : (observedSignLeafIndices
      (before ++ [.sign leafIndex signedOutput] ++ middle ++
        [.query leafIndex queriedOutput] ++ after)).Nodup) :
    runObserved State.empty
      (before ++ [.sign leafIndex signedOutput] ++ middle ++
        [.query leafIndex queriedOutput] ++ after) = true := by
  let tail := .sign leafIndex signedOutput :: middle ++ .query leafIndex queriedOutput :: after
  have hlist : before ++ [.sign leafIndex signedOutput] ++ middle ++
      [.query leafIndex queriedOutput] ++ after = before ++ tail := by
    simp [tail, List.append_assoc]
  rw [hlist]
  have hreplayValid : (replayObserved State.empty (before ++ tail)).valid = true :=
    replayObserved_empty_valid_iff (before ++ tail) |>.2 (by simpa [← hlist] using hvalid)
  rw [runObserved_eq_replayObserved_hit_of_valid _ _ hreplayValid]
  rw [replayObserved_append]
  let beforeResult := replayObserved State.empty before
  have hbeforeSigned : beforeResult.state.signed leafIndex = none := by
    calc
      beforeResult.state.signed leafIndex = State.empty.signed leafIndex :=
        replayObserved_state_signed_eq_of_not_mem State.empty before leafIndex hnoBeforeSign
      _ = none := rfl
  have htailHit : (replayObserved beforeResult.state tail).hit = true := by
    exact replayObserved_hit_of_sign_before_query beforeResult.state leafIndex signedOutput
      queriedOutput middle after hbeforeSigned hnoMiddleSign hcollision
  change (beforeResult.hit || (replayObserved beforeResult.state tail).hit) = true
  simp [htailHit]

theorem observedSignLeafIndices_not_mem_around_sign
    (leafIndex : LeafIndex) (output : HashOutput)
    (before after : List ObservedAction)
    (hvalid : (observedSignLeafIndices
      (before ++ [.sign leafIndex output] ++ after)).Nodup) :
    leafIndex ∉ observedSignLeafIndices before ∧ leafIndex ∉ observedSignLeafIndices after := by
  have hnormalized :
      (observedSignLeafIndices before ++ leafIndex :: observedSignLeafIndices after).Nodup := by
    simpa [observedSignLeafIndices, List.append_assoc] using hvalid
  have hparts := List.nodup_append.mp hnormalized
  constructor
  · intro hmem
    exact hparts.2.2 leafIndex hmem leafIndex (by simp) rfl
  · exact (List.nodup_cons.mp hparts.2.1).1

theorem runObserved_empty_eq_true_of_query_before_sign_of_nodup
    (leafIndex : LeafIndex) (queriedOutput signedOutput : HashOutput)
    (before middle after : List ObservedAction)
    (hcollision : truncateHash queriedOutput = truncateHash signedOutput)
    (hvalid : (observedSignLeafIndices
      (before ++ [.query leafIndex queriedOutput] ++ middle ++
        [.sign leafIndex signedOutput] ++ after)).Nodup) :
    runObserved State.empty
      (before ++ [.query leafIndex queriedOutput] ++ middle ++
        [.sign leafIndex signedOutput] ++ after) = true := by
  have haround := observedSignLeafIndices_not_mem_around_sign leafIndex signedOutput
    (before ++ [.query leafIndex queriedOutput] ++ middle) after (by
      simpa [List.append_assoc] using hvalid)
  have hnoPrefix : leafIndex ∉ observedSignLeafIndices before := by
    intro hmem
    apply haround.1
    simp [hmem]
  have hnoMiddle : leafIndex ∉ observedSignLeafIndices middle := by
    intro hmem
    apply haround.1
    have : leafIndex ∈ observedSignLeafIndices before ++ observedSignLeafIndices middle :=
      List.mem_append_right _ hmem
    simpa [observedSignLeafIndices, List.append_assoc] using this
  exact runObserved_empty_eq_true_of_query_before_sign leafIndex queriedOutput
    signedOutput before middle after hnoPrefix hnoMiddle hcollision hvalid

theorem runObserved_empty_eq_true_of_sign_before_query_of_nodup
    (leafIndex : LeafIndex) (signedOutput queriedOutput : HashOutput)
    (before middle after : List ObservedAction)
    (hcollision : truncateHash signedOutput = truncateHash queriedOutput)
    (hvalid : (observedSignLeafIndices
      (before ++ [.sign leafIndex signedOutput] ++ middle ++
        [.query leafIndex queriedOutput] ++ after)).Nodup) :
    runObserved State.empty
      (before ++ [.sign leafIndex signedOutput] ++ middle ++
        [.query leafIndex queriedOutput] ++ after) = true := by
  have haround := observedSignLeafIndices_not_mem_around_sign leafIndex signedOutput before
    (middle ++ [.query leafIndex queriedOutput] ++ after) (by
      simpa [List.append_assoc] using hvalid)
  have hnoMiddle : leafIndex ∉ observedSignLeafIndices middle := by
    intro hmem
    apply haround.2
    have : leafIndex ∈ observedSignLeafIndices middle ++ observedSignLeafIndices after :=
      List.mem_append_left _ hmem
    simpa [observedSignLeafIndices, List.append_assoc] using this
  exact runObserved_empty_eq_true_of_sign_before_query leafIndex signedOutput
    queriedOutput before middle after haround.1 hnoMiddle hcollision hvalid

theorem pair_sublist_iff (first second : α) (actions : List α) :
    List.Sublist [first, second] actions ↔
      ∃ before middle after,
        actions = before ++ (first :: (middle ++ (second :: after))) := by
  constructor
  · intro hsub
    induction actions with
    | nil => simp at hsub
    | cons action actions ih =>
        cases hsub with
        | cons _ htail =>
            obtain ⟨before, middle, after, hactions⟩ := ih htail
            exact ⟨action :: before, middle, after, by simp [hactions]⟩
        | cons_cons _ htail =>
            have hsecond : second ∈ actions := by
              exact List.singleton_sublist.mp htail
            obtain ⟨middle, after, hactions⟩ := List.append_of_mem hsecond
            exact ⟨[], middle, after, by simp [hactions]⟩
  · rintro ⟨before, middle, after, rfl⟩
    have hsecond : List.Sublist [second] (middle ++ second :: after) :=
      List.singleton_sublist.mpr (List.mem_append_right middle (by simp))
    have hprefix : List.Sublist (first :: (middle ++ (second :: after)))
        (before ++ (first :: (middle ++ (second :: after)))) :=
      List.sublist_append_right before _
    exact (hsecond.cons_cons first).trans hprefix

theorem observedSignLeafIndices_sublist {left right : List ObservedAction}
    (hsub : List.Sublist left right) :
    List.Sublist (observedSignLeafIndices left) (observedSignLeafIndices right) := by
  induction hsub with
  | slnil => exact .slnil
  | cons action hsub ih =>
      cases action with
      | query leafIndex output => exact ih
      | sign leafIndex output => exact ih.cons leafIndex
  | cons_cons action hsub ih =>
      cases action with
      | query leafIndex output => exact ih
      | sign leafIndex output => exact ih.cons_cons leafIndex

def HasCollisionPair (actions : List ObservedAction) : Prop :=
  ∃ leafIndex queriedOutput signedOutput,
    truncateHash queriedOutput = truncateHash signedOutput ∧
      (List.Sublist [.query leafIndex queriedOutput, .sign leafIndex signedOutput] actions ∨
        List.Sublist [.sign leafIndex signedOutput, .query leafIndex queriedOutput] actions)

theorem HasCollisionPair.mono {left right : List ObservedAction}
    (hcollision : HasCollisionPair left) (hsub : List.Sublist left right) :
    HasCollisionPair right := by
  obtain ⟨leafIndex, queriedOutput, signedOutput, hdigest, hpair⟩ := hcollision
  exact ⟨leafIndex, queriedOutput, signedOutput, hdigest,
    hpair.imp (·.trans hsub) (·.trans hsub)⟩

def StateRepresentedBy (state : State) (actions : List ObservedAction) : Prop :=
  (∀ leafIndex digest, state.signed leafIndex = some digest →
      ∃ output, .sign leafIndex output ∈ actions ∧ truncateHash output = digest) ∧
    (∀ leafIndex digest, digest ∈ state.pending leafIndex →
      ∃ output, .query leafIndex output ∈ actions ∧ truncateHash output = digest)

theorem StateRepresentedBy.empty : StateRepresentedBy State.empty [] := by
  constructor
  · intro leafIndex digest hsigned
    simp [State.empty] at hsigned
  · intro leafIndex digest hpending
    simp [State.empty] at hpending

theorem StateRepresentedBy.applyObservedTotal
    {state : State} {actions : List ObservedAction}
    (hrepresented : StateRepresentedBy state actions)
    (action : ObservedAction) :
    StateRepresentedBy (state.applyObservedTotal action).state
      (actions ++ [action]) := by
  rcases hrepresented with ⟨hsignedRep, hpendingRep⟩
  cases action with
  | query leafIndex output =>
      cases hsigned : state.signed leafIndex with
      | some target =>
          simp only [State.applyObservedTotal, hsigned]
          constructor
          · intro candidate digest hcandid
            obtain ⟨oldOutput, hold, hdigest⟩ :=
              hsignedRep candidate digest hcandid
            exact ⟨oldOutput, List.mem_append_left _ hold, hdigest⟩
          · intro candidate digest hcandid
            obtain ⟨oldOutput, hold, hdigest⟩ :=
              hpendingRep candidate digest hcandid
            exact ⟨oldOutput, List.mem_append_left _ hold, hdigest⟩
      | none =>
          simp only [State.applyObservedTotal, hsigned]
          constructor
          · intro candidate digest hcandid
            obtain ⟨oldOutput, hold, hdigest⟩ :=
              hsignedRep candidate digest hcandid
            exact ⟨oldOutput, List.mem_append_left _ hold, hdigest⟩
          · intro candidate digest hcandid
            by_cases heq : candidate = leafIndex
            · subst candidate
              simp only [State.addPending, Function.update_self,
                Finset.mem_insert] at hcandid
              rcases hcandid with hcandid | hcandid
              · subst digest
                exact ⟨output, by simp, rfl⟩
              · obtain ⟨oldOutput, hold, hdigest⟩ :=
                  hpendingRep leafIndex digest hcandid
                exact ⟨oldOutput, List.mem_append_left _ hold, hdigest⟩
            · have hold : digest ∈ state.pending candidate := by
                simpa [State.addPending, heq] using hcandid
              obtain ⟨oldOutput, hmem, hdigest⟩ :=
                hpendingRep candidate digest hold
              exact ⟨oldOutput, List.mem_append_left _ hmem, hdigest⟩
  | sign leafIndex output =>
      cases hsigned : state.signed leafIndex with
      | some target =>
          simp only [State.applyObservedTotal, hsigned]
          constructor
          · intro candidate digest hcandid
            obtain ⟨oldOutput, hold, hdigest⟩ :=
              hsignedRep candidate digest hcandid
            exact ⟨oldOutput, List.mem_append_left _ hold, hdigest⟩
          · intro candidate digest hcandid
            obtain ⟨oldOutput, hold, hdigest⟩ :=
              hpendingRep candidate digest hcandid
            exact ⟨oldOutput, List.mem_append_left _ hold, hdigest⟩
      | none =>
          simp only [State.applyObservedTotal, hsigned]
          constructor
          · intro candidate digest hcandid
            by_cases heq : candidate = leafIndex
            · subst candidate
              simp only [State.install, Function.update_self,
                Option.some.injEq] at hcandid
              subst digest
              exact ⟨output, by simp, rfl⟩
            · have hold : state.signed candidate = some digest := by
                simpa [State.install, heq] using hcandid
              obtain ⟨oldOutput, hmem, hdigest⟩ :=
                hsignedRep candidate digest hold
              exact ⟨oldOutput, List.mem_append_left _ hmem, hdigest⟩
          · intro candidate digest hcandid
            by_cases heq : candidate = leafIndex
            · subst candidate
              simp [State.install] at hcandid
            · have hold : digest ∈ state.pending candidate := by
                simpa [State.install, heq] using hcandid
              obtain ⟨oldOutput, hmem, hdigest⟩ :=
                hpendingRep candidate digest hold
              exact ⟨oldOutput, List.mem_append_left _ hmem, hdigest⟩

theorem replayObserved_hit_eq_true_hasCollisionPair
    (state : State) (actionsBefore tail : List ObservedAction)
    (hrepresented : StateRepresentedBy state actionsBefore)
    (hhit : (replayObserved state tail).hit = true) :
    HasCollisionPair (actionsBefore ++ tail) := by
  induction tail generalizing state actionsBefore with
  | nil => simp [replayObserved] at hhit
  | cons action tail ih =>
      rw [replayObserved_cons] at hhit
      let head := state.applyObservedTotal action
      let rest := replayObserved head.state tail
      change (head.hit || rest.hit) = true at hhit
      rw [Bool.or_eq_true] at hhit
      rcases hhit with hhead | htail
      · cases action with
        | query leafIndex output =>
            cases hsigned : state.signed leafIndex with
            | none => simp [head, State.applyObservedTotal, hsigned] at hhead
            | some target =>
                have hquery : truncateHash output = target := by
                  simpa [head, State.applyObservedTotal, hsigned] using hhead
                obtain ⟨signedOutput, hsignedMem, hsignedDigest⟩ :=
                  hrepresented.1 leafIndex target hsigned
                have hpair : List.Sublist
                    [.sign leafIndex signedOutput, .query leafIndex output]
                    (actionsBefore ++ .query leafIndex output :: tail) := by
                  have hbase := (List.singleton_sublist.mpr hsignedMem).append
                    (List.Sublist.refl [.query leafIndex output])
                  exact hbase.trans (by simp)
                exact ⟨leafIndex, output, signedOutput,
                  hquery.trans hsignedDigest.symm, Or.inr hpair⟩
        | sign leafIndex output =>
            cases hsigned : state.signed leafIndex with
            | some target => simp [head, State.applyObservedTotal, hsigned] at hhead
            | none =>
                have hpending : truncateHash output ∈ state.pending leafIndex := by
                  simpa [head, State.applyObservedTotal, hsigned] using hhead
                obtain ⟨queriedOutput, hqueryMem, hqueryDigest⟩ :=
                  hrepresented.2 leafIndex (truncateHash output) hpending
                have hpair : List.Sublist
                    [.query leafIndex queriedOutput, .sign leafIndex output]
                    (actionsBefore ++ .sign leafIndex output :: tail) := by
                  have hbase := (List.singleton_sublist.mpr hqueryMem).append
                    (List.Sublist.refl [.sign leafIndex output])
                  exact hbase.trans (by simp)
                exact ⟨leafIndex, queriedOutput, output, hqueryDigest,
                  Or.inl hpair⟩
      · have htailPair := ih head.state (actionsBefore ++ [action])
          (hrepresented.applyObservedTotal action) htail
        simpa [head, List.append_assoc] using htailPair

theorem runObserved_empty_eq_true_of_collisionPair
    (actions : List ObservedAction)
    (hnodup : (observedSignLeafIndices actions).Nodup)
    (hcollision : HasCollisionPair actions) :
    runObserved State.empty actions = true := by
  obtain ⟨leafIndex, queriedOutput, signedOutput, hdigest, hpair | hpair⟩ := hcollision
  · obtain ⟨before, middle, after, hactions⟩ :=
      (pair_sublist_iff _ _ _).mp hpair
    subst actions
    simpa [List.append_assoc] using
      runObserved_empty_eq_true_of_query_before_sign_of_nodup
        leafIndex queriedOutput signedOutput before middle after hdigest
          (by simpa [List.append_assoc] using hnodup)
  · obtain ⟨before, middle, after, hactions⟩ :=
      (pair_sublist_iff _ _ _).mp hpair
    subst actions
    simpa [List.append_assoc] using
      runObserved_empty_eq_true_of_sign_before_query_of_nodup
        leafIndex signedOutput queriedOutput before middle after hdigest.symm
          (by simpa [List.append_assoc] using hnodup)

theorem collisionPair_of_runObserved_empty_eq_true
    (actions : List ObservedAction)
    (hnodup : (observedSignLeafIndices actions).Nodup)
    (hhit : runObserved State.empty actions = true) :
    HasCollisionPair actions := by
  have hvalid : (replayObserved State.empty actions).valid = true :=
    (replayObserved_empty_valid_iff actions).mpr hnodup
  have hreplay := runObserved_eq_replayObserved_hit_of_valid
    State.empty actions hvalid
  rw [hreplay] at hhit
  simpa using replayObserved_hit_eq_true_hasCollisionPair
    State.empty [] actions StateRepresentedBy.empty hhit

theorem runObserved_empty_eq_true_mono_sublist
    {left right : List ObservedAction}
    (hsub : List.Sublist left right)
    (hnodup : (observedSignLeafIndices right).Nodup)
    (hhit : runObserved State.empty left = true) :
    runObserved State.empty right = true := by
  have hsignSub := observedSignLeafIndices_sublist hsub
  have hleftNodup := hsignSub.nodup hnodup
  exact runObserved_empty_eq_true_of_collisionPair right hnodup
    ((collisionPair_of_runObserved_empty_eq_true left hleftNodup hhit).mono hsub)

end XmssSecurity.EncodingMonitor
