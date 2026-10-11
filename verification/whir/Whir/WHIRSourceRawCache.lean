import Whir.WHIRSourceObserver
import Whir.RawOracleProvenance

namespace Whir.WHIRSourceRawCache
open FiatShamirGame DuplexModeGame RawOracleCoupling.Concrete
open WHIRSourceChronology WHIRSourceObserver

variable {cap : Nat}

private def lookup {Key : Type} [DecidableEq Key] : List (Key × Digest32) → Key → Option Digest32
  | [], _ => none
  | (key,answer) :: rest, wanted => if wanted = key then some answer else lookup rest wanted

def cache (Q : Nat) (state : CausalBindingState.State cap) : RawKey Q → Option Digest32 :=
  lookup (state.rawAnswers Q)

def LogAgrees (ro : RawKey Q → Digest32) (entries : List (RawKey Q × Digest32)) : Prop :=
  ∀ entry ∈ entries, entry.2 = ro entry.1

theorem lookup_agrees (Q : Nat) (ro : RawKey Q → Digest32)
    (entries : List (RawKey Q × Digest32)) (agrees : LogAgrees ro entries) :
    DuplexPublicSimulator.CacheAgrees (lookup entries) ro := by
  induction entries with
  | nil => intro key answer found; simp [lookup] at found
  | cons entry rest ih =>
      intro key answer found
      by_cases same : key = entry.1
      · simp only [lookup,ite_eq_left same,Option.some.injEq] at found
        exact found.symm.trans ((agrees entry (by simp)).trans (congrArg ro same.symm))
      · have hit : lookup rest key = some answer := by simpa [lookup,same] using found
        exact ih (fun e he => agrees e (List.mem_cons_of_mem _ he)) key answer hit

/-- A packet supplies exactly its finite output blocks; a garbage allocation supplies its single exact raw input. -/
def groupEntries (ctx : RawWHIRKeys.Context) (Q : Nat) :
    (key : GroupKey ctx Q) → GroupAnswer ctx Q key → List (RawKey Q × Digest32)
  | .inl packet, answer => List.ofFn (fun block => (RawWHIRKeys.encode ctx Q ⟨packet,block⟩,answer block))
  | .inr raw, answer => [(raw.val,answer)]

theorem groupEntries_table (ctx : RawWHIRKeys.Context) (Q : Nat)
    (ro : RawKey Q → Digest32) (key : GroupKey ctx Q) :
    LogAgrees ro (groupEntries ctx Q key ((partition ctx Q).split ro key)) := by
  cases key with
  | inl packet =>
      intro entry member
      obtain ⟨block,rfl⟩ := List.mem_ofFn.mp member
      rfl
  | inr raw =>
      intro entry member
      have equal : entry = (raw.val,ro raw.val) := by
        simpa [groupEntries,RawOracleCoupling.Partition.split] using member
      subst entry
      rfl

/-- Only newly supplied finite group cells are copied. On actual executions every stored answer agrees with the same raw table, including any repeated cell. -/
def addGroup (ctx : RawWHIRKeys.Context) (Q : Nat) (state : CausalBindingState.State cap)
    (key : GroupKey ctx Q) (answer : GroupAnswer ctx Q key) : CausalBindingState.State cap :=
  {state with rawAnswers := fun q =>
    if h : q = Q then
      h.symm ▸ (groupEntries ctx Q key answer ++ state.rawAnswers Q)
    else state.rawAnswers q}

@[simp] theorem addGroup_entries (ctx : RawWHIRKeys.Context) (Q : Nat)
    (state : CausalBindingState.State cap) (key : GroupKey ctx Q) (answer : GroupAnswer ctx Q key) :
    (addGroup ctx Q state key answer).rawAnswers Q = groupEntries ctx Q key answer ++ state.rawAnswers Q := by
  simp [addGroup]

theorem addGroup_extends (ctx : RawWHIRKeys.Context) (Q : Nat)
    (state : CausalBindingState.State cap) (key : GroupKey ctx Q) (answer : GroupAnswer ctx Q key) :
    CausalBindingState.Extends state (addGroup ctx Q state key answer) :=
  ⟨fun _ _ h => h,fun _ _ h => h,fun _ _ _ => rfl,fun _ _ _ h => h,fun _ _ _ => rfl⟩

theorem addGroup_agrees (ctx : RawWHIRKeys.Context) (Q : Nat)
    (ro : RawKey Q → Digest32) (state : CausalBindingState.State cap)
    (agrees : LogAgrees ro (state.rawAnswers Q)) (key : GroupKey ctx Q) :
    LogAgrees ro ((addGroup ctx Q state key ((partition ctx Q).split ro key)).rawAnswers Q) := by
  rw [addGroup_entries]
  intro entry member
  rcases List.mem_append.mp member with fresh | old
  · exact groupEntries_table ctx Q ro key entry fresh
  · exact agrees entry old

private theorem lookup_hit_iff (Q : Nat) (ro : RawKey Q → Digest32)
    (entries : List (RawKey Q × Digest32)) (agrees : LogAgrees ro entries)
    (key : RawKey Q) (answer : Digest32) :
    lookup entries key = some answer ↔ (key,answer) ∈ entries := by
  induction entries with
  | nil => simp [lookup]
  | cons entry rest ih =>
      have tail := fun e he => agrees e (List.mem_cons_of_mem _ he)
      by_cases same : key = entry.1
      · simp only [lookup,same,↓reduceIte,Option.some.injEq,List.mem_cons]
        constructor
        · intro equal
          exact Or.inl (Prod.ext rfl equal.symm)
        · intro member
          rcases member with equal | member
          · exact (congrArg Prod.snd equal).symm
          · exact (agrees entry (by simp)).trans
              (tail (entry.1,answer) member).symm
      · simp only [lookup,same,↓reduceIte,List.mem_cons,ih tail]
        constructor
        · exact Or.inr
        · intro member
          rcases member with equal | member
          · exact (same (congrArg Prod.fst equal)).elim
          · exact member

theorem cache_hit_iff (Q : Nat) (ro : RawKey Q → Digest32)
    (state : CausalBindingState.State cap) (agrees : LogAgrees ro (state.rawAnswers Q))
    (key : RawKey Q) (answer : Digest32) :
    cache Q state key = some answer ↔ (key,answer) ∈ state.rawAnswers Q :=
  lookup_hit_iff Q ro (state.rawAnswers Q) agrees key answer

theorem cache_addGroup_preserves (ctx : RawWHIRKeys.Context) (Q : Nat)
    (ro : RawKey Q → Digest32) (state : CausalBindingState.State cap)
    (agrees : LogAgrees ro (state.rawAnswers Q)) (group : GroupKey ctx Q)
    (key : RawKey Q) (answer : Digest32) (hit : cache Q state key = some answer) :
    cache Q (addGroup ctx Q state group ((partition ctx Q).split ro group)) key = some answer := by
  apply (cache_hit_iff Q ro _ (addGroup_agrees ctx Q ro state agrees group) key answer).mpr
  rw [addGroup_entries]
  exact List.mem_append_right _ ((cache_hit_iff Q ro state agrees key answer).mp hit)

theorem cache_addGroup_member (ctx : RawWHIRKeys.Context) (Q : Nat)
    (ro : RawKey Q → Digest32) (state : CausalBindingState.State cap)
    (agrees : LogAgrees ro (state.rawAnswers Q)) (group : GroupKey ctx Q)
    (key : RawKey Q) (answer : Digest32)
    (member : (key,answer) ∈ groupEntries ctx Q group ((partition ctx Q).split ro group)) :
    cache Q (addGroup ctx Q state group ((partition ctx Q).split ro group)) key = some answer := by
  apply (cache_hit_iff Q ro _ (addGroup_agrees ctx Q ro state agrees group) key answer).mpr
  rw [addGroup_entries]
  exact List.mem_append_left _ member

@[simp] theorem observe_raw (state : CausalBindingState.State cap) (bytes : List Byte) (answer : Digest32) :
    (CausalBindingState.observe state bytes answer).rawAnswers = state.rawAnswers := by
  unfold CausalBindingState.observe
  split <;> rfl

@[simp] theorem registerRoot_raw (state : CausalBindingState.State cap) (root : Digest32) :
    (CausalBindingState.registerRoot state root).rawAnswers = state.rawAnswers := by
  unfold CausalBindingState.registerRoot
  split <;> rfl

@[simp] theorem registerRoots_raw (state : CausalBindingState.State cap) (roots : List Digest32) :
    (CausalBindingState.registerRoots state roots).rawAnswers = state.rawAnswers := by
  induction roots generalizing state with
  | nil => rfl
  | cons root rest ih =>
      change (CausalBindingState.registerRoots (CausalBindingState.registerRoot state root) rest).rawAnswers = _
      rw [ih,registerRoot_raw]

@[simp] theorem registerStatement_raw (state : CausalBindingState.State cap) (p : ParameterBounds.Profile)
    (entry : FramedHistory) (data : Option (WHIRFiatShamir.StackInitial p cap)) :
    (CausalBindingState.registerStatement state p entry data).rawAnswers = state.rawAnswers := by
  unfold CausalBindingState.registerStatement
  split <;> rfl

@[simp] theorem prepareClaims_raw (state : CausalBindingState.State cap) (p : ParameterBounds.Profile)
    (entry : FramedHistory) (key : StackWHIRReplay.Key p)
    (request : Option (CausalBindingState.ClaimRequest cap p)) :
    (CausalBindingState.prepareClaims state p entry key request).1.rawAnswers = state.rawAnswers := by
  cases request <;> simp [CausalBindingState.prepareClaims,CausalBindingState.prepare,
    CausalBindingState.registerFootprint,CausalBindingState.commit]

@[simp] theorem observeRecords_raw (state : CausalBindingState.State cap)
    (records : MerkleTransport.Commitments.Records) :
    (observeRecords state records).rawAnswers = state.rawAnswers := by
  induction records generalizing state with
  | nil => rfl
  | cons record rest ih =>
      change (observeRecords (CausalBindingState.observe state record.1 record.2) rest).rawAnswers = _
      rw [ih,observe_raw]

@[simp] theorem observePublic_raw (state : CausalBindingState.State cap)
    (input : DuplexFraming.Node) (answer : Digest32) :
    (observePublic state input answer).rawAnswers = state.rawAnswers := by
  simp [observePublic]

theorem step_raw (state next : CausalBindingState.State cap) (event : Event cap)
    (success : step state event = .ok next) : next.rawAnswers = state.rawAnswers := by
  cases event with
  | answer query value =>
      cases query with
      | primitive purpose input => cases success; exact observePublic_raw _ _ _
      | construction coordinate valid => cases success; rfl
  | commit root => cases success; exact registerRoot_raw _ _
  | claims profile entry request =>
      unfold step at success
      cases found : MerkleTransport.Commitments.lookup request.root state.registry with
      | none => simp [found] at success
      | some snapshot =>
          simp only [found] at success
          cases success
          rfl

@[simp] theorem replayTracked_raw (state : CausalBindingState.State cap) (events : List (Event cap)) :
    (replayTracked state events).rawAnswers = state.rawAnswers := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      unfold replayTracked
      cases progress : step state event with
      | error root => exact ih _
      | ok next => exact (ih next).trans (step_raw state next event progress)

end Whir.WHIRSourceRawCache
