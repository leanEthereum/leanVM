import Whir.MerkleTransport
import Whir.WHIRSnapshotReplay
import Whir.DuplexModeGame
import Whir.WHIRPhysicalRows

/-! Causal ghost state for the PCS boundary. Root extraction closes over finite answers captured at first registration, never over a future primitive table. Bindings are identified by the complete actual caller entry, so cloned histories sharing a seed remain distinct. Actual caller claim binding remains the library's input contract. -/
namespace Whir.CausalBindingState
open Concrete Protocol ParameterBounds CausalGame
open FiatShamirGame (Digest32 Byte FramedHistory)
open MerkleTransport.Commitments
open Classical

structure State (cap : Nat) where
  records : Records := []
  registry : Registry := []
  frozen : Digest32 → Option Records := fun _ => none
  entries : (p : Profile) → FramedHistory → Option (Option (WHIRFiatShamir.StackInitial p cap)) := fun _ _ => none
  rawAnswers : (Q : Nat) → List (DuplexModeGame.RawKey Q × Digest32) := fun _ => []
  publicLog : List (DuplexFraming.Node × Digest32) := []
  frozenLog : Digest32 → Option (List (DuplexFraming.Node × Digest32)) := fun _ => none
  sourceError : Option Digest32 := none

/-- Flatten the first recorded caller result, retaining rejected entries separately. -/
def State.catalog {cap : Nat} (s : State cap) (p : Profile) (entry : FramedHistory) :
    Option (WHIRFiatShamir.StackInitial p cap) :=
  (s.entries p entry).getD none

def empty (cap : Nat) : State cap := {}

def localCatalog {cap : Nat} (s : State cap) (p : Profile) (entry : FramedHistory) :
    StackWHIRReplay.Catalog p cap :=
  fun seed => if seed = entry.statement then s.catalog p entry else none

def snapshot (records : Records) : Snapshot := ⟨recordDomain records,[]⟩

def observe {cap : Nat} (s : State cap) (input : List Byte) (value : Digest32) : State cap :=
  match recordLookup input s.records with
  | some _ => s
  | none => {s with records := (input,value) :: s.records}

def registerRoot {cap : Nat} (s : State cap) (root : Digest32) : State cap :=
  match lookup root s.registry with
  | some _ => s
  | none => {s with
      registry := register s.registry root (snapshot s.records)
      frozen := Function.update s.frozen root (some s.records)
      frozenLog := Function.update s.frozenLog root (some s.publicLog)}

def registerRoots {cap : Nat} (s : State cap) (roots : List Digest32) : State cap :=
  roots.foldl registerRoot s

def registerStatement {cap : Nat} (s : State cap) (p : Profile) (entry : FramedHistory)
    (data : Option (WHIRFiatShamir.StackInitial p cap)) : State cap :=
  match s.entries p entry with
  | some _ => s
  | none => {s with
      entries := Function.update s.entries p (Function.update (s.entries p) entry (some data))}

structure Extends {cap : Nat} (old new : State cap) : Prop where
  records : ∀ input value, recordLookup input old.records = some value →
    recordLookup input new.records = some value
  registry : ∀ root snap, lookup root old.registry = some snap →
    lookup root new.registry = some snap
  frozen : ∀ root snap, lookup root old.registry = some snap → old.frozen root = new.frozen root
  entries : ∀ p entry data, old.entries p entry = some data → new.entries p entry = some data
  frozenLog : ∀ root snap, lookup root old.registry = some snap → old.frozenLog root = new.frozenLog root

theorem Extends.catalog {cap : Nat} {old new : State cap} (growth : Extends old new)
    (p : Profile) (entry : FramedHistory) (data : WHIRFiatShamir.StackInitial p cap)
    (known : old.catalog p entry = some data) : new.catalog p entry = some data := by
  cases h : old.entries p entry with
  | none => simp [State.catalog, h] at known
  | some result =>
    simpa only [State.catalog, h, growth.entries p entry result h, Option.getD_some] using known

/-- A first rejection cannot become an accepted catalog entry after any extension. -/
theorem Extends.rejected {cap : Nat} {old new : State cap} (growth : Extends old new)
    (p : Profile) (entry : FramedHistory) (known : old.entries p entry = some none) :
    new.entries p entry = some none ∧ new.catalog p entry = none :=
  ⟨growth.entries p entry none known, by
    simp [State.catalog, growth.entries p entry none known]⟩

theorem Extends.refl {cap : Nat} (s : State cap) : Extends s s :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ _ => rfl, fun _ _ _ h => h, fun _ _ _ => rfl⟩

theorem Extends.trans {cap : Nat} {a b c : State cap} (ab : Extends a b) (bc : Extends b c) :
    Extends a c :=
  ⟨fun x y h => bc.records x y (ab.records x y h),
   fun r snap h => bc.registry r snap (ab.registry r snap h),
   fun r snap h => (ab.frozen r snap h).trans (bc.frozen r snap (ab.registry r snap h)),
   fun p entry data h => bc.entries p entry data (ab.entries p entry data h),
   fun r snap h => (ab.frozenLog r snap h).trans (bc.frozenLog r snap (ab.registry r snap h))⟩

theorem observe_extends {cap : Nat} (s : State cap) (input : List Byte) (value : Digest32) :
    Extends s (observe s input value) := by
  unfold observe
  cases found : recordLookup input s.records with
  | some _ => exact .refl s
  | none =>
    refine ⟨?_,fun _ _ h => h,fun _ _ _ => rfl,fun _ _ _ h => h,fun _ _ _ => rfl⟩
    intro x d old
    have ne : x ≠ input := by intro eq; subst x; simp [found] at old
    simp [recordLookup,ne,old]

theorem registerRoot_extends {cap : Nat} (s : State cap) (root : Digest32) :
    Extends s (registerRoot s root) := by
  unfold registerRoot
  cases found : lookup root s.registry with
  | some _ => exact .refl s
  | none =>
    refine ⟨fun _ _ h => h,?_,?_,fun _ _ _ h => h,?_⟩
    · intro r snap old
      exact register_preserves s.registry r root snap (snapshot s.records) old
    · intro r snap old
      have ne : r ≠ root := by intro eq; subst r; simp [found] at old
      simp [Function.update_of_ne ne]
    · intro r snap old
      have ne : r ≠ root := by intro eq; subst r; simp [found] at old
      simp [Function.update_of_ne ne]

theorem registerRoot_known {cap : Nat} (s : State cap) (root : Digest32) :
    ∃ snap, lookup root (registerRoot s root).registry = some snap := by
  unfold registerRoot
  cases found : lookup root s.registry with
  | some snap => exact ⟨snap,found⟩
  | none => exact ⟨snapshot s.records,register_first _ _ _ found⟩

theorem registerRoots_extends {cap : Nat} (s : State cap) (roots : List Digest32) :
    Extends s (registerRoots s roots) := by
  induction roots generalizing s with
  | nil => exact .refl s
  | cons root rest ih =>
    exact (registerRoot_extends s root).trans (ih (registerRoot s root))

theorem registerRoots_known {cap : Nat} (s : State cap) (roots : List Digest32)
    (root : Digest32) (member : root ∈ roots) :
    ∃ snap, lookup root (registerRoots s roots).registry = some snap := by
  induction roots generalizing s with
  | nil => simp at member
  | cons r rest ih =>
    rcases List.mem_cons.mp member with eq | member
    · subst r
      obtain ⟨snap,known⟩ := registerRoot_known s root
      exact ⟨snap,(registerRoots_extends (registerRoot s root) rest).registry _ _ known⟩
    · exact ih (registerRoot s r) member

theorem registerStatement_extends {cap : Nat} (s : State cap) (p : Profile)
    (entry : FramedHistory) (data : Option (WHIRFiatShamir.StackInitial p cap)) :
    Extends s (registerStatement s p entry data) := by
  unfold registerStatement
  cases found : s.entries p entry with
  | some _ => exact .refl s
  | none =>
    refine ⟨fun _ _ h => h,fun _ _ h => h,fun _ _ _ => rfl,?_,fun _ _ _ => rfl⟩
    intro q other old known
    by_cases hp : q = p
    · subst q
      by_cases hs : other = entry
      · subst other; simp [found] at known
      · simpa [Function.update_of_ne hs] using known
    · simpa [Function.update_of_ne hp] using known

def selected {cap : Nat} (s : State cap) (p : Profile) (entry : FramedHistory)
    (data : Option (WHIRFiatShamir.StackInitial p cap)) : Option (WHIRFiatShamir.StackInitial p cap) :=
  (s.entries p entry).getD data

theorem registerStatement_found {cap : Nat} (s : State cap) (p : Profile)
    (entry : FramedHistory) (data : Option (WHIRFiatShamir.StackInitial p cap)) :
    (registerStatement s p entry data).entries p entry = some (selected s p entry data) := by
  unfold registerStatement selected
  cases found : s.entries p entry <;> simp [found]

structure Commitment (p : Profile) where
  digest : Digest32
  lanes : Nat
  lane_bound : lanes ≤ 2 ^ (config p).folds[0]!
  snapshot : Snapshot
  records : Records

def capture {cap : Nat} (s : State cap) (p : Profile) (root : Digest32) (lanes : Nat)
    (bound : lanes ≤ 2 ^ (config p).folds[0]!) : Commitment p :=
  ⟨root,lanes,bound,(lookup root s.registry).getD (snapshot []),(s.frozen root).getD []⟩

/-- Call at the actual commitment announcement, before choosing opening claims. Prequeried roots retain the earlier snapshot instead of being reassigned. -/
def commit {cap : Nat} (s : State cap) (p : Profile) (root : Digest32) (lanes : Nat)
    (bound : lanes ≤ 2 ^ (config p).folds[0]!) : State cap × Commitment p :=
  let next := registerRoot s root
  (next,capture next p root lanes bound)

noncomputable def Commitment.base {p : Profile} (c : Commitment p) : CausalGame.BaseOracle :=
  WHIRPhysicalRows.compactBaseOracle (recordedHash c.records (fun _ => 0)) c.snapshot c.digest
    (remaining (config p) 0 + (config p).rates[0]!) (ParameterBounds.length (config p) 0)
    (2 ^ (config p).folds[0]!) c.lanes

structure OriginalClaims (cap : Nat) where
  count : Nat
  family : Fin count → RingPCSGame.FamilyClaim
  family_bound : count ≤ cap
  points : Array RingPCSGame.PointClaim
  claim_bound : points.size + 1 ≤ 2^64

noncomputable def bindClaims {cap : Nat} {p : Profile} (c : Commitment p)
    (claims : OriginalClaims cap) : WHIRFiatShamir.StackInitial p cap where
  lanes := c.lanes
  root := c.base
  lane_bound := c.lane_bound
  familyCount := claims.count
  family := claims.family
  family_bound := claims.family_bound
  points := claims.points
  claim_bound := claims.claim_bound

/-- The witness list is chosen from the captured commitment, before the original family or point claims are supplied. -/
noncomputable def Commitment.witnesses {p : Profile} (c : Commitment p) :=
  InitialCandidates.witnesses (config p) c.lanes c.base

theorem Commitment.witnesses_bound {p : Profile} (c : Commitment p) : c.witnesses.card ≤ 2^32 :=
  InitialCandidates.production_witnesses_card p c.lanes c.base

theorem bindClaims_witnesses {cap : Nat} {p : Profile} (c : Commitment p)
    (claims : OriginalClaims cap) :
    InitialCandidates.witnesses (config p) (bindClaims c claims).lanes (bindClaims c claims).root =
      c.witnesses := rfl

theorem capture_stable {cap : Nat} {old new : State cap} (growth : Extends old new)
    (p : Profile) (root : Digest32) (lanes : Nat) (bound : lanes ≤ 2 ^ (config p).folds[0]!)
    (snap : Snapshot) (known : lookup root old.registry = some snap) :
    capture old p root lanes bound = capture new p root lanes bound := by
  simp only [capture,known,growth.registry root snap known,growth.frozen root snap known]

noncomputable def roots {cap : Nat} (s : State cap) (p : Profile) : WHIRReplay.Roots :=
  fun root level => intermediateOracle
    (recordedHash ((s.frozen root).getD []) (fun _ => 0))
    ((lookup root s.registry).getD (snapshot [])) root
    (remaining (config p) level + (config p).rates[level]!)
    (ParameterBounds.length (config p) level) (2 ^ (config p).folds[level]!)

theorem roots_stable {cap : Nat} {old new : State cap} (growth : Extends old new)
    (p : Profile) (root : Digest32) (level : Nat) (snap : Snapshot)
    (known : lookup root old.registry = some snap) : roots old p root level = roots new p root level := by
  simp only [roots,known,growth.registry root snap known,growth.frozen root snap known]

def Prepared {cap : Nat} (s : State cap) (p : Profile) (key : StackWHIRReplay.Key p) : Prop :=
  ∀ ref ∈ WHIRSnapshotReplay.historyFootprint p key.statement key.messages,
    ∃ snap, lookup ref.1 s.registry = some snap

def registerFootprint {cap : Nat} (s : State cap) (p : Profile) (key : StackWHIRReplay.Key p) : State cap :=
  registerRoots s ((WHIRSnapshotReplay.historyFootprint p key.statement key.messages).map Prod.fst)

theorem registerFootprint_extends {cap : Nat} (s : State cap) (p : Profile) (key : StackWHIRReplay.Key p) :
    Extends s (registerFootprint s p key) := registerRoots_extends _ _

theorem registerFootprint_prepared {cap : Nat} (s : State cap) (p : Profile) (key : StackWHIRReplay.Key p) :
    Prepared (registerFootprint s p key) p key := by
  intro ref member
  exact registerRoots_known _ _ ref.1 (List.mem_map.mpr ⟨ref,member,rfl⟩)

structure Label (cap : Nat) (p : Profile) where
  state : State cap
  entry : FramedHistory
  key : StackWHIRReplay.Key p
  original : Option (WHIRFiatShamir.StackInitial p cap)
  found : state.entries p entry = some original
  prepared : Prepared state p key

/-- `proposed` is computed by the source-resolvable caller binding before the fresh packet is sampled. Existing registration wins, including a prequery's earlier registration. -/
def prepare {cap : Nat} (s : State cap) (p : Profile) (entry : FramedHistory)
    (key : StackWHIRReplay.Key p) (proposed : Option (WHIRFiatShamir.StackInitial p cap)) : State cap × Label cap p :=
  let registered := registerStatement s p entry proposed
  let next := registerFootprint registered p key
  (next,⟨next,entry,key,selected s p entry proposed,
    (registerFootprint_extends registered p key).entries p entry _
      (registerStatement_found s p entry proposed),
    registerFootprint_prepared registered p key⟩)

theorem prepare_extends {cap : Nat} (s : State cap) (p : Profile) (entry : FramedHistory)
    (key : StackWHIRReplay.Key p) (proposed : Option (WHIRFiatShamir.StackInitial p cap)) :
    Extends s (prepare s p entry key proposed).1 :=
  (registerStatement_extends s p entry proposed).trans (registerFootprint_extends _ p key)

noncomputable def Label.bad {cap : Nat} {p : Profile} (label : Label cap p)
    (x : StackWHIRReplay.Answer p label.key) : Prop :=
  StackWHIRROM.keyBad p cap (localCatalog label.state p label.entry) (roots label.state p) label.key x

theorem Label.sparse {cap : Nat} {p : Profile} (label : Label cap p) :
    FiatShamirGame.average (fun x => if label.bad x then 1 else 0) ≤ WHIRFiatShamir.stackEta p cap := by
  classical
  exact StackWHIRROM.key_sparse p cap (localCatalog label.state p label.entry) (roots label.state p) label.key

theorem Label.final_agreement {cap : Nat} {p : Profile} (label : Label cap p) (final : State cap)
    (growth : Extends label.state final) :
    localCatalog label.state p label.entry label.key.statement = localCatalog final p label.entry label.key.statement ∧
    WHIRSnapshotReplay.AgreeOn
      (WHIRSnapshotReplay.historyFootprint p label.key.statement label.key.messages)
      (roots label.state p) (roots final p) := by
  constructor
  · have stored := label.found.trans (growth.entries p label.entry label.original label.found).symm
    simp only [localCatalog, State.catalog, stored]
  · intro ref member
    obtain ⟨snap,known⟩ := label.prepared ref member
    exact roots_stable growth p ref.1 ref.2 snap known

theorem Label.bad_final {cap : Nat} {p : Profile} (label : Label cap p) (final : State cap)
    (growth : Extends label.state final) (x : StackWHIRReplay.Answer p label.key) :
    label.bad x ↔ StackWHIRROM.keyBad p cap (localCatalog final p label.entry) (roots final p) label.key x := by
  obtain ⟨catalog,agree⟩ := label.final_agreement final growth
  exact WHIRSnapshotReplay.stack_keyBad_congr p cap (localCatalog label.state p label.entry)
    (localCatalog final p label.entry) (roots label.state p) (roots final p) label.key x catalog agree

/-- Rejected entries contribute no bad event, even after an arbitrary future extension. -/
theorem Label.rejected_final {cap : Nat} {p : Profile} (label : Label cap p)
    (rejected : label.original = none) (final : State cap)
    (growth : Extends label.state final) (x : StackWHIRReplay.Answer p label.key) :
    final.entries p label.entry = some none ∧ final.catalog p label.entry = none ∧
      ¬ StackWHIRROM.keyBad p cap (localCatalog final p label.entry) (roots final p) label.key x := by
  have frozen := growth.rejected p label.entry (label.found.trans (congrArg some rejected))
  refine ⟨frozen.1, frozen.2, ?_⟩
  have absent : localCatalog final p label.entry label.key.statement = none := by
    simp [localCatalog, frozen.2]
  have initial : StackWHIRReplay.decodeInitial p cap (localCatalog final p label.entry) label.key = none := by
    unfold StackWHIRReplay.decodeInitial
    split <;> simp [absent]
  simp [StackWHIRROM.keyBad, initial, StackWHIRReplay.decode, absent]

theorem Label.rejected_bad {cap : Nat} {p : Profile} (label : Label cap p)
    (rejected : label.original = none) (x : StackWHIRReplay.Answer p label.key) :
    ¬ label.bad x :=
  (label.rejected_final rejected label.state (.refl _) x).2.2

structure ClaimRequest (cap : Nat) (p : Profile) where
  root : Digest32
  lanes : Nat
  lane_bound : lanes ≤ 2 ^ (config p).folds[0]!
  claims : OriginalClaims cap

/-- Resolve before sampling. A real request's root is captured before binding;
an unresolved caller is registered as a permanent rejection, without fake claims. -/
noncomputable def prepareClaims {cap : Nat} (s : State cap) (p : Profile) (entry : FramedHistory)
    (key : StackWHIRReplay.Key p) (request : Option (ClaimRequest cap p)) : State cap × Label cap p :=
  match request with
  | none => prepare s p entry key none
  | some request =>
    let committed := commit s p request.root request.lanes request.lane_bound
    prepare committed.1 p entry key (some (bindClaims committed.2 request.claims))

@[simp] theorem prepareClaims_key {cap : Nat} (s : State cap) (p : Profile)
    (entry : FramedHistory) (key : StackWHIRReplay.Key p) (request : Option (ClaimRequest cap p)) :
    (prepareClaims s p entry key request).2.key = key := by
  cases request <;> rfl

@[simp] theorem prepareClaims_entry {cap : Nat} (s : State cap) (p : Profile)
    (entry : FramedHistory) (key : StackWHIRReplay.Key p) (request : Option (ClaimRequest cap p)) :
    (prepareClaims s p entry key request).2.entry = entry := by
  cases request <;> rfl

@[simp] theorem prepareClaims_state {cap : Nat} (s : State cap) (p : Profile)
    (entry : FramedHistory) (key : StackWHIRReplay.Key p) (request : Option (ClaimRequest cap p)) :
    (prepareClaims s p entry key request).2.state = (prepareClaims s p entry key request).1 := by
  cases request <;> rfl

theorem prepareClaims_extends {cap : Nat} (s : State cap) (p : Profile) (entry : FramedHistory)
    (key : StackWHIRReplay.Key p) (request : Option (ClaimRequest cap p)) :
    Extends s (prepareClaims s p entry key request).1 := by
  cases request with
  | none => exact prepare_extends _ _ _ _ _
  | some request =>
    exact (registerRoot_extends s request.root).trans (prepare_extends _ _ _ _ _)

/-- The first unresolved caller is recorded, rather than left available for replacement. -/
theorem prepareClaims_first_rejected {cap : Nat} (s : State cap) (p : Profile)
    (entry : FramedHistory) (key : StackWHIRReplay.Key p) (fresh : s.entries p entry = none) :
    (prepareClaims s p entry key none).1.entries p entry = some none := by
  exact (registerFootprint_extends (registerStatement s p entry none) p key).entries p entry none
    (by simpa [selected, fresh] using registerStatement_found s p entry none)

/-- Any later resolver request, valid or invalid, preserves an earlier rejection. -/
theorem prepareClaims_preserves_rejection {cap : Nat} (s : State cap) (p : Profile)
    (entry : FramedHistory) (key : StackWHIRReplay.Key p) (request : Option (ClaimRequest cap p))
    (rejected : s.entries p entry = some none) :
    (prepareClaims s p entry key request).1.entries p entry = some none ∧
      (prepareClaims s p entry key request).1.catalog p entry = none :=
  (prepareClaims_extends s p entry key request).rejected p entry rejected

theorem commit_persists {cap : Nat} (s : State cap) (p : Profile) (root : Digest32)
    (lanes : Nat) (bound : lanes ≤ 2 ^ (config p).folds[0]!) (later : State cap)
    (growth : Extends (commit s p root lanes bound).1 later) :
    (commit s p root lanes bound).2 = capture later p root lanes bound := by
  obtain ⟨snap,known⟩ := registerRoot_known s root
  exact capture_stable growth p root lanes bound snap known

theorem commitment_before_claims (cap : Nat) (p : Profile) (c : Commitment p) :
    ∃ candidates : Finset (Witness (config p) c.lanes),
      candidates.card ≤ 2^32 ∧ ∀ claims : OriginalClaims cap,
        InitialCandidates.witnesses (config p) (bindClaims c claims).lanes
          (bindClaims c claims).root = candidates :=
  ⟨c.witnesses,c.witnesses_bound,fun claims => bindClaims_witnesses c claims⟩

def Covered {cap : Nat} (s : State cap) : Prop :=
  ∀ root snap, lookup root s.registry = some snap →
    snap.table ⊆ recordDomain ((s.frozen root).getD [])

theorem empty_covered (cap : Nat) : Covered (empty cap) := by
  intro root snap known
  simp [empty,lookup] at known

theorem observe_covered {cap : Nat} (s : State cap) (input : List Byte) (value : Digest32)
    (covered : Covered s) : Covered (observe s input value) := by
  unfold observe
  cases recordLookup input s.records <;> exact covered

theorem registerRoot_covered {cap : Nat} (s : State cap) (root : Digest32)
    (covered : Covered s) : Covered (registerRoot s root) := by
  unfold registerRoot
  cases found : lookup root s.registry with
  | some _ => exact covered
  | none =>
    intro r snap known
    by_cases eq : r = root
    · subst r
      have hs : snap = snapshot s.records := by
        simpa [register,found,lookup] using known.symm
      subst snap
      simp [snapshot]
    · have old : lookup r s.registry = some snap := by
        simpa [register,found,lookup,eq] using known
      simpa [Function.update_of_ne eq] using covered r snap old

theorem registerRoots_covered {cap : Nat} (s : State cap) (rs : List Digest32)
    (covered : Covered s) : Covered (registerRoots s rs) := by
  induction rs generalizing s with
  | nil => exact covered
  | cons r rs ih => exact ih (registerRoot s r) (registerRoot_covered s r covered)

theorem registerStatement_covered {cap : Nat} (s : State cap) (p : Profile)
    (entry : FramedHistory) (data : Option (WHIRFiatShamir.StackInitial p cap)) (covered : Covered s) :
    Covered (registerStatement s p entry data) := by
  unfold registerStatement
  cases s.entries p entry <;> exact covered

theorem prepare_covered {cap : Nat} (s : State cap) (p : Profile) (entry : FramedHistory)
    (key : StackWHIRReplay.Key p) (proposed : Option (WHIRFiatShamir.StackInitial p cap))
    (covered : Covered s) : Covered (prepare s p entry key proposed).1 :=
  registerRoots_covered _ _ (registerStatement_covered s p entry proposed covered)

theorem prepareClaims_covered {cap : Nat} (s : State cap) (p : Profile) (entry : FramedHistory)
    (key : StackWHIRReplay.Key p) (request : Option (ClaimRequest cap p)) (covered : Covered s) :
    Covered (prepareClaims s p entry key request).1 := by
  cases request with
  | none => exact prepare_covered _ _ _ _ _ covered
  | some request => exact prepare_covered _ _ _ _ _ (registerRoot_covered s request.root covered)

def AuthenticState {cap : Nat} (hash : MerkleTransport.Primitive) (s : State cap) : Prop :=
  Authentic hash s.records ∧ ∀ root records, s.frozen root = some records → Authentic hash records

theorem empty_authentic (hash : MerkleTransport.Primitive) (cap : Nat) :
    AuthenticState hash (empty cap) := by
  simp [AuthenticState,empty,Authentic]

theorem observe_authentic {cap : Nat} (hash : MerkleTransport.Primitive) (s : State cap)
    (input : List Byte) (value : Digest32) (authentic : AuthenticState hash s)
    (answer : hash input = value) : AuthenticState hash (observe s input value) := by
  unfold observe
  cases recordLookup input s.records with
  | some _ => exact authentic
  | none =>
    refine ⟨?_,authentic.2⟩
    intro x d member
    rcases List.mem_cons.mp member with eq | member
    · cases eq; exact answer
    · exact authentic.1 x d member

theorem registerRoot_authentic {cap : Nat} (hash : MerkleTransport.Primitive) (s : State cap)
    (root : Digest32) (authentic : AuthenticState hash s) :
    AuthenticState hash (registerRoot s root) := by
  unfold registerRoot
  cases lookup root s.registry with
  | some _ => exact authentic
  | none =>
    refine ⟨authentic.1,?_⟩
    intro r records known
    by_cases eq : r = root
    · subst r
      have hr : records = s.records := by simpa using known.symm
      subst records
      exact authentic.1
    · exact authentic.2 r records (by simpa [Function.update_of_ne eq] using known)

theorem registerRoots_authentic {cap : Nat} (hash : MerkleTransport.Primitive) (s : State cap)
    (rs : List Digest32) (authentic : AuthenticState hash s) :
    AuthenticState hash (registerRoots s rs) := by
  induction rs generalizing s with
  | nil => exact authentic
  | cons r rs ih => exact ih (registerRoot s r) (registerRoot_authentic hash s r authentic)

theorem registerStatement_authentic {cap : Nat} (hash : MerkleTransport.Primitive)
    (s : State cap) (p : Profile) (entry : FramedHistory) (data : Option (WHIRFiatShamir.StackInitial p cap))
    (authentic : AuthenticState hash s) : AuthenticState hash (registerStatement s p entry data) := by
  unfold registerStatement
  cases s.entries p entry <;> exact authentic

theorem frozen_authentic {cap : Nat} (hash : MerkleTransport.Primitive) (s : State cap)
    (authentic : AuthenticState hash s) (root : Digest32) :
    Authentic hash ((s.frozen root).getD []) := by
  cases found : s.frozen root with
  | none => simp [Authentic]
  | some records => exact authentic.2 root records found

theorem capture_covered {cap : Nat} (s : State cap) (p : Profile) (root : Digest32)
    (lanes : Nat) (bound : lanes ≤ 2 ^ (config p).folds[0]!) (covered : Covered s) :
    (capture s p root lanes bound).snapshot.table ⊆
      recordDomain (capture s p root lanes bound).records := by
  cases found : lookup root s.registry with
  | none => simp [capture,found,snapshot,recordDomain]
  | some snap => simpa [capture,found] using covered root snap found

/-- This is a locality theorem about genuine exposed hash answers, not a future-dependent choice of an ideal row oracle. -/
theorem capture_base_actual {cap : Nat} (hash : MerkleTransport.Primitive) (s : State cap)
    (p : Profile) (root : Digest32) (lanes : Nat) (bound : lanes ≤ 2 ^ (config p).folds[0]!)
    (covered : Covered s) (authentic : AuthenticState hash s) :
    (capture s p root lanes bound).base =
      WHIRPhysicalRows.compactBaseOracle hash (capture s p root lanes bound).snapshot root
        (remaining (config p) 0 + (config p).rates[0]!) (ParameterBounds.length (config p) 0)
        (2 ^ (config p).folds[0]!) lanes :=
  (WHIRPhysicalRows.compactBaseOracle_eq_recorded hash _ root _ _ _ _ _ _
    (frozen_authentic hash s authentic root) (capture_covered s p root lanes bound covered)).symm

theorem roots_actual {cap : Nat} (hash : MerkleTransport.Primitive) (s : State cap)
    (p : Profile) (root : Digest32) (level : Nat) (snap : Snapshot)
    (known : lookup root s.registry = some snap) (covered : Covered s)
    (authentic : AuthenticState hash s) :
    roots s p root level = intermediateOracle hash snap root
      (remaining (config p) level + (config p).rates[level]!)
      (ParameterBounds.length (config p) level) (2 ^ (config p).folds[level]!) := by
  simp only [roots,known,Option.getD_some]
  exact (intermediateOracle_eq_recorded hash snap root _ _ _ _ _
    (frozen_authentic hash s authentic root) (covered root snap known)).symm

end Whir.CausalBindingState
