import Whir.WHIRReplay

/-! The actual stacked opening uses one initial eight-scalar allocation. The
ring prefix transforms the original frozen statement before ordinary WHIR
replay; it is not a second query or a preselected transformed statement. -/
namespace Whir.StackWHIRReplay
open Concrete Protocol CausalGame CausalProbability ParameterBounds
open FiatShamirGame (Digest32)
open WHIRHistory (Pending)

abbrev Sample {c : Config} : Coordinate c → Type := WHIRHistory.StackSample

noncomputable instance {c : Config} (q : Coordinate c) : Fintype (Sample q) := by
  cases q <;> unfold Sample <;> infer_instance
instance {c : Config} (q : Coordinate c) : Nonempty (Sample q) := by
  cases q <;> unfold Sample <;> infer_instance

abbrev Key (p : Profile) :=
  TypedFiatShamirGame.FullInput Digest32 Pending (Coordinate (config p)) Sample
abbrev query := WHIRReplay.query
abbrev Answer (p : Profile) (key : Key p) := Sample (query p (key.statement,key.messages))
abbrev Catalog (p : Profile) (cap : Nat) := Digest32 → Option (WHIRFiatShamir.StackInitial p cap)
abbrev Roots := WHIRReplay.Roots

def transformedStatement {p : Profile} {cap : Nat} (data : WHIRFiatShamir.StackInitial p cap)
    (ringPrefix : RingPCSGame.Prefix) : WHIRFiatShamir.Statement p where
  lanes := data.lanes
  root := data.root
  claims := RingPCSGame.transformedClaims (2 ^ (config p).logN) data.family data.points ringPrefix
  lane_bound := data.lane_bound
  claim_shape := RingPCSGame.transformedClaims_shapes _ _ _ _
  claim_cap := by simpa only [RingPCSGame.transformedClaims_size, Nat.add_comm] using data.claim_bound

/-- Projection keeps the WHIR lambda but not the preceding seven ring scalars.
The full compiler cache and its keys still retain the entire initial vector. -/
def projectSample {c : Config} (q : Coordinate c) : Sample q → CausalProbability.Sample q :=
  match q with
  | .initial => fun x => x.2
  | .fold _ _ => id
  | .ood _ _ => id
  | .query _ => id
  | .tail _ => id

def projectEntry {c : Config} (entry : Pending × Sigma (@Sample c)) :
    Pending × Sigma (@CausalProbability.Sample c) :=
  (entry.1,⟨entry.2.1,projectSample entry.2.1 entry.2.2⟩)

def projectKey {p : Profile} (key : Key p) : WHIRReplay.Key p :=
  ⟨key.statement,key.messages,key.ancestors.map projectEntry⟩

def seedValue {c : Config} : Sigma (@Sample c) → Option (RingPCSGame.Prefix × E)
  | ⟨.initial,x⟩ => some x
  | _ => none

/-- The oldest completed ancestor is the indivisible initial allocation. -/
def initialSeed {c : Config} (history : List (Pending × Sigma (@Sample c))) :
    Option (RingPCSGame.Prefix × E) :=
  history.getLast?.bind (fun entry => seedValue entry.2)

theorem initialSeed_drop {c : Config} (history : List (Pending × Sigma (@Sample c)))
    (i : Nat) (hi : i < history.length) : initialSeed (history.drop i) = initialSeed history := by
  simp [initialSeed, List.getLast?_drop, Nat.not_le_of_lt hi]

theorem initialSeed_last {c : Config} (history : List (Pending × Sigma (@Sample c)))
    (seed : RingPCSGame.Prefix × E) (ok : initialSeed history = some seed) :
    ∃ m, history.getLast? = some (m,⟨.initial,seed⟩) := by
  unfold initialSeed at ok
  cases last : history.getLast? with
  | none => simp [last] at ok
  | some entry =>
    rcases entry with ⟨m,q,a⟩
    cases q <;> simp [last,seedValue] at ok
    subst seed
    exact ⟨m,rfl⟩

structure Replay (p : Profile) (cap : Nat) where
  original : WHIRFiatShamir.StackInitial p cap
  initial : RingPCSGame.Prefix × E
  whir : WHIRReplay.Replay p

/-- This local catalog is used only after the original digest has been resolved.
All recursive decoder calls retain that same digest. -/
def localCatalog {p : Profile} {cap : Nat} (data : WHIRFiatShamir.StackInitial p cap)
    (seed : RingPCSGame.Prefix × E) : WHIRReplay.Catalog p :=
  fun _ => some (transformedStatement data seed.1)

def decode (p : Profile) (cap : Nat) (catalog : Catalog p cap) (roots : Roots)
    (key : Key p) : Option (Replay p cap) := do
  let original ← catalog key.statement
  let initial ← initialSeed key.ancestors
  let whir ← WHIRReplay.decode p (localCatalog original initial) roots (projectKey key)
  pure ⟨original,initial,whir⟩

/-- Initial requests are parsed before their eight-scalar answer exists. -/
def decodeInitial (p : Profile) (cap : Nat) (catalog : Catalog p cap) (key : Key p) :
    Option (WHIRFiatShamir.StackInitial p cap) :=
  match key.messages, key.ancestors with
  | [m], [] => if m.scalars.isEmpty && m.nonce.isNone then catalog key.statement else none
  | _, _ => none

def request (p : Profile) (cap : Nat) (catalog : Catalog p cap) (roots : Roots)
    (key : Key p) : Option (WHIRFiatShamir.StackRequest p cap) :=
  if h : query p (key.statement,key.messages) = .initial then
    (decodeInitial p cap catalog key).map WHIRFiatShamir.StackRequest.initial
  else
    (decode p cap catalog roots key).map (fun r =>
      .later (WHIRReplay.request (projectKey key) r.whir) h)

def finish {p : Profile} {cap : Nat} (key : Key p) (r : Replay p cap) (x : Answer p key) : Replay p cap :=
  {r with whir := WHIRReplay.finish (projectKey key) r.whir (projectSample _ x)}

theorem decode_spec {p : Profile} {cap : Nat} (catalog : Catalog p cap) (roots : Roots)
    (key : Key p) (out : Replay p cap) (ok : decode p cap catalog roots key = some out) :
    catalog key.statement = some out.original ∧ initialSeed key.ancestors = some out.initial ∧
      WHIRReplay.decode p (localCatalog out.original out.initial) roots (projectKey key) = some out.whir := by
  unfold decode at ok
  cases hd : catalog key.statement with
  | none => simp [hd] at ok
  | some data =>
    cases hs : initialSeed key.ancestors with
    | none => simp [hd,hs] at ok
    | some seed =>
      cases hw : WHIRReplay.decode p (localCatalog data seed) roots (projectKey key) with
      | none => simp [hd,hs,hw] at ok
      | some whir =>
        simp [hd,hs,hw] at ok
        subst out
        exact ⟨rfl,rfl,hw⟩

theorem decode_statement {p : Profile} {cap : Nat} (catalog : Catalog p cap) (roots : Roots)
    (key : Key p) (out : Replay p cap) (ok : decode p cap catalog roots key = some out) :
    out.whir.statement = transformedStatement out.original out.initial.1 := by
  have hw := (decode_spec catalog roots key out ok).2.2
  have hs := (WHIRReplay.decodeHistory_decodes p _ _ _ _ _ out.whir hw).statement
  exact (Option.some.inj hs).symm

theorem decode_initial_lambda {p : Profile} {cap : Nat} (catalog : Catalog p cap) (roots : Roots)
    (key : Key p) (out : Replay p cap) (ok : decode p cap catalog roots key = some out)
    (x : Answer p key) : get .initial (finish key out x).whir.tape = out.initial.2 := by
  obtain ⟨_,hs,hw⟩ := decode_spec catalog roots key out ok
  obtain ⟨m,last⟩ := initialSeed_last key.ancestors out.initial hs
  have hm : projectEntry (m,⟨.initial,out.initial⟩) ∈ (projectKey key).ancestors :=
    List.mem_map.mpr ⟨_,List.mem_of_getLast? last,rfl⟩
  exact (WHIRReplay.finish_samples _ roots (projectKey key) out.whir hw (projectSample _ x)).2 _ hm

/-- No resampling or transformed-statement hypothesis is needed when moving to
an earlier non-initial key: its oldest eight-scalar ancestor is unchanged. -/
theorem decode_prefix_finish {p : Profile} {cap : Nat} (catalog : Catalog p cap) (roots : Roots)
    (key : Key p) (out : Replay p cap) (ok : decode p cap catalog roots key = some out)
    (x : Answer p key) (i : Nat) (hi : i < key.ancestors.length) (hm : i < key.messages.length) :
    ∃ before, decode p cap catalog roots ⟨key.statement,key.messages.drop i,key.ancestors.drop i⟩ =
        some before ∧ before.original = out.original ∧ before.initial = out.initial ∧
      WHIRReplay.PrefixAgreement (position (query p (key.statement,key.messages.drop i)))
        before.whir (finish key out x).whir := by
  obtain ⟨hd,hs,hw⟩ := decode_spec catalog roots key out ok
  obtain ⟨before,hb,hp⟩ := WHIRReplay.decode_prefix_finish _ roots (projectKey key) out.whir hw
    (projectSample _ x) i hm
  refine ⟨⟨out.original,out.initial,before⟩,?_,rfl,rfl,hp⟩
  have hb' : WHIRReplay.decode p (localCatalog out.original out.initial) roots
      (projectKey ⟨key.statement,key.messages.drop i,key.ancestors.drop i⟩) = some before := by
    simpa only [projectKey,List.map_drop] using hb
  simp [decode,hd,initialSeed_drop _ i hi,hs,hb']

theorem decoded_ancestor_length {p : Profile} {catalog : WHIRReplay.Catalog p} {roots : Roots}
    {s messages ancestors out} (h : WHIRReplay.Decodes p catalog roots s messages ancestors out) :
    ancestors.length + 1 = messages.length := by
  induction h <;> simp_all

theorem decode_ancestor_length {p : Profile} {cap : Nat} (catalog : Catalog p cap) (roots : Roots)
    (key : Key p) (out : Replay p cap) (ok : decode p cap catalog roots key = some out) :
    key.ancestors.length + 1 = key.messages.length := by
  have hw := (decode_spec catalog roots key out ok).2.2
  simpa only [projectKey,List.length_map] using
    decoded_ancestor_length (WHIRReplay.decodeHistory_decodes p _ _ _ _ _ out.whir hw)

theorem finish_samples {p : Profile} {cap : Nat} (catalog : Catalog p cap) (roots : Roots)
    (key : Key p) (out : Replay p cap) (ok : decode p cap catalog roots key = some out)
    (x : Answer p key) :
    get (query p (key.statement,key.messages)) (finish key out x).whir.tape = projectSample _ x ∧
      ∀ entry ∈ key.ancestors, get entry.2.1 (finish key out x).whir.tape =
        projectSample entry.2.1 entry.2.2 := by
  have hw := (decode_spec catalog roots key out ok).2.2
  obtain ⟨current,past⟩ := WHIRReplay.finish_samples _ roots (projectKey key) out.whir hw (projectSample _ x)
  refine ⟨current,?_⟩
  intro entry member
  exact past (projectEntry entry) (List.mem_map.mpr ⟨entry,member,rfl⟩)

/-- Exact trace realization for every later WHIR allocation, retaining the
original first vector in both the full key and the decoded stack context. -/
theorem trace_realization {p : Profile} {cap : Nat} (catalog : Catalog p cap) (roots : Roots)
    (key : Key p) (out : Replay p cap) (ok : decode p cap catalog roots key = some out)
    (x : Answer p key) (head : Pending) (trace : List (Sigma (Answer p)))
    (recorded : TypedOracleCompiler.HistoryRecorded (query p) key.statement trace key.messages
      ((head,⟨query p (key.statement,key.messages),x⟩)::key.ancestors))
    (i : Nat) (hi : i < key.ancestors.length) :
    ∃ m tail past, ∃ a : Sample (query p (key.statement,m::tail)), ∃ before : Replay p cap,
      key.messages.drop i = m::tail ∧
      (⟨⟨key.statement,m::tail,past⟩,a⟩ : Sigma (Answer p)) ∈ trace ∧
      decode p cap catalog roots ⟨key.statement,m::tail,past⟩ = some before ∧
      before.original = out.original ∧ before.initial = out.initial ∧
      WHIRReplay.PrefixAgreement (position (query p (key.statement,m::tail)))
        before.whir (finish key out x).whir ∧
      get (query p (key.statement,m::tail)) (finish key out x).whir.tape = projectSample _ a ∧
      position (query p (key.statement,m::tail)) = key.messages.length - i - 1 := by
  have len := decode_ancestor_length catalog roots key out ok
  have him : i < key.messages.length := by omega
  obtain ⟨m,tail,past,a,hm,hh,allocated⟩ := TypedOracleCompiler.HistoryRecorded.at_index
    (query p) recorded i him
  obtain ⟨before,hb,hd,hs,hp⟩ := decode_prefix_finish catalog roots key out ok x i hi him
  have ha : key.ancestors.drop i = past := by
    have ht := congrArg List.tail hh
    simpa only [List.tail_drop,List.drop_succ_cons,List.tail_cons] using ht
  have parsed : decode p cap catalog roots ⟨key.statement,m::tail,past⟩ = some before := by
    simpa only [hm,ha] using hb
  have agree : WHIRReplay.PrefixAgreement (position (query p (key.statement,m::tail)))
      before.whir (finish key out x).whir := by simpa only [hm] using hp
  have sample : get (query p (key.statement,m::tail)) (finish key out x).whir.tape = projectSample _ a := by
    have member : (m,(⟨query p (key.statement,m::tail),a⟩ : Sigma Sample)) ∈
        (head,⟨query p (key.statement,key.messages),x⟩)::key.ancestors :=
      List.mem_of_mem_drop (by rw [hh]; exact List.mem_cons_self)
    rcases List.mem_cons.mp member with same | older
    · have eqs := congrArg Prod.snd same
      exact Eq.mp (congrArg (fun qa : Sigma Sample =>
        get qa.1 (finish key out x).whir.tape = projectSample qa.1 qa.2) eqs.symm)
          (finish_samples catalog roots key out ok x).1
    · exact (finish_samples catalog roots key out ok x).2 _ older
  have hw := (decode_spec catalog roots _ before parsed).2.2
  have pos := (WHIRReplay.decodeHistory_decodes p _ _ _ _ _ before.whir hw).phase_position
  have length := congrArg List.length hm
  rw [List.length_drop] at length
  refine ⟨m,tail,past,a,before,hm,allocated,parsed,hd,hs,agree,sample,?_⟩
  change position (query p (key.statement,m::tail)) = (m::tail).length - 1 at pos
  rw [pos,← length]

/-- The oldest initial allocation is present as the original full eight-scalar
sample, not just its lambda projection, and parses to the frozen original
stack statement. -/
theorem initial_trace_realization {p : Profile} {cap : Nat} (catalog : Catalog p cap) (roots : Roots)
    (key : Key p) (out : Replay p cap) (ok : decode p cap catalog roots key = some out)
    (x : Answer p key) (head : Pending) (trace : List (Sigma (Answer p)))
    (recorded : TypedOracleCompiler.HistoryRecorded (query p) key.statement trace key.messages
      ((head,⟨query p (key.statement,key.messages),x⟩)::key.ancestors)) :
    ∃ m, ∃ a : Sample (query p (key.statement,[m])),
      (⟨⟨key.statement,[m],[]⟩,a⟩ : Sigma (Answer p)) ∈ trace ∧
      decodeInitial p cap catalog ⟨key.statement,[m],[]⟩ = some out.original ∧
      seedValue ⟨query p (key.statement,[m]),a⟩ = some out.initial := by
  obtain ⟨hd,hs,hw⟩ := decode_spec catalog roots key out ok
  have len := decode_ancestor_length catalog roots key out ok
  have hi : key.ancestors.length < key.messages.length := by omega
  obtain ⟨m,tail,past,a,hm,hh,allocated⟩ := TypedOracleCompiler.HistoryRecorded.at_index
    (query p) recorded key.ancestors.length hi
  have htail : tail = [] := by
    have h := congrArg List.length hm
    simp only [List.length_drop,List.length_cons] at h
    exact List.length_eq_zero_iff.mp (by omega)
  subst tail
  have hpast : past = [] := by
    have h := congrArg List.length hh
    simp only [List.length_drop,List.length_cons] at h
    exact List.length_eq_zero_iff.mp (by omega)
  subst past
  have nonempty : key.ancestors ≠ [] := by
    intro he
    simp [he,initialSeed] at hs
  have last : key.ancestors.getLast? = some (m,⟨query p (key.statement,[m]),a⟩) := by
    have h := congrArg List.getLast? hh
    simpa [List.getLast?_drop,List.getLast?_cons_of_ne_nil nonempty] using h
  have sample : seedValue ⟨query p (key.statement,[m]),a⟩ = some out.initial := by
    simpa only [initialSeed,last,Option.bind_some] using hs
  obtain ⟨before,hb,_⟩ := WHIRReplay.decode_prefix _ roots (projectKey key) out.whir hw
    key.ancestors.length hi
  have parsed : WHIRReplay.decode p (localCatalog out.original out.initial) roots
      ⟨key.statement,[m],[]⟩ = some before := by
    have drop : (key.ancestors.map projectEntry).drop key.ancestors.length = [] := by simp
    simpa only [projectKey,hm,drop] using hb
  have derivation := WHIRReplay.decodeHistory_decodes p _ _ _ _ _ before parsed
  have initial : decodeInitial p cap catalog ⟨key.statement,[m],[]⟩ = some out.original := by
    cases derivation with
    | initial shape found => simp [decodeInitial,shape,hd]
  exact ⟨m,a,allocated,initial,sample⟩

/-- Original fixed-list falsity is transported through the actual executable
ring-family transformation unless the charged ring event already occurred. -/
theorem false_or_initial_event {p : Profile} {cap : Nat} (catalog : Catalog p cap) (roots : Roots)
    (key : Key p) (out : Replay p cap) (ok : decode p cap catalog roots key = some out)
    (hfalse : ¬ ∃ w ∈ InitialCandidates.witnesses (config p) out.original.lanes out.original.root,
      RingPCSGame.Honest (config p) out.original.lanes out.original.family out.original.points w)
    (outside : ¬ RingPCSGame.InitialEvent p out.original.lanes out.original.root
      out.original.family out.original.points out.initial) :
    ¬ ∃ w ∈ InitialCandidates.witnesses (config p) out.whir.statement.lanes out.whir.statement.root,
      ∀ claim ∈ out.whir.statement.claims.toList,
        dot (paddedWitness (config p) out.whir.statement.lanes w) claim.weight = claim.value := by
  rw [decode_statement catalog roots key out ok]
  exact RingPCSGame.false_or_escape (config p) _ _ _ _ _ hfalse (fun h => outside (Or.inl h))

/-- The actual accepted-false cover separates the one grouped initial event
from all later WHIR coordinates. Original honesty, not transformed honesty,
is the input predicate. Both alternatives are proved from the checked verifier. -/
theorem accepted_false_cover {p : Profile} {cap : Nat} (catalog : Catalog p cap) (roots : Roots)
    (key : Key p) (out : Replay p cap) (ok : decode p cap catalog roots key = some out)
    (x : Answer p key)
    (accepted : CausalGame.experiment out.whir.statement.input
      (CausalStrategy.indexedStrategy out.whir.replies) (finish key out x).whir.tape = true)
    (hfalse : ¬ ∃ w ∈ InitialCandidates.witnesses (config p) out.original.lanes out.original.root,
      RingPCSGame.Honest (config p) out.original.lanes out.original.family out.original.points w) :
    RingPCSGame.InitialEvent p out.original.lanes out.original.root
      out.original.family out.original.points out.initial ∨
    ∃ q : Coordinate (config p), q ≠ .initial ∧
      WHIRFiatShamir.allocationBad
        (WHIRFiatShamir.requestOfTape out.whir.statement
          (CausalStrategy.indexedStrategy out.whir.replies) q (finish key out x).whir.tape)
        (get q (finish key out x).whir.tape) := by
  classical
  by_cases initial : RingPCSGame.InitialEvent p out.original.lanes out.original.root
      out.original.family out.original.points out.initial
  · exact Or.inl initial
  · right
    obtain ⟨q,hq⟩ := WHIRFiatShamir.accepted_false_prefix_cover p out.whir.statement
      (CausalStrategy.indexedStrategy out.whir.replies) (finish key out x).whir.tape accepted
      (false_or_initial_event catalog roots key out ok hfalse initial)
    by_cases same : q = .initial
    · subst q
      apply (initial (Or.inr ?_)).elim
      change get .initial (set .initial
        (WHIRFiatShamir.Prefix.ofTape .initial (finish key out x).whir.tape).tape
        (get .initial (finish key out x).whir.tape)) ∈
          InitialBatching.candidateEscape
            (InitialCandidates.extensionCandidates (config p) out.whir.statement.lanes out.whir.statement.root)
            out.whir.statement.claims at hq
      rw [get_set,decode_initial_lambda catalog roots key out ok x] at hq
      simpa only [decode_statement catalog roots key out ok,transformedStatement] using hq
    · exact ⟨q,same,hq⟩

end Whir.StackWHIRReplay
