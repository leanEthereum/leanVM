import Whir.WHIRHistory
import Whir.CausalStrategy
import Whir.TypedOracleCompiler

/-! Concrete reification of canonical typed-ROM keys. The immutable statement
catalog and extracted commitment table are explicit inputs, not assumed parsers
or a source of future challenge samples. Malformed keys return `none`. -/
namespace Whir.WHIRReplay
open Concrete Protocol CausalGame CausalProbability ParameterBounds
open FiatShamirGame (Digest32)
open WHIRHistory (Pending)

abbrev Key (p : Profile) :=
  TypedFiatShamirGame.FullInput Digest32 Pending (Coordinate (config p)) Sample
abbrev query (p : Profile) := WHIRHistory.queryFor (config p)
abbrev Answer (p : Profile) (key : Key p) := Sample (query p (key.statement,key.messages))
abbrev Catalog (p : Profile) := Digest32 → Option (WHIRFiatShamir.Statement p)
/-- Frozen extracted commitments, indexed by the requested code level. -/
abbrev Roots := Digest32 → Nat → Oracle

structure Replay (p : Profile) where
  statement : WHIRFiatShamir.Statement p
  tape : Tape (config p)
  replies : Array Reply

def zeroTape (p : Profile) : Tape (config p) :=
  (coordinates (config p)).symm (fun _ => 0)

/-- Rows are reconstructed in sampled order from the actual prequery oracle.
They are not read from a guessed proof body or supplied through a certificate. -/
def queryRows {p : Profile} (r : Replay p) (i : Fin (config p).folds.size)
    (x : Sample (.query i)) : Oracle :=
  (QueryBatchSoundness.queries (remaining (config p) i + (config p).rates[i.val]!)
    (config p).queries[i.val]! x.1).map
      (fun q => (CausalExecution.levelAt r.statement.input
        (CausalStrategy.indexedStrategy r.replies) r.tape i).oracle[q]!)

def reply {p : Profile} (roots : Roots) (r : Replay p) (q : Coordinate (config p))
    (x : Sample q) (pending : Pending) : Option Reply :=
  let lookup := fun digest => roots digest (WHIRHistory.coordinateLevel q + 1)
  let rows := match q, x with
    | .query i, x => queryRows r i x
    | _, _ => #[]
  WHIRHistory.decodeReplyScalars q lookup rows pending.scalars

/-- Extend only by the answer actually recorded for the preceding full key,
then parse the absorbed response with the concrete transport decoder. -/
def step {p : Profile} (roots : Roots) (r : Replay p) (q : Coordinate (config p))
    (x : Sample q) (pending : Pending) : Option (Replay p) :=
  (reply roots r q x pending).map (fun response =>
    ⟨r.statement, set q r.tape x, r.replies.push response⟩)

theorem step_spec {p : Profile} (roots : Roots) (r out : Replay p)
    (q : Coordinate (config p)) (x : Sample q) (pending : Pending)
    (ok : step roots r q x pending = some out) :
    ∃ response, reply roots r q x pending = some response ∧
      out = ⟨r.statement,set q r.tape x,r.replies.push response⟩ := by
  unfold step at ok
  cases hr : reply roots r q x pending with
  | none => simp [hr] at ok
  | some response =>
    simp only [hr, Option.map_some, Option.some.injEq] at ok
    exact ⟨response,rfl,ok.symm⟩

/-- The nonce is an auxiliary public event exactly at a query batch. It is not
an algebraic query row and earns no grinding factor. -/
def nonceShape {c : Config} (q : Coordinate c) (m : Pending) : Bool :=
  match q with
  | .query _ => m.nonce.isSome
  | _ => m.nonce.isNone

/-- The raw syntax and completed ancestors must agree at each recursive step.
Position checks enforce strict chronological challenge use even on malformed
or rejecting branches. Only successful decoding produces a replay state. -/
def decodeHistory (p : Profile) (catalog : Catalog p) (roots : Roots) (s : Digest32) :
    List Pending → List (Pending × Sigma (@Sample (config p))) → Option (Replay p)
  | [], _ => none
  | [m], [] => do
    if m.scalars.isEmpty && m.nonce.isNone then
      let statement ← catalog s
      pure ⟨statement,zeroTape p,#[]⟩
    else none
  | m :: previous :: older, (previous' , ⟨q,x⟩) :: past => do
    if previous' = previous then
      if _hq : q = query p (s,previous::older) then
        if position q = older.length then
          if position (query p (s,m::previous::older)) = older.length + 1 then
            if nonceShape (query p (s,m::previous::older)) m then
              let before ← decodeHistory p catalog roots s (previous::older) past
              step roots before q x m
            else none
          else none
        else none
      else none
    else none
  | _, _ => none

def decode (p : Profile) (catalog : Catalog p) (roots : Roots) (key : Key p) : Option (Replay p) :=
  decodeHistory p catalog roots key.statement key.messages key.ancestors

def request {p : Profile} (key : Key p) (r : Replay p) : WHIRFiatShamir.Request p :=
  WHIRFiatShamir.requestOfTape r.statement (CausalStrategy.indexedStrategy r.replies)
    (query p (key.statement,key.messages)) r.tape

/-- The executable decoder's successful derivations. Each constructor performs
the concrete scalar parser, rather than assuming a replay certificate. -/
inductive Decodes (p : Profile) (catalog : Catalog p) (roots : Roots) (s : Digest32) :
    List Pending → List (Pending × Sigma (@Sample (config p))) → Replay p → Prop where
  | initial {m statement}
      (shape : (m.scalars.isEmpty && m.nonce.isNone) = true)
      (found : catalog s = some statement) :
      Decodes p catalog roots s [m] [] ⟨statement,zeroTape p,#[]⟩
  | next {m previous older past q x before out}
      (prior : Decodes p catalog roots s (previous::older) past before)
      (phase : q = query p (s,previous::older))
      (previousPosition : position q = older.length)
      (currentPosition : position (query p (s,m::previous::older)) = older.length + 1)
      (nonce : nonceShape (query p (s,m::previous::older)) m = true)
      (parsed : step roots before q x m = some out) :
      Decodes p catalog roots s (m::previous::older) ((previous,⟨q,x⟩)::past) out

theorem decodeHistory_decodes (p : Profile) (catalog : Catalog p) (roots : Roots) (s : Digest32)
    (messages : List Pending) (ancestors : List (Pending × Sigma (@Sample (config p))))
    (out : Replay p) (ok : decodeHistory p catalog roots s messages ancestors = some out) :
    Decodes p catalog roots s messages ancestors out := by
  induction messages generalizing ancestors out with
  | nil => cases ok
  | cons m messages ih =>
    cases messages with
    | nil =>
      cases ancestors with
      | cons a as => cases ok
      | nil =>
        simp only [decodeHistory] at ok
        split at ok
        · rename_i shape
          cases found : catalog s with
          | none => simp [found] at ok
          | some statement =>
            simp [found] at ok
            subst out
            exact .initial shape found
        · cases ok
    | cons previous older =>
      cases ancestors with
      | nil => cases ok
      | cons a past =>
        rcases a with ⟨previous',q,x⟩
        simp only [decodeHistory] at ok
        split at ok
        · rename_i same
          subst previous'
          split at ok
          · rename_i phase
            split at ok
            · rename_i previousPosition
              split at ok
              · rename_i currentPosition
                split at ok
                · rename_i nonce
                  cases prior : decodeHistory p catalog roots s (previous::older) past with
                  | none => simp [prior] at ok
                  | some before =>
                    simp only [prior] at ok
                    exact .next (ih past before prior) phase previousPosition currentPosition nonce ok
                · cases ok
              · cases ok
            · cases ok
          · cases ok
        · cases ok

theorem Decodes.to_decode {p : Profile} {catalog : Catalog p} {roots : Roots} {s messages ancestors out}
    (h : Decodes p catalog roots s messages ancestors out) :
    decodeHistory p catalog roots s messages ancestors = some out := by
  induction h with
  | initial shape found => simp [decodeHistory, shape, found]
  | next prior phase previousPosition currentPosition nonce parsed ih =>
    cases phase
    simp [decodeHistory, previousPosition, currentPosition, nonce, ih, parsed]

theorem Decodes.size {p : Profile} {catalog : Catalog p} {roots : Roots} {s messages ancestors out}
    (h : Decodes p catalog roots s messages ancestors out) :
    out.replies.size = messages.length - 1 := by
  induction h with
  | initial => rfl
  | next prior phase previousPosition currentPosition nonce parsed ih =>
    obtain ⟨response,_,rfl⟩ := step_spec _ _ _ _ _ _ parsed
    simp only [Array.size_push, List.length_cons] at ih ⊢
    omega

theorem query_singleton (p : Profile) (s : Digest32) (m : Pending) :
    query p (s,[m]) = .initial := by
  simp [query, WHIRHistory.queryFor, WHIRHistory.schedule, visibleCoordinates]

theorem Decodes.phase_position {p : Profile} {catalog : Catalog p} {roots : Roots} {s messages ancestors out}
    (h : Decodes p catalog roots s messages ancestors out) :
    position (query p (s,messages)) = messages.length - 1 := by
  cases h with
  | initial =>
    simp [query_singleton, CausalProbability.position, visibleCoordinates]
  | next prior phase previousPosition currentPosition nonce parsed =>
    simpa using currentPosition

theorem Decodes.statement {p : Profile} {catalog : Catalog p} {roots : Roots}
    {s messages ancestors out} (h : Decodes p catalog roots s messages ancestors out) :
    catalog s = some out.statement := by
  induction h with
  | initial shape found => exact found
  | next prior phase previousPosition currentPosition nonce parsed ih =>
    obtain ⟨response,_,rfl⟩ := step_spec _ _ _ _ _ _ parsed
    exact ih

/-- Precisely the information relevant to an allocation before its answer is
sampled. The response at index `n` is deliberately not compared. -/
structure PrefixAgreement {p : Profile} (n : Nat) (before after : Replay p) : Prop where
  statement : before.statement = after.statement
  replies : ∀ i, i < n → before.replies[i]! = after.replies[i]!
  tape : ∀ q, position q < n → get q before.tape = get q after.tape

theorem PrefixAgreement.refl {p : Profile} (n : Nat) (r : Replay p) : PrefixAgreement n r r :=
  ⟨rfl,fun _ _ => rfl,fun _ _ => rfl⟩

theorem PrefixAgreement.mono {p : Profile} {m n : Nat} {before after : Replay p}
    (h : PrefixAgreement n before after) (le : m ≤ n) : PrefixAgreement m before after :=
  ⟨h.statement,fun i hi => h.replies i (lt_of_lt_of_le hi le),
    fun q hq => h.tape q (lt_of_lt_of_le hq le)⟩

theorem PrefixAgreement.trans {p : Profile} {n : Nat} {a b c : Replay p}
    (h : PrefixAgreement n a b) (k : PrefixAgreement n b c) : PrefixAgreement n a c :=
  ⟨h.statement.trans k.statement,fun i hi => (h.replies i hi).trans (k.replies i hi),
    fun q hq => (h.tape q hq).trans (k.tape q hq)⟩

theorem step_prefix {p : Profile} (roots : Roots) (before after : Replay p)
    (q : Coordinate (config p)) (x : Sample q) (pending : Pending)
    (ok : step roots before q x pending = some after)
    (size : before.replies.size = position q) :
    PrefixAgreement (position q) before after := by
  obtain ⟨response,_,rfl⟩ := step_spec _ _ _ _ _ _ ok
  refine ⟨rfl,?_,?_⟩
  · intro i hi
    have hb : i < before.replies.size := by omega
    have ha : i < (before.replies.push response).size := by simp; omega
    simp only [_root_.getElem!_pos before.replies i hb,
      _root_.getElem!_pos (before.replies.push response) i ha, Array.getElem_push_lt hb]
  · intro r hr
    have ne : r ≠ q := by intro he; subst r; omega
    exact (get_set_ne q r before.tape x ne).symm

/-- Dropping the same newest prefix from raw messages and completed ancestors
replays exactly an earlier state, agreeing on every strict-past response and
challenge. This is a theorem about the concrete decoder, not an input premise. -/
theorem Decodes.drop {p : Profile} {catalog : Catalog p} {roots : Roots} {s messages ancestors out}
    (h : Decodes p catalog roots s messages ancestors out) (i : Nat) (hi : i < messages.length) :
    ∃ before, Decodes p catalog roots s (messages.drop i) (ancestors.drop i) before ∧
      PrefixAgreement (messages.length - i - 1) before out := by
  induction h generalizing i with
  | initial shape found =>
    have hz : i = 0 := by simpa using hi
    subst i
    exact ⟨_,.initial shape found,.refl _ _⟩
  | @next m previous older past q x before out prior phase previousPosition currentPosition nonce parsed ih =>
    cases i with
    | zero =>
      exact ⟨_,.next prior phase previousPosition currentPosition nonce parsed,.refl _ _⟩
    | succ i =>
      obtain ⟨ancestor,ha,hp⟩ := ih i (by simpa using hi)
      have size : before.replies.size = position q := by
        rw [prior.size, previousPosition]
        simp
      have he := step_prefix roots before out q x m parsed size
      have hn : (previous::older).length - i - 1 ≤ position q := by
        simp only [List.length_cons, previousPosition]
        omega
      have result := hp.trans (he.mono hn)
      have eqn : (m::previous::older).length - (i+1) - 1 =
          (previous::older).length - i - 1 := by simp only [List.length_cons]; omega
      exact ⟨ancestor,by simpa only [List.drop_succ_cons] using ha,by simpa only [eqn] using result⟩

/-- Every ancestor value is literally the corresponding coordinate of the
decoded tape, and its coordinate is strictly earlier than the current one. -/
theorem Decodes.samples {p : Profile} {catalog : Catalog p} {roots : Roots} {s messages ancestors out}
    (h : Decodes p catalog roots s messages ancestors out) :
    ∀ entry ∈ ancestors,
      position entry.2.1 < position (query p (s,messages)) ∧
        get entry.2.1 out.tape = entry.2.2 := by
  induction h with
  | initial =>
    intro entry member
    cases member
  | @next m previous older past q x before out prior phase previousPosition currentPosition nonce parsed ih =>
    obtain ⟨response,_,rfl⟩ := step_spec _ _ _ _ _ _ parsed
    intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨by simpa only [currentPosition, previousPosition] using Nat.lt_succ_self older.length,
        get_set q before.tape x⟩
    · obtain ⟨earlier,value⟩ := ih entry member
      rw [← phase] at earlier
      have ne : entry.2.1 ≠ q := by intro he; rw [he] at earlier; omega
      refine ⟨?_,?_⟩
      · rw [currentPosition]
        rw [previousPosition] at earlier
        omega
      · simpa only [get_set_ne q _ _ _ ne] using value

/-- Explicit final completion installs the terminal sampled vector. It does not
invoke an adversarial continuation, including at the hidden last tail. -/
def finish {p : Profile} (key : Key p) (r : Replay p)
    (x : Sample (query p (key.statement,key.messages))) : Replay p :=
  {r with tape := set (query p (key.statement,key.messages)) r.tape x}

theorem finish_prefix {p : Profile} (key : Key p) (r : Replay p)
    (x : Sample (query p (key.statement,key.messages))) :
    PrefixAgreement (position (query p (key.statement,key.messages))) r (finish key r x) := by
  refine ⟨rfl,fun _ _ => rfl,?_⟩
  intro q hq
  have ne : q ≠ query p (key.statement,key.messages) := by intro he; subst q; omega
  exact (get_set_ne _ _ _ _ ne).symm

theorem decode_prefix {p : Profile} (catalog : Catalog p) (roots : Roots) (key : Key p)
    (out : Replay p) (ok : decode p catalog roots key = some out)
    (i : Nat) (hi : i < key.messages.length) :
    ∃ before, decode p catalog roots ⟨key.statement,key.messages.drop i,key.ancestors.drop i⟩ =
        some before ∧
      PrefixAgreement (position (query p (key.statement,key.messages.drop i))) before out := by
  obtain ⟨before,hb,hp⟩ := (decodeHistory_decodes p catalog roots _ _ _ out ok).drop i hi
  refine ⟨before,hb.to_decode,?_⟩
  rw [hb.phase_position, List.length_drop]
  exact hp

/-- Installing the final invisible sample preserves all recorded ancestors. -/
theorem finish_samples {p : Profile} (catalog : Catalog p) (roots : Roots) (key : Key p)
    (out : Replay p) (ok : decode p catalog roots key = some out)
    (x : Sample (query p (key.statement,key.messages))) :
    (get (query p (key.statement,key.messages)) (finish key out x).tape = x) ∧
    ∀ entry ∈ key.ancestors, get entry.2.1 (finish key out x).tape = entry.2.2 := by
  refine ⟨get_set _ _ _,?_⟩
  intro entry member
  obtain ⟨earlier,value⟩ := (decodeHistory_decodes p catalog roots _ _ _ out ok).samples entry member
  have ne : entry.2.1 ≠ query p (key.statement,key.messages) := by
    intro he
    rw [he] at earlier
    omega
  simpa only [finish, get_set_ne _ _ _ _ ne] using value

theorem decode_prefix_finish {p : Profile} (catalog : Catalog p) (roots : Roots) (key : Key p)
    (out : Replay p) (ok : decode p catalog roots key = some out) (x : Answer p key)
    (i : Nat) (hi : i < key.messages.length) :
    ∃ before, decode p catalog roots ⟨key.statement,key.messages.drop i,key.ancestors.drop i⟩ =
        some before ∧
      PrefixAgreement (position (query p (key.statement,key.messages.drop i))) before
        (finish key out x) := by
  obtain ⟨before,hb,hp⟩ := decode_prefix catalog roots key out ok i hi
  refine ⟨before,hb,hp.trans ((finish_prefix key out x).mono ?_)⟩
  have hpos := (decodeHistory_decodes p catalog roots _ _ _ out ok).phase_position
  have bpos := (decodeHistory_decodes p catalog roots _ _ _ before hb).phase_position
  rw [bpos,hpos,List.length_drop]
  omega

/-- The compiler's recorded-history theorem and the concrete decoder jointly
realize each allocated final-path key as the strict prefix of one actual
terminal replay. No parser-correctness or cover certificate is assumed. -/
theorem trace_realization {p : Profile} (catalog : Catalog p) (roots : Roots)
    (key : Key p) (out : Replay p) (ok : decode p catalog roots key = some out)
    (x : Answer p key) (head : Pending) (trace : List (Sigma (Answer p)))
    (recorded : TypedOracleCompiler.HistoryRecorded (query p) key.statement trace key.messages
      ((head,⟨query p (key.statement,key.messages),x⟩)::key.ancestors))
    (i : Nat) (hi : i < key.messages.length) :
    ∃ m tail past, ∃ a : Sample (query p (key.statement,m::tail)), ∃ before : Replay p,
      key.messages.drop i = m::tail ∧
      (⟨⟨key.statement,m::tail,past⟩,a⟩ : Sigma (Answer p)) ∈ trace ∧
      decode p catalog roots ⟨key.statement,m::tail,past⟩ = some before ∧
      PrefixAgreement (position (query p (key.statement,m::tail))) before (finish key out x) ∧
      get (query p (key.statement,m::tail)) (finish key out x).tape = a ∧
      position (query p (key.statement,m::tail)) = key.messages.length - i - 1 := by
  obtain ⟨m,tail,past,a,hm,hh,allocated⟩ := TypedOracleCompiler.HistoryRecorded.at_index
    (query p) recorded i hi
  obtain ⟨before,hb,hp⟩ := decode_prefix_finish catalog roots key out ok x i hi
  have ha : key.ancestors.drop i = past := by
    have ht := congrArg List.tail hh
    simpa only [List.tail_drop,List.drop_succ_cons,List.tail_cons] using ht
  have parsed : decode p catalog roots ⟨key.statement,m::tail,past⟩ = some before := by
    simpa only [hm,ha] using hb
  have agree : PrefixAgreement (position (query p (key.statement,m::tail))) before
      (finish key out x) := by simpa only [hm] using hp
  have sample : get (query p (key.statement,m::tail)) (finish key out x).tape = a := by
    have member : (m,(⟨query p (key.statement,m::tail),a⟩ : Sigma Sample)) ∈
        (head,⟨query p (key.statement,key.messages),x⟩)::key.ancestors :=
      List.mem_of_mem_drop (by rw [hh]; exact List.mem_cons_self)
    rcases List.mem_cons.mp member with same | older
    · have hs := congrArg Prod.snd same
      have result := (finish_samples catalog roots key out ok x).1
      exact Eq.mp (congrArg (fun qa : Sigma Sample =>
        get qa.1 (finish key out x).tape = qa.2) hs.symm) result
    · exact (finish_samples catalog roots key out ok x).2 _ older
  have pos := (decodeHistory_decodes p catalog roots _ _ _ before parsed).phase_position
  have len := congrArg List.length hm
  rw [List.length_drop] at len
  refine ⟨m,tail,past,a,before,hm,allocated,parsed,agree,sample,?_⟩
  rw [pos,← len]

end Whir.WHIRReplay
