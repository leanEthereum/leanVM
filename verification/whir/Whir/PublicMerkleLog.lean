import Whir.DuplexModeGame
import Whir.MerkleTransport

/-! Ordinary BLAKE2s provenance recovered exclusively from public compression
records. No hidden oracle table or caller-declared hash event is consulted.
The resource bound and the 56-bit domain separation bound are distinct. -/
namespace Whir.PublicMerkleLog
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open MerkleTransport.Commitments

abbrev PublicLog := List (Node × Digest32)

instance : DecidableEq Node := fun a b =>
  if h : a.cv = b.cv ∧ a.block = b.block ∧ a.tweak = b.tweak ∧ a.last = b.last then
    isTrue (by cases a; cases b; simp_all)
  else isFalse (by intro e; exact h (by simp [e]))

def AuthenticLog (C : PrimitiveOracle) (log : PublicLog) : Prop :=
  ∀ n d, (n,d) ∈ log → C n = d

/-- The first public answer is retained even for an inconsistent repeated query. -/
def lookup (log : PublicLog) (n : Node) : Option Digest32 :=
  match log with
  | [] => none
  | (m,d) :: rest => if n = m then some d else lookup rest n

def insert (log : PublicLog) (n : Node) (d : Digest32) : PublicLog :=
  if (lookup log n).isSome then log else log ++ [(n,d)]

/-- One final chunk, including the empty chunk for an empty input. -/
def chunks (bytes : List Byte) : List (List Byte) :=
  if bytes.length ≤ 64 then [bytes]
  else bytes.take 64 :: chunks (bytes.drop 64)
termination_by bytes.length
 decreasing_by simp; omega

/-- Concrete ordinary nodes; counters count real bytes, not padded bytes. -/
def node (cv : Digest32) (count : Nat) (bytes : List Byte) (last : Bool) : Node :=
  ⟨cv, padded bytes.toArray, UInt64.ofNat (count + bytes.length), last⟩

/-- A public-query interpreter. Its optional oracle makes absence explicit. -/
def run (query : Node → Option Digest32) (cv : Digest32) (count : Nat) :
    List (List Byte) → Option Digest32
  | [] => none
  | [b] => query (node cv count b true)
  | b :: next :: rest => do
      let d ← query (node cv count b false)
      run query d (count + b.length) (next :: rest)

def hash (C : PrimitiveOracle) (bytes : List Byte) : Digest32 :=
  (run (fun n => some (C n)) DuplexCompression.parameterIV 0 (chunks bytes)).getD
    DuplexCompression.parameterIV

def hashBlake2s : List Byte → Digest32 := hash blake2sOracle

/-- The exact public compression plan of the ordinary computation. -/
def planFrom (C : PrimitiveOracle) (cv : Digest32) (count : Nat) :
    List (List Byte) → PublicLog
  | [] => []
  | [b] => let n := node cv count b true; [(n,C n)]
  | b :: next :: rest =>
      let n := node cv count b false
      (n,C n) :: planFrom C (C n) (count + b.length) (next :: rest)

def plan (C : PrimitiveOracle) (bytes : List Byte) : PublicLog :=
  planFrom C DuplexCompression.parameterIV 0 (chunks bytes)

/-- Only a full output-CV match and the exact ordinary counter are accepted. -/
def predecessor (log : PublicLog) (count : Nat) (cv : Digest32) : Option Node :=
  match log with
  | [] => none
  | (n,d) :: rest =>
      if d = cv ∧ n.tweak.toNat = count ∧ n.last = false then some n
      else predecessor rest count cv

/-- Fuel prevents a malicious huge counter from allocating or scanning huge
amounts of data. Every successful link contributes exactly 64 bytes. -/
def recover (log : PublicLog) : Nat → Nat → Digest32 → Option (List Byte)
  | 0, _, _ => none
  | fuel + 1, count, cv =>
      if count = 0 then
        if cv = DuplexCompression.parameterIV then some [] else none
      else if count % 64 = 0 then do
        let n ← predecessor log count cv
        let prior ← recover log fuel (count - 64) n.cv
        return prior ++ List.ofFn n.block
      else none

def finalLength (count : Nat) : Nat :=
  if count = 0 then 0 else (count - 1) % 64 + 1

/-- Reconstruct then replay against the *public* answers. Replay checks all
padding, chaining, counters, and final flags without evaluating private C. -/
def parse (log : PublicLog) (n : Node) (answer : Digest32) : Option (List Byte) := do
  if n.last != true then none else do
    let size := finalLength n.tweak.toNat
    let prior ← recover log (log.length + 1) (n.tweak.toNat - size) n.cv
    let bytes := prior ++ (List.ofFn n.block).take size
    if run (lookup log) DuplexCompression.parameterIV 0 (chunks bytes) = some answer
      then some bytes else none

/-- Completed records discovered by this public observation. Scanning all
finals also handles a final query appearing before its predecessor queries. -/
def records (log : PublicLog) : Records :=
  log.filterMap fun (n,d) => (parse log n d).map fun bytes => (bytes,d)

def observe (log : PublicLog) (n : Node) (answer : Digest32) : PublicLog × Records :=
  let updated := insert log n answer
  (updated, records updated)

 theorem lookup_mem {log : PublicLog} {n : Node} {d : Digest32}
    (h : lookup log n = some d) : (n,d) ∈ log := by
  induction log with
  | nil => simp [lookup] at h
  | cons entry rest ih =>
    rcases entry with ⟨m,e⟩
    by_cases he : n = m
    · simp [lookup,he] at h
      simp [he,h]
    · simp [lookup,he] at h
      exact List.mem_cons_of_mem _ (ih h)

 theorem run_authentic (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (bs : List (List Byte)) (cv : Digest32) (count : Nat)
    (d : Digest32) (h : run (lookup log) cv count bs = some d) :
    run (fun n => some (C n)) cv count bs = some d := by
  induction bs generalizing cv count with
  | nil => simp [run] at h
  | cons b rest ih =>
    cases rest with
    | nil =>
      simp only [run] at h ⊢
      rw [auth _ _ (lookup_mem h)]
    | cons next rest =>
      simp only [run, Option.bind_eq_bind] at h ⊢
      cases he : lookup log (node cv count b false) with
      | none => simp [he] at h
      | some e =>
        have hc := auth _ _ (lookup_mem he)
        simp only [he, Option.bind_some] at h
        simp only [hc, Option.bind_some]
        exact ih e (count + b.length) h

 theorem parse_authentic (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (n : Node) (d : Digest32) (bytes : List Byte)
    (h : parse log n d = some bytes) : hash C bytes = d := by
  unfold parse at h
  split at h
  · simp at h
  · cases hr : recover log (log.length + 1)
        (n.tweak.toNat - finalLength n.tweak.toNat) n.cv with
    | none => simp [hr] at h
    | some prior =>
      simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      next he =>
        have hb := Option.some.inj h
        subst bytes
        have hh := run_authentic C log auth _ _ _ _ he
        exact congrArg (fun x => x.getD DuplexCompression.parameterIV) hh
      next => simp at h

 theorem records_authentic (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) : Authentic (hash C) (records log) := by
  intro bytes d hm
  obtain ⟨⟨n,e⟩, _, he⟩ := List.mem_filterMap.mp hm
  cases hp : parse log n e with
  | none => simp [hp] at he
  | some bs =>
    simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩
    exact parse_authentic C log auth n e bs hp

 theorem insert_authentic (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (n : Node) :
    AuthenticLog C (insert log n (C n)) := by
  intro m d hm
  unfold insert at hm
  split at hm
  · exact auth m d hm
  · simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | hm
    · exact auth m d hm
    · cases hm; rfl

 theorem observe_authentic (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (n : Node) :
    Authentic (hash C) (observe log n (C n)).2 :=
  records_authentic C _ (insert_authentic C log auth n)

/-- A literal ordinary primitive collision, not a cryptographic assumption. -/
def Collision (C : PrimitiveOracle) : Prop :=
  ∃ a b : Node, a ≠ b ∧ C a = C b

def OutputCollision (log : PublicLog) : Prop :=
  ∃ a b d, (a,d) ∈ log ∧ (b,d) ∈ log ∧ a ≠ b

theorem outputCollision_primitive (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (h : OutputCollision log) : Collision C := by
  obtain ⟨a,b,d,ha,hb,hne⟩ := h
  exact ⟨a,b,hne,(auth a d ha).trans (auth b d hb).symm⟩

theorem predecessor_spec {log : PublicLog} {count : Nat} {cv : Digest32} {n : Node}
    (h : predecessor log count cv = some n) :
    (n,cv) ∈ log ∧ n.tweak.toNat = count ∧ n.last = false := by
  induction log with
  | nil => simp [predecessor] at h
  | cons entry rest ih =>
    rcases entry with ⟨m,d⟩
    simp only [predecessor] at h
    split at h
    next he =>
      cases Option.some.inj h
      exact ⟨by simp [he.1],he.2⟩
    next =>
      obtain ⟨hm,ht,hl⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hm,ht,hl⟩

theorem predecessor_exists {log : PublicLog} {count : Nat} {cv : Digest32} {n : Node}
    (hm : (n,cv) ∈ log) (ht : n.tweak.toNat = count) (hl : n.last = false) :
    ∃ m, predecessor log count cv = some m := by
  induction log with
  | nil => simp at hm
  | cons entry rest ih =>
    rcases entry with ⟨m,d⟩
    by_cases he : d = cv ∧ m.tweak.toNat = count ∧ m.last = false
    · exact ⟨m,by rw [predecessor,ite_eq_left he]⟩
    · have hm' : (n,cv) ∈ rest := by
        rcases List.mem_cons.mp hm with eq | mem
        · cases eq
          exact False.elim (he ⟨rfl,ht,hl⟩)
        · exact mem
      obtain ⟨p,hp⟩ := ih hm'
      exact ⟨p,by simp only [predecessor,he,↓reduceIte,hp]⟩

/-- A finite, full-CV-linked ordinary prefix trace, made solely of actual
public records. Its index is the number of nonfinal compression queries.
Counters are natural byte counts, so wrapped counter traces are excluded. -/
inductive Prefix (log : PublicLog) : Nat → Nat → Digest32 → List Byte → Prop
  | seed : Prefix log 0 0 DuplexCompression.parameterIV []
  | step {k count cv bytes} (n : Node) :
      Prefix log k (count - 64) n.cv bytes →
      0 < count → count % 64 = 0 →
      n.tweak.toNat = count → n.last = false → (n,cv) ∈ log →
      Prefix log (k+1) count cv (bytes ++ List.ofFn n.block)

theorem recover_complete_or_collision {log : PublicLog} {k count : Nat}
    {cv : Digest32} {bytes : List Byte} (trace : Prefix log k count cv bytes)
    (fuel : Nat) (enough : k < fuel) :
    recover log fuel count cv = some bytes ∨ OutputCollision log := by
  induction trace generalizing fuel with
  | seed =>
    cases fuel with
    | zero => omega
    | succ fuel => exact Or.inl (by simp only [recover,↓reduceIte])
  | @step k count cv bytes n prior pos multiple ht hl hm ih =>
    obtain ⟨m,hfind⟩ := predecessor_exists hm ht hl
    obtain ⟨hmem,_,_⟩ := predecessor_spec hfind
    by_cases he : m = n
    · subst m
      cases fuel with
      | zero => omega
      | succ fuel =>
        rcases ih fuel (by omega) with hr | hc
        · left
          simp only [recover,show count ≠ 0 by omega,multiple,↓reduceIte,
            hfind,Option.bind_eq_bind,Option.bind_some,hr,Option.pure_def]
        · exact Or.inr hc
    · exact Or.inr ⟨m,n,cv,hmem,hm,he⟩

theorem prefix_length {log : PublicLog} {k count : Nat} {cv : Digest32}
    {bytes : List Byte} (trace : Prefix log k count cv bytes) :
    bytes.length = 64*k ∧ count = 64*k := by
  induction trace with
  | seed => simp
  | @step k count cv bytes n prior pos multiple ht hl hm ih =>
    have hc : 64 ≤ count := Nat.le_of_dvd pos (Nat.dvd_of_mod_eq_zero multiple)
    simp only [List.length_append,List.length_ofFn]
    constructor <;> omega

/-- A completed ordinary computation in the public query interpreter.
`Prefix` records all actual predecessor inputs and answers; `replayed`
records the final public compression answer as well. These are trace facts,
not self-reported high-level hash events. -/
structure Completed (log : PublicLog) (n : Node) (answer : Digest32)
    (bytes : List Byte) where
  member : (n,answer) ∈ log
  finalFlag : n.last = true
  depth : Nat
  prior : List Byte
  trace : Prefix log depth (n.tweak.toNat - finalLength n.tweak.toNat) n.cv prior
  message : bytes = prior ++ (List.ofFn n.block).take (finalLength n.tweak.toNat)
  replayed : run (lookup log) DuplexCompression.parameterIV 0 (chunks bytes) = some answer

theorem parse_complete_or_collision {log : PublicLog} {n : Node} {answer : Digest32}
    {bytes : List Byte} (trace : Completed log n answer bytes)
    (enough : trace.depth ≤ log.length) :
    parse log n answer = some bytes ∨ OutputCollision log := by
  rcases recover_complete_or_collision trace.trace (log.length + 1) (by omega) with hr | hc
  · left
    simp only [parse,trace.finalFlag,show (true != true) = false from rfl,
      Bool.false_eq_true,↓reduceIte,hr,Option.bind_eq_bind,Option.bind_some]
    rw [← trace.message]
    simp only [trace.replayed,↓reduceIte]
  · exact Or.inr hc

theorem parse_complete_or_primitive_collision (C : PrimitiveOracle)
    {log : PublicLog} (auth : AuthenticLog C log) {n : Node} {answer : Digest32}
    {bytes : List Byte} (trace : Completed log n answer bytes)
    (enough : trace.depth ≤ log.length) :
    parse log n answer = some bytes ∨ Collision C :=
  (parse_complete_or_collision trace enough).imp id (outputCollision_primitive C log auth)

theorem parse_complete {log : PublicLog} (noCollision : ¬ OutputCollision log)
    {n : Node} {answer : Digest32} {bytes : List Byte}
    (trace : Completed log n answer bytes) (enough : trace.depth ≤ log.length) :
    parse log n answer = some bytes :=
  (parse_complete_or_collision trace enough).resolve_right noCollision

theorem records_complete {log : PublicLog} (noCollision : ¬ OutputCollision log)
    {n : Node} {answer : Digest32} {bytes : List Byte}
    (trace : Completed log n answer bytes) (enough : trace.depth ≤ log.length) :
    (bytes,answer) ∈ records log := by
  apply List.mem_filterMap.mpr
  exact ⟨(n,answer),trace.member,by
    simp only [parse_complete noCollision trace enough,Option.map_some]⟩

theorem lookup_exists {log : PublicLog} {n : Node} {d : Digest32}
    (hm : (n,d) ∈ log) : ∃ e, lookup log n = some e := by
  induction log with
  | nil => simp at hm
  | cons entry rest ih =>
    rcases entry with ⟨m,e⟩
    by_cases he : n = m
    · exact ⟨e,by simp only [lookup,he,↓reduceIte]⟩
    · have ht : (n,d) ∈ rest := by
        simpa only [List.mem_cons,Prod.mk.injEq,he,false_and,false_or] using hm
      obtain ⟨v,hv⟩ := ih ht
      exact ⟨v,by simp only [lookup,he,↓reduceIte,hv]⟩

theorem lookup_authentic_member (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) {n : Node} {d : Digest32} (hm : (n,d) ∈ log) :
    lookup log n = some (C n) := by
  obtain ⟨e,he⟩ := lookup_exists hm
  rw [he,auth n e (lookup_mem he)]

theorem run_plan (C : PrimitiveOracle) (log : PublicLog) (auth : AuthenticLog C log)
    (bs : List (List Byte)) (cv : Digest32) (count : Nat)
    (present : ∀ e ∈ planFrom C cv count bs, e ∈ log) :
    run (lookup log) cv count bs = run (fun n => some (C n)) cv count bs := by
  induction bs generalizing cv count with
  | nil => rfl
  | cons b rest ih =>
    cases rest with
    | nil =>
      exact lookup_authentic_member C log auth
        (present (node cv count b true,C (node cv count b true)) (by simp only [planFrom,List.mem_singleton]))
    | cons next rest =>
      have hm := present _ (List.mem_cons_self :
        (node cv count b false,C (node cv count b false)) ∈
          planFrom C cv count (b :: next :: rest))
      simp only [run,lookup_authentic_member C log auth hm,
        Option.bind_eq_bind,Option.bind_some]
      apply ih
      intro e he
      exact present e (List.mem_cons_of_mem _ he)

theorem run_nonempty (C : PrimitiveOracle) (bs : List (List Byte))
    (hne : bs ≠ []) (cv : Digest32) (count : Nat) :
    ∃ d, run (fun n => some (C n)) cv count bs = some d := by
  induction bs generalizing cv count with
  | nil => contradiction
  | cons b rest ih =>
    cases rest with
    | nil => exact ⟨_,rfl⟩
    | cons next rest =>
      simpa only [run,Option.bind_eq_bind,Option.bind_some] using
        ih (by simp) (C (node cv count b false)) (count + b.length)

theorem chunks_nonempty (bytes : List Byte) : chunks bytes ≠ [] := by
  rw [chunks]
  split <;> simp

theorem hash_replay (C : PrimitiveOracle) (log : PublicLog) (auth : AuthenticLog C log)
    (bytes : List Byte) (present : ∀ e ∈ plan C bytes, e ∈ log) :
    run (lookup log) DuplexCompression.parameterIV 0 (chunks bytes) = some (hash C bytes) := by
  rw [run_plan C log auth _ _ _ present]
  obtain ⟨d,hd⟩ := run_nonempty C (chunks bytes) (chunks_nonempty bytes)
    DuplexCompression.parameterIV 0
  unfold hash
  rw [hd]
  rfl

theorem padded_take (bytes : List Byte) (h : bytes.length ≤ 64) :
    (List.ofFn (padded bytes.toArray)).take bytes.length = bytes := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_ofFn,Nat.min_eq_left h]
  · intro i hi hj
    simp only [List.getElem_take,List.getElem_ofFn,padded]
    simp [List.getElem_toArray,show i < bytes.length from hj]

theorem padded_full (bytes : List Byte) (h : bytes.length = 64) :
    List.ofFn (padded bytes.toArray) = bytes := by
  have hp := padded_take bytes (by omega)
  simpa only [h,List.take_of_length_le (by simp : (List.ofFn (padded bytes.toArray)).length ≤ 64)] using hp

theorem finalLength_bounds (n : Nat) : finalLength n ≤ 64 ∧ finalLength n ≤ n := by
  unfold finalLength
  split <;> omega

theorem finalLength_block (k r : Nat) (hr : r ≤ 64) (positive : 0 < r ∨ k = 0) :
    finalLength (64*k+r) = r := by
  unfold finalLength
  have hm : (64*k+r-1) % 64 = (r-1) % 64 := by omega
  split <;> omega

theorem recover_bound {log : PublicLog} {fuel count : Nat} {cv : Digest32}
    {bytes : List Byte} (h : recover log fuel count cv = some bytes) :
    bytes.length ≤ 64 * fuel := by
  induction fuel generalizing count cv bytes with
  | zero => simp [recover] at h
  | succ fuel ih =>
    simp only [recover] at h
    split at h
    · split at h
      · cases Option.some.inj h; simp
      · simp at h
    · split at h
      · cases hp : predecessor log count cv with
        | none => simp [hp] at h
        | some n =>
          simp only [hp,Option.bind_eq_bind,Option.bind_some] at h
          cases hr : recover log fuel (count-64) n.cv with
          | none => simp [hr] at h
          | some bs =>
            simp only [hr,Option.bind_some,Option.pure_def,Option.some.injEq] at h
            subst bytes
            have hh := ih hr
            simp only [List.length_append,List.length_ofFn]
            omega
      · simp at h

theorem parse_resource_bound {log : PublicLog} {n : Node} {d : Digest32}
    {bytes : List Byte} (h : parse log n d = some bytes) :
    bytes.length ≤ 64 * (log.length + 2) := by
  unfold parse at h
  split at h
  · simp at h
  · cases hr : recover log (log.length+1) (n.tweak.toNat-finalLength n.tweak.toNat) n.cv with
    | none => simp [hr] at h
    | some bs =>
      simp only [hr,Option.bind_eq_bind,Option.bind_some] at h
      split at h
      · cases Option.some.inj h
        have hb := recover_bound hr
        have hl := (finalLength_bounds n.tweak.toNat).1
        simp only [List.length_append,List.length_take,List.length_ofFn]
        omega
      · simp at h

/-- This is a conditional #552 tag separation statement, not a statement
about baseline interactive code or a cryptographic collision probability. -/
theorem ordinary_tag_zero (cv : Digest32) (count : Nat) (bytes : List Byte) (last : Bool)
    (bound : count + bytes.length < 2^56) : tag (node cv count bytes last) = 0 := by
  have h64 : count + bytes.length < 2^64 := by omega
  simp only [tag,node,UInt64.toNat_ofNat',Nat.mod_eq_of_lt h64]
  exact Nat.div_eq_of_lt bound

theorem ordinary_ne_duplex (cv : Digest32) (count : Nat) (bytes : List Byte)
    (last : Bool) (bound : count + bytes.length < 2^56) (mode : Node)
    (modeTag : 1 ≤ tag mode) : node cv count bytes last ≠ mode := by
  intro he
  have hz := ordinary_tag_zero cv count bytes last bound
  rw [he] at hz
  omega

theorem insert_preserves_first (log : PublicLog) (n : Node) (d first : Digest32)
    (h : lookup log n = some first) : insert log n d = log := by
  simp only [insert,h,Option.isSome_some,↓reduceIte]

/-- Every real plan has a reverse-linked trace; no reverse trace is assumed
by the end-to-end completeness theorem below. -/
theorem plan_shape (C : PrimitiveOracle) (log : PublicLog) (bytes : List Byte)
    (cv : Digest32) (k : Nat) (prior : List Byte)
    (prefixTrace : Prefix log k (64*k) cv prior)
    (bound : 64*k + bytes.length < 2^64)
    (positive : 0 < bytes.length ∨ k = 0)
    (present : ∀ e ∈ planFrom C cv (64*k) (chunks bytes), e ∈ log) :
    ∃ n d depth pre, (n,d) ∈ log ∧ n.last = true ∧
      Prefix log depth (n.tweak.toNat - finalLength n.tweak.toNat) n.cv pre ∧
      prior ++ bytes = pre ++ (List.ofFn n.block).take (finalLength n.tweak.toNat) ∧
      run (fun n => some (C n)) cv (64*k) (chunks bytes) = some d := by
  by_cases short : bytes.length ≤ 64
  · let n := node cv (64*k) bytes true
    have ht : n.tweak.toNat = 64*k + bytes.length := by
      simp only [n,node,UInt64.toNat_ofNat',Nat.mod_eq_of_lt bound]
    have hf : finalLength n.tweak.toNat = bytes.length := by
      rw [ht]; exact finalLength_block k bytes.length short positive
    have hc : n.tweak.toNat - finalLength n.tweak.toNat = 64*k := by
      rw [hf,ht]; omega
    refine ⟨n,C n,k,prior,?_,rfl,?_,?_,?_⟩
    · apply present
      simp only [chunks,short,↓reduceIte,planFrom,List.mem_singleton]
      rfl
    · rw [hc]; exact prefixTrace
    · rw [hf]
      exact congrArg (prior ++ ·) (padded_take bytes short).symm
    · simp only [chunks,short,↓reduceIte,run]
      rfl
  · have full : (bytes.take 64).length = 64 := by simp only [List.length_take]; omega
    let n := node cv (64*k) (bytes.take 64) false
    have ht : n.tweak.toNat = 64*(k+1) := by
      have hb : 64*k + (bytes.take 64).length < 2^64 := by omega
      simp only [n,node,UInt64.toNat_ofNat',full]
      omega
    have hm : (n,C n) ∈ log := by
      apply present
      rw [chunks,ite_eq_right short]
      have hne := chunks_nonempty (bytes.drop 64)
      cases he : chunks (bytes.drop 64) with
      | nil => contradiction
      | cons next rest => exact List.mem_cons_self
    have hp : Prefix log (k+1) (64*(k+1)) (C n) (prior ++ bytes.take 64) := by
      have hstep := Prefix.step n (count := 64*(k+1))
        (by simpa only [show 64*(k+1)-64 = 64*k by omega,n,node] using prefixTrace)
        (by omega) (by omega) ht rfl hm
      simpa only [n,node,padded_full (bytes.take 64) full] using hstep
    have present' : ∀ e ∈ planFrom C (C n) (64*(k+1)) (chunks (bytes.drop 64)), e ∈ log := by
      intro e he
      apply present
      rw [chunks,ite_eq_right short]
      cases hbs : chunks (bytes.drop 64) with
      | nil => simp only [hbs,planFrom,List.not_mem_nil] at he
      | cons next rest =>
        simp only [planFrom]
        apply List.mem_cons_of_mem
        simpa only [hbs,show 64*k+(bytes.take 64).length = 64*(k+1) by omega] using he
    obtain ⟨last,d,depth,pre,hmLast,hflag,htrace,hmessage,hrun⟩ :=
      plan_shape C log (bytes.drop 64) (C n) (k+1) (prior ++ bytes.take 64) hp
        (by simp only [List.length_drop]; omega)
        (Or.inl (by simp only [List.length_drop]; omega)) present'
    refine ⟨last,d,depth,pre,hmLast,hflag,htrace,?_,?_⟩
    · simpa only [List.append_assoc,List.take_append_drop] using hmessage
    · rw [chunks,ite_eq_right short]
      cases hbs : chunks (bytes.drop 64) with
      | nil => exact False.elim (chunks_nonempty (bytes.drop 64) hbs)
      | cons next rest =>
        simp only [run,Option.bind_eq_bind,Option.bind_some]
        simpa only [hbs,show 64*k+(bytes.take 64).length = 64*(k+1) by omega] using hrun
termination_by bytes.length
decreasing_by simp only [List.length_drop]; omega

theorem plan_completed (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (bytes : List Byte) (bound : bytes.length < 2^64)
    (present : ∀ e ∈ plan C bytes, e ∈ log) :
    ∃ n, Nonempty (Completed log n (hash C bytes) bytes) := by
  obtain ⟨n,d,depth,pre,hm,hflag,ht,he,hr⟩ :=
    plan_shape C log bytes DuplexCompression.parameterIV 0 [] Prefix.seed
      (by simpa using bound) (Or.inr rfl) present
  have hd : hash C bytes = d := by
    exact congrArg (fun x => x.getD DuplexCompression.parameterIV) hr
  refine ⟨n,⟨?_⟩⟩
  exact ⟨by simpa only [hd] using hm,hflag,depth,pre,ht,
    by simpa only [List.nil_append] using he,hash_replay C log auth bytes present⟩

theorem prefix_counter_present {log : PublicLog} {k count : Nat}
    {cv : Digest32} {bytes : List Byte} (trace : Prefix log k count cv bytes)
    (i : Nat) (hi : i < k) :
    ∃ n d, (n,d) ∈ log ∧ n.tweak.toNat = 64*(i+1) := by
  induction trace with
  | seed => omega
  | @step k count cv bytes n prior pos multiple ht hl hm ih =>
    by_cases he : i = k
    · subst i
      have hc := (prefix_length (Prefix.step n prior pos multiple ht hl hm)).2
      exact ⟨n,cv,hm,ht.trans hc⟩
    · exact ih (by omega)

theorem prefix_depth_bound {log : PublicLog} {k count : Nat}
    {cv : Digest32} {bytes : List Byte} (trace : Prefix log k count cv bytes) :
    k ≤ log.length := by
  let counters := log.map fun e => e.1.tweak.toNat / 64 - 1
  have hsub : Finset.range k ⊆ counters.toFinset := by
    intro i hi
    obtain ⟨n,d,hm,ht⟩ := prefix_counter_present trace i (Finset.mem_range.mp hi)
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    exact ⟨(n,d),hm,by dsimp; rw [ht]; omega⟩
  have hcard := (Finset.card_le_card hsub).trans counters.toFinset_card_le
  simpa only [Finset.card_range,counters,List.length_map] using hcard

/-- End-to-end completeness for arbitrary-length ordinary hashing: the only
alternative is two *distinct actual compression inputs* sharing a public
answer. The real-byte bound rules out UInt64 counter wraparound. -/
theorem plan_complete_or_collision (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (bytes : List Byte) (bound : bytes.length < 2^64)
    (present : ∀ e ∈ plan C bytes, e ∈ log) :
    (bytes,hash C bytes) ∈ records log ∨ Collision C := by
  obtain ⟨n,⟨trace⟩⟩ := plan_completed C log auth bytes bound present
  rcases parse_complete_or_collision trace (prefix_depth_bound trace.trace) with hp | hc
  · left
    exact List.mem_filterMap.mpr ⟨(n,hash C bytes),trace.member,by
      simp only [hp,Option.map_some]⟩
  · exact Or.inr (outputCollision_primitive C log auth hc)

theorem plan_complete (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (noCollision : ¬ OutputCollision log)
    (bytes : List Byte) (bound : bytes.length < 2^64)
    (present : ∀ e ∈ plan C bytes, e ∈ log) :
    (bytes,hash C bytes) ∈ records log := by
  obtain ⟨n,⟨trace⟩⟩ := plan_completed C log auth bytes bound present
  exact records_complete noCollision trace (prefix_depth_bound trace.trace)

theorem recover_byte_count {log : PublicLog} {fuel count : Nat} {cv : Digest32}
    {bytes : List Byte} (h : recover log fuel count cv = some bytes) :
    bytes.length = count := by
  induction fuel generalizing count cv bytes with
  | zero => simp [recover] at h
  | succ fuel ih =>
    simp only [recover] at h
    split at h
    next hz =>
      split at h
      · cases Option.some.inj h; simpa only [List.length_nil] using hz.symm
      · simp at h
    next hn =>
      split at h
      next hm =>
        cases hp : predecessor log count cv with
        | none => simp [hp] at h
        | some n =>
          simp only [hp,Option.bind_eq_bind,Option.bind_some] at h
          cases hr : recover log fuel (count-64) n.cv with
          | none => simp [hr] at h
          | some bs =>
            simp only [hr,Option.bind_some,Option.pure_def,Option.some.injEq] at h
            subst bytes
            have hh := ih hr
            have hc : 64 ≤ count := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hm)
            simp only [List.length_append,List.length_ofFn]
            omega
      next => simp at h

theorem parse_byte_count {log : PublicLog} {n : Node} {d : Digest32}
    {bytes : List Byte} (h : parse log n d = some bytes) :
    bytes.length = n.tweak.toNat := by
  unfold parse at h
  split at h
  · simp at h
  · cases hr : recover log (log.length+1) (n.tweak.toNat-finalLength n.tweak.toNat) n.cv with
    | none => simp [hr] at h
    | some bs =>
      simp only [hr,Option.bind_eq_bind,Option.bind_some] at h
      split at h
      · cases Option.some.inj h
        have hb := recover_byte_count hr
        have hl := finalLength_bounds n.tweak.toNat
        simp only [List.length_append,List.length_take,List.length_ofFn]
        omega
      · simp at h

theorem chunks_flatten (bytes : List Byte) : (chunks bytes).flatten = bytes := by
  rw [chunks]
  split
  · simp only [List.flatten_cons,List.flatten_nil,List.append_nil]
  · rw [List.flatten_cons,chunks_flatten,List.take_append_drop]
termination_by bytes.length
decreasing_by simp only [List.length_drop]; omega

theorem planFrom_tag_zero (C : PrimitiveOracle) (cv : Digest32) (count : Nat)
    (bs : List (List Byte)) (bound : count + bs.flatten.length < 2^56)
    (n : Node) (d : Digest32) (hm : (n,d) ∈ planFrom C cv count bs) :
    tag n = 0 := by
  induction bs generalizing cv count with
  | nil => simp only [planFrom,List.not_mem_nil] at hm
  | cons b rest ih =>
    cases rest with
    | nil =>
      simp only [planFrom,List.mem_singleton,Prod.mk.injEq] at hm
      rw [hm.1]
      apply ordinary_tag_zero
      simpa only [List.flatten_cons,List.flatten_nil,List.append_nil] using bound
    | cons next rest =>
      simp only [planFrom,List.mem_cons,Prod.mk.injEq] at hm
      have hb : count + b.length + (next :: rest).flatten.length < 2^56 := by
        simpa only [List.flatten_cons,List.length_append,Nat.add_assoc] using bound
      rcases hm with ⟨he,_⟩ | hm
      · rw [he]
        apply ordinary_tag_zero
        omega
      · exact ih (C (node cv count b false)) (count + b.length) hb hm

theorem plan_tag_zero (C : PrimitiveOracle) (bytes : List Byte)
    (bound : bytes.length < 2^56) (n : Node) (d : Digest32)
    (hm : (n,d) ∈ plan C bytes) : tag n = 0 :=
  planFrom_tag_zero C DuplexCompression.parameterIV 0 (chunks bytes)
    (by simpa only [chunks_flatten,Nat.zero_add] using bound) n d hm

/-- RFC-style sequential-byte KATs, independently evaluated with Python's
standard hashlib BLAKE2s. Leaf bytes are 00..17; the Merkle pair hashes the
two 24-byte leaves 00..17 and 18..2f and concatenates their full digests. -/
def knownAnswerVectors : List (Nat × String) := [
  (0, "69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9"),
  (1, "e34d74dbaf4ff4c6abd871cc220451d2ea2648846c7757fbaac82fe51ad64bea"),
  (64, "56f34e8b96557e90c1f24b52d0c89d51086acf1b00f634cf1dde9233b8eaaa3e"),
  (65, "1b53ee94aaf34e4b159d48de352c7f0661d0a40edff95a0b1639b4090e974472"),
  (128, "1fa877de67259d19863a2a34bcc6962a2b25fcbf5cbecd7ede8f1fa36688a796"),
  (129, "5bd169e67c82c2c2e98ef7008bdf261f2ddf30b1c00f9e7f275bb3e8a28dc9a2")]

def sequentialBytes (start count : Nat) : List Byte :=
  (List.range count).map fun i => ⟨(start+i)%256,Nat.mod_lt _ (by decide)⟩

/-- Executable smoke, deliberately separate from checked theorem evidence. -/
def smoke : IO Unit := do
  for (size,expected) in knownAnswerVectors do
    let bytes := sequentialBytes 0 size
    let digest := hashBlake2s bytes
    let actual := DuplexCompression.hex (List.ofFn digest)
    unless actual == expected do
      throw (IO.userError s!"BLAKE2s KAT {size}: {actual} != {expected}")
    let trace := plan blake2sOracle bytes
    let mut log : PublicLog := []
    -- Final-first exposes why completion must also run on predecessor arrival.
    for (n,d) in trace.reverse do
      log := (observe log n d).1
    unless (recordLookup bytes (records log)) == some digest do
      throw (IO.userError s!"public reconstruction failed at {size}")
    IO.println s!"BLAKE2s-{size}: {actual}; final-first public replay OK"
  let left := hashBlake2s (sequentialBytes 0 24)
  let right := hashBlake2s (sequentialBytes 24 24)
  let pairBytes := List.ofFn left ++ List.ofFn right
  let pair := hashBlake2s pairBytes
  unless DuplexCompression.hex (List.ofFn left) ==
      "b2c2420f05f9abe36315919336b37e4e0fa33ff7e76a492767006fdb5d935462" do
    throw (IO.userError "Merkle leaf KAT failed")
  unless DuplexCompression.hex (List.ofFn pair) ==
      "7d89d5eaf3414032e779649edf3b3c60d7b34401a49bea6ae2826b065c95e914" do
    throw (IO.userError "Merkle pair KAT failed")
  unless recordLookup pairBytes (records (plan blake2sOracle pairBytes)) == some pair do
    throw (IO.userError "Merkle pair public reconstruction failed")
  let bytes := sequentialBytes 0 129
  let trace := plan blake2sOracle bytes
  match trace.reverse with
  | [] => throw (IO.userError "missing concrete plan")
  | (n,d) :: _ =>
    unless records [(n,d)] == [] do
      throw (IO.userError "incomplete prefix was accepted")
    let wrong : Digest32 := fun _ => 0
    unless lookup (insert [(n,d)] n wrong) n == some d do
      throw (IO.userError "first public answer was overwritten")
  IO.println "Merkle leaf/pair, missing-prefix rejection, first-answer retention: OK"

/-- Targets known at a frozen snapshot: a registered digest or the complete
CV field of a public compression input. In particular, a final digest that
was public before its predecessors is not treated as a fresh hash output. -/
def SnapshotTarget (oldLog : PublicLog) (target output : Digest32) : Prop :=
  output = target ∨ ∃ n answer, (n,answer) ∈ oldLog ∧ output = n.cv

def FreshTarget (C : PrimitiveOracle) (oldLog : PublicLog)
    (target : Digest32) (trace : PublicLog) : Prop :=
  ∃ n, (n,C n) ∈ trace ∧
    (∀ answer, (n,answer) ∉ oldLog) ∧ SnapshotTarget oldLog target (C n)

theorem planFrom_head (C : PrimitiveOracle) (cv : Digest32) (count : Nat)
    (bs : List (List Byte)) (hne : bs ≠ []) :
    ∃ n d, (n,d) ∈ planFrom C cv count bs ∧ n.cv = cv := by
  cases bs with
  | nil => contradiction
  | cons b rest =>
    cases rest with
    | nil => exact ⟨node cv count b true,_,List.mem_cons_self,rfl⟩
    | cons next rest => exact ⟨node cv count b false,_,List.mem_cons_self,rfl⟩

/-- Root-first cut through an actual forward plan. The last absent node
either produces the final target or links into an already public CV. -/
theorem planFrom_frozen_cut (C : PrimitiveOracle) (oldLog : PublicLog)
    (auth : AuthenticLog C oldLog) (bs : List (List Byte))
    (cv : Digest32) (count : Nat) (target : Digest32)
    (finished : run (fun n => some (C n)) cv count bs = some target) :
    (∀ e ∈ planFrom C cv count bs, e ∈ oldLog) ∨
      FreshTarget C oldLog target (planFrom C cv count bs) := by
  induction bs generalizing cv count with
  | nil => simp [run] at finished
  | cons b rest ih =>
    cases rest with
    | nil =>
      let n := node cv count b true
      have hout : C n = target := Option.some.inj finished
      by_cases seen : ∃ answer, (n,answer) ∈ oldLog
      · obtain ⟨answer,ha⟩ := seen
        left
        intro e he
        have he' : e = (n,C n) := List.mem_singleton.mp he
        rw [he',auth n answer ha]
        exact ha
      · right
        exact ⟨n,List.mem_cons_self,fun answer ha => seen ⟨answer,ha⟩,Or.inl hout⟩
    | cons next rest =>
      let n := node cv count b false
      have hr : run (fun n => some (C n)) (C n) (count+b.length) (next::rest) =
          some target := finished
      rcases ih (C n) (count+b.length) hr with tailPresent | tailFresh
      · by_cases seen : ∃ answer, (n,answer) ∈ oldLog
        · obtain ⟨answer,ha⟩ := seen
          left
          intro e he
          rcases List.mem_cons.mp he with he | he
          · rw [he,auth n answer ha]
            exact ha
          · exact tailPresent e he
        · right
          obtain ⟨nextNode,d,hm,hcv⟩ := planFrom_head C (C n) (count+b.length)
            (next::rest) (by simp)
          exact ⟨n,List.mem_cons_self,fun answer ha => seen ⟨answer,ha⟩,
            Or.inr ⟨nextNode,d,tailPresent _ hm,hcv.symm⟩⟩
      · right
        obtain ⟨missing,hm,ha,ht⟩ := tailFresh
        exact ⟨missing,List.mem_cons_of_mem _ hm,ha,ht⟩

theorem plan_complete_or_public_collision (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (bytes : List Byte) (bound : bytes.length < 2^64)
    (present : ∀ e ∈ plan C bytes, e ∈ log) :
    (bytes,hash C bytes) ∈ records log ∨ OutputCollision log := by
  obtain ⟨n,⟨trace⟩⟩ := plan_completed C log auth bytes bound present
  rcases parse_complete_or_collision trace (prefix_depth_bound trace.trace) with hp | hc
  · left
    exact List.mem_filterMap.mpr ⟨(n,hash C bytes),trace.member,by
      simp only [hp,Option.map_some]⟩
  · exact Or.inr hc

/-- Preserve the public witnesses when translating an output-log collision
to an ordinary primitive collision. No global injectivity is assumed. -/
theorem observedCollision_primitive (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (h : OutputCollision log) :
    ∃ a b d, (a,d) ∈ log ∧ (b,d) ∈ log ∧ a ≠ b ∧ C a = C b := by
  obtain ⟨a,b,d,ha,hb,hne⟩ := h
  exact ⟨a,b,d,ha,hb,hne,(auth a d ha).trans (auth b d hb).symm⟩

/-- Exact shared-C alternative at an arbitrary frozen public snapshot.
There is no independent fresh-whole-hash assumption. The absent input is
an actual node of the ordinary plan, and its output targets only the fixed
digest or a CV already recorded in `oldLog`. -/
theorem frozen_target_alternative (C : PrimitiveOracle) (oldLog : PublicLog)
    (auth : AuthenticLog C oldLog) (bytes : List Byte) (target : Digest32)
    (bound : bytes.length < 2^64) (hits : hash C bytes = target) :
    (bytes,target) ∈ records oldLog ∨ OutputCollision oldLog ∨
      FreshTarget C oldLog target (plan C bytes) := by
  obtain ⟨d,hd⟩ := run_nonempty C (chunks bytes) (chunks_nonempty bytes)
    DuplexCompression.parameterIV 0
  have he : d = target := by
    have hh : hash C bytes = d :=
      congrArg (fun x => x.getD DuplexCompression.parameterIV) hd
    exact hh.symm.trans hits
  rcases planFrom_frozen_cut C oldLog auth (chunks bytes)
      DuplexCompression.parameterIV 0 target (by simpa only [he] using hd) with present | fresh
  · rcases plan_complete_or_public_collision C oldLog auth bytes bound present with recorded | collision
    · exact Or.inl (by simpa only [hits] using recorded)
    · exact Or.inr (Or.inl collision)
  · exact Or.inr (Or.inr fresh)

theorem frozen_target_fresh (C : PrimitiveOracle) (oldLog : PublicLog)
    (auth : AuthenticLog C oldLog) (noCollision : ¬ OutputCollision oldLog)
    (bytes : List Byte) (target : Digest32) (bound : bytes.length < 2^64)
    (hits : hash C bytes = target) (absent : (bytes,target) ∉ records oldLog) :
    FreshTarget C oldLog target (plan C bytes) := by
  rcases frozen_target_alternative C oldLog auth bytes target bound hits with h | h | h
  · exact False.elim (absent h)
  · exact False.elim (noCollision h)
  · exact h

end Whir.PublicMerkleLog
