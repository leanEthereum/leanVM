import Whir.DuplexModeGame

/-! The deterministic, public-log part of radicalExtend. The private randomness
is a finite-domain fallback table, never a source of raw-query coordinates.
Output collisions choose the first matching public record. The stochastic DMV
coupling and its bad-event probability remain an external theorem. -/
namespace Whir.DuplexPublicSimulator
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame

abbrev PublicLog := List (Node × Digest32)
abbrev Seed := Node → Digest32

instance : DecidableEq Node := fun a b =>
  if h : (a.cv,a.block,a.tweak,a.last) = (b.cv,b.block,b.tweak,b.last) then
    isTrue (by cases a; cases b; simpa using h)
  else isFalse (fun e => h (by cases e; rfl))

/-- Newest record wins; every public primitive answer, including a repeated
input, is recorded. Construction answers are not primitive records. -/
def observe (log : PublicLog) (input : Node) (answer : Digest32) : PublicLog :=
  (input,answer) :: log

def lookup (log : PublicLog) (input : Node) : Option Digest32 :=
  (log.find? (fun e => decide (e.1 = input))).map Prod.snd

def predecessor (log : PublicLog) (cv : Digest32) : Option Node :=
  (log.find? (fun e => decide (e.2 = cv))).map Prod.fst

/-- Fuel counts prior public calls, not the private raw-oracle budget. Complete
chains retain the entire seed input; only nonseed CVs are chaining pointers. -/
def extend (log : PublicLog) : Nat → Digest32 → Option (List Node)
  | 0, _ => none
  | fuel+1, cv =>
    match predecessor log cv with
    | none => none
    | some n =>
      if isSeed n then some [n]
      else if isInternal n then (extend log fuel n.cv).map (n :: ·)
      else none

def recognized (log : PublicLog) (input : Node) : Option (List Node) :=
  if isTerminal input then (extend log log.length input.cv).map (input :: ·)
  else none

theorem extend_sound {log : PublicLog} {fuel : Nat} {cv : Digest32} {ns : List Node}
    (h : extend log fuel cv = some ns) : Body ns ∧ ns.length ≤ fuel := by
  induction fuel generalizing cv ns with
  | zero => simp [extend] at h
  | succ fuel ih =>
    simp only [extend] at h
    cases hp : predecessor log cv with
    | none => simp [hp] at h
    | some n =>
      simp only [hp] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst ns
        exact ⟨Body.seed (by assumption), by simp⟩
      · split at h
        · cases he : extend log fuel n.cv with
          | none => simp [he] at h
          | some rest =>
            simp only [he, Option.map_some, Option.some.injEq] at h
            subst ns
            obtain ⟨hb, hl⟩ := ih he
            exact ⟨Body.step (by assumption) hb, by simpa using Nat.succ_le_succ hl⟩
        · simp at h

theorem recognized_sound {log : PublicLog} {input : Node} {ns : List Node}
    (h : recognized log input = some ns) : Complete ns ∧ ns.length ≤ log.length+1 := by
  unfold recognized at h
  split at h
  · cases he : extend log log.length input.cv with
    | none => simp [he] at h
    | some rest =>
      simp only [he, Option.map_some, Option.some.injEq] at h
      subst ns
      obtain ⟨hb, hl⟩ := extend_sound he
      exact ⟨⟨input,rest,rfl,by assumption,hb⟩, by simpa using Nat.succ_le_succ hl⟩
  · simp at h

/-- The length check only totalizes the API on unreachable oversized logs.
`privateKey_of_recognized` proves it cannot drop a tree in a counted run. -/
def privateKey (Q : Nat) (log : PublicLog) (input : Node) : Option (RawKey Q) :=
  if (lookup log input).isSome then none else
  match recognized log input with
  | none => none
  | some ns =>
    if h : ns.length ≤ Q then
      some (restrictKey Q ⟨ns.map payload, ns.map (fun n => (n.tweak,n.last))⟩
        (by simpa using h) (by simpa using h))
    else none

theorem privateKey_of_recognized {Q : Nat} {log : PublicLog} {input : Node} {ns : List Node}
    (fresh : lookup log input = none) (tree : recognized log input = some ns)
    (budget : log.length+1 ≤ Q) :
    ∃ key, privateKey Q log input = some key ∧ extract ns = some (expandKey key) := by
  have hs := recognized_sound tree
  have hl : ns.length ≤ Q := hs.2.trans budget
  simp only [privateKey, fresh, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, tree, hl]
  refine ⟨_, rfl, ?_⟩
  simp [extract, (complete?_correct ns).mpr hs.1]

theorem privateKey_sound {Q : Nat} {log : PublicLog} {input : Node} {key : RawKey Q}
    (h : privateKey Q log input = some key) :
    ∃ ns, recognized log input = some ns ∧ Complete ns ∧ extract ns = some (expandKey key) := by
  unfold privateKey at h
  split at h
  · simp at h
  · cases hr : recognized log input with
    | none => simp [hr] at h
    | some ns =>
      simp only [hr] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst key
        refine ⟨ns,rfl,(recognized_sound hr).1,?_⟩
        simp [extract, (complete?_correct ns).mpr (recognized_sound hr).1]
      · simp at h

theorem privateKey_lengths_log {Q : Nat} {log : PublicLog} {input : Node} {key : RawKey Q}
    (h : privateKey Q log input = some key) :
    key.1.1.val ≤ log.length+1 ∧ key.2.1.val ≤ log.length+1 := by
  unfold privateKey at h
  split at h
  · simp at h
  · cases hr : recognized log input with
    | none => simp [hr] at h
    | some ns =>
      simp only [hr] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst key
        simpa [restrictKey, shortList] using
          And.intro (recognized_sound hr).2 (recognized_sound hr).2
      · simp at h

structure State where
  seed : Seed
  publicLog : PublicLog

def simulator (Q : Nat) : Simulator Q Seed State where
  initial seed := ⟨seed,[]⟩
  answer state input :=
    match lookup state.publicLog input with
    | some answer => .done (⟨state.seed,observe state.publicLog input answer⟩,answer)
    | none =>
      match privateKey Q state.publicLog input with
      | some key => .ask key (fun answer =>
          .done (⟨state.seed,observe state.publicLog input answer⟩,answer))
      | none =>
          let answer := state.seed input
          .done (⟨state.seed,observe state.publicLog input answer⟩,answer)

theorem repeated_no_query (Q : Nat) (state : State) (input : Node) (answer : Digest32)
    (h : lookup state.publicLog input = some answer) :
    (simulator Q).answer state input =
      .done (⟨state.seed,observe state.publicLog input answer⟩,answer) := by
  simp [simulator, h]

theorem answer_publicLog (Q : Nat) (ro : RawKey Q → Digest32) (state : State) (input : Node) :
    (runRO ro ((simulator Q).answer state input)).1.1.publicLog =
      observe state.publicLog input (runRO ro ((simulator Q).answer state input)).1.2 := by
  simp only [simulator]
  cases lookup state.publicLog input <;> simp only
  · cases privateKey Q state.publicLog input <;> rfl
  · rfl

theorem answer_seed (Q : Nat) (ro : RawKey Q → Digest32) (state : State) (input : Node) :
    (runRO ro ((simulator Q).answer state input)).1.1.seed = state.seed := by
  simp only [simulator]
  cases lookup state.publicLog input <;> simp only
  · cases privateKey Q state.publicLog input <;> rfl
  · rfl

theorem answer_queries_le_one (Q : Nat) (ro : RawKey Q → Digest32) (state : State) (input : Node) :
    (runRO ro ((simulator Q).answer state input)).2 ≤ 1 := by
  simp only [simulator]
  cases lookup state.publicLog input <;> simp only
  · cases privateKey Q state.publicLog input <;> simp [runRO]
  · simp [runRO]

theorem simulatorBound {Q : Nat} {Result : Type} (ro : RawKey Q → Digest32) (iv : Digest32)
    (state : State) (p : Program Result) (remaining : Nat) (cap : remaining ≤ Q)
    (counted : Counts remaining p) :
    (runIdeal (simulator Q) ro iv state p remaining cap counted).simulatorQueries ≤ remaining := by
  induction p generalizing state remaining with
  | done r => simp [runIdeal]
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      have hr := ih (runRO ro ((simulator Q).answer state input)).1.2
        (runRO ro ((simulator Q).answer state input)).1.1 (remaining-1) (by omega) (counted.2 _)
      have ha := answer_queries_le_one Q ro state input
      have hc : 1 ≤ remaining := counted.1
      simp only [runIdeal, prepend]
      omega
    | construction q valid =>
      have hr := ih (ro (constructionKey Q iv q (counted.1.trans cap))) state
        (remaining-pathCost q) (by omega) (counted.2 _)
      simp only [runIdeal, prepend]
      omega

/-- Private schedule from public data alone. This includes direct construction
requests, in their actual order; construction replies never enter the log. -/
def replay (Q : Nat) (iv : Digest32) (log : PublicLog) : List Observation → List (RawKey Q)
  | [] => []
  | ⟨.primitive _ input,answer⟩ :: rest =>
      (privateKey Q log input).toList ++ replay Q iv (observe log input answer) rest
  | ⟨.construction q _,_⟩ :: rest =>
      if h : pathCost q ≤ Q then constructionKey Q iv q h :: replay Q iv log rest
      else replay Q iv log rest

/-- Instrumentation of actual RO programs, used only for the replay theorem. -/
def requests {Q : Nat} {Result : Type} (ro : RawKey Q → Digest32) : ROProgram Q Result → List (RawKey Q)
  | .done _ => []
  | .ask key next => key :: requests ro (next (ro key))

theorem answer_requests (Q : Nat) (ro : RawKey Q → Digest32) (state : State) (input : Node) :
    requests ro ((simulator Q).answer state input) = (privateKey Q state.publicLog input).toList := by
  cases h : lookup state.publicLog input with
  | none =>
    simp only [simulator, h]
    cases privateKey Q state.publicLog input <;> rfl
  | some answer => simp [simulator, h, requests, privateKey]

def actualRequests {Q : Nat} {Result : Type} (ro : RawKey Q → Digest32) (iv : Digest32)
    (state : State) : (p : Program Result) → (remaining : Nat) → remaining ≤ Q →
      Counts remaining p → List (RawKey Q)
  | .done _, _, _, _ => []
  | .ask (.primitive _ input) next, remaining, cap, counted =>
      let answer := runRO ro ((simulator Q).answer state input)
      requests ro ((simulator Q).answer state input) ++
        actualRequests ro iv answer.1.1 (next answer.1.2) (remaining-1) (by omega) (counted.2 _)
  | .ask (.construction q _) next, remaining, cap, counted =>
      let key := constructionKey Q iv q (counted.1.trans cap)
      key :: actualRequests ro iv state (next (ro key)) (remaining-pathCost q) (by omega) (counted.2 _)

theorem replay_actual {Q : Nat} {Result : Type} (ro : RawKey Q → Digest32) (iv : Digest32)
    (state : State) (p : Program Result) (remaining : Nat) (cap : remaining ≤ Q)
    (counted : Counts remaining p) :
    replay Q iv state.publicLog (runIdeal (simulator Q) ro iv state p remaining cap counted).view.observations =
      actualRequests ro iv state p remaining cap counted := by
  induction p generalizing state remaining with
  | done r => rfl
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      simp only [runIdeal, prepend, replay, actualRequests, answer_requests]
      rw [← answer_publicLog Q ro state input]
      exact congrArg ((privateKey Q state.publicLog input).toList ++ ·)
        (ih _ _ _ _ _)
    | construction q valid =>
      have hq : pathCost q ≤ Q := counted.1.trans cap
      simp only [runIdeal, prepend, replay, actualRequests, hq, ↓reduceDIte]
      exact congrArg (constructionKey Q iv q hq :: ·) (ih _ _ _ _ _)

/-- Collision ambiguity is the ordinary event that distinct primitive inputs
have the same full 256-bit output. Repeated records are not ambiguities. -/
def OutputCollision (log : PublicLog) : Prop :=
  ∃ n m d, (n,d) ∈ log ∧ (m,d) ∈ log ∧ n ≠ m

theorem predecessor_mem {log : PublicLog} {cv : Digest32} {n : Node}
    (h : predecessor log cv = some n) : (n,cv) ∈ log := by
  induction log with
  | nil => simp [predecessor] at h
  | cons entry rest ih =>
    rcases entry with ⟨m,d⟩
    by_cases hd : d = cv
    · simp [predecessor, List.find?, hd] at h
      subst n; subst d; simp
    · have ht : predecessor rest cv = some n := by
        simpa [predecessor, List.find?, hd] using h
      exact List.mem_cons_of_mem _ (ih ht)

theorem predecessor_of_mem {log : PublicLog} (clean : ¬OutputCollision log)
    {n : Node} {cv : Digest32} (member : (n,cv) ∈ log) :
    predecessor log cv = some n := by
  induction log with
  | nil => simp at member
  | cons entry rest ih =>
    rcases entry with ⟨m,d⟩
    by_cases hd : d = cv
    · have same : m = n := by
        by_contra hn
        exact clean ⟨m,n,cv,by simp [hd],member,hn⟩
      simp [predecessor, List.find?, hd, same]
    · have hm : (n,cv) ∈ rest := by
        rcases List.mem_cons.mp member with he | he
        · cases he; exact False.elim (hd rfl)
        · exact he
      have hc : ¬OutputCollision rest := by
        rintro ⟨a,b,e,ha,hb,hn⟩
        exact clean ⟨a,b,e,List.mem_cons_of_mem _ ha,List.mem_cons_of_mem _ hb,hn⟩
      simpa [predecessor, List.find?, hd] using ih hc hm

/-- Full-CV links are witnessed by actual primitive input/output records. -/
inductive PublicBody (log : PublicLog) : Digest32 → List Node → Prop where
  | seed {n d} : (n,d) ∈ log → isSeed n → PublicBody log d [n]
  | step {n d ns} : (n,d) ∈ log → isInternal n →
      PublicBody log n.cv ns → PublicBody log d (n :: ns)

theorem PublicBody.body {log : PublicLog} {cv : Digest32} {ns : List Node}
    (h : PublicBody log cv ns) : Body ns := by
  induction h with
  | seed _ hs => exact Body.seed hs
  | step _ hi _ ih => exact Body.step hi ih

theorem PublicBody.members {log : PublicLog} {cv : Digest32} {ns : List Node}
    (h : PublicBody log cv ns) : ∀ n ∈ ns, n ∈ log.map Prod.fst := by
  induction h with
  | seed hm _ =>
    intro n hn
    simp only [List.mem_singleton] at hn
    subst n
    exact List.mem_map.mpr ⟨_,hm,rfl⟩
  | step hm _ _ ih =>
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact List.mem_map.mpr ⟨_,hm,rfl⟩
    · exact ih n hn

theorem extend_publicBody {log : PublicLog} {fuel : Nat} {cv : Digest32} {ns : List Node}
    (h : extend log fuel cv = some ns) : PublicBody log cv ns := by
  induction fuel generalizing cv ns with
  | zero => simp [extend] at h
  | succ fuel ih =>
    simp only [extend] at h
    cases hp : predecessor log cv with
    | none => simp [hp] at h
    | some n =>
      simp only [hp] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst ns
        exact PublicBody.seed (predecessor_mem hp) (by assumption)
      · split at h
        · cases he : extend log fuel n.cv with
          | none => simp [he] at h
          | some rest =>
            simp only [he, Option.map_some, Option.some.injEq] at h
            subst ns
            exact PublicBody.step (predecessor_mem hp) (by assumption) (ih he)
        · simp at h

theorem PublicBody.compression {log : PublicLog} {cv : Digest32} {ns : List Node}
    (h : PublicBody log cv ns) (oracle : PrimitiveOracle)
    (consistent : ∀ n d, (n,d) ∈ log → oracle n = d) :
    Tree (compressionOf oracle) cv ns := by
  induction h with
  | seed hm hs =>
    have he := consistent _ _ hm
    simpa [nodeValue, compressionOf, he] using Tree.seed (c := compressionOf oracle) _ hs
  | step hm hi _ ih =>
    have he := consistent _ _ hm
    simpa [nodeValue, compressionOf, he] using Tree.step _ _ hi ih

/-- On collision-free logs, radicalExtend follows every supplied full-CV link,
not block heuristics, a fixed IV, or private simulator state. -/
theorem extend_complete {log : PublicLog} (clean : ¬OutputCollision log)
    {cv : Digest32} {ns : List Node} (tree : PublicBody log cv ns)
    (fuel : Nat) (bound : ns.length ≤ fuel) : extend log fuel cv = some ns := by
  induction tree generalizing fuel with
  | seed hm hs =>
    cases fuel with
    | zero => simp at bound
    | succ fuel => simp [extend, predecessor_of_mem clean hm, hs]
  | step hm hi child ih =>
    cases fuel with
    | zero => simp at bound
    | succ fuel =>
      have hn : ¬isSeed _ := fun hs => seed_not_internal hs hi
      simp only [extend, predecessor_of_mem clean hm, hn, ↓reduceIte, hi]
      rw [ih fuel (by simpa using bound)]
      rfl

/-- The counted public program, not an assumed raw-query budget, supplies fuel
and the key-length bound at every primitive call of the actual run. -/
def BudgetSafe {Q : Nat} {Result : Type} (ro : RawKey Q → Digest32) (iv : Digest32)
    (state : State) : (p : Program Result) → (remaining : Nat) → remaining ≤ Q →
      Counts remaining p → Prop
  | .done _, _, _, _ => True
  | .ask (.primitive _ input) next, remaining, cap, counted =>
      state.publicLog.length+1 ≤ Q ∧
      let answer := runRO ro ((simulator Q).answer state input)
      BudgetSafe ro iv answer.1.1 (next answer.1.2) (remaining-1) (by omega) (counted.2 _)
  | .ask (.construction q _) next, remaining, cap, counted =>
      let key := constructionKey Q iv q (counted.1.trans cap)
      BudgetSafe ro iv state (next (ro key)) (remaining-pathCost q) (by omega) (counted.2 _)

theorem budgetSafe {Q : Nat} {Result : Type} (ro : RawKey Q → Digest32) (iv : Digest32)
    (state : State) (p : Program Result) (remaining : Nat) (cap : remaining ≤ Q)
    (counted : Counts remaining p) (budget : state.publicLog.length + remaining ≤ Q) :
    BudgetSafe ro iv state p remaining cap counted := by
  induction p generalizing state remaining with
  | done r => trivial
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      have hc : 1 ≤ remaining := counted.1
      refine ⟨by omega, ih _ _ _ _ _ ?_⟩
      rw [answer_publicLog]
      simp only [observe, List.length_cons]
      omega
    | construction q valid =>
      exact ih _ _ _ _ _ (by omega)

theorem initial_budgetSafe {Q : Nat} {Result : Type} (ro : RawKey Q → Digest32)
    (iv : Digest32) (seed : Seed) (p : Program Result) (counted : Counts Q p) :
    BudgetSafe ro iv ((simulator Q).initial seed) p Q (by omega) counted :=
  budgetSafe ro iv _ p Q (by omega) counted (by simp [simulator])

def Functional (log : PublicLog) : Prop :=
  ∀ n a b, (n,a) ∈ log → (n,b) ∈ log → a = b

theorem PublicBody.unique {log : PublicLog} (clean : ¬OutputCollision log)
    {cv : Digest32} {ns ms : List Node} (a : PublicBody log cv ns) (b : PublicBody log cv ms) :
    ns = ms := by
  have ha := extend_complete clean a (ns.length+ms.length) (by omega)
  have hb := extend_complete clean b (ns.length+ms.length) (by omega)
  exact Option.some.inj (ha.symm.trans hb)

theorem PublicBody.subtree {log : PublicLog} {cv : Digest32} {ns : List Node}
    (tree : PublicBody log cv ns) {n : Node} (member : n ∈ ns) :
    ∃ d rest, (n,d) ∈ log ∧ PublicBody log d (n :: rest) ∧ (n :: rest).length ≤ ns.length := by
  induction tree with
  | seed hm hs =>
    simp only [List.mem_singleton] at member
    subst n
    exact ⟨_,[],hm,PublicBody.seed hm hs,le_rfl⟩
  | step hm hi child ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,_,hm,PublicBody.step hm hi child,le_rfl⟩
    · obtain ⟨d,rest,hm,ht,hl⟩ := ih member
      exact ⟨d,rest,hm,ht,by simp only [List.length_cons] at *; omega⟩

theorem PublicBody.nodup {log : PublicLog} (functional : Functional log)
    (clean : ¬OutputCollision log) {cv : Digest32} {ns : List Node}
    (tree : PublicBody log cv ns) : ns.Nodup := by
  induction tree with
  | seed _ _ => simp
  | @step n d ns hm hi child ih =>
    refine List.nodup_cons.mpr ⟨?_,ih⟩
    intro member
    obtain ⟨d',rest,hm',ht,hl⟩ := child.subtree member
    have hd := functional n d d' hm hm'
    subst d'
    have he := PublicBody.unique clean (PublicBody.step hm hi child) ht
    have he' := congrArg List.length he
    simp only [List.length_cons] at *
    omega

theorem PublicBody.length_le {log : PublicLog} (functional : Functional log)
    (clean : ¬OutputCollision log) {cv : Digest32} {ns : List Node}
    (tree : PublicBody log cv ns) : ns.length ≤ log.length := by
  have h := List.Nodup.length_le_of_subset (tree.nodup functional clean) tree.members
  simpa using h

/-- No complete, publicly linked tree is lost to traversal fuel on an ordinary
functional, collision-free oracle log. Cyclic or ambiguous logs are outside this
structural theorem, not silently declared good by the simulator. -/
theorem recognized_complete {log : PublicLog} (functional : Functional log)
    (clean : ¬OutputCollision log) {input : Node} (terminal : isTerminal input)
    {ns : List Node} (tree : PublicBody log input.cv ns) :
    recognized log input = some (input :: ns) := by
  simp only [recognized, terminal, ↓reduceIte]
  rw [extend_complete clean tree log.length (tree.length_le functional clean)]
  rfl

theorem lookup_mem {log : PublicLog} {n : Node} {d : Digest32}
    (h : lookup log n = some d) : (n,d) ∈ log := by
  induction log with
  | nil => simp [lookup] at h
  | cons entry rest ih =>
    rcases entry with ⟨m,e⟩
    by_cases hn : m = n
    · simp [lookup, List.find?, hn] at h
      subst m; subst d; simp
    · have ht : lookup rest n = some d := by simpa [lookup, List.find?, hn] using h
      exact List.mem_cons_of_mem _ (ih ht)

theorem lookup_exists {log : PublicLog} {n : Node} {d : Digest32}
    (member : (n,d) ∈ log) : ∃ e, lookup log n = some e := by
  induction log with
  | nil => simp at member
  | cons entry rest ih =>
    rcases entry with ⟨m,e⟩
    by_cases hn : m = n
    · exact ⟨e,by simp [lookup, List.find?, hn]⟩
    · have hm : (n,d) ∈ rest := by
        rcases List.mem_cons.mp member with he | he
        · cases he; exact False.elim (hn rfl)
        · exact he
      obtain ⟨e,he⟩ := ih hm
      exact ⟨e,by simpa [lookup, List.find?, hn] using he⟩

theorem observe_functional {log : PublicLog} (functional : Functional log)
    (n : Node) (d : Digest32) (agree : ∀ e, (n,e) ∈ log → d = e) :
    Functional (observe log n d) := by
  intro m a b ha hb
  rcases List.mem_cons.mp ha with ha | ha
  · cases ha
    rcases List.mem_cons.mp hb with hb | hb
    · cases hb; rfl
    · exact agree _ hb
  · rcases List.mem_cons.mp hb with hb | hb
    · cases hb; exact (agree _ ha).symm
    · exact functional _ _ _ ha hb

theorem answer_functional (Q : Nat) (ro : RawKey Q → Digest32) (state : State)
    (input : Node) (functional : Functional state.publicLog) :
    Functional (runRO ro ((simulator Q).answer state input)).1.1.publicLog := by
  rw [answer_publicLog]
  apply observe_functional functional
  intro e member
  obtain ⟨d,hd⟩ := lookup_exists member
  rw [repeated_no_query Q state input d hd]
  exact functional input d e (lookup_mem hd) member

/-- Explicit finite private seed table; no state is added to `Mode.View`. -/
@[instance_reducible]
noncomputable def seedFintype : Fintype Seed := by
  letI : Finite UInt64 := Finite.of_injective ByteCodec.encodeK ByteCodec.encodeK_injective
  let fields : Node → Digest32 × Block64 × UInt64 × Bool :=
    fun n => (n.cv,n.block,n.tweak,n.last)
  have inj : Function.Injective fields := by
    intro a b h
    cases a; cases b
    simpa [fields] using h
  letI : Finite Node := Finite.of_injective fields inj
  exact Fintype.ofFinite Seed

theorem recognized_publicBody {log : PublicLog} {input : Node} {ns : List Node}
    (h : recognized log input = some ns) :
    ∃ rest, ns = input :: rest ∧ PublicBody log input.cv rest := by
  unfold recognized at h
  split at h
  · cases he : extend log log.length input.cv with
    | none => simp [he] at h
    | some rest =>
      simp only [he, Option.map_some, Option.some.injEq] at h
      exact ⟨rest,h.symm,extend_publicBody he⟩
  · simp at h

theorem privateKey_compression {Q : Nat} {log : PublicLog} {input : Node} {key : RawKey Q}
    (h : privateKey Q log input = some key) (oracle : PrimitiveOracle)
    (consistent : ∀ n d, (n,d) ∈ log → oracle n = d) :
    ∃ rest, Complete (input :: rest) ∧ Tree (compressionOf oracle) input.cv rest ∧
      extract (input :: rest) = some (expandKey key) := by
  obtain ⟨ns,hr,hc,he⟩ := privateKey_sound h
  obtain ⟨rest,rfl,ht⟩ := recognized_publicBody hr
  exact ⟨rest,hc,ht.compression oracle consistent,he⟩

/-- Exact canonical fresh-terminal behavior under checked structural
prerequisites, including arbitrary chosen/cloned seed CVs. -/
theorem canonical_terminal {Q : Nat} (state : State) (input : Node)
    (functional : Functional state.publicLog) (clean : ¬OutputCollision state.publicLog)
    (fresh : lookup state.publicLog input = none) (terminal : isTerminal input)
    {ns : List Node} (tree : PublicBody state.publicLog input.cv ns)
    (budget : state.publicLog.length+1 ≤ Q) :
    ∃ key, extract (input :: ns) = some (expandKey key) ∧
      (simulator Q).answer state input =
        .ask key (fun answer => .done (⟨state.seed,observe state.publicLog input answer⟩,answer)) := by
  obtain ⟨key,hk,he⟩ := privateKey_of_recognized fresh
    (recognized_complete functional clean terminal tree) budget
  exact ⟨key,he,by simp [simulator,fresh,hk]⟩

theorem same_public_schedule (Q : Nat) (ro : RawKey Q → Digest32)
    (a b : State) (input : Node) (same : a.publicLog = b.publicLog) :
    requests ro ((simulator Q).answer a input) = requests ro ((simulator Q).answer b input) := by
  simp only [answer_requests, same]

/-- Ordered public-derived raw requests paired with their public answers.
Cached and incomplete primitive calls produce no pair. -/
def replayAnswers (Q : Nat) (iv : Digest32) (log : PublicLog) :
    List Observation → List (RawKey Q × Digest32)
  | [] => []
  | ⟨.primitive _ input,answer⟩ :: rest =>
      ((privateKey Q log input).toList.map (fun key => (key,answer))) ++
        replayAnswers Q iv (observe log input answer) rest
  | ⟨.construction q _,answer⟩ :: rest =>
      if h : pathCost q ≤ Q then (constructionKey Q iv q h,answer) :: replayAnswers Q iv log rest
      else replayAnswers Q iv log rest

theorem replayAnswers_keys (Q : Nat) (iv : Digest32) (log : PublicLog)
    (observations : List Observation) :
    (replayAnswers Q iv log observations).map Prod.fst = replay Q iv log observations := by
  induction observations generalizing log with
  | nil => rfl
  | cons observation rest ih =>
    rcases observation with ⟨query,answer⟩
    cases query with
    | primitive purpose input =>
      simp only [replayAnswers, replay, List.map_append, List.map_map, ih]
      cases privateKey Q log input <;> rfl
    | construction q valid =>
      by_cases h : pathCost q ≤ Q <;> simp [replayAnswers, replay, h, ih]

theorem answer_privateKey {Q : Nat} (ro : RawKey Q → Digest32)
    (state : State) (input : Node) (key : RawKey Q)
    (h : privateKey Q state.publicLog input = some key) :
    (runRO ro ((simulator Q).answer state input)).1.2 = ro key := by
  cases hl : lookup state.publicLog input with
  | none => simp [simulator, hl, h, runRO]
  | some answer => simp [privateKey, hl] at h

theorem replayAnswers_consistent {Q : Nat} {Result : Type} (ro : RawKey Q → Digest32)
    (iv : Digest32) (state : State) (p : Program Result) (remaining : Nat)
    (cap : remaining ≤ Q) (counted : Counts remaining p) :
    ∀ entry ∈ replayAnswers Q iv state.publicLog
      (runIdeal (simulator Q) ro iv state p remaining cap counted).view.observations,
      entry.2 = ro entry.1 := by
  induction p generalizing state remaining with
  | done r => simp [runIdeal, replayAnswers]
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      simp only [runIdeal, prepend, replayAnswers]
      intro entry member
      rcases List.mem_append.mp member with member | member
      · cases hk : privateKey Q state.publicLog input with
        | none => simp [hk] at member
        | some key =>
          simp only [hk, Option.toList_some, List.map_cons, List.map_nil,
            List.mem_singleton] at member
          subst entry
          exact answer_privateKey ro state input key hk
      · exact ih (runRO ro ((simulator Q).answer state input)).1.2
          (runRO ro ((simulator Q).answer state input)).1.1 (remaining-1)
          (by omega) (counted.2 _) entry (by simpa only [answer_publicLog] using member)
    | construction q valid =>
      have hq : pathCost q ≤ Q := counted.1.trans cap
      simp only [runIdeal, prepend, replayAnswers, hq, ↓reduceDIte]
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · rfl
      · exact ih _ _ _ _ _ entry member

/-- Source accounting is independent of the ambient finite raw-key domain and
the interpreter's remaining meter. This allows a short source prefix to be
embedded in a larger experiment without inflating backfill path bounds. -/
theorem replayAnswers_lengths {Q : Nat} {Result : Type} (ro : RawKey Q → Digest32)
    (iv : Digest32) (state : State) (p : Program Result) (remaining : Nat)
    (cap : remaining ≤ Q) (counted : Counts remaining p)
    (sourceBudget sourceRemaining : Nat) (sourceCounted : Counts sourceRemaining p)
    (budget : state.publicLog.length + sourceRemaining ≤ sourceBudget) :
    ∀ entry ∈ replayAnswers Q iv state.publicLog
      (runIdeal (simulator Q) ro iv state p remaining cap counted).view.observations,
      entry.1.1.1.val ≤ sourceBudget ∧ entry.1.2.1.val ≤ sourceBudget := by
  induction p generalizing state remaining sourceRemaining with
  | done r => simp [runIdeal, replayAnswers]
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      have hc : 1 ≤ sourceRemaining := sourceCounted.1
      simp only [runIdeal, prepend, replayAnswers]
      intro entry member
      rcases List.mem_append.mp member with member | member
      · cases hk : privateKey Q state.publicLog input with
        | none => simp [hk] at member
        | some key =>
          simp only [hk, Option.toList_some, List.map_cons, List.map_nil,
            List.mem_singleton] at member
          subst entry
          have hl := privateKey_lengths_log hk
          dsimp only
          exact ⟨by omega,by omega⟩
      · have hb : (runRO ro ((simulator Q).answer state input)).1.1.publicLog.length +
            (sourceRemaining-1) ≤ sourceBudget := by
          rw [answer_publicLog]
          simp only [observe, List.length_cons]
          omega
        exact ih (runRO ro ((simulator Q).answer state input)).1.2
          (runRO ro ((simulator Q).answer state input)).1.1 (remaining-1) (by omega)
          (counted.2 _) (sourceRemaining-1) (sourceCounted.2 _) hb entry
          (by simpa only [answer_publicLog] using member)
    | construction q valid =>
      have hq : pathCost q ≤ Q := counted.1.trans cap
      have hs : pathCost q ≤ sourceRemaining := sourceCounted.1
      simp only [runIdeal, prepend, replayAnswers, hq, ↓reduceDIte]
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · simp only [constructionKey, restrictKey, shortList,
          (modeKey_lengths iv q).1, (modeKey_lengths iv q).2]
        exact ⟨by omega,by omega⟩
      · exact ih _ state (remaining-pathCost q) (by omega) (counted.2 _)
          (sourceRemaining-pathCost q) (sourceCounted.2 _) (by omega) entry member

theorem replayAnswers_source_bound {Q : Nat} {Result : Type} (ro : RawKey Q → Digest32)
    (iv : Digest32) (seed : Seed) (p : Program Result) (remaining : Nat)
    (cap : remaining ≤ Q) (counted : Counts remaining p)
    (sourceBudget : Nat) (sourceCounted : Counts sourceBudget p) :
    ∀ entry ∈ replayAnswers Q iv []
      (runIdeal (simulator Q) ro iv ((simulator Q).initial seed) p remaining cap counted).view.observations,
      entry.1.1.1.val ≤ sourceBudget ∧ entry.1.2.1.val ≤ sourceBudget :=
  replayAnswers_lengths ro iv ((simulator Q).initial seed) p remaining cap counted
    sourceBudget sourceBudget sourceCounted (by simp [simulator])

/-- Fold only public primitive observations; neither raw tables nor private
simulator state are arguments of seed reconstruction. -/
def finalLog (log : PublicLog) : List Observation → PublicLog
  | [] => log
  | ⟨.primitive _ input,answer⟩ :: rest => finalLog (observe log input answer) rest
  | ⟨.construction _ _,_⟩ :: rest => finalLog log rest

def fallbackFromLog (log : PublicLog) : Seed :=
  fun input => (lookup log input).getD zeroDigest

def reconstructSeed (observations : List Observation) : Seed :=
  fallbackFromLog (finalLog [] observations)

theorem finalLog_contains (log : PublicLog) (observations : List Observation) :
    ∀ entry ∈ log, entry ∈ finalLog log observations := by
  induction observations generalizing log with
  | nil => exact fun _ h => h
  | cons observation rest ih =>
    rcases observation with ⟨query,answer⟩
    cases query with
    | primitive purpose input => exact fun _ h => ih _ _ (List.mem_cons_of_mem _ h)
    | construction q valid => exact ih log

theorem finalLog_functional {Q : Nat} {Result : Type} (ro : RawKey Q → Digest32)
    (iv : Digest32) (state : State) (p : Program Result) (remaining : Nat)
    (cap : remaining ≤ Q) (counted : Counts remaining p) (functional : Functional state.publicLog) :
    Functional (finalLog state.publicLog
      (runIdeal (simulator Q) ro iv state p remaining cap counted).view.observations) := by
  induction p generalizing state remaining with
  | done r => exact functional
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      simpa only [runIdeal, prepend, finalLog, answer_publicLog] using
        ih _ _ _ _ _ (answer_functional Q ro state input functional)
    | construction q valid => exact ih _ _ _ _ _ functional

theorem fallbackFromLog_of_mem {log : PublicLog} (functional : Functional log)
    {input : Node} {answer : Digest32} (member : (input,answer) ∈ log) :
    fallbackFromLog log input = answer := by
  obtain ⟨d,hd⟩ := lookup_exists member
  have he := functional input d answer (lookup_mem hd) member
  simp [fallbackFromLog, hd, he]

/-- Agreement is required only where the actual execution consumes fallback
randomness. Complete-tree and cached inputs impose no seed equality premise. -/
def FallbackAgreement {Q : Nat} {Result : Type} (ro : RawKey Q → Digest32)
    (iv : Digest32) (replacement : Seed) (state : State) :
    (p : Program Result) → (remaining : Nat) → remaining ≤ Q → Counts remaining p → Prop
  | .done _, _, _, _ => True
  | .ask (.primitive _ input) next, remaining, cap, counted =>
      (lookup state.publicLog input = none → privateKey Q state.publicLog input = none →
        replacement input = state.seed input) ∧
      let answer := runRO ro ((simulator Q).answer state input)
      FallbackAgreement ro iv replacement answer.1.1 (next answer.1.2)
        (remaining-1) (by omega) (counted.2 _)
  | .ask (.construction q _) next, remaining, cap, counted =>
      let key := constructionKey Q iv q (counted.1.trans cap)
      FallbackAgreement ro iv replacement state (next (ro key))
        (remaining-pathCost q) (by omega) (counted.2 _)

theorem fallbackAgreement_from_log {Q : Nat} {Result : Type} (ro : RawKey Q → Digest32)
    (iv : Digest32) (state : State) (p : Program Result) (remaining : Nat)
    (cap : remaining ≤ Q) (counted : Counts remaining p) (log : PublicLog)
    (functional : Functional log)
    (recorded : ∀ entry ∈ finalLog state.publicLog
      (runIdeal (simulator Q) ro iv state p remaining cap counted).view.observations, entry ∈ log) :
    FallbackAgreement ro iv (fallbackFromLog log) state p remaining cap counted := by
  induction p generalizing state remaining with
  | done r => trivial
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      have recorded' : ∀ entry ∈ finalLog (runRO ro ((simulator Q).answer state input)).1.1.publicLog
          (runIdeal (simulator Q) ro iv (runRO ro ((simulator Q).answer state input)).1.1
            (next (runRO ro ((simulator Q).answer state input)).1.2)
            (remaining-1) (by omega) (counted.2 _)).view.observations, entry ∈ log := by
        simpa only [runIdeal, prepend, finalLog, answer_publicLog] using recorded
      refine ⟨?_,ih _ _ _ _ _ recorded'⟩
      intro fresh incomplete
      have member : (input,state.seed input) ∈
          (runRO ro ((simulator Q).answer state input)).1.1.publicLog := by
        simp [simulator, fresh, incomplete, runRO, observe]
      exact fallbackFromLog_of_mem functional
        (recorded' _ (finalLog_contains _ _ _ member))
    | construction q valid => exact ih _ _ _ _ _ recorded

theorem reconstructSeed_agrees {Q : Nat} {Result : Type} (ro : RawKey Q → Digest32)
    (iv : Digest32) (seed : Seed) (p : Program Result) (counted : Counts Q p) :
    FallbackAgreement ro iv
      (reconstructSeed (runIdeal (simulator Q) ro iv ((simulator Q).initial seed)
        p Q (by omega) counted).view.observations)
      ((simulator Q).initial seed) p Q (by omega) counted := by
  apply fallbackAgreement_from_log ro iv ((simulator Q).initial seed) p Q (by omega) counted
  · exact finalLog_functional ro iv ((simulator Q).initial seed) p Q (by omega) counted
      (by simp [simulator, Functional])
  · exact fun _ h => h

theorem answer_replace_seed {Q : Nat} (ro : RawKey Q → Digest32)
    (state : State) (replacement : Seed) (input : Node)
    (agree : lookup state.publicLog input = none → privateKey Q state.publicLog input = none →
      replacement input = state.seed input) :
    runRO ro ((simulator Q).answer {state with seed := replacement} input) =
      let actual := runRO ro ((simulator Q).answer state input)
      (({actual.1.1 with seed := replacement},actual.1.2),actual.2) := by
  cases hl : lookup state.publicLog input with
  | some d => simp [simulator, hl, runRO]
  | none =>
    cases hk : privateKey Q state.publicLog input with
    | some key => simp [simulator, hl, hk, runRO]
    | none => simp [simulator, hl, hk, runRO, agree hl hk]

theorem runIdeal_replace_seed {Q : Nat} {Result : Type} (ro : RawKey Q → Digest32)
    (iv : Digest32) (replacement : Seed) (state : State) (p : Program Result)
    (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining p)
    (agree : FallbackAgreement ro iv replacement state p remaining cap counted) :
    runIdeal (simulator Q) ro iv {state with seed := replacement} p remaining cap counted =
      runIdeal (simulator Q) ro iv state p remaining cap counted := by
  induction p generalizing state remaining with
  | done r => rfl
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      simp only [runIdeal, answer_replace_seed ro state replacement input agree.1]
      congr 1
      exact ih _ _ _ _ _ agree.2
    | construction q valid =>
      simp only [runIdeal]
      congr 1
      exact ih _ _ _ _ _ agree

theorem reconstructSeed_runIdeal {Q : Nat} {Result : Type} (ro : RawKey Q → Digest32)
    (iv : Digest32) (seed : Seed) (p : Program Result) (counted : Counts Q p) :
    let actual := runIdeal (simulator Q) ro iv ((simulator Q).initial seed) p Q (by omega) counted
    runIdeal (simulator Q) ro iv ((simulator Q).initial (reconstructSeed actual.view.observations))
      p Q (by omega) counted = actual :=
  runIdeal_replace_seed ro iv _ _ p Q (by omega) counted (reconstructSeed_agrees ro iv seed p counted)

theorem reconstructSeed_actualRequests {Q : Nat} {Result : Type} (ro : RawKey Q → Digest32)
    (iv : Digest32) (seed : Seed) (p : Program Result) (counted : Counts Q p) :
    let actual := runIdeal (simulator Q) ro iv ((simulator Q).initial seed) p Q (by omega) counted
    actualRequests ro iv ((simulator Q).initial (reconstructSeed actual.view.observations))
      p Q (by omega) counted =
      actualRequests ro iv ((simulator Q).initial seed) p Q (by omega) counted := by
  dsimp only
  rw [← replay_actual, ← replay_actual, reconstructSeed_runIdeal]
  rfl

/-- A partial raw oracle stops before executing a continuation whose answer
has not been physically acquired. No default digest fills a cache miss. -/
def runPartialRO {Q : Nat} {Result : Type} (cache : RawKey Q → Option Digest32) :
    ROProgram Q Result → Except (RawKey Q) Result
  | .done result => .ok result
  | .ask key next =>
      match cache key with
      | none => .error key
      | some answer => runPartialRO cache (next answer)

def CacheAgrees {Q : Nat} (cache : RawKey Q → Option Digest32) (ro : RawKey Q → Digest32) : Prop :=
  ∀ key answer, cache key = some answer → answer = ro key

theorem runPartialRO_success {Q : Nat} {Result : Type} (cache : RawKey Q → Option Digest32)
    (ro : RawKey Q → Digest32) (agrees : CacheAgrees cache ro) (p : ROProgram Q Result)
    (result : Result) (success : runPartialRO cache p = .ok result) :
    (runRO ro p).1 = result := by
  induction p with
  | done r => simpa [runPartialRO, runRO] using success
  | ask key next ih =>
    cases hc : cache key with
    | none => simp [runPartialRO, hc] at success
    | some answer =>
      have he := agrees key answer hc
      subst answer
      exact ih (ro key) (by simpa [runPartialRO, hc] using success)

/-- The reported miss is exactly the first unavailable request in the full
actual raw schedule; every preceding request has its real answer in cache. -/
theorem runPartialRO_first_miss {Q : Nat} {Result : Type} (cache : RawKey Q → Option Digest32)
    (ro : RawKey Q → Digest32) (agrees : CacheAgrees cache ro) (p : ROProgram Q Result)
    (key : RawKey Q) (miss : runPartialRO cache p = .error key) :
    ∃ before after, requests ro p = before ++ key :: after ∧
      (∀ k ∈ before, cache k = some (ro k)) ∧ cache key = none := by
  induction p with
  | done r => simp [runPartialRO] at miss
  | ask current next ih =>
    cases hc : cache current with
    | none =>
      simp only [runPartialRO, hc, Except.error.injEq] at miss
      subst key
      exact ⟨[],requests ro (next (ro current)),rfl,by simp,hc⟩
    | some answer =>
      have he := agrees current answer hc
      subst answer
      obtain ⟨before,after,hr,hb,hm⟩ := ih (ro current) (by simpa [runPartialRO, hc] using miss)
      refine ⟨current :: before,after,?_,?_,hm⟩
      · simp only [requests, List.cons_append, hr]
      · intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · exact hc
        · exact hb k hk

structure PartialExecution (Q : Nat) (Result : Type) where
  observations : List Observation
  outcome : Except (RawKey Q) Result

def prependPartial {Q : Nat} {Result : Type} (query : Query) (answer : Digest32)
    (rest : PartialExecution Q Result) : PartialExecution Q Result :=
  ⟨⟨query,answer⟩ :: rest.observations,rest.outcome⟩

def runPartial {Q : Nat} {Result : Type} (cache : RawKey Q → Option Digest32)
    (iv : Digest32) (state : State) :
    (p : Program Result) → (remaining : Nat) → remaining ≤ Q → Counts remaining p →
      PartialExecution Q Result
  | .done result, _, _, _ => ⟨[],.ok result⟩
  | .ask (.primitive purpose input) next, remaining, cap, counted =>
      match runPartialRO cache ((simulator Q).answer state input) with
      | .error key => ⟨[],.error key⟩
      | .ok answer => prependPartial (.primitive purpose input) answer.2
          (runPartial cache iv answer.1 (next answer.2) (remaining-1) (by omega) (counted.2 _))
  | .ask (.construction q valid) next, remaining, cap, counted =>
      let key := constructionKey Q iv q (counted.1.trans cap)
      match cache key with
      | none => ⟨[],.error key⟩
      | some answer => prependPartial (.construction q valid) answer
          (runPartial cache iv state (next answer) (remaining-pathCost q) (by omega) (counted.2 _))

theorem partialAnswer_replace_seed {Q : Nat} (cache : RawKey Q → Option Digest32)
    (state : State) (replacement : Seed) (input : Node)
    (agree : lookup state.publicLog input = none → privateKey Q state.publicLog input = none →
      replacement input = state.seed input) :
    runPartialRO cache ((simulator Q).answer {state with seed := replacement} input) =
      (runPartialRO cache ((simulator Q).answer state input)).map
        (fun answer => ({answer.1 with seed := replacement},answer.2)) := by
  cases hl : lookup state.publicLog input with
  | some d => simp [simulator, hl, runPartialRO, Except.map]
  | none =>
    cases hk : privateKey Q state.publicLog input with
    | some key => cases hc : cache key <;> simp [simulator, hl, hk, runPartialRO, hc, Except.map]
    | none => simp [simulator, hl, hk, runPartialRO, agree hl hk, Except.map]

theorem runPartial_replace_seed {Q : Nat} {Result : Type} (cache : RawKey Q → Option Digest32)
    (ro : RawKey Q → Digest32) (cacheAgrees : CacheAgrees cache ro)
    (iv : Digest32) (replacement : Seed) (state : State) (p : Program Result)
    (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining p)
    (agree : FallbackAgreement ro iv replacement state p remaining cap counted) :
    runPartial cache iv {state with seed := replacement} p remaining cap counted =
      runPartial cache iv state p remaining cap counted := by
  induction p generalizing state remaining with
  | done r => rfl
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      simp only [runPartial, partialAnswer_replace_seed cache state replacement input agree.1]
      cases hp : runPartialRO cache ((simulator Q).answer state input) with
      | error key => rfl
      | ok answer =>
        have he := runPartialRO_success cache ro cacheAgrees _ answer hp
        subst answer
        simp only [Except.map]
        congr 1
        exact ih _ _ _ _ _ agree.2
    | construction q valid =>
      simp only [runPartial]
      cases hc : cache (constructionKey Q iv q (counted.1.trans cap)) with
      | none => rfl
      | some answer =>
        have he := cacheAgrees _ answer hc
        subst answer
        dsimp only
        congr 1
        exact ih _ _ _ _ _ agree

theorem reconstructSeed_runPartial {Q : Nat} {Result : Type} (cache : RawKey Q → Option Digest32)
    (ro : RawKey Q → Digest32) (cacheAgrees : CacheAgrees cache ro)
    (iv : Digest32) (seed : Seed) (p : Program Result) (counted : Counts Q p) :
    let actual := runIdeal (simulator Q) ro iv ((simulator Q).initial seed) p Q (by omega) counted
    runPartial cache iv ((simulator Q).initial (reconstructSeed actual.view.observations))
      p Q (by omega) counted =
      runPartial cache iv ((simulator Q).initial seed) p Q (by omega) counted :=
  runPartial_replace_seed cache ro cacheAgrees iv _ _ p Q (by omega) counted
    (reconstructSeed_agrees ro iv seed p counted)

theorem runPartial_prefix {Q : Nat} {Result : Type} (cache : RawKey Q → Option Digest32)
    (ro : RawKey Q → Digest32) (cacheAgrees : CacheAgrees cache ro)
    (iv : Digest32) (state : State) (p : Program Result)
    (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining p) :
    ∃ suffix, (runIdeal (simulator Q) ro iv state p remaining cap counted).view.observations =
      (runPartial cache iv state p remaining cap counted).observations ++ suffix := by
  induction p generalizing state remaining with
  | done r => exact ⟨[],rfl⟩
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      cases hp : runPartialRO cache ((simulator Q).answer state input) with
      | error key =>
        refine ⟨(runIdeal (simulator Q) ro iv state
          (.ask (.primitive purpose input) next) remaining cap counted).view.observations,?_⟩
        simp [runPartial,hp]
      | ok answer =>
        have he := runPartialRO_success cache ro cacheAgrees _ answer hp
        subst answer
        obtain ⟨suffix,hs⟩ := ih (runRO ro ((simulator Q).answer state input)).1.2
          (runRO ro ((simulator Q).answer state input)).1.1 (remaining-1) (by omega) (counted.2 _)
        exact ⟨suffix,by simpa only [runIdeal, prepend, runPartial, hp, prependPartial,
          List.cons_append] using congrArg (⟨.primitive purpose input,
            (runRO ro ((simulator Q).answer state input)).1.2⟩ :: ·) hs⟩
    | construction q valid =>
      cases hc : cache (constructionKey Q iv q (counted.1.trans cap)) with
      | none =>
        refine ⟨(runIdeal (simulator Q) ro iv state
          (.ask (.construction q valid) next) remaining cap counted).view.observations,?_⟩
        simp [runPartial,hc]
      | some answer =>
        have he := cacheAgrees _ answer hc
        subst answer
        obtain ⟨suffix,hs⟩ := ih (ro (constructionKey Q iv q (counted.1.trans cap)))
          state (remaining-pathCost q) (by omega) (counted.2 _)
        exact ⟨suffix,by simpa only [runIdeal, prepend, runPartial, hc, prependPartial,
          List.cons_append] using congrArg (⟨.construction q valid,
            ro (constructionKey Q iv q (counted.1.trans cap))⟩ :: ·) hs⟩

/-- Public-only stopping rule. A raw-cache miss excludes the current
observation: its public answer cannot be consumed before that request is
physically acquired. Out-of-domain construction observations also stop. -/
def publicCut (Q : Nat) (iv : Digest32) (cache : RawKey Q → Option Digest32)
    (log : PublicLog) : List Observation → List Observation
  | [] => []
  | ⟨.primitive purpose input,answer⟩ :: rest =>
      match privateKey Q log input with
      | none => ⟨.primitive purpose input,answer⟩ ::
          publicCut Q iv cache (observe log input answer) rest
      | some key =>
          match cache key with
          | none => []
          | some _ => ⟨.primitive purpose input,answer⟩ ::
              publicCut Q iv cache (observe log input answer) rest
  | ⟨.construction q valid,answer⟩ :: rest =>
      if h : pathCost q ≤ Q then
        match cache (constructionKey Q iv q h) with
        | none => []
        | some _ => ⟨.construction q valid,answer⟩ :: publicCut Q iv cache log rest
      else []

theorem partialAnswer_cache {Q : Nat} (cache : RawKey Q → Option Digest32)
    (ro : RawKey Q → Digest32) (agrees : CacheAgrees cache ro) (state : State) (input : Node) :
    runPartialRO cache ((simulator Q).answer state input) =
      match privateKey Q state.publicLog input with
      | none => .ok (runRO ro ((simulator Q).answer state input)).1
      | some key =>
          match cache key with
          | none => .error key
          | some _ => .ok (runRO ro ((simulator Q).answer state input)).1 := by
  cases hl : lookup state.publicLog input with
  | some answer => simp [simulator, hl, privateKey, runPartialRO, runRO]
  | none =>
    cases hk : privateKey Q state.publicLog input with
    | none => simp [simulator, hl, hk, runPartialRO, runRO]
    | some key =>
      cases hc : cache key with
      | none => simp [simulator, hl, hk, hc, runPartialRO]
      | some answer =>
        have he := agrees key answer hc
        subst answer
        simp [simulator, hl, hk, hc, runPartialRO, runRO]

theorem publicCut_runPartial {Q : Nat} {Result : Type} (cache : RawKey Q → Option Digest32)
    (ro : RawKey Q → Digest32) (cacheAgrees : CacheAgrees cache ro)
    (iv : Digest32) (state : State) (p : Program Result)
    (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining p) :
    publicCut Q iv cache state.publicLog
      (runIdeal (simulator Q) ro iv state p remaining cap counted).view.observations =
      (runPartial cache iv state p remaining cap counted).observations := by
  induction p generalizing state remaining with
  | done r => rfl
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      have ht := ih (runRO ro ((simulator Q).answer state input)).1.2
        (runRO ro ((simulator Q).answer state input)).1.1 (remaining-1) (by omega) (counted.2 _)
      simp only [answer_publicLog] at ht
      simp only [runIdeal, prepend, publicCut, runPartial,
        partialAnswer_cache cache ro cacheAgrees state input]
      cases hk : privateKey Q state.publicLog input with
      | none => exact congrArg (⟨.primitive purpose input,
          (runRO ro ((simulator Q).answer state input)).1.2⟩ :: ·) ht
      | some key =>
        dsimp only
        cases hc : cache key with
        | none => rfl
        | some answer => exact congrArg (⟨.primitive purpose input,
            (runRO ro ((simulator Q).answer state input)).1.2⟩ :: ·) ht
    | construction q valid =>
      have hq : pathCost q ≤ Q := counted.1.trans cap
      simp only [runIdeal, prepend, publicCut, runPartial, hq, ↓reduceDIte]
      cases hc : cache (constructionKey Q iv q hq) with
      | none => rfl
      | some answer =>
        have he := cacheAgrees _ answer hc
        subst answer
        exact congrArg (⟨.construction q valid,ro (constructionKey Q iv q hq)⟩ :: ·)
          (ih _ _ _ _ _)

-- Executable smoke: real ROProgram interpretation, not an assumed simulator.
#eval do
  let digest (n : Nat) : Digest32 := fun _ => ⟨n % 256, Nat.mod_lt _ (by decide)⟩
  let block : Block64 := fun i => ⟨i.val,by omega⟩
  let seedNode : Node := ⟨digest 41,block,UInt64.ofNat (2^56),true⟩
  let internal : Node := ⟨digest 41,block,UInt64.ofNat (2*2^56+17),true⟩
  let terminal : Node := ⟨digest 2,block,UInt64.ofNat (6*2^56+23),true⟩
  let fallback : Seed := fun n => if isSeed n then n.cv else digest 2
  let ro : RawKey 8 → Digest32 := fun _ => digest 99
  let initial := (simulator 8).initial fallback
  let s := runRO ro ((simulator 8).answer initial seedNode)
  let i := runRO ro ((simulator 8).answer s.1.1 internal)
  let t := runRO ro ((simulator 8).answer i.1.1 terminal)
  let repeated := runRO ro ((simulator 8).answer t.1.1 terminal)
  let incomplete := runRO ro ((simulator 8).answer initial terminal)
  let clone : Node := { seedNode with cv := digest 42 }
  let c := runRO ro ((simulator 8).answer initial clone)
  let ct : Node := { terminal with cv := digest 42 }
  let chosen := runRO ro ((simulator 8).answer c.1.1 ct)
  let wrongLast : Node := { terminal with last := false }
  let program : Program Digest32 :=
    .ask (.primitive .direct seedNode) (fun _ =>
    .ask (.primitive .auxiliary internal) (fun _ =>
    .ask (.primitive .verification terminal) (fun _ =>
    .ask (.primitive .pow terminal) Program.done)))
  have counted : Counts 8 program := by simp [program, Counts, Query.cost]
  let execution := runIdeal (simulator 8) ro (digest 0) initial program 8 (by omega) counted
  let replayed := replay 8 (digest 0) [] execution.view.observations
  let paired := replayAnswers 8 (digest 0) [] execution.view.observations
  let publicSeed := reconstructSeed execution.view.observations
  let reconstructed := (simulator 8).initial publicSeed
  let rerun := runIdeal (simulator 8) ro (digest 0) reconstructed program 8 (by omega) counted
  let emptyCache : RawKey 8 → Option Digest32 := fun _ => none
  let fullCache : RawKey 8 → Option Digest32 := fun key => some (ro key)
  let stopped := runPartial emptyCache (digest 0) initial program 8 (by omega) counted
  let restopped := runPartial emptyCache (digest 0) reconstructed program 8 (by omega) counted
  let completed := runPartial fullCache (digest 0) reconstructed program 8 (by omega) counted
  let missed (r : PartialExecution 8 Digest32) :=
    match r.outcome with
    | .error key => some (expandKey key).message
    | .ok _ => none
  let coordinate : Coordinate := ⟨⟨digest 0,digest 1,[]⟩,.output 0⟩
  have valid : DuplexEncoding.Admissible coordinate := by
    simp [coordinate, DuplexEncoding.Admissible, DuplexEncoding.TerminalValid]
  let constructor : Program Digest32 := .ask (.construction coordinate valid) Program.done
  have constructorCounted : Counts 8 constructor := by
    simp [constructor, Counts, Query.cost, pathCost, DuplexEncoding.plan, coordinate]
  let constructed := runIdeal (simulator 8) ro (digest 0) initial constructor
    8 (by omega) constructorCounted
  let checks : List (String × Bool) := [
    ("seed fallback", s.2 == 0 && decide (s.1.2 = digest 41)),
    ("internal fallback", i.2 == 0 && decide (i.1.2 = digest 2)),
    ("terminal one raw query", t.2 == 1 && decide (t.1.2 = digest 99)),
    ("repeat cached no query", repeated.2 == 0 && decide (repeated.1.2 = t.1.2)),
    ("incomplete no raw query", incomplete.2 == 0),
    ("counted public-view replay", execution.simulatorQueries == 1 &&
      execution.primitiveCost == 4 && decide (execution.view.result = digest 99) &&
      decide (replayed.map (fun k => (expandKey k).template) =
        [[(terminal.tweak,true),(internal.tweak,true),(seedNode.tweak,true)]]) &&
      decide (replayed.map (fun k => (expandKey k).message) =
        [[(none,block),(none,block),(some (digest 41),block)]])),
    ("paired public raw answer", decide (paired.map Prod.snd = [digest 99]) &&
      decide (paired.map (fun (entry : RawKey 8 × Digest32) => (expandKey entry.1).message) =
        [[(none,block),(none,block),(some (digest 41),block)]])),
    ("reconstructed fallback only", decide (publicSeed seedNode = digest 41) &&
      decide (publicSeed internal = digest 2) && decide (publicSeed terminal = digest 99) &&
      decide (fallback terminal = digest 2) && decide (publicSeed wrongLast = zeroDigest)),
    ("reconstructed actual execution", rerun.simulatorQueries == 1 &&
      decide (rerun.view.result = digest 99) &&
      decide (rerun.view.observations.map Observation.answer =
        [digest 41,digest 2,digest 99,digest 99])),
    ("partial first missing raw key", decide (stopped.observations.map Observation.answer =
        [digest 41,digest 2]) &&
      decide (missed stopped = some [(none,block),(none,block),(some (digest 41),block)])),
    ("reconstructed partial prefix", decide (restopped.observations.map Observation.answer =
        [digest 41,digest 2]) &&
      decide (missed restopped = some [(none,block),(none,block),(some (digest 41),block)])),
    ("partial full-cache completion", decide (completed.observations.map Observation.answer =
        [digest 41,digest 2,digest 99,digest 99]) &&
      (match completed.outcome with | .ok answer => decide (answer = digest 99) | .error _ => false)),
    ("public cut before missing reply", decide (
      (publicCut 8 (digest 0) emptyCache [] execution.view.observations).map Observation.answer =
        [digest 41,digest 2])),
    ("public cut full cache", decide (
      (publicCut 8 (digest 0) fullCache [] execution.view.observations).map Observation.answer =
        [digest 41,digest 2,digest 99,digest 99])),
    ("public cut cached input needs no cache", decide (
      (publicCut 8 (digest 0) emptyCache t.1.1.publicLog
        [⟨.primitive .direct terminal,digest 99⟩]).map Observation.answer = [digest 99])),
    ("public cut incomplete needs no cache", decide (
      (publicCut 8 (digest 0) emptyCache []
        [⟨.primitive .direct terminal,digest 2⟩]).map Observation.answer = [digest 2])),
    ("public cut construction miss", (publicCut 8 (digest 0) emptyCache []
        constructed.view.observations).isEmpty),
    ("public cut construction hit", decide (
      (publicCut 8 (digest 0) fullCache [] constructed.view.observations).map Observation.answer =
        [digest 99])),
    ("chosen seed CV", chosen.2 == 1 &&
      decide ((privateKey 8 c.1.1.publicLog ct).map (fun k => (expandKey k).message) =
        some [(none,block),(some (digest 42),block)])),
    ("exact blocks tweaks last", decide (
      (privateKey 8 i.1.1.publicLog terminal).map (fun k => (expandKey k).template) =
        some [(terminal.tweak,true),(internal.tweak,true),(seedNode.tweak,true)])),
    ("last flag checked", (privateKey 8 i.1.1.publicLog wrongLast).isNone),
    ("public answer stored", decide (t.1.1.publicLog =
      [(terminal,digest 99),(internal,digest 2),(seedNode,digest 41)]))]
  for (label,ok) in checks do
    if ok = true then IO.println s!"{label}: ok" else throw (IO.userError s!"{label}: FAILED")

#print axioms canonical_terminal
#print axioms privateKey_compression
#print axioms recognized_complete
#print axioms initial_budgetSafe
#print axioms simulatorBound
#print axioms replay_actual
#print axioms replayAnswers_consistent
#print axioms reconstructSeed_agrees
#print axioms reconstructSeed_runIdeal
#print axioms reconstructSeed_actualRequests
#print axioms runPartialRO_first_miss
#print axioms reconstructSeed_runPartial
#print axioms runPartial_prefix
#print axioms replayAnswers_source_bound
#print axioms publicCut_runPartial

end Whir.DuplexPublicSimulator
