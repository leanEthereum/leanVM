import Whir.PublicCompressionCouplingCache
import Whir.PublicCompressionCouplingPublicTrace
import Whir.PublicCompressionCouplingIdealLateLinks
import Whir.PublicCompressionCouplingTargetCache

/-! Actual public-phase preservation of missed terminal recognition. The
computed late alarm concerns public Seed queries, not hidden causal reads.
Recognized RO terminals are never body nodes and are erased structurally. -/
namespace Whir.PublicCompressionCouplingLateRecognition
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame TypedOracleCompiler
open TypedFiatShamirGame RawOracleCoupling DuplexPublicSimulator
open PublicCompressionCouplingRecognition PublicCompressionCouplingMixed

section Generic
variable {K R S : Type} [DecidableEq K]

 theorem alarm_pad (inputCV : K → Option Digest32) (table : K → Digest32)
    {n m : Nat} (h : n ≤ m) (p : Sampling K (fun _ => Digest32) R n)
    (cache : K → Option Digest32) (history : List Digest32) :
    PublicCompressionCouplingIdealLateLinks.alarm inputCV table (Sampling.pad h p) cache history =
      PublicCompressionCouplingIdealLateLinks.alarm inputCV table p cache history := by
  induction p generalizing m cache history with
  | ret r => simp only [Sampling.pad,PublicCompressionCouplingIdealLateLinks.alarm]
  | @draw n key next ih =>
    cases m with
    | zero => omega
    | succ m =>
      simp only [Sampling.pad,PublicCompressionCouplingIdealLateLinks.alarm]
      cases hit : cache key with
      | some answer => exact ih answer (m:=m) (by omega) cache _
      | none =>
        exact congrArg (decide (table key ∈ history.toFinset) || ·)
          (ih (table key) (m:=m) (by omega) (put cache key (table key)) _)

 theorem alarm_map {Q : Nat} [DecidableEq (Key Q)]
    (inputCV : Key Q → Option Digest32) (table : Key Q → Digest32)
    {n : Nat} (f : R → S) (p : Computation Q R n)
    (cache : Key Q → Option Digest32) (history : List Digest32) :
    PublicCompressionCouplingIdealLateLinks.alarm inputCV table
      (PublicCompressionCouplingMixed.Computation.map f p) cache history =
      PublicCompressionCouplingIdealLateLinks.alarm inputCV table p cache history := by
  induction p generalizing cache history with
  | ret r => rfl
  | draw key next ih =>
    simp only [PublicCompressionCouplingMixed.Computation.map,PublicCompressionCouplingIdealLateLinks.alarm]
    cases hit : cache key with
    | some answer => exact ih answer cache _
    | none =>
      exact congrArg (decide (table key ∈ history.toFinset) || ·)
        (ih (table key) (put cache key (table key)) _)

 theorem memo_pad (table : K → Digest32) {n m : Nat} (h : n ≤ m)
    (p : Sampling K (fun _ => Digest32) R n) (cache : K → Option Digest32) :
    Sampling.eval table (memo (Sampling.pad h p) cache) = Sampling.eval table (memo p cache) := by
  induction p generalizing m cache with
  | ret r => simp only [Sampling.pad,memo,Sampling.eval]
  | @draw n key next ih =>
    cases m with
    | zero => omega
    | succ m =>
      simp only [Sampling.pad,memo]
      cases hit : cache key with
      | some answer => simp only [Sampling.eval_pad]; exact ih answer (m:=m) (by omega) cache
      | none => simp only [Sampling.eval]; exact ih (table key) (m:=m) (by omega) _

 theorem memo_map_cache {Q : Nat} [DecidableEq (Key Q)] (table : Key Q → Digest32)
    {n : Nat} (f : R → S) (p : Computation Q R n) (cache : Key Q → Option Digest32) :
    (Sampling.eval table (memo (PublicCompressionCouplingMixed.Computation.map f p) cache)).2 =
      (Sampling.eval table (memo p cache)).2 := by
  induction p generalizing cache with
  | ret r => rfl
  | draw key next ih =>
    simp only [PublicCompressionCouplingMixed.Computation.map,memo]
    cases hit : cache key with
    | some answer => simp only [Sampling.eval_pad]; exact ih answer cache
    | none => simp only [Sampling.eval]; exact ih (table key) _

 theorem memo_bind (table : K → Digest32) {n m : Nat}
    (p : Sampling K (fun _ => Digest32) R n) (f : R → Sampling K (fun _ => Digest32) S m)
    (cache : K → Option Digest32)
    (consistent : ∀ key answer, cache key=some answer → table key=answer) :
    Sampling.eval table (memo (Sampling.bind p f) cache) =
      Sampling.eval table (memo (f (Sampling.eval table p)) (Sampling.eval table (memo p cache)).2) := by
  induction p generalizing cache with
  | ret r => simp only [Sampling.bind,memo_pad,memo,Sampling.eval]
  | draw key next ih =>
    simp only [Sampling.bind,memo_pad,memo,Sampling.eval]
    cases hit : cache key with
    | some answer =>
      simp only [Sampling.eval_pad]
      rw [consistent key answer hit]
      exact ih answer cache consistent
    | none =>
      simp only [Sampling.eval]
      exact ih (table key) (put cache key (table key))
        (PublicCompressionCouplingTargetCache.put_consistent table cache consistent key)

 def historyTrace (inputCV : K → Option Digest32) (history : List Digest32)
    (trace : List (Sigma (fun _ : K => Digest32))) : List Digest32 :=
  trace.foldl (fun prior entry => PublicCompressionCouplingIdealLateLinks.advance inputCV entry.1 prior) history

 theorem alarm_bind (inputCV : K → Option Digest32) (table : K → Digest32) {n m : Nat}
    (p : Sampling K (fun _ => Digest32) R n) (f : R → Sampling K (fun _ => Digest32) S m)
    (cache : K → Option Digest32) (history : List Digest32)
    (consistent : ∀ key answer, cache key=some answer → table key=answer) :
    PublicCompressionCouplingIdealLateLinks.alarm inputCV table (Sampling.bind p f) cache history =
      (PublicCompressionCouplingIdealLateLinks.alarm inputCV table p cache history ||
        PublicCompressionCouplingIdealLateLinks.alarm inputCV table (f (Sampling.eval table p))
          (Sampling.eval table (memo p cache)).2
          (historyTrace inputCV history (Sampling.execute table p).2)) := by
  induction p generalizing cache history with
  | ret r => simp only [Sampling.bind,alarm_pad,PublicCompressionCouplingIdealLateLinks.alarm,memo,
      Sampling.eval,Sampling.execute,
      historyTrace,List.foldl_nil,Bool.false_or]
  | draw key next ih =>
    simp only [Sampling.bind,alarm_pad,PublicCompressionCouplingIdealLateLinks.alarm,memo,
      Sampling.eval,Sampling.execute,
      historyTrace,List.foldl_cons]
    cases hit : cache key with
    | some answer =>
      simp only [Sampling.eval_pad]
      rw [consistent key answer hit]
      exact ih answer cache _ consistent
    | none =>
      simp only [Sampling.eval]
      rw [ih (table key) (put cache key (table key)) _
        (PublicCompressionCouplingTargetCache.put_consistent table cache consistent key)]
      exact (Bool.or_assoc _ _ _).symm
end Generic

/-- Only nonterminal previous inputs can be chaining positions of a body.
Earlier recognized RO terminals need not be included in the late history. -/
theorem erase_nonlate_nonterminal {log : PublicLog} {input : Node} {answer cv : Digest32}
    {ns : List Node} (tree : PublicBody (observe log input answer) cv ns)
    (avoid : ∀ n d, (n,d)∈log → ¬isTerminal n → answer≠n.cv)
    (root : answer≠cv) : PublicBody log cv ns := by
  induction tree with
  | seed member seed =>
    rcases List.mem_cons.mp member with equal | old
    · exact False.elim (root (congrArg Prod.snd equal).symm)
    · exact PublicBody.seed old seed
  | @step n d rest member internal child ih =>
    rcases List.mem_cons.mp member with equal | old
    · exact False.elim (root (congrArg Prod.snd equal).symm)
    · exact PublicBody.step old internal (ih (avoid n d old (fun terminal => terminal_not_internal terminal internal)))

 theorem recognized_none_after_nonlate_nonterminal {log : PublicLog} {input target : Node}
    {answer : Digest32} (functional : Functional log) (clean : ¬OutputCollision log)
    (incomplete : recognized log target=none)
    (avoid : ∀ n d, (n,d)∈log → ¬isTerminal n → answer≠n.cv) (root : answer≠target.cv) :
    recognized (observe log input answer) target=none := by
  cases found : recognized (observe log input answer) target with
  | none => rfl
  | some ns =>
    obtain ⟨rest,rfl,body⟩ := recognized_publicBody found
    have old := erase_nonlate_nonterminal body avoid root
    have terminal := (recognized_sound found).1
    obtain ⟨t,tail,equal,ht,hb⟩ := terminal
    have head : t=target := by simpa using (congrArg List.head? equal).symm
    subst t
    have prior := recognized_complete functional clean ht old
    rw [incomplete] at prior
    cases prior

 theorem recognized_none_after_terminal {log : PublicLog} {input target : Node} {answer : Digest32}
    (functional : Functional log) (clean : ¬OutputCollision log) (terminal : isTerminal input)
    (incomplete : recognized log target=none) : recognized (observe log input answer) target=none := by
  cases found : recognized (observe log input answer) target with
  | none => rfl
  | some ns =>
    obtain ⟨rest,rfl,body⟩ := recognized_publicBody found
    have old := PublicBody.erase_terminal terminal body
    obtain ⟨t,tail,equal,ht,hb⟩ := (recognized_sound found).1
    have head : t=target := by simpa using (congrArg List.head? equal).symm
    subst t
    have prior := recognized_complete functional clean ht old
    rw [incomplete] at prior
    cases prior

 theorem recognized_none_after_repeat {log : PublicLog} {input target : Node} {answer : Digest32}
    (functional : Functional log) (clean : ¬OutputCollision log) (old : (input,answer)∈log)
    (incomplete : recognized log target=none) : recognized (observe log input answer) target=none := by
  cases found : recognized (observe log input answer) target with
  | none => rfl
  | some ns =>
    obtain ⟨rest,rfl,body⟩ := recognized_publicBody found
    have priorBody := PublicBody.erase_repeat old body
    obtain ⟨t,tail,equal,ht,hb⟩ := (recognized_sound found).1
    have head : t=target := by simpa using (congrArg List.head? equal).symm
    subst t
    have prior := recognized_complete functional clean ht priorBody
    rw [incomplete] at prior
    cases prior

 theorem privateKey_none_recognized_none {Q : Nat} {log : PublicLog} {input : Node}
    (fresh : lookup log input=none) (missing : privateKey Q log input=none)
    (budget : log.length+1≤Q) : recognized log input=none := by
  cases found : recognized log input with
  | none => rfl
  | some nodes =>
    obtain ⟨key,hit,extracted⟩ := privateKey_of_recognized fresh found budget
    rw [missing] at hit
    cases hit

def SeedRecorded {Q : Nat} (cache : Key Q → Option Digest32) (log : PublicLog) : Prop :=
  ∀ input answer, cache (.inl input)=some answer → (input,answer)∈log

def InlCVTracked {Q : Nat} (cache : Key Q → Option Digest32) (history : List Digest32) : Prop :=
  ∀ input answer, cache (.inl input)=some answer → input.cv∈history.toFinset

def NonterminalCVTracked (log : PublicLog) (history : List Digest32) : Prop :=
  ∀ input answer, (input,answer)∈log → ¬isTerminal input → input.cv∈history.toFinset

def StableFallbacks {Q : Nat} (cache : Key Q → Option Digest32) (log : PublicLog) : Prop :=
  ∀ input answer, cache (.inl input)=some answer → isTerminal input → recognized log input=none

open Classical in
theorem put_hit {K : Type} [DecidableEq K] (cache : K → Option Digest32) (key : K) (answer : Digest32)
    (hit : cache key=some answer) : put cache key answer=cache := by
  funext j
  by_cases same : j=key
  · subst j; simp only [put_self,hit]
  · exact put_other _ _ _ _ same

theorem seed_cache_fresh {Q : Nat} (cache : Key Q → Option Digest32) (log : PublicLog)
    (recorded : SeedRecorded cache log) (input : Node) (fresh : lookup log input=none) :
    cache (.inl input)=none := by
  cases hit : cache (.inl input) with
  | none => rfl
  | some answer =>
    obtain ⟨value,stored⟩ := lookup_exists (recorded input answer hit)
    rw [fresh] at stored
    cases stored

theorem history_insert {cv : Digest32} {history : List Digest32} {value : Digest32}
    (member : value∈history.toFinset) : value∈(cv::history).toFinset := by
  simp only [List.mem_toFinset] at member ⊢
  exact List.mem_cons_of_mem _ member

theorem privateKey_terminal {Q : Nat} {log : PublicLog} {input : Node} {key : RawKey Q}
    (found : privateKey Q log input=some key) : isTerminal input := by
  obtain ⟨nodes,recognized,complete,extracted⟩ := privateKey_sound found
  by_contra notTerminal
  simp [DuplexPublicSimulator.recognized,notTerminal] at recognized

open Classical in
theorem inl_put_inr {Q : Nat} (cache : Key Q → Option Digest32) (key : RawKey Q)
    (value : Digest32) (input : Node) :
    (put cache (.inr key) value) (.inl input)=cache (.inl input) := by
  simp [put]

open Classical in
theorem inr_preserves {Q : Nat} (cache : Key Q → Option Digest32) (log : PublicLog)
    (history : List Digest32) (key : RawKey Q) (value : Digest32)
    (recorded : SeedRecorded cache log) (tracked : InlCVTracked cache history)
    (stable : StableFallbacks cache log) :
    SeedRecorded (put cache (.inr key) value) log ∧
    InlCVTracked (put cache (.inr key) value) history ∧
    StableFallbacks (put cache (.inr key) value) log := by
  constructor
  · intro input answer stored
    exact recorded input answer (by simpa only [inl_put_inr] using stored)
  constructor
  · intro input answer stored
    exact tracked input answer (by simpa only [inl_put_inr] using stored)
  · intro input answer stored terminal
    exact stable input answer (by simpa only [inl_put_inr] using stored) terminal

theorem repeat_preserves {Q : Nat} (cache : Key Q → Option Digest32) (log : PublicLog)
    (history : List Digest32) (input : Node) (answer : Digest32)
    (functional : Functional log) (clean : ¬OutputCollision log) (old : (input,answer)∈log)
    (recorded : SeedRecorded cache log) (tracked : NonterminalCVTracked log history)
    (stable : StableFallbacks cache log) :
    SeedRecorded cache (observe log input answer) ∧
    NonterminalCVTracked (observe log input answer) history ∧
    StableFallbacks cache (observe log input answer) := by
  constructor
  · intro node digest stored
    exact List.mem_cons_of_mem _ (recorded node digest stored)
  constructor
  · intro node digest member nonterminal
    rcases List.mem_cons.mp member with equal | prior
    · cases equal; exact tracked input answer old nonterminal
    · exact tracked node digest prior nonterminal
  · intro node digest stored terminal
    exact recognized_none_after_repeat functional clean old (stable node digest stored terminal)

theorem terminal_preserves {Q : Nat} (cache : Key Q → Option Digest32) (log : PublicLog)
    (history : List Digest32) (input : Node) (answer : Digest32)
    (functional : Functional log) (clean : ¬OutputCollision log) (terminal : isTerminal input)
    (recorded : SeedRecorded cache log) (tracked : NonterminalCVTracked log history)
    (stable : StableFallbacks cache log) :
    SeedRecorded cache (observe log input answer) ∧
    NonterminalCVTracked (observe log input answer) history ∧
    StableFallbacks cache (observe log input answer) := by
  constructor
  · intro node digest stored
    exact List.mem_cons_of_mem _ (recorded node digest stored)
  constructor
  · intro node digest member nonterminal
    rcases List.mem_cons.mp member with equal | prior
    · cases equal; exact False.elim (nonterminal terminal)
    · exact tracked node digest prior nonterminal
  · intro node digest stored nodeTerminal
    exact recognized_none_after_terminal functional clean terminal (stable node digest stored nodeTerminal)

open Classical in
theorem fallback_preserves {Q : Nat} (cache : Key Q → Option Digest32) (log : PublicLog)
    (history : List Digest32) (input : Node) (answer : Digest32)
    (functional : Functional log) (clean : ¬OutputCollision log)
    (incomplete : recognized log input=none) (avoid : answer∉history.toFinset)
    (recorded : SeedRecorded cache log) (tracked : InlCVTracked cache history)
    (nonterminalTracked : NonterminalCVTracked log history) (stable : StableFallbacks cache log) :
    SeedRecorded (put cache (.inl input) answer) (observe log input answer) ∧
    InlCVTracked (put cache (.inl input) answer) (input.cv::history) ∧
    NonterminalCVTracked (observe log input answer) (input.cv::history) ∧
    StableFallbacks (put cache (.inl input) answer) (observe log input answer) := by
  constructor
  · intro node digest stored
    by_cases same : node=input
    · subst node
      simp only [put_self,Option.some.injEq] at stored
      subst digest
      exact List.mem_cons.mpr (Or.inl rfl)
    · have keys : (Sum.inl node : Key Q)≠.inl input := by intro equal; exact same (Sum.inl.inj equal)
      exact List.mem_cons_of_mem _ (recorded node digest (by simpa only [put_other _ _ _ _ keys] using stored))
  constructor
  · intro node digest stored
    by_cases same : node=input
    · subst node; simp
    · have keys : (Sum.inl node : Key Q)≠.inl input := by intro equal; exact same (Sum.inl.inj equal)
      exact history_insert (tracked node digest (by simpa only [put_other _ _ _ _ keys] using stored))
  constructor
  · intro node digest member nonterminal
    rcases List.mem_cons.mp member with equal | prior
    · cases equal; simp
    · exact history_insert (nonterminalTracked node digest prior nonterminal)
  · intro node digest stored terminal
    by_cases inputTerminal : isTerminal input
    · apply recognized_none_after_terminal functional clean inputTerminal
      by_cases same : node=input
      · subst node; exact incomplete
      · have keys : (Sum.inl node : Key Q)≠.inl input := by intro equal; exact same (Sum.inl.inj equal)
        exact stable node digest (by simpa only [put_other _ _ _ _ keys] using stored) terminal
    · have same : node≠input := by intro equal; exact inputTerminal (equal ▸ terminal)
      have keys : (Sum.inl node : Key Q)≠.inl input := by intro equal; exact same (Sum.inl.inj equal)
      have old : cache (.inl node)=some digest := by simpa only [put_other _ _ _ _ keys] using stored
      apply recognized_none_after_nonlate_nonterminal functional clean (stable node digest old terminal)
      · intro prior value member nonterminal equal
        exact avoid (equal ▸ nonterminalTracked prior value member nonterminal)
      · intro equal
        exact avoid (equal ▸ tracked node digest old)

open Classical in
theorem memo_singleton {K R : Type} [DecidableEq K] (table : K → Digest32) (key : K) (payload : Digest32 → R)
    (cache : K → Option Digest32)
    (consistent : ∀ key answer, cache key=some answer → table key=answer) :
    Sampling.eval table (memo (.draw key (fun d => .ret (n:=0) (payload d))) cache) =
      (payload (table key),put cache key (table key)) := by
  cases hit : cache key with
  | some answer =>
    simp only [memo,hit,Sampling.eval_pad,Sampling.eval]
    rw [consistent key answer hit,put_hit cache key answer hit]
  | none => simp only [memo,hit,Sampling.eval]

open Classical in
theorem primitive_preserves (Q : Nat) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (cache : Key Q → Option Digest32) (log : PublicLog) (history : List Digest32) (input : Node)
    (consistent : ∀ key answer, cache key=some answer → oracle seedTable ro key=answer)
    (functional : Functional log) (clean : ¬OutputCollision log) (budget : log.length+1≤Q)
    (recorded : SeedRecorded cache log) (tracked : InlCVTracked cache history)
    (nonterminalTracked : NonterminalCVTracked log history) (stable : StableFallbacks cache log)
    (quiet : PublicCompressionCouplingIdealLateLinks.alarm PublicCompressionCouplingIdealLateLinks.mixedCV
      (oracle seedTable ro) (primitiveCalls Q log input) cache history=false) :
    let result := Sampling.eval (oracle seedTable ro) (primitiveCalls Q log input)
    let finalCache := (Sampling.eval (oracle seedTable ro) (memo (primitiveCalls Q log input) cache)).2
    let finalHistory := historyTrace PublicCompressionCouplingIdealLateLinks.mixedCV history
      (Sampling.execute (oracle seedTable ro) (primitiveCalls Q log input)).2
    SeedRecorded finalCache result.1 ∧ InlCVTracked finalCache finalHistory ∧
      NonterminalCVTracked result.1 finalHistory ∧ StableFallbacks finalCache result.1 := by
  cases hit : lookup log input with
  | some answer =>
    simp only [primitiveCalls,hit,Sampling.eval,memo,Sampling.execute,historyTrace,List.foldl_nil]
    have preserved := repeat_preserves cache log history input answer functional clean (lookup_mem hit)
      recorded nonterminalTracked stable
    exact ⟨preserved.1,tracked,preserved.2.1,preserved.2.2⟩
  | none =>
    cases found : privateKey Q log input with
    | some key =>
      have terminal := privateKey_terminal found
      have changed := inr_preserves cache log history key (ro key) recorded tracked stable
      have preserved := terminal_preserves (put cache (.inr key) (ro key)) log history input (ro key)
        functional clean terminal changed.1 nonterminalTracked changed.2.2
      simpa only [primitiveCalls,hit,found,Sampling.eval,memo_singleton _ _ _ _ consistent,
        Sampling.execute,oracle,historyTrace,List.foldl_cons,List.foldl_nil,
        PublicCompressionCouplingIdealLateLinks.advance,PublicCompressionCouplingIdealLateLinks.mixedCV]
        using (show SeedRecorded (put cache (.inr key) (ro key)) (observe log input (ro key)) ∧
          InlCVTracked (put cache (.inr key) (ro key)) history ∧
          NonterminalCVTracked (observe log input (ro key)) history ∧
          StableFallbacks (put cache (.inr key) (ro key)) (observe log input (ro key)) from
          ⟨preserved.1,changed.2.1,preserved.2.1,preserved.2.2⟩)
    | none =>
      have fresh := seed_cache_fresh cache log recorded input hit
      simp only [primitiveCalls,hit,found,PublicCompressionCouplingIdealLateLinks.alarm,fresh,
        PublicCompressionCouplingIdealLateLinks.alarm,oracle,Bool.or_false] at quiet
      have avoid := of_decide_eq_false quiet
      have incomplete := privateKey_none_recognized_none hit found budget
      have preserved := fallback_preserves cache log history input (seedTable input) functional clean
        incomplete avoid recorded tracked nonterminalTracked stable
      simpa only [primitiveCalls,hit,found,Sampling.eval,memo,fresh,Sampling.execute,oracle,
        historyTrace,List.foldl_cons,List.foldl_nil,PublicCompressionCouplingIdealLateLinks.advance,
        PublicCompressionCouplingIdealLateLinks.mixedCV] using preserved

open Classical in
theorem alarm_draw_quiet {K R : Type} [DecidableEq K] (inputCV : K → Option Digest32)
    (table : K → Digest32) (key : K) {n : Nat}
    (next : Digest32 → Sampling K (fun _ => Digest32) R n) (cache : K → Option Digest32)
    (history : List Digest32)
    (consistent : ∀ key answer, cache key=some answer → table key=answer)
    (quiet : PublicCompressionCouplingIdealLateLinks.alarm inputCV table (.draw key next) cache history=false) :
    PublicCompressionCouplingIdealLateLinks.alarm inputCV table (next (table key))
      (put cache key (table key)) (PublicCompressionCouplingIdealLateLinks.advance inputCV key history)=false := by
  cases hit : cache key with
  | some answer =>
    simp only [PublicCompressionCouplingIdealLateLinks.alarm,hit] at quiet
    rw [consistent key answer hit,put_hit cache key answer hit]
    exact quiet
  | none =>
    simp only [PublicCompressionCouplingIdealLateLinks.alarm,hit,Bool.or_eq_false_iff] at quiet
    exact quiet.2

open Classical in
theorem memo_draw {K R : Type} [DecidableEq K] (table : K → Digest32) (key : K) {n : Nat}
    (next : Digest32 → Sampling K (fun _ => Digest32) R n) (cache : K → Option Digest32)
    (consistent : ∀ key answer, cache key=some answer → table key=answer) :
    Sampling.eval table (memo (.draw key next) cache) =
      Sampling.eval table (memo (next (table key)) (put cache key (table key))) := by
  cases hit : cache key with
  | some answer =>
    simp only [memo,hit,Sampling.eval_pad]
    rw [consistent key answer hit,put_hit cache key answer hit]
  | none => simp only [memo,hit,Sampling.eval]

theorem primitive_functional (Q : Nat) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (log : PublicLog) (input : Node) (functional : Functional log) :
    Functional (Sampling.eval (oracle seedTable ro) (primitiveCalls Q log input)).1 := by
  simpa only [primitiveCalls_actual] using
    answer_functional Q ro ({seed:=seedTable,publicLog:=log} : DuplexPublicSimulator.State) input functional

theorem primitive_result_log (Q : Nat) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (log : PublicLog) (input : Node) :
    (Sampling.eval (oracle seedTable ro) (primitiveCalls Q log input)).1 =
      DuplexPublicSimulator.observe log input
        (Sampling.eval (oracle seedTable ro) (primitiveCalls Q log input)).2 := by
  simpa only [primitiveCalls_actual] using
    answer_publicLog Q ro ({seed:=seedTable,publicLog:=log} : DuplexPublicSimulator.State) input

theorem primitive_log_length (Q : Nat) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (log : PublicLog) (input : Node) :
    (Sampling.eval (oracle seedTable ro) (primitiveCalls Q log input)).1.length=log.length+1 := by
  rw [primitive_result_log]
  simp only [DuplexPublicSimulator.observe,List.length_cons]

theorem clean_initial_log (log : PublicLog) (observations : List Observation)
    (clean : ¬OutputCollision (finalLog log observations)) : ¬OutputCollision log := by
  rintro ⟨a,b,d,ha,hb,ne⟩
  exact clean ⟨a,b,d,finalLog_contains log observations _ ha,finalLog_contains log observations _ hb,ne⟩

open Classical in
theorem compile_stable {R : Type} (Q : Nat) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (iv : Digest32) (p : Program R) :
    ∀ (log : PublicLog) (remaining : Nat) (cap : remaining≤Q) (counted : Counts remaining p)
      (cache : Key Q → Option Digest32) (history : List Digest32),
      (∀ key answer, cache key=some answer → oracle seedTable ro key=answer) →
      Functional log → log.length+remaining≤Q →
      SeedRecorded cache log → InlCVTracked cache history → NonterminalCVTracked log history →
      StableFallbacks cache log →
      PublicCompressionCouplingIdealLateLinks.alarm PublicCompressionCouplingIdealLateLinks.mixedCV
        (oracle seedTable ro) (compile Q iv log p remaining cap counted) cache history=false →
      ¬OutputCollision (finalLog log
        (Sampling.eval (oracle seedTable ro) (compile Q iv log p remaining cap counted)).observations) →
      StableFallbacks
        (Sampling.eval (oracle seedTable ro) (memo (compile Q iv log p remaining cap counted) cache)).2
        (finalLog log (Sampling.eval (oracle seedTable ro) (compile Q iv log p remaining cap counted)).observations) := by
  induction p with
  | done result =>
    intro log remaining cap counted cache history consistent functional budget recorded tracked nonterminalTracked stable quiet clean
    simpa only [PublicCompressionCouplingMixed.compile,memo,Sampling.eval,finalLog] using stable
  | ask query next ih =>
    intro log remaining cap counted cache history consistent functional budget recorded tracked nonterminalTracked stable quiet clean
    have oldClean := clean_initial_log log _ clean
    cases query with
    | primitive purpose input =>
      simp only [PublicCompressionCouplingMixed.compile,alarm_pad,alarm_bind _ _ _ _ _ _ consistent,Bool.or_eq_false_iff] at quiet
      let stage := primitiveCalls Q log input
      let result := Sampling.eval (oracle seedTable ro) stage
      let nextCache := (Sampling.eval (oracle seedTable ro) (memo stage cache)).2
      let nextHistory := historyTrace PublicCompressionCouplingIdealLateLinks.mixedCV history
        (Sampling.execute (oracle seedTable ro) stage).2
      have stageBudget : log.length+1≤Q := by have hc : 1≤remaining := counted.1; omega
      have preserved := primitive_preserves Q seedTable ro cache log history input consistent
        functional oldClean stageBudget recorded tracked nonterminalTracked stable quiet.1
      have nextQuiet : PublicCompressionCouplingIdealLateLinks.alarm PublicCompressionCouplingIdealLateLinks.mixedCV
          (oracle seedTable ro)
          (compile Q iv result.1 (next result.2) (remaining-1) (by omega) (counted.2 _))
          nextCache nextHistory=false := by
        simpa only [alarm_map] using quiet.2
      have nextBudget : result.1.length+(remaining-1)≤Q := by
        dsimp only [result,stage]
        rw [primitive_log_length]
        have hc : 1≤remaining := counted.1
        omega
      have nextClean : ¬OutputCollision (finalLog result.1
          (Sampling.eval (oracle seedTable ro)
            (compile Q iv result.1 (next result.2) (remaining-1) (by omega) (counted.2 _))).observations) := by
        simpa only [PublicCompressionCouplingMixed.compile,Sampling.eval_pad,Sampling.eval_bind,
          PublicCompressionCouplingMixed.Computation.eval_map,DuplexRawProgram.observe,finalLog,
          ←primitive_result_log Q seedTable ro log input] using clean
      have child := ih result.2 result.1 (remaining-1) (by omega) (counted.2 _) nextCache nextHistory
        (memo_eval_consistent stage cache (oracle seedTable ro) consistent)
        (primitive_functional Q seedTable ro log input functional) nextBudget
        preserved.1 preserved.2.1 preserved.2.2.1 preserved.2.2.2 nextQuiet nextClean
      simpa only [PublicCompressionCouplingMixed.compile,memo_pad,memo_bind _ _ _ _ consistent,memo_map_cache,
        Sampling.eval_pad,Sampling.eval_bind,PublicCompressionCouplingMixed.Computation.eval_map,
        DuplexRawProgram.observe,finalLog,←primitive_result_log Q seedTable ro log input] using child
    | construction coordinate valid =>
      let key := constructionKey Q iv coordinate (counted.1.trans cap)
      let nextCache := put cache (.inr key) (ro key)
      simp only [PublicCompressionCouplingMixed.compile,alarm_pad] at quiet
      have nextQuiet := alarm_draw_quiet PublicCompressionCouplingIdealLateLinks.mixedCV
        (oracle seedTable ro) (.inr key) _ cache history consistent quiet
      simp only [alarm_map,PublicCompressionCouplingIdealLateLinks.advance,
        PublicCompressionCouplingIdealLateLinks.mixedCV,oracle] at nextQuiet
      have preserved := inr_preserves cache log history key (ro key) recorded tracked stable
      have nextBudget : log.length+(remaining-pathCost coordinate)≤Q := by omega
      have nextClean : ¬OutputCollision (finalLog log
          (Sampling.eval (oracle seedTable ro)
            (compile Q iv log (next (ro key)) (remaining-pathCost coordinate) (by omega)
              (counted.2 _))).observations) := by
        simpa only [PublicCompressionCouplingMixed.compile,Sampling.eval_pad,Sampling.eval,
          PublicCompressionCouplingMixed.Computation.eval_map,oracle,DuplexRawProgram.observe,finalLog] using clean
      have child := ih (ro key) log (remaining-pathCost coordinate) (by omega) (counted.2 _) nextCache history
        (PublicCompressionCouplingTargetCache.put_consistent (oracle seedTable ro) cache consistent (.inr key))
        functional nextBudget preserved.1 preserved.2.1 nonterminalTracked preserved.2.2 nextQuiet nextClean
      simpa only [PublicCompressionCouplingMixed.compile,memo_pad,memo_draw _ _ _ _ consistent,memo_map_cache,
        Sampling.eval_pad,Sampling.eval,PublicCompressionCouplingMixed.Computation.eval_map,
        oracle,DuplexRawProgram.observe,finalLog] using child

open Classical in
theorem actual_cached_fallback_unrecognized {R : Type} (Q : Nat) (seedTable : Seed)
    (ro : RawKey Q → Digest32) (iv : Digest32) (p : Program R) (counted : Counts Q p)
    (quiet : PublicCompressionCouplingIdealLateLinks.alarm PublicCompressionCouplingIdealLateLinks.mixedCV
      (oracle seedTable ro) (compile Q iv [] p Q (by omega) counted) (fun _ => none) []=false)
    (clean : ¬OutputCollision (finalLog []
      (Sampling.eval (oracle seedTable ro) (compile Q iv [] p Q (by omega) counted)).observations)) :
    ∀ input answer,
      (Sampling.eval (oracle seedTable ro)
        (memo (compile Q iv [] p Q (by omega) counted) (fun _ => none))).2 (.inl input)=some answer →
      isTerminal input →
      recognized (finalLog []
        (Sampling.eval (oracle seedTable ro) (compile Q iv [] p Q (by omega) counted)).observations) input=none := by
  apply compile_stable Q seedTable ro iv p [] Q (by omega) counted (fun _ => none) []
  · intro key answer impossible; cases impossible
  · intro a b d e first; cases first
  · simp only [List.length_nil,Nat.zero_add,Nat.le_refl]
  · intro input answer impossible; cases impossible
  · intro input answer impossible; cases impossible
  · intro input answer impossible; cases impossible
  · intro input answer impossible; cases impossible
  · exact quiet
  · exact clean

#print axioms actual_cached_fallback_unrecognized

#print axioms primitive_preserves

#print axioms alarm_bind
#print axioms recognized_none_after_nonlate_nonterminal
end Whir.PublicCompressionCouplingLateRecognition
