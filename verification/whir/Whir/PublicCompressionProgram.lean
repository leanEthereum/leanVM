import Whir.PublicMerkleLog
import Whir.RawOracleCoupling

/-! Real mode programs expanded into every shared compression call. Internal
construction nodes are counted, but remain absent from the public mode view. -/
namespace Whir.PublicCompressionProgram
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame TypedOracleCompiler

abbrev Computation (R : Type) (Q : Nat) := Sampling Node (fun _ => Digest32) R Q

def mapResult {R S : Type} (f : R → S) {Q : Nat} : Computation R Q → Computation S Q
  | .ret r => .ret (f r)
  | .draw n next => .draw n (fun d => mapResult f (next d))

@[simp] theorem eval_mapResult {R S : Type} (C : PrimitiveOracle) (f : R → S)
    {Q : Nat} (p : Computation R Q) :
    Sampling.eval C (mapResult f p) = f (Sampling.eval C p) := by
  induction p with
  | ret => rfl
  | draw n next ih => exact ih (C n)

@[simp] theorem execute_mapResult {R S : Type} (C : PrimitiveOracle) (f : R → S)
    {Q : Nat} (p : Computation R Q) :
    Sampling.execute C (mapResult f p) =
      (f (Sampling.execute C p).1,(Sampling.execute C p).2) := by
  induction p with
  | ret => rfl
  | draw n next ih => simp only [mapResult,Sampling.execute,ih]

def planCalls (cv : Digest32) : (xs : List DuplexEncoding.Instruction) → Computation Digest32 xs.length
  | [] => .ret cv
  | i :: rest => .draw ⟨cv,i.1,i.2,true⟩ (fun d => planCalls d rest)

 theorem planCalls_eval (C : PrimitiveOracle) (cv : Digest32) (xs : List DuplexEncoding.Instruction) :
    Sampling.eval C (planCalls cv xs) = evalPlan (compressionOf C) cv xs := by
  induction xs generalizing cv with
  | nil => rfl
  | cons i rest ih => exact ih _

def queryCalls (iv : Digest32) : (q : Query) → Computation Digest32 q.cost
  | .primitive _ n => .draw n (fun d => .ret d)
  | .construction q _ => planCalls iv (DuplexEncoding.plan q)

 theorem queryCalls_eval (C : PrimitiveOracle) (iv : Digest32) (q : Query) :
    Sampling.eval C (queryCalls iv q) = realAnswer C iv q := by
  cases q with
  | primitive => rfl
  | construction q valid => exact (planCalls_eval C iv _).trans (plan_evaluate _ _ _)

/-- The supplied Counts certificate charges each complete construction path.
There is no cached-path or successful-branch-only discount. -/
def compile {R : Type} (iv : Digest32) :
    (p : Program R) → (Q : Nat) → Counts Q p → Computation (Execution R) Q
  | .done r, _, _ => .ret ⟨⟨[],r⟩,0,0,0⟩
  | .ask q next, Q, h =>
      Sampling.pad (by have := h.1; omega)
        (Sampling.bind (queryCalls iv q) (fun d =>
          mapResult (prepend q d 0) (compile iv (next d) (Q-q.cost) (h.2 d))))

 theorem compile_eval {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    (p : Program R) (Q : Nat) (h : Counts Q p) :
    Sampling.eval C (compile iv p Q h) = runReal C iv p := by
  induction p generalizing Q with
  | done => rfl
  | ask q next ih =>
    simp only [compile,Sampling.eval_pad,Sampling.eval_bind,eval_mapResult,queryCalls_eval,ih,runReal]

def toLog (trace : List (Sigma (fun _ : Node => Digest32))) : PublicMerkleLog.PublicLog :=
  trace.map fun e => (e.1,e.2)

def primitiveLog {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    (p : Program R) (Q : Nat) (h : Counts Q p) : PublicMerkleLog.PublicLog :=
  toLog (Sampling.execute C (compile iv p Q h)).2

 theorem primitiveLog_length {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    (p : Program R) (Q : Nat) (h : Counts Q p) :
    (primitiveLog C iv p Q h).length ≤ Q := by
  simpa only [primitiveLog,toLog,List.length_map] using
    (Sampling.execute_runs C (compile iv p Q h)).length_le

 theorem execute_authentic {R : Type} (C : PrimitiveOracle) {Q : Nat} (p : Computation R Q) :
    PublicMerkleLog.AuthenticLog C (toLog (Sampling.execute C p).2) := by
  induction p with
  | ret => intro n d hm; simp [toLog,Sampling.execute] at hm
  | draw n next ih =>
    intro m d hm
    simp only [Sampling.execute,toLog,List.map_cons,List.mem_cons,Prod.mk.injEq] at hm
    rcases hm with ⟨rfl,rfl⟩ | hm
    · rfl
    · exact ih (C n) m d hm

 theorem primitiveLog_authentic {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    (p : Program R) (Q : Nat) (h : Counts Q p) :
    PublicMerkleLog.AuthenticLog C (primitiveLog C iv p Q h) := execute_authentic C _

 theorem body_tags {ns : List Node} (h : Body ns) : ∀ n ∈ ns, 0 < tag n := by
  induction h with
  | seed hs => intro n hn; have he := List.mem_singleton.mp hn; subst n; rw [hs.1]; omega
  | step hn hb ih =>
    intro n hm
    rcases List.mem_cons.mp hm with rfl | hm
    · rcases hn.1 with h | h | h | h | h <;> omega
    · exact ih n hm

 theorem complete_tags {ns : List Node} (h : Complete ns) : ∀ n ∈ ns, 0 < tag n := by
  obtain ⟨t,rest,rfl,ht,hb⟩ := h
  intro n hn
  rcases List.mem_cons.mp hn with rfl | hn
  · rcases ht.1 with h | h | h <;> omega
  · exact body_tags hb n hn

 theorem instruction_tag (iv : Digest32) (q : Coordinate) (valid : DuplexEncoding.Admissible q)
    (i : DuplexEncoding.Instruction) (hi : i ∈ DuplexEncoding.plan q) :
    0 < i.2.toNat / 2^56 := by
  let C : Compression := fun _ _ _ _ => iv
  have hp := coordinateTree_plan C iv q
  rw [← hp] at hi
  obtain ⟨n,hn,he⟩ := List.mem_map.mp hi
  have hn' := List.mem_reverse.mp hn
  have ht := complete_tags (coordinateTree_complete C iv q valid.1) n hn'
  have htweak := congrArg Prod.snd he
  dsimp only at htweak
  simpa only [tag,htweak] using ht

 theorem planCalls_origin (C : PrimitiveOracle) (cv : Digest32)
    (xs : List DuplexEncoding.Instruction) (n : Node) (d : Digest32)
    (hm : (n,d) ∈ toLog (Sampling.execute C (planCalls cv xs)).2) :
    ∃ i ∈ xs, n.tweak = i.2 := by
  induction xs generalizing cv with
  | nil => simp [planCalls,Sampling.execute,toLog] at hm
  | cons i rest ih =>
    simp only [planCalls,Sampling.execute,toLog,List.map_cons,List.mem_cons,Prod.mk.injEq] at hm
    rcases hm with ⟨he,_⟩ | hm
    · exact ⟨i,List.mem_cons_self,congrArg Node.tweak he⟩
    · obtain ⟨j,hj,ht⟩ := ih _ hm
      exact ⟨j,List.mem_cons_of_mem _ hj,ht⟩

 theorem construction_tags (C : PrimitiveOracle) (iv : Digest32) (q : Coordinate)
    (valid : DuplexEncoding.Admissible q) (n : Node) (d : Digest32)
    (hm : (n,d) ∈ toLog (Sampling.execute C (queryCalls iv (.construction q valid))).2) :
    0 < tag n := by
  obtain ⟨i,hi,ht⟩ := planCalls_origin C iv (DuplexEncoding.plan q) n d hm
  simpa only [tag,ht] using instruction_tag iv q valid i hi

/-- Direct primitive observations only; construction internals remain hidden. -/
def publicLog {R : Type} (view : View R) : PublicMerkleLog.PublicLog :=
  view.observations.filterMap fun o => match o.query with
    | .primitive _ n => some (n,o.answer)
    | .construction _ _ => none

 theorem ordinary_public {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    (p : Program R) (Q : Nat) (h : Counts Q p) (n : Node) (d : Digest32)
    (ordinary : tag n = 0) (hm : (n,d) ∈ primitiveLog C iv p Q h) :
    (n,d) ∈ publicLog (runReal C iv p).view := by
  induction p generalizing Q with
  | done => simp [primitiveLog,compile,Sampling.execute,toLog] at hm
  | ask q next ih =>
    simp only [primitiveLog,compile,Sampling.execute_pad,Sampling.execute_bind,
      execute_mapResult,toLog,List.map_append,List.mem_append,queryCalls_eval] at hm
    rcases hm with first | later
    · cases q with
      | primitive purpose input =>
        simp only [queryCalls,Sampling.execute,List.map_cons,List.map_nil,
          List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at first
        rcases first with ⟨rfl,rfl⟩
        exact List.mem_cons_self
      | construction coordinate valid =>
        have ht := construction_tags C iv coordinate valid n d first
        omega
    · have ht := ih (realAnswer C iv q) (Q-q.cost) (h.2 _) later
      cases q with
      | primitive => exact List.mem_cons_of_mem _ ht
      | construction => exact ht

 theorem planCalls_count (C : PrimitiveOracle) (cv : Digest32) (xs : List DuplexEncoding.Instruction) :
    (Sampling.execute C (planCalls cv xs)).2.length = xs.length := by
  induction xs generalizing cv with
  | nil => rfl
  | cons i rest ih => simp only [planCalls,Sampling.execute,List.length_cons,ih]

 theorem queryCalls_count (C : PrimitiveOracle) (iv : Digest32) (q : Query) :
    (Sampling.execute C (queryCalls iv q)).2.length = q.cost := by
  cases q with
  | primitive => rfl
  | construction q valid => exact planCalls_count C iv _

 theorem primitiveLog_exact_count {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    (p : Program R) (Q : Nat) (h : Counts Q p) :
    (primitiveLog C iv p Q h).length = (runReal C iv p).primitiveCost := by
  induction p generalizing Q with
  | done => rfl
  | ask q next ih =>
    simp only [primitiveLog,toLog,List.length_map,compile,Sampling.execute_pad,
      Sampling.execute_bind,execute_mapResult,List.length_append,queryCalls_count,queryCalls_eval,
      runReal,prepend]
    simpa only [primitiveLog,toLog,List.length_map] using
      congrArg (q.cost + ·) (ih _ _ (h.2 _))

/-- Conditional #552 mode smoke, separate from baseline interactive evidence.
The repeated ordinary query is a cache hit; the construction still expands
to its two complete internal compression nodes in the full-call trace. -/
def smoke : IO Unit := do
  let iv := DuplexCompression.parameterIV
  let coordinate : Coordinate := ⟨⟨iv,iv,[]⟩,.output 0⟩
  have valid : DuplexEncoding.Admissible coordinate := by
    constructor
    · simp [coordinate]
    · decide
  let ordinary := PublicMerkleLog.node iv 0 [] true
  let p : Program (Digest32 × Digest32 × Digest32) :=
    .ask (.primitive .direct ordinary) fun first =>
      .ask (.construction coordinate valid) fun middle =>
        .ask (.primitive .direct ordinary) fun last => .done (first,middle,last)
  have counts : Counts 4 p := by
    simp [p,Counts,Query.cost,pathCost,DuplexEncoding.plan,coordinate]
  let compiled := compile iv p 4 counts
  let result := Sampling.execute blake2sOracle compiled
  let reference := runReal blake2sOracle iv p
  unless result.1.view.result == reference.view.result && result.1.primitiveCost == 4 do
    throw (IO.userError "real-mode execution refinement failed")
  let calls := toLog result.2
  unless calls.map (fun e => tag e.1) == [0,1,6,0] do
    throw (IO.userError "mode compiler omitted or reordered compression nodes")
  unless (publicLog result.1.view).length == 2 do
    throw (IO.userError "hidden construction nodes leaked into public observations")
  let memoized := Sampling.execute blake2sOracle (RawOracleCoupling.memo compiled (fun _ => none))
  unless memoized.2.length == 3 && memoized.1.1.view.result == reference.view.result do
    throw (IO.userError "shared compression cache failed to reuse repeated input")
  IO.println "Conditional mode: 4 full compression calls, tags [0,1,6,0], 2 public direct records, 3 fresh cached draws; exact result OK"

end Whir.PublicCompressionProgram
