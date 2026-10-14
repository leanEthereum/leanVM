import Whir.PCSBCSSourcePublicMetadata
import Whir.PCSBCSSourceCallerAnswers
import Whir.PublicCompressionCouplingPrefixTrace
import Whir.PublicCompressionCouplingTerminalUnique
import Whir.WHIRHeaderRoots

/-! Old-history completion has a literal, source-cost-charged atomic execution.
Its prefix queries are primitive OTHER keys and its terminal query is a raw
OTHER key. This holds even when completion runs after the selected packet.
The actual primitive completion is also related to a concretely constructed
source table, not an externally supplied consistency certificate. That table
is a pushforward of a primitive oracle, NOT an independent uniform mixed table;
no distributional coupling or knowledge-extraction conclusion is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Whir.PCSBCSCallerCompletionCausality
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open TypedOracleCompiler RawOracleCoupling PublicCompressionProgram
open PCSBCSChallengeOracle PublicCompressionCouplingMixed
open PCSStateRestoration.Latent
noncomputable local instance : DecidableEq Coordinate := Classical.decEq _

variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {boundary : Nat}
local notation "part" => EnteredPacket.partition
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)
local notation "Keys" => PCSBCSSourceRootCapture.Key
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)
local notation "Answers" => PCSBCSSourceRootCapture.Answer
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)
abbrev Caller (packet : EnteredPacket p Q iv boundary) :=
  {q : Coordinate // q ∈ WHIRCallerOutputs.callerOutputs packet.1.val}

theorem caller_admissible (packet : EnteredPacket p Q iv boundary) (q : Caller packet) :
    DuplexEncoding.Admissible q.val :=
  WHIRCallerOutputs.callerOutputs_admissible _ packet.2.2.entryValid _ q.property

theorem caller_bounded (packet : EnteredPacket p Q iv boundary) (q : Caller packet) :
    pathCost q.val ≤ Q :=
  PCSBCSSourceCallerAnswers.caller_output_bounded packet q.val q.property

theorem primitive_other (n : Node) : (part).recognize (.inl n) = none := by
  cases hit : (part).recognize (.inl n) with
  | none => rfl
  | some block =>
    have impossible := (part).encode_recognize _ block hit
    change Sum.inr _ = Sum.inl n at impossible
    cases impossible

def primitiveKey (n : Node) : Keys := .inr ⟨.inl n, primitive_other n⟩
def terminalKey (packet : EnteredPacket p Q iv boundary) (q : Caller packet) : Keys :=
  .inr ⟨.inr (constructionKey Q iv q.val (caller_bounded packet q)),
    PCSBCSSourceCallerAnswers.caller_output_recognize_none packet.1.val
      packet.1.property packet.2.2.entryValid q.val q.property (caller_bounded packet q)⟩

theorem join_primitive (table : Table Keys Answers) (n : Node) :
    (part).join table (.inl n) = table (primitiveKey n) := by
  unfold Partition.join
  split
  · next block hit =>
      have impossible := hit.symm.trans (primitive_other (p := p) (Q := Q)
        (iv := iv) (boundary := boundary) n)
      cases impossible
  · rfl

theorem join_terminal (table : Table Keys Answers)
    (packet : EnteredPacket p Q iv boundary) (q : Caller packet) :
    (part).join table (.inr (constructionKey Q iv q.val (caller_bounded packet q))) =
      table (terminalKey packet q) := by
  unfold Partition.join
  split
  · next block hit =>
      have impossible := hit.symm.trans
        (PCSBCSSourceCallerAnswers.caller_output_recognize_none packet.1.val
          packet.1.property packet.2.2.entryValid q.val q.property (caller_bounded packet q))
      cases impossible
  · rfl

/-- The source lowering of the actual compiler's literal primitive prefix. -/
def sourceBody (cv : Digest32) : (xs : List DuplexEncoding.Instruction) →
    Sampling Keys Answers (Digest32 × BodyLog) xs.length
  | [] => .ret (cv,[])
  | i :: rest => .draw (primitiveKey ⟨cv,i.1,i.2,true⟩) (fun d =>
      Sampling.bind (sourceBody d rest) (fun result =>
        .ret (n := 0) (result.1,(⟨cv,i.1,i.2,true⟩,d)::result.2)))

/-- Prefix and terminal are all real Sampling draws, not a table callback. -/
def oldConstruction (packet : EnteredPacket p Q iv boundary) (q : Caller packet) :
    Sampling Keys Answers InspectedConstruction (pathCost q.val) :=
  Sampling.pad (n := (DuplexEncoding.plan q.val).dropLast.length + 1) (by
    have h := DuplexRawProgram.pathCost_pos q.val
    simp only [List.length_dropLast]
    unfold pathCost at h ⊢
    omega)
    (Sampling.bind (sourceBody iv (DuplexEncoding.plan q.val).dropLast)
      (fun body => .draw (terminalKey packet q) (fun d =>
        .ret ⟨q.val,caller_admissible packet q,d,body.1,body.2⟩)))

theorem sourceBody_actual (table : Table Keys Answers) (cv : Digest32)
    (xs : List DuplexEncoding.Instruction) :
    Sampling.eval table (sourceBody cv xs) =
      Sampling.eval ((part).join table) (bodyCalls Q cv xs) := by
  induction xs generalizing cv with
  | nil => rfl
  | cons i rest ih =>
    simp only [sourceBody,Sampling.eval,Sampling.eval_bind,bodyCalls,
      PublicCompressionCouplingMixed.Computation.eval_map,join_primitive,ih]

theorem oldConstruction_actual (table : Table Keys Answers)
    (packet : EnteredPacket p Q iv boundary) (q : Caller packet) :
    Sampling.eval table (oldConstruction packet q) =
      Sampling.eval ((part).join table)
        (causalConstruction Q iv q.val (caller_admissible packet q) (caller_bounded packet q)) := by
  simp only [oldConstruction,Sampling.eval_pad,Sampling.eval_bind,Sampling.eval,
    causalConstruction_eval,sourceBody_actual,join_terminal]

/-- Literal prefix nodes cannot be ANY selected source terminal, independently
of chaining-value collisions or when these completion draws are scheduled. -/
theorem prefix_not_terminal (C : PrimitiveOracle) (packet : EnteredPacket p Q iv boundary)
    (q : Caller packet) (n : Node) (d : Digest32)
    (member : (n,d) ∈ (Sampling.eval (oracle C (fun _ => d))
      (bodyCalls Q iv (DuplexEncoding.plan q.val).dropLast)).2)
    (terminal : Node) (selected : isTerminal terminal) : n ≠ terminal := by
  rw [PublicCompressionCouplingRecognition.inspection_body_nodes Q C (fun _ => d)
    iv q.val (caller_admissible packet q)] at member
  obtain ⟨node,hn,he⟩ := List.mem_map.mp member
  have equal : node = n := congrArg Prod.fst he
  subst node
  have body := (traceHistory_valid (compressionOf C) iv q.val.history
    (caller_admissible packet q).1).1.body
  intro equal
  subst terminal
  exact body_no_terminal body n (List.mem_reverse.mp hn) selected

/-- Recognition of the complete literal body has exactly the old raw key.
This does not assume the public predecessor search found that body. -/
theorem complete_body_other (C : PrimitiveOracle)
    (packet : EnteredPacket p Q iv boundary) (q : Caller packet)
    (key : RawKey Q)
    (recognized : extract (coordinateTree (compressionOf C) iv q.val) =
      some (expandKey key)) :
    (part).recognize (.inr key) = none := by
  have extracted := coordinateTree_key (compressionOf C) iv q.val (caller_admissible packet q)
  have expanded : expandKey key = expandKey
      (constructionKey Q iv q.val (caller_bounded packet q)) := by
    rw [expand_constructionKey]
    exact Option.some.inj (recognized.symm.trans extracted)
  have same := PublicCompressionCouplingRecognition.expandKey_injective expanded
  rw [same]
  exact PCSBCSSourceCallerAnswers.caller_output_recognize_none packet.1.val
    packet.1.property packet.2.2.entryValid q.val q.property (caller_bounded packet q)

/-- All executions of the actual source prefix are unchanged, including their
physical nodes and full answers, when only the selected packet is replaced. -/
theorem sourceBody_update (current : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) (full : EnteredPacket.Block current → Digest32)
    (cv : Digest32) (xs : List DuplexEncoding.Instruction) :
    Sampling.execute (Function.update table (.inl current) full) (sourceBody cv xs) =
      Sampling.execute table (sourceBody cv xs) := by
  classical
  induction xs generalizing cv with
  | nil => rfl
  | cons i rest ih =>
    have changed : Function.update table (.inl current) full
        (primitiveKey (p := p) (Q := Q) (iv := iv) (boundary := boundary)
          ⟨cv,i.1,i.2,true⟩) =
        table (primitiveKey ⟨cv,i.1,i.2,true⟩) := by simp [primitiveKey]
    simp only [sourceBody,Sampling.execute,changed,Sampling.execute_bind,
      ← Sampling.execute_value,ih]

 theorem oldConstruction_update (current packet : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) (full : EnteredPacket.Block current → Digest32)
    (q : Caller packet) :
    Sampling.execute (Function.update table (.inl current) full) (oldConstruction packet q) =
      Sampling.execute table (oldConstruction packet q) := by
  classical
  simp only [oldConstruction,Sampling.execute_pad,Sampling.execute_bind,
    ← Sampling.execute_value,sourceBody_update]
  simp [Sampling.execute,terminalKey]

theorem sourceBody_count (table : Table Keys Answers) (cv : Digest32)
    (xs : List DuplexEncoding.Instruction) :
    (Sampling.execute table (sourceBody cv xs)).2.length = xs.length := by
  induction xs generalizing cv with
  | nil => rfl
  | cons i rest ih =>
    simp [sourceBody,Sampling.execute,Sampling.execute_bind,ih]

theorem oldConstruction_count (table : Table Keys Answers)
    (packet : EnteredPacket p Q iv boundary) (q : Caller packet) :
    (Sampling.execute table (oldConstruction packet q)).2.length = pathCost q.val := by
  simp only [oldConstruction,Sampling.execute_pad,Sampling.execute_bind,
    List.length_append,sourceBody_count,Sampling.execute,List.length_cons,List.length_nil,
    List.length_dropLast]
  have h := DuplexRawProgram.pathCost_pos q.val
  unfold pathCost at h ⊢
  omega

theorem sourceBody_trace_other (table : Table Keys Answers) (cv : Digest32)
    (xs : List DuplexEncoding.Instruction) (current : EnteredPacket p Q iv boundary) :
    ∀ event ∈ (Sampling.execute table (sourceBody cv xs)).2,
      event.1 ≠ .inl current := by
  induction xs generalizing cv with
  | nil => simp [sourceBody,Sampling.execute]
  | cons i rest ih =>
    simp only [sourceBody,Sampling.execute,Sampling.execute_bind,
      List.append_nil,List.mem_cons]
    intro event member
    rcases member with equal | member
    · subst event
      simp [primitiveKey]
    · exact ih _ event member

theorem oldConstruction_trace_other (table : Table Keys Answers)
    (current packet : EnteredPacket p Q iv boundary) (q : Caller packet) :
    ∀ event ∈ (Sampling.execute table (oldConstruction packet q)).2,
      event.1 ≠ .inl current := by
  simp only [oldConstruction,Sampling.execute_pad,Sampling.execute_bind,
    List.mem_append]
  intro event member
  rcases member with earlier | terminal
  · exact sourceBody_trace_other table _ _ current event earlier
  · simp only [Sampling.execute,List.mem_cons,List.not_mem_nil,or_false] at terminal
    subst event
    simp [terminalKey]

 theorem oldConstruction_answer (table : Table Keys Answers)
    (packet : EnteredPacket p Q iv boundary) (q : Caller packet) :
    (Sampling.eval table (oldConstruction packet q)).advertised =
      PCSBCSSourceCallerAnswers.answers table q.val := by
  rw [oldConstruction_actual,causalConstruction_eval]
  exact (PCSBCSSourceCallerAnswers.answers_bounded table q.val
    (caller_bounded packet q)).symm

/-- The outside callback is never used for a requested coordinate after this
execution: each coordinate is overwritten with its genuinely sampled answer.
No initial/prefix availability is required. Duplicates are charged explicitly. -/
noncomputable def atomicComplete (packet : EnteredPacket p Q iv boundary)
    (outside : Coordinate → Digest32) : (requests : List (Caller packet)) →
    Sampling Keys Answers (Coordinate → Digest32)
      ((requests.map (fun q => pathCost q.val)).sum)
  | [] => .ret outside
  | q :: rest => Sampling.bind (oldConstruction packet q) (fun observed =>
      atomicComplete packet (Function.update outside q.val observed.advertised) rest)

theorem atomicComplete_preserves (packet : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) (requests : List (Caller packet)) (q : Caller packet)
    (absent : q ∉ requests) (outside : Coordinate → Digest32) :
    Sampling.eval table (atomicComplete packet outside requests) q.val = outside q.val := by
  classical
  induction requests generalizing outside with
  | nil => rfl
  | cons s rest ih =>
    simp only [atomicComplete,Sampling.eval_bind]
    rw [ih (fun member => absent (List.mem_cons_of_mem _ member))]
    apply Function.update_of_ne
    intro equal
    have same : q = s := Subtype.ext equal
    subst s
    exact absent List.mem_cons_self

 theorem atomicComplete_answers (packet : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) (outside : Coordinate → Digest32)
    (requests : List (Caller packet)) :
    ∀ q ∈ requests, Sampling.eval table (atomicComplete packet outside requests) q.val =
      PCSBCSSourceCallerAnswers.answers table q.val := by
  classical
  induction requests generalizing outside with
  | nil => simp
  | cons q rest ih =>
    simp only [atomicComplete,Sampling.eval_bind,oldConstruction_answer]
    intro r member
    by_cases later : r ∈ rest
    · exact ih _ r later
    · have equal : r = q := (List.mem_cons.mp member).resolve_right later
      subst r
      rw [atomicComplete_preserves packet table rest q later]
      simp

 theorem atomicComplete_update (current packet : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) (full : EnteredPacket.Block current → Digest32)
    (outside : Coordinate → Digest32) (requests : List (Caller packet)) :
    Sampling.execute (Function.update table (.inl current) full)
      (atomicComplete packet outside requests) =
      Sampling.execute table (atomicComplete packet outside requests) := by
  induction requests generalizing outside with
  | nil => rfl
  | cons q rest ih =>
    simp only [atomicComplete,Sampling.execute_bind,← Sampling.execute_value,
      oldConstruction_update,ih]

theorem atomicComplete_count (packet : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) (outside : Coordinate → Digest32)
    (requests : List (Caller packet)) :
    (Sampling.execute table (atomicComplete packet outside requests)).2.length =
      (requests.map (fun q => pathCost q.val)).sum := by
  induction requests generalizing outside with
  | nil => rfl
  | cons q rest ih =>
    simp only [atomicComplete,Sampling.execute_bind,List.length_append,
      oldConstruction_count,ih,List.map_cons,List.sum_cons]

theorem atomicComplete_trace_other (packet : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) (outside : Coordinate → Digest32)
    (requests : List (Caller packet)) (current : EnteredPacket p Q iv boundary) :
    ∀ event ∈ (Sampling.execute table (atomicComplete packet outside requests)).2,
      event.1 ≠ .inl current := by
  induction requests generalizing outside with
  | nil => simp [atomicComplete,Sampling.execute]
  | cons q rest ih =>
    simp only [atomicComplete,Sampling.execute_bind,List.mem_append]
    intro event member
    rcases member with first | later
    · exact oldConstruction_trace_other table current packet q event first
    · exact ih _ event later

theorem atomicCompletion_budget (packet : EnteredPacket p Q iv boundary)
    (requests : List (Caller packet)) :
    (requests.map (fun q => pathCost q.val)).sum ≤ Q * requests.length := by
  induction requests with
  | nil => simp
  | cons q rest ih =>
    have bound := caller_bounded packet q
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

 theorem atomicComplete_draws_le (packet : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) (outside : Coordinate → Digest32)
    (requests : List (Caller packet)) :
    (Sampling.execute table (atomicComplete packet outside requests)).2.length ≤
      (requests.map (fun q => pathCost q.val)).sum :=
  (Sampling.execute_runs table _).length_le

 theorem atomic_original (packet : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) (outside : Coordinate → Digest32)
    (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record) :
    PCSBCSSourceCallerOriginal.original p layout saved packet.1.val
      (Sampling.eval table (atomicComplete packet outside
        (WHIRCallerOutputs.callerOutputs packet.1.val).attach)) =
      PCSBCSSourceCallerOriginal.original p layout saved packet.1.val
        (PCSBCSSourceCallerAnswers.answers table) := by
  apply PCSBCSSourceCallerOriginal.original_prior_only
  intro q member
  exact atomicComplete_answers packet table outside _ ⟨q,member⟩ (List.mem_attach _ _)

/-- Canonical concrete relation: raw mode values are computed by C itself.
Garbage raw keys retain C's primitive seed value; no actual caller uses that
branch. This source table is deliberately not claimed uniformly distributed. -/
def realMixed (C : PrimitiveOracle) (iv : Digest32) : Key Q → Digest32
  | .inl n => C n
  | .inr raw => match WHIRHeaderRoots.decodeRaw iv raw with
      | some q => evalCoordinate (compressionOf C) iv q
      | none => C ⟨iv,ByteCodec.pairBytes (iv,iv),0,true⟩

noncomputable def realSourceTable (C : PrimitiveOracle) : Table Keys Answers :=
  (part).split (realMixed C iv)

 theorem realSource_answers (C : PrimitiveOracle)
    (packet : EnteredPacket p Q iv boundary) (q : Caller packet) :
    PCSBCSSourceCallerAnswers.answers
      (realSourceTable (p := p) (Q := Q) (iv := iv) (boundary := boundary) C) q.val =
      evalCoordinate (compressionOf C) iv q.val := by
  rw [PCSBCSSourceCallerAnswers.answers_bounded _ _ (caller_bounded packet q)]
  simp only [realSourceTable,Partition.join_split,realMixed,
    WHIRHeaderRoots.decodeRaw_construction iv q.val (caller_admissible packet q)
      (caller_bounded packet q)]

/-- Real missing-output execution recovers the actual original source input
against the concrete source table, with no C/table certificate or availability
premise. Its additional draw cap is the sum of all literal caller path costs. -/
 theorem real_original (C : PrimitiveOracle) (packet : EnteredPacket p Q iv boundary)
    (log : PublicMerkleLog.PublicLog) (auth : PublicMerkleLog.AuthenticLog C log)
    (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record)
    (outside : Coordinate → Digest32) :
    PCSBCSSourceCallerOriginal.original p layout saved packet.1.val
      (PCSBCSPublicCallerCompletion.callerAnswers iv
        (Sampling.execute C
          (PCSBCSPublicCallerCompletion.callerCompletion iv log packet.1.val)).1
        packet.1.val
        (PCSBCSPublicCallerCompletion.callerCompletion_total C iv log auth packet.1.val)
        outside) =
      PCSBCSSourceCallerOriginal.original p layout saved packet.1.val
        (PCSBCSSourceCallerAnswers.answers
          (realSourceTable (p := p) (Q := Q) (iv := iv) (boundary := boundary) C)) := by
  rw [PCSBCSPublicCallerCompletion.original_resolved C iv log auth packet.1.val
    p layout saved outside]
  apply PCSBCSSourceCallerOriginal.original_prior_only
  intro q member
  exact (realSource_answers C packet ⟨q,member⟩).symm

/-- Cached real completion may use fewer draws; it always stays under the
literal sum, including missing outputs first evaluated after the source query. -/
theorem real_completion_draws (C : PrimitiveOracle)
    (packet : EnteredPacket p Q iv boundary) (log : PublicMerkleLog.PublicLog) :
    (Sampling.execute C
      (PCSBCSPublicCallerCompletion.callerCompletion iv log packet.1.val)).2.length ≤
      ((WHIRCallerOutputs.callerOutputs packet.1.val).map pathCost).sum :=
  PCSBCSPublicCallerCompletion.complete_draws_le C iv log _

#print axioms prefix_not_terminal
#print axioms complete_body_other
#print axioms oldConstruction_actual
#print axioms oldConstruction_update
#print axioms atomicComplete_answers
#print axioms atomicComplete_update
#print axioms atomicComplete_draws_le
#print axioms atomic_original
#print axioms realSource_answers
#print axioms real_original
#print axioms atomicComplete_count
#print axioms atomicComplete_trace_other
#print axioms atomicCompletion_budget
#print axioms real_completion_draws
end Whir.PCSBCSCallerCompletionCausality
