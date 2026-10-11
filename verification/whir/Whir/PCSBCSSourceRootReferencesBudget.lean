import Whir.PCSBCSSourceRootReferences

/-! Target/reference accounting is deliberately independent of authentication.
Every root in a child prefix is charged, including equal CVs at different shape
addresses. Complete construction paths, not one root per query, pay the bill. -/
namespace Whir.PCSBCSSourceRootReferences
open Concrete Protocol FiatShamirGame WHIRHistory WHIRHistoryKey
open DuplexModeGame DuplexFraming PCSBCSMerkleRootCache

private theorem chunks_positive (first : Bool) (previous : Nat) (pending bytes : List Byte)
    (nonempty : pending ≠ [] ∨ bytes ≠ []) :
    0 < (DuplexEncoding.chunks first previous pending bytes).length := by
  induction bytes generalizing first previous pending with
  | nil =>
    have hp : pending ≠ [] := by simpa using nonempty
    simp [DuplexEncoding.chunks,hp]
  | cons b bs ih =>
    simp only [DuplexEncoding.chunks]
    split
    · simp
    · exact ih _ _ _ (Or.inl (by simp))

private theorem canonical_cost (width : Nat → Nat) (messages : List Pending)
    (normal : Normal messages) :
    messages.dropLast.length ≤
      ((canonicalFrames width messages).flatMap DuplexEncoding.framePlan).length := by
  induction normal with
  | initial => simp [initialPending,canonicalFrames,annotated,encodeSteps]
  | @cons ps prior m nonempty ih =>
    have scalarNonempty : scalarBytes m.scalars ≠ [] :=
      fun h => nonempty ((scalarBytes_empty _).mp h)
    have positive := chunks_positive true (width (ps.length-1)) []
      (scalarBytes m.scalars) (Or.inr scalarNonempty)
    have hp := prior.nonempty
    simp only [canonicalFrames,annotated,hp,↓reduceIte,List.reverse_cons,
      encodeSteps,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.length_append] at ih ⊢
    simp only [stepFrames,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      DuplexEncoding.framePlan,List.length_append,List.append_nil] at ih ⊢
    rw [List.dropLast_cons_of_ne_nil hp,List.length_cons]
    omega

theorem reference_count (c : Config) (messages : List Pending) (normal : Normal messages) :
    (phaseReferences c messages).length ≤ messages.dropLast.length := by
  have restore := normal.restore
  have hr : messages.reverse = initialPending :: messages.dropLast.reverse := by
    calc
      messages.reverse = (messages.dropLast ++ [initialPending]).reverse :=
        congrArg List.reverse restore.symm
      _ = initialPending :: messages.dropLast.reverse := by simp
  simp only [phaseReferences,hr,List.zipIdx_cons,List.filterMap_cons,phaseAt,
    ↓reduceIte]
  have bound := List.length_filterMap_le
    (fun (m,n) => phaseAt c n m)
    (List.zipIdx messages.dropLast.reverse 1)
  simpa [phaseAt] using bound

theorem complete_path_reference_bound (p : ParameterBounds.Profile) (entry : FramedHistory)
    (messages : List Pending) (nonempty : messages ≠ [])
    (admitted : scheduledAdmissible (ParameterBounds.config p) messages = true)
    (block : Nat) :
    1 + (phaseReferences (ParameterBounds.config p) messages).length ≤
      pathCost (WHIRCallerPrefix.outputKeyFrom (stackWidth (ParameterBounds.config p))
        entry messages block) := by
  have normal := scheduled_normal _ _ nonempty admitted
  have refs := reference_count (ParameterBounds.config p) messages normal
  have cost := canonical_cost (stackWidth (ParameterBounds.config p)) messages normal
  unfold pathCost DuplexEncoding.plan
  rw [WHIRCallerPrefix.outputKeyFrom_history _ (stackWidth_positive p) entry normal]
  simp only [List.flatMap_append,List.length_cons,List.length_append,List.length_nil]
  omega

/-- Each successful parser result is charged without a CV-based deduplication. -/
def requestReferences (p : ParameterBounds.Profile) (layout : WHIRCallerClaims.CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (entry : FramedHistory)
    (answers : FiatShamirGame.Coordinate → Digest32) : Query → List Reference
  | .construction key _ => (parseReferences p layout saved entry answers key).getD []
  | .primitive _ _ => []

theorem parsed_reference_bound (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record)
    (entry : FramedHistory) (answers : FiatShamirGame.Coordinate → Digest32)
    (key : FiatShamirGame.Coordinate) (refs : List Reference)
    (parsed : parseReferences p layout saved entry answers key = some refs) :
    refs.length ≤ pathCost key := by
  obtain ⟨_,_,claims,messages,_,pending,_,rfl⟩ :=
    parseReferences_admitted p layout saved entry answers key refs parsed
  obtain ⟨nonempty,admitted,block,same⟩ :=
    parsePendingKey_admitted p entry key messages pending
  rw [same]
  simpa only [List.length_cons,Nat.add_comm] using
    complete_path_reference_bound p entry messages nonempty admitted block

theorem request_reference_bound (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record)
    (entry : FramedHistory) (answers : FiatShamirGame.Coordinate → Digest32)
    (request : Query) :
    (requestReferences p layout saved entry answers request).length ≤ request.cost := by
  cases request with
  | primitive purpose node => simp [requestReferences,Query.cost]
  | construction key valid =>
    cases parsed : parseReferences p layout saved entry answers key with
    | none => simp [requestReferences,Query.cost,parsed]
    | some refs =>
      simpa [requestReferences,Query.cost,parsed] using
        parsed_reference_bound p layout saved entry answers key refs parsed

/-- A response-following prefix of the actual Program: no accepted-verifier or
source-truth premise. Rejected continuations and primitive queries also charge. -/
inductive RequestPrefix {R : Type} : Program R → List Query → Prop where
  | nil (program : Program R) : RequestPrefix program []
  | ask (q : Query) (next : Digest32 → Program R) (answer : Digest32)
      (rest : List Query) (tail : RequestPrefix (next answer) rest) :
      RequestPrefix (.ask q next) (q :: rest)

theorem counts_prefix_cost {R : Type} (Q : Nat) (program : Program R)
    (requests : List Query) (counted : Counts Q program)
    (tracePrefix : RequestPrefix program requests) : (requests.map Query.cost).sum ≤ Q := by
  induction tracePrefix generalizing Q with
  | nil => simp
  | ask q next answer rest tail ih =>
    have first := counted.1
    have later := ih (Q-q.cost) (counted.2 answer)
    simp only [List.map_cons,List.sum_cons]
    omega

def announcements (log : PublicMerkleLog.PublicLog) (refs : List Reference) : List Announcement :=
  refs.map (fun ref => ⟨log,ref.root,ref.shape⟩)

/-- CONSTRUCTION-request ledger only. Counts charges each complete construction
path; primitive terminals do not register here. All child-prefix references are
counted, and only identical shape addresses reuse the existing registry.
Public primitive first-reference/frame charging is a separate integration. -/
theorem aggregate_resource_bound {R : Type} (Q : Nat) (program : Program R)
    (requests : List Query) (counted : Counts Q program)
    (tracePrefix : RequestPrefix program requests)
    (p : ParameterBounds.Profile) (layout : WHIRCallerClaims.CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (entry : FramedHistory)
    (answers : FiatShamirGame.Coordinate → Digest32)
    (registry : Registry) (log : PublicMerkleLog.PublicLog) :
    (registerAll registry (announcements log (requests.flatMap
      (requestReferences p layout saved entry answers)))).size ≤ registry.size + Q := by
  have cost := counts_prefix_cost Q program requests counted tracePrefix
  have refs : (requests.flatMap (requestReferences p layout saved entry answers)).length ≤
      (requests.map Query.cost).sum := by
    clear counted tracePrefix cost
    induction requests with
    | nil => simp
    | cons request rest ih =>
      have first := request_reference_bound p layout saved entry answers request
      simp only [List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons]
      omega
  have bound := registerAll_size_le registry
    (announcements log (requests.flatMap (requestReferences p layout saved entry answers)))
  simp only [announcements,List.length_map] at bound
  unfold announcements
  omega

/-- Public recognizer integration: selected keys may be arbitrary child-prefix
prequeries. The endpoint explicitly requires their complete path charges; it
does not mistake a terminal primitive call for the cost of its ancestry. -/
theorem first_mention_path_budget (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record)
    (entry : FramedHistory) (answers : FiatShamirGame.Coordinate → Digest32)
    (keys : List FiatShamirGame.Coordinate) (Q : Nat)
    (charged : (keys.map pathCost).sum ≤ Q) (registry : Registry)
    (log : PublicMerkleLog.PublicLog) :
    (registerAll registry (announcements log (keys.flatMap (fun key =>
      (parseReferences p layout saved entry answers key).getD [])))).size ≤
        registry.size+Q := by
  have refs : (keys.flatMap (fun key =>
      (parseReferences p layout saved entry answers key).getD [])).length ≤
        (keys.map pathCost).sum := by
    clear charged
    induction keys with
    | nil => simp
    | cons key rest ih =>
      have first : ((parseReferences p layout saved entry answers key).getD []).length ≤
          pathCost key := by
        cases parsed : parseReferences p layout saved entry answers key with
        | none => simp
        | some refs => exact parsed_reference_bound p layout saved entry answers key refs parsed
      simp only [List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons]
      omega
  have bound := registerAll_size_le registry (announcements log
    (keys.flatMap (fun key => (parseReferences p layout saved entry answers key).getD [])))
  simp only [announcements,List.length_map] at bound
  unfold announcements
  omega

/-- The final proof root costs at most one extra address; if already registered,
register returns the same table. It is NOT one extra root per query. -/
theorem final_root_resource_bound (registry : Registry) (refs : List Announcement)
    (Q : Nat) (cap : (registerAll registry refs).size ≤ registry.size+Q)
    (log : PublicMerkleLog.PublicLog) (finalRoot : Digest32)
    (shape : PCSBCSMerkleRootCache.Shape) :
    (register (registerAll registry refs) log finalRoot shape).size ≤ registry.size+Q+1 := by
  have bound := register_size_le (registerAll registry refs) log finalRoot shape
  omega

theorem final_root_captured_bound (registry : Registry) (refs : List Announcement)
    (Q : Nat) (cap : (registerAll registry refs).size ≤ registry.size+Q)
    (log : PublicMerkleLog.PublicLog) (finalRoot : Digest32)
    (shape : PCSBCSMerkleRootCache.Shape) (frozen : Frozen)
    (captured : (registerAll registry refs)[cacheKey finalRoot shape]? = some frozen) :
    (register (registerAll registry refs) log finalRoot shape).size ≤ registry.size+Q := by
  rw [register_existing _ _ _ _ frozen captured]
  exact cap

#print axioms reference_count
#print axioms complete_path_reference_bound
#print axioms parsed_reference_bound
#print axioms counts_prefix_cost
#print axioms aggregate_resource_bound
#print axioms first_mention_path_budget
#print axioms final_root_resource_bound
#print axioms final_root_captured_bound
end Whir.PCSBCSSourceRootReferences
