import Whir.WHIRModeFinal

namespace Whir.WHIRPublicBackfill
open FiatShamirGame DuplexFraming DuplexModeGame
open RawWHIRKeys (Context Packet)
open RawOracleCoupling RawOracleCoupling.Concrete
open WHIRModeFinal

variable {R : Type}

/-- One cell per public-derived raw request, followed by the final selection.
Unrecognized requests have empty cells: their public primitive answers must be
replayed from the original view, not read again through an ambient raw table. -/
def selections (ctx : Context) (Q : Nat) (requests : List (RawKey Q))
    (final : Option (Packet ctx Q)) : List (Option (Packet ctx Q)) :=
  requests.map (fun key => (RawWHIRKeys.recognize ctx Q key).map Sigma.fst) ++ [final]

abbrev Record (ctx : Context) (Q : Nat) := WHIRModeFinal.Completed ctx Q Unit

structure Completed (ctx : Context) (Q : Nat) (R : Type) where
  result : R
  records : List (Record ctx Q)

/-- Cells retain request order and packet blocks remain one atomic group answer.
Repeats are deliberately physically reread, with their full uncached cost. -/
def readSelections (ctx : Context) (Q : Nat) : List (Option (Packet ctx Q)) →
    (List (Record ctx Q) → Program R) → Program R
  | [], next => next []
  | none :: rest, next => readSelections ctx Q rest (fun records => next (⟨(),none,[]⟩ :: records))
  | some p :: rest, next =>
    readCallerThenPackets ctx Q p (callerPositions ctx Q p) (terminalCompletion ctx Q (some p))
      (fun history => readSelections ctx Q rest (fun records => next (⟨(),some p,history⟩ :: records)))

def backfill (ctx : Context) (Q : Nat) (result : R) (requests : List (RawKey Q))
    (final : Option (Packet ctx Q)) : Program (Completed ctx Q R) :=
  readSelections ctx Q (selections ctx Q requests final) (fun records => .done ⟨result,records⟩)

def selectionsCost (ctx : Context) (Q : Nat) (ps : List (Option (Packet ctx Q))) : Nat :=
  (ps.map (completionCost ctx Q)).sum

def cost (ctx : Context) (Q : Nat) (requests : List (RawKey Q))
    (final : Option (Packet ctx Q)) : Nat := selectionsCost ctx Q (selections ctx Q requests final)

def realRecords (ctx : Context) (Q : Nat) (oracle : PrimitiveOracle)
    (ps : List (Option (Packet ctx Q))) : List (Record ctx Q) :=
  ps.map (fun p => ⟨(),p,realCompletion ctx Q oracle p⟩)

def idealRecords (ctx : Context) (Q : Nat) (table : RawKey Q → Digest32)
    (ps : List (Option (Packet ctx Q))) : List (Record ctx Q) :=
  ps.map (fun p => ⟨(),p,idealCompletion ctx Q table p⟩)

theorem readSelections_real_result (ctx : Context) (Q : Nat) (oracle : PrimitiveOracle)
    (ps : List (Option (Packet ctx Q))) (next : List (Record ctx Q) → Program R) :
    (runReal oracle ctx.iv (readSelections ctx Q ps next)).view.result =
      (runReal oracle ctx.iv (next (realRecords ctx Q oracle ps))).view.result := by
  induction ps generalizing next with
  | nil => rfl
  | cons p ps ih =>
    cases p with
    | none => exact ih _
    | some p =>
      rw [readSelections, readCallerThenPackets_real_result, ih]
      rfl

theorem readSelections_ideal_result (ctx : Context) (Q : Nat) {Seed State : Type}
    (sim : Simulator Q Seed State) (table : RawKey Q → Digest32) (state : State)
    (ps : List (Option (Packet ctx Q))) (next : List (Record ctx Q) → Program R)
    (value : List (Record ctx Q) → R)
    (after : ∀ records remaining (cap : remaining ≤ Q) (counted : Counts remaining (next records)),
      (runIdeal sim table ctx.iv state (next records) remaining cap counted).view.result = value records)
    (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining (readSelections ctx Q ps next)) :
    (runIdeal sim table ctx.iv state (readSelections ctx Q ps next) remaining cap counted).view.result =
      value (idealRecords ctx Q table ps) := by
  induction ps generalizing next value remaining with
  | nil => exact after [] remaining cap counted
  | cons p ps ih =>
    cases p with
    | none => exact ih _ _ (fun records => after (⟨(),none,[]⟩ :: records)) remaining cap counted
    | some p =>
      exact readCallerThenPackets_ideal_result ctx Q sim table state p _ _ _
        (fun history => value (⟨(),some p,history⟩ :: idealRecords ctx Q table ps))
        (fun history rem hc hn => ih _ _ (fun records => after (⟨(),some p,history⟩ :: records)) rem hc hn)
        remaining cap counted

theorem backfill_real_result (ctx : Context) (Q : Nat) (oracle : PrimitiveOracle)
    (result : R) (requests : List (RawKey Q)) (final : Option (Packet ctx Q)) :
    (runReal oracle ctx.iv (backfill ctx Q result requests final)).view.result =
      ⟨result,realRecords ctx Q oracle (selections ctx Q requests final)⟩ := by
  rw [backfill, readSelections_real_result]
  rfl

theorem backfill_ideal_result (ctx : Context) (Q : Nat) {Seed State : Type}
    (sim : Simulator Q Seed State) (table : RawKey Q → Digest32) (state : State)
    (result : R) (requests : List (RawKey Q)) (final : Option (Packet ctx Q))
    (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining (backfill ctx Q result requests final)) :
    (runIdeal sim table ctx.iv state (backfill ctx Q result requests final) remaining cap counted).view.result =
      ⟨result,idealRecords ctx Q table (selections ctx Q requests final)⟩ :=
  readSelections_ideal_result ctx Q sim table state _ _
    (fun records => (⟨result,records⟩ : Completed ctx Q R))
    (fun _ _ _ _ => rfl) remaining cap counted

theorem readSelections_counted (ctx : Context) (Q : Nat) (ps : List (Option (Packet ctx Q)))
    (next : List (Record ctx Q) → Program R) (budget : Nat)
    (after : ∀ records, Counts budget (next records)) :
    Counts (selectionsCost ctx Q ps + budget) (readSelections ctx Q ps next) := by
  induction ps generalizing next with
  | nil => simpa [selectionsCost, readSelections] using after []
  | cons p ps ih =>
    cases p with
    | none =>
      simpa [selectionsCost, completionCost, readSelections] using
        (ih _ (fun records => after (⟨(),none,[]⟩ :: records)))
    | some p =>
      have h := readCallerThenPackets_counted ctx Q p (callerPositions ctx Q p)
        (terminalCompletion ctx Q (some p)) _ (selectionsCost ctx Q ps + budget)
        (fun history => ih _ (fun records => after (⟨(),some p,history⟩ :: records)))
      simpa only [selectionsCost, List.map_cons, List.sum_cons, completionCost,
        Nat.add_assoc, readSelections] using h

theorem backfill_counted (ctx : Context) (Q : Nat) (result : R)
    (requests : List (RawKey Q)) (final : Option (Packet ctx Q)) :
    Counts (cost ctx Q requests final) (backfill ctx Q result requests final) := by
  simpa only [cost, backfill, Nat.add_zero] using
    readSelections_counted ctx Q (selections ctx Q requests final)
      (fun records => Program.done (⟨result,records⟩ : Completed ctx Q R)) 0 (fun _ => True.intro)

/-- Composition is certified for every continuation answer, not only the
observed real or ideal execution. The caller must budget the physical suffix. -/
theorem bind_backfill_counted (ctx : Context) (Q : Nat) (program : Program R)
    (requests : R → List (RawKey Q)) (final : R → Option (Packet ctx Q))
    (a b : Nat) (before : Counts a program)
    (bound : ∀ result, cost ctx Q (requests result) (final result) ≤ b) :
    Counts (a+b) (WHIRModeFinal.bind program (fun result => backfill ctx Q result (requests result) (final result))) :=
  bind_counted program _ a b before
    (fun result => counts_mono (backfill_counted ctx Q result _ _) (bound result))

/-- The exact cost expands into full caller paths and every block of every
ancestor and selected packet; packet repeats occur separately in this sum. -/
theorem cost_expansion (ctx : Context) (Q : Nat) (requests : List (RawKey Q))
    (final : Option (Packet ctx Q)) :
    cost ctx Q requests final =
      ((requests.map (fun key => completionCost ctx Q ((RawWHIRKeys.recognize ctx Q key).map Sigma.fst))).sum +
        completionCost ctx Q final) := by
  simp [cost, selectionsCost, selections, List.map_map, Function.comp_def]

/-- Completion membership includes callers, all ancestors, and the packet. -/
def completionKeys (ctx : Context) (Q : Nat) (p : Packet ctx Q) : List (GroupKey ctx Q) :=
  dependencyKeys ctx Q (.inl p) ++ [.inl p]

set_option backward.isDefEq.respectTransparency false in
theorem idealCompletion_eq (ctx : Context) (Q : Nat) (table : RawKey Q → Digest32)
    (p : Packet ctx Q) :
    idealCompletion ctx Q table (some p) =
      (completionKeys ctx Q p).map (fun key => ⟨key,(partition ctx Q).split table key⟩) := by
  rw [idealCompletion_some]
  unfold completionKeys dependencyKeys Partition.dependencies callerPlan schedule
  change _ = (((RawWHIRKeys.callerGroups ctx Q p).map
    (fun key => (Sum.inr key : GroupKey ctx Q)) ++
    (RawWHIRKeys.ancestors ctx Q p).map (fun p => (Sum.inl p : GroupKey ctx Q))) ++
    [Sum.inl p]).map
      (fun key => (⟨key,(partition ctx Q).split table key⟩ : Sigma (GroupAnswer ctx Q)))
  rw [List.map_append, List.map_append, List.map_map, List.map_map]
  simp only [idealHistory, List.map_append, List.map_cons, List.map_nil, List.append_assoc]
  rfl

theorem idealCompletion_agrees (ctx : Context) (Q : Nat) (table : RawKey Q → Digest32)
    (p : Option (Packet ctx Q)) (entry : Sigma (GroupAnswer ctx Q))
    (member : entry ∈ idealCompletion ctx Q table p) :
    (partition ctx Q).split table entry.1 = entry.2 := by
  cases p with
  | none => simp [idealCompletion] at member
  | some p =>
    rw [idealCompletion_eq] at member
    obtain ⟨key,_,rfl⟩ := List.mem_map.mp member
    rfl

theorem idealCompletion_covers (ctx : Context) (Q : Nat) (table : RawKey Q → Digest32)
    (p : Packet ctx Q) (key : GroupKey ctx Q) (member : key ∈ completionKeys ctx Q p) :
    (⟨key,(partition ctx Q).split table key⟩ : Sigma (GroupAnswer ctx Q)) ∈
      idealCompletion ctx Q table (some p) := by
  rw [idealCompletion_eq]
  exact List.mem_map.mpr ⟨key,member,rfl⟩

theorem recognized_covered (ctx : Context) (Q : Nat) (table : RawKey Q → Digest32)
    (requests : List (RawKey Q)) (final : Option (Packet ctx Q))
    (raw : RawKey Q) (member : raw ∈ requests) (pos : RawWHIRKeys.Position ctx Q)
    (recognized : RawWHIRKeys.recognize ctx Q raw = some pos) :
    (⟨(),some pos.1,idealCompletion ctx Q table (some pos.1)⟩ : Record ctx Q) ∈
      idealRecords ctx Q table (selections ctx Q requests final) := by
  apply List.mem_map.mpr
  refine ⟨some pos.1,List.mem_append_left _ ?_,rfl⟩
  exact List.mem_map.mpr ⟨raw,member,by simp [recognized]⟩

theorem final_covered (ctx : Context) (Q : Nat) (table : RawKey Q → Digest32)
    (requests : List (RawKey Q)) (final : Option (Packet ctx Q)) :
    (⟨(),final,idealCompletion ctx Q table final⟩ : Record ctx Q) ∈
      idealRecords ctx Q table (selections ctx Q requests final) := by
  apply List.mem_map.mpr
  exact ⟨final,List.mem_append_right _ (by simp),rfl⟩

/-- A completed public answer equals any existing private immutable cache hit.
This is a consequence of the proved compiler invariant, not a cover premise. -/
theorem agrees_compiler_cache (ctx : Context) (Q : Nat) (table : RawKey Q → Digest32)
    {S : Type} {K : Nat} (final : S → Option (Packet ctx Q))
    (program : TypedOracleCompiler.Sampling (RawKey Q) (fun _ => Digest32) S K)
    (p : Option (Packet ctx Q)) (entry : Sigma (GroupAnswer ctx Q))
    (member : entry ∈ idealCompletion ctx Q table p) (answer : GroupAnswer ctx Q entry.1)
    (hit : (tableExecution ctx Q final program table).2 entry.1 = some answer) :
    entry.2 = answer :=
  (idealCompletion_agrees ctx Q table p entry member).symm.trans
    (tableExecution_cache ctx Q final program table entry.1 answer hit)

end Whir.WHIRPublicBackfill

namespace Whir.WHIRPublicBackfill
open FiatShamirGame DuplexFraming DuplexModeGame
open RawWHIRKeys (Context Packet)
open RawOracleCoupling.Concrete WHIRModeFinal

/-- A finite executable maximum over the actual catalog profile alphabet and
scheduled positions, rather than a claimed constant packet width. -/
def maxPacketBlocks (ctx : Context) : Nat :=
  Finset.univ.sup (fun profile : ParameterBounds.Profile =>
    (Finset.range RawWHIRKeys.maxDepth).sup
      (fun n => (RawWHIRKeys.width ctx.mode profile n + 31) / 32))

theorem blocks_le_max (ctx : Context) (Q : Nat) (p : Packet ctx Q) :
    RawWHIRKeys.blocks ctx p.val ≤ maxPacketBlocks ctx := by
  have positive := List.length_pos_iff.mpr p.property.2.1
  have depth := (RawWHIRKeys.packet_depth ctx Q p).trans
    (RawWHIRKeys.profile_depth_le p.val.profile)
  apply le_trans (Finset.le_sup (f := fun n => (RawWHIRKeys.width ctx.mode p.val.profile n + 31) / 32)
    (Finset.mem_range.mpr (show p.val.messages.length - 1 < RawWHIRKeys.maxDepth by omega)))
  exact Finset.le_sup (f := fun profile : ParameterBounds.Profile =>
    (Finset.range RawWHIRKeys.maxDepth).sup
      (fun n => (RawWHIRKeys.width ctx.mode profile n + 31) / 32)) (Finset.mem_univ _)

private theorem sum_map_le {A : Type} (xs : List A) (f : A → Nat) (bound : Nat)
    (bounded : ∀ x ∈ xs, f x ≤ bound) : (xs.map f).sum ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have head := bounded x (by simp)
    have rest := ih (fun a ha => bounded a (List.mem_cons_of_mem x ha))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

theorem packetCost_bound (ctx : Context) (Q : Nat) (p : Packet ctx Q) :
    packetCost ctx Q p ≤ maxPacketBlocks ctx * Q := by
  apply le_trans (b := RawWHIRKeys.blocks ctx p.val * Q)
  · unfold packetCost
    calc
      _ ≤ ∑ _i : Fin (RawWHIRKeys.blocks ctx p.val), Q :=
        Finset.sum_le_sum (fun i _ => by
          rw [RawWHIRKeys.pathCost_block]
          exact RawWHIRKeys.packet_pathBound ctx Q p)
      _ = _ := by simp
  · exact Nat.mul_le_mul_right Q (blocks_le_max ctx Q p)

theorem completionCost_bound (ctx : Context) (Q : Nat) (p : Option (Packet ctx Q)) :
    completionCost ctx Q p ≤ (ctx.callerOutputCap + RawWHIRKeys.maxDepth * maxPacketBlocks ctx) * Q := by
  cases p with
  | none => exact Nat.zero_le _
  | some p =>
    have callers := sum_map_le (callerPositions ctx Q p) (fun q => pathCost q.val) Q
      (fun q _ => RawWHIRKeys.callerOutput_pathBound ctx Q p q.val q.property)
    have len : (callerPositions ctx Q p).length ≤ ctx.callerOutputCap := by
      rw [callerPositions, List.length_attach, WHIRCallerOutputs.callerOutputs_length]
      exact RawWHIRKeys.packet_callerOutputBound ctx Q p
    have packets := sum_map_le (terminalCompletion ctx Q (some p)) (packetCost ctx Q)
      (maxPacketBlocks ctx * Q) (fun packet _ => packetCost_bound ctx Q packet)
    have packetLen := terminalCompletion_bound ctx Q (some p)
    have c := callers.trans (Nat.mul_le_mul_right Q len)
    have ps := packets.trans (Nat.mul_le_mul_right (maxPacketBlocks ctx * Q) packetLen)
    change callerCost (callerPositions ctx Q p) + packetsCost ctx Q (terminalCompletion ctx Q (some p)) ≤ _
    dsimp only [callerCost, packetsCost]
    calc
      _ ≤ ctx.callerOutputCap * Q + RawWHIRKeys.maxDepth * (maxPacketBlocks ctx * Q) := Nat.add_le_add c ps
      _ = _ := by rw [Nat.add_mul, Nat.mul_assoc]

def overhead (ctx : Context) (Q requestCount : Nat) : Nat :=
  (requestCount + 1) * ((ctx.callerOutputCap + RawWHIRKeys.maxDepth * maxPacketBlocks ctx) * Q)

theorem cost_bound (ctx : Context) (Q : Nat) (requests : List (RawKey Q))
    (final : Option (Packet ctx Q)) :
    cost ctx Q requests final ≤ overhead ctx Q requests.length := by
  have h := sum_map_le (selections ctx Q requests final) (completionCost ctx Q)
    ((ctx.callerOutputCap + RawWHIRKeys.maxDepth * maxPacketBlocks ctx) * Q)
    (fun p _ => completionCost_bound ctx Q p)
  simpa [cost, selectionsCost, overhead, selections] using h

end Whir.WHIRPublicBackfill

namespace Whir.WHIRPublicBackfill
open FiatShamirGame DuplexFraming DuplexModeGame
open RawWHIRKeys (Context Packet)
open RawOracleCoupling.Concrete WHIRModeFinal

theorem idealRecords_length (ctx : Context) (Q : Nat) (table : RawKey Q → Digest32)
    (requests : List (RawKey Q)) (final : Option (Packet ctx Q)) :
    (idealRecords ctx Q table (selections ctx Q requests final)).length = requests.length + 1 := by
  simp [idealRecords, selections]

/-- Exact positional provenance, including empty garbage cells and repeats. -/
theorem idealRecords_request (ctx : Context) (Q : Nat) (table : RawKey Q → Digest32)
    (requests : List (RawKey Q)) (final : Option (Packet ctx Q)) (i : Fin requests.length) :
    (idealRecords ctx Q table (selections ctx Q requests final))[i.val]'(by
      rw [idealRecords_length]; omega) =
      let selected := (RawWHIRKeys.recognize ctx Q requests[i.val]).map Sigma.fst
      (⟨(),selected,idealCompletion ctx Q table selected⟩ : Record ctx Q) := by
  simp only [idealRecords, List.getElem_map]
  unfold selections
  rw [List.getElem_append_left (by simpa only [List.length_map] using i.isLt)]
  simp only [List.getElem_map]

theorem idealRecords_final (ctx : Context) (Q : Nat) (table : RawKey Q → Digest32)
    (requests : List (RawKey Q)) (final : Option (Packet ctx Q)) :
    (idealRecords ctx Q table (selections ctx Q requests final))[requests.length]'(by
      rw [idealRecords_length]; omega) =
      (⟨(),final,idealCompletion ctx Q table final⟩ : Record ctx Q) := by
  simp [idealRecords, selections]

/-- At the exact request index, all dependency answers and the touched packet
are present and equal to the real ideal-table values. -/
theorem request_dependencies (ctx : Context) (Q : Nat) (table : RawKey Q → Digest32)
    (requests : List (RawKey Q)) (final : Option (Packet ctx Q)) (i : Fin requests.length)
    (pos : RawWHIRKeys.Position ctx Q)
    (recognized : RawWHIRKeys.recognize ctx Q requests[i.val] = some pos)
    (key : GroupKey ctx Q) (member : key ∈ completionKeys ctx Q pos.1) :
    (⟨key,(partition ctx Q).split table key⟩ : Sigma (GroupAnswer ctx Q)) ∈
      ((idealRecords ctx Q table (selections ctx Q requests final))[i.val]'(by
        rw [idealRecords_length]; omega)).history := by
  rw [idealRecords_request]
  simp only [recognized, Option.map_some]
  exact idealCompletion_covers ctx Q table pos.1 key member

theorem packetCost_full_paths (ctx : Context) (Q : Nat) (p : Packet ctx Q) :
    packetCost ctx Q p = RawWHIRKeys.blocks ctx p.val *
      ((p.val.entryFrames.flatMap DuplexEncoding.framePlan).length +
       ((WHIRHistoryKey.canonicalFrames (RawWHIRKeys.width ctx.mode p.val.profile)
         p.val.messages).flatMap DuplexEncoding.framePlan).length + 2) := by
  simp [packetCost, RawWHIRKeys.pathCost_prefix]

private def smokeContext : Context :=
  ⟨.stack,fun _ => 0,fun _ => 1,fun _ => some (0,0),fun _ => 1,1⟩

private def smokePacket (clone : Byte) (advanced : Bool) : Option (Packet smokeContext 4096) :=
  let messages := if advanced then
      [⟨List.replicate (WHIRHistory.replyScalarCount
        (c := ParameterBounds.config (0,0)) .initial) 0,none⟩,WHIRHistoryKey.initialPending]
    else [WHIRHistoryKey.initialPending]
  let p : RawWHIRKeys.PacketData := ⟨fun _ => 2,(0,0),messages,[.absorb 32 [clone]]⟩
  if valid : RawWHIRKeys.ValidPacket smokeContext 4096 p then some ⟨p,valid⟩ else none

private def smokeMatches (table : RawKey 4096 → Digest32) (record : Record smokeContext 4096) : Bool :=
  record.history.all fun entry =>
    match entry with
    | ⟨.inl p,answer⟩ => decide (answer = idealPacket smokeContext 4096 table p)
    | ⟨.inr key,answer⟩ => decide (answer = table key.val)

/-- Executable regression: a prior caller raw key, nonfinal packet prequery,
same-statement different-entry clone, unrelated garbage, and repeated packet.
The real and ideal interpreters execute the actual construction requests. -/
private def smoke : IO Unit := do
  let some early := smokePacket 3 false | throw (IO.userError "early packet rejected")
  let some clone := smokePacket 4 false | throw (IO.userError "clone packet rejected")
  let some final := smokePacket 3 true | throw (IO.userError "final packet rejected")
  let some prior := (RawWHIRKeys.callerGroups smokeContext 4096 final).head? |
    throw (IO.userError "missing prior caller output")
  let garbage : RawKey 4096 :=
    (⟨⟨0,by decide⟩,Fin.elim0⟩,⟨⟨0,by decide⟩,Fin.elim0⟩)
  let raw (p : Packet smokeContext 4096) :=
    RawWHIRKeys.encode smokeContext 4096 ⟨p,⟨0,RawWHIRKeys.blocks_positive smokeContext p.val⟩⟩
  let requests := [prior.val,raw early,raw clone,garbage,raw early]
  let program := backfill smokeContext 4096 (37 : Nat) requests (some final)
  let charge := cost smokeContext 4096 requests (some final)
  if bounded : charge ≤ 4096 then
    let table : RawKey 4096 → Digest32 := fun key _ =>
      ⟨(key.1.1.val + key.2.1.val) % 256,Nat.mod_lt _ (by decide)⟩
    let sim : Simulator 4096 Unit Unit := ⟨id,fun state _ => .done (state,fun _ => 0)⟩
    let ideal := runIdeal sim table smokeContext.iv () program charge bounded
      (backfill_counted smokeContext 4096 37 requests (some final))
    let real := runReal (fun input i => input.block ⟨i.val,by omega⟩) smokeContext.iv program
    let sizes := ideal.view.result.records.map (fun record => record.history.length)
    unless sizes == [0,2,2,0,2,3] do
      throw (IO.userError s!"completion cell sizes: {sizes}")
    unless ideal.view.result.result == 37 && real.view.result.result == 37 &&
        ideal.primitiveCost == charge && real.primitiveCost == charge &&
        ideal.constructionRequests == 29 && real.constructionRequests == 29 &&
        ideal.view.result.records.all (smokeMatches table) &&
        decide (raw early ≠ raw clone) do
      throw (IO.userError "physical backfill result, charge, answer, or clone mismatch")
    IO.println s!"public backfill smoke: cells={sizes}, cost={charge}, construction requests={ideal.constructionRequests}, result=37; caller/prequery/clone/garbage/repeats checked"
  else throw (IO.userError s!"backfill exceeds actual mode budget: {charge}")

#eval smoke

end Whir.WHIRPublicBackfill

namespace Whir.WHIRPublicBackfill
open FiatShamirGame DuplexFraming DuplexModeGame
open RawWHIRKeys (Context Packet)
open RawOracleCoupling RawOracleCoupling.Concrete WHIRModeFinal

/-- The public path cap is independent of the raw-key domain bound. -/
theorem recognized_path_eq_raw_length (ctx : Context) (Q : Nat) (raw : RawKey Q)
    (pos : RawWHIRKeys.Position ctx Q)
    (recognized : RawWHIRKeys.recognize ctx Q raw = some pos) :
    pathCost (RawWHIRKeys.coordinate ctx pos.1.val 0) = raw.1.1.val := by
  have h := congrArg (fun key : RawKey Q => key.1.1.val)
    (RawWHIRKeys.encode_recognize ctx Q raw pos recognized)
  change (modeKey ctx.iv (RawWHIRKeys.coordinate ctx pos.1.val pos.2.val)).message.length = _ at h
  rw [(modeKey_lengths _ _).1, RawWHIRKeys.pathCost_block] at h
  exact h

theorem ancestor_path_le (ctx : Context) (Q : Nat) (p a : Packet ctx Q)
    (member : a ∈ RawWHIRKeys.ancestors ctx Q p) :
    pathCost (RawWHIRKeys.coordinate ctx a.val 0) ≤
      pathCost (RawWHIRKeys.coordinate ctx p.val 0) := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
  have h := RawWHIRKeys.canonicalCost_drop_le (RawWHIRKeys.width ctx.mode p.val.profile)
    p.val.messages (p.val.messages.length - 1 - i.val)
  simp only [RawWHIRKeys.pathCost_prefix, RawWHIRKeys.dropPacket]
  omega

theorem packetCost_path_bound (ctx : Context) (Q M : Nat) (p : Packet ctx Q)
    (bounded : pathCost (RawWHIRKeys.coordinate ctx p.val 0) ≤ M) :
    packetCost ctx Q p ≤ maxPacketBlocks ctx * M := by
  apply le_trans (b := RawWHIRKeys.blocks ctx p.val * M)
  · unfold packetCost
    calc
      _ ≤ ∑ _i : Fin (RawWHIRKeys.blocks ctx p.val), M :=
        Finset.sum_le_sum (fun i _ => by simpa only [RawWHIRKeys.pathCost_block] using bounded)
      _ = _ := by simp
  · exact Nat.mul_le_mul_right M (blocks_le_max ctx Q p)

def pathFactor (ctx : Context) : Nat :=
  ctx.callerOutputCap + RawWHIRKeys.maxDepth * maxPacketBlocks ctx

theorem completionCost_path_bound (ctx : Context) (Q M : Nat) (p : Packet ctx Q)
    (bounded : pathCost (RawWHIRKeys.coordinate ctx p.val 0) ≤ M) :
    completionCost ctx Q (some p) ≤ pathFactor ctx * M := by
  have callers := sum_map_le (callerPositions ctx Q p) (fun q => pathCost q.val) M
    (fun q _ => (WHIRCallerOutputs.callerOutputs_extended_pathCost_le
      (RawWHIRKeys.entry ctx p.val) q.val q.property
      (WHIRHistoryKey.canonicalFrames (RawWHIRKeys.width ctx.mode p.val.profile) p.val.messages)
      (.output 0)).trans bounded)
  have callerLen : (callerPositions ctx Q p).length ≤ ctx.callerOutputCap := by
    rw [callerPositions, List.length_attach, WHIRCallerOutputs.callerOutputs_length]
    exact RawWHIRKeys.packet_callerOutputBound ctx Q p
  have packets := sum_map_le (terminalCompletion ctx Q (some p)) (packetCost ctx Q)
    (maxPacketBlocks ctx * M) (by
      intro a ha
      apply packetCost_path_bound ctx Q M a
      change a ∈ RawWHIRKeys.ancestors ctx Q p ++ [p] at ha
      rcases List.mem_append.mp ha with ha | ha
      · exact (ancestor_path_le ctx Q p a ha).trans bounded
      · simpa only [List.mem_singleton.mp ha] using bounded)
  have c := callers.trans (Nat.mul_le_mul_right M callerLen)
  have ps := packets.trans (Nat.mul_le_mul_right (maxPacketBlocks ctx * M)
    (terminalCompletion_bound ctx Q (some p)))
  change callerCost (callerPositions ctx Q p) + packetsCost ctx Q (terminalCompletion ctx Q (some p)) ≤ _
  dsimp only [callerCost, packetsCost, pathFactor]
  calc
    _ ≤ ctx.callerOutputCap * M + RawWHIRKeys.maxDepth * (maxPacketBlocks ctx * M) := Nat.add_le_add c ps
    _ = _ := by rw [Nat.add_mul, Nat.mul_assoc]

/-- The prefix supplies an independent public message-length bound M. The
final selection is charged at its actual checked completion cost. -/
theorem cost_bound_prefix (ctx : Context) (Q M : Nat) (requests : List (RawKey Q))
    (final : Option (Packet ctx Q)) (bounded : ∀ raw ∈ requests, raw.1.1.val ≤ M) :
    cost ctx Q requests final ≤ requests.length * (pathFactor ctx * M) + completionCost ctx Q final := by
  rw [cost_expansion]
  apply Nat.add_le_add_right
  apply sum_map_le
  intro raw member
  cases recognized : RawWHIRKeys.recognize ctx Q raw with
  | none => exact Nat.zero_le _
  | some pos =>
    apply completionCost_path_bound
    rw [recognized_path_eq_raw_length ctx Q raw pos recognized]
    exact bounded raw member

/-- No circular Qtotal factor: M bounds prior public paths and Mf bounds the
selected final packet. Both may be strictly smaller than RawKey's domain Q. -/
theorem cost_bound_pathCaps (ctx : Context) (Q M Mf : Nat) (requests : List (RawKey Q))
    (final : Option (Packet ctx Q)) (bounded : ∀ raw ∈ requests, raw.1.1.val ≤ M)
    (finalBound : ∀ p, final = some p → pathCost (RawWHIRKeys.coordinate ctx p.val 0) ≤ Mf) :
    cost ctx Q requests final ≤ requests.length * (pathFactor ctx * M) + pathFactor ctx * Mf := by
  apply (cost_bound_prefix ctx Q M requests final bounded).trans
  apply Nat.add_le_add_left
  cases final with
  | none => exact Nat.zero_le _
  | some p => exact completionCost_path_bound ctx Q Mf p (finalBound p rfl)

end Whir.WHIRPublicBackfill

namespace Whir.WHIRPublicBackfill
open FiatShamirGame DuplexFraming DuplexModeGame
open RawWHIRKeys (Context Packet)
open RawOracleCoupling RawOracleCoupling.Concrete WHIRModeFinal
open TypedFiatShamirGame

private instance (ctx : Context) (Q : Nat) : DecidableEq (GroupKey ctx Q) := inferInstance

abbrev PublicCache (ctx : Context) (Q : Nat) := Cache (GroupKey ctx Q) (GroupAnswer ctx Q)

/-- Executable finite-support cache reconstructed solely from explicit records.
No total raw table, simulator state, or private compiler cache is an argument.
Earlier duplicate cells take precedence; table consistency makes this choice
irrelevant on actual ideal executions. -/
def entriesCache (ctx : Context) (Q : Nat) :
    List (Sigma (GroupAnswer ctx Q)) → PublicCache ctx Q
  | [] => fun _ => none
  | entry :: rest => put (entriesCache ctx Q rest) entry.1 entry.2

def garbageEntry (ctx : Context) (Q : Nat) (answer : RawKey Q × Digest32) :
    Option (Sigma (GroupAnswer ctx Q)) :=
  match recognized : RawWHIRKeys.recognize ctx Q answer.1 with
  | none => some ⟨.inr ⟨answer.1,recognized⟩,answer.2⟩
  | some _ => none

def observableEntries (ctx : Context) (Q : Nat) (answers : List (RawKey Q × Digest32))
    (records : List (Record ctx Q)) : List (Sigma (GroupAnswer ctx Q)) :=
  answers.filterMap (garbageEntry ctx Q) ++ records.flatMap (fun record => record.history)

def observableCache (ctx : Context) (Q : Nat) (answers : List (RawKey Q × Digest32))
    (records : List (Record ctx Q)) : PublicCache ctx Q :=
  entriesCache ctx Q (observableEntries ctx Q answers records)

theorem entriesCache_consistent (ctx : Context) (Q : Nat) (table : RawKey Q → Digest32)
    (entries : List (Sigma (GroupAnswer ctx Q)))
    (consistent : ∀ entry ∈ entries, (partition ctx Q).split table entry.1 = entry.2)
    (key : GroupKey ctx Q) (answer : GroupAnswer ctx Q key)
    (hit : entriesCache ctx Q entries key = some answer) :
    (partition ctx Q).split table key = answer := by
  induction entries with
  | nil => simp [entriesCache] at hit
  | cons entry rest ih =>
    by_cases same : key = entry.1
    · subst key
      have equal : entry.2 = answer := by simpa only [entriesCache, put_self, Option.some.injEq] using hit
      exact (consistent entry List.mem_cons_self).trans equal
    · apply ih (fun e he => consistent e (List.mem_cons_of_mem entry he))
      simpa only [entriesCache, put_other _ _ _ _ same] using hit

theorem entriesCache_covers (ctx : Context) (Q : Nat) (table : RawKey Q → Digest32)
    (entries : List (Sigma (GroupAnswer ctx Q)))
    (consistent : ∀ entry ∈ entries, (partition ctx Q).split table entry.1 = entry.2)
    (key : GroupKey ctx Q) (member : key ∈ entries.map Sigma.fst) :
    entriesCache ctx Q entries key = some ((partition ctx Q).split table key) := by
  induction entries with
  | nil => simp at member
  | cons entry rest ih =>
    by_cases same : key = entry.1
    · subst key
      rw [entriesCache, put_self, consistent entry List.mem_cons_self]
    · rw [entriesCache, put_other _ _ _ _ same]
      apply ih (fun e he => consistent e (List.mem_cons_of_mem entry he))
      simpa only [List.map_cons, List.mem_cons, same, false_or] using member

theorem observableEntries_consistent (ctx : Context) (Q : Nat) (table : RawKey Q → Digest32)
    (answers : List (RawKey Q × Digest32)) (ps : List (Option (Packet ctx Q)))
    (consistent : ∀ answer ∈ answers, table answer.1 = answer.2)
    (entry : Sigma (GroupAnswer ctx Q))
    (member : entry ∈ observableEntries ctx Q answers (idealRecords ctx Q table ps)) :
    (partition ctx Q).split table entry.1 = entry.2 := by
  rcases List.mem_append.mp member with garbage | packet
  · obtain ⟨answer,ha,he⟩ := List.mem_filterMap.mp garbage
    unfold garbageEntry at he
    split at he
    · cases Option.some.inj he
      exact consistent answer ha
    · contradiction
  · obtain ⟨record,hr,he⟩ := List.mem_flatMap.mp packet
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hr
    exact idealCompletion_agrees ctx Q table p entry he

theorem observableCache_consistent (ctx : Context) (Q : Nat) (table : RawKey Q → Digest32)
    (answers : List (RawKey Q × Digest32)) (ps : List (Option (Packet ctx Q)))
    (consistent : ∀ answer ∈ answers, table answer.1 = answer.2)
    (key : GroupKey ctx Q) (answer : GroupAnswer ctx Q key)
    (hit : observableCache ctx Q answers (idealRecords ctx Q table ps) key = some answer) :
    (partition ctx Q).split table key = answer :=
  entriesCache_consistent ctx Q table _ (observableEntries_consistent ctx Q table answers ps consistent)
    key answer hit

/-- Every physically returned dependency is a genuine reconstructed cache hit. -/
theorem observableCache_completion (ctx : Context) (Q : Nat) (table : RawKey Q → Digest32)
    (answers : List (RawKey Q × Digest32)) (ps : List (Option (Packet ctx Q)))
    (consistent : ∀ answer ∈ answers, table answer.1 = answer.2)
    (p : Packet ctx Q) (selected : some p ∈ ps)
    (key : GroupKey ctx Q) (member : key ∈ completionKeys ctx Q p) :
    observableCache ctx Q answers (idealRecords ctx Q table ps) key =
      some ((partition ctx Q).split table key) := by
  apply entriesCache_covers ctx Q table _
    (observableEntries_consistent ctx Q table answers ps consistent)
  apply List.mem_map.mpr
  refine ⟨⟨key,(partition ctx Q).split table key⟩,?_,rfl⟩
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨⟨(),some p,idealCompletion ctx Q table (some p)⟩,?_,
    idealCompletion_covers ctx Q table p key member⟩
  exact List.mem_map.mpr ⟨some p,selected,rfl⟩

theorem observableCache_garbage (ctx : Context) (Q : Nat) (table : RawKey Q → Digest32)
    (answers : List (RawKey Q × Digest32)) (ps : List (Option (Packet ctx Q)))
    (consistent : ∀ answer ∈ answers, table answer.1 = answer.2)
    (raw : (partition ctx Q).Garbage) (answer : Digest32) (member : (raw.val,answer) ∈ answers) :
    observableCache ctx Q answers (idealRecords ctx Q table ps) (.inr raw) = some (table raw.val) := by
  apply entriesCache_covers ctx Q table _
    (observableEntries_consistent ctx Q table answers ps consistent)
  apply List.mem_map.mpr
  refine ⟨⟨.inr raw,answer⟩,List.mem_append_left _ ?_,rfl⟩
  apply List.mem_filterMap.mpr
  refine ⟨(raw.val,answer),member,?_⟩
  have missing : RawWHIRKeys.recognize ctx Q raw.val = none := raw.property
  unfold garbageEntry
  split
  · rfl
  · rename_i pos recognized
    have impossible : (none : Option (RawWHIRKeys.Position ctx Q)) = some pos :=
      missing.symm.trans recognized
    cases impossible

theorem observableCache_request (ctx : Context) (Q : Nat) (table : RawKey Q → Digest32)
    (answers : List (RawKey Q × Digest32)) (requests : List (RawKey Q)) (final : Option (Packet ctx Q))
    (consistent : ∀ answer ∈ answers, table answer.1 = answer.2)
    (raw : RawKey Q) (requested : raw ∈ requests) (pos : RawWHIRKeys.Position ctx Q)
    (recognized : RawWHIRKeys.recognize ctx Q raw = some pos)
    (key : GroupKey ctx Q) (member : key ∈ completionKeys ctx Q pos.1) :
    observableCache ctx Q answers (idealRecords ctx Q table (selections ctx Q requests final)) key =
      some ((partition ctx Q).split table key) := by
  apply observableCache_completion ctx Q table answers _ consistent pos.1 _ key member
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨raw,requested,by simp [recognized]⟩

theorem observableCache_final (ctx : Context) (Q : Nat) (table : RawKey Q → Digest32)
    (answers : List (RawKey Q × Digest32)) (requests : List (RawKey Q)) (p : Packet ctx Q)
    (consistent : ∀ answer ∈ answers, table answer.1 = answer.2)
    (key : GroupKey ctx Q) (member : key ∈ completionKeys ctx Q p) :
    observableCache ctx Q answers (idealRecords ctx Q table (selections ctx Q requests (some p))) key =
      some ((partition ctx Q).split table key) := by
  apply observableCache_completion ctx Q table answers _ consistent p _ key member
  exact List.mem_append_right _ (by simp)

end Whir.WHIRPublicBackfill

namespace Whir.WHIRPublicBackfill
open FiatShamirGame DuplexFraming DuplexModeGame
open RawWHIRKeys (Context Packet)
open RawOracleCoupling RawOracleCoupling.Concrete WHIRModeFinal

/-- A partial oracle reconstructed from observed bytes; absence stays explicit.
There is no invented fallback answer for unseen raw requests. -/
def publicRawAnswer (ctx : Context) (Q : Nat) (cache : PublicCache ctx Q) (raw : RawKey Q) :
    Option Digest32 :=
  match recognized : RawWHIRKeys.recognize ctx Q raw with
  | some pos => (cache (.inl pos.1)).map (fun packet => packet pos.2)
  | none => cache (.inr ⟨raw,recognized⟩)

theorem publicRawAnswer_observed (ctx : Context) (Q : Nat) (table : RawKey Q → Digest32)
    (answers : List (RawKey Q × Digest32)) (final : Option (Packet ctx Q))
    (consistent : ∀ answer ∈ answers, table answer.1 = answer.2)
    (raw : RawKey Q) (answer : Digest32) (member : (raw,answer) ∈ answers) :
    publicRawAnswer ctx Q
      (observableCache ctx Q answers (idealRecords ctx Q table (selections ctx Q (answers.map Prod.fst) final)))
      raw = some answer := by
  unfold publicRawAnswer
  split
  · rename_i pos recognized
    have hit := observableCache_request ctx Q table answers (answers.map Prod.fst) final consistent
      raw (List.mem_map.mpr ⟨(raw,answer),member,rfl⟩) pos recognized (.inl pos.1)
      (List.mem_append_right _ (by simp))
    rw [hit, Option.map_some]
    change some (table (RawWHIRKeys.encode ctx Q pos)) = some answer
    rw [RawWHIRKeys.encode_recognize ctx Q raw pos recognized, consistent (raw,answer) member]
  · rename_i recognized
    have hit := observableCache_garbage ctx Q table answers
      (selections ctx Q (answers.map Prod.fst) final) consistent ⟨raw,recognized⟩ answer member
    exact hit.trans (congrArg some (consistent (raw,answer) member))

/-- On every publicly recognized request dependency, reconstruction equals the
actual compiler's immutable cached value, whenever that group was allocated.
The reconstruction hit is derived above, not supplied as a coverage premise. -/
theorem observableCache_compiler_request (ctx : Context) (Q : Nat) (table : RawKey Q → Digest32)
    (answers : List (RawKey Q × Digest32)) (requests : List (RawKey Q)) (selected : Option (Packet ctx Q))
    (consistent : ∀ answer ∈ answers, table answer.1 = answer.2)
    (raw : RawKey Q) (requested : raw ∈ requests) (pos : RawWHIRKeys.Position ctx Q)
    (recognized : RawWHIRKeys.recognize ctx Q raw = some pos)
    {R : Type} {K : Nat} (final : R → Option (Packet ctx Q))
    (program : TypedOracleCompiler.Sampling (RawKey Q) (fun _ => Digest32) R K)
    (key : GroupKey ctx Q) (member : key ∈ completionKeys ctx Q pos.1)
    (answer : GroupAnswer ctx Q key)
    (hit : (tableExecution ctx Q final program table).2 key = some answer) :
    observableCache ctx Q answers (idealRecords ctx Q table (selections ctx Q requests selected)) key =
      some answer := by
  rw [observableCache_request ctx Q table answers requests selected consistent raw requested pos recognized key member]
  exact congrArg some (tableExecution_cache ctx Q final program table key answer hit)

end Whir.WHIRPublicBackfill

namespace Whir.WHIRPublicBackfill
open FiatShamirGame DuplexFraming DuplexModeGame
open RawWHIRKeys (Context Packet)
open RawOracleCoupling.Concrete WHIRModeFinal

/-- A noncircular all-answer prefix/suffix certificate with independent public
source path and final path caps. Q only indexes the raw-key domain. -/
theorem bind_backfill_path_counted (ctx : Context) (Q A N M Mf : Nat) {R : Type}
    (program : Program R) (requests : R → List (RawKey Q)) (final : R → Option (Packet ctx Q))
    (before : Counts A program) (lengthBound : ∀ r, (requests r).length ≤ N)
    (paths : ∀ r raw, raw ∈ requests r → raw.1.1.val ≤ M)
    (finalPaths : ∀ r p, final r = some p → pathCost (RawWHIRKeys.coordinate ctx p.val 0) ≤ Mf) :
    Counts (A + (N * (pathFactor ctx * M) + pathFactor ctx * Mf))
      (WHIRModeFinal.bind program (fun r => backfill ctx Q r (requests r) (final r))) := by
  apply bind_backfill_counted ctx Q program requests final A _ before
  intro r
  exact (cost_bound_pathCaps ctx Q M Mf (requests r) (final r) (paths r) (finalPaths r)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ (lengthBound r)) _)

private def cacheSmoke : IO Unit := do
  let some early := smokePacket 3 false | throw (IO.userError "early packet rejected")
  let some clone := smokePacket 4 false | throw (IO.userError "clone packet rejected")
  let some final := smokePacket 3 true | throw (IO.userError "final packet rejected")
  let some prior := (RawWHIRKeys.callerGroups smokeContext 4096 final).head? |
    throw (IO.userError "missing prior caller output")
  let garbage : RawKey 4096 :=
    (⟨⟨0,by decide⟩,Fin.elim0⟩,⟨⟨0,by decide⟩,Fin.elim0⟩)
  let raw (p : Packet smokeContext 4096) :=
    RawWHIRKeys.encode smokeContext 4096 ⟨p,⟨0,RawWHIRKeys.blocks_positive smokeContext p.val⟩⟩
  let requests := [prior.val,raw early,raw clone,garbage,raw early]
  let table : RawKey 4096 → Digest32 := fun key _ =>
    ⟨(key.1.1.val + key.2.1.val) % 256,Nat.mod_lt _ (by decide)⟩
  let answers := requests.map (fun key => (key,table key))
  let charge := cost smokeContext 4096 requests (some final)
  if bounded : charge ≤ 4096 then
    let sim : Simulator 4096 Unit Unit := ⟨id,fun state _ => .done (state,fun _ => 0)⟩
    let execution := runIdeal sim table smokeContext.iv ()
      (backfill smokeContext 4096 (37 : Nat) requests (some final)) charge bounded
      (backfill_counted smokeContext 4096 37 requests (some final))
    let cache := observableCache smokeContext 4096 answers execution.view.result.records
    unless requests.all (fun key => decide (publicRawAnswer smokeContext 4096 cache key = some (table key))) do
      throw (IO.userError "observed raw cache reconstruction failed")
    unless decide (publicRawAnswer smokeContext 4096 cache (raw final) = some (table (raw final))) do
      throw (IO.userError "final packet cache reconstruction failed")
    let sourceCap := (requests.map (fun key => key.1.1.val)).foldl max 0
    let finalCap := pathCost (RawWHIRKeys.coordinate smokeContext final.val 0)
    let overhead := requests.length * (pathFactor smokeContext * sourceCap) + pathFactor smokeContext * finalCap
    unless charge ≤ overhead && sourceCap == 3 && finalCap == 4 do
      throw (IO.userError "independent path-cap overhead failed")
    IO.println s!"public cache smoke: observed raw replies and final reconstructed; source path cap={sourceCap}, final path cap={finalCap}, key domain=4096, maxDepth={RawWHIRKeys.maxDepth}, maxBlocks={maxPacketBlocks smokeContext}, overhead={overhead}, actual cost={charge}"
  else throw (IO.userError "cache smoke budget exceeded")

#eval cacheSmoke

end Whir.WHIRPublicBackfill
