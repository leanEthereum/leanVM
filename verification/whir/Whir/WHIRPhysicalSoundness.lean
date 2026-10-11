import Whir.WHIRPhysicalCaller
import Whir.WHIRPhysicalOpeningRuns
import Whir.PublicMerkleProbability
import Whir.WHIRPhysicalRoots
import Whir.WHIRPhysicalSnapshots

namespace Whir.WHIRPhysicalSoundness
open Concrete Protocol FiatShamirGame DuplexModeGame
open MerkleTransport MerkleTransport.Commitments
open WHIRPhysicalVerifier WHIRPhysicalReplay WHIRPhysicalOpeningRuns
open PublicMerkleProgram (Runs)
set_option maxHeartbeats 800000

private theorem bind_done_observations {R S : Type} (C : PrimitiveOracle) (iv : Digest32)
    (program : Program R) (finish : R → S) :
    (runReal C iv (WHIRModeFinal.bind program (fun value => .done (finish value)))).view.observations =
      (runReal C iv program).view.observations := by
  induction program with
  | done value => rfl
  | ask query next ih =>
    simpa only [WHIRModeFinal.bind,runReal,prepend] using
      congrArg (List.cons ⟨query,realAnswer C iv query⟩) (ih (realAnswer C iv query))

theorem openRows_observations (C : PrimitiveOracle) (iv : Digest32)
    (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) (base : Bool) :
    (runReal C iv (openRows proof root numLeaves queries rowWords leafWords base)).view.observations =
      (runReal C iv (PrunedMerkleProgram.verify proof root numLeaves queries rowWords leafWords)).view.observations :=
  bind_done_observations C iv _ _

/-- Every compression event in every returned Merkle path was executed by the
actual counted opener. Reconstructing the logical path adds no oracle call. -/
theorem openRows_plan_coverage (C : PrimitiveOracle) (iv : Digest32)
    (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) (base : Bool) (out : Opened)
    (accepted : (runReal C iv (openRows proof root numLeaves queries rowWords leafWords base)).view.result = some out)
    (path : RawPath) (member : path ∈ out.paths) (bytes : List Byte)
    (input : bytes ∈ path.opening.inputs (hashing (PublicMerkleLog.hash C)))
    (event : DuplexFraming.Node × Digest32) (present : event ∈ PublicMerkleLog.plan C bytes) :
    (⟨.primitive .verification event.1,event.2⟩ : Observation) ∈
      (runReal C iv (openRows proof root numLeaves queries rowWords leafWords base)).view.observations := by
  rw [openRows_observations]
  apply PrunedMerkleProgram.verify_opening_primitive_coverage C iv proof root numLeaves queries rowWords leafWords
    out.paths _ path member bytes input event present
  rw [PrunedMerkleProgram.verify_real_result]
  exact (openRows_real_accepted C iv proof root numLeaves queries rowWords leafWords base out accepted).1

theorem openQuery_evaluated (C : PrimitiveOracle) (iv : Digest32)
    (p : ParameterBounds.Profile) (i : Fin (ParameterBounds.config p).folds.size)
    (lanes : Nat) (proof : PrunedMerklePaths) (root : Digest32)
    (sample : CausalProbability.Sample (.query i)) (out : Opened)
    (accepted : (runReal C iv (openQuery p i lanes proof root sample)).view.result = some out) :
    ∀ path ∈ out.paths, ∀ bytes ∈ path.opening.inputs (hashing (PublicMerkleLog.hash C)),
      bytes.length < 2^56 ∧ ∀ event ∈ PublicMerkleLog.plan C bytes,
        (⟨.primitive .verification event.1,event.2⟩ : Observation) ∈
          (runReal C iv (openQuery p i lanes proof root sample)).view.observations := by
  have opened := (openRows_real_accepted C iv proof root
    (ParameterBounds.length (ParameterBounds.config p) i.val) (queryIndices p i sample)
    (if i.val = 0 then lanes else leafWords p i.val) (leafWords p i.val) (i.val == 0) out accepted).1
  have bounded := path_input_bounds_lt C proof root
    (ParameterBounds.length (ParameterBounds.config p) i.val) (queryIndices p i sample)
    (if i.val = 0 then lanes else leafWords p i.val) (leafWords p i.val) (2^56)
    out.paths opened (production_leaf_byte_tag_zero p i) (by decide)
  intro path member bytes input
  refine ⟨bounded path member bytes input,?_⟩
  intro event present
  exact openRows_plan_coverage C iv proof root _ _ _ _ _ out accepted path member bytes input event present

/-- The stored source opening record carries an actual indexed subrun, not a
caller-provided certificate linking ideal rows to a claimed transcript. -/
theorem observed_evaluated {p : ParameterBounds.Profile} {lanes : Nat}
    {proofs : Array PrunedMerklePaths} {observations : List Observation} {opening : QueryOpening p}
    (observed : ObservedOpening lanes proofs observations opening) (C : PrimitiveOracle) (iv : Digest32)
    (answers : ∀ o ∈ observations, o.answer = realAnswer C iv o.query) :
    ∀ path ∈ opening.result.paths, ∀ bytes ∈ path.opening.inputs (hashing (PublicMerkleLog.hash C)),
      bytes.length < 2^56 ∧ ∀ event ∈ PublicMerkleLog.plan C bytes,
        (⟨.primitive .verification event.1,event.2⟩ : Observation) ∈ observations := by
  obtain ⟨proof,_,accepted,covered⟩ := observed.real C iv answers
  intro path member bytes input
  obtain ⟨bound,executed⟩ := openQuery_evaluated C iv p opening.level lanes proof opening.root
    opening.sample opening.result accepted path member bytes input
  exact ⟨bound,fun event present => covered _ (executed event present)⟩

theorem observed_binding {p : ParameterBounds.Profile} {lanes : Nat}
    {proofs : Array PrunedMerklePaths} {observations : List Observation} {opening : QueryOpening p}
    (observed : ObservedOpening lanes proofs observations opening) (C : PrimitiveOracle) (iv : Digest32)
    (answers : ∀ o ∈ observations, o.answer = realAnswer C iv o.query)
    (oldLog : PublicMerkleLog.PublicLog) (authentic : PublicMerkleLog.AuthenticLog C oldLog)
    (retained : Records)
    (history : ∀ e ∈ retained, ∃ earlier : PublicMerkleLog.PublicLog,
      (∀ q ∈ earlier, q ∈ oldLog) ∧ e ∈ PublicMerkleLog.records earlier)
    (saturated : ∀ bytes d, (bytes,d) ∈ PublicMerkleLog.records oldLog → ∃ first, (bytes,first) ∈ retained)
    (snapshot : Snapshot) (table : snapshot.table = recordDomain retained) :
    opening.result.rows = atQueries
      (frozenQueryOracle (PublicMerkleLog.hash C) snapshot opening.root p opening.level.val lanes)
      (queryIndices p opening.level opening.sample) ∨
      PublicMerkleBinding.OpenPrimitiveBad C oldLog opening.root opening.result.paths := by
  obtain ⟨proof,_,accepted,_⟩ := observed.real C iv answers
  exact openQuery_retained C iv oldLog authentic retained history saturated snapshot table
    p opening.level lanes proof opening.root opening.sample opening.result accepted

/-- The resulting primitive witness is the existing causal compression-game
terminal event, with its path coverage and tag-zero limits already proved. -/
theorem observed_frozen_bad {p : ParameterBounds.Profile} {lanes : Nat}
    {proofs : Array PrunedMerklePaths} {observations : List Observation} {opening : QueryOpening p}
    (observed : ObservedOpening lanes proofs observations opening) (C : PrimitiveOracle) (iv : Digest32)
    (answers : ∀ o ∈ observations, o.answer = realAnswer C iv o.query)
    (roots : PublicMerkleProbability.RootPolicy) (trace before after oldLog : PublicMerkleLog.PublicLog)
    (freeze : trace = before ++ after) (prior : ∀ e ∈ oldLog, e ∈ before)
    (ordinary : ∀ n d, (n,d) ∈ before → DuplexFraming.tag n = 0 → (n,d) ∈ oldLog)
    (registered : opening.root ∈ roots before.reverse)
    (executed : ∀ n d, (⟨.primitive .verification n,d⟩ : Observation) ∈ observations → (n,d) ∈ trace)
    (bad : PublicMerkleBinding.OpenPrimitiveBad C oldLog opening.root opening.result.paths) :
    PublicMerkleProbability.FrozenOpeningBad C roots trace := by
  have evaluated := observed_evaluated observed C iv answers
  exact ⟨before,after,oldLog,opening.root,opening.result.paths,freeze,prior,ordinary,registered,
    fun path member bytes input => (evaluated path member bytes input).1,
    fun path member bytes input event present => executed _ _ ((evaluated path member bytes input).2 event present),bad⟩

private def QueryRowsAt (p : ParameterBounds.Profile) (rows : WHIRPhysicalHistory.Rows)
    (replies : Array CausalGame.Reply) : Prop :=
  ∀ i : Fin (ParameterBounds.config p).folds.size,
    CausalProbability.position (.query i) < replies.size →
      CausalGame.rowsField replies[CausalProbability.position (.query i)]! = rows i.val

private theorem coordinate_position_injective {c : Config} :
    Function.Injective (@CausalProbability.position c) := by
  intro a b equal
  apply Option.some.inj
  rw [← WHIRHistory.schedule_get_position a,← WHIRHistory.schedule_get_position b,equal]

private theorem queryRowsAt_push (p : ParameterBounds.Profile) (rows : WHIRPhysicalHistory.Rows)
    (roots : WHIRReplay.Roots) (replies : Array CausalGame.Reply)
    (q : CausalProbability.Coordinate (ParameterBounds.config p)) (pending : WHIRHistory.Pending)
    (response : CausalGame.Reply) (prior : QueryRowsAt p rows replies)
    (position : CausalProbability.position q = replies.size)
    (parsed : WHIRPhysicalHistory.reply roots rows q pending = some response) :
    QueryRowsAt p rows (replies.push response) := by
  intro i covered
  by_cases before : CausalProbability.position (.query i) < replies.size
  · rw [getElem!_pos (replies.push response) _ covered,Array.getElem_push_lt before,
      ← getElem!_pos replies _ before]
    exact prior i before
  · have equal : CausalProbability.position (.query i) = replies.size := by
      simp only [Array.size_push] at covered
      omega
    have phase : q = .query i := coordinate_position_injective (position.trans equal.symm)
    subst q
    rw [WHIRPhysicalHistory.reply_query] at parsed
    obtain ⟨message,_,rfl⟩ := Option.map_eq_some_iff.mp parsed
    rw [equal,getElem!_pos (replies.push (.query (rows i.val) message)) replies.size (by simp),
      Array.getElem_push_eq]
    rfl

/-- Every covered query response position contains the actual physical row
table. The decoder itself supplies both position alignment and reply count. -/
theorem decodeHistory_queryRows (p : ParameterBounds.Profile) (catalog : WHIRReplay.Catalog p)
    (roots : WHIRReplay.Roots) (rows : WHIRPhysicalHistory.Rows) (statement : Digest32)
    (messages : List WHIRHistory.Pending)
    (ancestors : List (WHIRHistory.Pending × Sigma (@CausalProbability.Sample (ParameterBounds.config p))))
    (out : WHIRReplay.Replay p)
    (parsed : WHIRPhysicalHistory.decodeHistory p catalog roots rows statement messages ancestors = some out) :
    out.replies.size = messages.length - 1 ∧ QueryRowsAt p rows out.replies ∧
      ∀ i : Fin (ParameterBounds.config p).folds.size,
        CausalProbability.position (.query i) < out.replies.size →
        ∃ pending sample, (pending,⟨CausalProbability.Coordinate.query i,sample⟩) ∈ ancestors := by
  induction messages generalizing ancestors out with
  | nil => cases parsed
  | cons pending messages ih =>
    cases messages with
    | nil =>
      cases ancestors with
      | cons a rest => cases parsed
      | nil =>
        simp only [WHIRPhysicalHistory.decodeHistory] at parsed
        split at parsed
        · cases found : catalog statement with
          | none => simp [found] at parsed
          | some originalStatement =>
            simp [found] at parsed
            subst out
            refine ⟨rfl,?_,?_⟩ <;> intro i covered <;> simp at covered
        · cases parsed
    | cons previous older =>
      cases ancestors with
      | nil => cases parsed
      | cons entry past =>
        obtain ⟨previous',q,sample⟩ := entry
        simp only [WHIRPhysicalHistory.decodeHistory] at parsed
        split at parsed
        · split at parsed
          · split at parsed
            · rename_i position
              split at parsed
              · split at parsed
                · cases decoded : WHIRPhysicalHistory.decodeHistory p catalog roots rows statement
                      (previous::older) past with
                  | none => simp [decoded] at parsed
                  | some before =>
                    obtain ⟨size,prior,history⟩ := ih past before decoded
                    simp only [List.length_cons,Nat.add_sub_cancel] at size
                    simp only [decoded,WHIRPhysicalHistory.step] at parsed
                    obtain ⟨response,reply,rfl⟩ := Option.map_eq_some_iff.mp parsed
                    constructor
                    · simp only [Array.size_push,List.length_cons]
                      omega
                    · constructor
                      · exact queryRowsAt_push p rows roots before.replies q pending response
                          prior (position.trans size.symm) reply
                      · intro i covered
                        by_cases earlier : CausalProbability.position (.query i) < before.replies.size
                        · obtain ⟨message,value,member⟩ := history i earlier
                          exact ⟨message,value,List.mem_cons_of_mem _ member⟩
                        · have equal : CausalProbability.position (.query i) = before.replies.size := by
                            simp only [Array.size_push] at covered
                            omega
                          have phase : q = .query i :=
                            coordinate_position_injective (position.trans (size.symm.trans equal.symm))
                          cases phase
                          exact ⟨previous',sample,List.mem_cons_self⟩
                · cases parsed
              · cases parsed
            · cases parsed
          · cases parsed
        · cases parsed

private theorem query_position_lt_replies (c : Config) (tape : CausalGame.Tape c)
    (replies : Array CausalGame.Reply) (proof : Opening)
    (accepted : CausalGame.opening c (CausalGame.challenges c tape) replies = .ok proof)
    (i : Fin c.folds.size) : CausalProbability.position (.query i) < replies.size := by
  have checked := (CausalRefinement.opening_ok_iff c _ replies proof).mp accepted |>.1
  have count := CausalRefinement.checkReplies_length _ _ checked
  have stream := congrArg List.length (CausalProbability.visibleCoordinates_map c tape)
  simp only [List.length_map] at stream
  have size : replies.size = (CausalProbability.visibleCoordinates c).length := by
    calc
      replies.size = (CausalGame.visibleBatches c E.zero (CausalGame.challenges c tape)).length := count
      _ = (CausalGame.visibleBatches c tape.1 (CausalGame.challenges c tape)).length := by
        simp only [CausalGame.visibleBatches,List.length_append,List.length_singleton]
      _ = _ := stream.symm
  rw [size]
  apply List.idxOf_lt_length_of_mem
  simp only [CausalProbability.visibleCoordinates,List.mem_append]
  left
  right
  apply List.mem_flatMap.mpr
  exact ⟨i.val,List.mem_range.mpr i.isLt,by simp [CausalProbability.levelCoordinates,i.isLt]⟩

theorem decodeHistory_opening_rows (p : ParameterBounds.Profile) (catalog : WHIRReplay.Catalog p)
    (roots : WHIRReplay.Roots) (rows : WHIRPhysicalHistory.Rows) (statement : Digest32)
    (messages : List WHIRHistory.Pending)
    (ancestors : List (WHIRHistory.Pending × Sigma (@CausalProbability.Sample (ParameterBounds.config p))))
    (out : WHIRReplay.Replay p)
    (parsed : WHIRPhysicalHistory.decodeHistory p catalog roots rows statement messages ancestors = some out)
    (tape : CausalGame.Tape (ParameterBounds.config p)) (proof : Opening)
    (accepted : CausalGame.opening (ParameterBounds.config p)
      (CausalGame.challenges (ParameterBounds.config p) tape) out.replies = .ok proof) :
    ∀ i : Fin (ParameterBounds.config p).folds.size, proof.levels[i.val]!.rows = rows i.val := by
  intro i
  have position := query_position_lt_replies _ tape out.replies proof accepted i
  have field := (decodeHistory_queryRows p catalog roots rows statement messages ancestors out parsed).2.1 i position
  rw [CausalRefinement.opening_eq_decoded _ _ _ _ accepted]
  change (Array.ofFn (fun j : Fin (ParameterBounds.config p).folds.size =>
    CausalGame.decodedLevel _ (CausalGame.challenges _ tape) out.replies j.val))[i.val]!.rows = _
  rw [getElem!_pos _ i.val (by simpa only [Array.size_ofFn] using i.isLt),Array.getElem_ofFn]
  dsimp only [CausalGame.decodedLevel]
  simp only [CausalStateCausality.challenge_folds_size,CausalStateCausality.challenge_oods_size]
  rw [← CausalPositions.position_query i tape]
  exact field

theorem decodeStack_opening_rows (p : ParameterBounds.Profile) (cap : Nat)
    (catalog : StackWHIRReplay.Catalog p cap) (roots : WHIRReplay.Roots)
    (rows : WHIRPhysicalHistory.Rows) (key : StackWHIRReplay.Key p)
    (out : StackWHIRReplay.Replay p cap)
    (parsed : WHIRPhysicalHistory.decodeStack p cap catalog roots rows key = some out)
    (tape : CausalGame.Tape (ParameterBounds.config p)) (proof : Opening)
    (accepted : CausalGame.opening (ParameterBounds.config p)
      (CausalGame.challenges (ParameterBounds.config p) tape) out.whir.replies = .ok proof) :
    ∀ i : Fin (ParameterBounds.config p).folds.size, proof.levels[i.val]!.rows = rows i.val := by
  unfold WHIRPhysicalHistory.decodeStack at parsed
  obtain ⟨original,_,parsed⟩ := Option.bind_eq_some_iff.mp parsed
  obtain ⟨seed,_,parsed⟩ := Option.bind_eq_some_iff.mp parsed
  obtain ⟨whir,decoded,parsed⟩ := Option.bind_eq_some_iff.mp parsed
  cases Option.some.inj parsed
  exact decodeHistory_opening_rows p _ roots rows key.statement key.messages _
    whir decoded tape proof accepted

theorem decodeHistory_opening_nextOracle (p : ParameterBounds.Profile) (catalog : WHIRReplay.Catalog p)
    (roots : WHIRReplay.Roots) (rows : WHIRPhysicalHistory.Rows) (statement : Digest32)
    (messages : List WHIRHistory.Pending)
    (ancestors : List (WHIRHistory.Pending × Sigma (@CausalProbability.Sample (ParameterBounds.config p))))
    (out : WHIRReplay.Replay p)
    (parsed : WHIRPhysicalHistory.decodeHistory p catalog roots rows statement messages ancestors = some out)
    (tape : CausalGame.Tape (ParameterBounds.config p)) (proof : Opening)
    (accepted : CausalGame.opening (ParameterBounds.config p)
      (CausalGame.challenges (ParameterBounds.config p) tape) out.replies = .ok proof)
    (i : Fin (ParameterBounds.config p).folds.size) (hasNext : i.val+1 < (ParameterBounds.config p).folds.size) :
    ∃ digest, (WHIRQueryOracleRecurrence.rootLog p statement messages)[i.val]? = some digest ∧
      proof.levels[i.val]!.nextOracle = some (roots digest (i.val+1)) := by
  have positive := WHIRQueryOracleRecurrence.production_folds_positive p i
  let j : Fin (ParameterBounds.config p).folds[i.val]! :=
    ⟨(ParameterBounds.config p).folds[i.val]! - 1,by omega⟩
  have last : j.val+1 = (ParameterBounds.config p).folds[i.val]! := by dsimp [j]; omega
  have count := (decodeHistory_queryRows p catalog roots rows statement messages ancestors out parsed).1
  have covered := query_position_lt_replies _ tape out.replies proof accepted i
  have available : CausalProbability.position (.fold i j) < messages.length-1 := by
    rw [← count]
    apply Nat.lt_trans _ covered
    rw [CausalPositions.position_fold i j tape,CausalPositions.position_query i tape]
    have bound := j.isLt
    omega
  obtain ⟨digest,logged,slot⟩ := WHIRQueryOracleRecurrence.decoded_rootLog_slot
    p catalog roots rows statement messages ancestors out parsed i j last hasNext
    (fun k hk => WHIRQueryOracleRecurrence.production_folds_positive p ⟨k,by omega⟩) available
  refine ⟨digest,logged,?_⟩
  rw [CausalRefinement.opening_eq_decoded _ _ _ _ accepted]
  change (Array.ofFn (fun k : Fin (ParameterBounds.config p).folds.size =>
    CausalGame.decodedLevel _ (CausalGame.challenges _ tape) out.replies k.val))[i.val]!.nextOracle = _
  rw [getElem!_pos _ i.val (by simpa only [Array.size_ofFn] using i.isLt),Array.getElem_ofFn]
  dsimp only [CausalGame.decodedLevel]
  simp only [CausalStateCausality.challenge_folds_size]
  rw [ite_eq_left ⟨hasNext,positive⟩]
  have index : CausalProbability.position (.fold i j) =
      CausalGame.levelStart (CausalGame.challenges (ParameterBounds.config p) tape) i.val +
        (ParameterBounds.config p).folds[i.val]! - 1 := by
    rw [CausalPositions.position_fold i j tape]
    omega
  rw [← index]
  exact slot

theorem decodeStack_opening_nextOracle (p : ParameterBounds.Profile) (cap : Nat)
    (catalog : StackWHIRReplay.Catalog p cap) (roots : WHIRReplay.Roots)
    (rows : WHIRPhysicalHistory.Rows) (key : StackWHIRReplay.Key p)
    (out : StackWHIRReplay.Replay p cap)
    (parsed : WHIRPhysicalHistory.decodeStack p cap catalog roots rows key = some out)
    (tape : CausalGame.Tape (ParameterBounds.config p)) (proof : Opening)
    (accepted : CausalGame.opening (ParameterBounds.config p)
      (CausalGame.challenges (ParameterBounds.config p) tape) out.whir.replies = .ok proof)
    (i : Fin (ParameterBounds.config p).folds.size) (hasNext : i.val+1 < (ParameterBounds.config p).folds.size) :
    ∃ digest, (WHIRQueryOracleRecurrence.rootLog p key.statement key.messages)[i.val]? = some digest ∧
      proof.levels[i.val]!.nextOracle = some (roots digest (i.val+1)) := by
  unfold WHIRPhysicalHistory.decodeStack at parsed
  obtain ⟨original,_,parsed⟩ := Option.bind_eq_some_iff.mp parsed
  obtain ⟨seed,_,parsed⟩ := Option.bind_eq_some_iff.mp parsed
  obtain ⟨whir,decoded,parsed⟩ := Option.bind_eq_some_iff.mp parsed
  cases Option.some.inj parsed
  exact decodeHistory_opening_nextOracle p _ roots rows key.statement key.messages _
    whir decoded tape proof accepted i hasNext

theorem decodeStack_query_mem (p : ParameterBounds.Profile) (cap : Nat)
    (catalog : StackWHIRReplay.Catalog p cap) (roots : WHIRReplay.Roots)
    (rows : WHIRPhysicalHistory.Rows) (key : StackWHIRReplay.Key p)
    (out : StackWHIRReplay.Replay p cap)
    (parsed : WHIRPhysicalHistory.decodeStack p cap catalog roots rows key = some out)
    (tape : CausalGame.Tape (ParameterBounds.config p)) (proof : Opening)
    (accepted : CausalGame.opening (ParameterBounds.config p)
      (CausalGame.challenges (ParameterBounds.config p) tape) out.whir.replies = .ok proof)
    (i : Fin (ParameterBounds.config p).folds.size) :
    ∃ pending sample, (pending,⟨CausalProbability.Coordinate.query i,sample⟩) ∈ key.ancestors := by
  unfold WHIRPhysicalHistory.decodeStack at parsed
  obtain ⟨original,_,parsed⟩ := Option.bind_eq_some_iff.mp parsed
  obtain ⟨seed,_,parsed⟩ := Option.bind_eq_some_iff.mp parsed
  obtain ⟨whir,decoded,parsed⟩ := Option.bind_eq_some_iff.mp parsed
  cases Option.some.inj parsed
  obtain ⟨pending,sample,member⟩ := (decodeHistory_queryRows p _ roots rows key.statement key.messages _
    whir decoded).2.2 i (query_position_lt_replies _ tape whir.replies proof accepted i)
  exact ⟨pending,sample,WHIRPhysicalRoots.projectEntry_query_mem key.ancestors pending i sample member⟩

theorem decodeStack_rootShapes (p : ParameterBounds.Profile) (cap : Nat)
    (state : CausalBindingState.State cap) (catalog : StackWHIRReplay.Catalog p cap)
    (rows : WHIRPhysicalHistory.Rows) (key : StackWHIRReplay.Key p)
    (out : StackWHIRReplay.Replay p cap)
    (parsed : WHIRPhysicalHistory.decodeStack p cap catalog (CausalBindingState.roots state p) rows key = some out)
    (tape : CausalGame.Tape (ParameterBounds.config p)) (proof : Opening)
    (accepted : CausalGame.opening (ParameterBounds.config p)
      (CausalGame.challenges (ParameterBounds.config p) tape) out.whir.replies = .ok proof) :
    WHIRNativeArithmetic.RootShapes (ParameterBounds.config p) proof := by
  intro i bound hasNext next found
  obtain ⟨digest,_,value⟩ := decodeStack_opening_nextOracle p cap catalog
    (CausalBindingState.roots state p) rows key out parsed tape proof accepted ⟨i,bound⟩ hasNext
  have equal := Option.some.inj (found.symm.trans value)
  subst next
  have shape : oracleValid (CausalBindingState.roots state p digest (i+1))
      (ParameterBounds.length (ParameterBounds.config p) (i+1))
      (2^(ParameterBounds.config p).folds[i+1]!) = true := by
    unfold CausalBindingState.roots
    exact intermediateOracle_valid _ _ _ _ _ _
  have dimensions := ((CausalBoundary.production_boundary_facts p ⟨i,bound⟩).2.2 hasNext).1
  change CausalGame.remaining (ParameterBounds.config p) (i+1) +
    (ParameterBounds.config p).folds[i+1]! = CausalGame.remaining (ParameterBounds.config p) i at dimensions
  have remaining : CausalGame.remaining (ParameterBounds.config p) (i+1) =
      CausalGame.remaining (ParameterBounds.config p) i - (ParameterBounds.config p).folds[i+1]! := by
    omega
  simpa only [ParameterBounds.length,remaining] using shape

theorem trace_opening_oracleBefore {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q cap : Nat}
    (packet : RawWHIRKeys.Packet ctx Q) {packets : List (RawWHIRKeys.Packet ctx Q)}
    {lanes : Nat} {proofs : Array PrunedMerklePaths} {wire : WireState packet.val.profile} {history}
    (root : Digest32) (base : CausalGame.BaseOracle) (roots : WHIRReplay.Roots)
    (chain : Chain ctx Q packet packets)
    (trace : Trace ctx stack Q packet.val.profile lanes proofs packets
      (initialWireState packet.val.profile root) wire history)
    (catalog : StackWHIRReplay.Catalog packet.val.profile cap)
    (past : List (WHIRRawReplay.LocalEntry packet.val.profile))
    (out : StackWHIRReplay.Replay packet.val.profile cap)
    (parsed : WHIRPhysicalHistory.decodeStack packet.val.profile cap catalog roots (fun i => wire.rows[i]!)
      ⟨packet.val.statement,packet.val.messages,past⟩ = some out)
    (proof : Opening)
    (accepted : CausalGame.opening (ParameterBounds.config packet.val.profile)
      (CausalGame.challenges (ParameterBounds.config packet.val.profile) wire.tape) out.whir.replies = .ok proof)
    (i : Fin (ParameterBounds.config packet.val.profile).folds.size) :
    WHIRNativeArithmetic.oracleBefore proof (CausalGame.liftRoot base) i.val =
      if i.val = 0 then CausalGame.liftRoot base else roots wire.roots[i.val]! i.val := by
  by_cases first : i.val = 0
  · simp only [WHIRNativeArithmetic.oracleBefore,first,ite_true]
  · let previous : Fin (ParameterBounds.config packet.val.profile).folds.size := ⟨i.val-1,by omega⟩
    have succ : previous.val+1 = i.val := by dsimp [previous]; omega
    obtain ⟨digest,logged,next⟩ := decodeStack_opening_nextOracle packet.val.profile cap catalog roots
      (fun i => wire.rows[i]!) ⟨packet.val.statement,packet.val.messages,past⟩ out parsed
      wire.tape proof accepted previous (by omega)
    have recorded := WHIRPhysicalRoots.trace_digest_from_prefix root chain trace 0 previous.val digest
      (by simpa using logged)
    rw [succ] at recorded next
    obtain ⟨rootBound,rootValue⟩ := Array.getElem?_eq_some_iff.mp recorded
    simp only [WHIRNativeArithmetic.oracleBefore,ite_eq_right first]
    rw [show i.val-1 = previous.val from rfl,next,Option.getD_some,
      getElem!_pos wire.roots i.val rootBound,rootValue]

private theorem atQueries_get (oracle : Oracle) (queries : Array Nat) (i : Nat) (bound : i < queries.size) :
    (atQueries oracle queries.toList)[i]! = oracle[queries[i]!]! := by
  have mapped : atQueries oracle queries.toList = queries.map (fun j => oracle[j]!) := by
    simp [atQueries,← Array.toList_map]
  rw [mapped,getElem!_pos _ i (by simpa only [Array.size_map] using bound),
    Array.getElem_map,getElem!_pos queries i bound]

/-- Native authentication is supplied by the actual retained openings and
their actual tape coordinates. No authentication certificate is assumed. -/
theorem trace_authenticatedRows {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q cap : Nat}
    (packet : RawWHIRKeys.Packet ctx Q) {packets : List (RawWHIRKeys.Packet ctx Q)}
    {lanes : Nat} {proofs : Array PrunedMerklePaths} {wire : WireState packet.val.profile} {history}
    (root : Digest32) (base : CausalGame.BaseOracle) (roots : WHIRReplay.Roots)
    (chain : Chain ctx Q packet packets)
    (trace : Trace ctx stack Q packet.val.profile lanes proofs packets
      (initialWireState packet.val.profile root) wire history)
    (bound : WHIRPhysicalRoots.BoundRows base roots wire)
    (catalog : StackWHIRReplay.Catalog packet.val.profile cap)
    (out : StackWHIRReplay.Replay packet.val.profile cap)
    (parsed : WHIRPhysicalHistory.decodeStack packet.val.profile cap catalog roots (fun i => wire.rows[i]!)
      ⟨packet.val.statement,packet.val.messages,(localHistory ctx stack Q packet.val.profile history).tail⟩ = some out)
    (proof : Opening)
    (accepted : CausalGame.opening (ParameterBounds.config packet.val.profile)
      (CausalGame.challenges (ParameterBounds.config packet.val.profile) wire.tape) out.whir.replies = .ok proof) :
    WHIRNativeArithmetic.AuthenticatedRows (ParameterBounds.config packet.val.profile)
      (CausalGame.challenges (ParameterBounds.config packet.val.profile) wire.tape) proof (CausalGame.liftRoot base) := by
  intro i index qs queried j jBound
  let level : Fin (ParameterBounds.config packet.val.profile).folds.size := ⟨i,index⟩
  obtain ⟨pending,sample,member⟩ := decodeStack_query_mem packet.val.profile cap catalog roots
    (fun i => wire.rows[i]!) _ out parsed wire.tape proof accepted level
  have present := List.mem_of_mem_tail member
  have sampleAt := WHIRPhysicalRoots.trace_query_sample root chain trace pending level sample present
  have actualRows := WHIRPhysicalRoots.trace_query_rows root base roots trace bound pending level sample present
  have actualSample := (CausalStateCausality.challenge_query (ParameterBounds.config packet.val.profile)
    wire.tape level).1
  rw [sampleAt] at actualSample
  rw [actualSample] at queried
  have depths := CausalBoundary.production_boundary_facts packet.val.profile level
  have actualQueries := QueryBatchSoundness.queries_actual _ _ sample.1 depths.1 depths.2.1
  have equal := Option.some.inj (queried.symm.trans actualQueries)
  subst qs
  have rows := decodeStack_opening_rows packet.val.profile cap catalog roots (fun i => wire.rows[i]!)
    _ out parsed wire.tape proof accepted level
  have incoming := trace_opening_oracleBefore packet root base roots chain trace catalog _ out parsed proof accepted level
  rw [rows,actualRows,incoming]
  exact atQueries_get _ _ j jBound

private theorem run_indexed_replies (input : CausalGame.Public) (tape : CausalGame.Tape input.config)
    (replies : Array CausalGame.Reply) (proof : Opening)
    (parsed : CausalGame.opening input.config (CausalGame.challenges input.config tape) replies = .ok proof) :
    CausalGame.run (CausalStrategy.indexedStrategy replies) input []
      (CausalGame.visibleBatches input.config tape.1 (CausalGame.challenges input.config tape)) = replies.toList := by
  have count := CausalRefinement.checkReplies_length _ _
    ((CausalRefinement.opening_ok_iff _ _ _ _).mp parsed).1
  have length : replies.toList.length =
      (CausalGame.visibleBatches input.config tape.1 (CausalGame.challenges input.config tape)).length := by
    simpa only [CausalGame.visibleBatches,List.length_append,List.length_singleton] using count
  apply List.ext_getElem! (by rw [CausalStrategy.run_length,length])
  intro i
  by_cases covered : i < replies.toList.length
  · rw [CausalStrategy.indexed_response replies input [] _ i (by omega)]
    simp only [List.length_nil,Nat.zero_add]
    rw [getElem!_pos replies i covered,getElem!_pos replies.toList i covered]
    rfl
  · have gone : ¬i < (CausalGame.run (CausalStrategy.indexedStrategy replies) input []
        (CausalGame.visibleBatches input.config tape.1 (CausalGame.challenges input.config tape))).length := by
      rw [CausalStrategy.run_length,← length]
      exact covered
    rw [getElem!_neg (CausalGame.run (CausalStrategy.indexedStrategy replies) input []
      (CausalGame.visibleBatches input.config tape.1 (CausalGame.challenges input.config tape))) i gone,
      getElem!_neg replies.toList i covered]

theorem experiment_indexed_accepts (input : CausalGame.Public) (tape : CausalGame.Tape input.config)
    (replies : Array CausalGame.Reply) (proof : Opening)
    (parsed : CausalGame.opening input.config (CausalGame.challenges input.config tape) replies = .ok proof)
    (shapes : input.claims.all (fun claim => shapeValid input.config input.lanes claim.weight) = true)
    (verified : let claim := CausalGame.batchClaims (2^input.config.logN) input.claims tape.1
      Protocol.verify input.config (CausalGame.challenges input.config tape) input.lanes
        (CausalGame.liftRoot input.root) claim.weight claim.value proof = .ok ()) :
    CausalGame.experiment input (CausalStrategy.indexedStrategy replies) tape = true := by
  unfold CausalGame.experiment
  dsimp only
  rw [shapes,run_indexed_replies input tape replies proof parsed]
  simp only [Bool.not_true,Bool.false_eq_true,ite_false,Array.toArray_toList,parsed,
    verified,Except.isOk]
  rfl

theorem capture_base_shape {cap : Nat} (state : CausalBindingState.State cap)
    (p : ParameterBounds.Profile) (root : Digest32) (lanes : Nat)
    (bound : lanes ≤ 2^(ParameterBounds.config p).folds[0]!) :
    oracleValid (CausalGame.liftRoot (CausalBindingState.capture state p root lanes bound).base)
      (2^((ParameterBounds.config p).logN-(ParameterBounds.config p).folds[0]!+
        (ParameterBounds.config p).rates[0]!)) lanes = true := by
  have shape := compactBaseOracle_valid
    (recordedHash (CausalBindingState.capture state p root lanes bound).records (fun _ => 0))
    (CausalBindingState.capture state p root lanes bound).snapshot root
    (CausalGame.remaining (ParameterBounds.config p) 0+(ParameterBounds.config p).rates[0]!)
    (ParameterBounds.length (ParameterBounds.config p) 0)
    (2^(ParameterBounds.config p).folds[0]!) lanes bound
  simpa only [CausalBindingState.Commitment.base,CausalBindingState.capture,ParameterBounds.length,
    (InitialCandidates.production_initial_facts p).1] using shape

theorem accepted_completed_depth {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q cap : Nat}
    {packet : RawWHIRKeys.Packet ctx Q} (v : Verified ctx Q cap packet)
    (complete : Completed stack packet v.wire v.history) :
    packet.val.messages.length = WHIRHistory.depth (ParameterBounds.config packet.val.profile) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,size,_,_⟩ := complete
  obtain ⟨_,proof,_,parsed,_⟩ := v.acceptance
  have count := CausalRefinement.checkReplies_length _ _
    ((CausalRefinement.opening_ok_iff _ _ _ _).mp parsed).1
  have stream := congrArg List.length
    (CausalProbability.visibleCoordinates_map (ParameterBounds.config packet.val.profile) v.wire.tape)
  simp only [List.length_map] at stream
  have length : v.wire.replies.size =
      (CausalProbability.visibleCoordinates (ParameterBounds.config packet.val.profile)).length := by
    calc
      v.wire.replies.size = (CausalGame.visibleBatches (ParameterBounds.config packet.val.profile)
        E.zero (CausalGame.challenges (ParameterBounds.config packet.val.profile) v.wire.tape)).length := count
      _ = (CausalGame.visibleBatches (ParameterBounds.config packet.val.profile)
        v.wire.tape.1 (CausalGame.challenges (ParameterBounds.config packet.val.profile) v.wire.tape)).length := by
        simp only [CausalGame.visibleBatches,List.length_append,List.length_singleton]
      _ = _ := stream.symm
  have max := RawWHIRKeys.packet_depth ctx Q packet
  have hidden : (WHIRHistory.hiddenTail (ParameterBounds.config packet.val.profile)).length ≤ 1 := by
    unfold WHIRHistory.hiddenTail
    split <;> simp
  simp only [WHIRHistory.depth,WHIRHistory.schedule,List.length_append] at max ⊢
  omega

private theorem runs_done_eq {R : Type} {left right : R} {trace : List Observation}
    (run : Runs (.done left) trace right) : left = right := by
  cases run
  rfl

/-- Both canonical causal replay and every retained actual Merkle subrun are
derived from acceptance of the real physical source, not provided as interfaces. -/
theorem verifySource_execution (cap : Nat) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q lanes : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (proofs : Array PrunedMerklePaths)
    (observations : List Observation) (v : Verified ctx Q cap packet)
    (run : Runs (WHIRSourceChronology.erase (verifySource cap model ctx stack Q lanes packet proofs))
      observations (some v)) :
    Trace ctx stack Q packet.val.profile v.request.lanes proofs
      (RawOracleCoupling.Concrete.completion ctx Q packet)
      (initialWireState packet.val.profile v.request.root) v.wire v.history ∧
      ∀ opening ∈ v.wire.openings, ObservedOpening v.request.lanes proofs observations opening := by
  obtain ⟨root,before,after,request,_,rootEq,traceEq,_,_,decoded,physical⟩ :=
    WHIRPhysicalCaller.verifySource_success cap model ctx stack Q lanes packet proofs observations v run
  obtain ⟨final,history,suffix,trace,last⟩ := readPhysicalPackets_trace ctx stack Q packet.val.profile
    request.lanes proofs _ _ _ _ after v physical
  obtain ⟨requestEq,wireEq,historyEq⟩ :=
    WHIRPhysicalCaller.finish_success ctx Q cap packet request final history _ _ v (runs_done_eq last)
  constructor
  · simpa only [← requestEq,rootEq,← wireEq,← historyEq] using trace
  · obtain ⟨state,log,remaining,last,_,opened⟩ :=
      readPhysicalCompletion_openings ctx stack Q packet request.lanes proofs root _ after v physical
    obtain ⟨_,wireEq',_⟩ :=
      WHIRPhysicalCaller.finish_success ctx Q cap packet request state log _ _ v (runs_done_eq last)
    intro opening member
    rw [wireEq'] at member
    have retained := opened opening member
    rw [requestEq]
    apply retained.mono
    intro event present
    rw [traceEq]
    exact List.mem_append_right _ present

/-- The actual caller's original claims, bound to the first captured physical
commitment. Re-reading the final state cannot replace that frozen capture. -/
noncomputable def committedStatement {ctx : RawWHIRKeys.Context} {Q cap : Nat}
    {packet : RawWHIRKeys.Packet ctx Q} (v : Verified ctx Q cap packet)
    (state : CausalBindingState.State cap) : WHIRFiatShamir.StackInitial packet.val.profile cap :=
  CausalBindingState.bindClaims
    (CausalBindingState.capture state packet.val.profile v.request.root v.request.lanes v.request.lane_bound)
    v.request.claims

private theorem opening_unerase (c : Config) (challenges : Challenges)
    (replies : Array CausalGame.Reply) (erased : Opening)
    (accepted : CausalGame.opening c challenges (replies.map WHIRPhysicalErasure.eraseReply) = .ok erased) :
    ∃ proof, CausalGame.opening c challenges replies = .ok proof ∧
      WHIRPhysicalErasure.eraseOracles proof = erased := by
  rw [WHIRPhysicalErasure.opening_erase] at accepted
  cases parsed : CausalGame.opening c challenges replies with
  | error message => simp [parsed,Except.map] at accepted
  | ok proof =>
    simp [parsed,Except.map] at accepted
    exact ⟨proof,rfl,accepted⟩

private theorem sourceVerify_erased {m : Nat} (family : Fin m → RingPCSGame.FamilyClaim)
    (points : Array RingPCSGame.PointClaim) (seed : RingPCSGame.Prefix) (lambda : E)
    (c : Config) (challenges : Challenges) (lanes : Nat) (proof : Opening) :
    WHIRNativeArithmetic.sourceVerify family points seed lambda c challenges lanes
        (WHIRPhysicalErasure.eraseOracles proof) =
      WHIRNativeArithmetic.sourceVerify family points seed lambda c challenges lanes proof :=
  WHIRNativeErasure.nativeVerify_erased c challenges lanes
    (WHIRNativeArithmetic.initialClaim family points seed lambda)
    (SuccinctRingGroups.sourceStackWeightAt family points seed lambda) proof

/-- Actual native acceptance plus physical opening binding implies the exact
stack-history failure. All scalar parsing, source caller shapes, ghost-root
restoration, query authentication, sample identity, and native-to-protocol
refinement are discharged here. -/
theorem trace_native_historyFailure {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q cap : Nat}
    (packet : RawWHIRKeys.Packet ctx Q) (proofs : Array PrunedMerklePaths)
    (v : Verified ctx Q cap packet) (state : CausalBindingState.State cap)
    (catalog : StackWHIRReplay.Catalog packet.val.profile cap)
    (found : catalog packet.val.statement = some (committedStatement v state))
    (trace : Trace ctx stack Q packet.val.profile v.request.lanes proofs
      (RawOracleCoupling.Concrete.completion ctx Q packet)
      (initialWireState packet.val.profile v.request.root) v.wire v.history)
    (bound : WHIRPhysicalRoots.BoundRows (committedStatement v state).root
      (CausalBindingState.roots state packet.val.profile) v.wire)
    (falseClaims : ¬ ∃ witness ∈ InitialCandidates.witnesses (ParameterBounds.config packet.val.profile)
      (committedStatement v state).lanes (committedStatement v state).root,
      RingPCSGame.Honest (ParameterBounds.config packet.val.profile) (committedStatement v state).lanes
        (committedStatement v state).family (committedStatement v state).points witness) :
    StackWHIRROM.HistoryFailure packet.val.profile cap catalog (CausalBindingState.roots state packet.val.profile)
      packet.val.statement packet.val.messages (localHistory ctx stack Q packet.val.profile v.history) := by
  let original := committedStatement v state
  let roots := CausalBindingState.roots state packet.val.profile
  have chain := completion_chain ctx Q packet
  have complete := trace_completed v.request.root chain trace
  have depth := accepted_completed_depth v complete
  obtain ⟨head,past,sample,erased,history,decoded,originalEq,initial,statement,tape,replies⟩ :=
    Completed.decodeStack packet v.wire v.history catalog original found complete v.replies_nonempty
  have tail : (localHistory ctx stack Q packet.val.profile v.history).tail = past := by rw [history]; rfl
  have full := decoded
  change WHIRPhysicalHistory.decodeStack packet.val.profile cap catalog WHIRPhysicalErasure.zeroRoots
    (fun i => v.wire.rows[i]!) ⟨packet.val.statement,packet.val.messages,past⟩ = some erased at full
  rw [WHIRPhysicalErasure.decodeStack_zero packet.val.profile cap catalog roots
    (fun i => v.wire.rows[i]!) ⟨packet.val.statement,packet.val.messages,past⟩] at full
  obtain ⟨replay,physical,erasedEq⟩ := Option.map_eq_some_iff.mp full
  subst erased
  change replay.original = original at originalEq
  change v.wire.initial = some replay.initial at initial
  change replay.whir.statement = StackWHIRReplay.transformedStatement original replay.initial.1 at statement
  change (StackWHIRReplay.finish ⟨packet.val.statement,packet.val.messages,past⟩ replay sample).whir.tape =
    v.wire.tape at tape
  change replay.whir.replies.map WHIRPhysicalErasure.eraseReply = v.wire.replies at replies
  have agreement := WHIRPhysicalRoots.trace_stackRowsAgree packet v.request.root catalog original roots
    found chain trace bound
  rw [tail] at agreement
  have ideal := WHIRPhysicalHistory.decodeStack_success packet.val.profile cap catalog roots
    (fun i => v.wire.rows[i]!) ⟨packet.val.statement,packet.val.messages,past⟩ replay agreement physical
  have lambda := StackWHIRReplay.decode_initial_lambda catalog roots
    ⟨packet.val.statement,packet.val.messages,past⟩ replay ideal sample
  rw [tape] at lambda
  change v.wire.tape.1 = replay.initial.2 at lambda
  obtain ⟨seed,nativeProof,seedFound,parsed,native,shapes⟩ := v.acceptance
  have sameSeed : seed = replay.initial := Option.some.inj (seedFound.symm.trans initial)
  subst seed
  rw [← replies] at parsed
  obtain ⟨proof,parsedFull,erasedProof⟩ := opening_unerase _ _ replay.whir.replies nativeProof parsed
  have nativeFull : WHIRNativeArithmetic.sourceVerify v.request.claims.family v.request.claims.points
      replay.initial.1 replay.initial.2 (ParameterBounds.config packet.val.profile)
      (CausalGame.challenges (ParameterBounds.config packet.val.profile) v.wire.tape)
      v.request.lanes proof = .ok () := by
    rw [← sourceVerify_erased,erasedProof]
    exact native
  have rootsShape := decodeStack_rootShapes packet.val.profile cap state catalog
    (fun i => v.wire.rows[i]!) ⟨packet.val.statement,packet.val.messages,past⟩ replay physical
    v.wire.tape proof parsedFull
  have authenticated := trace_authenticatedRows packet v.request.root original.root roots chain trace bound
    catalog replay (by rw [tail]; exact physical) proof parsedFull
  have verified := WHIRNativeArithmetic.sourceVerify_refines v.request.claims.family v.request.claims.points
    replay.initial.1 replay.initial.2 (ParameterBounds.config packet.val.profile) _
    v.request.lanes proof (CausalGame.liftRoot original.root) v.nativeShapes.1
    (fun i => v.nativeShapes.2 _ (by simp)) shapes.2
    (capture_base_shape state packet.val.profile v.request.root v.request.lanes v.request.lane_bound)
    rootsShape authenticated nativeFull
  refine ⟨head,past,sample,replay,history,depth,ideal,?_,?_⟩
  · change CausalGame.experiment replay.whir.statement.input
      (CausalStrategy.indexedStrategy replay.whir.replies)
      (StackWHIRReplay.finish ⟨packet.val.statement,packet.val.messages,past⟩ replay sample).whir.tape = true
    rw [tape,statement]
    apply experiment_indexed_accepts (StackWHIRReplay.transformedStatement original replay.initial.1).input
      v.wire.tape replay.whir.replies proof parsedFull
    · exact shapes.1
    · change Protocol.verify (ParameterBounds.config packet.val.profile)
        (CausalGame.challenges (ParameterBounds.config packet.val.profile) v.wire.tape) v.request.lanes
        (CausalGame.liftRoot original.root)
        (CausalGame.batchClaims (2^(ParameterBounds.config packet.val.profile).logN)
          (RingPCSGame.transformedClaims (2^(ParameterBounds.config packet.val.profile).logN)
            v.request.claims.family v.request.claims.points replay.initial.1) v.wire.tape.1).weight
        (CausalGame.batchClaims (2^(ParameterBounds.config packet.val.profile).logN)
          (RingPCSGame.transformedClaims (2^(ParameterBounds.config packet.val.profile).logN)
            v.request.claims.family v.request.claims.points replay.initial.1) v.wire.tape.1).value proof = .ok ()
      rw [lambda]
      exact verified
  · change ¬ ∃ witness ∈ InitialCandidates.witnesses (ParameterBounds.config packet.val.profile)
      replay.original.lanes replay.original.root,
      RingPCSGame.Honest (ParameterBounds.config packet.val.profile) replay.original.lanes
        replay.original.family replay.original.points witness
    rw [originalEq]
    exact falseClaims

theorem verifySource_native_historyFailure (cap : Nat) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q lanes : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (proofs : Array PrunedMerklePaths)
    (observations : List Observation) (v : Verified ctx Q cap packet)
    (run : Runs (WHIRSourceChronology.erase (verifySource cap model ctx stack Q lanes packet proofs))
      observations (some v))
    (state : CausalBindingState.State cap) (catalog : StackWHIRReplay.Catalog packet.val.profile cap)
    (found : catalog packet.val.statement = some (committedStatement v state))
    (bound : WHIRPhysicalRoots.BoundRows (committedStatement v state).root
      (CausalBindingState.roots state packet.val.profile) v.wire)
    (falseClaims : ¬ ∃ witness ∈ InitialCandidates.witnesses (ParameterBounds.config packet.val.profile)
      (committedStatement v state).lanes (committedStatement v state).root,
      RingPCSGame.Honest (ParameterBounds.config packet.val.profile) (committedStatement v state).lanes
        (committedStatement v state).family (committedStatement v state).points witness) :
    StackWHIRROM.HistoryFailure packet.val.profile cap catalog (CausalBindingState.roots state packet.val.profile)
      packet.val.statement packet.val.messages (localHistory ctx stack Q packet.val.profile v.history) :=
  trace_native_historyFailure packet proofs v state catalog found
    (verifySource_execution cap model ctx stack Q lanes packet proofs observations v run).1 bound falseClaims

private theorem replyFootprint_roots {c : Config} (q : CausalProbability.Coordinate c) (scalars : List E) :
    (WHIRSnapshotReplay.replyFootprint q scalars).map Prod.fst = (absorbedRoot q scalars).toList := by
  cases q with
  | initial => rfl
  | ood => rfl
  | query => rfl
  | tail => rfl
  | fold i j =>
    by_cases last : j.val+1 = c.folds[i.val]! <;> by_cases next : i.val+1 < c.folds.size
    all_goals
      rcases scalars with (_ | ⟨a,(_ | ⟨b,(_ | ⟨r,(_ | ⟨s,(_ | ⟨extra,rest⟩)⟩)⟩)⟩)⟩)
      all_goals simp_all [WHIRSnapshotReplay.replyFootprint,absorbedRoot,Function.comp_def]
      all_goals split_ifs <;> simp_all [Function.comp_def]

theorem rootLog_footprint (p : ParameterBounds.Profile) (statement : Digest32)
    (messages : List WHIRHistory.Pending) :
    WHIRQueryOracleRecurrence.rootLog p statement messages =
      (WHIRSnapshotReplay.historyFootprint p statement messages).map Prod.fst := by
  induction messages with
  | nil => rfl
  | cons pending messages ih =>
    cases messages with
    | nil => rfl
    | cons previous older =>
      rw [WHIRQueryOracleRecurrence.rootLog_cons,WHIRSnapshotReplay.historyFootprint,
        List.map_append,replyFootprint_roots,ih]

theorem trace_opening_origin {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    (packet : RawWHIRKeys.Packet ctx Q) {packets : List (RawWHIRKeys.Packet ctx Q)}
    {lanes : Nat} {proofs : Array PrunedMerklePaths} {wire : WireState packet.val.profile} {history}
    (root : Digest32) (chain : Chain ctx Q packet packets)
    (trace : Trace ctx stack Q packet.val.profile lanes proofs packets
      (initialWireState packet.val.profile root) wire history)
    (opening : QueryOpening packet.val.profile) (member : opening ∈ wire.openings) :
    opening.root = root ∨ ∃ ref ∈ WHIRSnapshotReplay.historyFootprint packet.val.profile
      packet.val.statement packet.val.messages, ref.1 = opening.root := by
  have registered := (WHIRPhysicalRoots.trace_rooted root trace opening member).1
  have present := Array.mem_of_getElem? registered
  rw [WHIRPhysicalRoots.trace_roots_log root chain trace] at present
  have alternatives : opening.root = root ∨ opening.root ∈
      WHIRQueryOracleRecurrence.rootLog packet.val.profile packet.val.statement packet.val.messages := by
    simpa using present
  rcases alternatives with first | later
  · exact Or.inl first
  · right
    rw [rootLog_footprint] at later
    exact List.mem_map.mp later

theorem trace_opening_registered {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q cap : Nat}
    (packet : RawWHIRKeys.Packet ctx Q) {packets : List (RawWHIRKeys.Packet ctx Q)}
    {lanes : Nat} {proofs : Array PrunedMerklePaths} {wire : WireState packet.val.profile} {history}
    (root : Digest32) (chain : Chain ctx Q packet packets)
    (trace : Trace ctx stack Q packet.val.profile lanes proofs packets
      (initialWireState packet.val.profile root) wire history)
    (state : CausalBindingState.State cap)
    (initial : ∃ snap, lookup root state.registry = some snap)
    (prepared : CausalBindingState.Prepared state packet.val.profile
      ⟨packet.val.statement,packet.val.messages,[]⟩)
    (opening : QueryOpening packet.val.profile) (member : opening ∈ wire.openings) :
    ∃ snap, lookup opening.root state.registry = some snap := by
  rcases trace_opening_origin packet root chain trace opening member with first | ⟨ref,present,equal⟩
  · simpa only [first] using initial
  · obtain ⟨snap,known⟩ := prepared ref present
    exact ⟨snap,equal ▸ known⟩

theorem trace_base_opening_root {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    (packet : RawWHIRKeys.Packet ctx Q) {packets : List (RawWHIRKeys.Packet ctx Q)}
    {lanes : Nat} {proofs : Array PrunedMerklePaths} {wire : WireState packet.val.profile} {history}
    (root : Digest32) (chain : Chain ctx Q packet packets)
    (trace : Trace ctx stack Q packet.val.profile lanes proofs packets
      (initialWireState packet.val.profile root) wire history)
    (opening : QueryOpening packet.val.profile) (member : opening ∈ wire.openings)
    (base : opening.level.val = 0) : opening.root = root := by
  have found := (WHIRPhysicalRoots.trace_rooted root trace opening member).1
  rw [base,WHIRPhysicalRoots.trace_roots_log root chain trace] at found
  have equal : root = opening.root := by simpa using found
  exact equal.symm

theorem frozenQueryOracle_state {cap : Nat} (C : PrimitiveOracle) (state : CausalBindingState.State cap)
    (invariant : WHIRPhysicalSnapshots.Invariant C state) (p : ParameterBounds.Profile)
    (root : Digest32) (snapshot : Snapshot) (known : lookup root state.registry = some snapshot)
    (level lanes : Nat) (bound : lanes ≤ 2^(ParameterBounds.config p).folds[0]!) :
    frozenQueryOracle (PublicMerkleLog.hash C) snapshot root p level lanes =
      if level = 0 then
        CausalGame.liftRoot (CausalBindingState.capture state p root lanes bound).base
      else CausalBindingState.roots state p root level := by
  by_cases base : level = 0
  · subst level
    rw [ite_eq_left rfl,CausalBindingState.capture_base_actual (PublicMerkleLog.hash C) state p root lanes bound
      invariant.covered invariant.authentic]
    simp only [frozenQueryOracle,leafWords,ite_true,CausalBindingState.capture,known,Option.getD_some,
      ParameterBounds.length,Nat.log2_two_pow]
  · rw [ite_eq_right base,CausalBindingState.roots_actual (PublicMerkleLog.hash C) state p root level
      snapshot known invariant.covered invariant.authentic]
    simp only [frozenQueryOracle,ite_eq_right base,ParameterBounds.length,Nat.log2_two_pow]

/-- A failure of the fixed actual row tables has a witnessed compression-game
failure at one of the real retained openings and its exact first-frozen log. -/
theorem trace_boundRows_or_bad {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q cap : Nat}
    (C : PrimitiveOracle) (iv : Digest32) (packet : RawWHIRKeys.Packet ctx Q)
    (proofs : Array PrunedMerklePaths) (v : Verified ctx Q cap packet)
    (observations : List Observation) (answers : ∀ o ∈ observations, o.answer = realAnswer C iv o.query)
    (observed : ∀ opening ∈ v.wire.openings, ObservedOpening v.request.lanes proofs observations opening)
    (trace : Trace ctx stack Q packet.val.profile v.request.lanes proofs
      (RawOracleCoupling.Concrete.completion ctx Q packet)
      (initialWireState packet.val.profile v.request.root) v.wire v.history)
    (state : CausalBindingState.State cap) (invariant : WHIRPhysicalSnapshots.Invariant C state)
    (initial : ∃ snap, lookup v.request.root state.registry = some snap)
    (prepared : CausalBindingState.Prepared state packet.val.profile
      ⟨packet.val.statement,packet.val.messages,[]⟩) :
    WHIRPhysicalRoots.BoundRows (committedStatement v state).root
      (CausalBindingState.roots state packet.val.profile) v.wire ∨
      ∃ opening ∈ v.wire.openings, ∃ oldLog,
        state.frozenLog opening.root = some oldLog ∧
        PublicMerkleBinding.OpenPrimitiveBad C oldLog opening.root opening.result.paths := by
  classical
  by_cases good : WHIRPhysicalRoots.BoundRows (committedStatement v state).root
      (CausalBindingState.roots state packet.val.profile) v.wire
  · exact Or.inl good
  · right
    unfold WHIRPhysicalRoots.BoundRows at good
    push Not at good
    obtain ⟨opening,member,different⟩ := good
    have chain := completion_chain ctx Q packet
    obtain ⟨snapshot,known⟩ := trace_opening_registered packet v.request.root chain trace state
      initial prepared opening member
    obtain ⟨retained,oldLog,_,frozen,authentic,history,saturated,table⟩ :=
      invariant.retained opening.root snapshot known
    rcases observed_binding (observed opening member) C iv answers oldLog authentic
      retained history saturated snapshot table with bound | bad
    · exfalso
      apply different
      rw [frozenQueryOracle_state C state invariant packet.val.profile opening.root snapshot known
        opening.level.val v.request.lanes v.request.lane_bound] at bound
      by_cases base : opening.level.val = 0
      · have rootEq := trace_base_opening_root packet v.request.root chain trace opening member base
        simpa only [base,ite_true,rootEq,committedStatement,CausalBindingState.bindClaims] using bound
      · simpa only [ite_eq_right base] using bound
    · exact ⟨opening,member,oldLog,frozen,bad⟩

end Whir.WHIRPhysicalSoundness
