import Whir.DuplexPublicSimulator
import Whir.WHIRModeFinal

/-! Deterministic realization of the chosen public simulator. Both the fallback
seed and the raw table below depend on the same compression oracle. This is a
semantic bridge, not an independent-seed probabilistic coupling. The evaluator
covers arbitrary complete extracted names, including chosen seed CVs and names
outside the admissible WHIR coordinate submode. `real_ideal_view` exposes only
the existing public view; `answer_real` also supplies the private log invariant
needed for induction. Neither theorem excludes compression collisions: the
chosen predecessor's actual `Complete`/`Tree`/`extract` witness suffices. -/
namespace Whir.WHIRRealSimulator
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame DuplexPublicSimulator

/-- Evaluate the terminal-first extracted representation from its leaf upward.
Malformed or mismatched tails have a fixed zero value; no parser acceptance is
changed, and the simulator still uses its existing recognition checks. -/
def evalRaw (C : PrimitiveOracle) :
    List (Option Digest32 × Block64) → List (UInt64 × Bool) → Digest32
  | (leaf, block) :: message, (tweak, last) :: template =>
      C ⟨leaf.getD (evalRaw C message template), block, tweak, last⟩
  | _, _ => fun _ => 0

/-- The canonical deterministic raw table, not a sampled random oracle. -/
def rawTable (Q : Nat) (C : PrimitiveOracle) (key : RawKey Q) : Digest32 :=
  evalRaw C (expandKey key).message (expandKey key).template

theorem evalRaw_tree (C : PrimitiveOracle) {cv : Digest32} {ns : List Node}
    (tree : Tree (compressionOf C) cv ns) :
    evalRaw C (ns.map payload) (ns.map (fun n => (n.tweak,n.last))) = cv := by
  induction tree with
  | seed n hs => simp [evalRaw, payload, hs, nodeValue, compressionOf]
  | step n ns hi child ih =>
    have hn : ¬isSeed n := fun hs => seed_not_internal hs hi
    simp [evalRaw, payload, hn, ih, nodeValue, compressionOf]

theorem evalRaw_complete (C : PrimitiveOracle) {input : Node} {rest : List Node}
    {key : Extracted} (complete : Complete (input :: rest))
    (tree : Tree (compressionOf C) input.cv rest)
    (extracted : extract (input :: rest) = some key) :
    evalRaw C key.message key.template = C input := by
  have hc := (complete?_correct _).mpr complete
  obtain ⟨t, ns, he, ht, _⟩ := complete
  cases he
  have hn : ¬isSeed input := terminal_not_seed ht
  have hk : key = ⟨(input :: rest).map payload,
      (input :: rest).map (fun n => (n.tweak,n.last))⟩ := by
    simpa [extract, hc] using extracted.symm
  rw [hk]
  simp [evalRaw, payload, hn, evalRaw_tree C tree]

theorem rawTable_privateKey {Q : Nat} (C : PrimitiveOracle) {log : PublicLog}
    {input : Node} {key : RawKey Q}
    (consistent : ∀ n d, (n,d) ∈ log → C n = d)
    (recognized : privateKey Q log input = some key) :
    rawTable Q C key = C input := by
  obtain ⟨rest, complete, tree, extracted⟩ :=
    privateKey_compression recognized C consistent
  exact evalRaw_complete C complete tree extracted

theorem rawTable_construction (Q : Nat) (C : PrimitiveOracle) (iv : Digest32)
    (q : Coordinate) (valid : DuplexEncoding.Admissible q) (cap : pathCost q ≤ Q) :
    rawTable Q C (constructionKey Q iv q cap) =
      evalCoordinate (compressionOf C) iv q := by
  have he := coordinateTree_key (compressionOf C) iv q valid
  have hc := coordinateTree_complete (compressionOf C) iv q valid.1
  have ht := (traceHistory_valid (compressionOf C) iv q.history valid.1).1
  have hcv : (terminalNode (traceHistory (compressionOf C) iv q.history).state.cv
      q.terminal).cv = (traceHistory (compressionOf C) iv q.history).state.cv := by
    cases q.terminal <;> rfl
  have hv := evalRaw_complete C hc (hcv.symm ▸ ht) he
  simpa [rawTable, coordinateTree, nodeValue, compressionOf,
    coordinateTree_evaluates, expand_constructionKey] using
    hv.trans (coordinateTree_evaluates (compressionOf C) iv q)

/-- Log consistency is maintained even when distinct compression inputs collide.
Recognition may choose either predecessor; its actual extracted tree still
canonically evaluates to the observed terminal input's compression value. -/
def Consistent (C : PrimitiveOracle) (state : DuplexPublicSimulator.State) : Prop :=
  state.seed = C ∧ ∀ n d, (n,d) ∈ state.publicLog → C n = d

theorem answer_real (Q : Nat) (C : PrimitiveOracle)
    (state : DuplexPublicSimulator.State) (input : Node) (h : Consistent C state) :
    (runRO (rawTable Q C) ((simulator Q).answer state input)).1 =
      (⟨C, observe state.publicLog input (C input)⟩, C input) := by
  rcases h with ⟨seed, consistent⟩
  cases cached : lookup state.publicLog input with
  | some d =>
    have hd := consistent input d (lookup_mem cached)
    simp [simulator, cached, runRO, seed, hd]
  | none =>
    cases recognized : privateKey Q state.publicLog input with
    | none => simp [simulator, cached, recognized, runRO, seed]
    | some key =>
      have hk := rawTable_privateKey C consistent recognized
      simp [simulator, cached, recognized, runRO, hk, seed]

theorem answer_consistent (Q : Nat) (C : PrimitiveOracle)
    (state : DuplexPublicSimulator.State) (input : Node) (h : Consistent C state) :
    Consistent C (runRO (rawTable Q C) ((simulator Q).answer state input)).1.1 := by
  rw [answer_real Q C state input h]
  refine ⟨rfl, ?_⟩
  intro n d member
  rcases List.mem_cons.mp member with he | he
  · cases he; rfl
  · exact h.2 n d he

/-- Equality of actual public views only: the ideal execution retains its own
private-query meter, which need not equal the real execution's zero meter. -/
theorem runIdeal_view {Q : Nat} {Result : Type} (C : PrimitiveOracle) (iv : Digest32)
    (state : DuplexPublicSimulator.State) (consistent : Consistent C state)
    (program : Program Result) (remaining : Nat) (cap : remaining ≤ Q)
    (counted : Counts remaining program) :
    (runIdeal (simulator Q) (rawTable Q C) iv state program remaining cap counted).view =
      (runReal C iv program).view := by
  induction program generalizing state remaining with
  | done result => rfl
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      have ha := answer_real Q C state input consistent
      have hc := answer_consistent Q C state input consistent
      have hr := ih (C input) _ hc (remaining-1) (by omega) (counted.2 _)
      simp only [runIdeal, runReal, realAnswer, prepend]
      simp only [ha] at hr ⊢
      exact congrArg (fun v : View Result =>
        View.mk (⟨.primitive purpose input,C input⟩ :: v.observations) v.result) hr
    | construction q valid =>
      have ha := rawTable_construction Q C iv q valid (counted.1.trans cap)
      have hr := ih (evalCoordinate (compressionOf C) iv q) state consistent
        (remaining-pathCost q) (by omega) (counted.2 _)
      simp only [runIdeal, runReal, realAnswer, prepend, ha]
      exact congrArg (fun v : View Result =>
        View.mk (⟨.construction q valid,evalCoordinate (compressionOf C) iv q⟩ ::
          v.observations) v.result) hr

/-- Deterministic real-game realization for every counted adaptive program.
No collision-freeness or simulator-correctness premise is required. -/
theorem real_ideal_view {Q : Nat} {Result : Type} (C : PrimitiveOracle) (iv : Digest32)
    (program : Program Result) (counted : Counts Q program) :
    (runReal C iv program).view =
      (runIdeal (simulator Q) (rawTable Q C) iv ((simulator Q).initial C)
        program Q (Nat.le_refl Q) counted).view := by
  exact (runIdeal_view C iv _ ⟨rfl, by simp [simulator]⟩ program Q
    (Nat.le_refl Q) counted).symm

/-- Every completed block is the same actual compression construction; this is a deterministic equality, not a uniform-table claim. -/
theorem realPacket_ideal (ctx : RawWHIRKeys.Context) (Q : Nat) (C : PrimitiveOracle)
    (packet : RawWHIRKeys.Packet ctx Q) :
    WHIRModeFinal.realPacket ctx Q C packet =
      WHIRModeFinal.idealPacket ctx Q (rawTable Q C) packet := by
  funext block
  exact (rawTable_construction Q C ctx.iv (RawWHIRKeys.coordinate ctx packet.val block.val)
    (RawWHIRKeys.coordinate_admissible ctx Q ⟨packet,block⟩)
    (by rw [RawWHIRKeys.pathCost_block]; exact RawWHIRKeys.packet_pathBound ctx Q packet)).symm

theorem realHistory_ideal (ctx : RawWHIRKeys.Context) (Q : Nat) (C : PrimitiveOracle)
    (packets : List (RawWHIRKeys.Packet ctx Q)) :
    WHIRModeFinal.realHistory ctx Q C packets =
      WHIRModeFinal.idealHistory ctx Q (rawTable Q C) packets := by
  simp only [WHIRModeFinal.realHistory,WHIRModeFinal.idealHistory,realPacket_ideal]

theorem realCallers_ideal (ctx : RawWHIRKeys.Context) (Q : Nat) (C : PrimitiveOracle)
    (packet : RawWHIRKeys.Packet ctx Q) (positions : List (WHIRModeFinal.CallerPosition ctx Q packet)) :
    WHIRModeFinal.realCallers ctx Q C packet positions =
      WHIRModeFinal.idealCallers ctx Q (rawTable Q C) packet positions := by
  unfold WHIRModeFinal.realCallers WHIRModeFinal.idealCallers
  apply List.map_congr_left
  intro position _
  have same := rawTable_construction Q C ctx.iv position.val
    (RawWHIRKeys.callerOutput_admissible ctx Q packet position.val position.property)
    (RawWHIRKeys.callerOutput_pathBound ctx Q packet position.val position.property)
  change rawTable Q C (RawWHIRKeys.callerOutputKey ctx Q packet position.val position.property).val = _ at same
  rw [same]

theorem realCompletion_ideal (ctx : RawWHIRKeys.Context) (Q : Nat) (C : PrimitiveOracle)
    (packet : Option (RawWHIRKeys.Packet ctx Q)) :
    WHIRModeFinal.realCompletion ctx Q C packet =
      WHIRModeFinal.idealCompletion ctx Q (rawTable Q C) packet := by
  cases packet with
  | none => rfl
  | some packet =>
      simp only [WHIRModeFinal.realCompletion,WHIRModeFinal.idealCompletion,realCallers_ideal,realHistory_ideal]

#print axioms evalRaw_complete
#print axioms rawTable_privateKey
#print axioms rawTable_construction
#print axioms answer_real
#print axioms answer_consistent
#print axioms runIdeal_view
#print axioms real_ideal_view
end Whir.WHIRRealSimulator
