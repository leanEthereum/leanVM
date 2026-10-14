import Whir.SpongefishCurrentIdealRows
import Whir.SpongefishCurrentHistoryReplies
import Whir.SpongefishCurrentPartitionCapture
import Whir.PCSBCSLiteralStatePath
import Whir.PCSBCSCapturedSourceStatePath
import Whir.PCSBCSRestorationHazard
import Whir.WHIRQueryOracleRecurrence

/-! Refinement of the current #607 round node model (`SpongefishCurrentBCSKnowledge.Refines` for `SpongefishCurrentGoodEvent.goodFull`).

The builder reads only the table with the selected packet erased. It recovers the received record from the post-binding construction key, the caller original by caller replay with the admissible in-budget getter of the joined table, the Root0 and level-root images by first-mention partition capture of the references mentioned by the packet history (header frame and level-ending reply frames), the tape of every earlier draw from the raw keys of the history prefixes, and the replies by a reply parser of the history completed with the captured oracles. On every opening packet of a good table it returns the literal caller data of the returned walk (`builder_exact`): the post-binding coordinate is short, so the erased packet is never read by the caller replay; every mentioned root is captured before the packet answer; earlier draws are other packets; and the parser is exact before the packet coordinate. The packets of all coordinates, in schedule order, are recorded, so the literal before/after identities give the state path (`statePath`).

`refines_of_facts` is generic in the program and the reply parser. `refines_full` instantiates it with the full source program and `SpongefishCurrentHistoryReplies.historyReplies`, using the opening packet histories, walk tape, seed, roots and parser exactness of `SpongefishCurrentHistoryReplies` and the row binding and terminal state of `SpongefishCurrentIdealRows`; its remaining hypotheses are static or header glue. -/
namespace Whir.SpongefishCurrentRefines
open Concrete Protocol CausalGame FiatShamirGame DuplexModeGame DuplexFraming
open TypedOracleCompiler PCSBCSChallengeOracle PCSBCSCallerBinding
open SpongefishCurrentOpeningAcceptance SpongefishCurrentRoundPackets
open CausalProbability (position get levelCoordinates visibleCoordinates)
set_option autoImplicit false

variable {p : ParameterBounds.Profile}
local notation "cfg" => ParameterBounds.config p

/-! ## Static schedule facts -/

/-- Every deployed coordinate draws a positive number of bytes. -/
theorem widths_deployed : ∀ p : ParameterBounds.Profile,
    ((WHIRHistory.schedule (ParameterBounds.config p)).all fun q =>
      decide (PCSBCSRounds.rawWidth q ≠ 0)) = true := by
  decide +kernel

theorem width_ne (q : Coord p) : PCSBCSRounds.rawWidth q ≠ 0 := by
  have all := widths_deployed p
  rw [List.all_eq_true] at all
  simpa using all q (WHIRHistory.coordinate_mem_schedule q)

/-- The proof-of-work draws of a coordinate. -/
def powPart (grinding : Fin (cfg).folds.size → Fin 64) (q : Coord p) : List (Option (Coord p)) :=
  match q with
  | .query i => if (grinding i).val = 0 then [] else [none]
  | _ => []

/-- The opening draws of one coordinate. -/
def drawStep (grinding : Fin (cfg).folds.size → Fin 64) (q : Coord p) : List (Option (Coord p)) :=
  powPart grinding q ++ (if PCSBCSRounds.rawWidth q = 0 then [] else [some q])

theorem openingDraws_eq (grinding : Fin (cfg).folds.size → Fin 64) :
    openingDraws grinding = (WHIRHistory.schedule cfg).flatMap (drawStep grinding) := rfl

theorem step_some (grinding : Fin (cfg).folds.size → Fin 64) (q y : Coord p) (n : Nat)
    (found : (drawStep grinding q)[n]? = some (some y)) :
    y = q ∧ n = (powPart grinding q).length := by
  have none_ : ∀ x ∈ powPart grinding q, x = none := by
    intro x member
    unfold powPart at member
    split at member
    · split at member <;> simp_all
    · simp at member
  unfold drawStep at found
  by_cases small : n < (powPart grinding q).length
  · rw [List.getElem?_append_left small] at found
    exact absurd (none_ _ (List.mem_of_getElem? found)) (by simp)
  · rw [List.getElem?_append_right (by omega)] at found
    split at found
    · simp at found
    · obtain ⟨inside,same⟩ := List.getElem?_eq_some_iff.mp found
      simp only [List.length_singleton] at inside
      simp only [List.getElem_singleton,Option.some.injEq] at same
      exact ⟨same.symm,by omega⟩

theorem flatMap_some {α : Type} (f : α → List (Option α)) (g : α → Nat)
    (hf : ∀ x y n, (f x)[n]? = some (some y) → y = x ∧ n = g x) :
    ∀ (xs : List α) (j : Nat) (y : α), (xs.flatMap f)[j]? = some (some y) →
      ∃ m, xs[m]? = some y ∧ j = ((xs.take m).flatMap f).length + g y ∧ g y < (f y).length
  | [], j, y, found => by simp at found
  | x :: xs, j, y, found => by
    rw [List.flatMap_cons] at found
    by_cases small : j < (f x).length
    · rw [List.getElem?_append_left small] at found
      obtain ⟨rfl,rfl⟩ := hf x y j found
      exact ⟨0,rfl,by simp,small⟩
    · rw [List.getElem?_append_right (by omega)] at found
      obtain ⟨m,at_,index,inside⟩ := flatMap_some f g hf xs _ y found
      refine ⟨m+1,by simpa using at_,?_,inside⟩
      simp only [List.take_succ_cons,List.flatMap_cons,List.length_append]
      omega

/-- The index of a PCS draw is fixed by the schedule position of its coordinate. -/
theorem draw_index (grinding : Fin (cfg).folds.size → Fin 64) (j : Nat) (q : Coord p)
    (found : (openingDraws grinding)[j]? = some (some q)) :
    j = (((WHIRHistory.schedule cfg).take (position q)).flatMap (drawStep grinding)).length +
        (powPart grinding q).length ∧
      (powPart grinding q).length < (drawStep grinding q).length := by
  obtain ⟨m,at_,index,inside⟩ := flatMap_some (drawStep grinding) (fun q => (powPart grinding q).length)
    (step_some grinding) _ j q found
  have place : m = position q := by
    obtain ⟨lt,eq⟩ := List.getElem?_eq_some_iff.mp at_
    rw [← WHIRHistory.schedule_idxOf,← eq]
    exact ((WHIRHistory.schedule_nodup cfg).idxOf_getElem m lt).symm
  subst place
  exact ⟨index,inside⟩

theorem flatMap_take_mono {α β : Type} (f : α → List β) (xs : List α) (a b : Nat) (le : a ≤ b) :
    ((xs.take a).flatMap f).length ≤ ((xs.take b).flatMap f).length := by
  conv_rhs => rw [← List.take_append_drop a (xs.take b)]
  rw [List.take_take,Nat.min_eq_left le,List.flatMap_append,List.length_append]
  omega

theorem flatMap_take_succ {α β : Type} (f : α → List β) (xs : List α) (m : Nat) (x : α)
    (at_ : xs[m]? = some x) :
    ((xs.take (m+1)).flatMap f).length = ((xs.take m).flatMap f).length + (f x).length := by
  rw [List.take_add_one,at_]
  simp [List.flatMap_append]

/-- Draw order is schedule order. -/
theorem draw_lt (grinding : Fin (cfg).folds.size → Fin 64) (j j' : Nat) (r q : Coord p)
    (hr : (openingDraws grinding)[j']? = some (some r))
    (hq : (openingDraws grinding)[j]? = some (some q)) (earlier : position r < position q) : j' < j := by
  obtain ⟨ir,inr⟩ := draw_index grinding j' r hr
  obtain ⟨iq,_⟩ := draw_index grinding j q hq
  have step := flatMap_take_succ (drawStep grinding) _ _ r (WHIRHistory.schedule_get_position r)
  have mono := flatMap_take_mono (drawStep grinding) (WHIRHistory.schedule cfg) (position r + 1)
    (position q) earlier
  omega

/-- The draw of a coordinate, in the static draw list. -/
def drawIndex (grinding : Fin (cfg).folds.size → Fin 64) (c : Coord p) : Nat :=
  (openingDraws grinding).idxOf (some c)

theorem drawIndex_eq (grinding : Fin (cfg).folds.size → Fin 64) (j : Nat) (c : Coord p)
    (found : (openingDraws grinding)[j]? = some (some c)) : drawIndex grinding c = j := by
  have at_ : (openingDraws grinding)[drawIndex grinding c]? = some (some c) :=
    List.getElem?_idxOf (List.mem_of_getElem? found)
  obtain ⟨a,_⟩ := draw_index grinding _ c at_
  obtain ⟨b,_⟩ := draw_index grinding j c found
  omega

theorem drawIndex_spec (grinding : Fin (cfg).folds.size → Fin 64) (c : Coord p) :
    (openingDraws grinding)[drawIndex grinding c]? = some (some c) := by
  obtain ⟨j,found⟩ := SpongefishCurrentOpeningPackets.openingDraws_complete grinding c
    (WHIRHistory.coordinate_mem_schedule c) (width_ne c)
  rw [drawIndex_eq grinding j c found]
  exact found

/-! ## Level order -/

def levelOf : Coord p → Option Nat
  | .fold i _ => some i.val
  | .ood i _ => some i.val
  | .query i => some i.val
  | _ => none

theorem levelOf_mem (k : Nat) (q : Coord p) (h : q ∈ levelCoordinates cfg k) : levelOf q = some k := by
  unfold levelCoordinates at h
  split_ifs at h with hk
  · simp only [List.mem_append,List.mem_ofFn,List.mem_singleton] at h
    rcases h with (⟨j,rfl⟩ | ⟨j,rfl⟩) | rfl <;> rfl
  · simp at h

/-- Every coordinate of an earlier level precedes every coordinate of a later level. -/
theorem level_before (a b : Nat) (lt : a < b) (x y : Coord p) (hx : x ∈ levelCoordinates cfg a)
    (hy : y ∈ levelCoordinates cfg b) : position x < position y := by
  have hb : b < (cfg).folds.size := by
    unfold levelCoordinates at hy
    split_ifs at hy with h
    · exact h
    · simp at hy
  have range : List.range (cfg).folds.size = List.range (a+1) ++
      (List.range ((cfg).folds.size-(a+1))).map (fun n => a+1+n) := by
    calc
      List.range (cfg).folds.size = List.range ((a+1)+((cfg).folds.size-(a+1))) :=
        congrArg List.range (by omega)
      _ = _ := by rw [List.range_add]
  have shape : visibleCoordinates cfg =
      ([(.initial : Coord p)] ++ (List.range (a+1)).flatMap (levelCoordinates cfg)) ++
      (((List.range ((cfg).folds.size-(a+1))).map (fun n => a+1+n)).flatMap (levelCoordinates cfg) ++
        List.ofFn fun j : Fin ((cfg).logN - (cfg).folds.toList.sum - 1) =>
          CausalProbability.Coordinate.tail ⟨j.val,by omega⟩) := by
    unfold visibleCoordinates
    rw [range,List.flatMap_append]
    simp only [List.append_assoc]
  have inA : x ∈ [(.initial : Coord p)] ++ (List.range (a+1)).flatMap (levelCoordinates cfg) :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨a,List.mem_range.mpr (by omega),hx⟩)
  have outA : y ∉ [(.initial : Coord p)] ++ (List.range (a+1)).flatMap (levelCoordinates cfg) := by
    have level := levelOf_mem b y hy
    intro member
    rcases List.mem_append.mp member with initial | later
    · rw [List.mem_singleton.mp initial] at level
      cases level
    · obtain ⟨m,hm,inside⟩ := List.mem_flatMap.mp later
      have := levelOf_mem m y inside
      rw [level] at this
      cases this
      have := List.mem_range.mp hm
      omega
  unfold position
  rw [shape,List.idxOf_append_of_mem inA,List.idxOf_append_of_notMem outA]
  have := List.idxOf_lt_length_of_mem inA
  omega

theorem fold_lt_query (i : Fin (cfg).folds.size) (k : Fin (cfg).folds[i.val]!) (t : Tape cfg) :
    position (.fold i k : Coord p) < position (.query i : Coord p) := by
  rw [CausalPositions.position_fold i k t,CausalPositions.position_query i t]
  have := k.isLt
  omega

/-- The last fold of the level before `i`. -/
def lastFold : Nat → Option (Coord p)
  | 0 => none
  | i+1 =>
    if h : i < (cfg).folds.size then
      some (.fold ⟨i,h⟩ ⟨(cfg).folds[i]! - 1,by
        have : 0 < (cfg).folds[i]! := WHIRQueryOracleRecurrence.production_folds_positive p ⟨i,h⟩
        change (cfg).folds[i]! - 1 < (cfg).folds[i]!
        omega⟩)
    else none

theorem lastFold_eq (i : Fin (cfg).folds.size) (k : Fin (cfg).folds[i.val]!)
    (last : isLastFold i k = true) : lastFold (p := p) (i.val+1) = some (.fold i k) := by
  have kEq : k.val = (cfg).folds[i.val]! - 1 := by
    simp only [isLastFold,decide_eq_true_eq] at last
    omega
  obtain ⟨kv,klt⟩ := k
  simp only at kEq
  subst kEq
  simp only [lastFold,i.isLt,↓reduceDIte]

/-! ## The builder -/

section Builder
variable (Q : Nat) (iv : Digest32) (grinding : Fin (ParameterBounds.config p).folds.size → Fin 64)
  (boundary : Nat)

/-- Tables of the current round partition. -/
abbrev Table := (key : Key p Q iv grinding boundary) → Answer p Q iv grinding boundary key

/-- The output blocks of the coordinate `r` drawn at the first `n` frames of `H`, looked up by raw key through the joined table. -/
noncomputable def prefixBlocks (T : Table Q iv grinding boundary) (H : FramedHistory) (n : Nat)
    (r : Coord p) : Fin (blocks (PCSBCSRounds.rawWidth r)) → Digest32 := fun b =>
  if work : pathCost ⟨{H with frames := H.frames.take n},.output b.val⟩ ≤ Q then
    (partition p Q iv grinding boundary).join T
      (.inr (constructionKey Q iv ⟨{H with frames := H.frames.take n},.output b.val⟩ work))
  else 0

/-- The grouped sample of `r` read at its draw prefix of `H`. -/
noncomputable def sampleAt (T : Table Q iv grinding boundary) (H : FramedHistory) (r : Coord p) :
    PCSBCSRounds.Raw r :=
  grouped r (prefixBlocks Q iv grinding boundary T H (boundary + drawIndex grinding r + 1) r)

/-- The tape of every coordinate strictly before `q`, read from the prefixes of `H`. -/
noncomputable def tapeOf (T : Table Q iv grinding boundary) (H : FramedHistory) (q : Coord p) : Tape cfg :=
  (CausalProbability.coordinates cfg).symm fun r =>
    if position r < position q then StackWHIRReplay.projectSample r (sampleAt Q iv grinding boundary T H r)
    else 0

/-- The ring prefix of the initial draw, read from the prefix of `H`. -/
noncomputable def ringOf (T : Table Q iv grinding boundary) (H : FramedHistory) : RingPCSGame.Prefix :=
  (sampleAt Q iv grinding boundary T H .initial).1

/-- The reference of the level-`i` root mentioned by `H`: Root0 from the header frame, a later level root from the reply frame of the last fold of the level before. -/
def rootRef (shape : SpongefishSessionAdapter.Shape) (headerFrames : Nat) (H : FramedHistory) (i : Nat) :
    Option PCSBCSSourceRootReferences.Reference :=
  if i = 0 then SpongefishCurrentRootPolicy.anchorReference shape headerFrames H
  else (lastFold (p := p) i).bind fun c =>
    SpongefishCurrentRootPolicy.levelAt p grinding boundary H (drawIndex grinding c)

/-- First-mention capture of the level-`i` root mentioned by `H`. -/
noncomputable def frozenAt {R : Type} {n : Nat}
    (source : Sampling (Key p Q iv grinding boundary) (Answer p Q iv grinding boundary) R n)
    (shape : SpongefishSessionAdapter.Shape) (headerFrames : Nat) (T : Table Q iv grinding boundary)
    (H : FramedHistory) (i : Nat) : Option PCSBCSMerkleRootCache.Frozen :=
  (rootRef grinding boundary shape headerFrames H i).bind fun ref =>
    SpongefishCurrentPartitionCapture.pcapture (partition p Q iv grinding boundary)
      (SpongefishCurrentRootPolicy.addresses p grinding shape headerFrames boundary iv) ref source T

open Classical in
/-- In-budget construction answers of a raw table, at admissible coordinates only. -/
noncomputable def admissibleGetter (table : PublicCompressionCouplingMixed.Key Q → Digest32)
    (c : Coordinate) : Option Digest32 :=
  if DuplexEncoding.Admissible c then SpongefishCurrentCallerOriginalTable.tableGetter Q iv table c else none

/-- The post-binding coordinate of a packet history. -/
def bindingCoordinate (H : FramedHistory) : Coordinate :=
  ⟨{H with frames := H.frames.take (boundary+1)},.output 0⟩

/-- The selected record of a coordinate's construction key. -/
def recordAt (k : Nat) (shape : AnchoredHeaderCodec.Shape) (q : Coordinate) :
    Option SpongefishSessionAdapter.Record :=
  if work : pathCost q ≤ Q then
    SpongefishCurrentCallerOriginalTable.recordOf shape iv k (constructionKey Q iv q work)
  else none

/-- The current round builder: from the table with the selected packet erased, the caller original at the post-binding coordinate, the first-mention Root0 and level captures, the tape of earlier draws and the replies parsed from the packet history. -/
noncomputable def builder (headerFrames k : Nat) (instanceBytes : List Byte)
    (layout : WHIRCallerClaims.CallerLayout) (parse : FramedHistory → Tape cfg → (Nat → Oracle) → Array Reply)
    {R : Type} {n : Nat}
    (source : Sampling (Key p Q iv grinding boundary) (Answer p Q iv grinding boundary) R n) :
    Builder p Q iv grinding boundary := fun packet other =>
  let T' := SpongefishCurrentPartitionCapture.otherTable (partition p Q iv grinding boundary) packet other
  let H := packet.history
  let q0 := bindingCoordinate boundary H
  (recordAt Q iv k (AnchoredSourceCaller.shape layout) q0).bind fun r =>
  (SpongefishCurrentCallerOriginalTable.tableCandidate p layout q0 r instanceBytes
    (admissibleGetter Q iv ((partition p Q iv grinding boundary).join T'))).bind fun input =>
  (frozenAt Q iv grinding boundary source (AnchoredSourceCaller.shape layout) headerFrames T' H 0).map fun f0 =>
    let next := fun i => ((frozenAt Q iv grinding boundary source (AnchoredSourceCaller.shape layout)
      headerFrames T' H i).bind (PCSBCSFrozenOracleRows.frozenOracle i)).getD #[]
    let t := tapeOf Q iv grinding boundary T' H packet.coord
    PCSBCSRestorationHazard.literalCallerData p input f0.raw (ringOf Q iv grinding boundary T' H) t
      (parse H t (SpongefishCurrentOpeningExperiment.levelOracle f0.raw next)) packet.coord

end Builder

/-! ## Erased tables, raw keys and root mentions -/

section Tables
variable (Q : Nat) (iv : Digest32) (grinding : Fin (ParameterBounds.config p).folds.size → Fin 64)
  (boundary : Nat)

theorem get_coordinates (f : ∀ r : Coord p, CausalProbability.Sample r) (r : Coord p) :
    get r ((CausalProbability.coordinates cfg).symm f) = f r :=
  congrFun ((CausalProbability.coordinates cfg).apply_symm_apply f) r

theorem otherTable_of_ne (packet : Packet p Q grinding boundary) (T : Table Q iv grinding boundary)
    (key : Key p Q iv grinding boundary) (ne : key ≠ .inl packet) :
    SpongefishCurrentPartitionCapture.otherTable (partition p Q iv grinding boundary) packet
      (PCSStateRestoration.Latent.erase (.inl packet) T) key = T key := by
  classical
  unfold SpongefishCurrentPartitionCapture.otherTable
  rw [PCSStateRestoration.Latent.fill_erase]
  exact Function.update_of_ne ne _ _

theorem join_other (packet : Packet p Q grinding boundary) (T : Table Q iv grinding boundary)
    (raw : PublicCompressionCouplingMixed.Key Q)
    (other : ∀ c, (partition p Q iv grinding boundary).recognize raw = some c → c.1 ≠ packet) :
    (partition p Q iv grinding boundary).join (SpongefishCurrentPartitionCapture.otherTable
      (partition p Q iv grinding boundary) packet (PCSStateRestoration.Latent.erase (.inl packet) T)) raw =
      (partition p Q iv grinding boundary).join T raw := by
  unfold RawOracleCoupling.Partition.join
  split
  · rename_i c hc
    exact congrFun (otherTable_of_ne Q iv grinding boundary packet T (.inl c.1)
      (fun e => other c hc (Sum.inl.inj e))) c.2
  · rename_i hc
    exact otherTable_of_ne Q iv grinding boundary packet T _ (by simp)

theorem recognize_key (raw : RawKey Q) (c : Sigma (PacketBlock (p := p) (Q := Q) (grinding := grinding)
    (boundary := boundary)))
    (found : (partition p Q iv grinding boundary).recognize (.inr raw) = some c) :
    raw = packetKey iv c.1 c.2 := by
  have encoded := (partition p Q iv grinding boundary).encode_recognize _ c found
  change Sum.inr (packetKey iv c.1 c.2) = _ at encoded
  exact (Sum.inr.inj encoded).symm

/-- A construction key of an admissible coordinate with at most `boundary` frames is garbage. -/
theorem small_garbage (c : Coordinate) (valid : DuplexEncoding.Admissible c) (work : pathCost c ≤ Q)
    (small : c.history.frames.length ≤ boundary)
    (blk : Sigma (PacketBlock (p := p) (Q := Q) (grinding := grinding) (boundary := boundary))) :
    (partition p Q iv grinding boundary).recognize (.inr (constructionKey Q iv c work)) ≠ some blk := by
  intro found
  have key := recognize_key Q iv grinding boundary _ blk found
  have same := constructionKey_injective Q iv valid (blk.1.admissible blk.2) work (blk.1.bounded blk.2) key
  have frames := congrArg (fun c : Coordinate => c.history.frames.length) same
  have large := SpongefishCurrentCallerOriginalTable.packet_frames blk.1
  simp only at frames
  omega

theorem addresses_block (shape : SpongefishSessionAdapter.Shape) (headerFrames : Nat)
    (P : Packet p Q grinding boundary) (b : PacketBlock P) :
    SpongefishCurrentRootPolicy.addresses p grinding shape headerFrames boundary iv
      ((partition p Q iv grinding boundary).encode ⟨P,b⟩) =
      SpongefishCurrentRootPolicy.references p grinding shape headerFrames boundary P.history := by
  change SpongefishCurrentRootPolicy.addresses p grinding shape headerFrames boundary iv
    (.inr (constructionKey Q iv ⟨P.history,.output b.val⟩ (P.bounded b))) = _
  simp only [SpongefishCurrentRootPolicy.addresses,
    WHIRHeaderRoots.decodeRaw_construction iv _ (P.admissible b) (P.bounded b)]
  rfl

theorem mentioned (shape : SpongefishSessionAdapter.Shape) (headerFrames : Nat)
    (P : Packet p Q grinding boundary) (ref : PCSBCSSourceRootReferences.Reference)
    (member : ref ∈ SpongefishCurrentRootPolicy.references p grinding shape headerFrames boundary P.history) :
    ref ∈ SpongefishCurrentPartitionCapture.paddr (partition p Q iv grinding boundary)
      (SpongefishCurrentRootPolicy.addresses p grinding shape headerFrames boundary iv) (.inl P) :=
  (SpongefishCurrentPartitionCapture.mem_paddr_packet _ _ P ref).mpr
    ⟨firstBlock P,by rw [addresses_block]; exact member⟩

theorem uniform (shape : SpongefishSessionAdapter.Shape) (headerFrames : Nat) :
    SpongefishCurrentPartitionCapture.Uniform (partition p Q iv grinding boundary)
      (SpongefishCurrentRootPolicy.addresses p grinding shape headerFrames boundary iv) := by
  intro P b c ref member
  rw [addresses_block] at member ⊢
  exact member

/-- On the source of a counted program, the partition capture is the public capture of the view. -/
theorem pcapture_public (shape : SpongefishSessionAdapter.Shape) (headerFrames : Nat) {R : Type}
    (program : Program R) (counted : Counts Q program) (T : Table Q iv grinding boundary)
    (ref : PCSBCSSourceRootReferences.Reference) :
    SpongefishCurrentPartitionCapture.pcapture (partition p Q iv grinding boundary)
        (SpongefishCurrentRootPolicy.addresses p grinding shape headerFrames boundary iv) ref
        (SpongefishCurrentBCSKnowledge.source (partition p Q iv grinding boundary) iv program counted) T =
      SpongefishCurrentRootPolicy.publicCapture (B := Q) p grinding shape headerFrames boundary iv ref
        (Sampling.eval T (SpongefishCurrentBCSKnowledge.source (partition p Q iv grinding boundary) iv
          program counted)) :=
  SpongefishCurrentPartitionCapture.pcapture_view _ _ (uniform Q iv grinding boundary shape headerFrames)
    (SpongefishCurrentPartitionCapture.round_plain p Q iv grinding boundary) iv ref program Q (le_refl Q)
    counted T

/-- The caller original of the erased table: the public candidate of the view transfers to the admissible getter of the joined table, and the erased packet is never read. -/
theorem input_exact {R : Type} (program : Program R) (counted : Counts Q program)
    (T : Table Q iv grinding boundary) (packet : Packet p Q grinding boundary)
    (layout : WHIRCallerClaims.CallerLayout) (q0 : Coordinate) (r : SpongefishSessionAdapter.Record)
    (instanceBytes : List Byte) (input : PCSBCSCallerBinding.CallerInput p)
    (atBoundary : q0.history.frames.length ≤ boundary + 1)
    (accepted : SpongefishCurrentSourceCallerOriginal.candidate (Q := Q) p layout q0 r instanceBytes
      (Sampling.eval T (SpongefishCurrentBCSKnowledge.source (partition p Q iv grinding boundary) iv program
        counted)).observations = some input) :
    SpongefishCurrentCallerOriginalTable.tableCandidate p layout q0 r instanceBytes
      (admissibleGetter Q iv ((partition p Q iv grinding boundary).join
        (SpongefishCurrentPartitionCapture.otherTable (partition p Q iv grinding boundary) packet
          (PCSStateRestoration.Latent.erase (.inl packet) T)))) = some input := by
  classical
  have first : SpongefishCurrentCallerOriginalTable.tableCandidate p layout q0 r instanceBytes
      (admissibleGetter Q iv ((partition p Q iv grinding boundary).join T)) = some input := by
    apply SpongefishCurrentCallerOriginalTable.candidate_tableCandidate p layout q0 r instanceBytes _ _ input
      accepted
    intro o member c valid query work
    unfold SpongefishCurrentBCSKnowledge.source at member
    rw [Atomic.eval_program] at member
    have observed := SpongefishCurrentCallerOriginalTable.table_observed Q _ iv [] program Q (le_refl Q)
      counted o member c valid query work
    simp only [admissibleGetter,valid,↓reduceIte]
    exact observed
  rw [SpongefishCurrentCallerOriginalTable.tableCandidate_boundary p layout q0 r instanceBytes _
    (admissibleGetter Q iv ((partition p Q iv grinding boundary).join T)) boundary atBoundary ?_]
  · exact first
  intro c small
  unfold admissibleGetter
  split
  · rename_i valid
    unfold SpongefishCurrentCallerOriginalTable.tableGetter
    split
    · rename_i work
      rw [join_other Q iv grinding boundary packet T _
        (fun blk found _ => small_garbage Q iv grinding boundary c valid work small blk found)]
    · rfl
  · rfl

end Tables

theorem fold_mem (i : Fin (cfg).folds.size) (k : Fin (cfg).folds[i.val]!) :
    (.fold i k : Coord p) ∈ levelCoordinates cfg i.val := by
  unfold levelCoordinates
  rw [dite_eq_left i.isLt]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨k,rfl⟩))

theorem query_mem (i : Fin (cfg).folds.size) : (.query i : Coord p) ∈ levelCoordinates cfg i.val := by
  simp [levelCoordinates,i.isLt]

/-- The literal caller data reads the ring only after the initial draw, the tape only strictly before `q` and the replies only before the position of `q`. -/
theorem literalCallerData_congr (original : PCSBCSCallerBinding.CallerInput p) (root : BaseOracle)
    (ring ring' : RingPCSGame.Prefix) (t t' : Tape cfg) (a a' : Array Reply) (q : Coord p)
    (rings : q ≠ .initial → ring = ring')
    (tapes : ∀ r : Coord p, position r < position q → get r t = get r t')
    (answers : PCSRoundByRoundTranscriptState.priorAnswers a (position q) =
      PCSRoundByRoundTranscriptState.priorAnswers a' (position q)) :
    PCSBCSRestorationHazard.literalCallerData p original root ring t a q =
      PCSBCSRestorationHazard.literalCallerData p original root ring' t' a' q := by
  unfold PCSBCSRestorationHazard.literalCallerData PCSBCSRestorationHazard.incomingData
    PCSBCSRestorationHazard.incomingTrace
  have ringPart : (if q = .initial then none else some ring) = (if q = .initial then none else some ring') := by
    split_ifs with h
    · rfl
    · rw [rings h]
  have tapePart : (fun r : Coord p => if position r < position q then some (get r t) else none) =
      (fun r : Coord p => if position r < position q then some (get r t') else none) := by
    funext r
    split_ifs with h
    · rw [tapes r h]
    · rfl
  rw [ringPart,tapePart,answers]

/-! ## Good-table facts and exactness -/

/-- Levels whose oracle is read by the replies strictly before `q`: the level announced by a root-carrying last fold before `q`, and the level of a query reply before `q`. -/
def LevelUsed (q : Coord p) (i : Nat) : Prop :=
  (∃ (i' : Fin (cfg).folds.size) (k : Fin (cfg).folds[i'.val]!), isLastFold i' k = true ∧
    i'.val + 1 < (cfg).folds.size ∧ i = i'.val + 1 ∧ position (.fold i' k : Coord p) < position q) ∨
  (∃ i' : Fin (cfg).folds.size, 0 < i'.val ∧ i = i'.val ∧ position (.query i' : Coord p) < position q)

/-- Drawn byte runs of the opening draws, in draw order. -/
def drawnBytes (grinding : Fin (cfg).folds.size → Fin 64) (data : SpongefishCurrentMixedModeCompiler.Data) :
    List (List Byte) :=
  SpongefishCurrentOpeningPackets.verifierBytes (SpongefishCurrentOpeningPackets.openingEvents grinding data.events)

section Exact
variable (Q : Nat) (iv : Digest32) (grinding : Fin (ParameterBounds.config p).folds.size → Fin 64)
  (boundary headerFrames k : Nat) (instanceBytes : List Byte) (layout : WHIRCallerClaims.CallerLayout)
  (parse : FramedHistory → Tape (ParameterBounds.config p) → (Nat → Oracle) → Array Reply)
  (program : Program (SpongefishCurrentOpeningProgram.FullResult p)) (counted : Counts Q program)

/-- Everything the good event and the sibling modules supply on one table: the good-event caller record and original, the opening packet histories with their nesting and recorded packets, the tape and seed of the returned walk at every draw, the header and level roots of the walk read from the histories, and exactness of the reply parser before every packet coordinate. -/
structure Facts (T : Table Q iv grinding boundary) (data : SpongefishCurrentMixedModeCompiler.Data)
    (col : Collected p) (r : SpongefishSessionAdapter.Record) (input : PCSBCSCallerBinding.CallerInput p)
    (seed : RingPCSGame.Prefix × E) (histories : List FramedHistory) : Prop where
  record : ∃ work : pathCost (SpongefishCurrentGoodEvent.postBinding boundary data) ≤ Q,
    SpongefishCurrentCallerOriginalTable.recordOf (AnchoredSourceCaller.shape layout) iv k
      (constructionKey Q iv (SpongefishCurrentGoodEvent.postBinding boundary data) work) = some r
  original : SpongefishCurrentSourceCallerOriginal.candidate (Q := Q) p layout
    (SpongefishCurrentGoodEvent.postBinding boundary data) r instanceBytes
    (Sampling.eval T (SpongefishCurrentBCSKnowledge.source (partition p Q iv grinding boundary) iv program
      counted)).observations = some input
  seeded : col.seed = some seed
  postHistory : ∀ h : FramedHistory, histories[0]? = some h →
    SpongefishCurrentGoodEvent.postBinding boundary data = ⟨h,.output 0⟩
  frames : ∀ (j : Nat) (h : FramedHistory), histories[j]? = some h → h.frames.length = boundary + j + 1
  nested : ∀ (i j : Nat) (hi hj : FramedHistory), i ≤ j → histories[i]? = some hi →
    histories[j]? = some hj → hi = {hj with frames := hj.frames.take (boundary + i + 1)}
  packets : ∀ (j : Nat) (q : Coord p), (openingDraws grinding)[j]? = some (some q) →
    ∃ (packet : Packet p Q grinding boundary) (bytes : List Byte),
      packet.coord = q ∧ histories[j]? = some packet.history ∧
      (drawnBytes grinding data)[j]? = some bytes ∧
      decodeSample packet.coord bytes = grouped packet.coord (T (.inl packet)) ∧
      (⟨.inl packet,T (.inl packet)⟩ : Sigma (Answer p Q iv grinding boundary)) ∈
        (Sampling.execute T (SpongefishCurrentBCSKnowledge.source (partition p Q iv grinding boundary) iv
          program counted)).2
  tapeAt : ∀ (j : Nat) (q : Coord p) (bytes : List Byte), (openingDraws grinding)[j]? = some (some q) →
    (drawnBytes grinding data)[j]? = some bytes →
    get q col.tape = StackWHIRReplay.projectSample q (decodeSample q bytes)
  seedAt : ∀ (j : Nat) (bytes : List Byte), (openingDraws grinding)[j]? = some (some .initial) →
    (drawnBytes grinding data)[j]? = some bytes → col.seed = some (decodeSample (.initial : Coord p) bytes)
  anchor : ∃ (root0 : Digest32) (h0 : FramedHistory), col.roots[0]? = some root0 ∧ histories[0]? = some h0 ∧
    headerFrames ≤ boundary + 1 ∧
    SpongefishCurrentAnchorHeader.fromHistory (AnchoredSourceCaller.shape layout)
      {h0 with frames := h0.frames.take headerFrames} = some root0
  levelRoots : ∀ (i' : Fin (cfg).folds.size) (k : Fin (cfg).folds[i'.val]!) (j' : Nat),
    isLastFold i' k = true → i'.val + 1 < (cfg).folds.size →
    (openingDraws grinding)[j']? = some (some (.fold i' k)) →
    ∃ (root : Digest32) (h : FramedHistory) (previous : Nat) (bytes : List Byte),
      col.roots[i'.val + 1]? = some root ∧ histories[j' + 1]? = some h ∧
      h.frames[boundary + j' + 1]? = some (.absorb previous bytes) ∧
      SpongefishCurrentRootPolicy.levelRoot bytes = some root
  parsed : ∀ (root : BaseOracle) (next : Nat → Oracle),
    SpongefishCurrentOpeningExperiment.RowsAuthenticated col.tape col.replies root next →
    ∀ (j : Nat) (q : Coord p) (h : FramedHistory), (openingDraws grinding)[j]? = some (some q) →
      histories[j]? = some h → ∀ t : Tape cfg, (∀ r : Coord p, position r < position q → get r t = get r col.tape) →
      ∀ next' : Nat → Oracle, (∀ i, LevelUsed q i → next' i = next i) →
        PCSRoundByRoundTranscriptState.priorAnswers
            (parse h t (SpongefishCurrentOpeningExperiment.levelOracle root next')) (position q) =
          PCSRoundByRoundTranscriptState.priorAnswers
            (SpongefishCurrentOpeningExperiment.restoredReplies col next) (position q)

/-- The view of the source on a table. -/
noncomputable abbrev viewOf (T : Table Q iv grinding boundary) : View (SpongefishCurrentOpeningProgram.FullResult p) :=
  Sampling.eval T (SpongefishCurrentBCSKnowledge.source (partition p Q iv grinding boundary) iv program counted)

/-- Exactness of the builder on every opening packet of a good table. -/
theorem builder_exact (T : Table Q iv grinding boundary) (data : SpongefishCurrentMixedModeCompiler.Data)
    (col : Collected p) (r : SpongefishSessionAdapter.Record) (input : PCSBCSCallerBinding.CallerInput p)
    (seed : RingPCSGame.Prefix × E) (histories : List FramedHistory)
    (facts : Facts Q iv grinding boundary headerFrames k instanceBytes layout parse program counted T data col r
      input seed histories)
    (frozens : Nat → PCSBCSMerkleRootCache.Frozen)
    (captured : SpongefishCurrentIdealRows.Captured grinding (AnchoredSourceCaller.shape layout) headerFrames
      boundary Q iv (viewOf Q iv grinding boundary program counted T) col frozens)
    (rows : SpongefishCurrentOpeningExperiment.RowsAuthenticated col.tape col.replies
      (SpongefishCurrentIdealRows.rootOracle (frozens 0)) (SpongefishCurrentIdealRows.nextOracle frozens))
    (j : Nat) (packet : Packet p Q grinding boundary)
    (draw : (openingDraws grinding)[j]? = some (some packet.coord))
    (history : histories[j]? = some packet.history) :
    builder Q iv grinding boundary headerFrames k instanceBytes layout parse
        (SpongefishCurrentBCSKnowledge.source (partition p Q iv grinding boundary) iv program counted)
        packet (PCSStateRestoration.Latent.erase (.inl packet) T) =
      some (PCSBCSRestorationHazard.literalCallerData p input (SpongefishCurrentIdealRows.rootOracle (frozens 0))
        seed.1 col.tape (SpongefishCurrentOpeningExperiment.restoredReplies col
          (SpongefishCurrentIdealRows.nextOracle frozens)) packet.coord) := by
  set H := packet.history with HDef
  set source := SpongefishCurrentBCSKnowledge.source (partition p Q iv grinding boundary) iv program counted
    with sourceDef
  set T' := SpongefishCurrentPartitionCapture.otherTable (partition p Q iv grinding boundary) packet
    (PCSStateRestoration.Latent.erase (.inl packet) T) with T'Def
  set shape := AnchoredSourceCaller.shape layout with shapeDef
  have lenH : H.frames.length = boundary + j + 1 := facts.frames j H history
  have inside : j < histories.length := (List.getElem?_eq_some_iff.mp history).1
  -- the post-binding coordinate and the caller original
  obtain ⟨h0,h0At⟩ : ∃ h0, histories[0]? = some h0 := ⟨_,List.getElem?_eq_getElem (by omega)⟩
  have h0Eq := facts.nested 0 j h0 H (Nat.zero_le _) h0At history
  have q0Eq : bindingCoordinate boundary H = SpongefishCurrentGoodEvent.postBinding boundary data := by
    rw [facts.postHistory h0 h0At,h0Eq]
    rfl
  have recordEq : recordAt Q iv k shape (bindingCoordinate boundary H) = some r := by
    obtain ⟨work,selected⟩ := facts.record
    unfold recordAt
    rw [q0Eq,dite_eq_left work]
    exact selected
  have inputEq := input_exact Q iv grinding boundary program counted T packet layout
    (bindingCoordinate boundary H) r instanceBytes input
    (by simp only [bindingCoordinate,List.length_take]; omega) (by rw [q0Eq]; exact facts.original)
  -- captures of the view
  have public_ : ∀ ref, SpongefishCurrentPartitionCapture.pcapture (partition p Q iv grinding boundary)
      (SpongefishCurrentRootPolicy.addresses p grinding shape headerFrames boundary iv) ref source T' =
      SpongefishCurrentPartitionCapture.pcapture (partition p Q iv grinding boundary)
        (SpongefishCurrentRootPolicy.addresses p grinding shape headerFrames boundary iv) ref source T →
      SpongefishCurrentPartitionCapture.pcapture (partition p Q iv grinding boundary)
        (SpongefishCurrentRootPolicy.addresses p grinding shape headerFrames boundary iv) ref source T' =
      SpongefishCurrentRootPolicy.publicCapture (B := Q) p grinding shape headerFrames boundary iv ref
        (viewOf Q iv grinding boundary program counted T) := by
    intro ref same
    rw [same]
    exact pcapture_public Q iv grinding boundary shape headerFrames program counted T ref
  -- Root0
  have rootEq : frozenAt Q iv grinding boundary source shape headerFrames T' H 0 = some (frozens 0) := by
    obtain ⟨root0,h0',rootAt,h0'At,headerLe,header⟩ := facts.anchor
    rw [h0At] at h0'At
    cases h0'At
    have headerH : SpongefishCurrentAnchorHeader.fromHistory shape
        {H with frames := H.frames.take headerFrames} = some root0 := by
      rw [← header,h0Eq]
      simp only [List.take_take]
      rw [Nat.min_eq_left (by omega)]
    have anchorH : SpongefishCurrentRootPolicy.anchorReference shape headerFrames H =
        some (SpongefishCurrentPhysicalRootCapture.reference shape root0) := by
      unfold SpongefishCurrentRootPolicy.anchorReference
      rw [ite_eq_left (by omega),headerH]
      rfl
    have member := mentioned Q iv grinding boundary shape headerFrames packet _
      (SpongefishCurrentRootPolicy.anchor_mem p grinding shape headerFrames boundary H root0 (by omega) headerH)
    have erased := SpongefishCurrentPartitionCapture.pcapture_erased (partition p Q iv grinding boundary)
      (SpongefishCurrentRootPolicy.addresses p grinding shape headerFrames boundary iv) packet _ member source T
    unfold frozenAt rootRef
    rw [ite_eq_left rfl,anchorH,Option.bind_some,public_ _ erased]
    exact captured 0 root0 (ParameterBounds.production_config_valid p).2.1 rootAt
  -- level roots
  have levelEq : ∀ (i' : Fin (cfg).folds.size) (kk : Fin (cfg).folds[i'.val]!), isLastFold i' kk = true →
      i'.val + 1 < (cfg).folds.size → position (.fold i' kk : Coord p) < position packet.coord →
      frozenAt Q iv grinding boundary source shape headerFrames T' H (i'.val+1) = some (frozens (i'.val+1)) := by
    intro i' kk last later earlier
    have drawC := drawIndex_spec grinding (.fold i' kk)
    have lt := draw_lt grinding j _ _ _ drawC draw earlier
    obtain ⟨root,h,previous,bytes,rootAt,hAt,frameAt,parsedRoot⟩ :=
      facts.levelRoots i' kk _ last later drawC
    have hEq := facts.nested _ j h H (by omega) hAt history
    have frameH : H.frames[boundary + drawIndex grinding (.fold i' kk) + 1]? = some (.absorb previous bytes) := by
      rw [hEq] at frameAt
      simp only [List.getElem?_take] at frameAt
      split at frameAt
      · exact frameAt
      · omega
    have levelAtEq : SpongefishCurrentRootPolicy.levelAt p grinding boundary H (drawIndex grinding (.fold i' kk)) =
        some ⟨root,SpongefishCurrentRootPolicy.levelShape p (i'.val+1)⟩ := by
      simp only [SpongefishCurrentRootPolicy.levelAt,drawC,last,later,and_self,↓reduceIte,frameH,parsedRoot,
        Option.map_some]
    have member := mentioned Q iv grinding boundary shape headerFrames packet _
      (SpongefishCurrentRootPolicy.level_mem p grinding shape headerFrames boundary H _ i' kk drawC last later
        previous bytes frameH root parsedRoot)
    have erased := SpongefishCurrentPartitionCapture.pcapture_erased (partition p Q iv grinding boundary)
      (SpongefishCurrentRootPolicy.addresses p grinding shape headerFrames boundary iv) packet _ member source T
    unfold frozenAt rootRef
    rw [ite_eq_right (by omega),lastFold_eq i' kk last,Option.bind_some,levelAtEq,Option.bind_some,public_ _ erased]
    have found := captured (i'.val+1) root later rootAt
    unfold SpongefishCurrentIdealRows.rootReference at found
    rw [ite_eq_right (by omega)] at found
    exact found
  have nextEq : ∀ i, LevelUsed packet.coord i →
      ((frozenAt Q iv grinding boundary source shape headerFrames T' H i).bind
        (PCSBCSFrozenOracleRows.frozenOracle i)).getD #[] = SpongefishCurrentIdealRows.nextOracle frozens i := by
    intro i used
    rcases used with ⟨i',kk,last,later,rfl,earlier⟩ | ⟨i',positive,rfl,earlier⟩
    · rw [levelEq i' kk last later earlier,Option.bind_some]
      rfl
    · let i0 : Fin (cfg).folds.size := ⟨i'.val - 1,by omega⟩
      have folds0 : 0 < (cfg).folds[i0.val]! := WHIRQueryOracleRecurrence.production_folds_positive p i0
      let k0 : Fin (cfg).folds[i0.val]! := ⟨(cfg).folds[i0.val]! - 1,by omega⟩
      have last0 : isLastFold i0 k0 = true := by
        simp only [isLastFold,decide_eq_true_eq,k0]
        omega
      have before := level_before (p := p) i0.val i'.val (by simp only [i0]; omega) (.fold i0 k0) (.query i')
        (fold_mem i0 k0) (query_mem i')
      have shift : i0.val + 1 = i'.val := by simp only [i0]; omega
      have agreed := levelEq i0 k0 last0 (by omega) (by omega)
      rw [shift] at agreed
      rw [agreed,Option.bind_some]
      rfl
  -- tape and ring
  have sample : ∀ r : Coord p, position r < position packet.coord → ∃ bytes,
      (drawnBytes grinding data)[drawIndex grinding r]? = some bytes ∧
      sampleAt Q iv grinding boundary T' H r = decodeSample r bytes := by
    intro r earlier
    have drawR := drawIndex_spec grinding r
    have lt := draw_lt grinding j _ r packet.coord drawR draw earlier
    obtain ⟨P,bytes,coordEq,histP,bytesAt,decoded,_⟩ := facts.packets _ r drawR
    subst coordEq
    refine ⟨bytes,bytesAt,?_⟩
    have nestP := facts.nested _ j P.history H lt.le histP history
    have ne : P ≠ packet := by
      intro same
      have lengths := facts.frames _ _ histP
      have equal := congrArg (fun x : Packet p Q grinding boundary => x.history.frames.length) same
      simp only [← HDef] at equal
      omega
    unfold sampleAt
    rw [decoded]
    refine congrArg (grouped P.coord) (funext fun b => ?_)
    unfold prefixBlocks
    rw [← nestP,dite_eq_left (P.bounded b)]
    change (partition p Q iv grinding boundary).join T' ((partition p Q iv grinding boundary).encode ⟨P,b⟩) = _
    rw [SpongefishCurrentOpeningPackets.join_encode]
    exact congrFun (otherTable_of_ne Q iv grinding boundary packet T (.inl P) (by simpa using ne)) b
  have tapes : ∀ r : Coord p, position r < position packet.coord →
      get r (tapeOf Q iv grinding boundary T' H packet.coord) = get r col.tape := by
    intro r earlier
    rw [tapeOf,get_coordinates,ite_eq_left earlier]
    obtain ⟨bytes,at_,eq⟩ := sample r earlier
    rw [eq,facts.tapeAt _ r bytes (drawIndex_spec grinding r) at_]
  have rings : packet.coord ≠ .initial → ringOf Q iv grinding boundary T' H = seed.1 := by
    intro different
    have earlier : position (.initial : Coord p) < position packet.coord := by
      rw [CausalPositions.position_initial]
      exact PCSBCSRestorationHazard.noninitial_positive _ different
    obtain ⟨bytes,at_,eq⟩ := sample .initial earlier
    have seedEq := facts.seedAt _ bytes (drawIndex_spec grinding .initial) at_
    rw [facts.seeded] at seedEq
    unfold ringOf
    rw [eq,Option.some.inj seedEq]
  -- replies
  have answers := facts.parsed _ _ rows j packet.coord H draw history
    (tapeOf Q iv grinding boundary T' H packet.coord) tapes _ nextEq
  -- assembly
  unfold builder
  dsimp only
  rw [← HDef,← T'Def,← shapeDef,recordEq,Option.bind_some,inputEq,Option.bind_some,rootEq,Option.map_some]
  refine congrArg some ?_
  exact literalCallerData_congr _ _ _ _ _ _ _ _ _ rings tapes answers

end Exact

/-! ## Captures of the walk roots and the state path -/

theorem literalRaw_decode (col : Collected p) (seed : RingPCSGame.Prefix × E) (q : Coord p) (bytes : List Byte)
    (seeded : col.seed = some seed)
    (tape : get q col.tape = StackWHIRReplay.projectSample q (decodeSample q bytes))
    (seedq : q = .initial → col.seed = some (decodeSample (.initial : Coord p) bytes)) :
    PCSBCSRestorationHazard.literalRaw seed.1 col.tape q = decodeSample q bytes := by
  cases q with
  | initial =>
    have same := seedq rfl
    rw [seeded] at same
    cases same
    simp only [PCSBCSRestorationHazard.literalRaw]
    rw [tape]
    rfl
  | fold i j => exact tape
  | ood i j => exact tape
  | query i => exact tape
  | tail j => exact tape

theorem ne_initial_of_position (q : Coord p) (moved : position q ≠ 0) : q ≠ .initial := by
  intro same
  rw [same,CausalPositions.position_initial] at moved
  exact moved rfl

section Path
variable (Q : Nat) (iv : Digest32) (grinding : Fin (ParameterBounds.config p).folds.size → Fin 64)
  (boundary headerFrames k : Nat) (instanceBytes : List Byte) (layout : WHIRCallerClaims.CallerLayout)
  (parse : FramedHistory → Tape (ParameterBounds.config p) → (Nat → Oracle) → Array Reply)
  (program : Program (SpongefishCurrentOpeningProgram.FullResult p)) (counted : Counts Q program)

/-- Every walk root below the number of levels is first-mentioned by the packet of the last coordinate, so it has a first-mention capture in the view. -/
theorem captures_exist (T : Table Q iv grinding boundary) (data : SpongefishCurrentMixedModeCompiler.Data)
    (col : Collected p) (r : SpongefishSessionAdapter.Record) (input : PCSBCSCallerBinding.CallerInput p)
    (seed : RingPCSGame.Prefix × E) (histories : List FramedHistory)
    (facts : Facts Q iv grinding boundary headerFrames k instanceBytes layout parse program counted T data col r
      input seed histories) :
    ∃ frozens, SpongefishCurrentIdealRows.Captured grinding (AnchoredSourceCaller.shape layout) headerFrames
      boundary Q iv (viewOf Q iv grinding boundary program counted T) col frozens := by
  classical
  let shape := AnchoredSourceCaller.shape layout
  let source := SpongefishCurrentBCSKnowledge.source (partition p Q iv grinding boundary) iv program counted
  let last := PCSRoundByRoundTranscriptState.lastCoordinate cfg
  obtain ⟨PL,bytesL,coordL,histL,_,_,recordedL⟩ := facts.packets _ last (drawIndex_spec grinding last)
  have lenL := facts.frames _ _ histL
  have visited : (.inl PL : Key p Q iv grinding boundary) ∈
      (Sampling.execute T source).2.map Sigma.fst := List.mem_map.mpr ⟨_,recordedL,rfl⟩
  have exists_ : ∀ ref, ref ∈ SpongefishCurrentRootPolicy.references p grinding shape headerFrames boundary
      PL.history → ∃ f, SpongefishCurrentRootPolicy.publicCapture (B := Q) p grinding shape headerFrames
        boundary iv ref (viewOf Q iv grinding boundary program counted T) = some f := by
    intro ref member
    obtain ⟨before,found⟩ := PCSBCSFirstRootDisclosure.first_mention_exists
      (SpongefishCurrentPartitionCapture.paddr (partition p Q iv grinding boundary)
        (SpongefishCurrentRootPolicy.addresses p grinding shape headerFrames boundary iv)) _ ref
      (mentioned Q iv grinding boundary shape headerFrames PL ref member) source T visited
    rw [← pcapture_public Q iv grinding boundary shape headerFrames program counted T ref]
    exact ⟨_,by unfold SpongefishCurrentPartitionCapture.pcapture; rw [found]; rfl⟩
  have each : ∀ i root, i < (cfg).folds.size → col.roots[i]? = some root →
      ∃ f, SpongefishCurrentRootPolicy.publicCapture (B := Q) p grinding shape headerFrames boundary iv
        (SpongefishCurrentIdealRows.rootReference p shape i root) (viewOf Q iv grinding boundary program counted T) =
          some f := by
    intro i root small rootAt
    cases i with
    | zero =>
      obtain ⟨root0,h0,root0At,h0At,headerLe,header⟩ := facts.anchor
      rw [rootAt] at root0At
      cases root0At
      have h0Eq := facts.nested 0 _ h0 PL.history (Nat.zero_le _) h0At histL
      have headerH : SpongefishCurrentAnchorHeader.fromHistory shape
          {PL.history with frames := PL.history.frames.take headerFrames} = some root := by
        rw [← header,h0Eq]
        simp only [List.take_take]
        rw [Nat.min_eq_left (by omega)]
      exact exists_ _ (SpongefishCurrentRootPolicy.anchor_mem p grinding shape headerFrames boundary
        PL.history root (by omega) headerH)
    | succ i0 =>
      let i' : Fin (cfg).folds.size := ⟨i0,by omega⟩
      have folds0 : 0 < (cfg).folds[i'.val]! := WHIRQueryOracleRecurrence.production_folds_positive p i'
      let kk : Fin (cfg).folds[i'.val]! := ⟨(cfg).folds[i'.val]! - 1,by omega⟩
      have lastK : isLastFold i' kk = true := by
        simp only [isLastFold,decide_eq_true_eq,kk]
        omega
      have drawC := drawIndex_spec grinding (.fold i' kk)
      have earlier : position (.fold i' kk : Coord p) < position last :=
        lt_of_lt_of_le (fold_lt_query i' kk col.tape)
          (PCSRoundByRoundTranscriptState.lastCoordinate_max cfg _)
      have lt := draw_lt grinding _ _ _ last drawC (drawIndex_spec grinding last) earlier
      obtain ⟨root',h,previous,bytes,root'At,hAt,frameAt,parsedRoot⟩ :=
        facts.levelRoots i' kk _ lastK small drawC
      rw [rootAt] at root'At
      cases root'At
      have hEq := facts.nested _ _ h PL.history (by omega) hAt histL
      have frameH : PL.history.frames[boundary + drawIndex grinding (.fold i' kk) + 1]? =
          some (.absorb previous bytes) := by
        rw [hEq] at frameAt
        simp only [List.getElem?_take] at frameAt
        split at frameAt
        · exact frameAt
        · omega
      have member := SpongefishCurrentRootPolicy.level_mem p grinding shape headerFrames boundary PL.history _ i' kk
        drawC lastK small previous bytes frameH root parsedRoot
      obtain ⟨f,found⟩ := exists_ _ member
      refine ⟨f,?_⟩
      unfold SpongefishCurrentIdealRows.rootReference
      rw [ite_eq_right (by omega)]
      exact found
  have nonempty : Nonempty PCSBCSMerkleRootCache.Frozen := by
    obtain ⟨root0,_,root0At,_⟩ := facts.anchor
    obtain ⟨f,_⟩ := each 0 root0 (ParameterBounds.production_config_valid p).2.1 root0At
    exact ⟨f⟩
  refine ⟨fun i => Classical.epsilon fun f => ∀ root, col.roots[i]? = some root →
    SpongefishCurrentRootPolicy.publicCapture (B := Q) p grinding shape headerFrames boundary iv
      (SpongefishCurrentIdealRows.rootReference p shape i root) (viewOf Q iv grinding boundary program counted T) =
        some f,?_⟩
  intro i root small rootAt
  obtain ⟨f,found⟩ := each i root small rootAt
  have spec := Classical.epsilon_spec (p := fun f => ∀ root, col.roots[i]? = some root →
    SpongefishCurrentRootPolicy.publicCapture (B := Q) p grinding shape headerFrames boundary iv
      (SpongefishCurrentIdealRows.rootReference p shape i root) (viewOf Q iv grinding boundary program counted T) =
        some f) ⟨f,fun root' at' => by rw [rootAt] at at'; cases at'; exact found⟩
  exact spec root rootAt

/-- The literal state path on a good table: the packets of all coordinates in schedule order are recorded, each reconstructed node is the literal caller data, neighbouring states are linked by the literal before/after identities, the initial state is undoomed and the terminal state is the literal final state. -/
theorem statePath (T : Table Q iv grinding boundary) (data : SpongefishCurrentMixedModeCompiler.Data)
    (col : Collected p) (r : SpongefishSessionAdapter.Record) (input : PCSBCSCallerBinding.CallerInput p)
    (seed : RingPCSGame.Prefix × E) (histories : List FramedHistory)
    (facts : Facts Q iv grinding boundary headerFrames k instanceBytes layout parse program counted T data col r
      input seed histories)
    (frozens : Nat → PCSBCSMerkleRootCache.Frozen)
    (captured : SpongefishCurrentIdealRows.Captured grinding (AnchoredSourceCaller.shape layout) headerFrames
      boundary Q iv (viewOf Q iv grinding boundary program counted T) col frozens)
    (rows : SpongefishCurrentOpeningExperiment.RowsAuthenticated col.tape col.replies
      (SpongefishCurrentIdealRows.rootOracle (frozens 0)) (SpongefishCurrentIdealRows.nextOracle frozens))
    (terminal : PCSBCSRestorationHazard.literalState p input (SpongefishCurrentIdealRows.rootOracle (frozens 0))
      seed.1 col.tape (SpongefishCurrentOpeningExperiment.restoredReplies col
        (SpongefishCurrentIdealRows.nextOracle frozens)) (PCSRoundByRoundTranscriptState.lastCoordinate cfg) = true) :
    PCSStateRestoration.Latent.StatePath
      (model p Q iv grinding boundary (builder Q iv grinding boundary headerFrames k instanceBytes layout parse
        (SpongefishCurrentBCSKnowledge.source (partition p Q iv grinding boundary) iv program counted)))
      T (Sampling.execute T (SpongefishCurrentBCSKnowledge.source (partition p Q iv grinding boundary) iv
        program counted)).2 false true := by
  classical
  let build := builder Q iv grinding boundary headerFrames k instanceBytes layout parse
    (SpongefishCurrentBCSKnowledge.source (partition p Q iv grinding boundary) iv program counted)
  let root := SpongefishCurrentIdealRows.rootOracle (frozens 0)
  let replies := SpongefishCurrentOpeningExperiment.restoredReplies col (SpongefishCurrentIdealRows.nextOracle frozens)
  have choose : ∀ q : Coord p, ∃ P : Packet p Q grinding boundary, P.coord = q ∧
      (openingDraws grinding)[drawIndex grinding q]? = some (some P.coord) ∧
      histories[drawIndex grinding q]? = some P.history ∧
      (⟨.inl P,T (.inl P)⟩ : Sigma (Answer p Q iv grinding boundary)) ∈
        (Sampling.execute T (SpongefishCurrentBCSKnowledge.source (partition p Q iv grinding boundary) iv
          program counted)).2 ∧
      grouped P.coord (T (.inl P)) = PCSBCSRestorationHazard.literalRaw seed.1 col.tape P.coord := by
    intro q
    have drawQ := drawIndex_spec grinding q
    obtain ⟨P,bytes,coordEq,hist,bytesAt,decoded,recorded⟩ := facts.packets _ q drawQ
    subst coordEq
    refine ⟨P,rfl,drawQ,hist,recorded,?_⟩
    rw [← decoded]
    exact (literalRaw_decode col seed P.coord bytes facts.seeded (facts.tapeAt _ _ bytes drawQ bytesAt)
      (fun initial => facts.seedAt _ bytes (initial ▸ drawQ) bytesAt)).symm
  let pk : Coord p → Packet p Q grinding boundary := fun q => Classical.choose (choose q)
  have pkSpec := fun q => Classical.choose_spec (choose q)
  have assembled : ∀ q, build (pk q) (PCSStateRestoration.Latent.erase (.inl (pk q)) T) =
      some (PCSBCSRestorationHazard.literalCallerData p input root seed.1 col.tape replies q) := by
    intro q
    obtain ⟨coordEq,drawQ,hist,_,_⟩ := pkSpec q
    have exact := builder_exact Q iv grinding boundary headerFrames k instanceBytes layout parse program counted
      T data col r input seed histories facts frozens captured rows _ (pk q) drawQ hist
    rw [coordEq] at exact
    exact exact
  have afterEq : ∀ q, PCSStateRestoration.Latent.after (model p Q iv grinding boundary build) (.inl (pk q)) T =
      PCSBCSRestorationHazard.literalState p input root seed.1 col.tape replies q := by
    intro q
    obtain ⟨coordEq,_,_,_,raw⟩ := pkSpec q
    change (match build (pk q) (PCSStateRestoration.Latent.erase (.inl (pk q)) T) with
      | some caller => (callerCertificate p).after caller (pk q).coord (grouped (pk q).coord (T (.inl (pk q))))
      | none => false) = _
    rw [assembled q,raw,coordEq]
    exact PCSBCSRestorationHazard.literal_after p input root seed.1 col.tape replies q
  have beforeEq : ∀ q (different : q ≠ .initial),
      PCSStateRestoration.Latent.before (model p Q iv grinding boundary build) (.inl (pk q)) T =
        PCSBCSRestorationHazard.literalState p input root seed.1 col.tape replies
          (PCSRoundByRoundTranscriptState.predecessor q (PCSBCSRestorationHazard.noninitial_positive q different)) := by
    intro q different
    obtain ⟨coordEq,_,_,_,_⟩ := pkSpec q
    have recovered : PCSStateRestoration.Latent.publicNode (model p Q iv grinding boundary build) (.inl (pk q)) T =
        some (PCSBCSRestorationHazard.literalCallerData p input root seed.1 col.tape replies q) := assembled q
    unfold PCSStateRestoration.Latent.before
    rw [recovered]
    change (callerCertificate p).before (PCSBCSRestorationHazard.literalCallerData p input root seed.1 col.tape
      replies q) (pk q).coord = _
    rw [coordEq]
    exact PCSBCSRestorationHazard.literal_before p input root seed.1 col.tape replies q different
  have initialEq : PCSStateRestoration.Latent.before (model p Q iv grinding boundary build)
      (.inl (pk .initial)) T = false := by
    obtain ⟨coordEq,_,_,_,_⟩ := pkSpec .initial
    have recovered : PCSStateRestoration.Latent.publicNode (model p Q iv grinding boundary build)
        (.inl (pk .initial)) T =
        some (PCSBCSRestorationHazard.literalCallerData p input root seed.1 col.tape replies .initial) :=
      assembled .initial
    unfold PCSStateRestoration.Latent.before
    rw [recovered]
    change (callerCertificate p).before (PCSBCSRestorationHazard.literalCallerData p input root seed.1 col.tape
      replies .initial) (pk .initial).coord = false
    rw [coordEq]
    rfl
  apply PCSBCSLiteralStatePath.of_round_links _ T _
    ((WHIRHistory.schedule cfg).map fun q => (.inl (pk q) : Key p Q iv grinding boundary)) false true
  · intro key member
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp member
    exact (pkSpec q).2.2.2.1
  · intro i hi
    have bound : i + 1 < (WHIRHistory.schedule cfg).length := by simpa only [List.length_map] using hi
    simp only [List.getElem_map]
    have positionI : position ((WHIRHistory.schedule cfg)[i]'(by omega)) = i :=
      WHIRHistory.position_schedule_get cfg ⟨i,by unfold WHIRHistory.depth; omega⟩
    have positionJ : position ((WHIRHistory.schedule cfg)[i+1]'bound) = i + 1 :=
      WHIRHistory.position_schedule_get cfg ⟨i+1,by unfold WHIRHistory.depth; omega⟩
    have different := ne_initial_of_position _ (by rw [positionJ]; omega)
    have predEq : PCSRoundByRoundTranscriptState.predecessor ((WHIRHistory.schedule cfg)[i+1]'(by omega))
        (PCSBCSRestorationHazard.noninitial_positive _ different) = (WHIRHistory.schedule cfg)[i]'(by omega) := by
      apply CausalPrefix.position_injective
      rw [PCSRoundByRoundTranscriptState.predecessor_position,positionI,positionJ]
      rfl
    rw [afterEq,beforeEq _ different,predEq]
  · intro key head
    have first : (WHIRHistory.schedule cfg).head? = some .initial := by
      have at0 := WHIRHistory.schedule_get_position (.initial : Coord p)
      rw [CausalPositions.position_initial] at at0
      simpa only [List.head?_eq_getElem?] using at0
    simp only [List.head?_map,first,Option.map_some,Option.some.injEq] at head
    rw [← head]
    exact initialEq
  · intro key final
    rw [List.getLast?_map] at final
    obtain ⟨q,atLast,rfl⟩ := Option.map_eq_some_iff.mp final
    have isLast : q = PCSRoundByRoundTranscriptState.lastCoordinate cfg := by
      apply CausalPrefix.position_injective
      rw [PCSBCSCapturedSourceStatePath.lastCoordinate_position]
      rw [List.getLast?_eq_getElem?] at atLast
      obtain ⟨inside,stored⟩ := List.getElem?_eq_some_iff.mp atLast
      rw [← stored]
      exact WHIRHistory.position_schedule_get cfg ⟨WHIRHistory.depth cfg - 1,inside⟩
    rw [afterEq,isLast]
    exact terminal
  · intro empty
    have member := WHIRHistory.coordinate_mem_schedule (.initial : Coord p)
    rw [List.map_eq_nil_iff.mp empty] at member
    cases member

end Path

/-! ## Refinement -/

section Refines
variable (Q : Nat) (iv : Digest32) (grinding : Fin (ParameterBounds.config p).folds.size → Fin 64)
  (boundary headerFrames k : Nat) (instanceBytes : List Byte) (layout : WHIRCallerClaims.CallerLayout)

/-- `Refines` for the public good event, for any counted program and reply parser, from the good-table facts and, for every family of root captures, row authentication and the literal terminal state. -/
theorem refines_of_facts
    (parse : FramedHistory → Tape (ParameterBounds.config p) → (Nat → Oracle) → Array Reply)
    (program : Program (SpongefishCurrentOpeningProgram.FullResult p)) (counted : Counts Q program)
    (facts : ∀ T : Table Q iv grinding boundary,
      SpongefishCurrentGoodEvent.GoodFull Q iv instanceBytes layout grinding headerFrames boundary k
        (viewOf Q iv grinding boundary program counted T) →
      ∃ (data : SpongefishCurrentMixedModeCompiler.Data) (col : Collected p) (r : SpongefishSessionAdapter.Record)
        (input : PCSBCSCallerBinding.CallerInput p) (seed : RingPCSGame.Prefix × E) (histories : List FramedHistory),
        Facts Q iv grinding boundary headerFrames k instanceBytes layout parse program counted T data col r input
          seed histories ∧
        ∀ frozens : Nat → PCSBCSMerkleRootCache.Frozen,
          SpongefishCurrentIdealRows.Captured grinding (AnchoredSourceCaller.shape layout) headerFrames boundary Q
            iv (viewOf Q iv grinding boundary program counted T) col frozens →
          SpongefishCurrentOpeningExperiment.RowsAuthenticated col.tape col.replies
            (SpongefishCurrentIdealRows.rootOracle (frozens 0)) (SpongefishCurrentIdealRows.nextOracle frozens) ∧
          PCSBCSRestorationHazard.literalState p input (SpongefishCurrentIdealRows.rootOracle (frozens 0)) seed.1
            col.tape (SpongefishCurrentOpeningExperiment.restoredReplies col
              (SpongefishCurrentIdealRows.nextOracle frozens)) (PCSRoundByRoundTranscriptState.lastCoordinate cfg) =
            true) :
    SpongefishCurrentBCSKnowledge.Refines (partition p Q iv grinding boundary)
      (model p Q iv grinding boundary (builder Q iv grinding boundary headerFrames k instanceBytes layout parse
        (SpongefishCurrentBCSKnowledge.source (partition p Q iv grinding boundary) iv program counted)))
      iv program counted (SpongefishCurrentGoodEvent.goodFull Q iv instanceBytes layout grinding headerFrames
        boundary k) := by
  intro T good
  simp only [SpongefishCurrentGoodEvent.goodFull,decide_eq_true_eq] at good
  obtain ⟨data,col,r,input,seed,histories,facts,extra⟩ := facts T good
  obtain ⟨frozens,captured⟩ := captures_exist Q iv grinding boundary headerFrames k instanceBytes layout parse
    program counted T data col r input seed histories facts
  obtain ⟨rows,terminal⟩ := extra frozens captured
  exact statePath Q iv grinding boundary headerFrames k instanceBytes layout parse program counted T data col r
    input seed histories facts frozens captured rows terminal

/-- The opening phase returns the source result unchanged as its first component. -/
theorem phase_first {Q' : Nat} {Seed State : Type} (sim : Simulator Q' Seed State) (ro : RawKey Q' → Digest32)
    (iv : Digest32) (state : State) (decode : SpongefishCurrentOpeningProgram.Decoder) (lanes index offset : Nat)
    (res : SpongefishCurrentSourceJoinProbability.SourceResult) (rest : Nat) (cap : rest ≤ Q')
    (counted : Counts rest (SpongefishCurrentOpeningProgram.openingPhase (p := p) decode grinding lanes index
      offset res)) :
    (runIdeal sim ro iv state (SpongefishCurrentOpeningProgram.openingPhase (p := p) decode grinding lanes index
      offset res) rest cap counted).view.result.1 = res := by
  revert counted
  rcases res with _ | (e | data)
  · intro counted
    rfl
  · intro counted
    rfl
  · dsimp only [SpongefishCurrentOpeningProgram.openingPhase]
    split
    · intro counted
      rfl
    · intro counted
      obtain ⟨_,_,_,_,same⟩ := SpongefishCurrentOpeningPackets.ideal_bind sim ro iv _ _ state rest cap counted
      rw [same]
      rfl

open SpongefishCurrentOpeningProgram in
/-- `Refines` of the current round node model for the full source program, with the history reply parser. The remaining hypotheses are static (`supported`, the opening frame shape `opening` and `headerLe`) and the two header glue facts: on every successful view the opening events of the walk are the opening-call events, and, for the public caller candidate of the good event, the commitment header frame of the post-binding history carries the walk's header root. -/
theorem refines_full
    (supported : SpongefishCurrentAnchorAttackerPrefix.Supported p (AnchoredSourceCaller.shape layout))
    (tag : List Byte) (before payloadCalls messages : List SpongefishPCSRoundFrames.Call) (decode : Decoder)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input)
    (counted : Counts Q (fullProgram iv tag instanceBytes layout before payloadCalls messages decode grinding
      prefixProgram))
    (opening : SpongefishCurrentOpeningPackets.openingShape instanceBytes (before ++
      SpongefishCurrentAcceptedJoin.headerCalls (AnchoredSourceCaller.shape layout).logN ++ payloadCalls ++
        messages) = (boundary,true))
    (headerLe : headerFrames ≤ boundary + 1)
    (events : ∀ (T : Table Q iv grinding boundary) (data : SpongefishCurrentMixedModeCompiler.Data)
      (col : Collected p),
      (viewOf Q iv grinding boundary (fullProgram iv tag instanceBytes layout before payloadCalls messages decode
        grinding prefixProgram) counted T).result = (some (.ok data),some col) →
      openingEvents (openingOffset layout before payloadCalls messages) data =
        SpongefishCurrentOpeningPackets.openingEvents grinding data.events)
    (header : ∀ (T : Table Q iv grinding boundary) (data : SpongefishCurrentMixedModeCompiler.Data)
      (col : Collected p),
      (viewOf Q iv grinding boundary (fullProgram iv tag instanceBytes layout before payloadCalls messages decode
        grinding prefixProgram) counted T).result = (some (.ok data),some col) →
      ∀ (r : SpongefishSessionAdapter.Record) (input : PCSBCSCallerBinding.CallerInput p),
      SpongefishCurrentSourceCallerOriginal.candidate (Q := Q) p layout
        (SpongefishCurrentGoodEvent.postBinding boundary data) r instanceBytes
        (viewOf Q iv grinding boundary (fullProgram iv tag instanceBytes layout before payloadCalls messages decode
          grinding prefixProgram) counted T).observations = some input →
      ∀ root0, headerRoot (rootIndex before) data.events = some root0 →
        SpongefishCurrentAnchorHeader.fromHistory (AnchoredSourceCaller.shape layout)
          {(SpongefishCurrentGoodEvent.postBinding boundary data).history with
            frames := (SpongefishCurrentGoodEvent.postBinding boundary data).history.frames.take headerFrames} =
          some root0) :
    SpongefishCurrentBCSKnowledge.Refines (partition p Q iv grinding boundary)
      (model p Q iv grinding boundary (builder Q iv grinding boundary headerFrames k instanceBytes layout
        (SpongefishCurrentHistoryReplies.historyReplies grinding boundary)
        (SpongefishCurrentBCSKnowledge.source (partition p Q iv grinding boundary) iv
          (fullProgram iv tag instanceBytes layout before payloadCalls messages decode grinding prefixProgram)
          counted)))
      iv (fullProgram iv tag instanceBytes layout before payloadCalls messages decode grinding prefixProgram) counted
      (SpongefishCurrentGoodEvent.goodFull Q iv instanceBytes layout grinding headerFrames boundary k) := by
  apply refines_of_facts
  intro T good
  have goodCopy := good
  obtain ⟨data,col,r,input,result,record,original,verdict,fails,_,quiet⟩ := goodCopy
  have verdictCopy := verdict
  obtain ⟨seed,_,seeded,_,_⟩ := verdictCopy
  -- the initialized part succeeded
  have success : (Sampling.eval T (SpongefishCurrentBCSKnowledge.source (partition p Q iv grinding boundary) iv
      (SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram
        ((before ++ SpongefishCurrentAcceptedJoin.headerCalls (AnchoredSourceCaller.shape layout).logN ++
          payloadCalls ++ messages) ++ openingCalls grinding))
      (WHIRModeFinal.bind_prefix_counted _ _ Q counted))).result = some (.ok data) := by
    obtain ⟨state,rest,cap,counted',same⟩ := SpongefishCurrentOpeningPackets.source_bind
      (partition p Q iv grinding boundary) iv
      (SpongefishCurrentSourceJoinProbability.program iv tag instanceBytes layout before payloadCalls messages
        grinding prefixProgram)
      (openingPhase decode grinding (AnchoredSourceCaller.shape layout).lanes (rootIndex before)
        (openingOffset layout before payloadCalls messages)) counted T
    have first := congrArg (fun v => v.result.1) same
    simp only [phase_first] at first
    have firstResult := congrArg Prod.fst result
    exact first.symm.trans firstResult
  obtain ⟨histories,length,frames,nested,_,_,packets,calls,_,framesAt,content,postHistory⟩ :=
    SpongefishCurrentHistoryReplies.opening_frames Q iv grinding boundary tag instanceBytes _ prefixProgram _
      counted opening T data success
  obtain ⟨root0,headerAt,walked,_⟩ := SpongefishCurrentIdealRows.ideal_walk (partition p Q iv grinding boundary)
    iv tag instanceBytes layout before payloadCalls messages decode grinding prefixProgram counted T data col result
  rw [events T data col result] at walked
  have rootAt := SpongefishCurrentHistoryReplies.root_start _ decode grinding _ root0 _ col calls walked
  refine ⟨data,col,r,input,seed,histories,⟨record,original,seeded,postHistory,frames,nested,packets,
    fun j q bytes found drawn => SpongefishCurrentHistoryReplies.tape_draw _ decode grinding _ root0 _ col calls
      walked j q bytes found drawn,
    fun j bytes found drawn => SpongefishCurrentHistoryReplies.seed_draw _ decode grinding _ root0 _ col calls
      walked j bytes found drawn,?_,
    fun i' kk j' last more found => SpongefishCurrentHistoryReplies.level_roots_of_frames _ decode grinding _ root0 _
      col calls walked boundary histories length content i' kk j' last more found,
    fun root next rows j q h found hAt t agree next' levels =>
      SpongefishCurrentHistoryReplies.replies_exact_local _ decode grinding _ root0 _ col calls walked j q found
        boundary h (framesAt j h hAt).1 root next rows t agree next' levels⟩,
    fun frozens captured => ⟨SpongefishCurrentIdealRows.ideal_rows (partition p Q iv grinding boundary) iv tag
        instanceBytes layout before payloadCalls messages decode grinding prefixProgram counted T headerFrames
        boundary supported data col result quiet frozens captured,
      SpongefishCurrentIdealRows.ideal_terminal (partition p Q iv grinding boundary) iv tag instanceBytes layout
        before payloadCalls messages decode grinding prefixProgram counted T headerFrames boundary supported data
        col result r input original verdict fails quiet frozens captured seed seeded⟩⟩
  obtain ⟨h0,h0At⟩ : ∃ h0, histories[0]? = some h0 := by
    obtain ⟨j,found⟩ := SpongefishCurrentOpeningPackets.openingDraws_complete grinding (.initial : Coord p)
      (WHIRHistory.coordinate_mem_schedule _) (width_ne _)
    have inside := (List.getElem?_eq_some_iff.mp found).1
    exact ⟨_,List.getElem?_eq_getElem (by omega)⟩
  refine ⟨root0,h0,rootAt,h0At,headerLe,?_⟩
  have fromHeader := header T data col result r input original root0 headerAt
  rw [postHistory h0 h0At] at fromHeader
  exact fromHeader

end Refines

#print axioms widths_deployed
#print axioms draw_lt
#print axioms level_before
#print axioms input_exact
#print axioms builder_exact
#print axioms captures_exist
#print axioms statePath
#print axioms refines_of_facts
#print axioms refines_full

end Whir.SpongefishCurrentRefines
