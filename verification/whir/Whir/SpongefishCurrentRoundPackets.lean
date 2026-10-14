import Whir.SpongefishCurrentOpeningAcceptance
import Whir.PCSBCSChallengeOracleRestoration

/-! Current #607 PCS round packets in the basic full-prefix form. A current
construction key carries the session domain, the zero statement seed and the
complete absorbed prover prefix (`SpongefishCurrentAbsorbedPrefix`), not earlier
coin values. A packet is one closed key history together with the opening
coordinate it draws, selected by a fixed public classifier from the number of
absorbed frames after the caller boundary. Its blocks are the 32-byte output
blocks of that history; the grouped E decoder is the same as for the historical
packets. Every other raw key stays in the garbage summand.

The node model reads its caller data through an arbitrary builder of the
erased table and applies the additive source RBR certificate. Its conditional
hazard is the proved `rbrError` for EVERY builder; connecting a builder to
accepted current executions is a separate refinement obligation. -/
namespace Whir.SpongefishCurrentRoundPackets
open Concrete FiatShamirGame DuplexModeGame DuplexFraming RawOracleCoupling
open PCSBCSChallengeOracle PCSBCSCallerBinding SpongefishCurrentOpeningAcceptance
set_option autoImplicit false
set_option maxRecDepth 100000

variable {p : ParameterBounds.Profile}
local notation "cfg" => ParameterBounds.config p

/-- The verifier draws after expected-record binding, in order. A positive
query proof of work is a draw but not a PCS round (`none`); a zero-dimensional
OOD point issues no draw. -/
def openingDraws (grinding : Fin (cfg).folds.size → Fin 64) : List (Option (Coord p)) :=
  (WHIRHistory.schedule cfg).flatMap fun q =>
    (match q with
      | .query i => if (grinding i).val = 0 then [] else [none]
      | _ => []) ++
    (if PCSBCSRounds.rawWidth q = 0 then [] else [some q])

/-- Fixed public classifier: a closed history with `boundary + k + 1` frames is
the `k`-th opening draw. -/
def classify (grinding : Fin (cfg).folds.size → Fin 64) (boundary : Nat) (h : FramedHistory) :
    Option (Coord p) :=
  if boundary < h.frames.length then
    ((openingDraws grinding)[h.frames.length - boundary - 1]?).bind id
  else none

theorem openingDraws_width (grinding : Fin (cfg).folds.size → Fin 64) (q : Coord p)
    (member : some q ∈ openingDraws grinding) : PCSBCSRounds.rawWidth q ≠ 0 := by
  obtain ⟨r,_,member⟩ := List.mem_flatMap.mp member
  rcases List.mem_append.mp member with pow | draw
  · cases r <;> simp_all
  · by_cases zero : PCSBCSRounds.rawWidth r = 0
    · simp [zero] at draw
    · simp only [zero,↓reduceIte,List.mem_singleton,Option.some.injEq] at draw
      subst draw
      exact zero

theorem classify_width (grinding : Fin (cfg).folds.size → Fin 64) (boundary : Nat)
    (h : FramedHistory) (q : Coord p) (classified : classify grinding boundary h = some q) :
    PCSBCSRounds.rawWidth q ≠ 0 := by
  unfold classify at classified
  split at classified
  · obtain ⟨draw,found,same⟩ := Option.bind_eq_some_iff.mp classified
    cases same
    exact openingDraws_width grinding q (List.mem_of_getElem? found)
  · cases classified

theorem blocks_positive (q : Coord p) (width : PCSBCSRounds.rawWidth q ≠ 0) :
    0 < blocks (PCSBCSRounds.rawWidth q) := by
  unfold blocks
  omega

/-- One current round packet: a closed key history and its classified coordinate. -/
structure Packet (p : ParameterBounds.Profile) (Q : Nat)
    (grinding : Fin (ParameterBounds.config p).folds.size → Fin 64) (boundary : Nat) where
  history : FramedHistory
  coord : Coord p
  classified : classify grinding boundary history = some coord
  admissible : ∀ b : Fin (blocks (PCSBCSRounds.rawWidth coord)),
    DuplexEncoding.Admissible ⟨history,.output b.val⟩
  bounded : ∀ b : Fin (blocks (PCSBCSRounds.rawWidth coord)), pathCost ⟨history,.output b.val⟩ ≤ Q

section PacketKeys
variable {Q : Nat} {grinding : Fin (ParameterBounds.config p).folds.size → Fin 64} {boundary : Nat}

abbrev PacketBlock (packet : Packet p Q grinding boundary) := Fin (blocks (PCSBCSRounds.rawWidth packet.coord))

def packetKey (iv : Digest32) (packet : Packet p Q grinding boundary) (b : PacketBlock packet) : RawKey Q :=
  constructionKey Q iv ⟨packet.history,.output b.val⟩ (packet.bounded b)

def firstBlock (packet : Packet p Q grinding boundary) : PacketBlock packet :=
  ⟨0,blocks_positive packet.coord (classify_width grinding boundary _ _ packet.classified)⟩

theorem packet_ext_history (a b : Packet p Q grinding boundary) (same : a.history = b.history) : a = b := by
  cases a with
  | mk ha ca cla ada ba =>
    cases b with
    | mk hb cb clb adb bb =>
      dsimp only at same
      subst same
      have coords : ca = cb := Option.some.inj (cla.symm.trans clb)
      subst coords
      rfl

theorem key_coordinates (iv : Digest32) (a b : Packet p Q grinding boundary) (ia : PacketBlock a)
    (ib : PacketBlock b) (same : packetKey iv a ia = packetKey iv b ib) : a.history = b.history ∧ ia.val = ib.val := by
  have coordinates := constructionKey_injective Q iv (a.admissible ia) (b.admissible ib)
    (a.bounded ia) (b.bounded ib) same
  have history := congrArg FiatShamirGame.Coordinate.history coordinates
  have terminal := congrArg FiatShamirGame.Coordinate.terminal coordinates
  dsimp only at history terminal
  exact ⟨history,by simpa using terminal⟩

def blockKey (iv : Digest32) (block : Sigma (PacketBlock (p := p) (Q := Q) (grinding := grinding)
    (boundary := boundary))) : PublicCompressionCouplingMixed.Key Q :=
  .inr (packetKey iv block.1 block.2)

theorem blockKey_injective (iv : Digest32) :
    Function.Injective (blockKey (p := p) (Q := Q) (grinding := grinding) (boundary := boundary) iv) := by
  intro a b same
  rcases a with ⟨a,ia⟩
  rcases b with ⟨b,ib⟩
  obtain ⟨history,index⟩ := key_coordinates iv a b ia ib (Sum.inr.inj same)
  have packets := packet_ext_history a b history
  subst packets
  have blocksSame : ia = ib := Fin.ext index
  subst blocksSame
  rfl

theorem firstKey_injective (iv : Digest32) :
    Function.Injective (fun packet : Packet p Q grinding boundary => packetKey iv packet (firstBlock packet)) := by
  intro a b same
  exact packet_ext_history a b (key_coordinates iv a b _ _ same).1

noncomputable instance : Fintype (Packet p Q grinding boundary) := by
  classical
  letI := rawKeyFintype Q
  exact Fintype.ofInjective _ (firstKey_injective (p := p) (Q := Q) (grinding := grinding)
    (boundary := boundary) (fun _ => 0))

end PacketKeys

variable (p : ParameterBounds.Profile) (Q : Nat) (iv : Digest32)
  (grinding : Fin (ParameterBounds.config p).folds.size → Fin 64) (boundary : Nat)

/-- Raw source keys: current round packet blocks, every other key garbage. -/
noncomputable def partition :
    Partition (PublicCompressionCouplingMixed.Key Q) (Packet p Q grinding boundary) PacketBlock :=
  partitionOfInjection (blockKey iv) (blockKey_injective iv)

abbrev Key := (partition p Q iv grinding boundary).Key
abbrev Answer := (partition p Q iv grinding boundary).Answer (D := Digest32)

noncomputable local instance (key : Key p Q iv grinding boundary) :
    Fintype (Answer p Q iv grinding boundary key) :=
  match key with
  | .inl _ => inferInstance
  | .inr _ => inferInstance

/-- Caller data reconstructed from the table with the selected packet erased. -/
abbrev Builder := (packet : Packet p Q grinding boundary) →
  PCSStateRestoration.Latent.Erased (Answer p Q iv grinding boundary) (.inl packet) →
    Option (CallerData p)

/-- Additive RBR node model on the current round packets. -/
noncomputable def model (build : Builder p Q iv grinding boundary) :
    PCSStateRestoration.Latent.NodeModel (Key p Q iv grinding boundary)
      (Answer p Q iv grinding boundary) (Option (CallerData p)) where
  reconstruct key other := match key with
    | .inl packet => build packet other
    | .inr _ => none
  before data key := match key, data with
    | .inl packet, some caller => (callerCertificate p).before caller packet.coord
    | _, _ => false
  after data key answer := match key with
    | .inl packet => match data with
      | some caller => (callerCertificate p).after caller packet.coord (grouped packet.coord answer)
      | none => false
    | .inr _ => false

/-- The current whole output blocks of one packet induce exactly the checked
RBR alphabet; the incoming state is fixed before every bit of the packet. -/
theorem packet_fiber (caller : CallerData p) (packet : Packet p Q grinding boundary)
    (undoomed : (callerCertificate p).before caller packet.coord = false) :
    Soundness.uniformProb (Finset.univ.filter fun full :
      Fin (blocks (PCSBCSRounds.rawWidth packet.coord)) → Digest32 =>
      (callerCertificate p).after caller packet.coord (grouped packet.coord full) = true) ≤
        PCSRoundByRoundKnowledge.rbrError := by
  classical
  have law := grouped_uniform packet.coord (fun answer =>
    (callerCertificate p).after caller packet.coord answer = true)
  rw [SamplingProbability.probability_eq_uniformProb,
    SamplingProbability.probability_eq_uniformProb] at law
  have exactLaw := (Rat.cast_inj (α := ℝ)).mp law
  exact exactLaw.trans_le (caller_fiber p caller packet.coord undoomed)

/-- Proved conditional hazard on the current packets, for every builder. -/
theorem conditional_hazard (build : Builder p Q iv grinding boundary) :
    PCSStateRestoration.Latent.ConditionalHazard (model p Q iv grinding boundary build)
      PCSRoundByRoundKnowledge.rbrError := by
  classical
  intro key other undoomed
  cases key with
  | inl packet =>
    cases recovered : build packet other with
    | none =>
      simp only [model,recovered,Bool.false_eq_true,Finset.filter_false,
        Soundness.uniformProb,Finset.card_empty,Nat.cast_zero,zero_div]
      unfold PCSRoundByRoundKnowledge.rbrError SupportedCandidateExtraction.radiusEnvelope
      positivity
    | some caller =>
      simp only [model,recovered] at undoomed
      have bound := packet_fiber p Q grinding boundary caller packet undoomed
      unfold Soundness.uniformProb at bound ⊢
      simp only [model,recovered,Fintype.card_eq_nat_card] at bound ⊢
      exact bound
  | inr garbage =>
    simp only [model,Bool.false_eq_true,Finset.filter_false,Soundness.uniformProb,
      Finset.card_empty,Nat.cast_zero,zero_div]
    unfold PCSRoundByRoundKnowledge.rbrError SupportedCandidateExtraction.radiusEnvelope
    positivity

#print axioms blockKey_injective
#print axioms packet_fiber
#print axioms conditional_hazard

end Whir.SpongefishCurrentRoundPackets
