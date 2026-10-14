import Whir.SpongefishCurrentOpeningProgram
import Whir.SpongefishCurrentRootPolicy
import Whir.SpongefishCurrentCallerOriginalTable

/-! Public events of the current #607 knowledge endpoint, read from the whole view of the full source program (`SpongefishCurrentOpeningProgram.fullProgram`). The public extractor freezes Root0 at the first key whose history mentions it (`SpongefishCurrentRootPolicy.publicCapture`) and runs the straight-line source extractor on the frozen image. The good event joins the accepted replay and opening walk, the caller original reconstructed publicly at the post-binding coordinate, the native opening equations, extraction failure, absence of ordinary output collisions and Merkle quietness of every query opening against the frozen first-mention log of its root. No hidden primitive or coin is read. -/
namespace Whir.SpongefishCurrentGoodEvent
open Concrete Protocol CausalGame FiatShamirGame DuplexModeGame DuplexFraming SpongefishPCSRoundFrames
open PCSBCSSourceRootReferences SpongefishCurrentOpeningAcceptance SpongefishCurrentOpeningProgram
set_option autoImplicit false

variable {p : ParameterBounds.Profile}
local notation "cfg" => ParameterBounds.config p

/-- Merkle reference of a query opening: Root0 at level 0 and the announced level root otherwise. -/
def openingReference (shape : SpongefishSessionAdapter.Shape) (o : QueryOpening p) : Reference :=
  if o.level.val = 0 then SpongefishCurrentPhysicalRootCapture.reference shape o.root
  else ⟨o.root,SpongefishCurrentRootPolicy.levelShape p o.level.val⟩

/-- Every query opening of the returned walk is clean against the frozen first-mention log of its root, judged with the public seed of the view. -/
def Quiet (grinding : Fin (cfg).folds.size → Fin 64) (shape : SpongefishSessionAdapter.Shape)
    (headerFrames boundary B : Nat) (iv : Digest32) (view : View (FullResult p)) : Prop :=
  ∀ col, view.result.2 = some col → ∀ o ∈ col.openings, ∀ frozen,
    SpongefishCurrentRootPolicy.publicCapture (B := B) p grinding shape headerFrames boundary iv
      (openingReference shape o) view = some frozen →
    ¬ PublicMerkleBinding.OpenPrimitiveBad (PCSBCSPublicPrimitiveOpening.publicSeed view)
      frozen.queryPrefix o.root o.opened.paths

/-- The commitment root returned by the opening walk. -/
def publicRoot0 (view : View (FullResult p)) : Option Digest32 :=
  view.result.2.bind fun col => col.roots[0]?

/-- The public straight-line extractor does not return a witness explaining the original claims on the frozen Root0 image. -/
def ExtractionFails (grinding : Fin (cfg).folds.size → Fin 64) (shape : SpongefishSessionAdapter.Shape)
    (headerFrames boundary B : Nat) (iv : Digest32) (input : PCSBCSCallerBinding.CallerInput p)
    (view : View (FullResult p)) : Prop :=
  ¬ ∃ root frozen w, publicRoot0 view = some root ∧
    SpongefishCurrentRootPolicy.publicCapture (B := B) p grinding shape headerFrames boundary iv
      (SpongefishCurrentPhysicalRootCapture.reference shape root) view = some frozen ∧
    PCSRoundByRoundKnowledge.extract p input.lanes input.family input.points input.anchorPoint
      input.anchorValue frozen.raw = some w ∧
    PCSRewindSource.ExplainsOriginal cfg input.lanes frozen.raw input.family input.points
      input.anchorPoint input.anchorValue w

/-- Post-binding coordinate of a successful replay: the first `boundary + 1` closed frames, block 0. -/
def postBinding (boundary : Nat) (data : SpongefishCurrentMixedModeCompiler.Data) : Coordinate :=
  let h := (close data.pending).core.history
  ⟨{h with frames := h.frames.take (boundary+1)},.output 0⟩

/-- The native opening equations on the returned walk. -/
def Verdict (r : SpongefishSessionAdapter.Record) (input : PCSBCSCallerBinding.CallerInput p)
    (col : Collected p) : Prop :=
  ∃ (seed : RingPCSGame.Prefix × E) (proof : Opening), col.seed = some seed ∧
    CausalGame.opening cfg (challenges cfg col.tape) col.replies = .ok proof ∧
    anchoredVerify r input.family input.points seed.1 seed.2 cfg (challenges cfg col.tape) proof = .ok ()

/-- The public good event for the binding message shape with `k` pending packs. -/
def GoodFull (Q : Nat) (iv : Digest32) (instanceBytes : List Byte)
    (layout : WHIRCallerClaims.CallerLayout) (grinding : Fin (cfg).folds.size → Fin 64)
    (headerFrames boundary k : Nat) (view : View (FullResult p)) : Prop :=
  ∃ (data : SpongefishCurrentMixedModeCompiler.Data) (col : Collected p)
    (r : SpongefishSessionAdapter.Record) (input : PCSBCSCallerBinding.CallerInput p),
    view.result = (some (.ok data),some col) ∧
    (∃ work : pathCost (postBinding boundary data) ≤ Q,
      SpongefishCurrentCallerOriginalTable.recordOf (AnchoredSourceCaller.shape layout) iv k
        (constructionKey Q iv (postBinding boundary data) work) = some r) ∧
    SpongefishCurrentSourceCallerOriginal.candidate (Q := Q) p layout (postBinding boundary data) r
      instanceBytes view.observations = some input ∧
    Verdict r input col ∧
    ExtractionFails grinding (AnchoredSourceCaller.shape layout) headerFrames boundary Q iv input view ∧
    ¬ PublicMerkleLog.OutputCollision (PCSBCSPublicPrimitiveOpening.publicOrdinaryLog Q iv view) ∧
    Quiet grinding (AnchoredSourceCaller.shape layout) headerFrames boundary Q iv view

open Classical in
noncomputable def goodFull (Q : Nat) (iv : Digest32) (instanceBytes : List Byte)
    (layout : WHIRCallerClaims.CallerLayout) (grinding : Fin (cfg).folds.size → Fin 64)
    (headerFrames boundary k : Nat) (view : View (FullResult p)) : Bool :=
  decide (GoodFull Q iv instanceBytes layout grinding headerFrames boundary k view)

end Whir.SpongefishCurrentGoodEvent
