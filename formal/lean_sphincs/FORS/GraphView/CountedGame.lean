module

public import FORS.GraphView.Cost
public import FORS.GraphView.HashCalls
import all PolyFun.PFunctor.Handler.Instrumentation

@[expose] public section

section

/-! The counted graph-reveal signer. Its final assembly preserves the joint law of the actual
signature and its original hash cost on a fixed answer function. Internal graph work is charged
even when encoding exhausts. -/

open OracleComp OracleSpec

namespace FORS.Security.GraphView

variable [Params]
open Concrete Completeness Prefix HiddenGraph
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] firstEncoding ReferenceChoice.search encodingAttemptLimit
  Seeded.finishSign digestAttemptLimit sequenceFin

abbrev CostSpec := HiddenCost.SourceCostSpec HashInput HashOutput Coordinate

theorem fixedWorldCost_lift_hash (f : QueryImpl HashSpec Id)
    {α : Type} (computation : OracleComp HashSpec α) :
    simulateQ (fixedWorldCost f) (liftM computation : OracleComp OracleWorld α) =
      WriterT.mk (PMF.pure (evalWithAnswerFn f computation,
        Multiplicative.ofAdd (hashCalls f computation))) := by
  apply WriterT.ext
  have hcount : (simulateQ (fixedWorldCost f)
      (liftM computation : OracleComp OracleWorld α)).run =
      simulateQ (fixedHashWorld f) (QueryCap.counted SourceHash
        (liftM computation : OracleComp OracleWorld α)) := by
    rw [QueryCap.simulate_withCost]
    congr 2
    funext input
    cases input <;> simp only [fixedWorldCost, QueryImpl.withAddCost_apply] <;> rfl
  rw [hcount, fixedHashWorld_counted_lift_hash]
  rfl

/-- One tree's opening at the cost level: its secret and leaf are revealed, the path is public. -/
noncomputable def treeCostSource (data : PublicData) (index : Index) (κ : FTree) (leaf : FLeaf) :
    OracleComp CostSpec TreeOpening := do
  let values ← sequenceFin fun k : Fin 2 =>
    HiddenCost.reveal (H := Empty) (D := HashInput) (R := HashOutput) (.fors index κ leaf k)
  return ⟨values 0, data.forsPath index κ leaf⟩

/-- The counter search of one layer at the cost level: the honest cost of the key's message is
charged first, and on success the chain values and the path. -/
noncomputable def layerCostSearch (parameter : PublicParameter) (data : PublicData) (index : Index)
    (lay : Layer) : OracleComp CostSpec (Option (Counter × Encoding)) := do
  let found ← liftM (layerSearch parameter data index lay)
  match found with
  | some pair => do
      HiddenCost.tick (192 + treePathCost lay + recoverCost lay)
      return some pair
  | none => return none

noncomputable def finishCostSource (parameter : PublicParameter) (data : PublicData)
    (message : Message) (randomness : Randomness) : OracleComp CostSpec (Option Signature) := do
  let digest ← liftM (messageDigest parameter data.root message randomness :
    OracleComp HashSpec MessageDigest)
  HiddenCost.tick (forsTrees * treeOpenCost + forsRecoverCost)
  let index := digestIndex digest
  let some found ← sequenceDep (α := fun _ => Counter × Encoding) (layerCostSearch parameter data index)
    | return none
  let values ← sequenceFin fun lay : Layer => sequenceFin fun chain => HiddenCost.reveal
    (.chain lay (treeIndexAt index lay) (leafIndexAt index lay) chain ((found lay).2 chain))
  let opening ← sequenceFin fun κ => treeCostSource data index κ (digestLeaves digest κ)
  return some ⟨randomness, opening, layerSignatures data index found values⟩

/-- The scan from a start with a step: no randomness. -/
noncomputable def signCostSourceLoop (parameter : PublicParameter) (data : PublicData)
    (message : Message) (step : Randomness) : Nat → Randomness → OracleComp CostSpec (Option Signature)
  | 0, _ => pure none
  | attempts + 1, randomness => do
      let first ← liftM (messageDigestCall parameter data.root message randomness firstCall :
        OracleComp HashSpec HashOutput)
      if Landed parameter (blockIndex first) then
        finishCostSource parameter data message randomness
      else signCostSourceLoop parameter data message step attempts (randomness + step)

/-- The step of the walk of `message`. -/
def PublicData.step (data : PublicData) (message : Message) : Randomness := walkStep (data.steps message)

/-- One uniform start, then the scan with the message's step. -/
noncomputable def signCostSource (parameter : PublicParameter) (data : PublicData)
    (message : Message) : OracleComp CostSpec (Option Signature) := do
  let start ← liftM ($ᵗ Randomness : ProbComp Randomness)
  signCostSourceLoop parameter data message (data.step message) digestAttemptLimit start

end FORS.Security.GraphView

end

section

/-! The counted graph signer composed through an arbitrary adaptive adversary and the actual
verifier: explicit-reveal cost programs for the interaction, the rest of the game and the whole
game, which retain the strong signing log, and the cost of key generation on a fixed answer
function. -/

open OracleComp OracleSpec
namespace FORS.Security.GraphView

variable [Params]
open Concrete Completeness Prefix HiddenGraph SeedCoupling
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] signCostSource Seeded.keygenFromSeed

def ordinaryCostSource : QueryImpl OracleWorld (OracleComp CostSpec)
  | .inl request => liftM (CostSpec.query (.inl (.inl request)))
  | .inr request => liftM (CostSpec.query (.inl (.inr (.inl request))))

noncomputable def costInteraction (parameter : PublicParameter) (data : PublicData) :
    QueryImpl (OracleWorld + SigningSpec) (WriterT (QueryLog SigningSpec) (OracleComp CostSpec)) :=
  ordinaryCostSource.liftTarget (WriterT (QueryLog SigningSpec) (OracleComp CostSpec)) +
    QueryImpl.withLogging (spec := SigningSpec) (m := OracleComp CostSpec)
      (fun message => signCostSource parameter data message)

end FORS.Security.GraphView

end
