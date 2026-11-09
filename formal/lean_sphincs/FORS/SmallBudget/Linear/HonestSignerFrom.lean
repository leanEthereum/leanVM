module

public import FORS.SmallBudget.Linear.HonestFrom
public import FORS.GraphView.HonestSigner
public import FORS.GraphView.PreparedSearch

@[expose] public section

/-! The honest signer meets the small route's honest-read class from the prepared cache. Its
reads are message-digest inputs and prepared WOTS+C trials (`GraphView.SignerReadsGood`);
`HonestGood` at a targeting that leaves exactly the message-digest inputs untargeted is the small
route's class, so the signer's `HonestOkFrom` there is its `HonestWithFrom (SmallHonest …)`. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.PotentialA

variable [Params]

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost HiddenReveal GraphView

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- A targeting whose untargeted inputs are exactly the message-digest inputs. -/
noncomputable def msgTargeting (tg : Targeting HashInput HashOutput Coordinate) :
    Targeting HashInput HashOutput Coordinate where
  trunc := tg.trunc
  kind := fun x => if ForsSigner.IsMsgInput x then .none else .fixed default
  digest := tg.digest

theorem msgTargeting_kind_none {tg : Targeting HashInput HashOutput Coordinate} {x : HashInput} :
    (msgTargeting tg).kind x = .none ↔ ForsSigner.IsMsgInput x := by
  unfold msgTargeting
  by_cases hx : ForsSigner.IsMsgInput x <;> simp [hx]

section Sample

variable (parameterOutput : HashOutput) (highs : CoordinateHighs)
  (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)

/-- `HonestOkFrom` at `msgTargeting` is `HonestWithFrom` of the small route's class. -/
theorem honestWithFrom_small_of_honestOkFrom (tg : Targeting HashInput HashOutput Coordinate) {H : Type}
    [HonestInputs H HashInput] {α : Type} {comp : OracleComp (SourceCostSpec HashInput HashOutput Coordinate H) α}
    (h : HonestOkFrom (msgTargeting tg) prepared.2 (sampleModel parameterOutput highs) comp) :
    HonestWithFrom prepared.2 (SmallHonest parameterOutput highs prepared) comp :=
  honestWithFrom_mono prepared.2 (P := HonestGood (msgTargeting tg) prepared.2 (sampleModel parameterOutput highs))
    (fun _ hx => ⟨hx.1, hx.2.imp id msgTargeting_kind_none.1⟩) h

/-- The signer's reads are good at `msgTargeting` when message-digest inputs and trials are unparsed
and every key's counter search is prepared. -/
theorem signerReadsGood_msg (tg : Targeting HashInput HashOutput Coordinate) (parameter : PublicParameter)
    (data : PublicData)
    (hdigest : ∀ parameter' root message randomness call,
      (sampleModel parameterOutput highs).parse (messageDigestInput parameter' root message randomness call) = none)
    (htrial : ∀ lay tree leaf message start,
      (sampleModel parameterOutput highs).parse (trialInput parameter lay tree leaf message start) = none)
    (hsearch : ∀ lay tree leaf, SearchCached prepared.2 parameter lay tree leaf (data.keyMessage lay tree leaf)
      encodingAttemptLimit 0) :
    SignerReadsGood (msgTargeting tg) prepared.2 (sampleModel parameterOutput highs) parameter data :=
  ⟨fun parameter' root message randomness call => ⟨hdigest parameter' root message randomness call,
      Or.inr (msgTargeting_kind_none.2 ⟨parameter', root, message, randomness, call, rfl⟩)⟩,
    htrial, hsearch⟩

/-- **The honest signer reads the small route's class from the prepared cache.** -/
theorem honestWithFrom_small_signCostSourceH (tg : Targeting HashInput HashOutput Coordinate)
    (parameter : PublicParameter) (data : PublicData)
    (hgood : SignerReadsGood (msgTargeting tg) prepared.2 (sampleModel parameterOutput highs) parameter data)
    (message : Message) :
    HonestWithFrom prepared.2 (SmallHonest parameterOutput highs prepared) (signCostSourceH parameter data message) :=
  honestWithFrom_small_of_honestOkFrom parameterOutput highs prepared tg
    (honestOkFrom_signCostSourceH (msgTargeting tg) prepared.2 (sampleModel parameterOutput highs) parameter data
      hgood message)

/-- **The sampled signer's reads are good at `msgTargeting`** for every prepared cache. -/
theorem signerReadsGood_sample (tg : Targeting HashInput HashOutput Coordinate) (fixed : HiddenGraph.Table)
    (remaining : RemainingOutputs) (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining)) :
    SignerReadsGood (msgTargeting tg) prepared.2 (sampleModel parameterOutput highs) (truncateHash parameterOutput)
      (sampleData parameterOutput fixed highs remaining) :=
  signerReadsGood_msg parameterOutput highs prepared tg _ _
    (fun parameter' root message randomness call => by
      rw [sampleModel_parse]
      exact parse_msg_none _ _ _ ⟨parameter', root, message, randomness, call, rfl⟩)
    (fun lay tree leaf message start => by
      rw [sampleModel_parse, trialInput, parse_tweakable_none _ _ _ _
        (fun address => by cases address <;> simp [Address.position, Position.domain]) (by trivial)])
    (searchCached_preparation parameterOutput fixed highs remaining prepared hprepared)

end Sample

end FORS.Security.PotentialA
