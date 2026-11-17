module

public import Quantum.Qrom.Sphincs.Hybrid
public import Quantum.StdModel.Sphincs.Events
public import Quantum.StdModel.Props.Basic

@[expose] public section

/-!
# The ITSR game of leanSPHINCS's B3 as a template program

The template game (`Quantum.Qrom.Sphincs.Template`) with the ITSR decision in place of the
verification: the challenge prefix `prefixT`, then for each of the first `signatureLimit` signed
messages the signer's first three steps again (`foldT`: reveal `PK.seed`, `PK.root` and `R(M)`,
reveal the digest policy's coordinates, hardwire the digest cell), giving the message, its
randomizer and its digest; then the forgery's digest through read ports (`tailIT`, the two
`H_msg` calls of `(R*, M*)`), and the ITSR decision (`itsrDecT`): the forgery's pair is no signed
pair and its digest's cells are covered by the signed digests' cells. A transcript longer than
`signatureLimit` decides `true` (such runs do not occur within the signing budget).

* `foldT pol B msgs`, `prefixIT`, `tailIT`, `gameIT` (`gameIT_eq`: the prefix with the data, then
  the tail).
* The canonical realized games at the hidden values `θ` (`SelMem`, `cwUpd`): `gameIQ`, `prefixIQ`;
  runtime 2's win `p2I pol A θ`.
-/

open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open scoped ENNReal

namespace Quantum.StdModel.Sphincs.SphItsr

open Quantum QuantumRuntime
open Quantum.Qrom.Sphincs
open Quantum.Xmss.Assembly (runtimeR realizeT revealThen progThen recHwSpec RevealVals)

/-! ## The template game -/

/-- A signed message's ITSR datum: the message, its randomizer, its digest. -/
abbrev ItsrDatum : Type :=
  Message × Randomizer × MessageDigest

/-- **The ITSR event on the data**: the pair `(R, M)` is no signed pair, and the cells of the digest
`dF` are covered by the cells of the signed digests. -/
def ItsrHolds (dF : MessageDigest) (R : Randomizer) (msg : Message) (ds : List ItsrDatum) :
    Prop :=
  (R, msg) ∉ ds.map (fun d ↦ (d.2.1, d.1)) ∧
    digestCells dF ⊆ (ds.map fun d ↦ digestCells d.2.2).foldr (· ∪ ·) ∅

/-- **The ITSR decision of the template game**: `true` past `signatureLimit` signed messages,
the ITSR event of the forgery's digest `dF` on the data otherwise. -/
noncomputable def itsrDecT (n : ℕ) (forg : Forgery) (ds : List ItsrDatum) (dF : MessageDigest) :
    Bool :=
  decide (signatureLimit < n) ||
    Props.holds (ItsrHolds dF forg.signature.randomizer forg.message ds)

variable (M : Type) [Fintype M] [DecidableEq M] (upd : TrialUpd M)

/-- **The data of the signed messages `msgs`**: for each, the signer's first three steps (reveal
`PK.seed`, `PK.root`, `R(M)` with the label `L` before; reveal `pol.need L M`; hardwire the digest
cell), giving the message, its randomizer and its digest. -/
noncomputable def foldT (pol : DigestPolicy) (B : QReg) :
    List Message → QComp (SSpecQ M) B B (List ItsrDatum)
  | [] => QuantumComp₂.pure []
  | msg :: ms =>
    revealThen goodQ {seedC, rootC, rndC msg} fun r₁ ↦
    revealThen goodQ (pol.need r₁.2.1 msg) fun r₂ ↦
    progThen (digPort pol r₁.2.1 msg) trivial <|
    (foldT pol B ms).bind fun ds ↦
      QuantumComp₂.pure ((msg, (tabR r₁.1).randomizer msg, digestT pol r₁.2.1 msg r₂.1) :: ds)

/-- The challenge prefix's outcome with the data of the signed messages. -/
abbrev PreI : Type :=
  PublicKey × (Forgery × SufCma.SignLog Message (Option Signature)) × List ItsrDatum

/-- The messages of a signing transcript, at most `signatureLimit` of them. -/
def logMsgsT (log : SufCma.SignLog Message (Option Signature)) : List Message :=
  (log.map Sigma.fst).take signatureLimit

/-- **The challenge prefix with the data**: `prefixT`, then `foldT` on the first
`signatureLimit` signed messages. -/
noncomputable def prefixIT (pol : DigestPolicy) (A : SAdversary) :
    QComp (SSpecQ M) (QReg.of Unit) (QReg.of Unit) PreI :=
  (prefixT M upd pol A).bind fun x ↦
    (foldT M pol (QReg.of Unit) (logMsgsT x.2.2)).bind fun ds ↦
      QuantumComp₂.pure (x.1, x.2, ds)

/-- **The tail**: the forgery's digest through read ports, then the ITSR decision. -/
noncomputable def tailIT (y : PreI) : QComp (SSpecQ M) (QReg.of Unit) (QReg.of Unit) Bool :=
  readsThenT M (LeanSphincsOver.messageDigest Qrom.hashQ y.1 y.2.1.1.signature.randomizer
    y.2.1.1.message) fun dF ↦ itsrDecT y.2.1.2.length y.2.1.1 y.2.2 dF

/-- **The ITSR game of B3 as a template**: the challenge prefix, the data of the signed messages,
the forgery's digest through read ports and the ITSR decision. -/
noncomputable def gameIT (pol : DigestPolicy) (A : SAdversary) :
    QComp (SSpecQ M) (QReg.of Unit) (QReg.of Unit) Bool :=
  (prefixIT M upd pol A).bind (tailIT M)

omit [Fintype M] [DecidableEq M] in
theorem gameIT_eq (pol : DigestPolicy) (A : SAdversary) :
    gameIT M upd pol A = (prefixIT M upd pol A).bind (tailIT M) :=
  rfl

/-! ## The canonical realized games -/

/-- **The canonical realized ITSR game** at the policy `pol` and the hidden values `θ` (the
counter searches' reads record codeword selections, `cwUpd`). -/
noncomputable def gameIQ (pol : DigestPolicy) (A : SAdversary) (θ : TVals) :
    QComp (recHwSpec PairOut Qrom.HashDomain TPos SelMem) (QReg.of Unit) (QReg.of Unit) Bool :=
  realizeT θ (gameIT SelMem cwUpd pol A)

/-- The canonical realized prefix with the data. -/
noncomputable def prefixIQ (pol : DigestPolicy) (A : SAdversary) (θ : TVals) :
    QComp (recHwSpec PairOut Qrom.HashDomain TPos SelMem) (QReg.of Unit) (QReg.of Unit) PreI :=
  realizeT θ (prefixIT SelMem cwUpd pol A)

/-- **Runtime 2's ITSR win** at the policy `pol` and the hidden values `θ`. -/
noncomputable def p2I (pol : DigestPolicy) (A : SAdversary) (θ : TVals) : ℝ≥0∞ :=
  (runtimeR m0H).evalDistMap .instruments (gameIQ pol A θ) (SubState.basis ()) winObsQ {true}

end Quantum.StdModel.Sphincs.SphItsr

end
