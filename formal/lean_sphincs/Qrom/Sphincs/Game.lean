module

public import Qrom.Sphincs.VerifyBound
public import FORS.Statement

@[expose] public section

/-!
# The SUF-CMA game of leanSPHINCS in the quantum random-oracle model

The hash is a uniform function `H` on the inputs of length at most `maxLen`, which the adversary
queries in superposition. Beside it the game offers two classical ports: the public key, and the
signing oracle, which signs a message with `Seeded.sign` on `H` and logs the request and its answer
while the log holds fewer than `signatureLimit` entries (`Qrom.Sphincs.realGame`). The adversary
starts from any state of its register, reads the public key, makes its calls and returns a forgery,
which the game checks with the verifier on `H` (`Qrom.Sphincs.gameProg`). It wins when the forgery
verifies and the log does not hold it (`Qrom.Sphincs.winProb`).
-/

open OracleComp OracleSpec FORS Quantum

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

variable [Params]

/-! ## Finiteness of the scheme's types -/

instance : Fintype PublicKey :=
  Fintype.ofEquiv (Digest × PublicParameter)
    { toFun := fun x ↦ ⟨x.1, x.2⟩, invFun := fun pk ↦ (pk.root, pk.parameter),
      left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }

instance : Fintype TreeOpening :=
  Fintype.ofEquiv (Digest × (Fin forsHeight → Digest))
    { toFun := fun x ↦ ⟨x.1, x.2⟩, invFun := fun o ↦ (o.secret, o.path),
      left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }

instance (lay : Layer) : Fintype (LayerSignature lay) :=
  Fintype.ofEquiv (Counter × (ChainIndex → Digest) × (Fin (layerHeight lay) → Digest))
    { toFun := fun x ↦ ⟨x.1, x.2.1, x.2.2⟩, invFun := fun l ↦ (l.counter, l.chainValues, l.path),
      left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }

instance : Fintype Signature :=
  Fintype.ofEquiv (Randomness × (FTree → TreeOpening) × ((lay : Layer) → LayerSignature lay))
    { toFun := fun x ↦ ⟨x.1, x.2.1, x.2.2⟩, invFun := fun σ ↦ (σ.randomness, σ.fors, σ.layers),
      left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }

/-! ## The ports -/

/-- The classical ports: the public key, and the signing of a message. -/
inductive Port where
  | pk
  | sign (message : Message)
deriving DecidableEq

instance : Fintype Port :=
  Fintype.ofEquiv (Option Message)
    { toFun := fun o ↦ o.elim .pk .sign
      invFun := fun | .pk => none | .sign m => some m
      left_inv := fun o ↦ by cases o <;> rfl
      right_inv := fun j ↦ by cases j <;> rfl }

/-- The result of a port: the public key, or a signature unless the signer failed. -/
@[reducible]
def Res : Port → Type
  | .pk => PublicKey
  | .sign _ => Option Signature

instance (j : Port) : Fintype (Res j) := by cases j <;> exact inferInstance
instance (j : Port) : DecidableEq (Res j) := by cases j <;> exact inferInstance

/-- The signing log: the requests and their answers, at most `signatureLimit`. -/
abbrev Log := {l : List (Message × Option Signature) // l.length ≤ signatureLimit}

/-- The empty log. -/
def Log.empty : Log := ⟨[], Nat.zero_le _⟩

/-- The log holds the forgery: its message, answered with its signature. -/
def Log.Contains (s : Log) (F : Forgery) : Prop :=
  ∃ e ∈ s.1, e.1 = F.message ∧ e.2 = some F.signature

instance (s : Log) (F : Forgery) : Decidable (s.Contains F) := by
  unfold Log.Contains
  exact inferInstance

/-- The specification of the game's ports: the hash, then the classical ports. -/
abbrev Spec := ovSpec Input HashOutput Log Port Res

/-! ## The game -/

/-- Key generation from `SK.seed` on the hash `H`. -/
def keysOf (seed : MasterSeed) (H : Input → HashOutput) : PublicKey × Seeded.SecretKey :=
  evalWithAnswerFn (QueryImpl.ofFn (extend H)) (Seeded.keygen seed)

/-- The signature of a message on the hash `H`. -/
def signOf (seed : MasterSeed) (H : Input → HashOutput) (m : Message) : Option Signature :=
  evalWithAnswerFn (QueryImpl.ofFn (extend H))
    (Seeded.sign (keysOf seed H).2 m : OracleComp HashSpec (Option Signature))

/-- The transition of a classical port, given the signer. -/
def portTrans (pk : PublicKey) (sign : Message → Option Signature) :
    (j : Port) → Log → Res j × Log
  | .pk, s => (pk, s)
  | .sign m, s =>
    if h : s.1.length < signatureLimit then (sign m, ⟨s.1 ++ [(m, sign m)], by simp; omega⟩)
    else (none, s)

/-- The game with `SK.seed` and the hash `H`: no override, and the classical ports. -/
def realGame (seed : MasterSeed) (H : Input → HashOutput) : OvGame Input HashOutput Log Port Res where
  init := Log.empty
  ov := fun _ _ ↦ none
  trans := portTrans (keysOf seed H).1 (signOf seed H)

/-- An adversary from the register `A`: given the public key, a program that returns a forgery. -/
abbrev Adversary (A : QReg) := PublicKey → QComp Spec A (QReg.of Unit) Forgery

/-- Read the public key. -/
def readKey (A : QReg) : QComp Spec A A PublicKey :=
  QComp.callBasis (spec := Spec) (Sum.inr Port.pk) A () fun _ r ↦ r.1

/-- The adversary run on the public key it reads. -/
def withKey {A : QReg} (adv : Adversary A) : QComp Spec A (QReg.of Unit) (PublicKey × Forgery) :=
  (readKey A).bind fun pk ↦ (adv pk).map fun F ↦ (pk, F)

/-- The verifier on the finite oracle, with the inputs it reads. -/
def verifier (x : PublicKey × Forgery) : OracleComp (Input →ₒ HashOutput) (Bool × List HashInput) :=
  liftH (traced (Concrete.verify x.1 x.2.message x.2.signature))

/-- The game's program: the adversary, then the verifier of its forgery. -/
def gameProg {A : QReg} (adv : Adversary A) :
    QComp Spec A (QReg.of Unit) ((PublicKey × Forgery) × (Bool × List HashInput)) :=
  OvGame.withVerifier (withKey adv) verifier

/-- The adversary wins: its forgery verifies and the log does not hold it. -/
def win (v : (PublicKey × Forgery) × (Bool × List HashInput)) (s : Log) : Bool :=
  v.2.1 && !decide (s.Contains v.1.2)

/-- **The probability that the adversary wins**, over a uniform `SK.seed` and a uniform hash, from the
state `ρ` of its register: the weight of the final results and logs in which it wins. -/
def winProb {A : QReg} (adv : Adversary A) (ρ : SubState A) : ENNReal :=
  ∑ seed : MasterSeed, ∑ H : Input → HashOutput,
    ((Fintype.card MasterSeed : ENNReal) * Fintype.card (Input → HashOutput))⁻¹ *
      OvGame.sideW (realGame seed H) H .instruments (gameProg adv) ρ fun p s ↦ win p.2.2 s

end Qrom.Sphincs
