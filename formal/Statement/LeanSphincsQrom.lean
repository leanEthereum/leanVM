module

public import Statement.LeanSphincs
public import Mathlib.Data.BitVec
public import VCVio.Quantum.Oracle.Compressed.Oracle
public import VCVio.Quantum.Oracle.Model
public import VCVio.Quantum.Oracle.Classical
public import VCVio.Quantum.Comp.Combinators
public import VCVio.Quantum.Comp.TotalQueryBound

/-!
# leanSPHINCS in the quantum random-oracle model

Read after `LeanSphincs.lean`. Keccak-256 is a uniform random function `H` on the byte strings of
at most `2048` bytes (`Input`), which the adversary queries in superposition, as VCVio's
quantum random oracle (`Quantum.qromSpec`, its table oracle `|x, y⟩ ↦ |x, y + H x⟩`, where `+` on
the 256-bit answers is XOR, `Output`). Key
generation, the signer and the verifier are those of `LeanSphincs.lean` with `H` as the hash
(`hashOf`): every input they hash is shorter than `2048` bytes, and a longer one would be answered
`0`. The adversary's queries count the same whether quantum or classical.

The game draws `SK.seed` and `H` uniformly. Beside the hash it offers two classical ports, which
read and update the game's signing log: the public key, and the signer, which signs a message and
logs the request and its answer while the log holds fewer than `signatureLimit` entries (and
answers `none` past them). A port returns its answer and the log it read, and moves the log on
(`portTrans`). The
adversary starts from any substate `ρ` of its register, reads the public key, makes its calls and
returns a forgery; it wins when the forgery verifies on `H` and the log does not hold it
(`win`, strong unforgeability). `winProb` is the weight of the final leaves and logs at which it
wins, averaged over `SK.seed` and `H`.

The end statement, `LeanSphincsQromStronglyUnforgeable`: an adversary making at most `n` calls in
all (hash queries, quantum or classical, and signing requests) wins with probability at most
`((n + 2048) / 2^61.8)²`. As in `LeanSphincs.lean`, a key past its signature limit, which the deployed
signer does not count, is not covered.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal Matrix Quantum
open scoped Kronecker

namespace Sphincs.QuantumRandomOracleModel

open HashSig

/-! ## The finite types -/

/-- The lists of length at most `n` over a finite type are finitely many. -/
instance boundedListFintype (α : Type) [Fintype α] (n : ℕ) :
    Fintype {l : List α // l.length ≤ n} :=
  Fintype.ofEquiv (Σ k : Fin (n + 1), List.Vector α k)
    { toFun := fun v ↦ ⟨v.2.toList, by simpa using Nat.le_of_lt_succ v.1.2⟩
      invFun := fun x ↦ ⟨⟨x.1.length, Nat.lt_succ_of_le x.2⟩, ⟨x.1, rfl⟩⟩
      left_inv := by
        rintro ⟨⟨k, hk⟩, l, hl⟩
        simp only at hl
        subst hl
        rfl
      right_inv := fun _ ↦ rfl }

instance : Fintype PublicKey :=
  Fintype.ofEquiv (PublicParameter × Digest)
    { toFun := fun x ↦ ⟨x.1, x.2⟩, invFun := fun pk ↦ (pk.publicSeed, pk.root),
      left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }

instance : Fintype ForsTreeOpening :=
  Fintype.ofEquiv (Digest × (Fin forsTreeHeight → Digest))
    { toFun := fun x ↦ ⟨x.1, x.2⟩, invFun := fun o ↦ (o.secret, o.path),
      left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }

instance (layer : Layer) : Fintype (LayerSignature layer) :=
  Fintype.ofEquiv (EncodingCounter × (ChainIndex → Digest) × (Fin (layerHeight layer) → Digest))
    { toFun := fun x ↦ ⟨x.1, x.2.1, x.2.2⟩,
      invFun := fun l ↦ (l.counter, l.chainValues, l.authenticationPath),
      left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }

instance : Fintype Signature :=
  Fintype.ofEquiv (Randomizer × (ForsTreeIndex → ForsTreeOpening) × ((layer : Layer) → LayerSignature layer))
    { toFun := fun x ↦ ⟨x.1, x.2.1, x.2.2⟩,
      invFun := fun σ ↦ (σ.randomizer, σ.forsOpening, σ.layers),
      left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }

/-! ## The hash -/

/-- The oracle's answers: Keccak-256's outputs, 256-bit strings, added by XOR, so that the oracle
is the usual `|x, y⟩ ↦ |x, y ⊕ H x⟩`. -/
def Output := BitVec 256

instance : Add Output := ⟨fun a b ↦ BitVec.xor (n := 256) a b⟩
instance : Zero Output := ⟨(0 : BitVec 256)⟩
instance : Neg Output := ⟨fun a ↦ a⟩

instance : AddCommGroup Output where
  add_assoc a b c := BitVec.xor_assoc (w := 256) a b c
  zero_add a := BitVec.zero_xor (w := 256) (x := a)
  add_zero a := BitVec.xor_zero (w := 256) (x := a)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := BitVec.xor_self (w := 256) (x := a)
  add_comm a b := BitVec.xor_comm (w := 256) a b

instance : Fintype Output := inferInstanceAs (Fintype (BitVec 256))
instance : DecidableEq Output := inferInstanceAs (DecidableEq (BitVec 256))

/-- The longest input the random oracle answers. -/
def maxInputLength : ℕ := 2048

/-- The oracle's inputs: the byte strings of at most `maxInputLength` bytes. -/
abbrev Input := {l : HashInput // l.length ≤ maxInputLength}

/-- The hash of the algorithms on the random function `H`: `H` on its inputs, `0` past them. -/
def hashOf (H : Input → Output) (input : HashInput) : Id HashOutput :=
  if h : input.length ≤ maxInputLength then H ⟨input, h⟩ else 0

/-- Key generation from `SK.seed` on `H`. -/
def keysOn (seed : MasterSeed) (H : Input → Output) : PublicKey × SecretKey :=
  Id.run (KeyGenerationAndSigning.keygenFromSeed (hashOf H) seed)

/-- The signature of a message on `H`, `none` if the signer fails. -/
def signOn (seed : MasterSeed) (H : Input → Output) (message : Message) : Option Signature :=
  Id.run (KeyGenerationAndSigning.sign (hashOf H) seed message)

/-- Verification on `H`. -/
def verifyOn (H : Input → Output) (publicKey : PublicKey) (forgery : Forgery) : Bool :=
  Id.run (Verification.verify (hashOf H) publicKey forgery.message forgery.signature)

/-! ## The classical ports -/

/-- The classical ports: the public key, and the signing of a message. -/
inductive Port where
  | publicKey
  | sign (message : Message)
deriving DecidableEq

instance : Fintype Port :=
  Fintype.ofEquiv (Option Message)
    { toFun := fun o ↦ o.elim .publicKey .sign
      invFun := fun | .publicKey => none | .sign m => some m
      left_inv := fun o ↦ by cases o <;> rfl
      right_inv := fun j ↦ by cases j <;> rfl }

/-- A port's answer: the public key, or a signature unless the signer fails. -/
@[reducible]
def Answer : Port → Type
  | .publicKey => PublicKey
  | .sign _ => Option Signature

instance (j : Port) : Fintype (Answer j) := by cases j <;> exact inferInstance
instance (j : Port) : DecidableEq (Answer j) := by cases j <;> exact inferInstance

/-- The signing log: the requests and their answers, at most `signatureLimit`. -/
abbrev Log := {l : List (Message × Option Signature) // l.length ≤ signatureLimit}

instance : DecidableEq Log := inferInstance
instance : Fintype Log := inferInstance

/-- The empty log. -/
def Log.empty : Log := ⟨[], Nat.zero_le _⟩

/-- The log holds the forgery: its message, answered with its signature. -/
def Log.Contains (log : Log) (forgery : Forgery) : Prop :=
  ∃ e ∈ log.1, e.1 = forgery.message ∧ e.2 = some forgery.signature

instance (log : Log) (forgery : Forgery) : Decidable (log.Contains forgery) := by
  unfold Log.Contains
  exact inferInstance

/-- A port's answer and the log after it, from the log before: the public key leaves the log alone;
the signer signs and logs while the log has room, and answers `none` past it. -/
def portTrans (seed : MasterSeed) (H : Input → Output) : (j : Port) → Log → Answer j × Log
  | .publicKey, log => ((keysOn seed H).1, log)
  | .sign m, log =>
    if h : log.1.length < signatureLimit then
      (signOn seed H m, ⟨log.1 ++ [(m, signOn seed H m)], by simp; omega⟩)
    else (none, log)

/-! ## The game -/

/-- The classical ports' signature: no quantum register, the answer and the log read. -/
@[reducible]
def portSpec : QuantumOracleSpec.{0, 0} where
  Port := Port
  In _ := QReg.of Unit
  Out _ := QReg.of Unit
  Result j := Answer j × Log

/-- The game's signature: the random oracle, then the classical ports. -/
@[reducible]
def spec : QuantumOracleSpec.{0, 0} := (qromSpec Input Output).sum portSpec

/-- The Kraus operator of port `j` with answer `a` read at log `log₀`: it moves `log₀` to its
successor, `|log'⟩⟨log₀|`, when `a` is the answer at `log₀`. -/
noncomputable def portKraus (seed : MasterSeed) (H : Input → Output) (j : Port)
    (al : Answer j × Log) : Matrix (Unit × (Log × Unit)) (Unit × (Log × Unit)) ℂ :=
  (if (portTrans seed H j al.2).1 = al.1 then (1 : ℂ) else 0) •
    ((1 : Matrix Unit Unit ℂ) ⊗ₖ (Matrix.single (portTrans seed H j al.2).2 al.2 (1 : ℂ) ⊗ₖ
      (1 : Matrix Unit Unit ℂ)))

/-- The Kraus operators of a port sum to the identity: a port is a measurement of the log. -/
theorem sum_portKraus (seed : MasterSeed) (H : Input → Output) (j : Port) :
    ∑ al, (portKraus seed H j al)ᴴ * portKraus seed H j al = 1 := by
  have hterm : ∀ al : Answer j × Log, (portKraus seed H j al)ᴴ * portKraus seed H j al =
      (if (portTrans seed H j al.2).1 = al.1 then (1 : ℂ) else 0) •
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ (Matrix.single al.2 al.2 (1 : ℂ) ⊗ₖ
          (1 : Matrix Unit Unit ℂ))) := by
    intro al
    rw [portKraus, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      conjTranspose_kronecker, conjTranspose_kronecker, conjTranspose_one, conjTranspose_single,
      ← mul_kronecker_mul, ← mul_kronecker_mul, single_mul_single_same]
    congr 1
    · split_ifs <;> simp
    · simp
  simp only [hterm]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hsum : ∀ (M : Log → Matrix Log Log ℂ),
      (1 : Matrix Unit Unit ℂ) ⊗ₖ ((∑ i, M i) ⊗ₖ (1 : Matrix Unit Unit ℂ)) =
        ∑ i, (1 : Matrix Unit Unit ℂ) ⊗ₖ (M i ⊗ₖ (1 : Matrix Unit Unit ℂ)) := by
    intro M
    ext a b
    simp [kroneckerMap_apply, Matrix.sum_apply, Finset.mul_sum]
  rw [← hsum, sum_single_one, one_kronecker_one, one_kronecker_one]

/-- A call of the random oracle: `|x, y⟩ ↦ |x, y + H x⟩`, the log untouched. -/
noncomputable def hashStep (H : Input → Output) :
    SubInstrument ((Input × Output) × (Log × Unit)) ((Input × Output) × (Log × Unit)) Unit :=
  SubInstrument.ofIsometry (tableOracle fun (_ : Log × Unit) ↦ H) (conjTranspose_tableOracle_mul_self _)

/-- A call of port `j`: the measurement of `portKraus`. -/
noncomputable def portStep (seed : MasterSeed) (H : Input → Output) (j : Port) :
    SubInstrument (Unit × (Log × Unit)) (Unit × (Log × Unit)) (Answer j × Log) :=
  SubInstrument.ofKraus (portKraus seed H j) (sum_portKraus seed H j)

/-- **The game's runtime** on `SK.seed` and `H`: its register holds the signing log, empty at the
start; the random oracle answers `H`, and the classical ports read and update the log. -/
noncomputable def runtime (seed : MasterSeed) (H : Input → Output) : QuantumRuntime spec where
  D := QReg.of (Log × Unit)
  init := (SubState.basis Log.empty).prod (SubState.basis ())
  step
    | .inl _ => hashStep H
    | .inr j => portStep seed H j

/-- An adversary from the register `A`: given the public key, a program that returns a forgery. -/
abbrev Adversary (A : QReg) := PublicKey → QComp spec A (QReg.of Unit) Forgery

/-- Read the public key from its port. -/
noncomputable def readKey (A : QReg) : QComp spec A A PublicKey :=
  QComp.callBasis (spec := spec) (Sum.inr Port.publicKey) A () fun _ r ↦ r.1

/-- The adversary run on the public key it reads; its leaf records the key and the forgery. -/
noncomputable def withKey {A : QReg} (adv : Adversary A) :
    QComp spec A (QReg.of Unit) (PublicKey × Forgery) :=
  (readKey A).bind fun pk ↦ (adv pk).map fun forgery ↦ (pk, forgery)

/-- The adversary wins: its forgery verifies on `H` against the key it read, and the log does not
hold it. -/
def win (H : Input → Output) (v : PublicKey × Forgery) (log : Log) : Bool :=
  verifyOn H v.1 v.2 && !decide (log.Contains v.2)

/-- **The probability that the adversary wins** from the substate `ρ` of its register: the weight,
in the joint post-state of the run, of the leaves and final logs at which it wins, averaged over a
uniform `SK.seed` and a uniform `H`. -/
noncomputable def winProb {A : QReg} (adv : Adversary A) (ρ : SubState A) : ℝ≥0∞ :=
  ∑ seed : MasterSeed, ∑ H : Input → Output,
    ((Fintype.card MasterSeed : ℝ≥0∞) * Fintype.card (Input → Output))⁻¹ *
      ∑' p, ∑ log : Log, if win H p.2.2 log then
        ENNReal.ofReal (∑ b, (((runtime seed H).jointPost .instruments (withKey adv) ρ p).matrix
          (b, (log, ())) (b, (log, ()))).re) else 0

/-! ## The end statement -/

/-- **leanSPHINCS in the quantum random-oracle model**: an adversary making at most `n` calls in
all, hash queries (quantum or classical) and signing requests, on every public key, forges with
probability at most `((n + 2048) / 2^61.8)²`. Key generation's hashing, the signer's and the
forgery's verification are not charged to `n`. Proved by `Qrom.Sphincs.leanSphincsQrom`. -/
def LeanSphincsQromStronglyUnforgeable : Prop :=
  ∀ (A : QReg) (adv : Adversary A) (n : ℕ), (∀ pk, (adv pk).IsTotalQueryBound n) →
    ∀ ρ : SubState A, winProb adv ρ ≤ ((n + 2048 : ℝ≥0∞) / 2 ^ (61.8 : ℝ)) ^ 2

end Sphincs.QuantumRandomOracleModel

end
