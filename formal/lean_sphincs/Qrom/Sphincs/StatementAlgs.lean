module

public import Qrom.Sphincs.Game
public import Statement.LeanSphincsQrom
public import Sphincs.CrateSim
public import FORS.CrateStatic

@[expose] public section

/-!
# The statement's algorithms on a fixed hash

On a function `H` on the inputs, key generation, the signer and the verifier of
`Statement/LeanSphincsQrom.lean` (the statement's algorithms with `H` as the hash) are those of the
proof's game (`Qrom.Sphincs.keysOf`, `Qrom.Sphincs.signOf`, FORS's verifier), through the maps of
keys and signatures of `Sphincs/Model.lean`: the statement's algorithms are the crate's on any hash
(`Sphincs.Model.simulateQ_crateKeygen`, `simulateQ_crateSign`, `simulateQ_verify`), and the crate's
key generation and signer are FORS's on every answer function (`FORS.Crate.eval_keygen`,
`FORS.Crate.eval_sign`).
-/

open OracleComp OracleSpec

noncomputable section

namespace Qrom.SphincsStatement

/-! ## The crate's key generation and signer on `H`, for any parameters -/

section generic

variable [FORS.Params]

theorem crate_keygen_fst (seed : FORS.MasterSeed) (H : Qrom.Sphincs.Input → FORS.HashOutput) :
    (@simulateQ FORS.HashInput FORS.HashSpec Id _ (QueryImpl.ofFn (Qrom.Sphincs.extend H)) _
      (FORS.Crate.keygen seed : OracleComp FORS.HashSpec _)).1 = (Qrom.Sphincs.keysOf seed H).1 :=
  congrArg Prod.fst (FORS.Crate.eval_keygen (QueryImpl.ofFn (Qrom.Sphincs.extend H)) seed)

theorem crate_sign (seed : FORS.MasterSeed) (H : Qrom.Sphincs.Input → FORS.HashOutput)
    (m : FORS.Message) :
    @simulateQ FORS.HashInput FORS.HashSpec Id _ (QueryImpl.ofFn (Qrom.Sphincs.extend H)) _
      (FORS.Crate.sign seed m : OracleComp FORS.HashSpec _) = Qrom.Sphincs.signOf seed H m :=
  FORS.Crate.eval_sign (QueryImpl.ofFn (Qrom.Sphincs.extend H)) seed m

end generic

attribute [local instance] _root_.Sphincs.Model.params

open _root_.Sphincs.Model (hashImpl ofModelPublicKey toModelPublicKey ofModelSignature
  toModelSignature)

/-- The statement's hash on `H` is the proof's. -/
theorem hashOf_eq (H : Qrom.Sphincs.Input → FORS.HashOutput) :
    hashImpl (_root_.Sphincs.QuantumRandomOracleModel.hashOf H) =
      QueryImpl.ofFn (Qrom.Sphincs.extend H) := by
  funext l
  show _root_.Sphincs.QuantumRandomOracleModel.hashOf H l = Qrom.Sphincs.extend H l
  unfold _root_.Sphincs.QuantumRandomOracleModel.hashOf Qrom.Sphincs.extend Qrom.Sphincs.embed
  by_cases h : l.length ≤ 2048 <;>
    simp [h, _root_.Sphincs.QuantumRandomOracleModel.maxInputLength, Qrom.Sphincs.maxLen] <;> rfl

/-- **Key generation**: the statement's public key on `H` is the proof's, mapped. -/
theorem keysOn_fst (seed : FORS.MasterSeed) (H : Qrom.Sphincs.Input → FORS.HashOutput) :
    (_root_.Sphincs.QuantumRandomOracleModel.keysOn seed H).1 =
      ofModelPublicKey (Qrom.Sphincs.keysOf seed H).1 := by
  have h := _root_.Sphincs.Model.simulateQ_crateKeygen
    (hash := _root_.Sphincs.QuantumRandomOracleModel.hashOf H) seed
  rw [hashOf_eq] at h
  have e1 := congrArg (fun x ↦ (Id.run x).1) h
  simp only [Id.run_map] at e1
  unfold _root_.Sphincs.QuantumRandomOracleModel.keysOn
  rw [← crate_keygen_fst seed H]
  exact e1.symm

/-- **The signer**: the statement's signature on `H` is the proof's, mapped. -/
theorem signOn_eq (seed : FORS.MasterSeed) (H : Qrom.Sphincs.Input → FORS.HashOutput)
    (m : FORS.Message) :
    _root_.Sphincs.QuantumRandomOracleModel.signOn seed H m =
      Option.map ofModelSignature (Qrom.Sphincs.signOf seed H m) := by
  have h := _root_.Sphincs.Model.simulateQ_crateSign
    (hash := _root_.Sphincs.QuantumRandomOracleModel.hashOf H) seed m
  rw [hashOf_eq] at h
  unfold _root_.Sphincs.QuantumRandomOracleModel.signOn
  rw [← h, Id.run_map, crate_sign]
  rfl

/-- **The verifier**: the statement's verification on `H` is FORS's, through the maps. -/
theorem verifyOn_eq (H : Qrom.Sphincs.Input → FORS.HashOutput) (pk : _root_.Sphincs.PublicKey)
    (F : _root_.Sphincs.Forgery) :
    _root_.Sphincs.QuantumRandomOracleModel.verifyOn H pk F =
      evalWithAnswerFn (QueryImpl.ofFn (Qrom.Sphincs.extend H))
        (FORS.Concrete.verify (toModelPublicKey pk) F.message (toModelSignature F.signature)) := by
  have h := _root_.Sphincs.Model.simulateQ_verify
    (hash := _root_.Sphincs.QuantumRandomOracleModel.hashOf H) pk F.message F.signature
  rw [hashOf_eq] at h
  unfold _root_.Sphincs.QuantumRandomOracleModel.verifyOn evalWithAnswerFn
  rw [← h]
  rfl

end Qrom.SphincsStatement
