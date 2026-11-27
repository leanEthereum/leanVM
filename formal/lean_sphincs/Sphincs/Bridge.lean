module

public import Sphincs.ModelRpm
public import Sphincs.Transport

@[expose] public section

/-!
# The statement's end statement from the crate's copy

The statement's leanSPHINCS in the random-permutation model
(`Sphincs.RandomPermutationModel.sufCmaScheme`) is the crate's copy in the model's hash monad
(`Sphincs.Model.crateScheme`: `FORS.Crate.keygen`, `FORS.Crate.sign`, FORS's verifier), each
hash query answered by Keccak-256 over `π`, through the maps of the keys, the signatures and the
forgeries: key generation (`simulateQ_crateKeygen`), the signer (`simulateQ_crateSign`), both in
`Sphincs/CrateSim.lean`, and the verifier (`simulateQ_verify`) correspond, and so do the winning
conditions (`win_eq`), the statement's with the model's limit on the signing requests
(`limitedScheme`). So that scheme's game is the crate's copy's against the adversary read through
the maps (`Sphincs.Transport.forgeryGame_eq`), and, against an adversary within the limit, the
statement's (`Sphincs.Transport.forgeryGame_winningCondition_congr`), which `Sphincs/AdvRpm.lean`
uses.
-/

open OracleComp OracleSpec ENNReal Common Common.SufCma

namespace Sphincs.Model

attribute [local instance] params

/-- A statement forgery as the model's. -/
def toModelForgery (forgery : Forgery) : FORS.Forgery :=
  ⟨forgery.message, toModelSignature forgery.signature⟩

theorem map_eq_some_iff (answer : Option FORS.Signature) (signature : Signature) :
    Option.map ofModelSignature answer = some signature ↔
      answer = some (toModelSignature signature) := by
  rcases answer with _ | answer
  · simp
  · simp only [Option.map_some, Option.some.injEq]
    constructor
    · rintro rfl
      exact (signatureEquiv.left_inv answer).symm
    · rintro rfl
      exact signatureEquiv.right_inv signature

/-- The statement's scheme with the model's winning condition: a forgery the signer did not return,
in a log of at most `signatureLimit` requests (`FORS.SigningTranscript.Valid`). Against an adversary
of at most `signatureLimit` requests it is the statement's game
(`Transport.forgeryGame_winningCondition_congr`). -/
noncomputable def limitedScheme :=
  { RandomPermutationModel.sufCmaScheme with
    winningCondition := fun log forgery ↦
      decide (log.length ≤ signatureLimit ∧
        ¬SignerReturnedForgery id log forgery.message forgery.signature) }

/-- **The same winning condition**, the log read through the signatures' map. -/
theorem win_eq (log : QueryLog (FORS.Message →ₒ Option FORS.Signature)) (forgery : Forgery) :
    limitedScheme.winningCondition
        (Transport.mapLog (Option.map ofModelSignature) log) forgery =
      crateScheme.win log (toModelForgery forgery) := by
  simp only [limitedScheme, crateScheme, modelScheme, FORS.SigningTranscript.Valid,
    FORS.SigningTranscript.Contains, SignerReturnedForgery, toModelForgery]
  have hlength : List.length (Transport.mapLog (Option.map ofModelSignature) log) =
      List.length log :=
    Transport.mapLog_length _ _
  congr 1
  apply propext
  refine and_congr ⟨fun h ↦ hlength.symm.le.trans h, fun h ↦ hlength.le.trans h⟩ (not_congr ?_)
  constructor
  · rintro ⟨entry, hentry, hmessage, hanswer⟩
    obtain ⟨original, horiginal, rfl⟩ := Transport.mem_mapLog.mp hentry
    exact ⟨original, horiginal, hmessage, (map_eq_some_iff _ _).mp hanswer⟩
  · rintro ⟨entry, hentry, hmessage, hanswer⟩
    exact ⟨⟨entry.1, Option.map ofModelSignature entry.2⟩,
      Transport.mem_mapLog.mpr ⟨entry, hentry, rfl⟩, hmessage, (map_eq_some_iff _ _).mpr hanswer⟩

end Sphincs.Model
