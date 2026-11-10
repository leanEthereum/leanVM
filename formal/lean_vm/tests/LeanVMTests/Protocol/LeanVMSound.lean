import LeanVM.Protocol.LeanVMSound
import LeanVM.Protocol.ErrorBounds
import LeanVM.Protocol.WithHash

/-!
# leanVM's knowledge soundness, locked

Statement locks of `LeanVM/Protocol/LeanVMSound.lean`: the verifier for any hash and permutation,
the deployed verifier, knowledge soundness in the two-oracle random-oracle model (a step of the
proof of `LeanVM.KnowledgeSoundness`, locked in `LeanVMTests.Protocol.LeanVMRpm`), and the
numbers, with the axioms each depends on.
-/

open LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol.LeanIsa LeanVM
open LeanVM.Protocol.KeccakHash

example (prog : LeanIsaProgram) (input : PublicInput) (proof : LeanVM.Protocol.Compile.Proof) :
    verify prog input proof = Id.run (verifierWithHash (m := Id) keccak256 keccakF1600 prog input proof) :=
  rfl

example {A : Adversary} {Q : ℕ}
    (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← experiment A}[z.1.2 = true ∧
      ¬ ∃ t, extractor z.1.1.1.1 z.1.1.1.2 z.2.2 z.1.1.2 = some t ∧
        ValidExecution z.1.1.1.1 z.1.1.1.2 t] ≤
      soundnessError Q :=
  knowledgeSoundnessRom hA

/-- The adversary chooses the statement: a fixed statement is the special case of an adversary
that outputs it. -/
example (prog : LeanIsaProgram) (input : PublicInput)
    (P : OracleComp KeccakCalls LeanVM.Protocol.Compile.Proof) {Q : ℕ}
    (hP : P.IsTotalQueryBound Q) :
    Pr{let z ← experiment ((fun proof ↦ ((prog, input), proof)) <$> P)}[Breaks extractor z] ≤
      soundnessError Q :=
  knowledgeSoundnessRom ((OracleComp.isQueryBound_map_iff P _ Q _ _).mpr hP)

/-- The numbers: `13261` verifier queries, `2^-125` per message, a collision term of `5` per pair
of queries. -/
example (Q : ℕ) : soundnessError Q =
    ((Q + 13261 : ℕ) : ENNReal) *
        ((2 : ENNReal)⁻¹ ^ 125 + ((5 * (Q + 13261) : ℕ) : ENNReal) / 2 ^ 256) +
      ((13261 : ℕ) : ENNReal) / 2 ^ 256 := rfl

example {Q : ℕ} (hQ : Q ≤ 2 ^ 64) : soundnessError Q ≤ (2 : ENNReal)⁻¹ ^ 60 :=
  soundnessError_le hQ

/-- The query positions' proofs of work have `17` bits. -/
example : LeanVM.Parameters.Whir.queryGrindingBits = 17 := rfl

/-- info: 'LeanVM.knowledgeSoundnessRom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms knowledgeSoundnessRom

/--
info: 'LeanVM.soundnessError_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms soundnessError_le

/-! ## The statement of `LeanVM/Protocol/Rom/Statement.lean` -/

example : KnowledgeSoundnessRom := knowledgeSoundnessRom_holds

/--
info: 'LeanVM.knowledgeSoundnessRom_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms knowledgeSoundnessRom_holds
