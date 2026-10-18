import LeanVM.Protocol.LeanVM

/-!
# The leanVM front page, locked

Statement locks of `LeanVM/Protocol/LeanVM.lean`: the verifier for any hash, the deployed
verifier, completeness, knowledge soundness in the random-oracle model, and the numbers, with the
axioms each depends on.
-/

open LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol.LeanIsa LeanVM

example (prog : Program) (input : PublicInput) (proof : LeanVM.Proof) :
    verify prog input proof = Id.run (verifier LeanVM.Protocol.Blake2sHash.blake2sBytes prog
      input proof) := rfl

example {A : Adversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← experiment A}[z.1.2 = true ∧ SentinelSafe z.1.1.1.1 ∧
      ¬ ∃ t, extract z.1.1.1.1 z.1.1.1.2 z.2 z.1.1.2 = some t ∧
        ValidExecution z.1.1.1.1 z.1.1.1.2 t] ≤
      soundnessError Q :=
  knowledgeSoundness hA

/-- The adversary chooses the statement: a fixed statement is the special case of an adversary
that outputs it. -/
example (prog : Program) (input : PublicInput)
    (P : OracleComp LeanVM.Protocol.Compile.Rom.HashSpec LeanVM.Proof) {Q : ℕ}
    (hP : P.IsTotalQueryBound Q) :
    Pr{let z ← experiment ((fun proof ↦ ((prog, input), proof)) <$> P)}[Breaks extract z] ≤
      soundnessError Q :=
  knowledgeSoundness ((OracleComp.isQueryBound_map_iff P _ Q _ _).mpr hP)

example {Q : ℕ} (hQ : Q ≤ 2 ^ 64) : soundnessError Q ≤ (2 : ENNReal)⁻¹ ^ 63 :=
  soundnessError_le hQ

example {prog : Program} {input : PublicInput} {t : Trace prog}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ 28) {ρ : ℕ}
    (hρ : 1 ≤ ρ ∧ ρ ≤ 4) {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let z ← experiment (honestProver prog input t ρ fuel)}[z.1.2 = false] ≤
      completenessError fuel :=
  completeness hv hbudget hρ hfuel

example : completenessError (2 ^ 25) ≤ (2 : ENNReal)⁻¹ ^ 128 := completenessError_le

/-- The proofs of work have `17` bits. -/
example : LeanVM.Parameters.Whir.queryGrindingBits = 17 := rfl

/-- info: 'LeanVM.knowledgeSoundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms knowledgeSoundness

/-- info: 'LeanVM.completeness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms completeness

/--
info: 'LeanVM.completenessError_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms completenessError_le

/-! ## The statements of `LeanVM/Spec/Statement.lean` -/

example : KnowledgeSoundness := knowledgeSoundness_holds

example : Completeness := completeness_holds

/--
info: 'LeanVM.knowledgeSoundness_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms knowledgeSoundness_holds

/--
info: 'LeanVM.completeness_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms completeness_holds
