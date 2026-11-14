/-
  LeanVM.Protocol.Verifier.Phases

  The verifier's phases in normal form: each phase's spec lemma, which the proofs about the phase
  rewrite with instead of unfolding it.
-/

module

public import LeanVM.Protocol.Compile.Prog

/-!
# The phases, in normal form

A phase's normal form keeps its prover messages, challenges, grinds and commitments, and collapses
each run of pure steps between them (checks, `let`s, `liftOption`, the returned value) into one
`liftOption (xOf …)`, where `xOf` transcribes those steps in their order. The `_eq` lemma is proved
by `phase_nf` (`simp` with the collapsing rules, then `rfl`), and a spec structure says what a value
`xOf` returns satisfies. The proofs about a phase (each family's lemma: `allRet_*`, `costs_*`,
`moves_*`, `reads_*`, `noOpen_*`, the `*Pure` runs) rewrite with the `_eq` lemma and read the spec,
so a change to a phase's checks or returned value changes its `xOf`, here, and nothing else. A new
message, or a check between two messages where the phase had no pure steps, changes the lemma's
statement.

* step 1, `readAnnouncedSizes`: `readScalars`, then `sizesOf` (`readAnnouncedSizes_eq`, `SizesSpec`);
* step 2, `commitStack`: `commitShapeOf`, then the root (`commitStack_eq`); `readOod`: the grind, the
  point, the value, then `oodOf` (`readOod_eq`);
* step 5, `publicInputPhase`: the challenge, then `publicClaimsOf` (`publicInputPhase_eq`);
* step 7, `ringSwitch`: the grind, the challenges, then `ringOf` (`ringSwitch_eq`);
  `verifyStackedOpening`: its checks as one `require (StackedOk claims)`, which the guest's copy
  `verifyStackedOpeningNZ` shares, the challenge, then WHIR (`verifyStackedOpening_nf`).

The bus (`verifyBusBalance`), the table sumcheck (`tablePhase`) and the Keccak reduction
(`keccakPhase`) call sub-protocols between their checks and are not in normal form yet.
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

@[expose] public section

/-! ## Collapsing pure steps -/

theorem ret_eq_liftOption {α : Type} (a : α) : VerifierProgram.ret a = liftOption (some a) := rfl

theorem require_eq_liftOption (c : Prop) [Decidable c] :
    VerifierProgram.require c = liftOption (if c then some () else none) := by
  by_cases h : c <;> simp only [VerifierProgram.require, h, ↓reduceIte] <;> rfl

theorem liftOption_bind_liftOption {α β : Type} (o : Option α) (g : α → Option β) :
    (liftOption o).bind (fun a ↦ liftOption (g a)) = liftOption (o.bind g) := by
  cases o <;> rfl

theorem liftOption_bind_liftOption_bind {α β γ : Type} (o : Option α) (g : α → Option β)
    (k : β → VerifierProgram γ) :
    (liftOption o).bind (fun a ↦ (liftOption (g a)).bind k) = (liftOption (o.bind g)).bind k := by
  cases o <;> rfl

theorem guard_bind {β : Type} (c : Prop) [Decidable c] (f : Unit → Option β) :
    (if c then some () else none).bind f = if c then f () else none := by
  by_cases h : c <;> simp only [h, ↓reduceIte] <;> rfl

/-- A phase's normal form, from its definition: the pure steps collapsed into `liftOption`s, then
`rfl` against the transcriptions `xOf`. -/
macro "phase_nf" : tactic => `(tactic| (
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq, ret_eq_liftOption, require_eq_liftOption,
    liftOption_bind_liftOption, liftOption_bind_liftOption_bind, guard_bind, Option.bind_some] <;>
  rfl))

/-! ## Step 1: the announced sizes -/

/-- **What `readAnnouncedSizes` makes of the scalars it read**: its checks, in its order, and the
layout and rate it returns. -/
def sizesOf (bytecode : List K) (announced : List E) : Option (Layout × ℕ) :=
  if (announced.all fun value ↦ value.limb 1 = 0) then
    let logMemory := kToNat ((announced.headD 0).limb 0)
    let tableRows := ((announced.drop 1).take tables.length).map fun value ↦ kToNat (value.limb 0)
    let logInverseRate := kToNat ((announced.getLastD 0).limb 0)
    if 1 ≤ logInverseRate ∧ logInverseRate ≤ 4 then
      (buildLayout bytecode logMemory tableRows).bind fun layout ↦
        if Whir.minLogStack ≤ layout.stackLog ∧ layout.stackLog ≤ Whir.maxLogStack then
          some (layout, logInverseRate)
        else none
    else none
  else none

/-- **`readAnnouncedSizes`, normal form**: its reads, then its checks (`sizesOf`). -/
theorem readAnnouncedSizes_eq (bytecode : List K) :
    readAnnouncedSizes bytecode = VerifierProgram.readScalars (2 + tables.length) >>= fun announced ↦
      liftOption (sizesOf bytecode announced) := by
  unfold readAnnouncedSizes
  phase_nf

/-- What a value `readAnnouncedSizes` returns satisfies, of the scalars it read. -/
structure SizesSpec (bytecode : List K) (announced : List E) (x : Layout × ℕ) : Prop where
  limbs : announced.all fun value ↦ value.limb 1 = 0
  rate_ge : 1 ≤ x.2
  rate_le : x.2 ≤ 4
  rate : x.2 = kToNat ((announced.getLastD 0).limb 0)
  layout : buildLayout bytecode (kToNat ((announced.headD 0).limb 0))
    (((announced.drop 1).take tables.length).map fun value ↦ kToNat (value.limb 0)) = some x.1
  stack_ge : Whir.minLogStack ≤ x.1.stackLog
  stack_le : x.1.stackLog ≤ Whir.maxLogStack

theorem sizesOf_spec {bytecode : List K} {announced : List E} {x : Layout × ℕ}
    (h : sizesOf bytecode announced = some x) : SizesSpec bytecode announced x := by
  simp only [sizesOf, Option.ite_none_right_eq_some, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨h1, h2, layout, hb, h3, rfl⟩ := h
  exact ⟨h1, h2.1, h2.2, rfl, hb, h3.1, h3.2⟩

/-! ## Step 2: the stack's root and its out-of-domain sample -/

/-- The shape of the stack's root, from the ladder's first level. -/
def commitShapeOf (logN logInvRate : ℕ) : Option (ℕ × ℕ) :=
  match Whir.ladder logN logInvRate with
  | some (level :: _) => some (levelShape logN level (2 ^ level.fold))
  | _ => none

theorem commitShapeOf_spec {logN logInvRate : ℕ} {shape : ℕ × ℕ}
    (h : commitShapeOf logN logInvRate = some shape) :
    ∃ level rest, Whir.ladder logN logInvRate = some (level :: rest) ∧
      shape = levelShape logN level (2 ^ level.fold) := by
  unfold commitShapeOf at h
  split at h
  · next level rest hl => exact ⟨level, rest, hl, (Option.some.inj h).symm⟩
  · cases h

/-- **`commitStack`, normal form**: the root's shape (`commitShapeOf`), then the root. -/
theorem commitStack_eq (logN logInvRate : ℕ) :
    commitStack logN logInvRate = liftOption (commitShapeOf logN logInvRate) >>= fun shape ↦
      VerifierProgram.readCommitment shape.1 shape.2 := by
  unfold commitStack commitShapeOf
  simp only [VerifierProgram.bind_eq]
  cases Whir.ladder logN logInvRate with
  | none => rfl
  | some config => cases config <;> rfl

/-- The out-of-domain claim at the point `z`, its value read. -/
def oodStackClaim (z : List E) (value : E) : StackClaim := (fun x ↦ eqEval z x, value)

/-- What `readOod` makes of its point and value. -/
def oodOf (z : List E) (value : E) : Option StackClaim := some (oodStackClaim z value)

/-- **`readOod`, normal form**: the grind, the point, the value, then `oodOf`. -/
theorem readOod_eq (stackLog : ℕ) :
    readOod stackLog = VerifierProgram.grindProofOfWork Whir.oodGrindingBits >>= fun _ ↦
      VerifierProgram.sampleChallenges stackLog >>= fun z ↦ VerifierProgram.readScalar >>= fun value ↦
        liftOption (oodOf z value) := by
  unfold readOod
  phase_nf

/-! ## Step 5: the public input -/

/-- The public input's claims at the challenge. -/
def publicClaims (layout : Layout) (publicInput : Digest) (publicChallenge : E) : List ColumnClaim :=
  let halves := digestHalves publicInput
  let publicLimbs := ([0, 1] : List (Fin 2)).map fun limb ↦
    multilinearEval [ofK (halves.1.limb limb), ofK (halves.2.limb limb)] [publicChallenge]
  let publicPoint := publicChallenge ::
    List.replicate ((layout.placement memory0).variableCount - 1) 0
  List.zipWith (fun column value ↦ ⟨column, publicPoint, value⟩) [memory0, memory1] publicLimbs

/-- What `publicInputPhase` makes of its challenge. -/
def publicClaimsOf (layout : Layout) (publicInput : Digest) (publicChallenge : E) :
    Option (List ColumnClaim) :=
  some (publicClaims layout publicInput publicChallenge)

theorem publicClaimsOf_spec {layout : Layout} {publicInput : Digest} {c : E} {cl : List ColumnClaim}
    (h : publicClaimsOf layout publicInput c = some cl) : cl = publicClaims layout publicInput c := by
  simp only [publicClaimsOf, Option.some.injEq] at h
  exact h.symm

/-- **`publicInputPhase`, normal form**: the challenge, then `publicClaimsOf`. -/
theorem publicInputPhase_eq (layout : Layout) (publicInput : Digest) :
    publicInputPhase layout publicInput = VerifierProgram.sampleChallenge >>= fun c ↦
      liftOption (publicClaimsOf layout publicInput c) := by
  unfold publicInputPhase
  phase_nf

/-! ## Step 7: ring switching and the stacked opening -/

/-- The ring switch's target and weight at its challenges. -/
def ringResult (point s challenges : List E) : E × (List E → E) :=
  let f := challenges.take ringMapWidth
  let g := challenges.drop ringMapWidth
  let coefficients := ringCoefficients f g
  (ringTarget s f g, fun rPrime ↦ ringWeight point rPrime coefficients)

/-- What `ringSwitch` makes of its challenges. -/
def ringOf (point s challenges : List E) : Option (E × (List E → E)) :=
  some (ringResult point s challenges)

/-- **`ringSwitch`, normal form**: the grind, the challenges, then `ringOf`. -/
theorem ringSwitch_eq (point s : List E) :
    ringSwitch point s = VerifierProgram.grindProofOfWork Whir.batchGrindingBits >>= fun _ ↦
      VerifierProgram.sampleChallenges (2 * ringMapWidth) >>= fun challenges ↦
        liftOption (ringOf point s challenges) := by
  unfold ringSwitch
  phase_nf

/-- The stacked opening's checks on its claims, as one condition. -/
def StackedOk (claims : List StackClaim) : Prop := claims.length ≤ maxStackedClaims

instance (claims : List StackClaim) : Decidable (StackedOk claims) :=
  inferInstanceAs (Decidable (claims.length ≤ maxStackedClaims))

theorem StackedOk.length_le {claims : List StackClaim} (h : StackedOk claims) :
    claims.length ≤ maxStackedClaims := h

theorem stackedOk_of {claims : List StackClaim} (h : claims.length ≤ maxStackedClaims) :
    StackedOk claims := h

theorem require_bind_require {β : Type} (a b : Prop) [Decidable a] [Decidable b] (k : Unit → VerifierProgram β) :
    (VerifierProgram.require a).bind (fun _ ↦ (VerifierProgram.require b).bind k) =
      (VerifierProgram.require (a ∧ b)).bind k := by
  by_cases ha : a <;> by_cases hb : b <;> simp only [VerifierProgram.require, ha, hb, and_self, and_false,
    false_and, ↓reduceIte] <;> rfl

/-- A phase whose only pure steps are checks, from its definition: consecutive `require`s merged into one. -/
macro "require_nf" : tactic => `(tactic| (simp only [VerifierProgram.bind_eq, require_bind_require] <;> rfl))

/-- **`verifyStackedOpening`, normal form**: its checks (`StackedOk`), the challenge, then WHIR on the
batched claim. -/
theorem verifyStackedOpening_nf (stackLog logInvRate : ℕ) (claims : List StackClaim) :
    verifyStackedOpening stackLog logInvRate claims =
      (VerifierProgram.require (StackedOk claims)).bind fun _ ↦ VerifierProgram.sampleChallenge.bind fun c ↦
        verifyWhir stackLog logInvRate (dot (powers c claims.length) (claims.map (·.2)))
          fun point ↦ dot (powers c claims.length) (claims.map fun cl ↦ cl.1 point) := by
  unfold verifyStackedOpening
  require_nf

end
end LeanVM.Protocol.Verifier
