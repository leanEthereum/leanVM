module

public import Quantum.Qrom.SufCma.Game
public import Quantum.SufCma.GamePar

@[expose] public section

/-!
# The parallel-query SUF-CMA game in the QROM

A parallel adversary calls the random function in rounds: one call of the port `.hashPar w` acts
on the register `Fin w → HashDomain × HashOutput`, `w` query registers at once. Its signing
requests stay single classical calls (`.sign r`). A round of width `w` is, by definition, its `w`
calls on the components in the order `0, …, w - 1` (`toSeq`, through `Quantum.Par.seqCalls`): for a
fixed function these are basis maps on disjoint registers, so a round is the product unitary
`|x_i, y_i⟩ ↦ |x_i, y_i + H x_i⟩` in every slot (`run₂_challenged_hashRound`). The game of a
parallel adversary is the game `Quantum.Qrom.SufCma.game` of its serialization (`winProbPar_eq`).
Structure and names follow the QRPM game `Quantum.SufCma.GamePar`.

* `widthCharge` counts the calls of a round (`w`), `roundCharge` the rounds (`1` each, so a path
  of `d` rounds has query depth `d`), `signChargePar` the signing requests.
* `QuantumStronglyUnforgeablePar sch limit bound`: every parallel adversary making at most `q`
  calls of `H` in at most `d` rounds and at most `limit` signing requests on every path wins with
  probability at most `bound q d`.

## Main statements

* `isChargeBound_toSeq_hash`, `isChargeBound_toSeq_sign`: the serialized adversary makes at most
  `q` calls of `H` when the parallel one has total width at most `q`, and the same signing
  requests.
* `QuantumStronglyUnforgeable.par`: the sequential theorem gives the parallel one with the bound
  `fun q _ ↦ bound q`.
* `run₂_challenged_hashRound`: fidelity of a round of the game for each function, from the
  generic `Quantum.QuantumRuntime.run₂_seqCalls_eq_relabel` of `Quantum.SufCma.GamePar`.
-/

open IPFunctor
open scoped ENNReal

universe u v

namespace Quantum.Qrom.SufCma

open Common HashSig SubInstrument
open Quantum.Par (roundIn roundOut seqCalls seqCalls_succ isChargeBound_seqCalls)

/-! ## The parallel adversary -/

/-- The parallel adversary's ports: a round of `w` calls of `H`, and one classical signing port
per request. -/
inductive AdvPortPar (Req : Type) where
  /-- A round of `w` calls of `H`. -/
  | hashPar (w : ℕ)
  /-- The signing request `r`. -/
  | sign (r : Req)

variable (PK Req Resp F : Type)

/-- The parallel adversary's signature: a round of width `w` acts on
`Fin w → HashDomain × HashOutput` (the `w` query registers, each input then response) and reports
nothing; a signing port acts on no register and reports the signer's answer. -/
@[reducible]
def advSpecPar : QuantumOracleSpec.{0, 0} where
  Port := AdvPortPar Req
  In
    | .hashPar w => QReg.of (Fin w → HashDomain × HashOutput)
    | .sign _ => QReg.of Unit
  Out
    | .hashPar w => QReg.of (Fin w → HashDomain × HashOutput)
    | .sign _ => QReg.of Unit
  Result
    | .hashPar _ => Unit
    | .sign _ => Resp

/-- A parallel quantum SUF-CMA adversary: from the public key, a program over `advSpecPar`. -/
abbrev AdversaryPar := PK → QComp (advSpecPar Req Resp) (QReg.of Unit) (QReg.of Unit) F

variable {PK Req Resp F}

/-- A round costs its width, a signing request nothing: the number of calls of `H`. -/
def widthCharge : AdvPortPar Req → ℕ
  | .hashPar w => w
  | .sign _ => 0

/-- A round costs one, a signing request nothing: the query depth. -/
def roundCharge : AdvPortPar Req → ℕ
  | .hashPar _ => 1
  | .sign _ => 0

/-- A signing request costs one, a round nothing. -/
def signChargePar : AdvPortPar Req → ℕ
  | .hashPar _ => 0
  | .sign _ => 1

/-- A charge on the parallel ports as a charge on commands: a call of port `i` costs `c i`, a
local operation nothing. -/
def cmdChargePar {L : LocalSig.{u, v}} (c : AdvPortPar Req → ℕ) (A : QReg) :
    QuantumComp.Cmd L (advSpecPar Req Resp) A → ℕ
  | .prim _ => 0
  | .query i _ _ => c i

/-! ## Serialization -/

/-- **A round of width `w`** with the adversary's register
`A ≃ (Fin w → HashDomain × HashOutput) × E`: its `w` calls of `H` on the components, in order,
ending on the register of the round's output. -/
noncomputable def hashRound (w : ℕ) (E : QReg) {A : QReg}
    (ℓ : A ≃ (advSpecPar Req Resp).In (.hashPar w) × E) :
    QComp (advSpec Req Resp) A (QReg.of ((advSpecPar Req Resp).Out (.hashPar w) × E))
      (Fin w → Unit) :=
  seqCalls (spec := advSpec Req Resp) (fun _ ↦ AdvPort.hash) E ℓ (Equiv.refl _)

/-- **Serialization**: a local operation stays, a round becomes its calls in order
(`hashRound`), and a signing request stays. -/
noncomputable def toSeq :
    CommandSubstitution
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpecPar Req Resp))
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec Req Resp))
  | _, .prim o => QuantumComp.primBind o fun b ↦ QuantumComp.pure ⟨ULift.up b, rfl⟩
  | _, .query (.hashPar w) E ℓ =>
      QuantumComp.bind (hashRound w E ℓ) fun _ l ↦ QuantumComp.pure ⟨ULift.up (), l.1.symm⟩
  | _, .query (.sign r) E ℓ =>
      QuantumComp.queryBind (spec := advSpec Req Resp) (.sign r) E ℓ fun b ↦
        QuantumComp.pure ⟨ULift.up b, rfl⟩

/-- The serialized adversary: every round replaced by its calls in order. -/
noncomputable def serialize (A : AdversaryPar PK Req Resp F) : Adversary PK Req Resp F :=
  fun pk ↦ IFreeM.substitute toSeq (A pk)

/-! ## Budgets of the serialized adversary -/

/-- **Calls of the serialized adversary**: a parallel adversary of total width at most `q` is
serialized to one making at most `q` calls of `H`. -/
theorem isChargeBound_toSeq_hash {A B : QReg} {α : Type}
    {x : QComp (advSpecPar Req Resp) A B α} {q : ℕ}
    (hx : IFreeM.IsChargeBound x (cmdChargePar widthCharge) q) :
    IFreeM.IsChargeBound (IFreeM.substitute toSeq x) (cmdCharge hashCharge) q := by
  refine IFreeM.IsChargeBound.substitute toSeq (fun A c ↦ ?_) hx
  rcases c with o | ⟨w | r, E, ℓ⟩
  · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨le_rfl, fun _ ↦ trivial⟩
  · refine IFreeM.IsChargeBound.mono (IFreeM.isChargeBound_bind
      (isChargeBound_seqCalls (k := fun _ ↦ 1) (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ le_rfl) _ _ _)
      fun _ _ ↦ IFreeM.isChargeBound_pure _ 0) ?_
    simp [cmdChargePar, widthCharge]
  · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨Nat.zero_le _, fun _ ↦ trivial⟩

/-- **Signing requests of the serialized adversary**: the same as the parallel adversary's. -/
theorem isChargeBound_toSeq_sign {A B : QReg} {α : Type}
    {x : QComp (advSpecPar Req Resp) A B α} {n : ℕ}
    (hx : IFreeM.IsChargeBound x (cmdChargePar signChargePar) n) :
    IFreeM.IsChargeBound (IFreeM.substitute toSeq x) (cmdCharge signCharge) n := by
  refine IFreeM.IsChargeBound.substitute toSeq (fun A c ↦ ?_) hx
  rcases c with o | ⟨w | r, E, ℓ⟩
  · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨le_rfl, fun _ ↦ trivial⟩
  · refine IFreeM.IsChargeBound.mono (IFreeM.isChargeBound_bind
      (isChargeBound_seqCalls (k := fun _ ↦ 0) (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ le_rfl) _ _ _)
      fun _ _ ↦ IFreeM.isChargeBound_pure _ 0) ?_
    simp [cmdChargePar, signChargePar]
  · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨le_rfl, fun _ ↦ trivial⟩

/-! ## The game -/

variable {Seed SK : Type} (sch : SchemeOver RomOracles Seed PK SK Req Resp F)

/-- **The winning probability of a parallel adversary**: that of its serialization in the QROM
game. -/
noncomputable def winProbPar [Fintype Seed] (A : AdversaryPar PK Req Resp F) : ℝ≥0∞ :=
  winProb sch (serialize A)

/-- **Parallel SUF-CMA of `sch` against quantum adversaries in the QROM**: every parallel adversary
that makes at most `q` calls of `H` in at most `d` rounds and at most `limit` signing requests on
every path wins with probability at most `bound q d`. -/
def QuantumStronglyUnforgeablePar [Fintype Seed] (limit : ℕ) (bound : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ q d (A : AdversaryPar PK Req Resp F),
    (∀ pk, IFreeM.IsChargeBound (A pk) (cmdChargePar widthCharge) q) →
    (∀ pk, IFreeM.IsChargeBound (A pk) (cmdChargePar roundCharge) d) →
    (∀ pk, IFreeM.IsChargeBound (A pk) (cmdChargePar signChargePar) limit) →
      winProbPar sch A ≤ bound q d

/-- **The serialized adversary is an adversary of the sequential game with the same winning
probability.** -/
theorem winProbPar_eq [Fintype Seed] (A : AdversaryPar PK Req Resp F) :
    winProbPar sch A = winProb sch (serialize A) :=
  rfl

/-- **The sequential theorem gives the parallel one**, with a bound that ignores the depth. -/
theorem QuantumStronglyUnforgeable.par [Fintype Seed] {limit : ℕ} {bound : ℕ → ℝ≥0∞}
    (h : QuantumStronglyUnforgeable sch limit bound) :
    QuantumStronglyUnforgeablePar sch limit fun q _ ↦ bound q :=
  fun q _ A hw _ hs ↦
    h q (serialize A) (fun pk ↦ isChargeBound_toSeq_hash (hw pk))
      fun pk ↦ isChargeBound_toSeq_sign (hs pk)

/-! ## Fidelity: a round is the product unitary -/

/-- The bijection of a round of the oracle of `H`: every slot adds `H` of its input into its
response register. -/
def parHashEquiv (H : HashDomain → HashOutput) (w : ℕ) :
    (Fin w → HashDomain × HashOutput) ≃ (Fin w → HashDomain × HashOutput) :=
  Equiv.piCongrRight fun _ ↦ oracleEquiv H

/-- The step of the oracle of `H` relabels along the oracle bijection of `H`. -/
theorem step_additiveOracleRuntime (H : HashDomain → HashOutput) :
    (additiveOracleRuntime H).step () =
      (relabel ((oracleEquiv H).prodCongr (Equiv.refl Unit))).map fun _ ↦ () := by
  rw [Quantum.SufCma.map_const_unit]
  exact frame_relabel _ _

/-- **A round against the oracle of `H`**: its calls relabel the exposed register along the
product oracle bijection `parHashEquiv H w`, `|x_i, y_i⟩ ↦ |x_i, y_i + H x_i⟩` in every slot,
then along `post`. -/
theorem run₂_seqCalls_additiveOracleRuntime (H : HashDomain → HashOutput) {w : ℕ} (E : QReg)
    {A B : QReg} (ℓ : A ≃ roundIn romSpec (fun _ : Fin w ↦ ()) × E)
    (post : roundOut romSpec (fun _ : Fin w ↦ ()) × E ≃ B) :
    (additiveOracleRuntime H).run₂ .instruments (seqCalls (fun _ : Fin w ↦ ()) E ℓ post) =
      (relabel (((ℓ.trans ((parHashEquiv H w).prodCongr (Equiv.refl E))).trans
        post).prodCongr (Equiv.refl Unit))).map fun _ _ ↦ () :=
  (additiveOracleRuntime H).run₂_seqCalls_eq_relabel _ (fun _ ↦ oracleEquiv H) (fun _ ↦ ())
    (fun _ ↦ step_additiveOracleRuntime H) E ℓ post

/-- The challenger passes a hash call through. -/
theorem challenged_queryBind_hash (sk : SK) (E : QReg) {A B : QReg} {α : Type}
    (ℓ : A ≃ (advSpec Req Resp).In .hash × E)
    (k : Unit → QComp (advSpec Req Resp) (QReg.of ((advSpec Req Resp).Out .hash × E)) B α) :
    challenged sch sk (QuantumComp₂.queryBind .hash E ℓ k) =
      QuantumComp₂.queryBind (spec := romSpec) () E ℓ fun r ↦ challenged sch sk (k r) :=
  rfl

/-- The challenger commutes with relabelling the return value. -/
theorem challenged_map (sk : SK) {A B : QReg} {α β : Type} (g : α → β)
    (x : QComp (advSpec Req Resp) A B α) :
    challenged sch sk (x.map g) = (challenged sch sk x).map g := by
  rw [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.map_eq_bind_pure]
  show IFreeM.substitute (challenge sch sk) (IFreeM.bind x _) =
    IFreeM.bind (IFreeM.substitute (challenge sch sk) x) _
  refine (IFreeM.substitute_bind _ _ _).trans
    (congrArg (IFreeM.bind _) (funext fun _ ↦ funext fun p ↦ ?_))
  obtain ⟨h, _⟩ := p
  cases h
  rfl

/-- **The challenger keeps a round of hash calls**: the same calls of `romSpec`. -/
theorem challenged_seqCalls (sk : SK) : ∀ {w : ℕ} (E : QReg) {A B : QReg}
    (ℓ : A ≃ roundIn (advSpec Req Resp) (fun _ : Fin w ↦ .hash) × E)
    (post : roundOut (advSpec Req Resp) (fun _ : Fin w ↦ .hash) × E ≃ B),
    challenged sch sk (seqCalls (fun _ : Fin w ↦ AdvPort.hash) E ℓ post) =
      seqCalls (spec := romSpec) (fun _ : Fin w ↦ ()) E ℓ post
  | 0, _, _, _, _, _ => rfl
  | _ + 1, E, _, _, ℓ, post => by
    rw [seqCalls_succ, seqCalls_succ]
    refine (challenged_queryBind_hash sch sk _ _ _).trans
      (congrArg (QuantumComp₂.queryBind _ _ _) (funext fun r ↦ ?_))
    rw [challenged_map]
    exact congrArg (QuantumComp₂.map _) (challenged_seqCalls sk _ _ _)

/-- **Fidelity of a round in the game.** Against the oracle of `H`, a round of width `w` of the
serialized adversary, as the challenger runs it, is the product unitary
`|x_i, y_i⟩ ↦ |x_i, y_i + H x_i⟩` in every slot of the exposed register. -/
theorem run₂_challenged_hashRound (H : HashDomain → HashOutput) (sk : SK) (w : ℕ) (E : QReg)
    {A : QReg} (ℓ : A ≃ (advSpecPar Req Resp).In (.hashPar w) × E) :
    (additiveOracleRuntime H).run₂ .instruments (challenged sch sk (hashRound w E ℓ)) =
      (relabel ((ℓ.trans ((parHashEquiv H w).prodCongr (Equiv.refl E))).prodCongr
        (Equiv.refl Unit))).map fun _ _ ↦ () := by
  rw [hashRound, challenged_seqCalls, run₂_seqCalls_additiveOracleRuntime]
  rfl

end Quantum.Qrom.SufCma

end
