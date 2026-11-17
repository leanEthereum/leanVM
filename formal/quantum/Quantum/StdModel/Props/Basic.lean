module

public import Quantum.StdModel.World
public import VCVio.OracleComp.Constructions.SampleableType.Basic

@[expose] public section

/-!
# Property games over an oracle world: the common frame

Every property of the standard-model reduction (`Quantum.StdModel.Props.Prf`, `Tcr`, `Cpre`,
`EncTcr`, `Itsr`) is a game between a classical challenger and a quantum adversary. The adversary
has superposition access to the world's hash ports (`advSpec W.spec R`, ports `.hash p`) and
classical access to the challenger's ports (`.call q`, answered in `R.Range q`). The challenger is a
classical program over the world's classical oracles `W.Oracles` (coins and the primitive): it
computes Keccak-256 by `W.hash`, so that at a fixed table its hash calls are classical basis calls
of the same oracle the adversary queries.

* `Experiment W R Pub Out`: a challenger: its secret state and its sampling (`setup`), the public
  input of the adversary (`pub`), the answers to classical queries (`answer`, stateless given the
  setup) and the final decision (`judge`), which sees the setup, the ordered transcript of the
  classical queries and their answers (`QueryLog R`, kept by `withCallLog`) and the adversary's
  output.
* `Experiment.game E A`: the game as a program over `W.spec`; the adversary runs once, its
  classical ports substituted by the challenger (`answerSub`), its hash ports forwarded.
* `Experiment.succAt E tab A`: the probability that the game returns `true` at the fixed table
  `tab` (the standard model at `tab = Keccak-f`).

Restrictions on the adversary (distinct tweaks, phase order) are part of `judge`: a transcript
that breaks them loses. Since the transcript is classical and ordered, this is equivalent to a
challenger that refuses such queries. Two-phase games give the public parameter through a classical
`reveal` port; queries before the first reveal are phase 1 (`phaseTwo` is the rest).

* `TwColl`: a collection of tweakable hashes `Th_l(P, T, M) = trunc (H (layout l P T M))` sharing
  the public parameter `P`; `TwHash` is a single one.

## Instance obligations

The games are generic in the layouts; an instance that breaks one of the following makes its game
trivially winnable, so each instance must prove it (with the distinct-input lemmas of the input
formats):

* (a) `TwColl.LengthLe C Qrom.maxLen` (and the same bound for every other hashed input): in the
  QROM world, inputs longer than `Qrom.maxLen` bytes all hash to `0`, so two long inputs collide.
* (b) For KIM-PRF, `x ↦ (fmt x, trunc x)` is injective (`Props.KimFmtInjective`): two formats
  with the same bytes and the same truncation give equal real outputs and independent ideal ones.
* (c) `TwColl.TweakSeparated D C`: the evaluation collection `D` never produces the bytes of an
  input of the challenge collection `C` under a different tweak. The games restrict evaluations
  by tweak values, which means "no access to a challenge function at the hidden `P`" only under
  this separation.
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal

universe u v w w₁

namespace Quantum.StdModel.Props

open HashSig

/-! ## Decisions and sampling -/

/-- A proposition as a boolean, by classical decision. -/
noncomputable def holds (p : Prop) : Bool :=
  @decide p (Classical.propDecidable p)

theorem holds_eq_true {p : Prop} : holds p = true ↔ p := by
  unfold holds
  exact @decide_eq_true_iff p (Classical.propDecidable p)

/-- A uniform element of `α` drawn by the challenger from the world's coins. -/
noncomputable def sample (W : OracleWorld) (α : Type) [SampleableType α] :
    OracleComp W.Oracles α :=
  liftComp ($ᵗ α) W.Oracles

/-! ## Phases of the classical transcript -/

/-- The transcript from the first query satisfying `isReveal` on (phase 2); empty if there is
none. -/
def phaseTwo {Q : Type} {R : OracleSpec.{0, 0} Q} (isReveal : Q → Bool) (log : QueryLog R) :
    QueryLog R :=
  log.dropWhile fun e ↦ !isReveal e.1

/-! ## The challenger -/

variable (W : OracleWorld) {Q : Type} {R : OracleSpec.{0, 0} Q}

/-- The answer to the classical query `q` with the adversary's register `A ≃ Unit × E` held:
relabel the register, then run the challenger's classical answer with the world's oracles. -/
noncomputable def callTree (ans : (q : Q) → OracleComp W.Oracles (R.Range q)) (q : Q)
    (E : QReg) {A : QReg} (ℓ : A ≃ (advSpec W.spec R).In (.call q) × E) :
    QComp W.spec A (QReg.of ((advSpec W.spec R).Out (.call q) × E)) (R.Range q) :=
  (QComp.act (B := QReg.of ((advSpec W.spec R).Out (.call q) × E))
    (SubInstrument.relabel ℓ)).bind fun _ ↦ (ans q).toQuantumAt (W.impl _)

/-- **The challenger as a substitution**: a local operation stays, a hash call becomes the same
call of `W.spec`, and a classical query is answered by `ans` (`callTree`). -/
noncomputable def answerSub (ans : (q : Q) → OracleComp W.Oracles (R.Range q)) :
    CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec W.spec R))
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} W.spec)
  | _, .prim o => QuantumComp.primBind o fun b ↦ QuantumComp.pure ⟨ULift.up b, rfl⟩
  | _, .query (.hash p) E ℓ =>
      QuantumComp.queryBind (spec := W.spec) p E ℓ fun r ↦ QuantumComp.pure ⟨ULift.up r, rfl⟩
  | _, .query (.call q) E ℓ =>
      QuantumComp.bind (callTree W ans q E ℓ) fun _ l ↦
        QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- The adversary's program with the challenger `ans` substituted, on `W.spec`. -/
noncomputable def answered (ans : (q : Q) → OracleComp W.Oracles (R.Range q)) {A B : QReg}
    {α : Type} (x : QComp (advSpec W.spec R) A B α) : QComp W.spec A B α :=
  IFreeM.substitute (answerSub W ans) x

/-- The world's classical oracles are answered losslessly. -/
def ImplLossless : Prop :=
  ∀ (B : QReg) (t : W.Oracles.Domain), (W.impl B t).Lossless .instruments

variable {W} in
/-- The challenger keeps losslessness. -/
theorem lossless_substitute_answerSub (hW : ImplLossless W)
    (ans : (q : Q) → OracleComp W.Oracles (R.Range q)) {X : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} (advSpec W.spec R) X A)
    (hx : x.Lossless .instruments) :
    QuantumComp.Lossless (spec := W.spec) LocalSig.Interp.instruments
      (IFreeM.substitute (answerSub W ans) x) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => trivial
  | liftBind A c next ih =>
    rw [IFreeM.substitute_liftBind]
    refine QuantumComp.Lossless.bind ?_ fun u ⟨b, h⟩ ↦ ?_
    · rcases c with o | ⟨p | q, E, ℓ⟩
      · exact (QuantumComp.lossless_primBind_iff _ _).mpr ⟨hx.1, fun _ ↦ trivial⟩
      · exact (QuantumComp.lossless_queryBind_iff _ _ _ _).mpr fun _ ↦ trivial
      · exact QuantumComp.Lossless.bind
          (QuantumComp₂.lossless_bind (QComp.lossless_act (SubInstrument.lossless_relabel _))
            fun _ ↦ lossless_toQuantumAt (hW _) _) fun _ _ ↦ trivial
    · subst h
      exact ih b (hx.2 b)

variable (R) in
/-- A property adversary: from the public input, a quantum program over the world's hash ports
and the challenger's classical ports that keeps its own registers and returns an output. -/
abbrev Adversary (Pub Out : Type) :=
  Pub → QComp (advSpec W.spec R) (QReg.of Unit) (QReg.of Unit) Out

variable (R) in
/-- **A classical challenger** of a property game over the world `W`. -/
structure Experiment (Pub Out : Type) : Type 1 where
  /-- The challenger's secret state. -/
  State : Type
  /-- Sample the state (coins and hash calls). -/
  setup : OracleComp W.Oracles State
  /-- The adversary's public input. -/
  pub : State → Pub
  /-- The answer to a classical query. -/
  answer : State → (q : Q) → OracleComp W.Oracles (R.Range q)
  /-- The decision from the state, the ordered transcript and the adversary's output. -/
  judge : State → QueryLog R → Out → OracleComp W.Oracles Bool

namespace Experiment

variable {W} {Pub Out : Type} (E : Experiment W R Pub Out)

/-- **The property game**: the challenger's setup, the adversary once with its classical queries
answered and logged, then the challenger's decision. -/
noncomputable def game (A : Adversary W R Pub Out) :
    QComp W.spec (QReg.of Unit) (QReg.of Unit) Bool :=
  (E.setup.toQuantumAt (W.impl _)).bind fun s ↦
    (answered W (E.answer s) (withCallLog (A (E.pub s)))).bind fun run ↦
      (E.judge s run.2 run.1).toQuantumAt (W.impl _)

/-- **The success probability at the fixed table `tab`.** -/
noncomputable def succAt (tab : W.Tab) (A : Adversary W R Pub Out) : ℝ≥0∞ :=
  W.probAt tab (E.game A)

/-- **The game of a lossless adversary is lossless.** -/
theorem lossless_game (hW : ImplLossless W) {A : Adversary W R Pub Out}
    (hA : ∀ p, (A p).Lossless .instruments) : (E.game A).Lossless .instruments :=
  QuantumComp₂.lossless_bind (lossless_toQuantumAt (hW _) _) fun s ↦
    QuantumComp₂.lossless_bind
      (lossless_substitute_answerSub hW _ _ (lossless_withCallLog (hA (E.pub s))))
      fun _ ↦ lossless_toQuantumAt (hW _) _

end Experiment

/-! ## Tweakable hashes over the world -/

/-- **A collection of tweakable hashes** sharing a public parameter: the function `l` maps
`(P, T, M)` to `trunc (H (layout l P T M))`, with `H` the world's Keccak-256. -/
structure TwColl (Par Tw Fn : Type) (Msg : Fn → Type) (Out : Type) where
  /-- The hashed bytes. -/
  layout : (l : Fn) → Par → Tw → Msg l → HashInput
  /-- The truncation of the digest. -/
  trunc : HashOutput → Out

/-- A single tweakable hash. -/
abbrev TwHash (Par Tw Msg Out : Type) := TwColl Par Tw Unit (fun _ ↦ Msg) Out

/-- **The tweakable hash `Th_l(P, T, M)`**, computed by the challenger through the world. -/
noncomputable def TwColl.eval {Par Tw Fn Out : Type} {Msg : Fn → Type}
    (C : TwColl Par Tw Fn Msg Out) (l : Fn) (P : Par) (t : Tw) (m : Msg l) :
    OracleComp W.Oracles Out :=
  C.trunc <$> W.hash (C.layout l P t m)

/-- **Obligation (a)**: every input of the collection has at most `n` bytes. -/
def TwColl.LengthLe {Par Tw Fn Out : Type} {Msg : Fn → Type} (C : TwColl Par Tw Fn Msg Out)
    (n : ℕ) : Prop :=
  ∀ l P t m, (C.layout l P t m).length ≤ n

/-- **Obligation (c)**: an input of `D` with the bytes of an input of `C` has the same tweak. -/
def TwColl.TweakSeparated {Par Tw Fn Out EFn EOut : Type} {Msg : Fn → Type}
    {EMsg : EFn → Type} (D : TwColl Par Tw EFn EMsg EOut) (C : TwColl Par Tw Fn Msg Out) :
    Prop :=
  ∀ l P t m l' t' m', D.layout l' P t' m' = C.layout l P t m → t' = t

end Quantum.StdModel.Props

end
