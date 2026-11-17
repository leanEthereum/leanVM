module

public import Quantum.Qrom.Classical
public import Quantum.Qrom.SufCma.Game

@[expose] public section

/-!
# The quantum SUF-CMA game in the QROM on classical adversaries

A classical adversary of `forgeryGameOver RomOracles`, an `OracleComp` over coins, `H` and the
signing oracle, is a quantum adversary of `Quantum.Qrom.SufCma.game` that asks every query
classically (`classicalAdversary`: coins by uniform coins, `H x` by a basis call of the port
`.hash` at `(x, 0)`, a signing request by the call of its port). Its quantum game, with the
challenger substituted, runs against each `H` as the forgery game after the seed with its queries
answered by `H` (`classicalOn_game`), so by `Quantum.Qrom.Classical` it wins with the probability
of the classical game in the random-oracle model: `winProb_classicalAdversary`. Structure and
names follow `Quantum.SufCma.Classical`.
-/

open IPFunctor OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Quantum.Qrom.SufCma

open Common HashSig

variable {Seed PK SK Req Resp F : Type} (sch : SchemeOver RomOracles Seed PK SK Req Resp F)

variable (Resp) in
/-- The trivial register split as the signing port's register beside a trivial remainder. -/
def signSplit (r : Req) : QReg.of Unit ≃ (advSpec Req Resp).In (.sign r) × QReg.of Unit :=
  (Equiv.prodPUnit Unit).symm

variable (Resp) in
/-- A classical signing request `r`: the call of the port `.sign r`, whose classical result is the
signer's answer, then the relabelling back to the trivial register. -/
noncomputable def signCall (r : Req) :
    QComp (advSpec Req Resp) (QReg.of Unit) (QReg.of Unit) Resp :=
  (QuantumComp₂.query (L := LocalSig.instruments) (spec := advSpec Req Resp) (.sign r)
      (QReg.of Unit) (signSplit Resp r)).bind fun b ↦
    (QComp.act (A := QReg.of ((advSpec Req Resp).Out (.sign r) × QReg.of Unit))
      (B := QReg.of Unit) (SubInstrument.relabel (signSplit Resp r).symm)).bind fun _ ↦
        QuantumComp₂.pure b

variable (Req Resp) in
/-- **A classical adversary's queries as calls of the quantum adversary's ports**: coins by
uniform coins, `H x` by a basis call of `.hash` at `(x, 0)`, reading the response, and a signing
request by the call of its port. -/
noncomputable def advImpl :
    QueryImpl (RomOracles + (Req →ₒ Resp)) (QComp (advSpec Req Resp) (QReg.of Unit) (QReg.of Unit))
  | .inl (.inl n) => QComp.coinImpl (advSpec Req Resp) _ n
  | .inl (.inr x) => QComp.callBasis (spec := advSpec Req Resp) .hash _
      ((x, 0) : HashDomain × HashOutput) fun o _ ↦ (o : HashDomain × HashOutput).2
  | .inr r => signCall Resp r

/-- **The quantum adversary of a classical adversary**: the same algorithm, its queries asked by
classical calls of the ports (`advImpl`). -/
noncomputable def classicalAdversary (adv : PK → OracleComp (RomOracles + (Req →ₒ Resp)) F) :
    Adversary PK Req Resp F :=
  fun pk ↦ (adv pk).toQuantumAt (advImpl Req Resp)

/-- `romImpl` is the classical-call implementation of `Quantum.Qrom.Classical`. -/
theorem romImpl_eq_funImpl (B : QReg) : romImpl B = funImpl B := by
  funext t
  rcases t with n | x <;> rfl

/-- The adversary's program with its signing transcript kept after `log`. -/
def withSignLogFrom {A B : QReg} {α : Type} (log : SignLog Req Resp)
    (x : QComp (advSpec Req Resp) A B α) : QComp (advSpec Req Resp) A B (α × SignLog Req Resp) :=
  logSigns (fun _ l log ↦ ⟨l.1, (l.2, log)⟩) x log

/-! ## The challenger on a classical adversary -/

variable (sk : SK)

/-- A coin or a hash query of the classical adversary becomes the challenger's classical call. -/
theorem challenged_withSignLogFrom_inl_bind {α : Type} (t : RomOracles.Domain)
    (g : RomOracles.Range t → QComp (advSpec Req Resp) (QReg.of Unit) (QReg.of Unit) α)
    (log : SignLog Req Resp) :
    challenged sch sk (withSignLogFrom log ((advImpl Req Resp (.inl t)).bind g)) =
      (funImpl _ t).bind fun y ↦ challenged sch sk (withSignLogFrom log (g y)) := by
  rcases t with n | x <;> rfl

/-- A signing request of the classical adversary becomes the signer, between the relabellings of
the trivial register, and is logged. -/
theorem challenged_withSignLogFrom_signCall_bind {α : Type} (r : Req)
    (g : Resp → QComp (advSpec Req Resp) (QReg.of Unit) (QReg.of Unit) α)
    (log : SignLog Req Resp) :
    challenged sch sk (withSignLogFrom log ((signCall Resp r).bind g)) =
      (signTree sch sk r (QReg.of Unit) (signSplit Resp r)).bind fun u ↦
        (QComp.act (A := QReg.of ((advSpec Req Resp).Out (.sign r) × QReg.of Unit))
          (B := QReg.of Unit) (SubInstrument.relabel (signSplit Resp r).symm)).bind fun _ ↦
            challenged sch sk (withSignLogFrom (log ++ [⟨r, u⟩]) (g u)) := by
  refine (IFreeM.bind_assoc _ _ _).trans (congrArg (IFreeM.bind _) ?_)
  funext u l
  obtain ⟨rfl, a⟩ := l
  rfl

omit sch sk in
/-- The relabelling of the trivial register onto the signing port's register and back is the
identity. -/
theorem relabel_signSplit_symm_comp (r : Req) (D : QReg) :
    ((SubInstrument.relabel (signSplit Resp r).symm).frame D).branch () ∘ₗ
        ((SubInstrument.relabel (signSplit Resp r)).frame D).branch () = LinearMap.id := by
  refine LinearMap.ext fun ρ ↦ ?_
  rw [LinearMap.comp_apply, SubInstrument.frame_relabel, SubInstrument.frame_relabel,
    SubInstrument.relabel_branch_apply, SubInstrument.relabel_branch_apply,
    Matrix.submatrix_submatrix]
  ext x y
  rfl

/-- **The classical adversary's run**, as the forgery game runs it: coins and `H` passed on, each
signing request answered by the signer and logged after `log`. -/
noncomputable def advRun (log : SignLog Req Resp) {α : Type}
    (oa : OracleComp (RomOracles + (Req →ₒ Resp)) α) :
    OracleComp RomOracles (α × SignLog Req Resp) :=
  (fun p ↦ (p.1, log ++ p.2)) <$> (simulateQ (QueryImpl.ofLift RomOracles
      (WriterT (SignLog Req Resp) (OracleComp RomOracles)) +
    QueryImpl.withLogging (spec := Req →ₒ Resp) (sch.sign sk)) oa).run

theorem advRun_pure (log : SignLog Req Resp) {α : Type} (a : α) :
    advRun sch sk log (pure a) = pure (a, log) := by
  simp [advRun]

theorem advRun_query_bind_inl (log : SignLog Req Resp) {α : Type} (t : RomOracles.Domain)
    (k : RomOracles.Range t → OracleComp (RomOracles + (Req →ₒ Resp)) α) :
    advRun sch sk log (liftM ((RomOracles + (Req →ₒ Resp)).query (.inl t)) >>= k) =
      liftM (RomOracles.query t) >>= fun u ↦ advRun sch sk log (k u) := by
  have h : (liftM (RomOracles.query t) :
      WriterT (SignLog Req Resp) (OracleComp RomOracles) _).run =
        (fun u ↦ (u, ∅)) <$> liftM (RomOracles.query t) := rfl
  simp [advRun, h]

theorem advRun_query_bind_inr (log : SignLog Req Resp) {α : Type} (r : Req)
    (k : Resp → OracleComp (RomOracles + (Req →ₒ Resp)) α) :
    advRun sch sk log (liftM ((RomOracles + (Req →ₒ Resp)).query (.inr r)) >>= k) =
      sch.sign sk r >>= fun u ↦ advRun sch sk (log ++ [⟨r, u⟩]) (k u) := by
  simp [advRun]

/-- **The challenged classical adversary runs classically.** Against the oracle of `H`, the
classical adversary `oa` with the challenger substituted and its signing transcript kept after
`log` runs as its classical run `advRun` with its queries answered by `H`. -/
theorem classicalOn_challenged (H : HashDomain → HashOutput) (log : SignLog Req Resp)
    {α : Type} (oa : OracleComp (RomOracles + (Req →ₒ Resp)) α) :
    ClassicalOn (additiveOracleRuntime H)
      (challenged sch sk (withSignLogFrom log (oa.toQuantumAt (advImpl Req Resp))))
      (simulateQ (eagerFunOracles H) (advRun sch sk log oa)) LinearMap.id := by
  induction oa using OracleComp.inductionOn generalizing log with
  | pure a =>
    rw [advRun_pure, simulateQ_pure]
    exact classicalOn_pure (a, log)
  | query_bind t k ih =>
    rw [toQuantumAt_query_bind]
    rcases t with t | r
    · rw [challenged_withSignLogFrom_inl_bind, advRun_query_bind_inl, simulateQ_bind,
        simulateQ_spec_query]
      exact (classicalOn_funImpl _ H t).bind_id fun u ↦ ih u log
    · rw [show advImpl Req Resp (.inr r) = signCall Resp r from rfl,
        challenged_withSignLogFrom_signCall_bind, advRun_query_bind_inr, simulateQ_bind,
        signTree, QuantumComp₂.bind_assoc, romImpl_eq_funImpl]
      have h := (classicalOn_act (R := additiveOracleRuntime H) (spec := romSpec)
        (A := QReg.of Unit) (B := QReg.of ((advSpec Req Resp).Out (.sign r) × QReg.of Unit))
        (SubInstrument.relabel (signSplit Resp r))).bind fun _ ↦
          (classicalOn_toQuantumAt_funImpl _ H (sch.sign sk r)).bind fun u ↦
            (classicalOn_act (R := additiveOracleRuntime H) (spec := romSpec)
              (A := QReg.of ((advSpec Req Resp).Out (.sign r) × QReg.of Unit))
              (B := QReg.of Unit) (SubInstrument.relabel (signSplit Resp r).symm)).bind
                fun _ ↦ ih u (log ++ [⟨r, u⟩])
      refine h.congr (by simp only [pure_bind]) ?_
      rw [LinearMap.id_comp, LinearMap.comp_id]
      exact relabel_signSplit_symm_comp (Resp := Resp) r _

/-! ## The quantum game of a classical adversary is the classical game -/

variable (adv : PK → OracleComp (RomOracles + (Req →ₒ Resp)) F)

/-- The forgery game after the seed `S0`: key generation, the adversary with its signing requests
answered and logged, the verification of its forgery. -/
noncomputable def forgeryGameAt (S0 : Seed) : OracleComp RomOracles Bool := do
  let (pk, secretKey) ← sch.generateKeys S0
  let ((forgery, log) : F × QueryLog (Req →ₒ Resp)) ←
    (simulateQ
      (QueryImpl.ofLift RomOracles (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp RomOracles)) +
      QueryImpl.withLogging (spec := Req →ₒ Resp) (sch.sign secretKey))
        (adv pk)).run
  let verified ← sch.verify pk forgery
  return sch.winningCondition log forgery && verified

/-- The forgery game draws the seed, then runs `forgeryGameAt`. -/
theorem forgeryGameOver_eq :
    forgeryGameOver RomOracles sch adv = liftM sch.sampleSeed >>= forgeryGameAt sch adv :=
  rfl

theorem forgeryGameAt_eq (S0 : Seed) :
    forgeryGameAt sch adv S0 = sch.generateKeys S0 >>= fun keys ↦
      advRun sch keys.2 [] (adv keys.1) >>= fun run ↦
        sch.verify keys.1 run.1 >>= fun verified ↦
          pure (sch.winningCondition run.2 run.1 && verified) := by
  simp [forgeryGameAt, advRun]

/-- **The quantum game of a classical adversary runs classically**: against the oracle of `H`, as
the forgery game after the seed `S0` with its queries answered by `H`. -/
theorem classicalOn_game (H : HashDomain → HashOutput) (S0 : Seed) :
    ClassicalOn (additiveOracleRuntime H) (game sch S0 (classicalAdversary adv))
      (simulateQ (eagerFunOracles H) (forgeryGameAt sch adv S0)) LinearMap.id := by
  rw [forgeryGameAt_eq]
  simp only [simulateQ_bind, simulateQ_pure]
  have hadv (keys : PK × SK) :
      challenged sch keys.2 (withSignLog (classicalAdversary adv keys.1)) =
        challenged sch keys.2 (withSignLogFrom [] ((adv keys.1).toQuantumAt (advImpl Req Resp))) :=
    rfl
  simp only [game, hadv, romImpl_eq_funImpl]
  refine (classicalOn_toQuantumAt_funImpl _ H _).bind_id fun keys ↦ ?_
  refine (classicalOn_challenged sch keys.2 H [] (adv keys.1)).bind_id fun run ↦ ?_
  exact (classicalOn_toQuantumAt_funImpl _ H _).bind_id fun _ ↦ classicalOn_pure _

/-- At each seed, the quantum game of a classical adversary wins with the probability of the
forgery game after that seed in the classical random-oracle model. -/
theorem qromEvalDistMap_game_classicalAdversary (S0 : Seed) :
    qromEvalDistMap .instruments (game sch S0 (classicalAdversary adv)) (SubState.basis ())
        (fun _ p ↦ p.2.2) {true} =
      Pr{let b ← runWithRandomOracle (forgeryGameAt sch adv S0)}[b = true] := by
  rw [qromEvalDistMap_of_classicalOn_singleton (fun H ↦ classicalOn_game sch adv H S0) true,
    runWithRandomOracle]

/-- The classical game averages the game after each seed over the seed law. -/
theorem prEvent_runWithRandomOracle_forgeryGameOver [Fintype Seed] :
    Pr{let b ← runWithRandomOracle (forgeryGameOver RomOracles sch adv)}[b = true] =
      ∑ S0 : Seed, Pr{let s ← sch.sampleSeed}[s = S0] *
        Pr{let b ← runWithRandomOracle (forgeryGameAt sch adv S0)}[b = true] := by
  rw [forgeryGameOver_eq, runWithRandomOracle, simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    run_simulateQ_lazyFunOracles_liftM, bind_map_left, map_bind, prEvent_bind_eq_sum_fintype]
  refine Finset.sum_congr rfl fun S0 _ ↦ ?_
  rw [runWithRandomOracle, StateT.run'_eq]

/-- **The quantum SUF-CMA game on a classical adversary is the classical game.** An adversary
that only asks classical queries, the quantum adversary of a classical adversary `adv`
(`classicalAdversary`), wins the quantum game in the QROM with the probability that `adv` wins
`forgeryGameOver RomOracles`, the statement's game over coins and `H`, against the lazily sampled
random oracle. -/
theorem winProb_classicalAdversary [Fintype Seed] :
    winProb sch (classicalAdversary adv) =
      Pr{let b ← runWithRandomOracle (forgeryGameOver RomOracles sch adv)}[b = true] := by
  rw [winProb, prEvent_runWithRandomOracle_forgeryGameOver]
  exact Finset.sum_congr rfl fun S0 _ ↦ by rw [qromEvalDistMap_game_classicalAdversary]

end Quantum.Qrom.SufCma

end
