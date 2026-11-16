module

public import Quantum.Classical
public import Quantum.SufCma.Game

@[expose] public section

/-!
# The quantum SUF-CMA game on classical adversaries

A classical adversary of the statement's `SufCma.forgeryGame`, an `OracleComp` over coins, `π`,
`π⁻¹` and the signing oracle, is a quantum adversary of `Quantum.SufCma.game` that asks every
query classically (`classicalAdversary`: coins by uniform coins, `π` and `π⁻¹` by basis calls of
the ports `.perm`, read back through `e`, a signing request by the call of its port). Its quantum
game, with the challenger substituted, runs against each `φ` as the statement's game after the
seed against the fixed permutation `e⁻¹ φ e` (`classicalOn_game`), so by `Quantum.Classical` it
wins with the statement's probability: `winProb_classicalAdversary`.
-/

open IPFunctor OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Quantum.SufCma

open Common Common.SufCma
open LeanVM.Semantics (KeccakState)

variable {Seed PK SK Req Resp F : Type} {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
  (sch : Scheme Seed PK SK Req Resp F) (e : KeccakState ≃ S)

variable (Resp S) in
/-- The trivial register split as the signing port's register beside a trivial remainder. -/
def signSplit (r : Req) :
    QReg.of Unit ≃ (advSpec Req Resp S).In (.sign r) × QReg.of Unit :=
  (Equiv.prodPUnit Unit).symm

variable (Resp S) in
/-- A classical signing request `r`: the call of the port `.sign r`, whose classical result is the
signer's answer, then the relabelling back to the trivial register. -/
noncomputable def signCall (r : Req) :
    QComp (advSpec Req Resp S) (QReg.of Unit) (QReg.of Unit) Resp :=
  (QuantumComp₂.query (L := LocalSig.instruments) (spec := advSpec Req Resp S) (.sign r)
      (QReg.of Unit) (signSplit Resp S r)).bind fun b ↦
    (QComp.act (A := QReg.of ((advSpec Req Resp S).Out (.sign r) × QReg.of Unit))
      (B := QReg.of Unit) (SubInstrument.relabel (signSplit Resp S r).symm)).bind fun _ ↦
        QuantumComp₂.pure b

variable (Req Resp) in
/-- **A classical adversary's queries as calls of the quantum adversary's ports**: coins by
uniform coins, `π` and `π⁻¹` by basis calls of `.perm`, read back through `e`, and a signing
request by the call of its port. -/
noncomputable def advImpl :
    QueryImpl (RandomPermutationOracles + (Req →ₒ Resp))
      (QComp (advSpec Req Resp S) (QReg.of Unit) (QReg.of Unit))
  | .inl (.inl n) => QComp.coinImpl (advSpec Req Resp S) _ n
  | .inl (.inr (.forward s)) => QComp.callBasis (spec := advSpec Req Resp S) (.perm .forward) _
      ((e s, 0) : S × S) fun o _ ↦ e.symm (o : S × S).2
  | .inl (.inr (.inverse s)) => QComp.callBasis (spec := advSpec Req Resp S) (.perm .inverse) _
      ((e s, 0) : S × S) fun o _ ↦ e.symm (o : S × S).2
  | .inr r => signCall Resp S r

/-- **The quantum adversary of a classical adversary**: the same algorithm, its queries asked by
classical calls of the ports (`advImpl`). -/
noncomputable def classicalAdversary
    (adv : PK → OracleComp (RandomPermutationOracles + (Req →ₒ Resp)) F) :
    Adversary PK Req Resp F S :=
  fun pk ↦ (adv pk).toQuantumAt (advImpl Req Resp e)

/-- `permImpl` is the classical-call implementation of `Quantum.Classical`. -/
theorem permImpl_eq_qrpmImpl (B : QReg) : permImpl e B = qrpmImpl e B := by
  funext t
  rcases t with n | (s | s) <;> rfl

/-- The adversary's program with its signing transcript kept after `log`. -/
def withSignLogFrom {A B : QReg} {α : Type} (log : SignLog Req Resp)
    (x : QComp (advSpec Req Resp S) A B α) :
    QComp (advSpec Req Resp S) A B (α × SignLog Req Resp) :=
  logSigns (fun _ l log ↦ ⟨l.1, (l.2, log)⟩) x log

/-! ## The challenger on a classical adversary -/

variable (sk : SK)

/-- A coin, `π` or `π⁻¹` of the classical adversary becomes the challenger's classical call. -/
theorem challenged_withSignLogFrom_inl_bind {α : Type} (t : RandomPermutationOracles.Domain)
    (g : RandomPermutationOracles.Range t →
      QComp (advSpec Req Resp S) (QReg.of Unit) (QReg.of Unit) α)
    (log : SignLog Req Resp) :
    challenged sch e sk (withSignLogFrom log ((advImpl Req Resp e (.inl t)).bind g)) =
      (qrpmImpl e _ t).bind fun y ↦ challenged sch e sk (withSignLogFrom log (g y)) := by
  rcases t with n | (s | s) <;> rfl

/-- A signing request of the classical adversary becomes the signer, between the relabellings of
the trivial register, and is logged. -/
theorem challenged_withSignLogFrom_signCall_bind {α : Type} (r : Req)
    (g : Resp → QComp (advSpec Req Resp S) (QReg.of Unit) (QReg.of Unit) α)
    (log : SignLog Req Resp) :
    challenged sch e sk (withSignLogFrom log ((signCall Resp S r).bind g)) =
      (signTree sch e sk r (QReg.of Unit) (signSplit Resp S r)).bind fun u ↦
        (QComp.act (A := QReg.of ((advSpec Req Resp S).Out (.sign r) × QReg.of Unit))
          (B := QReg.of Unit) (SubInstrument.relabel (signSplit Resp S r).symm)).bind fun _ ↦
            challenged sch e sk (withSignLogFrom (log ++ [⟨r, u⟩]) (g u)) := by
  refine (IFreeM.bind_assoc _ _ _).trans (congrArg (IFreeM.bind _) ?_)
  funext u l
  obtain ⟨rfl, a⟩ := l
  rfl

omit [AddCommGroup S] in
/-- The relabelling of the trivial register onto the signing port's register and back is the
identity. -/
theorem relabel_signSplit_symm_comp (r : Req) (D : QReg) :
    ((SubInstrument.relabel (signSplit Resp S r).symm).frame D).branch () ∘ₗ
        ((SubInstrument.relabel (signSplit Resp S r)).frame D).branch () = LinearMap.id := by
  refine LinearMap.ext fun ρ ↦ ?_
  rw [LinearMap.comp_apply, SubInstrument.frame_relabel, SubInstrument.frame_relabel,
    SubInstrument.relabel_branch_apply, SubInstrument.relabel_branch_apply,
    Matrix.submatrix_submatrix]
  ext x y
  rfl

/-- **The classical adversary's run**, as the forgery game runs it: coins, `π` and `π⁻¹` passed
on, each signing request answered by the signer and logged after `log`. -/
noncomputable def advRun (log : SignLog Req Resp) {α : Type}
    (oa : OracleComp (RandomPermutationOracles + (Req →ₒ Resp)) α) :
    OracleComp RandomPermutationOracles (α × SignLog Req Resp) :=
  (fun p ↦ (p.1, log ++ p.2)) <$> (simulateQ (QueryImpl.ofLift RandomPermutationOracles
      (WriterT (SignLog Req Resp) (OracleComp RandomPermutationOracles)) +
    QueryImpl.withLogging (spec := Req →ₒ Resp) (sch.sign sk)) oa).run

theorem advRun_pure (log : SignLog Req Resp) {α : Type} (a : α) :
    advRun sch sk log (pure a) = pure (a, log) := by
  simp [advRun]

theorem advRun_query_bind_inl (log : SignLog Req Resp) {α : Type}
    (t : RandomPermutationOracles.Domain)
    (k : RandomPermutationOracles.Range t →
      OracleComp (RandomPermutationOracles + (Req →ₒ Resp)) α) :
    advRun sch sk log
        (liftM ((RandomPermutationOracles + (Req →ₒ Resp)).query (.inl t)) >>= k) =
      liftM (RandomPermutationOracles.query t) >>= fun u ↦ advRun sch sk log (k u) := by
  have h : (liftM (RandomPermutationOracles.query t) :
      WriterT (SignLog Req Resp) (OracleComp RandomPermutationOracles) _).run =
        (fun u ↦ (u, ∅)) <$> liftM (RandomPermutationOracles.query t) := rfl
  simp [advRun, h]

theorem advRun_query_bind_inr (log : SignLog Req Resp) {α : Type} (r : Req)
    (k : Resp → OracleComp (RandomPermutationOracles + (Req →ₒ Resp)) α) :
    advRun sch sk log
        (liftM ((RandomPermutationOracles + (Req →ₒ Resp)).query (.inr r)) >>= k) =
      sch.sign sk r >>= fun u ↦ advRun sch sk (log ++ [⟨r, u⟩]) (k u) := by
  simp [advRun]

/-- **The challenged classical adversary runs classically.** Against the oracle of `φ`, the
classical adversary `oa` with the challenger substituted and its signing transcript kept after
`log` runs as its classical run `advRun` against the fixed permutation `e⁻¹ φ e`. -/
theorem classicalOn_challenged (φ : Equiv.Perm S) (log : SignLog Req Resp) {α : Type}
    (oa : OracleComp (RandomPermutationOracles + (Req →ₒ Resp)) α) :
    ClassicalOn (permutationRuntime φ)
      (challenged sch e sk (withSignLogFrom log (oa.toQuantumAt (advImpl Req Resp e))))
      (simulateQ (eagerPermOracles (e.symm.permCongr φ)) (advRun sch sk log oa))
      LinearMap.id := by
  induction oa using OracleComp.inductionOn generalizing log with
  | pure a =>
    rw [advRun_pure, simulateQ_pure]
    exact classicalOn_pure (a, log)
  | query_bind t k ih =>
    rw [toQuantumAt_query_bind]
    rcases t with t | r
    · rw [challenged_withSignLogFrom_inl_bind, advRun_query_bind_inl, simulateQ_bind,
        simulateQ_spec_query]
      exact (classicalOn_qrpmImpl e _ φ t).bind_id fun u ↦ ih u log
    · rw [show advImpl Req Resp e (.inr r) = signCall Resp S r from rfl,
        challenged_withSignLogFrom_signCall_bind, advRun_query_bind_inr, simulateQ_bind,
        signTree, QuantumComp₂.bind_assoc, permImpl_eq_qrpmImpl]
      have h := (classicalOn_act (R := permutationRuntime φ) (spec := qrpmSpec S)
        (A := QReg.of Unit) (B := QReg.of ((advSpec Req Resp S).Out (.sign r) × QReg.of Unit))
        (SubInstrument.relabel (signSplit Resp S r))).bind fun _ ↦
          (classicalOn_toQuantumAt_qrpmImpl e _ φ (sch.sign sk r)).bind fun u ↦
            (classicalOn_act (R := permutationRuntime φ) (spec := qrpmSpec S)
              (A := QReg.of ((advSpec Req Resp S).Out (.sign r) × QReg.of Unit))
              (B := QReg.of Unit) (SubInstrument.relabel (signSplit Resp S r).symm)).bind
                fun _ ↦ ih u (log ++ [⟨r, u⟩])
      refine h.congr (by simp only [pure_bind]) ?_
      rw [LinearMap.id_comp, LinearMap.comp_id]
      exact relabel_signSplit_symm_comp (Resp := Resp) (S := S) r _

/-! ## The quantum game of a classical adversary is the classical game -/

variable (adv : PK → OracleComp (RandomPermutationOracles + (Req →ₒ Resp)) F)

/-- The statement's forgery game after the seed `S0`: key generation, the adversary with its
signing requests answered and logged, the verification of its forgery. -/
noncomputable def forgeryGameAt (S0 : Seed) : OracleComp RandomPermutationOracles Bool := do
  let (pk, secretKey) ← sch.generateKeys S0
  let ((forgery, log) : F × QueryLog (Req →ₒ Resp)) ←
    (simulateQ
      (QueryImpl.ofLift RandomPermutationOracles
        (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp RandomPermutationOracles)) +
      QueryImpl.withLogging (spec := Req →ₒ Resp) (sch.sign secretKey))
        (adv pk)).run
  let verified ← sch.verify pk forgery
  return sch.winningCondition log forgery && verified

/-- The forgery game draws the seed, then runs `forgeryGameAt`. -/
theorem forgeryGame_eq :
    forgeryGame sch adv = liftM sch.sampleSeed >>= forgeryGameAt sch adv :=
  rfl

theorem forgeryGameAt_eq (S0 : Seed) :
    forgeryGameAt sch adv S0 = sch.generateKeys S0 >>= fun keys ↦
      advRun sch keys.2 [] (adv keys.1) >>= fun run ↦
        sch.verify keys.1 run.1 >>= fun verified ↦
          pure (sch.winningCondition run.2 run.1 && verified) := by
  simp [forgeryGameAt, advRun]

/-- **The quantum game of a classical adversary runs classically**: against the oracle of `φ`, as
the statement's game after the seed `S0` against the fixed permutation `e⁻¹ φ e`. -/
theorem classicalOn_game (φ : Equiv.Perm S) (S0 : Seed) :
    ClassicalOn (permutationRuntime φ) (game sch e S0 (classicalAdversary e adv))
      (simulateQ (eagerPermOracles (e.symm.permCongr φ)) (forgeryGameAt sch adv S0))
      LinearMap.id := by
  rw [forgeryGameAt_eq]
  simp only [simulateQ_bind, simulateQ_pure]
  have hadv (keys : PK × SK) :
      challenged sch e keys.2 (withSignLog (classicalAdversary e adv keys.1)) =
        challenged sch e keys.2
          (withSignLogFrom [] ((adv keys.1).toQuantumAt (advImpl Req Resp e))) :=
    rfl
  simp only [game, hadv, permImpl_eq_qrpmImpl]
  refine (classicalOn_toQuantumAt_qrpmImpl e _ φ _).bind_id fun keys ↦ ?_
  refine (classicalOn_challenged sch e keys.2 φ [] (adv keys.1)).bind_id fun run ↦ ?_
  exact (classicalOn_toQuantumAt_qrpmImpl e _ φ _).bind_id fun _ ↦ classicalOn_pure _

/-- The statement's lazy oracles are those of `Quantum.Classical` on the Keccak state. -/
theorem lazyRandomPermutationOracles_eq :
    lazyRandomPermutationOracles = lazyPermOracles (S := KeccakState) := by
  funext t
  rcases t with n | q <;> rfl

/-- At each seed, the quantum game of a classical adversary wins with the probability of the
statement's game after that seed. -/
theorem qrpmEvalDistMap_game_classicalAdversary (S0 : Seed) :
    qrpmEvalDistMap .instruments (game sch e S0 (classicalAdversary e adv)) (SubState.basis ())
        (fun _ p ↦ p.2.2) {true} =
      Pr{let b ← runWithRandomPermutation (forgeryGameAt sch adv S0)}[b = true] := by
  rw [qrpmEvalDistMap_of_classicalOn_singleton e (fun φ ↦ classicalOn_game sch e adv φ S0) true,
    runWithRandomPermutation, lazyRandomPermutationOracles_eq]

/-- The statement's game averages the game after each seed over the seed law. -/
theorem prEvent_runWithRandomPermutation_forgeryGame [Fintype Seed] :
    Pr{let b ← runWithRandomPermutation (forgeryGame sch adv)}[b = true] =
      ∑ S0 : Seed, Pr{let s ← sch.sampleSeed}[s = S0] *
        Pr{let b ← runWithRandomPermutation (forgeryGameAt sch adv S0)}[b = true] := by
  rw [forgeryGame_eq, runWithRandomPermutation, lazyRandomPermutationOracles_eq,
    simulateQ_bind, StateT.run'_eq, StateT.run_bind, run_simulateQ_lazyPermOracles_liftM,
    bind_map_left, map_bind, prEvent_bind_eq_sum_fintype]
  refine Finset.sum_congr rfl fun S0 _ ↦ ?_
  rw [runWithRandomPermutation, lazyRandomPermutationOracles_eq, StateT.run'_eq]

/-- **The quantum SUF-CMA game on a classical adversary is the statement's game.** An adversary
that only asks classical queries, the quantum adversary of a classical adversary `adv`
(`classicalAdversary`), wins the quantum game in the QRPM with the probability that `adv` wins the
statement's `forgeryGame` against the lazily sampled random permutation. -/
theorem winProb_classicalAdversary [Fintype Seed] :
    winProb sch e (classicalAdversary e adv) =
      Pr{let b ← runWithRandomPermutation (forgeryGame sch adv)}[b = true] := by
  rw [winProb, prEvent_runWithRandomPermutation_forgeryGame]
  exact Finset.sum_congr rfl fun S0 _ ↦ by rw [qrpmEvalDistMap_game_classicalAdversary]

end Quantum.SufCma

end
