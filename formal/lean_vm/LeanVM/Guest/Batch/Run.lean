/-
  LeanVM.Guest.Batch.Run

  `Node.batch` run on the duplex sponge: the transcript, the lambdas and the sumcheck as explicit
  functions of the sponge.
-/

module

public import LeanVM.Guest.Batch.Bytecode
public import LeanVM.Protocol.Compile.Prover

/-!
# The batching, run

`Node.batch` is a `StateM Sponge` program. `batch_eq` unfolds it: the sponge after the label's
seed absorbs the count and the children's words, each padded to a whole rate (`cellsBeforeChallenge`), the
lambdas are the powers of one squeeze (`sqL`) after the proof of work on the hinted nonce
(`powB`), and the sumcheck's rounds absorb the round's two
values and squeeze its challenge (`rsRun`); the deferred claim is the challenges and the hinted
value, if the final claim is the hinted value times the batched weight at the challenges.
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-! ## The sponge, in `Id` -/

/-- Absorb a scalar the prover sent (tag `1`). -/
abbrev obs (sp : Sponge) (x : E) : Sponge := absorbI keccakF1600 sp x dsObserve

/-- Absorb scalars, in order. -/
def obsAll (sp : Sponge) (xs : List E) : Sponge := xs.foldl obs sp

/-- Squeeze a challenge: the challenge and the sponge after it. -/
abbrev sq (sp : Sponge) : E × Sponge := squeezeI keccakF1600 sp

theorem obsAll_append (sp : Sponge) (xs ys : List E) :
    obsAll sp (xs ++ ys) = obsAll (obsAll sp xs) ys := List.foldl_append ..

theorem sq_fst {sp : Sponge} (hg : sp.ground = none) : (sq sp).1 = challengeOf (sq sp).2.state := by
  obtain ⟨st, pe, g⟩ := sp
  cases hg
  rfl

theorem obs_ground' (sp : Sponge) (x : E) : (obs sp x).ground = sp.ground := absorbI_ground _ _ _ _

/-! ## The transcript -/

/-- The sponge after the batching's absorptions. -/
def batchSponge (cs : List ChildClaims) : Sponge := obsAll ⟨batchSeed, [], none⟩ (cellsBeforeChallenge cs)

/-- One squeeze, its powers the lambdas of `n` children (`lambdaPowers`): the lambdas and the
sponge after the squeeze. -/
def sqL (n : ℕ) (sp : Sponge) : List (E × E) × Sponge := (lambdaPowers (sq sp).1 n, (sq sp).2)

theorem length_lambdaPowers (lam : E) (n : ℕ) : (lambdaPowers lam n).length = n := by
  simp [lambdaPowers]

theorem length_sqL (n : ℕ) (sp : Sponge) : (sqL n sp).1.length = n := length_lambdaPowers _ _

/-! ## The rounds -/

/-- One round: absorb its message, squeeze the challenge, fold the claim. -/
def rsStep (st : E × Sponge) (g : E × E) : E × Sponge :=
  let sp := (sq (obsAll st.2 [g.1, g.2])).2
  (sumcheckRoundPolynomial st.1 g (challengeOf sp.state), sp)

/-- The rounds from `claim` at `sp`: the challenges, the final claim, the sponge after them. -/
def rsRun : List (E × E) → E → Sponge → (List E × E) × Sponge
  | [], claim, sp => (([], claim), sp)
  | g :: rest, claim, sp =>
    let st := rsStep (claim, sp) g
    let res := rsRun rest st.1 st.2
    ((challengeOf st.2.state :: res.1.1, res.1.2), res.2)

/-- The claim and the sponge before round `j`. -/
def rsSt (rounds : List (E × E)) (claim : E) (sp : Sponge) : ℕ → E × Sponge
  | 0 => (claim, sp)
  | j + 1 => rsStep (rsSt rounds claim sp j) (rounds.getD j (0, 0))

theorem rsSt_cons (g : E × E) (rest : List (E × E)) (claim : E) (sp : Sponge) :
    ∀ j, rsSt (g :: rest) claim sp (j + 1) =
      rsSt rest (rsStep (claim, sp) g).1 (rsStep (claim, sp) g).2 j
  | 0 => rfl
  | j + 1 => by
    rw [rsSt, rsSt_cons g rest claim sp j, List.getD_cons_succ]
    rfl

theorem rsRun_eq (rounds : List (E × E)) (claim : E) (sp : Sponge) :
    rsRun rounds claim sp =
      (((List.range rounds.length).map fun j ↦ challengeOf (rsSt rounds claim sp (j + 1)).2.state,
        (rsSt rounds claim sp rounds.length).1), (rsSt rounds claim sp rounds.length).2) := by
  induction rounds generalizing claim sp with
  | nil => rfl
  | cons g rest ih =>
    rw [rsRun, ih, List.length_cons, List.range_succ_eq_map, rsSt_cons]
    simp only [List.map_cons, List.map_map, Function.comp_def, rsSt_cons]
    rfl

theorem length_rsRun (rounds : List (E × E)) (claim : E) (sp : Sponge) :
    (rsRun rounds claim sp).1.1.length = rounds.length := by
  rw [rsRun_eq]; simp

/-! ## `batch`, unfolded -/

theorem sample_run (sp : Sponge) : sample.run sp = sq sp := rfl

theorem grind_run (bits : ℕ) (n : E) (sp : Sponge) :
    (grind bits n).run sp = (powOk bits (powStep keccakF1600 sp n).1, (powStep keccakF1600 sp n).2) := rfl

theorem batchRounds_run (rounds : List (E × E)) (claim : E) {sp : Sponge} (hg : sp.ground = none) :
    (batchRounds claim rounds).run sp = rsRun rounds claim sp := by
  induction rounds generalizing claim sp with
  | nil => rfl
  | cons g rest ih =>
    obtain ⟨g1, gInf⟩ := g
    show (fun q ↦ (((sq (obs (obs sp g1) gInf)).1 :: q.1.1, q.1.2), q.2))
      (StateT.run (batchRounds (sumcheckRoundPolynomial claim (g1, gInf) (sq (obs (obs sp g1) gInf)).1) rest)
        (sq (obs (obs sp g1) gInf)).2) = _
    rw [ih _ (squeezeI_ground _ _),
      sq_fst (((obs_ground' _ _).trans (obs_ground' _ _)).trans hg)]
    rfl

theorem id_bind {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl

theorem id_map {α β : Type} (x : Id α) (f : α → β) : f <$> x = f x := rfl

theorem ite_run {α : Type} (c : Prop) [Decidable c] (p q : Chain α) (sp : Sponge) :
    StateT.run (if c then p else q) sp = if c then p.run sp else q.run sp := by
  split <;> rfl

theorem forIn_observe_run (xs : List E) (sp : Sponge) :
    (forIn xs PUnit.unit (fun x _ ↦ do
        observe x
        pure (ForInStep.yield PUnit.unit)) : Chain PUnit).run sp = ((), obsAll sp xs) := by
  induction xs generalizing sp with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forIn_cons]
    exact ih (obs sp x)

theorem forIn_children_run (cs : List ChildClaims) (sp : Sponge) :
    (forIn cs PUnit.unit (fun c _ ↦ do
        forIn (padToRate c.words) PUnit.unit fun x _ ↦ do
          observe x
          pure (ForInStep.yield PUnit.unit)
        pure (ForInStep.yield PUnit.unit)) : Chain PUnit).run sp =
      ((), obsAll sp (cs.flatMap childCells)) := by
  induction cs generalizing sp with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.forIn_cons, StateT.run_bind, forIn_observe_run, List.flatMap_cons,
      obsAll_append]
    exact ih _

/-- The proof of work on the hinted nonce at the batching's sponge: its third lane and the sponge
after it, whose ground challenge is `λ`. -/
def powB (cs : List ChildClaims) (h : BatchingHints) : UInt64 × Sponge :=
  powStep keccakF1600 (batchSponge cs) h.lambdaGrindNonce

/-- **`Node.batch` on the sponge.** -/
theorem batch_eq (cs : List ChildClaims) (h : BatchingHints) :
    batch cs h =
      if powOk batchLambdaGrindBits (powB cs h).1 then
        let L := sqL cs.length (powB cs h).2
        let R := rsRun h.sumcheckMessages (batchedClaim cs L.1) L.2
        if R.1.2 = h.finalBytecodeValue * batchedBytecodeWeight cs L.1 R.1.1 then
          some ⟨R.1.1, h.finalBytecodeValue⟩
        else none
      else none := by
  have hs : obsAll (obsAll ⟨batchSeed, [], none⟩ (childCountCells cs.length)) (cs.flatMap childCells) =
      batchSponge cs := (obsAll_append _ _ _).symm
  simp only [batch, batch.go, StateT.run'_eq, StateT.run_bind, forIn_observe_run,
    forIn_children_run, grind_run, id_bind]
  rw [show padToRate [gpow cs.length] = childCountCells cs.length from rfl, hs,
    show powStep keccakF1600 (batchSponge cs) h.lambdaGrindNonce = powB cs h from rfl, ite_run]
  by_cases hp : powOk batchLambdaGrindBits (powB cs h).1 = true
  · simp only [hp, ↓reduceIte, StateT.run_bind, sample_run, batchRounds_run _ _ (squeezeI_ground _ _),
      id_bind, id_map, ite_run, StateT.run_pure, apply_ite Prod.fst]
    rfl
  · simp only [hp, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, id_map]
    rfl

end
end LeanVM.Guest.Batch
