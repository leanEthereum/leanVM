/-
  LeanVM.Guest.B1.Whir.Split

  The Spec's stacked WHIR opening split at the terminal the guest checks apart: `whirOpen`, then
  the terminal's check, and the names of `open_stacked`'s specializations.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Protocol.Compile.Prog

/-!
# `verifyWhir`, split at its terminal

`open_stacked` (`crates/rec_aggregation/guests/lean_ethereum.py:1565-1806`, G below) runs
`verifyWhir` (`Statement/LeanVmVerifier.lean`; `crates/verifier/src/whir.rs:215-329`) up to its
last `require`, the terminal's check, which `check_opening_terminal` makes (G:3497).

* `WhirEnd`, `whirLevelsOpen`, `whirOpen`: `whirLevels` and `verifyWhir` without the final
  `require`, returning what the terminal reads (the final level's query checks stay);
* `WhirEnd.Accepts`: the terminal's check, `(inner + evaluateBasis point) · residual = claim`;
* `verifyWhir_split`: `verifyWhir` is `whirOpen`, then `require Accepts`;
* `stackShape μ r`, `commitStack_eq`: the shape `commitStack` gives the stack's root;
* `openArms`, `openNames`, `minOpenLog`, `openName`: `open_stacked`'s specializations, one per
  stack log from `minOpenLog`, as `verify_sub` dispatches them (G:3691);
* `rateSel`: the rate's selector, `open_stacked`'s argument (G:3550);
* `pointCap`: the length of the point buffers (G:1727-1728).

Only the Statement is imported, so the split builds apart from the guest's proofs.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The opening up to its terminal (`whirLevels`, `verifyWhir`) -/

/-- What the stacked opening leaves for its terminal: the point in witness order, the glued
claims' weight there, the final lane's low part at the tail challenges, and the running claim. -/
structure WhirEnd where
  /-- The terminal point, rotated into witness order (`point.drop laneFolds ++ point.take …`). -/
  point : List E
  /-- `Σ scalar · weightAt` over the glued claims. -/
  inner : E
  /-- `multilinearEval (folded.take (2^μ)) tail`. -/
  residual : E
  /-- The final running claim. -/
  target : E

/-- `whirLevels` without its final `require`: it returns what the terminal reads. The final
level's query checks stay, as `open_stacked` makes them. -/
def whirLevelsOpen (logN laneFolds : ℕ) : ℕ → List Whir.Level → WhirState → VerifierProgram WhirEnd
  | _, [], _ => VerifierProgram.fail
  | index, level :: rest, s => do
    let (s, rounds) ← foldRounds level.fold s
    let mu := logN - s.alphas.length
    let depth := mu + level.logInvRate
    let lanesOf : List K → List E := fun row ↦
      if index = 0 then row.reverse.map ofK else extRow row
    match rest with
    | [] => do
      let folded ← VerifierProgram.readScalars (2 ^ mu + level.fold)
      VerifierProgram.grindProofOfWork Whir.queryGrindingBits
      let queries ← sampleQueries depth level.queries
      let words ← VerifierProgram.queryOpenings index queries
      VerifierProgram.require ((List.zip queries words).all fun (query, row) ↦
        foldRow (lanesOf row) (K.ofBits query) rounds =
          novelEval folded (subspaceAt mu (K.ofBits query)))
      let (tail, claim) ← sumcheck s.claim 3 (List.replicate mu none)
      let point := s.alphas ++ tail
      let inner := s.glued.foldl
        (fun weight glued ↦ weight + glued.scalar * glued.weightAt (point.drop glued.foldStart)) 0
      return ⟨point.drop laneFolds ++ point.take laneFolds, inner,
        multilinearEval (folded.take (2 ^ mu)) tail, claim⟩
    | next :: _ => do
      let (height, width) := levelShape mu next (2 * 2 ^ next.fold)
      VerifierProgram.readCommitment height width
      let high ← VerifierProgram.readScalars level.fold
      VerifierProgram.grindProofOfWork Whir.oodGrindingBits
      let oodPoint ← VerifierProgram.sampleChallenges mu
      let oodValue ← VerifierProgram.readScalar
      VerifierProgram.grindProofOfWork Whir.queryGrindingBits
      let queries ← sampleQueries depth level.queries
      let lam ← VerifierProgram.sampleChallenge
      let queryWeights := powers lam queries.length
      let words ← VerifierProgram.queryOpenings index queries
      let batched := sumE (List.zipWith (fun (query, row) queryWeight ↦
        let what := subspaceAt mu (K.ofBits query)
        queryWeight * (foldRow (lanesOf row) (K.ofBits query) rounds +
          novelEval high what * ofK (what.getD mu 0))) (List.zip queries words) queryWeights)
      let s := glueLevel s lam mu oodPoint oodValue queries queryWeights batched
      whirLevelsOpen logN laneFolds (index + 1) rest s

/-- `verifyWhir` up to its terminal: what `open_stacked` runs. -/
def whirOpen (logN logInvRate : ℕ) (target : E) : VerifierProgram WhirEnd := do
  let config ← liftOption (Whir.ladder logN logInvRate)
  whirLevelsOpen logN ((config.head?.map (·.fold)).getD 0) 0 config ⟨target, [], []⟩

/-- The terminal's check (`check_opening_terminal`): the weight at the point times the final
lane's low part at the tail challenges is the claim. -/
def WhirEnd.Accepts (w : WhirEnd) (evaluateBasis : List E → E) : Prop :=
  (w.inner + evaluateBasis w.point) * w.residual = w.target

instance (w : WhirEnd) (evaluateBasis : List E → E) : Decidable (w.Accepts evaluateBasis) :=
  inferInstanceAs (Decidable (_ = _))

theorem foldl_add_shift {α : Type} (f : α → E) (a : E) (l : List α) :
    l.foldl (fun w c ↦ w + f c) a = a + l.foldl (fun w c ↦ w + f c) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, List.foldl_cons, ih, ih (0 + f x), zero_add, add_assoc]

theorem prog_bind_congr {α β : Type} {p : VerifierProgram α} {f g : α → VerifierProgram β}
    (h : ∀ a, f a = g a) : p.bind f = p.bind g := by rw [funext h]

theorem whirLevels_split (logN laneFolds : ℕ) (eb : List E → E) :
    ∀ (index : ℕ) (levels : List Whir.Level) (s : WhirState),
      whirLevels logN laneFolds eb index levels s =
        (whirLevelsOpen logN laneFolds index levels s).bind fun w ↦
          VerifierProgram.require (w.Accepts eb)
  | _, [], _ => rfl
  | index, [level], s => by
    rw [whirLevels, whirLevelsOpen]
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc,
      VerifierProgram.ret_bind, WhirEnd.Accepts]
    repeat refine prog_bind_congr fun _ ↦ ?_
    rw [foldl_add_shift _ (eb _), add_comm (eb _)]
    congr 1
  | index, level :: next :: rest, s => by
    rw [whirLevels, whirLevelsOpen]
    simp only [VerifierProgram.bind_eq, VerifierProgram.bind_assoc,
      whirLevels_split logN laneFolds eb (index + 1) (next :: rest)]

/-- **`verifyWhir` is `whirOpen`, then the terminal's check.** -/
theorem verifyWhir_split (logN logInvRate : ℕ) (target : E) (eb : List E → E) :
    verifyWhir logN logInvRate target eb = (do
      let w ← whirOpen logN logInvRate target
      VerifierProgram.require (w.Accepts eb)) := by
  simp only [verifyWhir, whirOpen, VerifierProgram.bind_eq, VerifierProgram.bind_assoc,
    whirLevels_split]

/-- The shape `commitStack` gives the stack's root (V:1844): `(height, width)`. -/
def stackShape (logN logInvRate : ℕ) : ℕ × ℕ :=
  match Whir.ladder logN logInvRate with
  | some (level :: _) => levelShape logN level (2 ^ level.fold)
  | _ => (0, 0)

/-- **`commitStack` commits the stack's shape**, when the configuration has a level. -/
theorem commitStack_eq {logN logInvRate : ℕ} {level : Whir.Level} {rest : List Whir.Level}
    (h : Whir.ladder logN logInvRate = some (level :: rest)) :
    commitStack logN logInvRate =
      VerifierProgram.readCommitment (stackShape logN logInvRate).1 (stackShape logN
          logInvRate).2 := by
  simp only [commitStack, stackShape, h, VerifierProgram.bind_eq]
  rfl

/-! ## The specializations -/

/-- `ligNSizes`: `open_stacked`'s specializations, one per stack log. -/
abbrev openArms : ℕ := 11

/-- `open_stacked`'s specializations, in dispatch order. -/
def openNames : List String :=
  (List.range openArms).map fun m ↦ "open_stacked__L" ++ toString m

/-- The smallest stack log a child's opening takes (`verifier::min_execution_stacked_log` of the
guest's bytecode). -/
abbrev minOpenLog : ℕ := 20

/-- The specialization of `open_stacked` for the stack log `μ`: `μ - minOpenLog` in dispatch
order. -/
def openName (μ : ℕ) : String := openNames.getD (μ - minOpenLog) ""

/-- The rate's selector, an argument of `open_stacked`: `g^(r - 1)`. -/
def rateSel (r : ℕ) : E := ofK (addressOfIndex (r - 1))

/-- The length of the point buffers, `SIZE_BITS + QKECCAK_SLOT_LOG`. -/
abbrev pointCap : ℕ := 40

end
end LeanVM.Guest.B1.Whir
