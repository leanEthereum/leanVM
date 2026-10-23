import LeanVM.Protocol.Whir.Complete.Opening

/-!
# Completeness of the WHIR opening: tests

* **Statement locks** of the main theorems (`runFrom_verifyStackedOpening`,
  `exists_prove_runProof_openingProgram`, `follows_whirLevels`, `follows_whirRun`): a change of a
  hypothesis or of the conclusion fails here.
* **The honest round polynomials** (`#guard`, compiled): the sumcheck identity
  `polyEval_roundQuad` on small tables (and its failure on a wrong claim), the derived linear
  coefficient, linearity in the weight table; the equality kernel, the partial fold and the
  multilinear extension against their sums.
* **Scaled-down runs** of the deployed level loop `whirRun` (the verifier's `verify_whir` past
  `derive_config`, `LeanVM.Protocol.Verifier.whirLevels` unchanged) on toy ladders over stacks
  of `2^7` and `2^8` cells with two column claims. The smallest admissible stack (`2^15` cells,
  at least `223` level-0 queries) is out of reach of the interpreter (`~0.6 ms` per `E`
  multiplication). The honest prover is accepted: once through the strategy `Strategy.ofScript`
  the theorems are about (`Strategy.runFrom`, `2^7`), once through `lockstep`, which runs the
  script against the program directly instead of replaying it from the start at every message
  (`2^8`, a ladder whose final level has a tail round). A tampered first message, a wrong claimed
  value, and the word of another stack are rejected.
* `follows_whirRun` holds on the toy instance (its hypotheses are discharged), so the runs are
  instances of the theorem, not only of the code; the toy stack is a candidate of its honest
  word (`stackWord_agrees`).
-/

namespace LeanVMTests.Protocol.Whir.Complete.Opening

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
  LeanVM.Protocol.Compile LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Complete

/-! ## Statement locks -/

example : ∀ {μ R : ℕ}, Whir.Admissible μ R → ∀ (q : Column μ) (claims : List StackClaim),
    (∀ c ∈ claims, StackClaim.Holds μ c q) → (∀ c ∈ claims, IsMultilinearFn μ c.1) →
    ∀ (h : List Ev), commits h = [stackCommit μ R q] → ∀ (S : Strategy),
    (∀ e, S.msg (h ++ e) = (honestOpening μ R q claims).msgAt e ∧
      S.word (h ++ e) = (honestOpening μ R q claims).wordAt e) →
    ∀ (chal : List Ev → E),
      S.runFrom chal (verifyStackedOpening μ R claims) h = some () ∧
        S.ShapedFrom chal (verifyStackedOpening μ R claims) h :=
  @runFrom_verifyStackedOpening

example : ∀ (H : Bytes → Digest) {μ R : ℕ}, Whir.Admissible μ R → ∀ (q : Column μ)
    (claims : List StackClaim), (∀ c ∈ claims, StackClaim.Holds μ c q) →
    (∀ c ∈ claims, IsMultilinearFn μ c.1) → ∀ (seed : Digest) (fuel : ℕ),
    (∀ h bits k cv, (openingProgram μ R claims).after h = some (.grind bits k) →
      findNonce H bits cv fuel ≠ none) →
    ∃ π, prove H (openingProgram μ R claims) (openingProver μ R q claims) seed fuel = some π ∧
      runProof (m := Id) H (openingProgram μ R claims) seed π = true :=
  @exists_prove_runProof_openingProgram

example : ∀ {μ lf : ℕ} {f₀ : List E} {B : List E → E}, f₀.length = 2 ^ μ → μ ≤ 64 →
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState) (W : List E) (cs : Commits),
      levels ≠ [] → Inv μ lf f₀ B s W → (levels.map (·.fold)).sum ≤ μ - s.folds.length →
      (∀ level ∈ levels.head?,
        LevelCommit cs index (μ - s.folds.length) (foldAll f₀ s.folds) level) →
      Follows (fun _ _ _ ↦ True) (hLevels μ f₀ index levels s W)
        (whirLevels μ lf B index levels s) cs :=
  @follows_whirLevels

example : ∀ {μ R q₀ : ℕ} {rest : List Whir.Level}, laneBits ≤ μ → μ ≤ 64 →
    laneBits + (rest.map (·.fold)).sum ≤ μ → ∀ (q : Column μ) (scales : List E)
    (claims : List StackClaim), (∀ c ∈ claims, StackClaim.Holds μ c q) →
    (∀ c ∈ claims, IsMultilinearFn μ c.1) →
    Follows (fun _ _ _ ↦ True)
      (hWhirRun μ (stackTable μ q) (basisTable μ scales claims) (⟨laneBits, R, q₀⟩ :: rest)
        (dot scales (claims.map (·.2))))
      (whirRun μ (⟨laneBits, R, q₀⟩ :: rest) (dot scales (claims.map (·.2)))
        (batchedBasis scales claims))
      [stackCommit μ R q] :=
  @follows_whirRun

/-- The opening program is `commitStack`, then `verifyStackedOpening`, then accept. -/
example (μ R : ℕ) (claims : List StackClaim) :
    openingProgram μ R claims =
      (do commitStack μ R; verifyStackedOpening μ R claims; return true) := rfl

/-- `verifyWhir` is `whirRun` on the derived configuration. -/
example (μ R : ℕ) (target : E) (B : List E → E) :
    verifyWhir μ R target B =
      Verifier.liftOption (deriveConfig μ R) >>= fun config ↦ whirRun μ config target B := rfl

/-- The stack's commitment is opened at level `0` with the shape `commitStack` announces. -/
example : stackCommit 15 1 ⟨Vector.replicate _ 0⟩ = (10, 64, stackWord 15 ⟨Vector.replicate _ 0⟩) :=
  rfl

/-! ## The honest round polynomials -/

/-- A field element from three words. -/
def eK (a b c : ℕ) : E := E.ofLimbs (K.ofBits a) (K.ofBits b) (K.ofBits c)

/-- A pseudo-random table of `n` entries. -/
def tbl (seed n : ℕ) : List E :=
  (List.range n).map fun i ↦ eK (i * 0x9E3779B97F4A7C15 + seed) (i * i + 3 * seed) (seed + 7 * i)

-- The sumcheck round: the polynomial built from the two scalars sent and the claim `Σ W·g` is,
-- at `c`, the sum of the folded product.
#guard (List.range 4).all fun k ↦
  let W := tbl 1 (2 ^ (k + 1))
  let g := tbl 2 (2 ^ (k + 1))
  let c := eK 5 6 7
  decide (polyEval (roundQuad (dot W g) W g) c = dot (foldPairs c W) (foldPairs c g))

-- Negative: with a claim off by one the identity fails (the claim is load-bearing).
#guard
  let W := tbl 1 8
  let g := tbl 2 8
  let c := eK 5 6 7
  polyEval (roundQuad (dot W g + 1) W g) c ≠ dot (foldPairs c W) (foldPairs c g)

-- `h(0) + h(1)` is the claim: the linear coefficient the verifier derives is the honest one.
#guard
  let W := tbl 3 16
  let g := tbl 4 16
  let h := roundQuad (dot W g) W g
  polyEval h 0 + polyEval h 1 = dot W g

-- The round polynomial is linear in the weight table (gluing).
#guard
  let W := tbl 1 8
  let T := tbl 9 8
  let g := tbl 2 8
  let s := eK 11 0 1
  roundC0 (axpy s W T) g = roundC0 W g + s * roundC0 T g ∧
    roundC2 (axpy s W T) g = roundC2 W g + s * roundC2 T g

-- The equality kernel is `eq(j, p)` entrywise, and pairing with it is the multilinear extension.
#guard
  let p := [eK 1 2 3, eK 4 5 6, eK 7 8 9]
  let t := tbl 6 8
  (List.range 8).all (fun j ↦ decide ((eqKernel p).getD j 0 = eqEval (boolPoint 3 j) p)) &&
    decide (dot t (eqKernel p) = multilinearEval t p)

-- Partial folding: fixing the first two of four coordinates.
#guard
  let t := tbl 8 16
  let r := [eK 2 3 5, eK 7 11 13]
  (List.range 4).all fun x ↦
    decide ((foldAll t r).getD x 0 =
      ((List.range 4).map fun j ↦ eqEval (boolPoint 2 j) r * t.getD (j + 4 * x) 0).sum)

/-! ## Scaled-down runs of the level loop -/

/-- A toy stack of `2^μ` cells. -/
def toyQ (μ seed : ℕ) : Column μ :=
  ⟨Vector.ofFn fun i ↦ K.ofBits (i.val * i.val * 0x9E3779B9 + seed)⟩

/-- The stack's cells as a list in `E`. -/
def cellsE {μ : ℕ} (q : Column μ) : List E :=
  (List.range (2 ^ μ)).map fun x ↦ ofK (q.values.getD x 0)

/-- A point of `μ` coordinates. -/
def pt (μ a : ℕ) : List E := (List.range μ).map fun i ↦ eK (a * i + 3) (2 * i + a) (i + 5)

/-- Two column claims on the stack: its extension at two points. -/
def toyClaims {μ : ℕ} (q : Column μ) : List StackClaim :=
  [(eqEval (pt μ 1), multilinearEval (cellsE q) (pt μ 1)),
   (eqEval (pt μ 7), multilinearEval (cellsE q) (pt μ 7))]

/-- The batching scales. -/
def toyScales : List E := [1, eK 3 4 5]

/-- The batched claimed value. -/
def toyTarget {μ : ℕ} (q : Column μ) : E := dot toyScales ((toyClaims q).map (·.2))

/-- The verifier: `whirRun` on a toy ladder. -/
def toyProg {μ : ℕ} (levels : List Whir.Level) (q : Column μ) (target : E) : Prog Unit :=
  whirRun μ levels target (batchedBasis toyScales (toyClaims q))

/-- The honest prover for the stack `q` and the claimed value `target`. -/
def toyScript {μ : ℕ} (levels : List Whir.Level) (q : Column μ) (target : E) : Script Unit :=
  hWhirRun μ (stackTable μ q) (basisTable μ toyScales (toyClaims q)) levels target

/-- The challenges: a function of the history's length. -/
def chal (h : List Ev) : E :=
  eK (h.length * 0x9E3779B97F4A7C15 + 5) (h.length + 11) (h.length * 3)

/-- The program run against the script's moves directly: the run `Strategy.runFrom` makes
against `Strategy.ofScript`, without replaying the script from its start at every message. -/
def lockstep {α β : Type} (chal : List Ev → E) :
    Script α → Prog β → List Ev → Commits → Option β
  | .ret _, .ret b, _, _ => some b
  | .send x k, .read k', h, cs => lockstep chal k (k' x) (h ++ [Ev.read x]) cs
  | .sample k, .sample k', h, cs =>
    lockstep chal (k (chal h)) (k' (chal h)) (h ++ [Ev.sample (chal h)]) cs
  | .grind k, .grind b k', h, cs => lockstep chal k k' (h ++ [Ev.grind b]) cs
  | .commit W k, .commit ht w k', h, cs =>
    lockstep chal k k' (h ++ [Ev.commit ht w W]) (cs ++ [(ht, w, W)])
  | .query k, .query i ps k', h, cs => match answerOf cs i ps with
    | some rows => lockstep chal (k rows) (k' rows) (h ++ [Ev.query rows]) cs
    | none => none
  | _, _, _, _ => none

/-- The prover with its first scalar off by one. -/
def tamperFirst {α : Type} : Script α → Script α
  | .send x k => .send (x + 1) k
  | .sample k => .sample fun c ↦ tamperFirst (k c)
  | .grind k => .grind (tamperFirst k)
  | .commit W k => .commit W (tamperFirst k)
  | .query k => .query fun r ↦ tamperFirst (k r)
  | .ret a => .ret a

/-- The toy ladder: the lane fold at rate `1` with one query, then one more fold with one query.
At `2^7` the residual is a single value; at `2^8` it has one variable, so the final level runs a
tail round. -/
def toyLadder : List Whir.Level := [⟨6, 1, 1⟩, ⟨1, 1, 1⟩]

-- The honest prover, as the strategy the theorems speak of, wins at `2^7`.
#guard
  let q := toyQ 7 7
  (Strategy.ofScript (toyScript toyLadder q (toyTarget q)) 1).runFrom chal
    (toyProg toyLadder q (toyTarget q)) [Ev.commit (7 - 6 + 1) 64 (stackWord 7 q)] = some ()

-- The honest prover wins at `2^8`, with a tail round.
#guard
  let q := toyQ 8 7
  lockstep chal (toyScript toyLadder q (toyTarget q)) (toyProg toyLadder q (toyTarget q))
    [Ev.commit (8 - 6 + 1) 64 (stackWord 8 q)] [(8 - 6 + 1, 64, stackWord 8 q)] = some ()

-- A first message off by one is rejected.
#guard
  let q := toyQ 7 7
  lockstep chal (tamperFirst (toyScript toyLadder q (toyTarget q)))
    (toyProg toyLadder q (toyTarget q))
    [Ev.commit (7 - 6 + 1) 64 (stackWord 7 q)] [(7 - 6 + 1, 64, stackWord 7 q)] = none

-- A claimed value off by one is rejected, the prover otherwise honest.
#guard
  let q := toyQ 7 7
  lockstep chal (toyScript toyLadder q (toyTarget q + 1)) (toyProg toyLadder q (toyTarget q + 1))
    [Ev.commit (7 - 6 + 1) 64 (stackWord 7 q)] [(7 - 6 + 1, 64, stackWord 7 q)] = none

-- The word of another stack is rejected.
#guard
  let q := toyQ 7 7
  let q' := toyQ 7 8
  lockstep chal (toyScript toyLadder q (toyTarget q)) (toyProg toyLadder q (toyTarget q))
    [Ev.commit (7 - 6 + 1) 64 (stackWord 7 q')] [(7 - 6 + 1, 64, stackWord 7 q')] = none

/-! ## The toy runs are instances of the theorem -/

/-- A column claim holds of the stack when its value is the stack's extension at its point. -/
theorem holds_eval {μ : ℕ} (q : Column μ) (z : List E) (hz : z.length = μ) :
    StackClaim.Holds μ (eqEval z, multilinearEval (cellsE q) z) q := by
  rw [StackClaim.Holds, Fin.sum_univ_eq_sum_range
    (fun x ↦ eqEval z (boolPoint μ x) * ofK (q.values.getD x 0)),
    multilinearEval_eq_sum μ _ z (by simp [cellsE]) hz]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  simp only [cellsE]
  rw [List.getD_eq_getElem _ _ (by simpa using hx), List.getElem_map, List.getElem_range,
    eqEval_comm, mul_comm]

theorem toyClaims_holds {μ : ℕ} (q : Column μ) : ∀ c ∈ toyClaims q, StackClaim.Holds μ c q := by
  intro c hc
  simp only [toyClaims, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> exact holds_eval q _ (by simp [pt])

theorem toyClaims_multilinear {μ : ℕ} (q : Column μ) :
    ∀ c ∈ toyClaims q, IsMultilinearFn μ c.1 := by
  intro c hc
  simp only [toyClaims, List.mem_cons, List.not_mem_nil, or_false] at hc
  have hl : ∀ a, (pt μ a).length = μ := fun a ↦ by simp [pt]
  rcases hc with rfl | rfl
  · have h := isMultilinearFn_eqEval (pt μ 1)
    rwa [hl] at h
  · have h := isMultilinearFn_eqEval (pt μ 7)
    rwa [hl] at h

/-- `follows_whirRun` on the toy instance at `2^8`: its hypotheses hold. -/
example : Follows (fun _ _ _ ↦ True) (toyScript toyLadder (toyQ 8 7) (toyTarget (toyQ 8 7)))
    (toyProg toyLadder (toyQ 8 7) (toyTarget (toyQ 8 7))) [stackCommit 8 1 (toyQ 8 7)] :=
  follows_whirRun (by decide) (by decide) (by decide) _ _ _ (toyClaims_holds _)
    (toyClaims_multilinear _)

/-- The toy stack is a candidate of its honest word, on every column. -/
example : toyQ 8 7 ∈ Candidates 8 1 (2 ^ (8 - laneBits + 1)) (stackWord 8 (toyQ 8 7)) :=
  ⟨Finset.univ, by simp, stackWord_agrees 8 1 _⟩

end LeanVMTests.Protocol.Whir.Complete.Opening
