/-
  LeanVM.Guest.Batch.Honest

  The honest batching prover, and its completeness: true children's claims and a nonce that
  passes the proof of work give hints the batching program accepts, deferring a true claim.
-/

module

public import LeanVM.Guest.Batch.Node

/-!
# The honest batching

A parent forms its witness from its children's claims: the hints of the batching
(`BatchingHints`), which the honest prover computes (`honestHints`, as `crates/aggregation/src/deferred.rs`
does). After the proof of work on the nonce, the transcript squeezes `λ`, whose powers are the
lambdas; the sumcheck sums `P = B̃ · W` over the cube of `n = log₂ |bytecode|` coordinates, `B̃` the
bytecode's multilinear extension and `W` the batched weight at the lambdas (`bytecodePoly`).
Round `i`, after the challenges `pre = r_1..r_{i-1}`, sends `(g(1), g(∞))` of the round polynomial
`g(y) = cubeSum n P (pre ++ [y])`: `g(1)` is the cube sum at `pre ++ [1]`, `g(∞)` its leading
coefficient, `Σ_x (B̃₀ + B̃₁)(W₀ + W₁)` over the remaining Boolean `x` (`leadCoeff`, `round_msg`'s
second value; characteristic two, a difference is a sum). The prover runs alongside the
verifier's sponge (`honestRounds`): it absorbs the message and squeezes the challenge exactly as
`rsRun` does, so the verifier's challenges on the produced stream are the prover's. The final
value is `B̃` at the challenges (`value = rows[0]`).

The proof, by induction on rounds (`rsRun_honestRounds`): the claim before round `i` is
`cubeSum n P pre`. A product of two multilinear functions is, along one coordinate,
`a y² + b y + c` with `a` the leading coefficient above and `c` the value at `0`
(`affine_mul`), so the wire's round polynomial from the claim and the message is the cube sum
along the round's coordinate (`cubeSum_mul_round`), and folding at the challenge `r` gives the
claim `cubeSum n P (pre ++ [r])`. After the last round the claim is `P r = B̃(r) · W(r)`
(`cubeSum_full`), the final check. The first claim, the lambdas' combination of the children's
claimed values, is the cube sum: the claims are true (`batchedClaim_eq_bytecodeTrue`,
`bytecode_cubeSum`).

* `honest_batching`: for true children's claims of the bytecode's shape and a nonce that passes
  the proof of work, the batching program, over the deployed Keccak-f[1600], accepts the honest
  stream with a deferred claim that is true (`HoldsWithShape`): (a) and (b) of the batching.
* `deferredClaimBatched_honest`: the same in the statement's vocabulary, a node's
  `DeferredClaimBatched` with the honest hints; `deferredClaimBatched_leaf`: a leaf's deferred
  claim, the bytecode at the zero point, is batched and true. By induction on the tree, the
  carried claims of honest children are true at every level.
* `honest_root_holdsWithShape`: (c), the part reachable in the model: an honest root's deferred
  claim passes the outer verifier's recomputation of the deferred value.

The nonce is a hypothesis: that the proof of work of `batchLambdaGrindBits` bits passes on it is
a property of the concrete Keccak-f[1600] at the transcript's sponge (`powStep` at
`batchSponge cs`); that some nonce passes is not provable in general, and the Rust prover grinds
for one. Nothing here evaluates the permutation.

What (c) does not cover. The outer verifier (`AggregateProof::verify`,
`crates/aggregation/src/proof.rs`) is Rust and is not modelled: its check that both claim lists
are strictly sorted, the derivation of the DA digest it recomputes (the root's grinded
membership challenge, `crates/verifier/src/da.rs`), the statement digest it recomputes from
them, and the parsing of the proof's bytes (`from_bytes`). Its last check, `verify_execution` on
the guest's bytecode, is the protocol's completeness: `LeanVM.Node.aggregate_complete_of`
(`LeanVM/Guest/EndRpm.lean`) and `honest_proof_rarely_refused`
(`HonestProofRarelyRefused`, `LeanVM/Guest/HonestChildren.lean`), in the random-permutation
model, not for the deployed Keccak-f[1600].
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd LeanVM.Node Finset

@[expose] public section

/-! ## A round of the honest sumcheck -/

/-- **The leading coefficient** of the round polynomial of `u · v` after the challenges `pre`:
`Σ_x (u₀ + u₁)(v₀ + v₁)` over the remaining Boolean `x`, `u_b` at `pre ++ b :: x`
(`round_msg`'s second value, `crates/aggregation/src/deferred.rs`). -/
def leadCoeff (n : ℕ) (u v : List E → E) (pre : List E) : E :=
  ∑ i ∈ range (2 ^ (n - pre.length - 1)),
    (u (pre ++ 0 :: boolPoint (n - pre.length - 1) i) +
        u (pre ++ 1 :: boolPoint (n - pre.length - 1) i)) *
      (v (pre ++ 0 :: boolPoint (n - pre.length - 1) i) +
        v (pre ++ 1 :: boolPoint (n - pre.length - 1) i))

/-- A product of two affine functions of `y`, as a quadratic in characteristic two. -/
theorem affine_mul (u0 u1 v0 v1 y : E) :
    ((1 + y) * u0 + y * u1) * ((1 + y) * v0 + y * v1) =
      (u0 + u1) * (v0 + v1) * y ^ 2 + (u0 * v0 + u1 * v1 + (u0 + u1) * (v0 + v1)) * y +
        u0 * v0 := by
  linear_combination (-(u1 * v1 * y)) * Whir.Complete.two_eq_zero_E

/-- The wire's round polynomial from the claim `g(0) + g(1)` and the message `(g(1), a)` is the
quadratic of leading coefficient `a` through `g(0)` and `g(1)`. -/
theorem roundPoly_eq (a s0 s1 y : E) :
    sumcheckRoundPolynomial (s0 + s1) (s1, a) y = a * y ^ 2 + (s0 + s1 + a) * y + s0 := by
  unfold sumcheckRoundPolynomial
  linear_combination (s1 * y + s1) * Whir.Complete.two_eq_zero_E

/-- **The honest round**: from the claim `cubeSum n (u · v) pre`, the message of the cube sum at
`pre ++ [1]` and the leading coefficient folds, at any `y`, to the cube sum at `pre ++ [y]`. -/
theorem cubeSum_mul_round {n : ℕ} {u v : List E → E} (hu : Multilinear n u)
    (hv : Multilinear n v) {pre : List E} (h : pre.length < n) (y : E) :
    sumcheckRoundPolynomial (cubeSum n (fun p ↦ u p * v p) pre)
        (cubeSum n (fun p ↦ u p * v p) (pre ++ [1]), leadCoeff n u v pre) y =
      cubeSum n (fun p ↦ u p * v p) (pre ++ [y]) := by
  rw [cubeSum_split h, roundPoly_eq]
  have hk : ∀ x : E, n - (pre ++ [x]).length = n - pre.length - 1 := fun x ↦ by simp; omega
  have hl : ∀ i, pre.length + 1 + (boolPoint (n - pre.length - 1) i).length = n := fun i ↦ by
    rw [Whir.Complete.length_boolPoint]; omega
  have eu : ∀ i, u (pre ++ y :: boolPoint (n - pre.length - 1) i) =
      (1 + y) * u (pre ++ 0 :: boolPoint (n - pre.length - 1) i) +
        y * u (pre ++ 1 :: boolPoint (n - pre.length - 1) i) := fun i ↦ hu pre _ (hl i) y
  have ev : ∀ i, v (pre ++ y :: boolPoint (n - pre.length - 1) i) =
      (1 + y) * v (pre ++ 0 :: boolPoint (n - pre.length - 1) i) +
        y * v (pre ++ 1 :: boolPoint (n - pre.length - 1) i) := fun i ↦ hv pre _ (hl i) y
  simp only [cubeSum, hk, List.append_assoc, List.singleton_append, leadCoeff, eu, ev, affine_mul,
    sum_add_distrib, ← sum_mul]

/-! ## The honest rounds, on the verifier's sponge -/

/-- **The honest sumcheck's rounds** of `u · v` on points of `n` coordinates, `k` rounds after
the challenges `pre`, from the sponge `sp`: each round's message `(g(1), g(∞))`, absorbed, and the
challenge squeezed after it, as the verifier's rounds (`rsStep`) do. The messages and the final
point, `pre` followed by the challenges. -/
def honestRounds (n : ℕ) (u v : List E → E) : ℕ → List E → Sponge → List (E × E) × List E
  | 0, pre, _ => ([], pre)
  | k + 1, pre, sp =>
    let g : E × E := (cubeSum n (fun p ↦ u p * v p) (pre ++ [1]), leadCoeff n u v pre)
    let sp' := (sq (obsAll sp [g.1, g.2])).2
    let rest := honestRounds n u v k (pre ++ [challengeOf sp'.state]) sp'
    (g :: rest.1, rest.2)

theorem honestRounds_length (n : ℕ) (u v : List E → E) :
    ∀ (k : ℕ) (pre : List E) (sp : Sponge),
      (honestRounds n u v k pre sp).1.length = k ∧
        (honestRounds n u v k pre sp).2.length = pre.length + k
  | 0, pre, sp => by simp [honestRounds]
  | k + 1, pre, sp => by
    obtain ⟨h1, h2⟩ := honestRounds_length n u v k
      (pre ++ [challengeOf (sq (obsAll sp [cubeSum n (fun p ↦ u p * v p) (pre ++ [1]),
        leadCoeff n u v pre])).2.state])
      (sq (obsAll sp [cubeSum n (fun p ↦ u p * v p) (pre ++ [1]), leadCoeff n u v pre])).2
    simp only [honestRounds]
    rw [List.length_cons, h1, h2, List.length_append, List.length_singleton]
    omega

/-- **The honest rounds' completeness**: from the claim `cubeSum n (u · v) pre`, the verifier's
rounds on the honest messages take the honest challenges and end at the claim `u r · v r`, `r`
the final point. -/
theorem rsRun_honestRounds {n : ℕ} {u v : List E → E} (hu : Multilinear n u)
    (hv : Multilinear n v) :
    ∀ (k : ℕ) (pre : List E) (sp : Sponge), pre.length + k = n →
      pre ++ (rsRun (honestRounds n u v k pre sp).1 (cubeSum n (fun p ↦ u p * v p) pre) sp).1.1 =
          (honestRounds n u v k pre sp).2 ∧
        (rsRun (honestRounds n u v k pre sp).1 (cubeSum n (fun p ↦ u p * v p) pre) sp).1.2 =
          u (honestRounds n u v k pre sp).2 * v (honestRounds n u v k pre sp).2
  | 0, pre, sp, h => by
    simp only [honestRounds, rsRun, List.append_nil, true_and]
    exact cubeSum_full (by omega)
  | k + 1, pre, sp, h => by
    obtain ⟨h1, h2⟩ := rsRun_honestRounds hu hv k
      (pre ++ [challengeOf (sq (obsAll sp [cubeSum n (fun p ↦ u p * v p) (pre ++ [1]),
        leadCoeff n u v pre])).2.state])
      (sq (obsAll sp [cubeSum n (fun p ↦ u p * v p) (pre ++ [1]), leadCoeff n u v pre])).2
      (by simp; omega)
    simp only [honestRounds, rsRun, rsStep, cubeSum_mul_round hu hv (show pre.length < n by omega)]
    refine ⟨?_, h2⟩
    rw [← h1, List.append_assoc, List.singleton_append]

/-! ## The honest prover -/

/-- The lambdas and the sponge at the sumcheck, after the proof of work on `nonce`: `lambdasB`
and `spB` of hints with that nonce. -/
def honestLambdas (cs : List ChildClaims) (nonce : E) : List (E × E) × Sponge :=
  sqL cs.length (powStep keccakF1600 (batchSponge cs) nonce).2

/-- The honest sumcheck of the bytecode's batching: its messages and its challenges. -/
def honestSumcheck (bytecode : List K) (cs : List ChildClaims) (nonce : E) :
    List (E × E) × List E :=
  honestRounds (Nat.log2 bytecode.length) (multilinearEval (bytecode.map ofK))
    (batchedBytecodeWeight cs (honestLambdas cs nonce).1) (Nat.log2 bytecode.length) []
    (honestLambdas cs nonce).2

/-- **The honest batching prover** (`aggregate_deferred_claims`, `crates/aggregation/src/deferred.rs`):
the nonce, the honest sumcheck's messages, and the bytecode's value at its challenges. -/
def honestHints (bytecode : List K) (cs : List ChildClaims) (nonce : E) : BatchingHints :=
  ⟨nonce, (honestSumcheck bytecode cs nonce).1,
    multilinearEval (bytecode.map ofK) (honestSumcheck bytecode cs nonce).2⟩

/-- The honest batching's deferred claim: the bytecode's value at the sumcheck's challenges. -/
def honestDeferred (bytecode : List K) (cs : List ChildClaims) (nonce : E) :
    DeferredBytecodeClaim :=
  ⟨(honestSumcheck bytecode cs nonce).2,
    multilinearEval (bytecode.map ofK) (honestSumcheck bytecode cs nonce).2⟩

/-- True claims' combination is the true values' combination. -/
theorem batchedClaim_eq_bytecodeTrue {bytecode : List K} {cs : List ChildClaims}
    (htrue : ∀ c ∈ cs, c.freshClaim.Holds bytecode ∧ c.carriedClaim.HoldsWithShape bytecode)
    (l : List (E × E)) : batchedClaim cs l = bytecodeTrue bytecode cs l := by
  induction cs generalizing l with
  | nil => simp [batchedClaim, bytecodeTrue]
  | cons c cs ih =>
    cases l with
    | nil => simp [batchedClaim, bytecodeTrue]
    | cons x l =>
      have e := ih (fun c' hc' ↦ htrue c' (List.mem_cons_of_mem _ hc')) l
      obtain ⟨hf, -, -, hc⟩ := htrue c List.mem_cons_self
      simp only [batchedClaim, bytecodeTrue, List.zipWith_cons_cons, Whir.Complete.sumE_eq,
        List.sum_cons] at e ⊢
      rw [e, ← hf, ← hc]

/-- The honest deferred claim is true. -/
theorem honestDeferred_holds {bytecode : List K}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length) (cs : List ChildClaims) (nonce : E) :
    (honestDeferred bytecode cs nonce).HoldsWithShape bytecode := by
  have hl := (honestRounds_length (Nat.log2 bytecode.length) (multilinearEval (bytecode.map ofK))
    (batchedBytecodeWeight cs (honestLambdas cs nonce).1) (Nat.log2 bytecode.length) []
    (honestLambdas cs nonce).2).2
  rw [List.length_nil, Nat.zero_add] at hl
  refine ⟨hl, ?_, rfl⟩
  change 2 ^ (honestSumcheck bytecode cs nonce).2.length = bytecode.length
  rw [honestSumcheck, hl, ← hb]

/-- **The guest program's transcript defers the honest claim** (`Node.batch`), for true
children's claims of the bytecode's shape and a nonce that passes the proof of work. -/
theorem batch_honest {bytecode : List K} (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)
    {cs : List ChildClaims} (hshape : ∀ c ∈ cs, ChildHasBytecodeShape bytecode c)
    (htrue : ∀ c ∈ cs, c.freshClaim.Holds bytecode ∧ c.carriedClaim.HoldsWithShape bytecode)
    {nonce : E}
    (hpow : powOk batchLambdaGrindBits (powStep keccakF1600 (batchSponge cs) nonce).1 = true) :
    batch cs (honestHints bytecode cs nonce) = some (honestDeferred bytecode cs nonce) := by
  have hL : (bytecode.map ofK).length = 2 ^ Nat.log2 bytecode.length := by
    rw [List.length_map]; exact hb
  have hp : ∀ c ∈ cs, c.freshClaim.bytecodePoint.length = Nat.log2 bytecode.length ∧
      c.carriedClaim.bytecodePoint.length = Nat.log2 bytecode.length :=
    fun c hc ↦ ⟨(hshape c hc).1, (hshape c hc).2⟩
  have hu := multilinear_multilinearEval hL
  have hv := multilinear_bytecodeWeight hp (honestLambdas cs nonce).1
  obtain ⟨h1, h2⟩ := rsRun_honestRounds hu hv (Nat.log2 bytecode.length) []
    (honestLambdas cs nonce).2 (by simp)
  rw [List.nil_append] at h1
  have e1 : (honestHints bytecode cs nonce).sumcheckMessages =
      (honestRounds (Nat.log2 bytecode.length) (multilinearEval (bytecode.map ofK))
        (batchedBytecodeWeight cs (honestLambdas cs nonce).1) (Nat.log2 bytecode.length) []
        (honestLambdas cs nonce).2).1 := rfl
  have e2 : claimB cs (honestHints bytecode cs nonce) =
      cubeSum (Nat.log2 bytecode.length) (fun p ↦ multilinearEval (bytecode.map ofK) p *
        batchedBytecodeWeight cs (honestLambdas cs nonce).1 p) [] :=
    (batchedClaim_eq_bytecodeTrue htrue _).trans (bytecode_cubeSum hb hp _).symm
  have e3 : spB cs (honestHints bytecode cs nonce) = (honestLambdas cs nonce).2 := rfl
  have e4 : lambdasB cs (honestHints bytecode cs nonce) = (honestLambdas cs nonce).1 := rfl
  have hpow' : powOk batchLambdaGrindBits (powB cs (honestHints bytecode cs nonce)).1 = true :=
    hpow
  rw [batch_eq', ite_eq_left hpow', e1, e2, e3, e4, h1, h2]
  exact ite_eq_left rfl

/-! ## The batching, honest -/

/-- **The batching program accepts the honest stream**, deferring the honest claim. -/
theorem honest_batching_run {bytecode : List K}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)
    {cs : List ChildClaims} (hshape : ∀ c ∈ cs, ChildHasBytecodeShape bytecode c)
    (htrue : ∀ c ∈ cs, c.freshClaim.Holds bytecode ∧ c.carriedClaim.HoldsWithShape bytecode)
    {nonce : E}
    (hpow : powOk batchLambdaGrindBits (powStep keccakF1600 (batchSponge cs) nonce).1 = true) :
    runBatching (m := Id) keccakF1600
      (nodeBatchingProgram (· = honestDeferred bytecode cs nonce) bytecode cs)
      ⟨batchingStream cs (honestHints bytecode cs nonce), []⟩ = true := by
  rw [runBatching_deployed]
  exact (batchRun_iff_of_rounds (h := honestHints bytecode cs nonce)
    (d := honestDeferred bytecode cs nonce)
    (honestRounds_length (Nat.log2 bytecode.length) (multilinearEval (bytecode.map ofK))
      (batchedBytecodeWeight cs (honestLambdas cs nonce).1) (Nat.log2 bytecode.length) []
      (honestLambdas cs nonce).2).1).mpr (batch_honest hb hshape htrue hpow)

/-- **The honest batching**, (a) and (b): for true children's claims of the bytecode's shape and
a nonce that passes the proof of work of `batchLambdaGrindBits` bits at the transcript's sponge
after the children's cells, the batching program over the deployed Keccak-f[1600] accepts the
honest hints' stream, deferring a true claim. -/
theorem honest_batching {bytecode : List K} (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)
    {cs : List ChildClaims}
    (hshape : ∀ c ∈ cs, ChildHasBytecodeShape bytecode c)
    (htrue : ∀ c ∈ cs, c.freshClaim.Holds bytecode ∧ c.carriedClaim.HoldsWithShape bytecode)
    (nonce : E)
    (hpow : powOk batchLambdaGrindBits (powStep keccakF1600 (batchSponge cs) nonce).1 = true) :
    let h := honestHints bytecode cs nonce
    ∃ d : DeferredBytecodeClaim, d.HoldsWithShape bytecode ∧
      runBatching (m := Id) keccakF1600 (nodeBatchingProgram (· = d) bytecode cs)
        ⟨batchingStream cs h, []⟩ = true :=
  ⟨_, honestDeferred_holds hb cs nonce, honest_batching_run hb hshape htrue hpow⟩

/-! ## A node's deferred claim -/

/-- A node's children as `DeferredClaimBatched` batches them: each child's statement's digest,
its proof's claim and its statement's deferred claim. -/
def nodeChildClaims (seed : Digest) (w : NodeWitness) : List ChildClaims :=
  w.children.map fun child ↦
    ⟨statementDigest seed child.statement, child.freshClaim, child.statement.deferredClaim⟩

/-- **A parent's honest batching**, in the statement's vocabulary: for children whose claims are
true and of the bytecode's shape, and a nonce that passes the proof of work, the node's statement
with the honest deferred claim is batched (`DeferredClaimBatched`) by the witness with the honest
hints, and that claim is true. -/
theorem deferredClaimBatched_honest {bytecode : List K}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length) {seed : Digest} {w : NodeWitness}
    (hne : w.children ≠ [])
    (hshape : ∀ c ∈ nodeChildClaims seed w, ChildHasBytecodeShape bytecode c)
    (htrue : ∀ c ∈ nodeChildClaims seed w,
      c.freshClaim.Holds bytecode ∧ c.carriedClaim.HoldsWithShape bytecode)
    (claims : NodeClaims) (nonce : E)
    (hpow : powOk batchLambdaGrindBits
      (powStep keccakF1600 (batchSponge (nodeChildClaims seed w)) nonce).1 = true) :
    (honestDeferred bytecode (nodeChildClaims seed w) nonce).HoldsWithShape bytecode ∧
      DeferredClaimBatched bytecode seed
        ⟨claims, honestDeferred bytecode (nodeChildClaims seed w) nonce⟩
        { w with batchingHints := honestHints bytecode (nodeChildClaims seed w) nonce } := by
  refine ⟨honestDeferred_holds hb _ nonce, ?_⟩
  dsimp only [DeferredClaimBatched]
  rw [ite_eq_right hne]
  exact honest_batching_run hb hshape htrue hpow

/-- What a leaf defers (`DeferredBytecodeClaim::leaf`, `crates/aggregation/src/deferred.rs`): the
bytecode at the zero point. -/
def leafDeferred (bytecode : List K) : DeferredBytecodeClaim :=
  ⟨List.replicate (Nat.log2 bytecode.length) 0,
    multilinearEval (bytecode.map ofK) (List.replicate (Nat.log2 bytecode.length) 0)⟩

/-- **A leaf's deferred claim** is at the zero point and true. -/
theorem leafDeferred_holds {bytecode : List K}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length) :
    (leafDeferred bytecode).HasZeroPoint bytecode ∧
      (leafDeferred bytecode).HoldsWithShape bytecode :=
  ⟨rfl, List.length_replicate ..,
    show 2 ^ (List.replicate (Nat.log2 bytecode.length) (0 : E)).length = bytecode.length by
      rw [List.length_replicate, ← hb],
    rfl⟩

/-- **A leaf's deferred claim is batched**: a node without children, whatever its hints. -/
theorem deferredClaimBatched_leaf {bytecode : List K} {seed : Digest} {w : NodeWitness}
    (hw : w.children = []) (claims : NodeClaims) :
    DeferredClaimBatched bytecode seed ⟨claims, leafDeferred bytecode⟩ w := by
  unfold DeferredClaimBatched
  rw [ite_eq_left hw]
  exact rfl

/-! ## The root -/

/-- **(c), an honest root's deferred claim passes the outer verifier's recomputation**: a node
whose children's claims are true and of the bytecode's shape, with a nonce that passes the proof
of work if it has children, has hints and a deferred claim that the node batches
(`DeferredClaimBatched`) and that is true (`HoldsWithShape`, what `AggregateProof::verify`
recomputes of the root's deferred value). The rest of the outer verifier is not modelled: see
the module's docstring. -/
theorem honest_root_holdsWithShape {bytecode : List K}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length) {seed : Digest} (w : NodeWitness)
    (hshape : ∀ c ∈ nodeChildClaims seed w, ChildHasBytecodeShape bytecode c)
    (htrue : ∀ c ∈ nodeChildClaims seed w,
      c.freshClaim.Holds bytecode ∧ c.carriedClaim.HoldsWithShape bytecode)
    (hnonce : w.children ≠ [] → ∃ nonce : E, powOk batchLambdaGrindBits
      (powStep keccakF1600 (batchSponge (nodeChildClaims seed w)) nonce).1 = true)
    (claims : NodeClaims) :
    ∃ (d : DeferredBytecodeClaim) (h : BatchingHints), d.HoldsWithShape bytecode ∧
      DeferredClaimBatched bytecode seed ⟨claims, d⟩ { w with batchingHints := h } := by
  by_cases hw : w.children = []
  · exact ⟨leafDeferred bytecode, w.batchingHints, (leafDeferred_holds hb).2,
      deferredClaimBatched_leaf hw claims⟩
  · obtain ⟨nonce, hpow⟩ := hnonce hw
    obtain ⟨hd, hbat⟩ := deferredClaimBatched_honest hb hw hshape htrue claims nonce hpow
    exact ⟨_, _, hd, hbat⟩

end

/-- info: 'LeanVM.Guest.Batch.honest_batching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms honest_batching

/-- info: 'LeanVM.Guest.Batch.deferredClaimBatched_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms deferredClaimBatched_honest

/-- info: 'LeanVM.Guest.Batch.leafDeferred_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms leafDeferred_holds

/-- info: 'LeanVM.Guest.Batch.deferredClaimBatched_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms deferredClaimBatched_leaf

/-- info: 'LeanVM.Guest.Batch.honest_root_holdsWithShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms honest_root_holdsWithShape

end LeanVM.Guest.Batch
