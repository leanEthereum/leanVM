/-
  LeanVM.Protocol.ToArkLib.Flock.Zerocheck

  The zerocheck of a Flock argument as components: the point with its fixed prefix, the univariate
  skip's message and challenge, the multilinear rounds and the terminal values, each with its
  completeness. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Flock.Rounds
public import LeanVM.Protocol.ToCompPoly.Restriction

/-!
# The zerocheck with a univariate skip

The statement is that a batch of `2 ^ κ` Boolean R1CS blocks, stored as `2 ^ s` tables `z o i`
read off the oracles, satisfies its constraints and holds `1` at the constant position
(`BlockR1CS.BatchHolds`), beside a side condition `side` on the statement and the oracles that
the argument carries along untouched. `Params` fixes the sizes and the public constants: the
`2 · 2 ^ s` skip nodes (the skip domain, then its coset), the fixed prefix of the zerocheck point
and the constant position. The zerocheck is five components (Annex C, §C.2):

1. `pointDraws`: the verifier draws the `nRand` coordinates of the point after the fixed ones.
   The state (`pointRel`): every residual is zero on the coordinates fixed so far.
2. `skipMsg`: the prover sends `P` on the coset of the skip domain (`skipMessage`).
3. `skipDraw`: the verifier draws `z_skip` and interpolates `P(z_skip)` from `64` assumed zeros
   and the received values (`skipClaim`): the claim of the sumcheck.
4. `zcRounds`: the multilinear rounds, normalized (`zcFamily`), lowest coordinate first, the
   batch coordinates last; the invariant carries the side condition and the constant
   position's residual, zero on the batch coordinates drawn so far.
5. `zcEnd`: the prover sends `â, b̂` at the final point; `ĉ` is what the terminal identity leaves,
   `â · b̂ - R`. The state (`termRel`): the three values are the extensions'.

Nothing here transcribes a source.
-/

namespace LeanVM.Protocol

namespace Flock

open CompPoly CMlPolynomialEval OracleComp OracleSpec SumcheckRound BlockR1CS

@[expose] public section

/-- The sizes and public constants of a Flock argument over `F`: `2 ^ s` packed and skipped
coordinates, `m` within-block coordinates left after the skip, `κ` batch coordinates; the skip
nodes followed by their coset; the zerocheck point's `nFix` fixed coordinates, after which
`nRand` are drawn; the constant position of a block. -/
structure Params (F : Type) [Field F] where
  /-- The skipped coordinates. -/
  s : ℕ
  /-- The within-block coordinates bound by sumcheck. -/
  m : ℕ
  /-- The batch coordinates. -/
  κ : ℕ
  /-- The skip nodes, then their coset, with their inverse Lagrange denominators. -/
  nodes : SkipDomain F s
  /-- The number of fixed coordinates of the zerocheck point. -/
  nFix : ℕ
  /-- The number of drawn coordinates. -/
  nRand : ℕ
  /-- The fixed coordinates. -/
  fixed : Vector F nFix
  /-- The point covers the coordinates the sumcheck binds. -/
  hpoint : nFix + nRand = m + κ
  /-- The constant position of a block. -/
  cpos : Fin (2 ^ (s + m))

namespace Params

variable {F : Type} [Field F] (P : Params F)

/-- The zerocheck point: the fixed coordinates, then the drawn ones. -/
def point (v : Vector F P.nRand) : Vector F (P.m + P.κ) := Vector.cast P.hpoint (P.fixed ++ v)

/-- The partial point of the fixed coordinates and those drawn so far. -/
def pointPartial {j : ℕ} (v : Vector F j) : Partial F := Partial.ofVector 0 (P.fixed ++ v)

theorem pointPartial_push {j : ℕ} (v : Vector F j) (x : F) :
    P.pointPartial (v.push x) =
      Function.update (P.pointPartial v) (P.nFix + j) (some x) := by
  rw [pointPartial, Vector.append_push, Partial.ofVector_push, zero_add]
  rfl

theorem pointPartial_next {j : ℕ} (v : Vector F j) : P.pointPartial v (P.nFix + j) = none := by
  simp [pointPartial, Partial.ofVector]

theorem pointPartial_all (v : Vector F P.nRand) (k : ℕ) (hk : k < P.m + P.κ) :
    P.pointPartial v k = some (P.point v)[k] := by
  simp only [pointPartial, Partial.ofVector, point, Vector.getElem_cast]
  rw [dite_eq_left ⟨Nat.zero_le k, by have := P.hpoint; omega⟩]
  simp

end Params

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F] (P : Params F)
  {ι : Type} {O : ι → Type} [∀ i, OracleInterface (O i)] {W : Type}
  (C : BlockR1CS F (P.s + P.m))
  (z : (∀ i, O i) → Fin (2 ^ P.s) → CMlPolynomialEval F (P.m + P.κ))
  {S : Type} (side : S → (∀ i, O i) → Prop)

/-! ## The point -/

/-- The statement while the point is drawn: the input statement and the coordinates so far. -/
abbrev PointStmt (S F : Type) (j : ℕ) : Type := S × Vector F j

/-- While the point is drawn: the side condition, every residual zero on the coordinates fixed
so far, and every block holding `1` at the constant position. -/
def pointRel (j : ℕ) : Set ((PointStmt S F j × ∀ i, O i) × W) :=
  {p | side p.1.1.1 p.1.2 ∧
    (∀ i, RestrictedZero (errTable C (z p.1.2) i) (P.pointPartial p.1.1.2)) ∧
    ∀ t : Fin (2 ^ P.κ), (constTable P.cpos (z p.1.2))[t] = 0}

instance [∀ s o, Decidable (side s o)] (j : ℕ) (p : (PointStmt S F j × ∀ i, O i) × W) :
    Decidable (p ∈ pointRel P C z side j) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- One coordinate of the point, as a typed component. -/
def drawPoint (j : ℕ) :
    Typed.Def O (PointStmt S F j) W (PointStmt S F (j + 1)) W (Typed.drawSlot F) :=
  Typed.sampleChallenge O F (fun _ ↦ true) (fun s x ↦ (s.1, s.2.push x))

/-! ## The univariate skip -/

/-- The prover's first message, from the point and the oracles: `P` on the coset. -/
def skipHonest (p : (PointStmt S F P.nRand × ∀ i, O i) × W) : Vector F (2 ^ P.s) :=
  skipMessage P.nodes C (z p.1.2) (P.point p.1.1.2)

/-- After the skip message: the point's state, and the message is `P` on the coset. -/
def skipRel : Set (((PointStmt S F P.nRand × Vector F (2 ^ P.s)) × ∀ i, O i) × W) :=
  {p | (((p.1.1.1, p.1.2), p.2) ∈ pointRel P C z side P.nRand) ∧
    p.1.1.2 = skipHonest P C z ((p.1.1.1, p.1.2), p.2)}

instance [∀ s o, Decidable (side s o)]
    (p : ((PointStmt S F P.nRand × Vector F (2 ^ P.s)) × ∀ i, O i) × W) :
    Decidable (p ∈ skipRel P C z side) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The zerocheck's public data after the skip: the input statement, the point and `z_skip`. -/
abbrev ZcX (S F : Type) (n : ℕ) : Type := S × Vector F n × F

/-- After `z_skip`: the zerocheck's public data, no challenge yet, and the claim `P(z_skip)`
interpolated from the assumed zeros and the received values. -/
def skipNext (s : PointStmt S F P.nRand × Vector F (2 ^ P.s)) (Y : F) :
    Stmt (ZcX S F (P.m + P.κ)) F 0 :=
  ((s.1.1, P.point s.1.2, Y), (#v[], skipClaim P.nodes s.2 Y))

/-- `z_skip`, as a typed component. -/
def skipDraw : Typed.Def O (PointStmt S F P.nRand × Vector F (2 ^ P.s)) W
    (Stmt (ZcX S F (P.m + P.κ)) F 0) W (Typed.drawSlot F) :=
  Typed.sampleChallenge O F (fun _ ↦ true) (skipNext P)

/-! ## The multilinear rounds -/

/-- `â(Y, ·)`: the quirky extension of the left products. -/
def zcA (o : ∀ i, O i) (Y : F) : CMlPolynomialEval F (P.m + P.κ) :=
  skipTable P.nodes (leftTable C (z o)) Y

/-- `b̂(Y, ·)`: the quirky extension of the right products. -/
def zcB (o : ∀ i, O i) (Y : F) : CMlPolynomialEval F (P.m + P.κ) :=
  skipTable P.nodes (rightTable C (z o)) Y

/-- `ẑ(Y, ·)`: the quirky extension of the witness. -/
def zcC (o : ∀ i, O i) (Y : F) : CMlPolynomialEval F (P.m + P.κ) := skipTable P.nodes (z o) Y

/-- The zerocheck's sumcheck: `Σ_v eq(r, v) · (â · b̂ - ẑ)(z_skip, v)`, normalized, lowest
coordinate first; the invariant carries the side condition and the constant position's residual,
zero on the batch coordinates drawn so far. -/
def zcFamily : Family F (ZcX S F (P.m + P.κ)) O W 2 where
  claim ctx j c := partialSum
    (prodSub (zcA P C z ctx.1.2 ctx.1.1.2.2) (zcB P C z ctx.1.2 ctx.1.1.2.2)
      (zcC P z ctx.1.2 ctx.1.1.2.2)) ctx.1.1.2.1 j c
  poly ctx j c := normRound (zcA P C z ctx.1.2 ctx.1.1.2.2) (zcB P C z ctx.1.2 ctx.1.1.2.2)
    (zcC P z ctx.1.2 ctx.1.1.2.2) ctx.1.1.2.1 j c
  weight := normalizedWeights fun x : ZcX S F (P.m + P.κ) ↦ x.2.1
  inv ctx _ c := side ctx.1.1.1 ctx.1.2 ∧
    RestrictedZero (constTable P.cpos (z ctx.1.2)) (Partial.ofSuffix P.m c)

instance [∀ s o, Decidable (side s o)] (ctx : Ctx (ZcX S F (P.m + P.κ)) O W) (j : ℕ)
    (c : Vector F j) : Decidable ((zcFamily P C z side).inv ctx j c) :=
  inferInstanceAs (Decidable (_ ∧ _))

omit [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)] in
/-- The zerocheck's family is honest: its round polynomials pass the check and evaluate to the
next claim, and the invariant survives every challenge. -/
theorem zcFamily_honest : (zcFamily P C z side (W := W)).Honest (P.m + P.κ) where
  check := fun ctx _ c hj ↦
    weightedSum_normRound (zcA P C z ctx.1.2 ctx.1.1.2.2) (zcB P C z ctx.1.2 ctx.1.1.2.2)
      (zcC P z ctx.1.2 ctx.1.1.2.2) (fun x : ZcX S F (P.m + P.κ) ↦ x.2.1) ctx.1.1 hj c
  next := fun ctx _ c x hj ↦
    evaluate_normRound (zcA P C z ctx.1.2 ctx.1.1.2.2) (zcB P C z ctx.1.2 ctx.1.1.2.2)
      (zcC P z ctx.1.2 ctx.1.1.2.2) ctx.1.1.2.1 hj c x
  inv_push := fun ctx j c x _ h ↦ ⟨h.1, by
    by_cases hj : j < P.m
    · rw [Partial.ofSuffix_push_of_lt _ _ _ hj]
      exact h.2
    · rw [Partial.ofSuffix_push_of_le _ _ _ (by omega)]
      exact restrictedZero_update_of_none h.2 (Partial.ofSuffix_next _ _) x⟩

/-! ## The terminal values -/

/-- After the zerocheck: its public data, the point `χ` and the three values `â, b̂, ĉ` there. -/
abbrev TermStmt (S F : Type) (n : ℕ) : Type := ZcX S F n × Vector F n × F × F × F

/-- The prover sends `â` and `b̂` at the final point. -/
def termHonest (p : (Stmt (ZcX S F (P.m + P.κ)) F (P.m + P.κ) × ∀ i, O i) × W) : Vector F 2 :=
  #v[evalMle (zcA P C z p.1.2 p.1.1.1.2.2) p.1.1.2.1,
    evalMle (zcB P C z p.1.2 p.1.1.1.2.2) p.1.1.2.1]

/-- After `â, b̂`: the verifier derives `ĉ = â · b̂ - R` from the running claim `R`. -/
def termNext {n : ℕ} (s : Stmt (ZcX S F n) F n) (v : Vector F 2) : TermStmt S F n :=
  (s.1, s.2.1, v[0], v[1], v[0] * v[1] - s.2.2)

/-- The terminal values, as a typed component. -/
def zcEnd : Typed.Def O (Stmt (ZcX S F (P.m + P.κ)) F (P.m + P.κ)) W (TermStmt S F (P.m + P.κ))
    W (Typed.saySlot (Vector F 2)) :=
  Typed.sendChecked O _ (termHonest P C z) (fun _ _ ↦ true) termNext

/-- After the zerocheck: the side condition, the constant position's residual zero at the batch
coordinates of `χ`, and the three values are the quirky extensions at `(z_skip, χ)`. -/
def termRel : Set ((TermStmt S F (P.m + P.κ) × ∀ i, O i) × W) :=
  {p | side p.1.1.1.1 p.1.2 ∧
    RestrictedZero (constTable P.cpos (z p.1.2)) (Partial.ofSuffix P.m p.1.1.2.1) ∧
    evalMle (zcA P C z p.1.2 p.1.1.1.2.2) p.1.1.2.1 = p.1.1.2.2.1 ∧
    evalMle (zcB P C z p.1.2 p.1.1.1.2.2) p.1.1.2.1 = p.1.1.2.2.2.1 ∧
    evalMle (zcC P z p.1.2 p.1.1.1.2.2) p.1.1.2.1 = p.1.1.2.2.2.2}

instance [∀ s o, Decidable (side s o)] (p : (TermStmt S F (P.m + P.κ) × ∀ i, O i) × W) :
    Decidable (p ∈ termRel P C z side) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-! ## The components -/

/-- The first `j` drawn coordinates of the point, as a typed component. -/
def pointDraws : (j : ℕ) → Typed.Def O S W (PointStmt S F j) W (Typed.drawsSlot F j)
  | 0 => Typed.passThrough O fun s ↦ (s, #v[])
  | j + 1 => (pointDraws j).append (drawPoint j)

omit [DecidableEq F] [∀ i, OracleInterface (O i)] in
/-- Typed completeness of one coordinate. -/
theorem drawPointComplete (j : ℕ) :
    Typed.Complete (drawPoint (O := O) (W := W) (S := S) (F := F) j)
      (pointRel P C z side j) (pointRel P C z side (j + 1)) :=
  Typed.sampleChallengeComplete fun _ _ _ h ↦ ⟨rfl, fun x ↦ ⟨h.1, fun i ↦ by
    simp only [P.pointPartial_push]
    exact restrictedZero_update_of_none (h.2.1 i) (P.pointPartial_next _) x, h.2.2⟩⟩

omit [DecidableEq F] [∀ i, OracleInterface (O i)] in
/-- Typed completeness of the point's draws. -/
theorem pointDrawsComplete (relIn : Set ((S × ∀ i, O i) × W))
    (hIn : ∀ s o w, ((s, o), w) ∈ relIn → (((s, #v[]), o), w) ∈ pointRel P C z side 0) :
    (j : ℕ) → Typed.Complete (pointDraws j) relIn (pointRel P C z side j)
  | 0 => Typed.passThroughComplete hIn
  | j + 1 => (pointDrawsComplete relIn hIn j).append (drawPointComplete P C z side j)

/-- The skip message, as a typed component. -/
def skipMsg : Typed.Def O (PointStmt S F P.nRand) W (PointStmt S F P.nRand × Vector F (2 ^ P.s))
    W (Typed.saySlot (Vector F (2 ^ P.s))) :=
  Typed.sendChecked O _ (skipHonest P C z) (fun _ _ ↦ true) fun s msg ↦ (s, msg)

omit [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)] in
/-- Typed completeness of the skip message. -/
theorem skipMsgComplete :
    Typed.Complete (skipMsg P C z (S := S) (W := W)) (pointRel P C z side P.nRand)
      (skipRel P C z side) :=
  Typed.sendCheckedComplete fun _ _ _ h ↦ ⟨rfl, h, rfl⟩

omit [DecidableEq F] [∀ i, OracleInterface (O i)] in
/-- Typed completeness of `z_skip`. -/
theorem skipDrawComplete
    (hnodes : Function.Injective fun j : Fin (2 ^ P.s + 2 ^ P.s) ↦ P.nodes.pts[j]) :
    Typed.Complete (skipDraw P (S := S) (O := O) (W := W)) (skipRel P C z side)
      (rel (zcFamily P C z side) 0) :=
  Typed.sampleChallengeComplete fun s o w h ↦ ⟨rfl, fun Y ↦ by
    obtain ⟨⟨hside, hres, hconst⟩, hmsg⟩ := h
    refine ⟨⟨hside, ?_⟩, ?_⟩
    · show RestrictedZero _ (Partial.ofSuffix P.m (#v[] : Vector F 0))
      rw [Partial.ofSuffix_of_le _ _ (Nat.zero_le _), restrictedZero_empty_iff]
      exact hconst
    · show skipClaim P.nodes s.2 Y = partialSum _ (P.point s.1.2) 0 #v[]
      have hzero : ∀ i, evalMle (errTable C (z o) i) (P.point s.1.2) = 0 := fun i ↦
        (restrictedZero_of_all _ _ _ (P.pointPartial_all s.1.2)).mp (hres i)
      rw [hmsg, skipHonest, skipClaim_skipMessage P.nodes hnodes C (z o) _ hzero,
        partialSum_zero, pValue_eq]
      rfl⟩

/-- The rounds on the within-block coordinates, as a typed component. -/
def zcRoundsLow : Typed.Def O (Stmt (ZcX S F (P.m + P.κ)) F 0) W
    (Stmt (ZcX S F (P.m + P.κ)) F P.m) W (Typed.roundsSlot F 2 P.m) :=
  rounds (zcFamily P C z side (W := W)).poly (zcFamily P C z side (W := W)).weight P.m P.m 0
    (Nat.zero_add _)

/-- The rounds on the batch coordinates, as a typed component. -/
def zcRoundsHigh : Typed.Def O (Stmt (ZcX S F (P.m + P.κ)) F P.m) W
    (Stmt (ZcX S F (P.m + P.κ)) F (P.m + P.κ)) W (Typed.roundsSlot F 2 P.κ) :=
  rounds (zcFamily P C z side (W := W)).poly (zcFamily P C z side (W := W)).weight (P.m + P.κ)
    P.κ P.m rfl

omit [∀ i, OracleInterface (O i)] in
/-- Typed completeness of the rounds on the within-block coordinates. -/
theorem zcRoundsLowComplete :
    Typed.Complete (zcRoundsLow P C z side (O := O) (W := W))
      (rel (zcFamily P C z side) 0) (rel (zcFamily P C z side) P.m) :=
  roundsComplete (zcFamily P C z side) P.m
    { check := fun ctx j c hj ↦ (zcFamily_honest P C z side).check ctx j c (by omega)
      next := fun ctx j c x hj ↦ (zcFamily_honest P C z side).next ctx j c x (by omega)
      inv_push := fun ctx j c x hj ↦ (zcFamily_honest P C z side).inv_push ctx j c x (by omega) }
    P.m 0 (Nat.zero_add _)

omit [∀ i, OracleInterface (O i)] in
/-- Typed completeness of the rounds on the batch coordinates. -/
theorem zcRoundsHighComplete :
    Typed.Complete (zcRoundsHigh P C z side (O := O) (W := W))
      (rel (zcFamily P C z side) P.m) (rel (zcFamily P C z side) (P.m + P.κ)) :=
  roundsComplete (zcFamily P C z side) (P.m + P.κ) (zcFamily_honest P C z side) P.κ P.m rfl

omit [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)] in
/-- Typed completeness of the terminal message. -/
theorem zcEndComplete :
    Typed.Complete (zcEnd P C z (S := S) (O := O) (W := W))
      (rel (zcFamily P C z side) (P.m + P.κ)) (termRel P C z side) :=
  Typed.sendCheckedComplete fun s o w h ↦ ⟨rfl, by
    obtain ⟨⟨hside, hconst⟩, hclaim⟩ := h
    refine ⟨hside, hconst, rfl, rfl, ?_⟩
    show evalMle (zcC P z o s.1.2.2) s.2.1 =
      evalMle (zcA P C z o s.1.2.2) s.2.1 * evalMle (zcB P C z o s.1.2.2) s.2.1 - s.2.2
    rw [hclaim]
    simp only [zcFamily, partialSum_self, prodSub]
    ring⟩

end

end Flock

end LeanVM.Protocol
