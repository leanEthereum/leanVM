/-
  LeanVM.Protocol.Whir.Sound.LevelMid

  The specification of a WHIR level with a next one: the fold rounds, the next commitment and the
  folded lane's high part, the out-of-domain group, the query group after its grind, the batching
  challenge after its grind with the openings, and the glued claim handed to the next level.
-/

module

public import LeanVM.Protocol.Whir.Sound.LevelFacts

/-!
# A level with a next one

`whirLevels` on `level :: next :: rest` (`crates/verifier/src/whir.rs:240-341`): the level's fold
rounds (`foldRoundsSpec`), then `midTail`: the next commitment, the high part, the two
out-of-domain points (one group, no grind, `eOod`), their values, a `17`-bit grind and the
positions (`eQuery`), a `14`-bit grind and `λ` with the openings (`eLam`), the glued claim, and
the next level.

`LevelPre μ ℓ₀ w i P pre s cs`: the doom at the start of level `i`: the invariant with no round,
and the level's commitment is the last, of the level's shape. `MidOK P P' t εmax`: the level's
code relations and its groups' escapes within `εmax` after their grinds.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset

@[expose] public section

/-! ## The program -/

/-- The rest of a level with a next one, after its fold rounds. -/
def midTail (logN laneFolds : ℕ) (eb : List E → E) (index : ℕ) (level next : Whir.Level)
    (rest : List Whir.Level) (s : WhirState) (rounds : List FoldRound) : VerifierProgram Unit :=
  readCommitment (logN - s.gammas.length - next.fold + next.logInvRate) (2 * 2 ^ next.fold) >>=
    fun _ ↦ readScalars level.fold >>= fun high ↦
  sampleOodPoints (logN - s.gammas.length) Whir.oodSamples >>= fun pts ↦
  readScalars Whir.oodSamples >>= fun ys ↦
  grindProofOfWork Whir.queryGrindingBits >>= fun _ ↦
  sampleQueries (logN - s.gammas.length + level.logInvRate) level.queries >>= fun qs ↦
  grindProofOfWork Whir.batchGrindingBits >>= fun _ ↦
  sampleChallenge >>= fun lam ↦
  queryOpenings index qs >>= fun words ↦
  whirLevels logN laneFolds eb (index + 1) (next :: rest)
    (glueLevel s lam (logN - s.gammas.length) pts ys qs (powers lam qs.length)
      (batchedOf index (logN - s.gammas.length) rounds high qs (powers lam qs.length) words))

theorem whirLevels_mid (logN laneFolds : ℕ) (eb : List E → E) (index : ℕ)
    (level next : Whir.Level) (rest : List Whir.Level) (s : WhirState) :
    whirLevels logN laneFolds eb index (level :: next :: rest) s =
      foldRounds level.fold s >>= fun r ↦ midTail logN laneFolds eb index level next rest r.1 r.2 :=
  rfl

/-! ## The doom and the hypotheses -/

/-- **The doom at the start of level `i`**: the invariant with no round, and commitment `i` is the
last, of the level's shape. -/
def LevelPre (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P : LevelCode) (pre : ℕ) (s : WhirState)
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  RoundInv μ ℓ₀ w i P pre s [] cs ∧ ShapeOK i P cs ∧ cs.length = i + 1

/-- The out-of-domain group's escape: `L'² (κ |E|^(κ−1))² / |E|^(2κ)`. -/
noncomputable def eOod (P P' : LevelCode) : ENNReal :=
  (Fintype.card E : ENNReal)⁻¹ ^ P.κ * (Fintype.card E : ENNReal)⁻¹ ^ P.κ *
    ((P'.listMax ^ 2 * (P.κ * Fintype.card E ^ (P.κ - 1)) ^ 2 : ℕ) : ENNReal)

/-- The query group's escape: `((A − 1)/n)^t`. -/
noncomputable def eQuery (P : LevelCode) (t : ℕ) : ENNReal :=
  (((P.A - 1 : ℕ) : ENNReal) / ((2 ^ (P.κ + P.R) : ℕ) : ENNReal)) ^ t

/-- The batching group's escape: `(t + 2) L' / |E|`. -/
noncomputable def eLam (P' : LevelCode) (t : ℕ) : ENNReal :=
  (((t + 2) * P'.listMax : ℕ) : ENNReal) / Fintype.card E

/-- **A level with a next one**: the codes' relations and the groups' escapes within `εmax`
after their grinds. -/
structure MidOK (P P' : LevelCode) (t : ℕ) (εmax : ENNReal) : Prop where
  hκ : P.κ = P'.ℓ + P'.κ
  hℓ : 1 ≤ P.ℓ
  hℓκ : P.ℓ ≤ 2 ^ P.κ
  hA : 1 ≤ P.A
  gap : P'.n * P'.deg 0 < P'.thr 0 * P'.thr 0
  eO : eOod P P' ≤ εmax
  eO1 : eOod P P' < 1
  eQ : (2 : ENNReal)⁻¹ ^ Whir.queryGrindingBits * eQuery P t ≤ εmax
  eQ1 : eQuery P t < 1
  eL : (2 : ENNReal)⁻¹ ^ Whir.batchGrindingBits * eLam P' t ≤ εmax

end
end LeanVM.Protocol.Whir.Sound
