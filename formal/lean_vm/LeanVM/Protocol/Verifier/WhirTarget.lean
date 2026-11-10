/-
  LeanVM.Protocol.Verifier.WhirTarget

  The WHIR level loop with the running claim threaded through every level, the form the proofs
  reason on, and its equality with the statement's `verifyWhir`.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Parameters.Whir

/-!
# The WHIR level loop with a threaded running claim

`Statement/LeanVmVerifier.lean` transcribes `verify_whir` (`crates/verifier/src/whir.rs:141-265`)
with `running_target` set only in the final level's tail rounds, which fail when there are none (the
Rust starts it at zero). The proofs reason on a form that threads the running claim through every
fold round and adds the glued claims' values to it (`WhirStateT.target`); the tail rounds overwrite
it, so it never reaches the verdict.

`verifyWhir_eq_target` proves the two are one program: every ladder leaves the final level at
least one variable (`ladder_sum_lt`), so the tail rounds never start from none.
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters
open LeanVM.Semantics LeanVM.Protocol.Compile Claims

@[expose] public section

/-! ## The threaded form -/

/-- `WhirState` with the running claim. -/
structure WhirStateT where
  target : E
  quad : List E
  folds : List E
  glued : List GluedClaim

/-- The state without the running claim. -/
def WhirStateT.forget (s : WhirStateT) : WhirState := ⟨s.quad, s.folds, s.glued⟩

/-- `foldRounds`, folding the running claim. -/
def foldRoundsT (grinding : ℕ) : ℕ → WhirStateT → List E → VerifierProgram (WhirStateT × List E)
  | 0, s, levelFolds => return (s, levelFolds)
  | n + 1, s, levelFolds => do
    VerifierProgram.foldProofOfWork grinding
    let challenge ← VerifierProgram.sampleChallenge
    let target := polyEval s.quad challenge
    let quad ← sumcheckRoundPoly 3 target none
    foldRoundsT grinding n { s with target, quad, folds := s.folds ++ [challenge] }
      (levelFolds ++ [challenge])

/-- `tailRounds` from a running claim, which it returns when there is no round. -/
def tailRoundsT : ℕ → E → List E → VerifierProgram (List E × E)
  | 0, target, _ => return ([], target)
  | n + 1, _, quad => do
    let challenge ← VerifierProgram.sampleChallenge
    let target := polyEval quad challenge
    if n = 0 then return ([challenge], target)
    else do
      let quad ← sumcheckRoundPoly 3 target none
      let (rest, target) ← tailRoundsT n target quad
      return (challenge :: rest, target)

/-- `glue`, adding the pending claims' values to the running claim. -/
def glueT (lam : E) (s : WhirStateT) (pending : List (E × List E × (List E → E))) : WhirStateT :=
  (pending.foldl (fun (acc : WhirStateT × E) (value, intro, weightAt) ↦
    let scalar := acc.2 * lam
    let s := acc.1
    ({ s with quad := List.zipWith (fun q i ↦ q + scalar * i) s.quad intro,
              target := s.target + scalar * value,
              glued := s.glued ++ [⟨scalar, s.folds.length, weightAt⟩] }, scalar)) (s, 1)).1

/-- `whirLevels` with the running claim. -/
def whirLevelsT (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ℕ → List Whir.Level → WhirStateT → VerifierProgram Unit
  | _, [], _ => VerifierProgram.fail
  | index, level :: rest, s => do
    let (s, levelFolds) ← foldRoundsT level.foldGrinding level.fold s []
    let messageLog := logN - s.folds.length
    let (residual, pending) ← match rest with
      | [] => do
        let residual ← VerifierProgram.readScalars (2 ^ messageLog)
        pure (residual, ([] : List (E × List E × (List E → E))))
      | next :: _ => do
        let (height, width) := levelShape messageLog next (3 * 2 ^ next.fold)
        VerifierProgram.readCommitment height width
        let oodPoint ← VerifierProgram.sampleChallenges messageLog
        let oodValue ← VerifierProgram.readScalar
        let intro ← sumcheckRoundPoly 3 oodValue none
        pure ([], [(oodValue, intro, fun x ↦ eqEval oodPoint x)])
    VerifierProgram.grindProofOfWork Whir.queryGrindingBits
    let queries ← sampleQueries (messageLog + level.logInvRate) level.queries
    let lam ← VerifierProgram.sampleChallenge
    let queryWeights := powers lam queries.length
    let words ← VerifierProgram.queryOpenings index queries
    let rows : List (List E) :=
      if index = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow
    let enforced := enforcedSum rows levelFolds queryWeights
    let intro ← sumcheckRoundPoly 3 enforced none
    let pending := pending ++
      [(enforced, intro, fun x ↦ inducedWeight messageLog queries queryWeights x)]
    let s := glueT lam s pending
    match rest with
    | [] => do
      let (tailFolds, target) ← tailRoundsT messageLog s.target s.quad
      let point := s.folds ++ tailFolds
      let weight := s.glued.foldl
        (fun weight claim ↦
          weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ tailFolds))
        (evaluateBasis (point.drop laneFolds ++ point.take laneFolds))
      let terminal := weight * multilinearEval residual tailFolds
      VerifierProgram.require (terminal = target)
    | _ :: _ => whirLevelsT logN laneFolds evaluateBasis (index + 1) rest s

/-- `verifyWhir` with the running claim. -/
def verifyWhirT (logN logInvRate : ℕ) (target : E) (evaluateBasis : List E → E) : VerifierProgram
    Unit := do
  let config ← liftOption (Whir.ladder logN logInvRate)
  let quad ← sumcheckRoundPoly 3 target none
  whirLevelsT logN ((config.head?.map (·.fold)).getD 0) evaluateBasis 0 config
    ⟨target, quad, [], []⟩

/-! ## The equality -/

namespace WhirTarget

theorem foldRounds_forget (grinding : ℕ) : ∀ (n : ℕ) (s : WhirStateT) (levelFolds : List E),
    foldRounds grinding n s.forget levelFolds =
      (foldRoundsT grinding n s levelFolds).bind fun r ↦ VerifierProgram.ret (r.1.forget, r.2)
  | 0, _, _ => rfl
  | n + 1, s, levelFolds => by
    unfold foldRounds foldRoundsT
    simp only [VerifierProgram.bind_eq, VerifierProgram.bind_assoc]
    congr 1
    funext _
    congr 1
    funext challenge
    congr 1
    funext quad
    exact foldRounds_forget grinding n
      ⟨polyEval s.quad challenge, quad, s.folds ++ [challenge], s.glued⟩ _

theorem allRet_foldRoundsT (grinding : ℕ) : ∀ (n : ℕ) (s : WhirStateT) (levelFolds : List E),
    AllRet (foldRoundsT grinding n s levelFolds) fun r ↦ r.1.folds.length = s.folds.length + n
  | 0, _, _ => .ret rfl
  | n + 1, s, levelFolds => by
    unfold foldRoundsT
    simp only [VerifierProgram.bind_eq]
    refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
    refine AllRet.bind (fun challenge _ ↦ ?_) _ (allRet_true _)
    refine AllRet.bind (fun quad _ ↦ ?_) _ (allRet_true _)
    refine AllRet.mono (fun r hr ↦ ?_) (allRet_foldRoundsT grinding n _ _)
    rw [hr]
    simp only [List.length_append, List.length_singleton]
    omega

theorem tailRounds_eq : ∀ (n : ℕ), 1 ≤ n → ∀ (target : E) (quad : List E),
    tailRounds n quad = tailRoundsT n target quad
  | 0, h, _, _ => absurd h (by decide)
  | n + 1, _, target, quad => by
    unfold tailRounds tailRoundsT
    simp only [VerifierProgram.bind_eq]
    congr 1
    funext challenge
    split
    · rfl
    · rename_i hn
      congr 1
      funext quad'
      rw [tailRounds_eq n (Nat.one_le_iff_ne_zero.mpr hn)]

theorem bind_tailRounds {β : Type} (n : ℕ) (h : 1 ≤ n) (target : E) (quad quad' : List E)
    (hq : quad = quad') (f g : List E × E → VerifierProgram β) (hfg : f = g) :
    (tailRounds n quad).bind f = (tailRoundsT n target quad').bind g := by
  rw [tailRounds_eq n h target, hq, hfg]

theorem whirLevels_eq (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirStateT),
      s.folds.length + (levels.map (·.fold)).sum < logN →
      whirLevels logN laneFolds evaluateBasis index levels s.forget =
        whirLevelsT logN laneFolds evaluateBasis index levels s
  | [], _, _, _ => rfl
  | level :: rest, index, s, hlt => by
    unfold whirLevels whirLevelsT
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    rw [foldRounds_forget, VerifierProgram.bind_assoc]
    refine bind_congr (fun r hr ↦ ?_) _ (allRet_foldRoundsT level.foldGrinding level.fold s [])
    obtain ⟨s', levelFolds⟩ := r
    simp only [VerifierProgram.ret_bind] at hr ⊢
    simp only [List.map_cons, List.sum_cons] at hlt
    have hfolds : s'.forget.folds = s'.folds := rfl
    cases rest with
    | nil =>
      dsimp only
      refine bind_congr (Q := fun _ ↦ True) (fun residual _ ↦ ?_) _ (allRet_true _)
      refine bind_congr (Q := fun _ ↦ True) (fun _ _ ↦ ?_) _ (allRet_true _)
      refine bind_congr (Q := fun _ ↦ True) (fun queries _ ↦ ?_) _ (allRet_true _)
      refine bind_congr (Q := fun _ ↦ True) (fun lam _ ↦ ?_) _ (allRet_true _)
      refine bind_congr (Q := fun _ ↦ True) (fun words _ ↦ ?_) _ (allRet_true _)
      refine bind_congr (Q := fun _ ↦ True) (fun intro _ ↦ ?_) _ (allRet_true _)
      exact bind_tailRounds _ (by rw [hfolds, hr]; simp at hlt; omega) _ _ _ rfl _ _ rfl
    | cons next rest' =>
      dsimp only
      refine bind_congr (Q := fun _ ↦ True) (fun _ _ ↦ ?_) _ (allRet_true _)
      refine bind_congr (Q := fun _ ↦ True) (fun _ _ ↦ ?_) _ (allRet_true _)
      refine bind_congr (Q := fun _ ↦ True) (fun _ _ ↦ ?_) _ (allRet_true _)
      refine bind_congr (Q := fun _ ↦ True) (fun _ _ ↦ ?_) _ (allRet_true _)
      refine bind_congr (Q := fun _ ↦ True) (fun _ _ ↦ ?_) _ (allRet_true _)
      refine bind_congr (Q := fun _ ↦ True) (fun _ _ ↦ ?_) _ (allRet_true _)
      refine bind_congr (Q := fun _ ↦ True) (fun lam _ ↦ ?_) _ (allRet_true _)
      refine bind_congr (Q := fun _ ↦ True) (fun _ _ ↦ ?_) _ (allRet_true _)
      refine bind_congr (Q := fun _ ↦ True) (fun _ _ ↦ ?_) _ (allRet_true _)
      symm
      refine (whirLevels_eq logN laneFolds evaluateBasis (next :: rest') (index + 1)
        (glueT lam s' _) ?_).symm
      show s'.folds.length + _ < logN
      rw [hr]
      simpa [Nat.add_assoc] using hlt

/-- Every ladder leaves its final level at least one variable. -/
theorem ladder_sum_lt {μ r : ℕ} {levels : List Whir.Level} (h : Whir.ladder μ r = some levels) :
    (levels.map (·.fold)).sum < μ := by
  have hadm : Whir.Admissible μ r := by
    unfold Whir.ladder at h
    split at h
    · assumption
    · cases h
  have key : ∀ μ < Whir.maxLogStack + 1, ∀ r < 5, Whir.Admissible μ r →
      ∀ levels, Whir.ladder μ r = some levels → (levels.map (·.fold)).sum < μ := by
    decide +kernel
  have hb : μ < Whir.maxLogStack + 1 ∧ r < 5 := by
    unfold Whir.Admissible at hadm
    omega
  exact key μ hb.1 r hb.2 hadm levels h

end WhirTarget

open WhirTarget in
/-- **The two forms are one program.** -/
theorem verifyWhir_eq_target (logN logInvRate : ℕ) (target : E) (evaluateBasis : List E → E) :
    verifyWhir logN logInvRate target evaluateBasis =
      verifyWhirT logN logInvRate target evaluateBasis := by
  unfold verifyWhir verifyWhirT
  simp only [VerifierProgram.bind_eq]
  refine bind_congr (fun config hc ↦ ?_) _ (allRet_liftOption _)
  congr 1
  funext quad
  exact whirLevels_eq logN _ evaluateBasis config 0 ⟨target, quad, [], []⟩
    (by simpa using ladder_sum_lt hc)

/-- `verifyStackedOpening` on the threaded form. -/
theorem verifyStackedOpening_eq_target (stackLog logInvRate : ℕ) (claims : List StackClaim) :
    verifyStackedOpening stackLog logInvRate claims = (do
      let scales := powers (← VerifierProgram.sampleChallenge) claims.length
      verifyWhirT stackLog logInvRate (dot scales (claims.map (·.2)))
        fun point ↦ dot scales (claims.map fun c ↦ c.1 point)) := by
  unfold verifyStackedOpening
  simp only [verifyWhir_eq_target]

end

end LeanVM.Protocol.Verifier
