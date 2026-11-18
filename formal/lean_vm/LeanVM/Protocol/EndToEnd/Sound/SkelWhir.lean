/-
  LeanVM.Protocol.EndToEnd.Sound.SkelWhir

  The skeleton of the WHIR opening cut at the final polynomial, and of the cut verifier's body:
  fixed by the stack's size and the rate.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.SkelFront
public import LeanVM.Protocol.EndToEnd.Sound.CutRun

/-!
# The opening's skeleton

A fold round reads four scalars, grinds and samples two challenges; a level with a next one
commits the next one's word, reads its high part, samples the out-of-domain point and the query
positions and opens them; the final level, cut, reads the final polynomial. With the folds made
before a level (`s.alphas.length`), the ladder fixes all of it (`skel_whirLevelsGF`), so the cut
opening's skeleton is fixed by the stack's size and the rate (`skel_verifyStackedOpeningCut`),
and the cut verifier's body's by the layout and the rate (`skel_veBodyCut`).
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound

@[expose] public section

/-- The skeleton of a fold round. -/
def skFoldRound : List Op :=
  List.replicate 4 .read ++ skGrind Whir.foldGrindingBits ++ [.sample, .sample]

/-- The skeleton of `n` fold rounds. -/
def skFoldRounds : ℕ → List Op
  | 0 => []
  | n + 1 => skFoldRound ++ skFoldRounds n

theorem skel_foldRound (s : WhirState) :
    SkelP (foldRound s) skFoldRound fun r ↦ r.1.alphas.length = s.alphas.length + 1 := by
  unfold foldRound
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact (skel_readScalar.bind fun _ _ ↦ skel_readScalar.bind fun _ _ ↦ skel_readScalar.bind
    fun _ _ ↦ skel_readScalar.bind fun _ _ ↦ (skel_grindProofOfWork _).bind fun _ _ ↦
    skel_sampleChallenge.bind fun _ _ ↦ skel_sampleChallenge.bind fun _ _ ↦
    SkelP.ret (Q := fun r : WhirState × FoldRound ↦ r.1.alphas.length = s.alphas.length + 1)
      (by simp)).mono (by simp [skFoldRound]) fun _ h ↦ h

theorem skel_foldRounds : ∀ (n : ℕ) (s : WhirState),
    SkelP (foldRounds n s) (skFoldRounds n) fun r ↦ r.1.alphas.length = s.alphas.length + n
  | 0, s => SkelP.ret rfl
  | n + 1, s => by
    unfold foldRounds
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    exact ((skel_foldRound s).bind fun r hr ↦ (skel_foldRounds n r.1).bind fun r' hr' ↦
      SkelP.ret (Q := fun r : WhirState × List FoldRound ↦
        r.1.alphas.length = s.alphas.length + (n + 1))
        (by show r'.1.alphas.length = s.alphas.length + (n + 1); omega)).mono
      (by simp [skFoldRounds]) fun _ h ↦ h

/-- The skeleton of a level with a next one, after its folds, `A` the folds made. -/
def skMidTail (logN A : ℕ) (level next : Whir.Level) : List Op :=
  [.commit (logN - A - next.fold + next.logInvRate) (2 * 2 ^ next.fold)] ++
    List.replicate level.fold .read ++ skGrind Whir.oodGrindingBits ++
    List.replicate (logN - A) .sample ++ [.read] ++ skGrind Whir.queryGrindingBits ++
    List.replicate (sqSamples (logN - A + level.logInvRate) level.queries level.queries) .sample ++
    [.sample, .query]

theorem skel_midTailPre (logN index : ℕ) (level next : Whir.Level) (s : WhirState)
    (rounds : List FoldRound) :
    SkelP (midTailPre logN index level next s rounds) (skMidTail logN s.alphas.length level next)
      fun p ↦ p.2.alphas = s.alphas := by
  unfold midTailPre midTailC
  simp only [VerifierProgram.bind_eq]
  exact ((skel_readCommitment _ _).bind fun _ _ ↦ (skel_readScalars _).bind fun _ _ ↦
    (skel_grindProofOfWork _).bind fun _ _ ↦ (skel_sampleChallenges _).bind fun _ _ ↦
    skel_readScalar.bind fun _ _ ↦ (skel_grindProofOfWork _).bind fun _ _ ↦
    (skel_sampleQueries _ _).bind fun _ _ ↦ skel_sampleChallenge.bind fun _ _ ↦
    (skel_queryOpenings _ _).bind fun _ _ ↦
    SkelP.ret (Q := fun p : List E × WhirState ↦ p.2.alphas = s.alphas) rfl).mono
    (by simp [skMidTail, List.append_assoc]) fun _ h ↦ h

/-- The skeleton of the levels, cut, `A` the folds made before them. -/
def skLevels (logN : ℕ) : ℕ → List Whir.Level → List Op
  | _, [] => []
  | A, [level] => skFoldRounds level.fold ++
      List.replicate (2 ^ (logN - (A + level.fold)) + level.fold) .read
  | A, level :: next :: rest => skFoldRounds level.fold ++
      skMidTail logN (A + level.fold) level next ++ skLevels logN (A + level.fold) (next :: rest)

theorem skel_whirLevelsGF (logN : ℕ) : ∀ (index : ℕ) (levels : List Whir.Level) (s : WhirState),
    SkelP (whirLevelsGF logN (finCut logN) index levels s) (skLevels logN s.alphas.length levels)
      fun _ ↦ True
  | _, [], _ => SkelP.fail _ _
  | index, [level], s => by
    simp only [whirLevelsGF, VerifierProgram.bind_eq]
    exact ((skel_foldRounds level.fold s).bind fun r hr ↦
      ((by
        unfold finCut
        simp only [VerifierProgram.bind_eq]
        exact (skel_readScalars _).bind fun _ _ ↦
          SkelP.ret (Q := fun _ : WhirTrace ↦ True) trivial :
        SkelP (finCut logN index level r.1 r.2)
          (List.replicate (2 ^ (logN - r.1.alphas.length) + level.fold) .read ++ []) _).mono
        (sk' := List.replicate (2 ^ (logN - (s.alphas.length + level.fold)) + level.fold) .read)
        (by rw [hr, List.append_nil]) fun _ h ↦ h)).mono (by simp [skLevels]) fun _ h ↦ h
  | index, level :: next :: rest, s => by
    simp only [whirLevelsGF, VerifierProgram.bind_eq]
    rw [show (fun r : WhirState × List FoldRound ↦ midTailC logN index level next (fun high s' ↦
        (whirLevelsGF logN (finCut logN) (index + 1) (next :: rest) s').bind fun tr ↦
          VerifierProgram.ret (WhirTrace.mid r.2 high tr)) r.1 r.2) =
        fun r ↦ (midTailPre logN index level next r.1 r.2).bind fun p ↦
          (whirLevelsGF logN (finCut logN) (index + 1) (next :: rest) p.2).bind fun tr ↦
            VerifierProgram.ret (WhirTrace.mid r.2 p.1 tr) from
      funext fun r ↦ midTailC_eq_pre _ _ _ _ _ _ _]
    exact ((skel_foldRounds level.fold s).bind fun r hr ↦
      ((skel_midTailPre logN index level next r.1 r.2).mono
        (sk' := skMidTail logN (s.alphas.length + level.fold) level next) (by rw [hr])
        fun _ h ↦ h).bind fun p hp ↦
      ((skel_whirLevelsGF logN (index + 1) (next :: rest) p.2).mono
        (sk' := skLevels logN (s.alphas.length + level.fold) (next :: rest))
        (by rw [hp, hr]) fun _ h ↦ h).bind fun _ _ ↦
      SkelP.ret (Q := fun _ : WhirTrace ↦ True) trivial).mono
      (by simp [skLevels, List.append_assoc]) fun _ h ↦ h

/-- The skeleton of the cut opening at the stack's size and the rate. -/
def skWhir (logN logInvRate : ℕ) : List Op :=
  match Whir.ladder logN logInvRate with
  | some config => skLevels logN 0 config
  | none => []

theorem skel_verifyStackedOpeningCut (stackLog logInvRate : ℕ) (claims : List StackClaim) :
    SkelP (verifyStackedOpeningCut stackLog logInvRate claims)
      ([.sample] ++ skWhir stackLog logInvRate) fun _ ↦ True := by
  unfold verifyStackedOpeningCut verifyWhirCut
  simp only [VerifierProgram.bind_eq]
  exact ((skel_require _).bind fun _ _ ↦ skel_sampleChallenge.bind fun _ _ ↦
    (skel_liftOption _).bind fun config hc ↦
      (skel_whirLevelsGF stackLog 0 config ⟨_, [], []⟩).mono (sk' := skWhir stackLog logInvRate)
        (by rw [skWhir, hc]; rfl) fun _ h ↦ h).mono (by simp) fun _ h ↦ h

/-- The skeleton of the stack's commitment. -/
def skCommitStack (logN logInvRate : ℕ) : List Op :=
  match Whir.ladder logN logInvRate with
  | some (level :: _) => [.commit (levelShape logN level (2 ^ level.fold)).1
      (levelShape logN level (2 ^ level.fold)).2]
  | _ => []

theorem skel_commitStack (logN logInvRate : ℕ) :
    SkelP (commitStack logN logInvRate) (skCommitStack logN logInvRate) fun _ ↦ True := by
  unfold commitStack
  simp only [VerifierProgram.bind_eq]
  exact ((skel_liftOption _).bind fun config hc ↦ (by
    rcases config with _ | ⟨level, rest⟩
    · exact SkelP.fail (skCommitStack logN logInvRate) _
    · exact (skel_readCommitment _ _).mono (sk' := skCommitStack logN logInvRate)
        (by rw [skCommitStack, hc]) fun _ h ↦ h)).mono (by simp) fun _ h ↦ h

/-- The skeleton of the cut verifier's body at a layout and a rate. -/
def skBody (layout : Verifier.Layout) (ρ : ℕ) : List Op :=
  skCommitStack layout.stackLog ρ ++ skOod layout.stackLog ++ skFront layout ++ skRing ++
    ([.sample] ++ skWhir layout.stackLog ρ)

/-- **The cut verifier's body's skeleton**, fixed by the layout and the rate. -/
theorem skel_veBodyCut (pd : Digest) (layout : Verifier.Layout) (ρ : ℕ) :
    SkelP (veBodyCut computedBytecodeValue pd layout ρ) (skBody layout ρ) fun _ ↦ True := by
  unfold veBodyCut
  simp only [VerifierProgram.bind_eq]
  exact ((skel_commitStack _ _).bind fun _ _ ↦ (skel_readOod _).bind fun _ _ ↦
    (skel_frontProg layout pd).bind fun r _ ↦ (skel_ringSwitch _ _).bind fun y _ ↦
    skel_verifyStackedOpeningCut _ _ _).mono (by simp [skBody, List.append_assoc]) fun _ h ↦ h

/-- The skeleton of the announced sizes. -/
def skSizes : List Op := List.replicate (2 + tables.length) .read

theorem skel_readAnnouncedSizes (bytecode : List K) :
    SkelP (readAnnouncedSizes bytecode) skSizes fun _ ↦ True := by
  unfold readAnnouncedSizes
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact ((skel_readScalars _).bind fun _ _ ↦ (skel_require _).bind fun _ _ ↦
    (skel_require _).bind fun _ _ ↦ (skel_liftOption _).bind fun _ _ ↦
    (skel_require _).bind fun _ _ ↦
    SkelP.ret (Q := fun _ : Verifier.Layout × ℕ ↦ True) trivial).mono (by simp [skSizes])
    fun _ h ↦ h

end
end LeanVM.Protocol.EndToEnd.Sound
