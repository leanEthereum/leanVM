module

public import Quantum.StdModel.Sphincs.Extract
public import Quantum.StdModel.Sphincs.Table
public import Quantum.StdModel.Sphincs.Laws
public import Quantum.StdModel.Decide

@[expose] public section

/-!
# leanSPHINCS at a fixed table: the games of the reduction

At a fixed table `tab` of a world `W`, with `h := W.hashOf tab`, the SUF-CMA game of
`sphincsOver W.hash` is a canonical run (`Quantum.StdModel.kRunQ`) of the adversary against a
deterministic signer: the signature of `M` is the honest table's `v.signature (cellHash h) M`
(`detKernel`), so the game is a function of the table, `gameAt W tab A v d`, read through a
final decision `d` of the forgery and the transcript.

* `winProbAt_eq`: the SUF-CMA winning probability at `tab` is the seed average of `gameAt` at the
  real table (`realTable`) with the winning decision `winDec`.
* `gameAt_win_le`: at any honest table (`Honest h v`), the winning decision is at most the sum of
  the four event decisions of the forgery's verification trace: ITSR (`itsrDec`), EncTCR+C
  (`encDec`), SM-TCR (`tcrDec`) and CPRE (`cpreDec`) (`win_imp_eventsT'`).
* `ideal W tab A d`: the game at the table with a uniform `PK.seed`, uniform secret digests and a
  uniform randomizer function (`digTable`), the hybrid after the two PRF hops.
-/

open OracleComp OracleSpec
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Quantum.Qrom.Sphincs (QTable sphincsOver)

namespace Quantum.StdModel.Sphincs

/-- The signing oracle of leanSPHINCS. -/
abbrev SignSpec := Message →ₒ Option Signature

/-- A signing transcript. -/
abbrev SignLog := QueryLog SignSpec

/-- A quantum SUF-CMA adversary against leanSPHINCS over the world `W`. -/
abbrev SAdv (W : OracleWorld) := SufAdversary W PublicKey Message (Option Signature) Forgery

/-- The verifier evaluated with the hash `h`. -/
def verifyId (h : HashInput → HashOutput) (pk : PublicKey) (forg : Forgery) : Bool :=
  Quantum.Qrom.Sphincs.LeanSphincsOver.verify (m := Id) (fun l ↦ h l) pk forg.message
    forg.signature

/-- **The deterministic signer of the table `v`**, logging each answer. -/
noncomputable def detKernel (h : HashInput → HashOutput) (v : QTable) : Kernel SignSpec SignLog :=
  fun log M ↦ pure (v.signature (cellHash h) M, log ++ [⟨M, v.signature (cellHash h) M⟩])

/-- A transcript of the table's signer. -/
def LogOk (h : HashInput → HashOutput) (v : QTable) (log : SignLog) : Prop :=
  ∀ e ∈ log, e.2 = v.signature (cellHash h) e.1

/-- A transcript as a list of pairs. -/
def logPairs (log : SignLog) : List (Message × Option Signature) :=
  log.map fun e ↦ (e.1, e.2)

/-- The signed messages of a transcript. -/
def logMsgs (log : SignLog) : List Message :=
  (logPairs log).map Prod.fst

/-- **The winning decision**: the statement's winning condition and verification under `h`. -/
noncomputable def winDec (h : HashInput → HashOutput) (v : QTable) (r : Forgery × SignLog) :
    Bool :=
  RandomPermutationModel.sufCmaScheme.winningCondition r.2 r.1 && verifyId h v.publicKey r.1

/-- The verification trace of a forgery under the table's public key. -/
def forgTrace (h : HashInput → HashOutput) (v : QTable) (forg : Forgery) :
    HashInput → Option HashOutput :=
  Extract.traceH h v.publicKey forg.message forg.signature

/-- The ITSR decision. -/
noncomputable def itsrDec (h : HashInput → HashOutput) (v : QTable) (r : Forgery × SignLog) :
    Bool :=
  Props.holds (EvItsr h v (logMsgs r.2) r.1.signature.randomizer r.1.message)

/-- The EncTCR+C decision. -/
noncomputable def encDec (h : HashInput → HashOutput) (v : QTable) (r : Forgery × SignLog) :
    Bool :=
  Props.holds (EvEncT h v (forgTrace h v r.1))

/-- The SM-TCR decision. -/
noncomputable def tcrDec (h : HashInput → HashOutput) (v : QTable) (r : Forgery × SignLog) :
    Bool :=
  Props.holds (EvTcrT h v (forgTrace h v r.1))

/-- The CPRE decision. -/
noncomputable def cpreDec (h : HashInput → HashOutput) (v : QTable) (r : Forgery × SignLog) :
    Bool :=
  Props.holds (EvCpreT h v (forgTrace h v r.1) (logMsgs r.2))

variable (W : OracleWorld) (tab : W.Tab)

/-- **The game at the table `v`**: the adversary against the table's signer, read through the
decision `d`. -/
noncomputable def gameAt (A : SAdv W) (v : QTable) (d : Forgery × SignLog → Bool) : ℝ≥0∞ :=
  W.probAt tab ((kRunQ W (detKernel (W.hashOf tab) v) (A v.publicKey) []).map d)

/-! ## The SUF-CMA game as the game at the real table -/

/-- **The SUF-CMA game at a fixed table** is the game at the real table of its seed. -/
theorem probAt_game_eq (A : SAdv W) (S0 : MasterSeed) :
    W.probAt tab (game W (sphincsOver W.hash) S0 A) =
      gameAt W tab A (realTable W tab S0) (winDec (W.hashOf tab) (realTable W tab S0)) := by
  set h := W.hashOf tab
  set v := realTable W tab S0
  refine probAt_eq_of_run₂ W tab ((run₂_sufGame (sphincsOver W.hash) tab S0 A).trans ?_)
  rw [simulateQ_generateKeys_eager]
  refine (run₂_bind_of_classicalOn_pure _ (classicalOn_coinImpl_toQuantumAt _ _) _).trans ?_
  have hK : signKernel W (sphincsOver W.hash) S0 tab = detKernel h v := by
    funext log M
    simp only [signKernel, simulateQ_sign_eager, map_pure, detKernel, h, v]
  dsimp only
  rw [hK, QuantumComp₂.map_eq_bind_pure]
  refine run₂_bind_congr rfl fun run ↦ ?_
  rw [simulateQ_verify_eager]
  exact run₂_bind_of_classicalOn_pure _ (classicalOn_coinImpl_toQuantumAt _ _) _

/-- **The SUF-CMA winning probability at a fixed table** is the seed average of the game at the
real table. -/
theorem winProbAt_eq (A : SAdv W) :
    winProbAt W (sphincsOver W.hash) tab A =
      ∑ S0 : MasterSeed, Pr{let s ← sampleMasterSeed}[s = S0] *
        gameAt W tab A (realTable W tab S0) (winDec (W.hashOf tab) (realTable W tab S0)) := by
  unfold winProbAt
  exact Finset.sum_congr rfl fun S0 _ ↦ congrArg _ (probAt_game_eq W tab A S0)

/-! ## The win is in the events -/

theorem logOk_nil (h : HashInput → HashOutput) (v : QTable) : LogOk h v [] := by
  intro e he
  simp at he

theorem detKernel_logOk (h : HashInput → HashOutput) (v : QTable) (log : SignLog)
    (hl : LogOk h v log) (M : Message) : ∀ p ∈ support (detKernel h v log M), LogOk h v p.2 := by
  intro p hp
  simp only [detKernel, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hl e he
  · rw [List.mem_singleton.mp he]

/-- A decision may be restricted to the transcripts of the table's signer. -/
theorem gameAt_eq_logOk (A : SAdv W) (v : QTable) (d : Forgery × SignLog → Bool) :
    gameAt W tab A v d =
      gameAt W tab A v (fun r ↦ d r && Props.holds (LogOk (W.hashOf tab) v r.2)) := by
  refine probAt_eq_of_run₂ W tab ?_
  refine run₂_map_kRunQ_sim (W.runtime tab) (detKernel (W.hashOf tab) v)
    (detKernel (W.hashOf tab) v) (LogOk (W.hashOf tab) v) id (fun s _ q ↦ by simp)
    (fun s hs q ↦ detKernel_logOk _ v s hs q) (A v.publicKey) [] (logOk_nil _ v) _ _ ?_
  intro a s hs
  simp [Props.holds_eq_true.mpr hs]

/-- **The win is in the events**: at an honest table, the winning decision is at most the sum of
the four event decisions. -/
theorem gameAt_win_le (A : SAdv W) (v : QTable) (hv : Honest (W.hashOf tab) v) :
    gameAt W tab A v (winDec (W.hashOf tab) v) ≤
      gameAt W tab A v (itsrDec (W.hashOf tab) v) + gameAt W tab A v (encDec (W.hashOf tab) v) +
        gameAt W tab A v (tcrDec (W.hashOf tab) v) +
          gameAt W tab A v (cpreDec (W.hashOf tab) v) := by
  set h := W.hashOf tab
  rw [gameAt_eq_logOk]
  let ds : Fin 4 → Forgery × SignLog → Bool :=
    ![itsrDec h v, encDec h v, tcrDec h v, cpreDec h v]
  have hle := probAt_map_le_sum W tab (kRunQ W (detKernel h v) (A v.publicKey) [])
    (fun r ↦ winDec h v r && Props.holds (LogOk h v r.2)) Finset.univ ds ?_
  · refine hle.trans (le_of_eq ?_)
    simp only [Fin.sum_univ_four, ds, gameAt]
    rfl
  intro r hr
  simp only [Bool.and_eq_true, winDec, Props.holds_eq_true] at hr
  obtain ⟨⟨hwc, hver⟩, hlog⟩ := hr
  have hwc' := of_decide_eq_true hwc
  have hfresh : ¬∃ e ∈ logPairs r.2, e.1 = r.1.message ∧ e.2 = some r.1.signature := by
    rintro ⟨e, he, h1, h2⟩
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact hwc'.2 ⟨e', he', h1, h2⟩
  have hl : ∀ e ∈ logPairs r.2, e.2 = v.signature (cellHash h) e.1 := by
    intro e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact hlog e' he'
  rcases win_imp_eventsT' hv hl hver hfresh with h1 | h1 | h1 | h1
  · exact ⟨0, Finset.mem_univ _, Props.holds_eq_true.mpr h1⟩
  · exact ⟨1, Finset.mem_univ _, Props.holds_eq_true.mpr h1⟩
  · exact ⟨2, Finset.mem_univ _, Props.holds_eq_true.mpr h1⟩
  · exact ⟨3, Finset.mem_univ _, Props.holds_eq_true.mpr h1⟩

/-! ## The ideal hybrid -/

/-- **The ideal game**: uniform `PK.seed`, uniform secret digests, uniform randomizers. -/
noncomputable def ideal (A : SAdv W) (d : QTable → Forgery × SignLog → Bool) : ℝ≥0∞ :=
  unifAvg PublicParameter fun P ↦ unifAvg (KeygenDomain → Digest) fun s ↦
    unifAvg (Message → Digest) fun r ↦
      gameAt W tab A (digTable (W.hashOf tab) P s r) (d (digTable (W.hashOf tab) P s r))

/-- **The ideal win is in the events.** -/
theorem ideal_win_le (A : SAdv W) :
    ideal W tab A (winDec (W.hashOf tab)) ≤
      ideal W tab A (itsrDec (W.hashOf tab)) + ideal W tab A (encDec (W.hashOf tab)) +
        ideal W tab A (tcrDec (W.hashOf tab)) + ideal W tab A (cpreDec (W.hashOf tab)) := by
  unfold ideal unifAvg
  simp only [← mul_add, ← Finset.sum_add_distrib]
  refine mul_le_mul' le_rfl (Finset.sum_le_sum fun P _ ↦ mul_le_mul' le_rfl
    (Finset.sum_le_sum fun s _ ↦ mul_le_mul' le_rfl (Finset.sum_le_sum fun r _ ↦ ?_)))
  exact gameAt_win_le W tab A _ (honest_digTable _ _ _ _)

end Quantum.StdModel.Sphincs

end
