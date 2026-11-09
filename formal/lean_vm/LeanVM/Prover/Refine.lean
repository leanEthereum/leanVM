/-
  LeanVM.Prover.Refine

  The statement's script runner is the specification's compiled honest prover: running a script
  against the verifier's program (`runFrom`, `runScript`) is the commit-once honest prover
  (`proveFromM`, `proveM`) of the strategy that replays the script, in every monad, for every
  hash and permutation.
-/

module

public import Statement.Prover.Run
public import Statement.LeanVmGuest
public import LeanVM.Protocol.Whir.Complete.Script
public import LeanVM.Protocol.Compile.Rom.Complete
public import LeanVM.Protocol.Verifier.Cost
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.WithHash

/-!
# The runner is the specification's prover

`runFrom H F fuel P S sp cs` (`Statement/Prover/Run.lean`) carries the script's current node
`S : Option (Script β)`; the specification's honest prover `proveFromM H F (Strategy.ofScript Hs 0)
fuel P sp h cs` (`LeanVM/Protocol/Compile/Rom/Prover.lean`) carries the history `h` and replays
`Hs` along it (`Script.walk`). Both build each commitment's tree once (`buildTreeM`), read the
openings off it, and search nonces with `findNonceM`: they make the same calls in the same order.
Along a history whose walk ends at the runner's node (`Hs.walk h = S`), they are equal
(`runFrom_eq_proveFromM`): the runner's moves on a matching node are the replay's (`msgAt`,
`wordAt`), and off one (`0`, the empty rows) too.

* `runScript_eq_proveM`: from a seed, the runner's proof is the honest prover's, `none` where it
  fails.
* `simulateQ_runScript`, `simulateQ_seedRunScript`: answering the queries by any implementation
  is running with it; at Keccak-256 and Keccak-f[1600] (`Guest.Budget.deployedKeccakCalls`) the runner in
  `Id` (`atKeccak_seedRunScript`).
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Whir.Complete LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier
open OracleComp OracleSpec

@[expose] public section

/-! ## The runner's node is the replay's -/

namespace Script

variable {β : Type}

theorem msgAt_eq (Hs : Script β) (l : List Ev) : Hs.msgAt l = msgOf (Hs.walk l) := by
  unfold msgAt
  generalize Hs.walk l = o
  rcases o with _ | (_ | _ | _ | _ | _ | _) <;> rfl

theorem wordAt_eq (Hs : Script β) (l : List Ev) : Hs.wordAt l = wordOf (Hs.walk l) := by
  unfold wordAt
  generalize Hs.walk l = o
  rcases o with _ | (_ | _ | _ | _ | _ | _) <;> rfl

theorem afterSend_eq (S : Option (Script β)) (x : E) :
    afterSend S = S.bind fun H ↦ H.step (Ev.read x) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> rfl

theorem afterSample_eq (S : Option (Script β)) (c : E) :
    afterSample c S = S.bind fun H ↦ H.step (Ev.sample c) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> rfl

theorem afterGrind_eq (S : Option (Script β)) (b : ℕ) :
    afterGrind S = S.bind fun H ↦ H.step (Ev.grind b) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> rfl

theorem afterCommit_eq (S : Option (Script β)) (ht w : ℕ) (W : Word) :
    afterCommit S = S.bind fun H ↦ H.step (Ev.commit ht w W) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> rfl

theorem afterQuery_eq (S : Option (Script β)) (rows : List (List K)) :
    afterQuery rows S = S.bind fun H ↦ H.step (Ev.query rows) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> rfl

end Script

/-- The replay's scalar at a history is the runner's at the walk's node. -/
theorem ofScript_msg {β : Type} (Hs : Script β) (h : List Ev) :
    (Strategy.ofScript Hs 0).msg h = Script.msgOf (Hs.walk h) := by
  show Hs.msgAt (h.drop 0) = _
  rw [List.drop_zero, Script.msgAt_eq]

/-- The replay's word at a history is the runner's at the walk's node. -/
theorem ofScript_word {β : Type} (Hs : Script β) (h : List Ev) :
    (Strategy.ofScript Hs 0).word h = Script.wordOf (Hs.walk h) := by
  show Hs.wordAt (h.drop 0) = _
  rw [List.drop_zero, Script.wordAt_eq]

/-! ## The bridge -/

section Bridge

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState)

/-- **The runner is the specification's honest prover**: along a history whose walk through the
script ends at the runner's node, the run from there is the commit-once honest prover of the
script's replay, in every monad, for every hash and permutation. -/
theorem runFrom_eq_proveFromM (fuel : ℕ) {α β : Type} (Hs : Script β) :
    ∀ (P : VerifierProgram α) (S : Option (Script β)) (sp : Sponge) (h : List Ev) (cs : List Tree),
      Hs.walk h = S →
      runFromWithHash H F fuel P S sp cs = proveFromM H F (Strategy.ofScript Hs 0) fuel P sp h cs := by
  intro P
  induction P with
  | ret a => intros; rfl
  | fail => intros; rfl
  | read k ih =>
    intro S sp h cs hw
    have hm := ofScript_msg Hs h
    rw [hw] at hm
    simp only [runFromWithHash, proveFromM]
    rw [hm]
    congr 1; funext sp'; congr 1
    exact ih _ _ _ _ _ (by rw [Script.walk_append, hw, Script.afterSend_eq])
  | sample k ih =>
    intro S sp h cs hw
    simp only [runFromWithHash, proveFromM]
    congr 1; funext r
    exact ih _ _ _ _ _ (by rw [Script.walk_append, hw, Script.afterSample_eq])
  | grind bits k ih =>
    intro S sp h cs hw
    simp only [runFromWithHash, proveFromM]
    congr 1; funext o
    rcases o with _ | n
    · rfl
    · simp only
      congr 1; funext r; congr 1
      exact ih _ _ _ _ (by rw [Script.walk_append, hw, Script.afterGrind_eq _ bits])
  | commit ht w k ih =>
    intro S sp h cs hw
    have hm := ofScript_word Hs h
    rw [hw] at hm
    simp only [runFromWithHash, proveFromM]
    rw [hm]
    congr 1; funext tree; congr 1; funext sp0; congr 1; funext sp1; congr 1
    exact ih _ _ _ _ (by rw [Script.walk_append, hw, Script.afterCommit_eq _ ht w])
  | query i ps k ih =>
    intro S sp h cs hw
    simp only [runFromWithHash, proveFromM]
    split
    · rename_i _ hc
      rw [hc]
    · rename_i _ tree hc
      rw [hc]
      simp only
      congr 1
      exact ih _ _ _ _ _ (by rw [Script.walk_append, hw, Script.afterQuery_eq])

/-- **From a seed**: the runner's proof is the honest prover's of the script's replay, `none`
where a proof of work fails. -/
theorem runScript_eq_proveM (P : VerifierProgram Bool) {β : Type} (Hs : Script β) (seed :
    KeccakState)
    (fuel : ℕ) :
    runScriptWithHash H F P Hs seed fuel = proveM H F P (Strategy.ofScript Hs 0) seed fuel := by
  unfold runScriptWithHash proveM
  rw [runFrom_eq_proveFromM H F fuel Hs P (some Hs) ⟨seed, []⟩ [] [] rfl]

end Bridge

/-! ## Simulation -/

section Commute

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)

/-- **The runner commutes with simulation.** -/
theorem simulateQ_runScript (P : VerifierProgram Bool) {β : Type} (Hs : Script β) (seed :
    KeccakState)
    (fuel : ℕ) :
    simulateQ impl (runScriptWithHash callKeccak256 callKeccakF1600 P Hs seed fuel) =
      runScriptWithHash (implH impl) (implF impl) P Hs seed fuel := by
  rw [runScript_eq_proveM, runScript_eq_proveM, simulateQ_proveM]

/-- The seed commutes with simulation. -/
theorem simulateQ_seedWith (bytecode : List K) (publicInput : Digest) :
    simulateQ impl (seedWithHash callKeccak256 callKeccakF1600 bytecode publicInput) =
      seedWithHash (implH impl) (implF impl) bytecode publicInput := by
  rw [← seedRun_leanVmSeed, ← seedRun_leanVmSeed, simulateQ_seedRun]

/-- **The seed, then the runner, commute with simulation.** -/
theorem simulateQ_seedRunScript (bytecode : List K) (publicInput : Digest) (P :
    VerifierProgram Bool)
    {β : Type} (Hs : Script β) (fuel : ℕ) :
    simulateQ impl (do
        let seed ← seedWithHash callKeccak256 callKeccakF1600 bytecode publicInput
        runScriptWithHash callKeccak256 callKeccakF1600 P Hs seed fuel) = (do
      let seed ← seedWithHash (implH impl) (implF impl) bytecode publicInput
      runScriptWithHash (implH impl) (implF impl) P Hs seed fuel) := by
  rw [simulateQ_bind, simulateQ_seedWith]
  congr 1; funext seed
  exact simulateQ_runScript impl P Hs seed fuel

end Commute

end

end LeanVM.Prover
