/-
  LeanVM.Protocol.WithHashBridge

  The statement's verifier and honest prover, over a permutation `F` alone, are the proofs' forms
  with a hash of their own (`LeanVM.Protocol.WithHash`) at the hash Keccak-256 over `F`.
-/

module

public import LeanVM.Protocol.WithHash

/-!
# The verifier and the prover over a permutation are the forms with a hash

The statement's compiled verifier hashes with Keccak-256 over the permutation it is given
(`keccak256With F`); the proofs' forms take the hash `H` beside the permutation. With
`H = keccak256With F` they are the statement's, by induction on the program for the runs
(`run_eq_withHash`, `runFrom_eq_withHash`) and on the path or the list for the openings
(`climb_eq_withHash`, `openAll_eq_withHash`). With Keccak-f[1600] in `Id` the hash is the deployed
Keccak-256 (`keccak256With_keccakF1600`), so the deployed definitions are the forms with Keccak-256
and Keccak-f[1600] (`verifyDeferred_eq_withHash`, …).
-/

@[expose] public section

namespace LeanVM.Protocol

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash

/-- Keccak-256 over Keccak-f[1600] in `Id` is the deployed Keccak-256. -/
theorem keccak256With_keccakF1600 : keccak256With (m := Id) keccakF1600 = keccak256 := rfl

/-- Keccak-256 over the permutation that answers `default` is `default`: the last block's
permutation answers it, and its first four lanes are zero. -/
theorem keccak256With_default (data : List UInt8) :
    keccak256With (m := Id) (fun _ ↦ default) data = pure default := by
  have h : ∀ (n : ℕ) (s : KeccakState) (d : List UInt8),
      absorbWith (m := Id) (fun _ ↦ default) n s d = pure default := by
    intro n
    induction n with
    | zero => intro s d; rfl
    | succ n ih => intro s d; exact ih _ _
  show (do
      let state ← absorbWith (m := Id) (fun _ ↦ default) (data.length / rate)
        (Vector.replicate 25 0)
        data
      pure #v[Keccak.lane state 0, Keccak.lane state 1, Keccak.lane state 2, Keccak.lane state 3]) =
    pure default
  rw [h]
  rfl

namespace Compile

section Run

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

theorem climb_eq_withHash (path : List Digest) : ∀ (node : Digest) (q : ℕ),
    climb F node q path = climbWithHash (keccak256With F) node q path := by
  induction path with
  | nil => intro node q; rfl
  | cons s ss ih => intro node q; simp only [climb, climbWithHash, ih]

theorem openOne_eq_withHash (root : Digest) (height width q : ℕ) (o : Opening) :
    openOne F root height width q o = openOneWithHash (keccak256With F) root height width q o := by
  simp only [openOne, openOneWithHash, climb_eq_withHash]

theorem openAll_eq_withHash (root : Digest) (height width : ℕ) (ps : List ℕ) :
    ∀ os : List Opening,
      openAll F root height width ps os = openAllWithHash
        (keccak256With F) root height width ps os := by
  induction ps with
  | nil => intro os; rfl
  | cons q qs ih =>
    intro os
    cases os with
    | nil => rfl
    | cons o os => simp only [openAll, openAllWithHash, openOne_eq_withHash, ih]

theorem openPhase_eq_withHash (root : Digest) (height width : ℕ) (ps : List ℕ)
    (phase : List Opening) :
    openPhase F root height width ps phase =
      openPhaseWithHash (keccak256With F) root height width ps phase := by
  simp only [openPhase, openPhaseWithHash, openAll_eq_withHash]; rfl

theorem run_eq_withHash {α : Type} (P : VerifierProgram α) : ∀ s : VerifierProgramState,
    run F P s = runWithHash (keccak256With F) F P s := by
  induction P with
  | ret a => intro s; rfl
  | fail => intro s; rfl
  | read k ih => intro s; simp only [run, runWithHash, ih]; rfl
  | sample k ih => intro s; simp only [run, runWithHash, ih]
  | grind bits k ih => intro s; simp only [run, runWithHash, ih]; rfl
  | commit height width k ih => intro s; simp only [run, runWithHash, ih]; rfl
  | query i ps k ih => intro s; simp only [run, runWithHash, ih, openPhase_eq_withHash]; rfl

theorem runProof_eq_withHash (P : VerifierProgram Bool) (seed : KeccakState) (π : Proof) :
    runProof F P seed π = runProofWithHash (keccak256With F) F P seed π := by
  simp only [runProof, runProofWithHash, run_eq_withHash]; rfl

end Run

/-- The run with every permutation answered by `default` is the run with every hash and
permutation answered by `default`. -/
theorem runPure_eq_withHash {α : Type} (P : VerifierProgram α) (s : VerifierProgramState) :
    runPure P s =
      Id.run (runWithHash (m := Id) (fun _ ↦ default) (fun _ ↦ default) P s) := by
  have : keccak256With (m := Id) (fun _ ↦ (default : KeccakState)) = fun _ ↦ default :=
    funext keccak256With_default
  simp only [runPure, run_eq_withHash, this]

end Compile

namespace Verifier

open Compile

section Hash

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

theorem seedWith_eq_withHash (bytecode : List K) (publicInput : Digest) :
    spongeSeedWith F bytecode publicInput = seedWithHash (keccak256With F) F bytecode
        publicInput := rfl

theorem verifyWith_eq_withHash (bytecode : List K) (publicInput : Digest) (π : Proof) :
    verifyWith F bytecode publicInput π =
      verifyWithHash (keccak256With F) F bytecode publicInput π := by
  simp only [verifyWith, verifyWithHash, seedWith_eq_withHash, runProof_eq_withHash]

theorem verifyDeferredWith_eq_withHash (bytecode : List K) (iv publicInput : Digest)
    (c : BytecodeClaim)
    (π : Proof) :
    verifyDeferredWith F bytecode iv publicInput c π =
      verifyDeferredWithHash (keccak256With F) F bytecode iv publicInput c π := by
  simp only [verifyDeferredWith, verifyDeferredWithHash, runProof_eq_withHash]

end Hash

/-- The deployed deferring verifier is the form with Keccak-256 and Keccak-f[1600]. -/
theorem verifyDeferred_eq_withHash (bytecode : List K) (iv publicInput : Digest) (c : BytecodeClaim)
    (π : Proof) :
    verifyDeferred bytecode iv publicInput c π =
      Id.run (verifyDeferredWithHash (m := Id) keccak256 keccakF1600 bytecode iv publicInput c π) :=
        by
  rw [verifyDeferred, verifyDeferredWith_eq_withHash, keccak256With_keccakF1600]

end Verifier

end LeanVM.Protocol

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

theorem verifier_eq_withHash {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)
    (prog : LeanIsaProgram)
    (input : PublicInput) (proof : Proof) :
    leanVmVerifier F prog input proof = verifierWithHash (keccak256With F) F prog input proof := by
  simp only [leanVmVerifier, verifierWithHash, verifyWith_eq_withHash]

namespace Prover

section Monadic

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

theorem leafDigestsM_eq_withHash (height : ℕ) (word : Word) :
    leafDigestsM F height word = leafDigestsWithHash (keccak256With F) height word := rfl

theorem parentsM_eq_withHash (level : Array Digest) (n : ℕ) :
    parentsM F level n = parentsWithHash (keccak256With F) level n := rfl

theorem levelsM_eq_withHash (k : ℕ) : ∀ level : Array Digest,
    levelsM F k level = levelsWithHash (keccak256With F) k level := by
  induction k with
  | zero => intro level; rfl
  | succ k ih => intro level; simp only [levelsM, levelsWithHash, parentsM_eq_withHash, ih]

theorem buildTreeM_eq_withHash (height : ℕ) (word : Word) :
    buildTreeM F height word = buildTreeWithHash (keccak256With F) height word := by
  simp only [buildTreeM, buildTreeWithHash, leafDigestsM_eq_withHash, levelsM_eq_withHash]

theorem runFrom_eq_withHash (fuel : ℕ) {α β : Type} (P : VerifierProgram α) :
    ∀ (S : Option (Script β)) (sp : Sponge) (cs : List Tree),
      runFrom F fuel P S sp cs = runFromWithHash (keccak256With F) F fuel P S sp cs := by
  induction P with
  | ret a => intro S sp cs; rfl
  | fail => intro S sp cs; rfl
  | read k ih => intro S sp cs; simp only [runFrom, runFromWithHash, ih]
  | sample k ih => intro S sp cs; simp only [runFrom, runFromWithHash, ih]
  | grind bits k ih => intro S sp cs; simp only [runFrom, runFromWithHash, ih]; rfl
  | commit ht w k ih =>
    intro S sp cs; simp only [runFrom, runFromWithHash, ih, buildTreeM_eq_withHash]
  | query i ps k ih => intro S sp cs; simp only [runFrom, runFromWithHash, ih]; rfl

end Monadic

theorem runScript_eq_withHash {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)
    (P : VerifierProgram Bool)
    {β : Type} (S : Script β) (seed : KeccakState) (fuel : ℕ) :
    runScript F P S seed fuel = runScriptWithHash (keccak256With F) F P S seed fuel := by
  simp only [runScript, runScriptWithHash, runFrom_eq_withHash]

theorem prove_eq_withHash {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)
    (prog : LeanIsaProgram)
    (input : PublicInput) (t : Execution prog) (ρ fuel : ℕ) :
    prove F prog input t ρ fuel = proveWithHash (keccak256With F) F prog input t ρ fuel := by
  simp only [prove, proveWithHash, seedWith_eq_withHash, runScript_eq_withHash]; rfl

end Prover

end LeanVM

end
