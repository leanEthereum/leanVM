/-
  LeanVM.Protocol.Compile.Rom.Bridge

  The compiled verifier as an oracle computation, and the bridge from its runs against the
  logged random oracles to its deterministic run under the final log's answers.
-/

module

public import LeanVM.Protocol.Compile.Rom.History
public import LeanVM.Protocol.Compile.Rom.Potential
public import LeanVM.Protocol.ToVCVio.Rom.LoggedOracle
public import Statement.LeanVm
public import LeanVM.Facts.Verifier
public import Statement.Fast.Keccak
public import Statement.Fast.CubicExt
public import Statement.Fast.FieldWords
public import LeanVM.Protocol.WithHash

/-!
# The verifier against the random oracles

The hash of the compiled verifier is a random oracle `Bytes →ₒ Digest` and its permutation a
random oracle `KState →ₒ KState` (`HashSpec`); the verifier is the generic `verify` of
`LeanVM.Protocol.Compile.Rom.History` at the queries `callKeccak256` and `callKeccakF1600` (`verifierComp`).

* `simulateQ_verify`: interpreting the queries of `verifierComp` by any implementation is
  running `verify` with that implementation as the hash and the permutation; the verifier
  commutes with simulation because each of its parts does (`simulateQ_climb`, …,
  `simulateQ_run`).
* `simulateQ_look_of_mem_support`: every outcome of a computation run against the logged random
  oracles (`loggedRO`) is the computation's value when each query is answered by the final log,
  or any longer log: the run only appends, and an answered query keeps its answer.
* `verifyFam_of_mem_support_logExperiment`: so on every reachable outcome of the logged
  experiment in which the verifier accepts, `verify` accepts with the hash and the permutation
  answered by the final log. This is the hypothesis of the final inequality
  (`LeanVM.Protocol.Compile.Rom.Final`).
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash LeanVM.Protocol.Rom
open OracleComp OracleSpec

@[expose] public section

export LeanVM (KeccakCalls callKeccak256 callKeccakF1600)

/-- The seeded verifier as an oracle computation. -/
def verifierComp (σ : Seed) (P : VerifierProgram Bool) (π : Proof) : OracleComp KeccakCalls Bool :=
  verify callKeccak256 callKeccakF1600 σ P π

/-! ## Simulation commutes with the verifier -/

section Commute

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)

/-- The hash an implementation answers. -/
def implH : Bytes → r Digest := fun x ↦ impl (.inl x)

/-- The permutation an implementation answers. -/
def implF : KeccakState → r KeccakState := fun s ↦ impl (.inr s)

theorem simulateQ_queryH (x : Bytes) : simulateQ impl (callKeccak256 x) = implH impl x := by
  simp [callKeccak256, implH]

theorem simulateQ_queryF (s : KeccakState) : simulateQ impl (callKeccakF1600 s) = implF impl s := by
  simp [callKeccakF1600, implF]

theorem simulateQ_climb :
    ∀ (node : Digest) (q : ℕ) (path : List Digest),
      simulateQ impl (climbWithHash callKeccak256 node q path) = climbWithHash (implH impl) node q path
  | _, _, [] => by simp [climbWithHash]
  | node, q, s :: ss => by
    simp only [climbWithHash]
    split <;>
    · simp only [simulateQ_bind, simulateQ_queryH]
      congr 1; funext p; exact simulateQ_climb p _ ss

theorem simulateQ_openOne (root : Digest) (ht w q : ℕ) (o : Opening) :
    simulateQ impl (openOneWithHash callKeccak256 root ht w q o) = openOneWithHash (implH impl) root ht w q o := by
  simp only [openOneWithHash]
  split
  · simp only [simulateQ_bind, simulateQ_queryH, simulateQ_climb, simulateQ_pure]
  · simp

theorem simulateQ_openAll (root : Digest) (ht w : ℕ) :
    ∀ (ps : List ℕ) (os : List Opening),
      simulateQ impl (openAllWithHash callKeccak256 root ht w ps os) = openAllWithHash (implH impl) root ht w ps os
  | [], _ => by simp [openAllWithHash]
  | _ :: _, [] => by simp [openAllWithHash]
  | q :: qs, o :: os => by
    simp only [openAllWithHash, simulateQ_bind, simulateQ_openOne]
    congr 1; funext b
    split
    · simp only [simulateQ_bind, simulateQ_openAll root ht w qs os, simulateQ_pure]
    · simp

theorem simulateQ_openPhase (root : Digest) (ht w : ℕ) (ps : List ℕ) (phase : List Opening) :
    simulateQ impl (openPhaseWithHash callKeccak256 root ht w ps phase) =
      openPhaseWithHash (implH impl) root ht w ps phase := by
  simp only [openPhaseWithHash]
  split
  · simp only [simulateQ_bind, simulateQ_openAll]
    congr 1; funext o
    split <;> simp
  · simp

theorem simulateQ_duplex (sp : Sponge) :
    simulateQ impl (duplex callKeccakF1600 sp) = duplex (implF impl) sp := by
  simp only [duplex, simulateQ_bind, simulateQ_queryF, simulateQ_pure]

theorem simulateQ_absorb (sp : Sponge) (x : E) (tag : ℕ) :
    simulateQ impl (Compile.absorb callKeccakF1600 sp x tag) = Compile.absorb (implF impl) sp x tag := by
  simp only [Compile.absorb]
  split
  · simp only [simulateQ_bind, simulateQ_duplex, simulateQ_pure]
  · simp

theorem simulateQ_squeeze (sp : Sponge) :
    simulateQ impl (squeeze callKeccakF1600 sp) = squeeze (implF impl) sp := by
  simp only [squeeze, simulateQ_bind, simulateQ_duplex, simulateQ_pure]

theorem simulateQ_run :
    ∀ (p : VerifierProgram Bool) (s : VerifierProgramState),
      simulateQ impl (runWithHash callKeccak256 callKeccakF1600 p s) = runWithHash (implH impl) (implF impl) p s
  | .ret a, s => by simp [runWithHash]
  | .fail, s => by simp [runWithHash]
  | .read k, s => by
    simp only [runWithHash]
    split
    · simp
    · simp only [simulateQ_bind, simulateQ_absorb]
      congr 1; funext sp; exact simulateQ_run _ _
  | .sample k, s => by
    simp only [runWithHash, simulateQ_bind, simulateQ_squeeze]
    congr 1; funext r; exact simulateQ_run _ _
  | .grind bits k, s => by
    simp only [runWithHash]
    split
    · simp
    · simp only [simulateQ_bind, simulateQ_absorb, simulateQ_squeeze]
      congr 1; funext sp; congr 1; funext r
      split
      · exact simulateQ_run _ _
      · simp
  | .commit ht w k, s => by
    simp only [runWithHash]
    split
    · simp only [simulateQ_bind, simulateQ_absorb]
      congr 1; funext sp0; congr 1; funext sp1
      split
      · exact simulateQ_run _ _
      · simp
    · simp
  | .query i ps k, s => by
    simp only [runWithHash]
    split
    · simp only [simulateQ_bind, simulateQ_openPhase]
      congr 1; funext o
      split
      · exact simulateQ_run _ _
      · simp
    · simp

theorem simulateQ_runProof (P : VerifierProgram Bool) (seed : KeccakState) (π : Proof) :
    simulateQ impl (runProofWithHash callKeccak256 callKeccakF1600 P seed π) =
      runProofWithHash (implH impl) (implF impl) P seed π := by
  simp only [runProofWithHash, simulateQ_bind, simulateQ_run]
  congr 1; funext o
  split <;> simp

theorem simulateQ_hsRun :
    ∀ (fs : List (List Digest → Bytes)) (ds : List Digest),
      simulateQ impl (Seed.hsRun callKeccak256 fs ds) = Seed.hsRun (implH impl) fs ds
  | [], ds => by simp [Seed.hsRun]
  | f :: fs, ds => by
    simp only [Seed.hsRun, simulateQ_bind, simulateQ_queryH]
    congr 1; funext d; exact simulateQ_hsRun fs _

theorem simulateQ_seedRun (σ : Seed) :
    simulateQ impl (σ.run callKeccak256 callKeccakF1600) = σ.run (implH impl) (implF impl) := by
  simp only [Seed.run, simulateQ_bind, simulateQ_hsRun, simulateQ_queryF]

/-- **The verifier commutes with simulation.** -/
theorem simulateQ_verify (σ : Seed) (P : VerifierProgram Bool) (π : Proof) :
    simulateQ impl (verifierComp σ P π) = verify (implH impl) (implF impl) σ P π := by
  simp only [verifierComp, verify, simulateQ_bind, simulateQ_seedRun, simulateQ_runProof]

end Commute

/-! ## Runs against the logged oracles -/

/-- The answers of a log, as an implementation of the oracles in `Option`. -/
def lookImpl (ℓ : Log) : QueryImpl KeccakCalls Option := logLookup ℓ

theorem logLookup_of_prefix {ℓ ℓ' : Log} (hp : ℓ <+: ℓ') {t : Bytes ⊕ KeccakState}
    {v : KeccakCalls.Range t} (h : logLookup ℓ t = some v) : logLookup ℓ' t = some v := by
  rcases t with x | s
  · exact lookH_of_prefix hp h
  · exact lookF_of_prefix hp h

theorem logLookup_logRecord_self {ℓ : Log} {t : Bytes ⊕ KeccakState} (h : logLookup ℓ t = none)
    (u : KeccakCalls.Range t) : logLookup (logRecord ℓ t u) t = some u := by
  rw [logLookup_logRecord ℓ t u h t]
  simp

theorem prefix_logRecord (ℓ : Log) (t : Bytes ⊕ KeccakState) (u : KeccakCalls.Range t) :
    ℓ <+: logRecord ℓ t u := by
  rcases t with x | s <;> exact List.prefix_append _ _

/-- **Runs against the logged oracles.** Every outcome of a run against `loggedRO` from `ℓ` ends
with a log extending `ℓ`, and is the computation's value when every query is answered by any
log extending the final one. -/
theorem simulateQ_look_of_mem_support {β : Type} (oa : OracleComp KeccakCalls β) :
    ∀ (ℓ : Log) (z : β × Log), z ∈ support ((simulateQ loggedRO oa).run ℓ) →
      ℓ <+: z.2 ∧ ∀ ℓ', z.2 <+: ℓ' → simulateQ (lookImpl ℓ') oa = some z.1 := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro ℓ z hz
    simp at hz
    subst hz
    exact ⟨List.prefix_refl _, fun _ _ ↦ rfl⟩
  | query_bind t mx ih =>
    intro ℓ z hz
    rw [simulateQ_query_bind, StateT.run_bind] at hz
    simp only [OracleQuery.input_query, monadLift_self] at hz
    change z ∈ support ((loggedRO t).run ℓ >>= fun p ↦ (simulateQ loggedRO (mx p.1)).run p.2)
      at hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    have hp' : ℓ <+: p.2 ∧ logLookup p.2 t = some p.1 := by
      rw [loggedRO_isLazySampler t ℓ] at hp
      beta_reduce at hp
      rcases hl : logLookup ℓ t with _ | u
      · rw [hl] at hp
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
        obtain ⟨u, -, rfl⟩ := hp
        exact ⟨prefix_logRecord ℓ t u, logLookup_logRecord_self hl u⟩
      · rw [hl] at hp
        simp only [support_pure, Set.mem_singleton_iff] at hp
        subst hp
        exact ⟨List.prefix_refl _, hl⟩
    obtain ⟨h1, h2⟩ := ih p.1 p.2 z hz
    refine ⟨hp'.1.trans h1, fun ℓ' hℓ' ↦ ?_⟩
    rw [simulateQ_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id]
    change (logLookup ℓ' t).bind (fun u ↦ simulateQ _ (mx u)) = _
    rw [logLookup_of_prefix (h1.trans hℓ') hp'.2]
    exact h2 ℓ' hℓ'

/-- **The verifier of a family of statements**: on a statement and a proof, the statement's
seeded verifier, run from its root node. -/
def verifierFam {X : Type} (σ : Seeds X) (P : VerifierProgram Bool) (z : X × Proof) :
    OracleComp KeccakCalls Bool :=
  verifierComp (σ.seed z.1) (nodeAt P (σ.root z.1)) z.2

/-- **The bridge, for a family.** On every reachable outcome of the logged experiment in which
the verifier accepts, the statement's seeded verifier accepts the adversary's proof with every
query answered by the final log. -/
theorem verifyFam_of_mem_support_logExperiment {X : Type} {σ : Seeds X} {P : VerifierProgram Bool}
    (A : OracleComp KeccakCalls (X × Proof)) {z : ((X × Proof) × Bool) × Log}
    (hz : z ∈ support (logExperiment A (verifierFam σ P))) (hacc : z.1.2 = true) :
    verify (lookH z.2) (lookF z.2) (σ.seed z.1.1.1) (nodeAt P (σ.root z.1.1.1)) z.1.1.2 =
      some true := by
  have h := (simulateQ_look_of_mem_support _ [] z hz).2 z.2 (List.prefix_refl _)
  rw [simulateQ_bind] at h
  obtain ⟨π, -, h⟩ := Option.bind_eq_some_iff.mp h
  rw [simulateQ_map] at h
  obtain ⟨b, hb, hπb⟩ := Option.map_eq_some_iff.mp h
  rw [← hπb] at hacc ⊢
  rw [verifierFam, simulateQ_verify] at hb
  simp only at hacc
  rw [← hacc]
  exact hb

end
end LeanVM.Protocol.Compile.Rom
