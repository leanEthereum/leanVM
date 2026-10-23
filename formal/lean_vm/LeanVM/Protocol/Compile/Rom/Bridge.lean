/-
  LeanVM.Protocol.Compile.Rom.Bridge

  The compiled verifier as an oracle computation, and the bridge from its runs against the
  logged random oracle to its deterministic run under the final log's answers.
-/

module

public import LeanVM.Protocol.Compile.Rom.History
public import LeanVM.Protocol.Compile.Rom.Potential
public import LeanVM.Protocol.ToVCVio.Rom.LoggedOracle
public import LeanVM.Spec.Statement

/-!
# The verifier against the random oracle

The hash of the compiled verifier is a random oracle `Bytes →ₒ Digest` (`HashSpec`); the
verifier is the generic `verify` of `LeanVM.Protocol.Compile.Rom.History` at the query
`queryH` (`verifierComp`).

* `simulateQ_verify`: interpreting the queries of `verifierComp` by any implementation is
  running `verify` with that implementation as the hash; the verifier commutes with
  simulation because each of its parts does (`simulateQ_climb`, …, `simulateQ_run`).
* `simulateQ_look_of_mem_support`: every outcome of a computation run against the logged random
  oracle (`loggedRO`) is the computation's value when each query is answered by the final log,
  or any longer log: the run only appends, and an answered query keeps its answer.
* `verify_of_mem_support_logExperiment`: so on every reachable outcome of the logged experiment
  in which the verifier accepts, `verify` accepts with the hash answered by the final log. This
  is the hypothesis of the final inequality (`LeanVM.Protocol.Compile.Rom.Final`).
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Rom
open OracleComp OracleSpec

@[expose] public section

export LeanVM (HashSpec queryH)

/-- The seeded verifier as an oracle computation. -/
def verifierComp (σ : Seed) (P : Prog Bool) (π : Proof) : OracleComp HashSpec Bool :=
  verify queryH σ P π

/-! ## Simulation commutes with the verifier -/

section Commute

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl HashSpec r)

theorem simulateQ_queryH (x : Bytes) : simulateQ impl (queryH x) = impl x := by
  simp [queryH]

theorem simulateQ_climb :
    ∀ (node : Digest) (q : ℕ) (path : List Digest),
      simulateQ impl (climb queryH node q path) = climb (fun x ↦ impl x) node q path
  | _, _, [] => by simp [climb]
  | node, q, s :: ss => by
    simp only [climb]
    split <;>
    · simp only [simulateQ_bind, simulateQ_queryH]
      congr 1; funext p; exact simulateQ_climb p _ ss

theorem simulateQ_openOne (root : Digest) (ht w q : ℕ) (o : Opening) :
    simulateQ impl (openOne queryH root ht w q o) = openOne (fun x ↦ impl x) root ht w q o := by
  simp only [openOne]
  split
  · simp only [simulateQ_bind, simulateQ_queryH, simulateQ_climb, simulateQ_pure]
  · simp

theorem simulateQ_openAll (root : Digest) (ht w : ℕ) :
    ∀ (ps : List ℕ) (os : List Opening),
      simulateQ impl (openAll queryH root ht w ps os) = openAll (fun x ↦ impl x) root ht w ps os
  | [], _ => by simp [openAll]
  | _ :: _, [] => by simp [openAll]
  | q :: qs, o :: os => by
    simp only [openAll, simulateQ_bind, simulateQ_openOne]
    congr 1; funext b
    split
    · simp only [simulateQ_bind, simulateQ_openAll root ht w qs os, simulateQ_pure]
    · simp

theorem simulateQ_run :
    ∀ (p : Prog Bool) (s : St),
      simulateQ impl (run queryH p s) = run (fun x ↦ impl x) p s
  | .ret a, s => by simp [run]
  | .fail, s => by simp [run]
  | .read k, s => by
    simp only [run]
    split
    · simp
    · simp only [absorbBlock, simulateQ_bind, simulateQ_queryH]
      congr 1; funext cv; exact simulateQ_run _ _
  | .sample k, s => by
    simp only [run, absorbBlock, simulateQ_bind, simulateQ_queryH]
    congr 1; funext cv; exact simulateQ_run _ _
  | .grind bits k, s => by
    simp only [run]
    split
    · simp
    · simp only [absorbBlock, simulateQ_bind, simulateQ_queryH]
      congr 1; funext base; congr 1; funext d; congr 1; funext cv
      split
      · exact simulateQ_run _ _
      · simp
  | .commit ht w k, s => by
    simp only [run]
    split
    · simp only [absorbBlock, simulateQ_bind, simulateQ_queryH]
      congr 1; funext cv0; congr 1; funext cv1
      split
      · exact simulateQ_run _ _
      · simp
    · simp
  | .query i ps k, s => by
    simp only [run]
    split
    · simp
    · simp only [simulateQ_bind, simulateQ_openAll]
      congr 1; funext o
      split
      · exact simulateQ_run _ _
      · simp

theorem simulateQ_runProof (P : Prog Bool) (seed : Digest) (π : Proof) :
    simulateQ impl (runProof queryH P seed π) = runProof (fun x ↦ impl x) P seed π := by
  simp only [runProof, simulateQ_bind, simulateQ_run]
  congr 1; funext o
  split <;> simp

theorem simulateQ_foldlM_seed :
    ∀ (as : List (Bytes × Bytes)) (d : Digest),
      simulateQ impl (as.foldlM (fun d a ↦ queryH (Seed.input a d)) d) =
        as.foldlM (fun d a ↦ impl (Seed.input a d)) d
  | [], d => by simp
  | a :: as, d => by
    simp only [List.foldlM_cons, simulateQ_bind, simulateQ_queryH]
    congr 1; funext d'; exact simulateQ_foldlM_seed as d'

theorem simulateQ_seedRun (σ : Seed) :
    simulateQ impl (σ.run queryH) = σ.run (fun x ↦ impl x) := by
  simp only [Seed.run, simulateQ_bind, simulateQ_queryH]
  congr 1; funext d; exact simulateQ_foldlM_seed impl _ d

/-- **The verifier commutes with simulation.** -/
theorem simulateQ_verify (σ : Seed) (P : Prog Bool) (π : Proof) :
    simulateQ impl (verifierComp σ P π) = verify (fun x ↦ impl x) σ P π := by
  simp only [verifierComp, verify, simulateQ_bind, simulateQ_seedRun, simulateQ_runProof]

end Commute

/-! ## Runs against the logged oracle -/

/-- The answers of a log, as an implementation of the oracle in `Option`. -/
def lookImpl (ℓ : Log) : QueryImpl HashSpec Option := fun t ↦ look ℓ t

/-- **Runs against the logged oracle.** Every outcome of a run against `loggedRO` from `ℓ` ends
with a log extending `ℓ`, and is the computation's value when every query is answered by any
log extending the final one. -/
theorem simulateQ_look_of_mem_support {β : Type} (oa : OracleComp HashSpec β) :
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
    have hp' : ℓ <+: p.2 ∧ look p.2 t = some p.1 := by
      rw [loggedRO_isLazySampler t ℓ] at hp
      beta_reduce at hp
      rcases hl : logLookup ℓ t with _ | u
      · rw [hl] at hp
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
        obtain ⟨u, -, rfl⟩ := hp
        exact ⟨List.prefix_append _ _, look_append_single_self hl u⟩
      · rw [hl] at hp
        simp only [support_pure, Set.mem_singleton_iff] at hp
        subst hp
        exact ⟨List.prefix_refl _, hl⟩
    obtain ⟨h1, h2⟩ := ih p.1 p.2 z hz
    refine ⟨hp'.1.trans h1, fun ℓ' hℓ' ↦ ?_⟩
    rw [simulateQ_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id]
    change (look ℓ' t).bind (fun u ↦ simulateQ _ (mx u)) = _
    rw [look_of_prefix (h1.trans hℓ') hp'.2]
    exact h2 ℓ' hℓ'

/-- **The bridge.** On every reachable outcome of the logged experiment in which the verifier
accepts, the seeded verifier accepts the adversary's proof with every hash answered by the
final log. -/
theorem verify_of_mem_support_logExperiment {σ : Seed} {P : Prog Bool}
    (A : OracleComp HashSpec Proof) {z : (Proof × Bool) × Log}
    (hz : z ∈ support (logExperiment A (verifierComp σ P))) (hacc : z.1.2 = true) :
    verify (look z.2) σ P z.1.1 = some true := by
  have h := (simulateQ_look_of_mem_support _ [] z hz).2 z.2 (List.prefix_refl _)
  rw [simulateQ_bind] at h
  obtain ⟨π, -, h⟩ := Option.bind_eq_some_iff.mp h
  rw [simulateQ_map] at h
  obtain ⟨b, hb, hπb⟩ := Option.map_eq_some_iff.mp h
  rw [← hπb] at hacc ⊢
  rw [simulateQ_verify] at hb
  simp only at hacc
  rw [← hacc]
  exact hb

/-- **The verifier of a family of statements**: on a statement and a proof, the statement's
seeded verifier, run from its root node. -/
def verifierFam {X : Type} (σ : Seeds X) (P : Prog Bool) (z : X × Proof) :
    OracleComp HashSpec Bool :=
  verifierComp (σ.seed z.1) (nodeAt P (σ.root z.1)) z.2

/-- **The bridge, for a family.** On every reachable outcome of the logged experiment in which
the verifier accepts, the statement's seeded verifier accepts the adversary's proof with every
hash answered by the final log. -/
theorem verifyFam_of_mem_support_logExperiment {X : Type} {σ : Seeds X} {P : Prog Bool}
    (A : OracleComp HashSpec (X × Proof)) {z : ((X × Proof) × Bool) × Log}
    (hz : z ∈ support (logExperiment A (verifierFam σ P))) (hacc : z.1.2 = true) :
    verify (look z.2) (σ.seed z.1.1.1) (nodeAt P (σ.root z.1.1.1)) z.1.1.2 = some true := by
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
