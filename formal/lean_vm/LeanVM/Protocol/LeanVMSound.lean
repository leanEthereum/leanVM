/-
  LeanVM.Protocol.LeanVMSound

  Knowledge soundness of the leanVM verifier in the two-oracle random-oracle model
  (`LeanVM/Protocol/Rom/Statement.lean`), at 125 bits per query: the step of the proof of
  `LeanVM.KnowledgeSoundness` (`Statement/LeanVm.lean`) before the random-permutation model.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.Statements
public import LeanVM.Protocol.EndToEnd.Sound.Extractor
public import LeanVM.Protocol.Extraction.Sound
public import LeanVM.Protocol.WithHash
public import LeanVM.Protocol.Whir.Params.Iface

/-!
# leanVM, knowledge soundness

The statements are in `LeanVM/Spec/` (the ISA, the verifier, the extractor, `Statement.lean` and,
in the random-permutation model, `Rpm.lean`), which imports nothing else from the repository.
This page proves knowledge soundness in the two-oracle random-oracle model of
`LeanVM/Protocol/Rom/Statement.lean`, `knowledgeSoundnessRom_holds`, and gives the numbers;
`LeanVM.Protocol.LeanVM` proves completeness there, and `LeanVM.Protocol.LeanVMRpm` moves both to
the random-permutation model.

The verifier is leanVM's at the commit `leanvm-rev` names (`crates/verifier`), its
Fiat-Shamir sponge a duplex sponge over Keccak-f[1600] and its Merkle hash Keccak-256. Both are
modelled as independent random oracles (`HashSpec = (Bytes →ₒ Digest) + (KState →ₒ KState)`).

**Knowledge soundness** (`knowledgeSoundnessRom`): an adversary making at most `Q` queries to the
random oracles outputs a statement (a program and a public input) and a proof, choosing all three
after querying the oracles. The probability that the verifier accepts while the program's last
instruction is not a `JUMP` and the extractor (`extractor`, `LeanVM/Protocol/Extraction/Extractor.lean`: from
the proof and the oracle's answers to the adversary's Keccak-256 queries only, the halting run of
the memory image of a stack in the Johnson list of the word the proof commits to) does not return
a valid execution of the program on the public input is at most
`soundnessError Q = (Q + 13261) · (2^-125 + 5·(Q + 13261)/2^256) + 13261/2^256`, which is at most
`2^-60` for `Q ≤ 2^64` (`soundnessError_le`, `LeanVM.Protocol.ErrorBounds`). The `2^-125` is per
oracle query: every group of the protocol's challenges, discounted by the proof of work before it,
escapes with probability at most `2^-125`, the round-by-round error every verifier message is held
to after its grind (`SECURITY_BITS`), certified for every admissible size and rate. The
`13261` bounds the verifier's queries on every statement and proof
(`Verifier.leanVmQueryBound_eq`).

The proof (`knowledgeSoundnessRom`) runs the experiment over the ordered log of fresh queries, the
adversary's part first (`experiment_eq`, `Sound.logged2`). The proof's own extractor
(`Sound.extractStack`) reads the whole log and picks a stack satisfying the leanISA relation; an
accepted proof on which it fails is doomed, or the log fails (a fresh answer collides with or
predicts a digest or a sponge state's capacity the log refers to: `5 + 2` per earlier query, the
`2` the seed's two offsets), and both have probability at most the first term
(`Compile.Rom.romSound_log`). When it succeeds, the specification's extractor, reading the
adversary's part of the log only, returns a valid execution (`Sound.extractor_of_extracted`):
without failure, every climb to the announced root through the log runs through the adversary's
queries, unless a fresh Keccak-256 answer of the verifier is the root itself, which has
probability at most `13261/2^256` (`Sound.prEvent_logged2_root_le`, the second term).

**Scope and trust.**

* The stacked opening's specification enters through the interface `Sound.OpeningIface`
  (`EndToEnd/Sound/Assemble.lean`): level 0's threshold, list bound and shape, and the opening's
  specification from "every candidate violates a claim", filled by the deployed WHIR opening
  (`Whir.Params.openingIface`, `LeanVM/Protocol/Whir/Params/Iface.lean`).

* Keccak-256 and Keccak-f[1600] are independent random oracles here, the step of the proof before
  the random-permutation model of the statements (`LeanVM/Protocol/LeanVMRpm.lean`).
* The extractor is straight-line (it reads the proof and the answers to the adversary's
  queries, never the verifier's, and does not rewind), and a deterministic algorithm
  (`LeanVM/Protocol/Extraction/Extractor.lean`: it list-decodes the committed word and runs the candidates). Here
  the byte strings the cache answers, its keys, are enumerated classically
  (`Extraction.supportKeys`); which covering keys it is given does not change what it returns
  (`Extraction.ExtractProofs.extract_keys_congr`).
* That `verifier` is the Rust verifier is test evidence, not proof.
* Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Rom (cacheOf map_run_simulateQ_loggedRO_nil map_run_simulateQ_loggedRO)
open scoped ENNReal

@[expose] public section

/-- **The deployed verifier**: `verifier` with Keccak-256 and Keccak-f[1600] (moved here from
`Statement/LeanVm.lean`; no end statement names it). -/
def verify (prog : LeanIsaProgram) (input : PublicInput) (proof : Proof) : Bool :=
  Id.run (verifierWithHash (m := Id) keccak256 keccakF1600 prog input proof)

/-- `verify` is the transcription of the deployed verifier, run with Keccak-256 and
Keccak-f[1600] (`LeanVM.Protocol.Verifier.verify`, what `lake exe leanvm-verify` runs). -/
theorem verify_eq (prog : LeanIsaProgram) (input : PublicInput) (proof : Proof) :
    verify prog input proof =
      LeanVM.Protocol.Verifier.verify (bytecodeWords prog) (publicInputDigest input) proof :=
  rfl

/-- The verifier of the experiment, on a statement and a proof. -/
abbrev expVerifier : ProgramAndInput × Proof → OracleComp KeccakCalls Bool :=
  fun z ↦ verifierWithHash callKeccak256 callKeccakF1600 z.1.1 z.1.2 z.2

/-- The experiment's verifier is the random-oracle theorem's verifier of every statement. -/
theorem expVerifier_eq : expVerifier = Rom.verifierFam Sound.leanVmSeeds Sound.anyProgram := by
  funext z
  rw [Sound.verifierFam_leanVm, verifierComp_leanVm]
  rfl

/-- **The experiment over the ordered log**: the adversary's run from the empty log, then the
verifier's from the log it left (`Sound.logged2`), each log read as a cache. -/
theorem experiment_eq (A : Adversary) :
    experiment A = (fun w ↦ ((w.1.1, w.2.1), cacheOf w.2.2, cacheOf w.1.2)) <$>
      Sound.logged2 A expVerifier := by
  simp only [experiment, Sound.logged2, ← map_run_simulateQ_loggedRO_nil, bind_map_left,
    map_bind, Functor.map_map]
  refine bind_congr fun p ↦ ?_
  rw [← map_run_simulateQ_loggedRO, bind_map_left]
  simp [map_eq_bind_pure_comp]

/-! ## Knowledge soundness -/

/-- **Knowledge soundness in the random-oracle model.** For an adversary making at most `Q`
queries, which chooses the program, the public input and the proof, the verifier accepts while
the extractor `extractor`
(`LeanVM/Protocol/Extraction/Extractor.lean`) does not return a valid execution of the program on the public
input with probability at most `soundnessError Q`. -/
theorem knowledgeSoundnessRom {A : Adversary} {Q : ℕ}
    (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← experiment A}[Breaks extractor z] ≤ soundnessError Q := by
  -- Doom or failure, read off the final log.
  have h1 := romSound_log Sound.anyProgram (Sound.anyCert LeanVM.Protocol.Whir.Params.openingIface) Sound.leanVmSeeds
    (fun x ↦ Sound.rootOk_stmtHistory x) εmsg (Sound.anyCert_bound LeanVM.Protocol.Whir.Params.openingIface) A Q hA
    leanVmQueryBound Sound.isTotalQueryBound_leanVmFam
    (fun z ℓ ↦ Fail Sound.leanVmSeeds ℓ ∨
      Rom.verify (lookH ℓ) (lookF ℓ)
        (leanVmSeed (bytecodeWords z.1.1) (publicInputDigest z.1.2))
        (leanVmVerifierProgram (bytecodeWords z.1.1) (publicInputDigest z.1.2)) z.2 ≠ some true ∨
      ¬ Sound.Extracted LeanVM.Protocol.Whir.Params.openingIface z.1.1 z.1.2 (cacheOf ℓ) z.2)
    (fun z ℓ hf hv hb ↦ by
      simp only [Sound.leanVmSeeds, Sound.nodeAt_stmtHistory] at hv
      rcases hb with hb | hb | hb
      · exact absurd hb hf
      · exact absurd hv hb
      · exact Sound.doomed_of_doomedRun LeanVM.Protocol.Whir.Params.openingIface hv
          (Sound.doomed_of_not_extracted LeanVM.Protocol.Whir.Params.openingIface z.1.1 z.1.2 hv hb))
  rw [Sound.logExperiment_eq_logged2, prEvent_map] at h1
  -- A fresh Keccak-256 answer of the verifier that is the announced root.
  have h2 := Sound.prEvent_logged2_root_le A (Rom.verifierFam Sound.leanVmSeeds Sound.anyProgram)
    leanVmQueryBound Sound.isTotalQueryBound_leanVmFam (fun z ↦ Sound.announcedRoot z.1.1 z.2)
  rw [experiment_eq, expVerifier_eq, prEvent_map, soundnessError]
  refine (prEvent_mono _ _ _ ?_).trans ((prEvent_or_le _ _ _).trans
    (add_le_add (h1.trans (le_of_eq ?_)) (h2.trans (le_of_eq ?_))))
  · rintro w ⟨hacc, hno⟩
    dsimp only at hacc hno ⊢
    by_contra hne
    rw [not_or] at hne
    obtain ⟨hn1, hn2⟩ := hne
    have hf : ¬ Fail Sound.leanVmSeeds w.2.2 := fun h ↦ hn1 ⟨hacc, Or.inl h⟩
    have hv : Rom.verify (lookH w.2.2) (lookF w.2.2)
        (leanVmSeed (bytecodeWords w.1.1.1.1) (publicInputDigest w.1.1.1.2))
        (leanVmVerifierProgram (bytecodeWords w.1.1.1.1) (publicInputDigest w.1.1.1.2))
        w.1.1.2 = some true := by
      by_contra h
      exact hn1 ⟨hacc, Or.inr (Or.inl h)⟩
    have hx : Sound.Extracted LeanVM.Protocol.Whir.Params.openingIface w.1.1.1.1 w.1.1.1.2 (cacheOf w.2.2) w.1.1.2 := by
      by_contra h
      exact hn1 ⟨hacc, Or.inr (Or.inr h)⟩
    have hpre : w.1.2 <+: w.2.2 := by
      by_contra h
      exact hn2 (Or.inl h)
    obtain ⟨t, ht, htv⟩ := Sound.extractor_of_extracted LeanVM.Protocol.Whir.Params.openingIface Sound.leanVmSeeds hf hv
      (fun r hr x hx ↦ hn2 (Or.inr ⟨r, hr, x, hx⟩)) hx
    rw [← List.prefix_iff_eq_take.mp hpre] at ht
    exact hno ⟨t, ht, htv⟩
  · rw [leanVmQueryBound_eq, failBound]
    rfl
  · rw [leanVmQueryBound_eq, div_eq_mul_inv, verifierQueries]

/-- **The extractor's list is short**: at every admissible stack size and rate, the candidates of
any word at the Johnson threshold are at most level 0's list bound. -/
theorem candidates_ncard_le {μ R : ℕ} (h : Parameters.Whir.Admissible μ R) (W : ℕ → List K) :
    (Extraction.Candidates μ R (Extraction.johnsonThreshold μ R) W).ncard ≤
      Protocol.Whir.Params.listMax₀ μ R :=
  Sound.spec_candidates_ncard_le LeanVM.Protocol.Whir.Params.openingIface h W

/-! ## The statement of `LeanVM/Protocol/Rom/Statement.lean` -/

/-- **Knowledge soundness in the two-oracle random-oracle model holds**, for the extractor
`extractor`. -/
theorem knowledgeSoundnessRom_holds : KnowledgeSoundnessRom :=
  fun _ _ hA ↦ knowledgeSoundnessRom hA

end
end LeanVM
