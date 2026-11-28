/-
  LeanVM.Protocol.LeanVMSoundAS

  Knowledge soundness of the leanVM verifier in the two-oracle random-oracle model, for the
  agreement-set extractor.
-/

module

public import LeanVM.Protocol.Relation.AgreementExtractor
public import LeanVM.Protocol.Rom.Statement
public import LeanVM.Protocol.Keccak.Iface
import LeanVM.Protocol.Verifier.Cost

/-!
# leanVM, knowledge soundness for the agreement-set extractor

From tag `formal-bus-archive`, `Protocol/LeanVMSoundAS.lean` and the experiment's part of
`Protocol/LeanVMSound.lean`.

`knowledgeSoundnessRomAS LI : KnowledgeSoundnessRom extractorAS soundnessErrorAS`: for an
adversary of at most `Q` queries, the verifier accepts while the agreement-set extractor
(`Relation.extractAS` on the adversary's answers) does not return a valid execution with
probability at most `soundnessErrorAS Q`: the random-oracle theorem's
`(Q + V) · (2^-125 + 5 (Q + V) / 2^256)`, `V = leanVmQueryBound` (an accepted proof whose extracted
history is not a good run is doomed at the stack's root, `Relation.doomedRun_of_verify`), a fresh
hit of the final query's proof of work, `2^-127` once in all (`Relation.prEvent_logged2_hit_le`),
and a fresh hash answer of the verifier that is a root the replay reads, `rootCap · 2^-256` per
verifier query (`Relation.prEvent_logged2_roots_le`). Outside those, the adversary's answers cover
the extractor's queries (`Relation.avail_or_hit`) and the extractor returns a valid execution
(`Relation.extractAS_valid`).

The link's interface `LI : LinkIface` is a parameter: the certificate (`Relation.leanVmCert`) and
the meaning of a good run (`LinkIface.valid`) are stated over it, and the extractor does not read
it.
-/

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.Relation
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Whir.Params
open LeanVM.Protocol.Rom (cacheOf map_run_simulateQ_loggedRO_nil map_run_simulateQ_loggedRO)
open OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/-! ## The experiment over the ordered log -/

/-- The verifier of the experiment, on a statement and a proof. -/
abbrev expVerifier : ProgramAndInput × Proof → OracleComp KeccakCalls Bool :=
  fun z ↦ verifierWithHash callKeccak256 callKeccakF1600 z.1.1 z.1.2 z.2

/-- The experiment's verifier is the random-oracle theorem's verifier of every statement. -/
theorem expVerifier_eq : expVerifier = Rom.verifierFam leanVmSeeds anyProgram := by
  funext z
  rw [verifierFam_leanVm, verifierComp_leanVm]
  rfl

/-- **The experiment over the ordered log**: the adversary's run from the empty log, then the
verifier's from the log it left (`Relation.logged2`), each log read as a cache. -/
theorem experiment_eq (A : Adversary) :
    experiment A = (fun w ↦ ((w.1.1, w.2.1), cacheOf w.2.2, cacheOf w.1.2)) <$>
      logged2 A expVerifier := by
  simp only [experiment, logged2, ← map_run_simulateQ_loggedRO_nil, bind_map_left,
    map_bind, Functor.map_map]
  refine bind_congr fun p ↦ ?_
  rw [← map_run_simulateQ_loggedRO, bind_map_left]
  simp [map_eq_bind_pure_comp]

theorem romRootCap_eq : romRootCap = rootCap := rfl

/-! ## Knowledge soundness -/

/-- **Knowledge soundness in the random-oracle model, for the agreement-set extractor.** For an
adversary making at most `Q` queries, which chooses the program, the public input and the proof,
the verifier accepts while `extractorAS` does not return a valid execution of the program on
the public input with probability at most `soundnessErrorAS Q`. -/
theorem knowledgeSoundnessRomAS (LI : LinkIface) :
    KnowledgeSoundnessRom extractorAS soundnessErrorAS := by
  intro A Q hA
  -- Doom or failure, read off the final log.
  have h1 := romSound_logG anyProgram (anyCert openingIface LI KeccakGkr.keccakIface)
    leanVmSeeds (fun x ↦ rootOk_stmtHistory x) εmsg
    (anyCert_bound openingIface LI KeccakGkr.keccakIface) A Q hA leanVmQueryBound
    isTotalQueryBound_leanVmFam
    (fun z ℓ ↦ Fail leanVmSeeds ℓ ∨
      Rom.verify (lookH ℓ) (lookF ℓ)
        (leanVmSeed (bytecodeWords z.1.1) (publicInputDigest z.1.2))
        (leanVmVerifierProgram (bytecodeWords z.1.1) (publicInputDigest z.1.2)) z.2 ≠ some true ∨
      ¬ stmtG openingIface LI z.1 (extractedHistory (lookH ℓ) (lookF ℓ)
        (leanVmSeed (bytecodeWords z.1.1) (publicInputDigest z.1.2))
        (leanVmVerifierProgram (bytecodeWords z.1.1) (publicInputDigest z.1.2)) z.2))
    (fun z ℓ hf hv hb ↦ by
      simp only [leanVmSeeds, nodeAt_stmtHistory] at hv
      rcases hb with hb | hb | hb
      · exact absurd hb hf
      · exact absurd hv hb
      · exact ⟨doomed_of_doomedRun openingIface LI KeccakGkr.keccakIface hv
          (doomedRun_of_verify openingIface LI KeccakGkr.keccakIface _ _ _ hv),
          not_anyG_of (c := cacheOf ℓ) openingIface LI hv hb⟩)
  rw [logExperiment_eq_logged2, prEvent_map] at h1
  -- A fresh hit of the final proof of work, and a fresh root.
  have h2 := prEvent_logged2_hit_le A (Rom.verifierFam leanVmSeeds anyProgram)
    leanVmQueryBound isTotalQueryBound_leanVmFam (fun z ↦ bytecodeWords z.1.1)
    (fun z ↦ z.1.2) (fun z ↦ z.2)
  have h3 := prEvent_logged2_roots_le A (Rom.verifierFam leanVmSeeds anyProgram)
    leanVmQueryBound isTotalQueryBound_leanVmFam (fun z ↦ bytecodeWords z.1.1)
    (fun z ↦ z.1.2) (fun z ↦ z.2)
  rw [experiment_eq, expVerifier_eq, prEvent_map, soundnessErrorAS, romRootCap_eq]
  refine (prEvent_mono _ _ _ ?_).trans ((prEvent_or_le _ _ _).trans
    (add_le_add ((prEvent_or_le _ _ _).trans (add_le_add (h1.trans (le_of_eq ?_)) h2)) h3))
  · rintro w ⟨hacc, hno⟩
    dsimp only at hacc hno ⊢
    by_contra hne
    simp only [not_or] at hne
    obtain ⟨⟨hn1, hn2, hn2'⟩, hn3, hn3'⟩ := hne
    have hf : ¬ Fail leanVmSeeds w.2.2 := fun h ↦ hn1 ⟨hacc, Or.inl h⟩
    have hv : Rom.verify (lookH w.2.2) (lookF w.2.2)
        (leanVmSeed (bytecodeWords w.1.1.1.1) (publicInputDigest w.1.1.1.2))
        (leanVmVerifierProgram (bytecodeWords w.1.1.1.1) (publicInputDigest w.1.1.1.2))
        w.1.1.2 = some true := by
      by_contra h
      exact hn1 ⟨hacc, Or.inr (Or.inl h)⟩
    have hG : stmtG openingIface LI w.1.1.1
        (extractedHistory (lookH w.2.2) (lookF w.2.2)
          (leanVmSeed (bytecodeWords w.1.1.1.1) (publicInputDigest w.1.1.1.2))
          (leanVmVerifierProgram (bytecodeWords w.1.1.1.1) (publicInputDigest w.1.1.1.2))
          w.1.1.2) := by
      by_contra h
      exact hn1 ⟨hacc, Or.inr (Or.inr h)⟩
    have hpre : w.1.2 <+: w.2.2 := not_not.mp hn2
    obtain ⟨seed, hseed, hav | ⟨j, hkj, hj, t, u, hej, hhit⟩⟩ := avail_or_hit hf hv w.1.2.length
    · obtain ⟨t, ht, htv⟩ := extractAS_valid LI hf hpre hv hG
        (fun seed' hseed' ↦ by
          rw [hseed] at hseed'
          cases hseed'
          exact hav) hn3' (keysCover_supportKeys (finite_of_keysCover (keysCover_lookH w.1.2)))
      exact hno ⟨t, ht, htv⟩
    · exact hn2' ⟨j, hkj, hj, t, u, hej, hhit⟩
  · rw [failBound]
    rfl

end
end LeanVM
