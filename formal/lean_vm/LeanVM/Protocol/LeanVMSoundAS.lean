/-
  LeanVM.Protocol.LeanVMSoundAS

  Knowledge soundness of the leanVM verifier in the two-oracle random-oracle model, for the
  agreement-set extractor over any near-tuple decoder.
-/

module

public import LeanVM.Protocol.LeanVMSound
public import LeanVM.Protocol.EndToEnd.Sound.AgreementExtractor
public import LeanVM.Protocol.ErrorBounds

/-!
# leanVM, knowledge soundness for the agreement-set extractor

`knowledgeSoundnessRomAS`: for an adversary of at most `Q` queries, the verifier accepts while the
agreement-set extractor (`Sound.extractAS`, over any near-tuple decoder `D`, on the adversary's
answers) does not return a valid execution with probability at most `soundnessErrorAS Q`: the
random-oracle theorem's `(Q + V) · (2^-125 + 5 (Q + V) / 2^256)` (an accepted proof whose extracted
history is not a good run is doomed, `Sound.doomedRun_of_verify`), a fresh hit of the final query's
proof of work, `2^-127` once in all (`Sound.prEvent_logged2_hit_le`), and a fresh hash answer of
the verifier that is a root the replay reads, `rootCap · 2^-256` per verifier query
(`Sound.prEvent_logged2_roots_le`). Outside those, the adversary's answers cover the extractor's
queries (`Sound.avail_or_hit`) and the extractor returns a valid execution
(`Sound.extractAS_valid`).
-/

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir.Sound LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Rom (cacheOf)
open scoped ENNReal

@[expose] public section

/-- **The agreement-set extractor of the random-oracle model**, over the near-tuple decoder `D`,
on the adversary's cached answers. -/
noncomputable def extractorAS (D : NearDecoder) : Extractor := fun prog input answers π ↦
  Sound.extractAS D prog input (fun x ↦ answers (.inl x)) (fun t ↦ answers (.inr t)) π

/-- **The knowledge-soundness error for the agreement-set extractor**: the random-oracle theorem's,
a fresh hit of the final proof of work (`2^-127`, once), and a fresh hash answer of the verifier
that is a root the replay reads (`rootCap · 2^-256` per call). -/
noncomputable def soundnessErrorAS (Q : ℕ) : ℝ≥0∞ :=
  ((Q + verifierQueries : ℕ) : ℝ≥0∞) *
      ((2 : ℝ≥0∞)⁻¹ ^ 125 + ((5 * (Q + verifierQueries) : ℕ) : ℝ≥0∞) / 2 ^ 256) +
    (2 : ℝ≥0∞)⁻¹ ^ 127 + (verifierQueries : ℝ≥0∞) * (Sound.rootCap * (2 ^ 256 : ℝ≥0∞)⁻¹)

/-- **Knowledge soundness in the random-oracle model, for the agreement-set extractor.** For an
adversary making at most `Q` queries, which chooses the program, the public input and the proof,
the verifier accepts while `extractorAS D` does not return a valid execution of the program on
the public input with probability at most `soundnessErrorAS Q`. -/
theorem knowledgeSoundnessRomAS (D : NearDecoder) {A : Adversary} {Q : ℕ}
    (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← experiment A}[Breaks (extractorAS D) z] ≤ soundnessErrorAS Q := by
  -- Doom or failure, read off the final log.
  have h1 := romSound_logG Sound.anyProgram (Sound.anyCert Whir.Params.openingIface)
    Sound.leanVmSeeds (fun x ↦ Sound.rootOk_stmtHistory x) εmsg
    (Sound.anyCert_bound Whir.Params.openingIface) A Q hA leanVmQueryBound
    Sound.isTotalQueryBound_leanVmFam
    (fun z ℓ ↦ Fail Sound.leanVmSeeds ℓ ∨
      Rom.verify (lookH ℓ) (lookF ℓ)
        (leanVmSeed (bytecodeWords z.1.1) (publicInputDigest z.1.2))
        (leanVmVerifierProgram (bytecodeWords z.1.1) (publicInputDigest z.1.2)) z.2 ≠ some true ∨
      ¬ Sound.stmtG Whir.Params.openingIface z.1.1 z.1.2 (extractedHistory (lookH ℓ) (lookF ℓ)
        (leanVmSeed (bytecodeWords z.1.1) (publicInputDigest z.1.2))
        (leanVmVerifierProgram (bytecodeWords z.1.1) (publicInputDigest z.1.2)) z.2))
    (fun z ℓ hf hv hb ↦ by
      simp only [Sound.leanVmSeeds, Sound.nodeAt_stmtHistory] at hv
      rcases hb with hb | hb | hb
      · exact absurd hb hf
      · exact absurd hv hb
      · exact ⟨Sound.doomed_of_doomedRun Whir.Params.openingIface hv
          (Sound.doomedRun_of_verify Whir.Params.openingIface z.1.1 z.1.2 hv),
          Sound.not_anyG_of (c := cacheOf ℓ) Whir.Params.openingIface hv hb⟩)
  rw [Sound.logExperiment_eq_logged2, prEvent_map] at h1
  -- A fresh hit of the final proof of work, and a fresh root.
  have h2 := Sound.prEvent_logged2_hit_le A (Rom.verifierFam Sound.leanVmSeeds Sound.anyProgram)
    leanVmQueryBound Sound.isTotalQueryBound_leanVmFam (fun z ↦ bytecodeWords z.1.1)
    (fun z ↦ publicInputDigest z.1.2) (fun z ↦ z.2)
  have h3 := Sound.prEvent_logged2_roots_le A (Rom.verifierFam Sound.leanVmSeeds Sound.anyProgram)
    leanVmQueryBound Sound.isTotalQueryBound_leanVmFam (fun z ↦ bytecodeWords z.1.1)
    (fun z ↦ publicInputDigest z.1.2) (fun z ↦ z.2)
  rw [experiment_eq, expVerifier_eq, prEvent_map, soundnessErrorAS]
  refine (prEvent_mono _ _ _ ?_).trans ((prEvent_or_le _ _ _).trans
    (add_le_add ((prEvent_or_le _ _ _).trans (add_le_add (h1.trans (le_of_eq ?_)) h2))
      (h3.trans (le_of_eq ?_))))
  · rintro w ⟨hacc, hno⟩
    dsimp only at hacc hno ⊢
    by_contra hne
    simp only [not_or] at hne
    obtain ⟨⟨hn1, hn2, hn2'⟩, hn3, hn3'⟩ := hne
    have hf : ¬ Fail Sound.leanVmSeeds w.2.2 := fun h ↦ hn1 ⟨hacc, Or.inl h⟩
    have hv : Rom.verify (lookH w.2.2) (lookF w.2.2)
        (leanVmSeed (bytecodeWords w.1.1.1.1) (publicInputDigest w.1.1.1.2))
        (leanVmVerifierProgram (bytecodeWords w.1.1.1.1) (publicInputDigest w.1.1.1.2))
        w.1.1.2 = some true := by
      by_contra h
      exact hn1 ⟨hacc, Or.inr (Or.inl h)⟩
    have hG : Sound.stmtG Whir.Params.openingIface w.1.1.1.1 w.1.1.1.2
        (extractedHistory (lookH w.2.2) (lookF w.2.2)
          (leanVmSeed (bytecodeWords w.1.1.1.1) (publicInputDigest w.1.1.1.2))
          (leanVmVerifierProgram (bytecodeWords w.1.1.1.1) (publicInputDigest w.1.1.1.2))
          w.1.1.2) := by
      by_contra h
      exact hn1 ⟨hacc, Or.inr (Or.inr h)⟩
    have hpre : w.1.2 <+: w.2.2 := not_not.mp hn2
    obtain ⟨seed, hseed, hav | ⟨j, hkj, hj, t, u, hej, hhit⟩⟩ := Sound.avail_or_hit hf hv w.1.2.length
    · obtain ⟨t, ht, htv⟩ := Sound.extractAS_valid D hf hpre hv hG
        (fun seed' hseed' ↦ by
          rw [hseed] at hseed'
          cases hseed'
          exact hav) hn3'
      exact hno ⟨t, ht, htv⟩
    · exact hn2' ⟨j, hkj, hj, t, u, hej, hhit⟩
  · rw [leanVmQueryBound_eq, failBound]
    rfl
  · rw [leanVmQueryBound_eq]
    rfl

/-! ## The numbers -/

theorem rootCap_le : Sound.rootCap ≤ 2 ^ 16 := by decide

/-- **The agreement-set extractor's error fits the end statement's bound**: for `Q ≤ 2^128`
queries, with the transfer to the random-permutation model, at most
`(Q + 2^14) · 2^-125 + 5 (Q + 2^14)² · 2^-256`, as the list decoder's. The new terms, the fresh hit
`2^-127` and the fresh roots `V · rootCap · 2^-256`, are each at most `2^-125`, as are the
transfer's, and `Q + V + 3 ≤ Q + 2^14`. -/
theorem soundnessRpmAS_le_statement {Q : ℕ} (hQ : Q ≤ 2 ^ 128) :
    soundnessErrorAS Q + rpmError (Q + verifierPermCalls) ≤
      (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
        5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
  have hA3 : ((Q + verifierQueries : ℕ) : ℝ≥0∞) + 3 ≤ (Q + 2 ^ 14 : ℝ≥0∞) := by
    have h : Q + verifierQueries + 3 ≤ Q + 2 ^ 14 := by
      rw [Nat.add_assoc]
      exact Nat.add_le_add_left (by rw [verifierQueries_eq]; norm_num) Q
    exact_mod_cast h
  have hHit : (2 : ℝ≥0∞)⁻¹ ^ 127 ≤ (2 : ℝ≥0∞)⁻¹ ^ 125 := Common.inv_two_pow_le_of_le (by norm_num)
  have hRoots : (verifierQueries : ℝ≥0∞) * (Sound.rootCap * (2 ^ 256 : ℝ≥0∞)⁻¹) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 125 := by
    have hn : verifierQueries * Sound.rootCap ≤ 2 ^ 131 := by
      have := rootCap_le
      rw [verifierQueries_eq]
      calc 13708 * Sound.rootCap ≤ 13708 * 2 ^ 16 := Nat.mul_le_mul_left _ this
        _ ≤ 2 ^ 131 := by norm_num
    calc (verifierQueries : ℝ≥0∞) * (Sound.rootCap * (2 ^ 256 : ℝ≥0∞)⁻¹)
        = ((verifierQueries * Sound.rootCap : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
          rw [Nat.cast_mul, mul_assoc, ENNReal.inv_pow]
      _ ≤ (2 : ℝ≥0∞) ^ 131 * (2 : ℝ≥0∞)⁻¹ ^ (131 + 125) := by
          gcongr
          exact_mod_cast hn
      _ = (2 : ℝ≥0∞)⁻¹ ^ 125 := Common.two_pow_mul_inv_pow 131 125
  have hq : Q + verifierPermCalls ≤ 2 ^ 129 :=
    calc Q + verifierPermCalls ≤ 2 ^ 128 + verifierPermCalls := Nat.add_le_add_right hQ _
      _ ≤ 2 ^ 129 := by rw [verifierPermCalls_eq]; norm_num
  have hR : rpmError (Q + verifierPermCalls) ≤ (2 : ℝ≥0∞)⁻¹ ^ 125 :=
    calc rpmError (Q + verifierPermCalls)
        ≤ ((Q + verifierPermCalls : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 379 :=
          Common.sq_div_le_mul_inv_pow (k := 129) 379 hq
      _ ≤ (2 : ℝ≥0∞) ^ 129 * (2 : ℝ≥0∞)⁻¹ ^ (129 + 250) := by
          gcongr
          exact_mod_cast hq
      _ = (2 : ℝ≥0∞)⁻¹ ^ 250 := Common.two_pow_mul_inv_pow 129 250
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 125 := Common.inv_two_pow_le_of_le (by norm_num)
  have h5 : ((5 * (Q + verifierQueries) : ℕ) : ℝ≥0∞) / 2 ^ 256 =
      5 * ((Q + verifierQueries : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
    rw [Nat.cast_mul, div_eq_mul_inv, ENNReal.inv_pow, Nat.cast_ofNat]
  unfold soundnessErrorAS
  rw [h5]
  calc ((Q + verifierQueries : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 125 +
          5 * ((Q + verifierQueries : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 256) +
        (2 : ℝ≥0∞)⁻¹ ^ 127 + (verifierQueries : ℝ≥0∞) * (Sound.rootCap * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        rpmError (Q + verifierPermCalls)
      = ((Q + verifierQueries : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
          5 * ((Q + verifierQueries : ℕ) : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 +
          ((2 : ℝ≥0∞)⁻¹ ^ 127 + (verifierQueries : ℝ≥0∞) * (Sound.rootCap * (2 ^ 256 : ℝ≥0∞)⁻¹) +
            rpmError (Q + verifierPermCalls)) := by ring
    _ ≤ ((Q + verifierQueries : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
          5 * ((Q + verifierQueries : ℕ) : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 +
          ((2 : ℝ≥0∞)⁻¹ ^ 125 + (2 : ℝ≥0∞)⁻¹ ^ 125 + (2 : ℝ≥0∞)⁻¹ ^ 125) :=
        add_le_add le_rfl (add_le_add (add_le_add hHit hRoots) hR)
    _ = (((Q + verifierQueries : ℕ) : ℝ≥0∞) + 3) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
          5 * ((Q + verifierQueries : ℕ) : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 := by ring
    _ ≤ (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
          5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
        have hA : ((Q + verifierQueries : ℕ) : ℝ≥0∞) ≤ (Q + 2 ^ 14 : ℝ≥0∞) := le_self_add.trans hA3
        gcongr

end
end LeanVM
