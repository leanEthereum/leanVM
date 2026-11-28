/-
  LeanVM.Protocol.Relation.Runs

  The extracted history of an accepted run of the compiled verifier, as a run of the program.
-/

module

public import LeanVM.Protocol.Compile.Rom.History
import LeanVM.Protocol.Compile.Rom.Extract

/-!
# Runs of the compiled verifier

`xrun_after`: the extracted history of a compiled run that returns `a` is a history of the program
that returns `a`, with every commitment's word well shaped (from tag `formal-bus-archive`,
`EndToEnd/Sound/Runs.lean`, with the packed messages); `after_extractedHistory`: hence for an
accepted proof. A packed draw over `Option` gives the challenges asked for
(`length_samplesPacked_opt`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom

@[expose] public section

/-- A packed squeeze with enough fuel gives the challenges asked for, over `Option`. -/
theorem length_squeezePackedChunks_opt (F : KeccakState → Option KeccakState) :
    ∀ (fuel : ℕ) (sponge : Sponge) (missing : ℕ), missing ≤ fuel → ∀ r,
      squeezePackedChunks F fuel sponge missing = some r → r.1.length = missing
  | 0, _, missing, h, r, hr => by
    obtain rfl : missing = 0 := by omega
    simp only [squeezePackedChunks, pure, Option.some.injEq] at hr
    subst hr; rfl
  | _ + 1, _, 0, _, r, hr => by
    simp only [squeezePackedChunks, pure, Option.some.injEq] at hr
    subst hr; rfl
  | fuel + 1, sponge, missing + 1, h, r, hr => by
    simp only [squeezePackedChunks, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hr
    obtain ⟨sp, -, r', hr', rfl⟩ := hr
    rw [List.length_append, List.length_map, List.length_range,
      length_squeezePackedChunks_opt F fuel _ _ (by omega) r' hr']
    omega

/-- **A packed draw gives the challenges asked for**, over `Option`. -/
theorem length_samplesPacked_opt (F : KeccakState → Option KeccakState) (sponge : Sponge) (n : ℕ)
    {r : List E × Sponge} (hr : samplesPacked F sponge n = some r) : r.1.length = n := by
  unfold samplesPacked at hr
  rcases n with _ | c
  · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    simpa using length_squeezePackedChunks_opt F _ _ _ le_rfl r' hr'
  · rcases hg : sponge.ground with _ | g
    · simp only [hg, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hr
      obtain ⟨r', hr', rfl⟩ := hr
      have := length_squeezePackedChunks_opt F _ _ _ le_rfl r' hr'
      simp only [List.length_nil, Nat.sub_zero] at this
      simp [this]
    · simp only [hg, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hr
      obtain ⟨r', hr', rfl⟩ := hr
      have := length_squeezePackedChunks_opt F _ _ _ le_rfl r' hr'
      simp only [List.length_cons, List.length_map, List.length_take, List.length_range] at this
      simp only [List.length_append, List.length_cons, List.length_map, List.length_take,
        List.length_range, this]
      omega

section XRun

variable (H : Bytes → Option Digest) (F : KeccakState → Option KeccakState)

/-- **The extracted history of a compiled run is a run of the program**: it extends the
starting history by a history along which the program returns the run's value, and every
commitment in it holds a well-shaped word. -/
theorem xrun_after {α : Type} :
    ∀ (p : VerifierProgram α) (s : VerifierProgramState) (h : List Ev) {a : α} {s' :
        VerifierProgramState} {hist : List Ev},
      xrun H F p s h = some (a, s', hist) →
        ∃ l, hist = h ++ l ∧ p.after l = some (.ret a) ∧
          ∀ ht w W, Ev.commit ht w W ∈ l → WellShaped w W
  | .ret a, s, h, _, _, _, hr => by
    simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -, rfl⟩ := hr
    exact ⟨[], by simp, rfl, by simp⟩
  | .fail, s, h, _, _, _, hr => by simp [xrun] at hr
  | .read k, s, h, _, _, _, hr => by
    simp only [xrun] at hr
    split at hr
    · simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨_, _, hr⟩ := hr
      obtain ⟨l, rfl, hl, hw⟩ := xrun_after _ _ _ hr
      refine ⟨_ :: l, List.append_assoc _ _ _, by simpa [VerifierProgram.after] using hl, ?_⟩
      intro ht w W hm
      simp only [List.mem_cons, reduceCtorEq, false_or] at hm
      exact hw _ _ _ hm
    · simp at hr
  | .sample k, s, h, _, _, _, hr => by
    simp only [xrun, Option.bind_eq_some_iff] at hr
    obtain ⟨_, _, hr⟩ := hr
    obtain ⟨l, rfl, hl, hw⟩ := xrun_after _ _ _ hr
    refine ⟨_ :: l, List.append_assoc _ _ _, by simpa [VerifierProgram.after] using hl, ?_⟩
    intro ht w W hm
    simp only [List.mem_cons, reduceCtorEq, false_or] at hm
    exact hw _ _ _ hm
  | .readPacked n k, s, h, _, _, _, hr => by
    simp only [xrun] at hr
    split at hr
    · next hc =>
      simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨_, _, hr⟩ := hr
      obtain ⟨l, rfl, hl, hw⟩ := xrun_after _ _ _ hr
      refine ⟨_ :: l, List.append_assoc _ _ _, ?_, ?_⟩
      · simp only [VerifierProgram.after, List.length_take, Nat.min_eq_left hc.2, ↓reduceIte]
        exact hl
      · intro ht w W hm
        simp only [List.mem_cons, reduceCtorEq, false_or] at hm
        exact hw _ _ _ hm
    · simp at hr
  | .samplePacked n k, s, h, _, _, _, hr => by
    simp only [xrun, Option.bind_eq_some_iff] at hr
    obtain ⟨r, hr0, hr⟩ := hr
    obtain ⟨l, rfl, hl, hw⟩ := xrun_after _ _ _ hr
    refine ⟨_ :: l, List.append_assoc _ _ _, ?_, ?_⟩
    · simp only [VerifierProgram.after, length_samplesPacked_opt F _ _ hr0, ↓reduceIte]
      exact hl
    · intro ht w W hm
      simp only [List.mem_cons, reduceCtorEq, false_or] at hm
      exact hw _ _ _ hm
  | .grind bits k, s, h, _, _, _, hr => by
    simp only [xrun] at hr
    split at hr
    · simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨_, _, hr⟩ := hr
      split at hr
      · obtain ⟨l, rfl, hl, hw⟩ := xrun_after _ _ _ hr
        refine ⟨_ :: l, List.append_assoc _ _ _, by simpa [VerifierProgram.after] using hl, ?_⟩
        intro ht w W hm
        simp only [List.mem_cons, reduceCtorEq, false_or] at hm
        exact hw _ _ _ hm
      · simp at hr
    · simp at hr
  | .commit height width k, s, h, _, _, _, hr => by
    simp only [xrun] at hr
    split at hr
    · simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨_, _, _, _, hr⟩ := hr
      obtain ⟨l, rfl, hl, hw⟩ := xrun_after _ _ _ hr
      refine ⟨_ :: l, List.append_assoc _ _ _, by simpa [VerifierProgram.after] using hl, ?_⟩
      intro ht w W hm
      rcases List.mem_cons.1 hm with he | hm
      · simp only [Ev.commit.injEq] at he
        obtain ⟨-, rfl, rfl⟩ := he
        exact wellShaped_extract _ _ _ _
      · exact hw _ _ _ hm
    · simp at hr
  | .query i ps k, s, h, _, _, _, hr => by
    simp only [xrun] at hr
    split at hr
    · split at hr
      · obtain ⟨l, rfl, hl, hw⟩ := xrun_after _ _ _ hr
        refine ⟨_ :: l, List.append_assoc _ _ _, by simpa [VerifierProgram.after] using hl, ?_⟩
        intro ht w W hm
        simp only [List.mem_cons, reduceCtorEq, false_or] at hm
        exact hw _ _ _ hm
      · simp at hr
    · simp at hr

/-- **An accepted proof's extracted history is an accepting history of the program**, whose
commitments hold well-shaped words. -/
theorem after_extractedHistory {σ : Seed} {P : VerifierProgram Bool} {π : Proof}
    (hv : Rom.verify H F σ P π = some true) :
    P.after (extractedHistory H F σ P π) = some (.ret true) ∧
      ∀ ht w W, Ev.commit ht w W ∈ extractedHistory H F σ P π → WellShaped w W := by
  obtain ⟨seed, s, -, hx⟩ := xrun_of_verify hv
  obtain ⟨l, hl, ha, hw⟩ := xrun_after H F P _ [] hx
  simp only [List.nil_append] at hl
  rw [hl]
  exact ⟨ha, hw⟩

end XRun

end

end LeanVM.Protocol.Relation
