/-
  LeanVM.Protocol.EndToEnd.Sound.SkelExtract

  The agreement-set extractor with the verifier's replay driven by its skeleton: it returns what
  the agreement-set extractor returns.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.SkelDecode

/-!
# The extractor over the skeleton

`extractASF` replays the announced sizes' skeleton, reads the layout and the rate off it, replays
the body's skeleton, reads the opening's trace off it, and finishes as `Relation.extractAS` does.
Where the cut verifier's replay returns, the skeleton's replay returns the same state along a
history the decoders read the same value off (`replay_cut_skel`), so wherever `extractAS` returns
an execution, `extractASF` returns it (`extractASF_of_extractAS`). Its replay does none of the
verifier's arithmetic.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound
  LeanVM.Protocol.KeccakHash LeanVM.Protocol.Relation
open LeanVM.Protocol.Whir.Params (after_bind_ret)

@[expose] public section

/-- **The cut verifier's replay, through its skeleton**: where the replay returns, the replay of
the announced sizes' and the body's skeletons returns the same state, along a history the decoder
reads the same value off. -/
theorem replay_cut_skel (F : KeccakState → Option KeccakState) (bytecode : List K)
    (input : PublicInput) {s : VerifierProgramState} {a : Bool × ((Layout × ℕ) × WhirTrace)}
    {s' : VerifierProgramState}
    (h : replayU F (leanVmProgramCut bytecode input) s = some (a, s')) :
    ∃ hist, skelReplay F (skSizes ++ skBody a.2.1.1.lite a.2.1.2) s = some (hist, s') ∧
      decProgram bytecode hist = some a := by
  obtain ⟨hist, hafter, hrep⟩ := skelReplay_of_replayU F _ s h
  refine ⟨hist, ?_, dec_leanVmProgramCut bytecode input hist a hafter⟩
  have hafter' := hafter
  unfold leanVmProgramCut at hafter'
  obtain ⟨a', h₁, h₂, rfl, ha', hbody⟩ := after_bind_ret hafter'
  obtain ⟨tr, h₃, h₄, rfl, htr, hret⟩ := after_bind_ret hbody
  obtain ⟨rfl, rfl⟩ := after_ret_eq hret
  have hs₁ := (skel_readAnnouncedSizes bytecode).1 h₁ a' ha'
  obtain ⟨lm, rows, hb⟩ := (skel_readAnnouncedSizes bytecode).2 a' (Compile.returns_of_after ha')
  have hs₂ := (skel_veBodyCut a'.1 a'.2 input (layoutBounds_of_buildLayout hb).tables_eq).1 h₃ tr htr
  rw [List.append_nil] at hrep
  simp only [List.map_append, hs₁, hs₂] at hrep
  simpa using hrep

/-- **The agreement-set extractor over the skeleton**: the seed; the announced sizes' skeleton,
the layout and the rate read off it; the body's skeleton, the opening's trace read off it; then
the extractor's finish. -/
def extractASF (program : LeanIsaProgram) (input : PublicInput) (H : Bytes → Option Digest)
    (keys : List Bytes) (F : KeccakState → Option KeccakState) (π : Proof) :
    Option (Execution program) :=
  ((leanVmSeed (bytecodeWords program) (publicInputDigest input)).run H F).bind fun seed ↦
  (skelReplay F skSizes (startState π seed)).bind fun r₁ ↦
  (decSizes (bytecodeWords program) r₁.1).bind fun a ↦
  (skelReplay F (skBody a.1.lite a.2) r₁.2).bind fun r₂ ↦
  (decBody a.1.lite a.2 r₂.1).bind fun tr ↦
  finishAS program H keys ((true, (a, tr)), r₂.2)

/-- **Where the agreement-set extractor returns an execution, the extractor over the skeleton
returns it.** -/
theorem extractASF_of_extractAS {program : LeanIsaProgram} {input : PublicInput}
    {H : Bytes → Option Digest} {keys : List Bytes} {F : KeccakState → Option KeccakState}
    {π : Proof} {t : Execution program} (h : extractAS program input H keys F π = some t) :
    extractASF program input H keys F π = some t := by
  unfold extractAS at h
  obtain ⟨seed, hseed, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨a, s'⟩, hr, hfin⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hist, hsk, hdec⟩ := replay_cut_skel F _ _ hr
  rw [skelReplay_append] at hsk
  obtain ⟨⟨h₁, s₁⟩, hr₁, hsk⟩ := Option.bind_eq_some_iff.mp hsk
  obtain ⟨⟨h₂, s₂⟩, hr₂, he⟩ := Option.map_eq_some_iff.mp hsk
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have l₁ := length_skelReplay F _ _ hr₁
  have l₂ := length_skelReplay F _ _ hr₂
  unfold decProgram at hdec
  rw [List.take_left' l₁, List.drop_left' l₁] at hdec
  obtain ⟨a', hs, hdec⟩ := Option.bind_eq_some_iff.mp hdec
  obtain ⟨tr, hb, rfl⟩ := Option.map_eq_some_iff.mp hdec
  rw [← l₂, List.take_length] at hb
  unfold extractASF
  simp only [hseed, Option.bind_some, hr₁, hs, hr₂, hb]
  exact hfin

end
end LeanVM.Protocol.EndToEnd.Sound
