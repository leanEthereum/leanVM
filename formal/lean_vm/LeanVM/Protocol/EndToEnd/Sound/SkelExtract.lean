/-
  LeanVM.Protocol.EndToEnd.Sound.SkelExtract

  The agreement-set extractor with the verifier's replay driven by its skeleton: it returns what
  the computed extractor returns.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.SkelDecode
public import LeanVM.Protocol.EndToEnd.Sound.ExtractorC

/-!
# The extractor over the skeleton

`extractASF` replays the announced sizes' skeleton, reads the layout and the rate off it, replays
the body's skeleton, reads the opening's trace off it, and finishes as `extractASC` does. Where the
cut verifier's replay returns, the skeleton's replay returns the same state along a history the
decoders read the same value off (`replay_cut_skel`), so wherever `extractASC` returns an
execution, `extractASF` returns it (`extractASF_of_extractASC`). Its replay does none of the
verifier's arithmetic.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Sound
  LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.EndToEnd.Complete (publicInputDigest)

@[expose] public section

section

variable (F : KeccakState → Option KeccakState)

theorem skelReplay_append : ∀ (sk₁ sk₂ : List Op) (s : VerifierProgramState),
    skelReplay F (sk₁ ++ sk₂) s = (skelReplay F sk₁ s).bind fun r ↦
      (skelReplay F sk₂ r.2).map fun r' ↦ (r.1 ++ r'.1, r'.2)
  | [], sk₂, s => by
    simp only [List.nil_append, skelReplay, Option.bind_some, List.nil_append]
    rcases skelReplay F sk₂ s <;> rfl
  | op :: sk₁, sk₂, s => by
    cases op with
    | read =>
      simp only [List.cons_append, skelReplay]
      split
      · rcases absorb (m := Option) F s.sponge _ dsObserve with _ | sp
        · rfl
        · simp only [Option.bind_some, skelReplay_append sk₁ sk₂]
          rcases skelReplay F sk₁ _ with _ | r <;> simp [Function.comp_def]
      · rfl
    | sample =>
      simp only [List.cons_append, skelReplay]
      rcases squeeze (m := Option) F s.sponge with _ | c
      · rfl
      · simp only [Option.bind_some, skelReplay_append sk₁ sk₂]
        rcases skelReplay F sk₁ _ with _ | r <;> simp [Function.comp_def]
    | grind b =>
      simp only [List.cons_append, skelReplay]
      split
      · rcases absorbNonce (m := Option) F s.sponge _ with _ | c
        · rfl
        · simp only [Option.bind_some, skelReplay_append sk₁ sk₂]
          rcases skelReplay F sk₁ _ with _ | r <;> simp [Function.comp_def]
      · rfl
    | commit ht w =>
      simp only [List.cons_append, skelReplay]
      split
      · rcases absorb (m := Option) F s.sponge _ dsObserve with _ | sp0
        · rfl
        · simp only [Option.bind_some]
          rcases absorb (m := Option) F sp0 _ dsObserve with _ | sp1
          · rfl
          · simp only [Option.bind_some, skelReplay_append sk₁ sk₂]
            rcases skelReplay F sk₁ _ with _ | r <;> simp [Function.comp_def]
      · rfl
    | query =>
      simp only [List.cons_append, skelReplay]
      split
      · simp only [skelReplay_append sk₁ sk₂]
        rcases skelReplay F sk₁ _ with _ | r <;> simp [Function.comp_def]
      · rfl

theorem length_skelReplay : ∀ (sk : List Op) (s : VerifierProgramState) {h : List Ev}
    {s' : VerifierProgramState}, skelReplay F sk s = some (h, s') → h.length = sk.length
  | [], s, h, s', hr => by
    simp only [skelReplay, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    rfl
  | op :: sk, s, h, s', hr => by
    cases op <;> simp only [skelReplay] at hr <;> (try split at hr) <;>
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, reduceCtorEq, Prod.mk.injEq] at hr <;>
      first
      | (obtain ⟨_, -, r, hr', rfl, rfl⟩ := hr; simp [length_skelReplay sk _ hr'])
      | (obtain ⟨_, -, _, -, r, hr', rfl, rfl⟩ := hr; simp [length_skelReplay sk _ hr'])
      | (obtain ⟨r, hr', rfl, rfl⟩ := hr; simp [length_skelReplay sk _ hr'])

end

/-- **The cut verifier's replay, through its skeleton**: where the replay returns, the replay of
the announced sizes' and the body's skeletons returns the same state, along a history the decoder
reads the same value off. -/
theorem replay_cut_skel (F : KeccakState → Option KeccakState) (bytecode : List K) (pd : Digest)
    {s : VerifierProgramState} {a : Bool × ((Verifier.Layout × ℕ) × WhirTrace)}
    {s' : VerifierProgramState}
    (h : replayU F (leanVmProgramCut bytecode pd) s = some (a, s')) :
    ∃ hist, skelReplay F (skSizes ++ skBody a.2.1.1 a.2.1.2) s = some (hist, s') ∧
      decProgram bytecode hist = some a := by
  obtain ⟨hist, hafter, hrep⟩ := skelReplay_of_replayU F _ s h
  refine ⟨hist, ?_, dec_leanVmProgramCut bytecode pd hist a hafter⟩
  have hafter' := hafter
  unfold leanVmProgramCut at hafter'
  obtain ⟨d, h₁, h₂, rfl, hd, hret⟩ := after_bind_ret hafter'
  obtain ⟨rfl, rfl⟩ := after_ret_eq hret
  unfold verifyExecutionClaimsCut at hd
  obtain ⟨a', h₃, h₄, rfl, ha', hbody⟩ := after_bind_ret hd
  obtain ⟨tr, h₅, h₆, rfl, htr, hret'⟩ := after_bind_ret hbody
  obtain ⟨rfl, rfl⟩ := after_ret_eq hret'
  have hs₁ := (skel_readAnnouncedSizes bytecode).1 h₃ a' ha'
  have hs₂ := (skel_veBodyCut pd a'.1 a'.2).1 h₅ tr htr
  rw [List.append_nil, List.append_nil] at hrep
  simp only [List.map_append, hs₁, hs₂] at hrep
  simpa using hrep

variable {D : NearDecoder} (W : ValsDecoder D)

/-- **The agreement-set extractor over the skeleton**: the seed; the announced sizes' skeleton,
the layout and the rate read off it; the body's skeleton, the opening's trace read off it; then
the extractor's finish. -/
def extractASF (prog : LeanIsaProgram) (input : PublicInput) (H : Bytes → Option Digest)
    (keys : List Bytes) (F : KeccakState → Option KeccakState) (π : Proof) :
    Option (Execution prog) :=
  ((leanVmSeed (bytecodeWords prog) (publicInputDigest input)).run H F).bind fun seed ↦
  (skelReplay F skSizes (startState π seed)).bind fun r₁ ↦
  (decSizes (bytecodeWords prog) r₁.1).bind fun a ↦
  (skelReplay F (skBody a.1 a.2) r₁.2).bind fun r₂ ↦
  (decBody a.1 a.2 r₂.1).bind fun tr ↦
  finishAS W prog input H keys ((true, (a, tr)), r₂.2)

/-- **Where the computed extractor returns an execution, the extractor over the skeleton returns
it.** -/
theorem extractASF_of_extractASC {prog : LeanIsaProgram} {input : PublicInput}
    {H : Bytes → Option Digest} {keys : List Bytes} {F : KeccakState → Option KeccakState}
    {π : Proof} {t : Execution prog} (h : extractASC W prog input H keys F π = some t) :
    extractASF W prog input H keys F π = some t := by
  unfold extractASC at h
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
