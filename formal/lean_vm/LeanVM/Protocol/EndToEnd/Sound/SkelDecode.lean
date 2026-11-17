/-
  LeanVM.Protocol.EndToEnd.Sound.SkelDecode

  Reading a projection of a program's return value off a history it returns on, through its
  skeleton: the opening's trace, without the verifier's arithmetic.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.SkelWhir

/-!
# Decoders

`DecP p g d`: on every history `h` along which `p` returns `a`, `d h = some (g a)`: the decoder `d`
reads the projection `g` of the value off the history. Sequencing splits the history at the first
part's skeleton (`DecP.bind`), or drops the first part where the second part's projection does not
depend on its value (`DecP.drop`). The cut opening's trace is read off its history
(`dec_whirLevelsGF`): each fold round's two challenges, each level's high part, the final
polynomial; the running claims, the verifier's arithmetic, are never computed.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound

@[expose] public section

/-- **`d` reads the projection `g` of `p`'s value** off every history `p` returns on. -/
def DecP {α γ : Type} (p : VerifierProgram α) (g : α → γ) (d : List Ev → Option γ) : Prop :=
  ∀ h a, p.after h = some (.ret a) → d h = some (g a)

namespace DecP

variable {α β γ δ : Type}

theorem ret (a : α) (g : α → γ) : DecP (.ret a) g fun _ ↦ some (g a) := by
  intro h b hb
  rcases h with _ | ⟨e, h⟩
  · simp only [VerifierProgram.after, Option.some.injEq, VerifierProgram.ret.injEq] at hb
    rw [hb]
  · simp [VerifierProgram.after] at hb

/-- Sequencing, the history split at the first part's skeleton. -/
theorem bind {p : VerifierProgram α} {f : α → VerifierProgram β} {sk : List Op} {Q : α → Prop}
    {g₁ : α → γ} {g₂ : β → δ} {d₁ : List Ev → Option γ} {d₂ : γ → List Ev → Option δ}
    (hs : SkelP p sk Q) (hp : DecP p g₁ d₁) (hf : ∀ a, Q a → DecP (f a) g₂ (d₂ (g₁ a))) :
    DecP (p.bind f) g₂ fun h ↦ (d₁ (h.take sk.length)).bind fun x ↦ d₂ x (h.drop sk.length) := by
  intro h b hb
  obtain ⟨a, h₁, h₂, rfl, ha, hfa⟩ := after_bind_ret hb
  have hl : h₁.length = sk.length := by rw [← hs.1 h₁ a ha, List.length_map]
  dsimp only
  rw [List.take_left' hl, List.drop_left' hl, hp h₁ a ha, Option.bind_some]
  exact hf a (hs.2 a (returns_of_after ha)) h₂ b hfa

/-- Sequencing, the second part's projection read without the first's value. -/
theorem drop {p : VerifierProgram α} {f : α → VerifierProgram β} {sk : List Op} {Q : α → Prop}
    {g : β → δ} {d : List Ev → Option δ} (hs : SkelP p sk Q) (hf : ∀ a, Q a → DecP (f a) g d) :
    DecP (p.bind f) g fun h ↦ d (h.drop sk.length) := by
  intro h b hb
  obtain ⟨a, h₁, h₂, rfl, ha, hfa⟩ := after_bind_ret hb
  have hl : h₁.length = sk.length := by rw [← hs.1 h₁ a ha, List.length_map]
  dsimp only
  rw [List.drop_left' hl]
  exact hf a (hs.2 a (returns_of_after ha)) h₂ b hfa

theorem congr {p : VerifierProgram α} {g : α → γ} {d d' : List Ev → Option γ} (hp : DecP p g d)
    (e : ∀ h, d h = d' h) : DecP p g d' := fun h a ha ↦ (e h).symm.trans (hp h a ha)

end DecP

/-! ## Leaves -/

/-- The scalar a read event carries. -/
def Ev.readVal : Ev → Option E
  | .read x => some x
  | _ => none

/-- The challenge a sample event carries. -/
def Ev.sampleVal : Ev → Option E
  | .sample c => some c
  | _ => none

theorem dec_readScalars : ∀ n, DecP (VerifierProgram.readScalars n) id fun h ↦ h.mapM Ev.readVal
  | 0 => fun h a ha ↦ by
    rcases h with _ | ⟨e, h⟩
    · simp only [VerifierProgram.readScalars, VerifierProgram.after, Option.some.injEq,
        VerifierProgram.ret.injEq] at ha
      rw [← ha]; rfl
    · simp [VerifierProgram.readScalars, VerifierProgram.after] at ha
  | n + 1 => by
    unfold VerifierProgram.readScalars
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    intro h a ha
    rcases h with _ | ⟨e, h⟩
    · simp [VerifierProgram.readScalar, VerifierProgram.bind, VerifierProgram.after] at ha
    · cases e <;> simp only [VerifierProgram.readScalar, VerifierProgram.bind,
        VerifierProgram.after, reduceCtorEq] at ha
      rename_i x
      obtain ⟨xs, h₁, h₂, rfl, hxs, hret⟩ := after_bind_ret ha
      obtain ⟨rfl, rfl⟩ := after_ret_eq' hret
      rw [List.append_nil]
      have := dec_readScalars n h₁ xs hxs
      simp only [id] at this
      simp only [List.mapM_cons, Ev.readVal, this, id]
      rfl

theorem dec_sampleChallenge : DecP VerifierProgram.sampleChallenge id fun h ↦
    h.head?.bind Ev.sampleVal := fun h a ha ↦ by
  rcases h with _ | ⟨e, h⟩
  · simp [VerifierProgram.sampleChallenge, VerifierProgram.after] at ha
  · cases e <;> simp only [VerifierProgram.sampleChallenge, VerifierProgram.after,
      reduceCtorEq] at ha
    rename_i c
    obtain ⟨rfl, rfl⟩ := after_ret_eq' ha
    rfl

/-! ## The opening's trace -/

/-- A fold round's challenges, read off its history: after its reads and its proof of work. -/
def decRound (h : List Ev) : Option FoldRound :=
  let h' := h.drop (4 + (skGrind Whir.foldGrindingBits).length)
  (h'.head?.bind Ev.sampleVal).bind fun alpha ↦
    ((h'.drop 1).head?.bind Ev.sampleVal).map fun beta ↦ ⟨alpha, beta⟩

theorem head?_take_one (h : List Ev) : (h.take 1).head? = h.head? := by
  rcases h with _ | ⟨e, t⟩ <;> rfl

/-- A sample then a return: the projection of the value at the sample's challenge. -/
theorem dec_sample_ret {β γ : Type} (k : E → β) (g : β → γ) :
    DecP (VerifierProgram.sampleChallenge.bind fun c ↦ VerifierProgram.ret (k c)) g
      fun h ↦ (h.head?.bind Ev.sampleVal).map fun c ↦ g (k c) := by
  refine DecP.congr (DecP.bind skel_sampleChallenge dec_sampleChallenge
    (d₂ := fun c _ ↦ some (g (k c))) fun c _ ↦ DecP.ret (k c) g) fun h ↦ ?_
  simp only [List.length_singleton, head?_take_one]
  rcases h.head?.bind Ev.sampleVal <;> rfl

theorem dec_foldRound (s : WhirState) : DecP (foldRound s) Prod.snd decRound := by
  unfold foldRound decRound
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine DecP.congr (DecP.drop skel_readScalar fun _ _ ↦ DecP.drop skel_readScalar fun _ _ ↦
    DecP.drop skel_readScalar fun _ _ ↦ DecP.drop skel_readScalar fun _ _ ↦
    DecP.drop (skel_grindProofOfWork _) fun _ _ ↦
    DecP.bind skel_sampleChallenge dec_sampleChallenge
      (d₂ := fun alpha h ↦ (h.head?.bind Ev.sampleVal).map fun beta ↦ (⟨alpha, beta⟩ : FoldRound))
      fun alpha _ ↦ dec_sample_ret _ Prod.snd) fun h ↦ ?_
  simp only [List.length_singleton, head?_take_one, List.drop_drop]

/-- The fold rounds read off a fold-rounds history. -/
def decRounds : ℕ → List Ev → Option (List FoldRound)
  | 0, _ => some []
  | n + 1, h => (decRound (h.take skFoldRound.length)).bind fun r ↦
      (decRounds n ((h.drop skFoldRound.length).take (skFoldRounds n).length)).map fun rs ↦ r :: rs

theorem dec_foldRounds : ∀ (n : ℕ) (s : WhirState),
    DecP (foldRounds n s) Prod.snd (decRounds n)
  | 0, s => DecP.ret _ _
  | n + 1, s => by
    unfold foldRounds
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine DecP.congr (DecP.bind (skel_foldRound s) (dec_foldRound s)
      (d₂ := fun r h ↦ (decRounds n (h.take (skFoldRounds n).length)).map fun rs ↦ r :: rs)
      fun r _ ↦ DecP.congr (DecP.bind (skel_foldRounds n r.1) (dec_foldRounds n r.1)
        (d₂ := fun rs _ ↦ some (r.2 :: rs)) fun r' _ ↦ DecP.ret _ Prod.snd) fun h ↦ ?_) fun h ↦ ?_
    · rcases decRounds n (h.take (skFoldRounds n).length) <;> rfl
    · rfl

end
end LeanVM.Protocol.EndToEnd.Sound
