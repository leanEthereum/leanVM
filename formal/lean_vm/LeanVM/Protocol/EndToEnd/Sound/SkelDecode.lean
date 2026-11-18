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

theorem ret' (a : α) (g : α → γ) (c : γ) (h : g a = c) : DecP (.ret a) g fun _ ↦ some c :=
  h ▸ ret a g

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
      obtain ⟨rfl, rfl⟩ := after_ret_eq hret
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
    obtain ⟨rfl, rfl⟩ := after_ret_eq ha
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

theorem dec_liftOption {α : Type} (o : Option α) : DecP (Verifier.liftOption o) id fun _ ↦ o := by
  intro h a ha
  cases o with
  | none =>
    exfalso
    rcases h with _ | ⟨e, h⟩ <;> simp [Verifier.liftOption, VerifierProgram.after] at ha
  | some b =>
    have hb : (VerifierProgram.ret b : VerifierProgram α).after h = some (.ret a) := ha
    obtain ⟨-, rfl⟩ := after_ret_eq hb
    rfl

/-- A level's high part read off its rest's history: after the commitment. -/
def decHigh (fold : ℕ) (h : List Ev) : Option (List E) :=
  ((h.drop 1).take fold).mapM Ev.readVal

theorem dec_midTailPre (logN index : ℕ) (level next : Whir.Level) (s : WhirState)
    (rounds : List FoldRound) :
    DecP (midTailPre logN index level next s rounds) Prod.fst (decHigh level.fold) := by
  unfold midTailPre midTailC decHigh
  simp only [VerifierProgram.bind_eq]
  refine DecP.congr (DecP.drop (skel_readCommitment _ _) fun _ _ ↦
    DecP.bind (skel_readScalars _) (dec_readScalars _) (d₂ := fun high _ ↦ some high)
      fun high _ ↦ DecP.drop (skel_grindProofOfWork _) fun _ _ ↦
      DecP.drop (skel_sampleChallenges _) fun _ _ ↦ DecP.drop skel_readScalar fun _ _ ↦
      DecP.drop (skel_grindProofOfWork _) fun _ _ ↦ DecP.drop (skel_sampleQueries _ _) fun _ _ ↦
      DecP.drop skel_sampleChallenge fun _ _ ↦ DecP.drop (skel_queryOpenings _ _) fun _ _ ↦
      DecP.ret' _ Prod.fst high rfl) fun h ↦ ?_
  simp only [List.length_singleton, List.length_replicate]
  rcases ((h.drop 1).take level.fold).mapM Ev.readVal <;> rfl

theorem dec_finCut (logN index : ℕ) (level : Whir.Level) (s : WhirState)
    (rounds : List FoldRound) :
    DecP (finCut logN index level s rounds) id fun h ↦
      ((h.take (2 ^ (logN - s.alphas.length) + level.fold)).mapM Ev.readVal).map
        (WhirTrace.final rounds) := by
  unfold finCut
  simp only [VerifierProgram.bind_eq]
  refine DecP.congr (DecP.bind (skel_readScalars _) (dec_readScalars _)
    (d₂ := fun folded _ ↦ some (WhirTrace.final rounds folded)) fun _ _ ↦ DecP.ret _ id)
    fun h ↦ ?_
  simp only [List.length_replicate]
  rcases (h.take (2 ^ (logN - s.alphas.length) + level.fold)).mapM Ev.readVal <;> rfl

/-- **The cut levels' trace read off their history**, `A` the folds made before them. -/
def decLevels (logN : ℕ) : ℕ → List Whir.Level → List Ev → Option WhirTrace
  | _, [], _ => none
  | A, [level], h =>
    (decRounds level.fold (h.take (skFoldRounds level.fold).length)).bind fun rounds ↦
      (((h.drop (skFoldRounds level.fold).length).take
        (2 ^ (logN - (A + level.fold)) + level.fold)).mapM Ev.readVal).map (WhirTrace.final rounds)
  | A, level :: next :: rest, h =>
    (decRounds level.fold (h.take (skFoldRounds level.fold).length)).bind fun rounds ↦
      let h' := h.drop (skFoldRounds level.fold).length
      let Lm := (skMidTail logN (A + level.fold) level next).length
      (decHigh level.fold (h'.take Lm)).bind fun high ↦
        (decLevels logN (A + level.fold) (next :: rest) ((h'.drop Lm).take
          (skLevels logN (A + level.fold) (next :: rest)).length)).map fun tr ↦
          WhirTrace.mid rounds high tr

theorem dec_whirLevelsGF (logN : ℕ) : ∀ (index : ℕ) (levels : List Whir.Level) (s : WhirState)
    (A : ℕ), s.alphas.length = A →
    DecP (whirLevelsGF logN (finCut logN) index levels s) id (decLevels logN A levels)
  | _, [], _, _, _ => fun h a ha ↦ by
    rcases h with _ | ⟨e, h⟩ <;> simp [whirLevelsGF, VerifierProgram.after] at ha
  | index, [level], s, A, hA => by
    simp only [whirLevelsGF, VerifierProgram.bind_eq]
    refine DecP.congr (DecP.bind (skel_foldRounds level.fold s) (dec_foldRounds level.fold s)
      (d₂ := fun rounds h ↦ ((h.take (2 ^ (logN - (A + level.fold)) + level.fold)).mapM
        Ev.readVal).map (WhirTrace.final rounds)) fun r hr ↦ ?_) fun h ↦ rfl
    have := dec_finCut logN index level r.1 r.2
    rwa [hr, hA] at this
  | index, level :: next :: rest, s, A, hA => by
    simp only [whirLevelsGF, VerifierProgram.bind_eq]
    rw [show (fun r : WhirState × List FoldRound ↦ midTailC logN index level next (fun high s' ↦
        (whirLevelsGF logN (finCut logN) (index + 1) (next :: rest) s').bind fun tr ↦
          VerifierProgram.ret (WhirTrace.mid r.2 high tr)) r.1 r.2) =
        fun r ↦ (midTailPre logN index level next r.1 r.2).bind fun p ↦
          (whirLevelsGF logN (finCut logN) (index + 1) (next :: rest) p.2).bind fun tr ↦
            VerifierProgram.ret (WhirTrace.mid r.2 p.1 tr) from
      funext fun r ↦ midTailC_eq_pre _ _ _ _ _ _ _]
    refine DecP.congr (DecP.bind (skel_foldRounds level.fold s) (dec_foldRounds level.fold s)
      (d₂ := fun rounds h' ↦
        (decHigh level.fold (h'.take (skMidTail logN (A + level.fold) level next).length)).bind
          fun high ↦ (decLevels logN (A + level.fold) (next :: rest)
            ((h'.drop (skMidTail logN (A + level.fold) level next).length).take
              (skLevels logN (A + level.fold) (next :: rest)).length)).map fun tr ↦
            WhirTrace.mid rounds high tr) fun r hr ↦ ?_) fun h ↦ rfl
    have hr' : r.1.alphas.length = A + level.fold := by rw [hr, hA]
    refine DecP.congr (DecP.bind ((skel_midTailPre logN index level next r.1 r.2).mono
        (sk' := skMidTail logN (A + level.fold) level next) (by rw [hr']) fun _ h ↦ h)
      (dec_midTailPre logN index level next r.1 r.2)
      (d₂ := fun high h'' ↦ (decLevels logN (A + level.fold) (next :: rest)
        (h''.take (skLevels logN (A + level.fold) (next :: rest)).length)).map fun tr ↦
          WhirTrace.mid r.2 high tr) fun p hp ↦ ?_) fun h ↦ rfl
    have hp' : p.2.alphas.length = A + level.fold := by rw [hp, hr']
    refine DecP.congr (DecP.bind ((skel_whirLevelsGF logN (index + 1) (next :: rest) p.2).mono
        (sk' := skLevels logN (A + level.fold) (next :: rest)) (by rw [hp']) fun _ h ↦ h)
      (dec_whirLevelsGF logN (index + 1) (next :: rest) p.2 (A + level.fold) hp')
      (d₂ := fun tr _ ↦ some (WhirTrace.mid r.2 p.1 tr))
      fun tr _ ↦ DecP.ret' _ id _ rfl) fun h ↦ ?_
    rcases decLevels logN (A + level.fold) (next :: rest)
      (h.take (skLevels logN (A + level.fold) (next :: rest)).length) <;> rfl

/-! ## The cut verifier -/

/-- The cut opening's trace, read off the history after its batching challenge. -/
def decWhirCut (logN ρ : ℕ) (h : List Ev) : Option WhirTrace :=
  (Whir.ladder logN ρ).bind fun config ↦ decLevels logN 0 config h

theorem dec_verifyStackedOpeningCut (stackLog ρ : ℕ) (claims : List StackClaim) :
    DecP (verifyStackedOpeningCut stackLog ρ claims) id fun h ↦ decWhirCut stackLog ρ (h.drop 1) := by
  unfold verifyStackedOpeningCut verifyWhirCut
  simp only [VerifierProgram.bind_eq]
  refine DecP.congr (DecP.drop (skel_require _) fun _ _ ↦ DecP.drop skel_sampleChallenge
    fun _ _ ↦ DecP.bind (skel_liftOption _) (dec_liftOption _)
      (d₂ := fun config h ↦ decLevels stackLog 0 config h)
      fun config _ ↦ dec_whirLevelsGF stackLog 0 config _ 0 rfl) fun h ↦ ?_
  simp [decWhirCut]

/-- The skeleton of the cut body before the opening's trace. -/
def skBodyHead (layout : Verifier.Layout) (ρ : ℕ) : List Op :=
  skCommitStack layout.stackLog ρ ++ skOod layout.stackLog ++ skFront layout ++ skRing ++ [.sample]

/-- The cut body's trace, read off its history. -/
def decBody (layout : Verifier.Layout) (ρ : ℕ) (h : List Ev) : Option WhirTrace :=
  decWhirCut layout.stackLog ρ (h.drop (skBodyHead layout ρ).length)

theorem dec_veBodyCut (pd : Digest) (layout : Verifier.Layout) (ρ : ℕ) :
    DecP (veBodyCut computedBytecodeValue pd layout ρ) id (decBody layout ρ) := by
  unfold veBodyCut
  simp only [VerifierProgram.bind_eq]
  refine DecP.congr (DecP.drop (skel_commitStack _ _) fun _ _ ↦ DecP.drop (skel_readOod _)
    fun _ _ ↦ DecP.drop (skel_frontProg layout pd) fun _ _ ↦ DecP.drop (skel_ringSwitch _ _)
    fun _ _ ↦ dec_verifyStackedOpeningCut _ _ _) fun h ↦ ?_
  simp only [decBody, skBodyHead, List.drop_drop, List.length_append, List.length_singleton]

/-- The announced sizes, read off their history. -/
def decSizes (bytecode : List K) (h : List Ev) : Option (Verifier.Layout × ℕ) :=
  (h.mapM Ev.readVal).bind (sizesOf bytecode)

theorem dec_readAnnouncedSizes (bytecode : List K) :
    DecP (readAnnouncedSizes bytecode) id (fun h ↦ decSizes bytecode (h.take skSizes.length)) := by
  rw [readAnnouncedSizes_eq]
  simp only [VerifierProgram.bind_eq]
  refine DecP.congr (DecP.bind (skel_readScalars _) (dec_readScalars _)
    (d₂ := fun xs _ ↦ sizesOf bytecode xs) fun xs _ ↦ dec_liftOption _) fun h ↦ ?_
  simp [decSizes, skSizes]

/-- **The cut verifier's value read off its history**: the announced sizes, then the body's trace. -/
def decProgram (bytecode : List K) (h : List Ev) :
    Option (Bool × ((Verifier.Layout × ℕ) × WhirTrace)) :=
  (decSizes bytecode (h.take skSizes.length)).bind fun a ↦
    (decBody a.1 a.2 ((h.drop skSizes.length).take (skBody a.1 a.2).length)).map fun tr ↦
      (true, (a, tr))

theorem dec_leanVmProgramCut (bytecode : List K) (pd : Digest) :
    DecP (leanVmProgramCut bytecode pd) id (decProgram bytecode) := by
  unfold leanVmProgramCut verifyExecutionClaimsCut
  rw [VerifierProgram.bind_assoc]
  refine DecP.congr (DecP.bind (skel_readAnnouncedSizes bytecode)
    (dec_readAnnouncedSizes bytecode)
    (d₂ := fun a h ↦ (decBody a.1 a.2 (h.take (skBody a.1 a.2).length)).map fun tr ↦
      (true, (a, tr))) fun a _ ↦ ?_) fun h ↦ ?_
  · rw [VerifierProgram.bind_assoc]
    refine DecP.congr (DecP.bind (skel_veBodyCut pd a.1 a.2) (dec_veBodyCut pd a.1 a.2)
      (d₂ := fun tr _ ↦ some (true, (a, tr))) fun tr _ ↦ ?_) fun h ↦ ?_
    · simp only [VerifierProgram.ret_bind]
      exact DecP.ret' _ id _ rfl
    · simp only [id]
      rcases hd : decBody a.1 a.2 (h.take (skBody a.1 a.2).length) <;> simp
  · simp only [decProgram, List.take_take, min_self]

end
end LeanVM.Protocol.EndToEnd.Sound
