/-
  LeanVM.Protocol.EndToEnd.Sound.SkelPairs

  The skeleton's replay and the decoders on events reduced to the values they carry.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.SkelDecode

/-!
# Replay and decoding on pairs

The decoders read an event only through the scalar a read carries and the challenge a sample
carries (`Ev.readVal`, `Ev.sampleVal`). `skelReplayP` records each event as that pair
(`Ev.pair`), with no committed word, and the decoders on pairs (`decSizesP`, `decBodyP`) are the
decoders on the events (`skelReplayP_eq`, `decSizes_eq`, `decBody_eq`).
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound

@[expose] public section

/-- An event's values: the scalar of a read, the challenge of a sample. -/
abbrev EvP : Type := Option E × Option E

/-- The values an event carries. -/
def Ev.pair (e : Ev) : EvP := (Ev.readVal e, Ev.sampleVal e)

section Replay

variable (F : KeccakState → Option KeccakState)

/-- **The replay of a skeleton, on pairs.** -/
def skelReplayP : List Op → VerifierProgramState → Option (List EvP × VerifierProgramState)
  | [], s => some ([], s)
  | .read :: sk, s => match s.stream, s.sponge.ground with
    | x :: xs, none => (absorb (m := Option) F s.sponge x dsObserve).bind fun sp ↦
      (skelReplayP sk { s with sponge := sp, stream := xs }).map fun r ↦ ((some x, none) :: r.1, r.2)
    | _, _ => none
  | .sample :: sk, s => (squeeze (m := Option) F s.sponge).bind fun c ↦
      (skelReplayP sk { s with sponge := c.2 }).map fun r ↦ ((none, some c.1) :: r.1, r.2)
  | .grind _ :: sk, s => match s.stream, s.sponge.ground with
    | n :: xs, none => (absorbNonce (m := Option) F s.sponge n).bind fun c ↦
      (skelReplayP sk { s with sponge := c.2, stream := xs }).map fun r ↦ ((none, none) :: r.1, r.2)
    | _, _ => none
  | .commit height width :: sk, s => match s.stream, s.sponge.ground with
    | x0 :: x1 :: xs, none => (absorb (m := Option) F s.sponge x0 dsObserve).bind fun sp0 ↦
      (absorb (m := Option) F sp0 x1 dsObserve).bind fun sp1 ↦
      let roots := s.roots ++ [(KeccakHash.digestFromHalves (x0, x1), height, width)]
      (skelReplayP sk { s with sponge := sp1, stream := xs, roots := roots }).map fun r ↦
        ((none, none) :: r.1, r.2)
    | _, _ => none
  | .query :: sk, s => match s.openings with
    | _ :: rest => (skelReplayP sk { s with openings := rest }).map fun r ↦ ((none, none) :: r.1, r.2)
    | [] => none

/-- **The replay on pairs is the replay**, its events reduced to their values. -/
theorem skelReplayP_eq : ∀ (sk : List Op) (s : VerifierProgramState),
    skelReplayP F sk s = (skelReplay F sk s).map fun r ↦ (r.1.map Ev.pair, r.2)
  | [], s => rfl
  | op :: sk, ⟨sponge, stream, openings, roots⟩ => by
    cases op with
    | read =>
      rcases stream with _ | ⟨x, xs⟩
      · rfl
      · rcases hg : sponge.ground with _ | g
        · simp only [skelReplayP, skelReplay, hg]
          rcases absorb (m := Option) F sponge x dsObserve with _ | sp
          · rfl
          · simp only [Option.bind_some, skelReplayP_eq sk]
            rcases skelReplay F sk _ with _ | r <;> rfl
        · simp only [skelReplayP, skelReplay, hg, Option.map_none]
    | sample =>
      simp only [skelReplayP, skelReplay]
      rcases squeeze (m := Option) F sponge with _ | c
      · rfl
      · simp only [Option.bind_some, skelReplayP_eq sk]
        rcases skelReplay F sk _ with _ | r <;> rfl
    | grind b =>
      rcases stream with _ | ⟨x, xs⟩
      · rfl
      · rcases hg : sponge.ground with _ | g
        · simp only [skelReplayP, skelReplay, hg]
          rcases absorbNonce (m := Option) F sponge x with _ | c
          · rfl
          · simp only [Option.bind_some, skelReplayP_eq sk]
            rcases skelReplay F sk _ with _ | r <;> rfl
        · simp only [skelReplayP, skelReplay, hg, Option.map_none]
    | commit ht w =>
      rcases stream with _ | ⟨x0, _ | ⟨x1, xs⟩⟩
      · rfl
      · rfl
      · rcases hg : sponge.ground with _ | g
        · simp only [skelReplayP, skelReplay, hg]
          rcases absorb (m := Option) F sponge x0 dsObserve with _ | sp0
          · rfl
          · simp only [Option.bind_some]
            rcases absorb (m := Option) F sp0 x1 dsObserve with _ | sp1
            · rfl
            · simp only [Option.bind_some, skelReplayP_eq sk]
              rcases skelReplay F sk _ with _ | r <;> rfl
        · simp only [skelReplayP, skelReplay, hg, Option.map_none]
    | query =>
      rcases openings with _ | ⟨phase, rest⟩
      · rfl
      · simp only [skelReplayP, skelReplay, skelReplayP_eq sk]
        rcases skelReplay F sk _ with _ | r <;> rfl

end Replay

/-! ## The decoders on pairs -/

/-- A fold round's challenges. -/
def decRoundP (h : List EvP) : Option FoldRound :=
  let h' := h.drop (4 + (skGrind Whir.foldGrindingBits).length)
  (h'.head?.bind (fun p : EvP ↦ p.2)).bind fun alpha ↦
    ((h'.drop 1).head?.bind (fun p : EvP ↦ p.2)).map fun beta ↦ ⟨alpha, beta⟩

/-- The fold rounds. -/
def decRoundsP : ℕ → List EvP → Option (List FoldRound)
  | 0, _ => some []
  | n + 1, h => (decRoundP (h.take skFoldRound.length)).bind fun r ↦
      (decRoundsP n ((h.drop skFoldRound.length).take (skFoldRounds n).length)).map fun rs ↦ r :: rs

/-- A level's high part. -/
def decHighP (fold : ℕ) (h : List EvP) : Option (List E) :=
  ((h.drop 1).take fold).mapM (fun p : EvP ↦ p.1)

/-- The cut levels' trace. -/
def decLevelsP (logN : ℕ) : ℕ → List Whir.Level → List EvP → Option WhirTrace
  | _, [], _ => none
  | A, [level], h =>
    (decRoundsP level.fold (h.take (skFoldRounds level.fold).length)).bind fun rounds ↦
      (((h.drop (skFoldRounds level.fold).length).take
        (2 ^ (logN - (A + level.fold)) + level.fold)).mapM (fun p : EvP ↦ p.1)).map (WhirTrace.final rounds)
  | A, level :: next :: rest, h =>
    (decRoundsP level.fold (h.take (skFoldRounds level.fold).length)).bind fun rounds ↦
      let h' := h.drop (skFoldRounds level.fold).length
      let Lm := (skMidTail logN (A + level.fold) level next).length
      (decHighP level.fold (h'.take Lm)).bind fun high ↦
        (decLevelsP logN (A + level.fold) (next :: rest) ((h'.drop Lm).take
          (skLevels logN (A + level.fold) (next :: rest)).length)).map fun tr ↦
          WhirTrace.mid rounds high tr

/-- The cut opening's trace. -/
def decWhirCutP (logN ρ : ℕ) (h : List EvP) : Option WhirTrace :=
  (Whir.ladder logN ρ).bind fun config ↦ decLevelsP logN 0 config h

/-- The cut body's trace. -/
def decBodyP (layout : Verifier.Layout) (ρ : ℕ) (h : List EvP) : Option WhirTrace :=
  decWhirCutP layout.stackLog ρ (h.drop (skBodyHead layout ρ).length)

/-- The announced sizes. -/
def decSizesP (bytecode : List K) (h : List EvP) : Option (Verifier.Layout × ℕ) :=
  (h.mapM (fun p : EvP ↦ p.1)).bind (sizesOf bytecode)

theorem mapM_fst_pair (h : List Ev) : (h.map Ev.pair).mapM (fun p : EvP ↦ p.1) = h.mapM Ev.readVal := by
  rw [List.mapM_map]
  rfl

theorem decRound_eq (h : List Ev) : decRound h = decRoundP (h.map Ev.pair) := by
  unfold decRound decRoundP
  simp only [← List.map_drop, List.head?_map, Option.bind_map]
  rfl

theorem decRounds_eq : ∀ (n : ℕ) (h : List Ev), decRounds n h = decRoundsP n (h.map Ev.pair)
  | 0, _ => rfl
  | n + 1, h => by
    rw [decRounds, decRoundsP, ← List.map_take, decRound_eq, ← List.map_drop, ← List.map_take,
      decRounds_eq n]

theorem decHigh_eq (fold : ℕ) (h : List Ev) : decHigh fold h = decHighP fold (h.map Ev.pair) := by
  rw [decHigh, decHighP, ← List.map_drop, ← List.map_take, mapM_fst_pair]

theorem decLevels_eq (logN : ℕ) : ∀ (A : ℕ) (levels : List Whir.Level) (h : List Ev),
    decLevels logN A levels h = decLevelsP logN A levels (h.map Ev.pair)
  | _, [], _ => rfl
  | A, [level], h => by
    simp only [decLevels, decLevelsP, ← List.map_take, decRounds_eq, ← List.map_drop,
      mapM_fst_pair]
  | A, level :: next :: rest, h => by
    simp only [decLevels, decLevelsP, ← List.map_take, decRounds_eq, ← List.map_drop, decHigh_eq,
      decLevels_eq logN (A + level.fold)]

theorem decBody_eq (layout : Verifier.Layout) (ρ : ℕ) (h : List Ev) :
    decBody layout ρ h = decBodyP layout ρ (h.map Ev.pair) := by
  unfold decBody decBodyP decWhirCut decWhirCutP
  simp only [← List.map_drop, decLevels_eq]

theorem decSizes_eq (bytecode : List K) (h : List Ev) :
    decSizes bytecode h = decSizesP bytecode (h.map Ev.pair) := by
  rw [decSizes, decSizesP, mapM_fst_pair]

end
end LeanVM.Protocol.EndToEnd.Sound
