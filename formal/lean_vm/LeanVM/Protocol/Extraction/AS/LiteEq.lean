/-
  LeanVM.Protocol.Extraction.AS.LiteEq

  The lite extractor's pieces are the skeleton extractor's: the replay on values, the decoders,
  the announced sizes on the layout's sizes.
-/

module

public import LeanVM.Protocol.Extraction.AS.Lite
public import LeanVM.Protocol.EndToEnd.Sound.SkelExtract

/-!
# The lite extractor's pieces

* `skelReplayP_eq`: the replay on values is the skeleton's replay, each event reduced to its read
  and sampled values (`Ev.pair`);
* `decBodyL_eq`, `decSizesL_eq`: the lite decoders on the values read what the decoders read off
  the history, the layout reduced to its sizes (`Layout.lite`);
* `buildLayoutLite_eq`: `buildLayoutLite` is `buildLayout`'s sizes (`columnKappasL_eq`).
-/

namespace LeanVM.Extraction.AS

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound LeanVM.Protocol.Relation

@[expose] public section

/-- The values an event carries. -/
def Ev.pair (e : Ev) : EvP := (Ev.readVal e, Ev.sampleVal e)

section Replay

variable (F : KeccakState → Option KeccakState)

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
    | readPacked n =>
      have e : (stream.take n).length = n ↔ n ≤ stream.length := by rw [List.length_take]; omega
      simp only [skelReplayP, skelReplay, e]
      split_ifs
      · rcases observePacked (m := Option) F sponge (stream.take n) with _ | sp
        · rfl
        · simp only [Option.bind_some, skelReplayP_eq sk]
          rcases skelReplay F sk _ with _ | r <;> rfl
      · rfl
    | samplePacked n =>
      simp only [skelReplayP, skelReplay]
      rcases samplesPacked (m := Option) F sponge n with _ | c
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

/-! ## The decoders -/

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

theorem decBodyL_eq (lay : LayoutLite) (ρ : ℕ) (h : List Ev) :
    decBody lay ρ h = decBodyL lay ρ (h.map Ev.pair) := by
  unfold decBody decBodyL decWhirCut decWhirCutP
  simp only [← List.map_drop, decLevels_eq]

/-! ## The announced sizes -/

theorem tables_shape : tables.map (fun t ↦ (t.width, t.opcode)) =
    [(7, 0), (9, 1), (5, 2), (10, 3), (14, 4), (68, 5)] := by decide +kernel

theorem columnKappasL_eq (logMemory : ℕ) (tableLogHeights : List ℕ) :
    columnKappas tables logMemory tableLogHeights = columnKappasL logMemory tableLogHeights := by
  unfold columnKappas columnKappasL
  have h : tables.flatMap (fun t ↦ List.replicate t.width (tableLogHeights.getD t.opcode 0)) =
      (tables.map fun t ↦ (t.width, t.opcode)).flatMap
        fun p ↦ List.replicate p.1 (tableLogHeights.getD p.2 0) := by
    rw [List.flatMap_map]
  rw [h, tables_shape]
  rfl

theorem buildLayoutLite_eq (bytecode : List K) (logMemory : ℕ) (tableRows : List ℕ) :
    buildLayoutLite bytecode logMemory tableRows =
      (buildLayout bytecode logMemory tableRows).map Layout.lite := by
  unfold buildLayoutLite buildLayout
  rcases log2Strict bytecode.length with _ | logLength
  · rfl
  · dsimp only
    split_ifs
    · rw [columnKappasL_eq]
      rfl
    · rfl

theorem sizesOfL_eq (bytecode : List K) (announced : List E) :
    sizesOfL bytecode announced = (sizesOf bytecode announced).map fun a ↦ (a.1.lite, a.2) := by
  unfold sizesOfL sizesOf
  dsimp only
  rw [buildLayoutLite_eq]
  split_ifs
  · rcases buildLayout bytecode _ _ with _ | layout
    · rfl
    · simp only [Option.map_some, Option.bind_some]
      split_ifs with h1 h2 h2 <;> first | rfl | exact absurd h1 h2 | exact absurd h2 h1
  · rfl
  · rfl

theorem decSizesL_eq (bytecode : List K) (h : List Ev) :
    decSizesL bytecode (h.map Ev.pair) = (decSizes bytecode h).map fun a ↦ (a.1.lite, a.2) := by
  unfold decSizesL decSizes
  rw [mapM_fst_pair]
  rcases h.mapM Ev.readVal with _ | ann
  · rfl
  · exact sizesOfL_eq bytecode ann

end
end LeanVM.Extraction.AS
