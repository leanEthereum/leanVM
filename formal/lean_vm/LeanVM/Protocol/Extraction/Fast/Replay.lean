module

public import Statement.LeanVm
public import LeanVM.Protocol.Extraction.Fast.SortedMap
public import LeanVM.Protocol.Extraction.Fast.Unpad

/-!
# The transcript's replay, indexed and bounded

The statement's replay (`TranscriptReplay.step`, `Statement/LeanVm.lean`) looks up each query's
edge in the list of edges and the path to extend in the list of paths, and copies a path's bytes
to extend it: for `N` queries, `N²` state comparisons and up to `N²·136` bytes. `ReplayFast`
keeps the edges' inputs and outputs and the newest path of each capacity in sorted maps
(`SortedMap`: `O(log² N)` comparisons per lookup, worst-case), and stops recording a path's bytes past a bound `B` (`cut`): the extractor reads only byte
strings of length at most `L` (`64` and `8·width`, `Fast/Lookup.lean`), and a path of more than
`L + 136` bytes unpads to more than `L` bytes, as do its extensions.

* `ReplayFast.Sim`: the fast state simulates the statement's (the same edges' inputs and outputs,
  the same paths with their bytes `cut`, the same newest path per capacity), preserved by a step
  (`Sim.step`);
* the paths unpadded in one pass (`keccakUnpaddedFast`, `Fast/Unpad.lean`);
* **`keccakEvaluationsFast_eq`**: `keccakEvaluationsFast T L` is the statement's
  `keccakEvaluationsOfTranscript T` without the evaluations of more than `L` bytes.
-/

namespace LeanVM.Extraction.Fast

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile Common

public section

/-- A path's bytes if there are at most `B` of them. -/
@[expose] def cut (B : ℕ) (bs : Bytes) : Option Bytes := if bs.length ≤ B then some bs else none

/-- The block that takes the state `s` to the state `x`: the bytes of their rates' XOR. -/
@[expose] def blockBytes (s x : KeccakState) : Bytes :=
  (List.range 17).flatMap fun i ↦ wordBytes (Keccak.lane s i ^^^ Keccak.lane x i)

/-- The replay's state, indexed: the edges' inputs and outputs, the newest path of each
capacity, and the paths, newest first, with their bytes `cut`. -/
structure ReplayFast where
  /-- The inputs of the edges. -/
  fwd : SortedMap (List UInt64) Unit
  /-- The outputs of the edges. -/
  inv : SortedMap (List UInt64) Unit
  /-- The newest path of each capacity (lanes `17 … 24`). -/
  caps : SortedMap (List UInt64) (KeccakState × Option Bytes)
  /-- The paths, newest first. -/
  paths : List (KeccakState × Option Bytes)

/-- `TranscriptReplay.step`, indexed, the paths' bytes cut at `B`. -/
@[expose] def ReplayFast.step (B : ℕ) (τ : ReplayFast) :
    PermutationQuery KeccakState × KeccakState → ReplayFast
  | (.forward x, y) =>
    if τ.fwd.contains x.toList then τ
    else
      match τ.caps.get? (x.toList.drop 17) with
      | some (s, obs) =>
        let p := (y, obs.bind fun bs ↦ cut B (bs ++ blockBytes s x))
        ⟨τ.fwd.insert x.toList (), τ.inv.insert y.toList (), τ.caps.insert (y.toList.drop 17) p,
          p :: τ.paths⟩
      | none => ⟨τ.fwd.insert x.toList (), τ.inv.insert y.toList (), τ.caps, τ.paths⟩
  | (.inverse y, x) =>
    if τ.inv.contains y.toList then τ
    else ⟨τ.fwd.insert x.toList (), τ.inv.insert y.toList (), τ.caps, τ.paths⟩

/-- The replay's start: no edge, the zero state's empty path. -/
@[expose] def ReplayFast.init : ReplayFast :=
  let p : KeccakState × Option Bytes := (Vector.replicate 25 0, some [])
  ⟨.empty, .empty, SortedMap.empty.insert (p.1.toList.drop 17) p, [p]⟩

/-- **The Keccak-256 evaluations of at most `L` bytes a transcript holds**, indexed. -/
@[expose] def keccakEvaluationsFast (T : List (PermutationQuery KeccakState × KeccakState))
    (L : ℕ) : List (Bytes × Digest) :=
  (T.foldl (ReplayFast.step (L + rate)) ReplayFast.init).paths.filterMap fun p ↦
    p.2.bind fun bs ↦ (keccakUnpaddedFast bs).bind fun m ↦
      if m.length ≤ L then some (m, #v[p.1[0], p.1[1], p.1[2], p.1[3]]) else none

/-! ## The simulation -/

/-- The fast state `τ` simulates the statement's `σ`, the bytes cut at `B`. -/
structure ReplayFast.Sim (B : ℕ) (σ : TranscriptReplay) (τ : ReplayFast) : Prop where
  fwd : ∀ x : KeccakState, τ.fwd.contains x.toList = (forwardLookup σ.edges x).isSome
  inv : ∀ y : KeccakState, τ.inv.contains y.toList = (inverseLookup σ.edges y).isSome
  paths : τ.paths = σ.spongePaths.map fun p ↦ (p.1, cut B p.2)
  caps : ∀ c, τ.caps.get? c =
    (σ.spongePaths.find? fun p ↦ p.1.toList.drop 17 = c).map fun p ↦ (p.1, cut B p.2)

theorem cut_append_bind (B : ℕ) (bs blk : Bytes) :
    (cut B bs).bind (fun bs ↦ cut B (bs ++ blk)) = cut B (bs ++ blk) := by
  unfold cut
  by_cases h : bs.length ≤ B
  · simp [h]
  · simp only [h, ↓reduceIte, Option.bind_none]
    rw [ite_eq_right_iff.2 fun h' ↦ absurd (by simp at h'; omega) h]

private theorem contains_insert_toList (s : SortedMap (List UInt64) Unit) (a b : KeccakState) :
    (s.insert a.toList ()).contains b.toList = (decide (a = b) || s.contains b.toList) := by
  rw [SortedMap.contains_insert]
  congr 1
  simp [Vector.toList_inj]

theorem ReplayFast.Sim.step {B : ℕ} {σ : TranscriptReplay} {τ : ReplayFast} (h : Sim B σ τ)
    (q : PermutationQuery KeccakState × KeccakState) :
    Sim B (σ.step q) (τ.step B q) := by
  obtain ⟨q, z⟩ := q
  cases q with
  | forward x =>
    by_cases hx : τ.fwd.contains x.toList
    · have hσ : (forwardLookup σ.edges x).isSome := by rw [← h.fwd]; exact hx
      obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.1 hσ
      simp only [ReplayFast.step, hx, ↓reduceIte, TranscriptReplay.step, hy']
      exact h
    · have hσ : forwardLookup σ.edges x = none := by
        rw [← Option.not_isSome_iff_eq_none, ← h.fwd]; exact hx
      have hfwd : ∀ w : KeccakState, (τ.fwd.insert x.toList ()).contains w.toList =
          (forwardLookup ((x, z) :: σ.edges) w).isSome := by
        intro w
        rw [contains_insert_toList, h.fwd, forwardLookup]
        by_cases hw : x = w <;> simp [hw]
      have hinv : ∀ w : KeccakState, (τ.inv.insert z.toList ()).contains w.toList =
          (inverseLookup ((x, z) :: σ.edges) w).isSome := by
        intro w
        rw [contains_insert_toList, h.inv, inverseLookup]
        by_cases hw : z = w <;> simp [hw]
      have hc := h.caps (x.toList.drop 17)
      simp only [ReplayFast.step, hx, ↓reduceIte, TranscriptReplay.step, hσ, Bool.false_eq_true]
      cases hfind : σ.spongePaths.find? (fun p ↦ p.1.toList.drop 17 = x.toList.drop 17) with
      | none =>
        rw [hfind, Option.map_none] at hc
        simp only [hc]
        exact ⟨hfwd, hinv, h.paths, h.caps⟩
      | some p =>
        obtain ⟨s, bs⟩ := p
        rw [hfind, Option.map_some] at hc
        simp only [hc, cut_append_bind]
        refine ⟨hfwd, hinv, by simp [h.paths, blockBytes], fun c ↦ ?_⟩
        rw [SortedMap.get?_insert, List.find?_cons]
        by_cases hzc : z.toList.drop 17 = c
        · simp [hzc, blockBytes]
        · simp [hzc, h.caps c]
  | inverse y =>
    by_cases hy : τ.inv.contains y.toList
    · have hσ : (inverseLookup σ.edges y).isSome := by rw [← h.inv]; exact hy
      obtain ⟨x', hx'⟩ := Option.isSome_iff_exists.1 hσ
      simp only [ReplayFast.step, hy, ↓reduceIte, TranscriptReplay.step, hx']
      exact h
    · have hσ : inverseLookup σ.edges y = none := by
        rw [← Option.not_isSome_iff_eq_none, ← h.inv]; exact hy
      simp only [ReplayFast.step, hy, ↓reduceIte, TranscriptReplay.step, hσ, Bool.false_eq_true]
      refine ⟨fun w ↦ ?_, fun w ↦ ?_, h.paths, h.caps⟩
      · rw [contains_insert_toList, h.fwd, forwardLookup]
        by_cases hw : z = w <;> simp [hw]
      · rw [contains_insert_toList, h.inv, inverseLookup]
        by_cases hw : y = w <;> simp [hw]

theorem ReplayFast.Sim.init (B : ℕ) :
    Sim B ⟨[], [(Vector.replicate 25 0, [])]⟩ ReplayFast.init := by
  refine ⟨fun x ↦ by simp [ReplayFast.init, forwardLookup],
    fun y ↦ by simp [ReplayFast.init, inverseLookup], by simp [ReplayFast.init, cut], fun c ↦ ?_⟩
  simp only [ReplayFast.init, SortedMap.get?_insert, SortedMap.get?_empty,
    List.find?_cons, List.find?_nil]
  by_cases hc : ([0, 0, 0, 0, 0, 0, 0, 0] : List UInt64) = c <;> simp [hc, cut]

theorem ReplayFast.Sim.foldl {B : ℕ} (T : List (PermutationQuery KeccakState × KeccakState))
    {σ : TranscriptReplay} {τ : ReplayFast} (h : Sim B σ τ) :
    Sim B (T.foldl TranscriptReplay.step σ) (T.foldl (ReplayFast.step B) τ) := by
  induction T generalizing σ τ with
  | nil => exact h
  | cons q T ih => exact ih (h.step q)

/-! ## The evaluations -/

/-- An unpadded message is at most `136` bytes shorter than its padding. -/
theorem length_le_of_keccakUnpadded {bs m : Bytes} (h : keccakUnpadded bs = some m) :
    bs.length ≤ m.length + rate := by
  obtain ⟨k, hk, rfl⟩ : ∃ k < rate, bs.take (bs.length - 1 - k) = m := by
    have := List.mem_of_find?_eq_some h
    simpa using this
  simp only [List.length_take]
  omega

/-- **The indexed evaluations are the statement's of at most `L` bytes.** -/
theorem keccakEvaluationsFast_eq (T : List (PermutationQuery KeccakState × KeccakState))
    (L : ℕ) :
    keccakEvaluationsFast T L =
      (keccakEvaluationsOfTranscript T).filter fun e ↦ decide (e.1.length ≤ L) := by
  have hs := (ReplayFast.Sim.init (L + rate)).foldl T
  rw [keccakEvaluationsFast, keccakUnpaddedFast_eq_fun, hs.paths, keccakEvaluationsOfTranscript, List.filter_filterMap,
    List.filterMap_map]
  refine List.filterMap_congr fun p _ ↦ ?_
  obtain ⟨s, bs⟩ := p
  simp only [Function.comp_apply, cut]
  by_cases hb : bs.length ≤ L + rate
  · simp only [hb, ↓reduceIte, Option.bind_some]
    cases keccakUnpadded bs with
    | none => rfl
    | some m => by_cases hm : m.length ≤ L <;> simp [hm, Option.filter]
  · simp only [hb, ↓reduceIte, Option.bind_none]
    cases hu : keccakUnpadded bs with
    | none => rfl
    | some m =>
      have := length_le_of_keccakUnpadded hu
      have hm : ¬m.length ≤ L := by omega
      simp [hm, Option.filter]

end

end LeanVM.Extraction.Fast
