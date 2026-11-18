/-
  LeanVM.Protocol.Extraction.AS.Hash

  The transcript's Keccak-256 evaluations, recomputed over its first forward answers.
-/

module

public import LeanVM.Protocol.Extraction.AS.Forward
public import LeanVM.Protocol.Rpm.Paths
public import LeanVM.Wire.ReadWrite
public import LeanVM.Protocol.Extraction.Fast.Replay

/-!
# Keccak-256 over the first forward answers

A path the transcript's replay holds is a chain of forward queries from the zero state, each the
query that first fixed its edge, so the first forward query at each of its inputs: the sponge over
the transcript's first forward answers absorbs the path's bytes to the path's state
(`replay_inv`). Hence wherever the transcript's evaluations answer a message, Keccak-256 over the
first forward answers gives the same digest (`keccak256_of_lookupEvaluation`).
-/

namespace LeanVM.Extraction.AS

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash Common

@[expose] public section

/-- Absorb `k` whole blocks of `bs` with `F`. -/
def absorbBlocksF (F : KeccakState → Option KeccakState) :
    ℕ → KeccakState → Bytes → Option KeccakState
  | 0, s, _ => some s
  | k + 1, s, bs => (absorbBlockWith F s (bs.take rate)).bind fun s' ↦
      absorbBlocksF F k s' (bs.drop rate)

theorem absorbBlocksF_mono {F F' : KeccakState → Option KeccakState}
    (hF : ∀ x y, F x = some y → F' x = some y) :
    ∀ (k : ℕ) (s : KeccakState) (bs : Bytes) {t : KeccakState},
      absorbBlocksF F k s bs = some t → absorbBlocksF F' k s bs = some t
  | 0, s, bs, t, h => h
  | k + 1, s, bs, t, h => by
    obtain ⟨s', hs', h⟩ := Option.bind_eq_some_iff.mp h
    rw [absorbBlocksF, absorbBlockWith, hF _ _ hs', Option.bind_some]
    exact absorbBlocksF_mono hF k s' _ h

theorem absorbBlocksF_append (F : KeccakState → Option KeccakState) :
    ∀ (k : ℕ) (s : KeccakState) (bs blk : Bytes), bs.length = rate * k →
      absorbBlocksF F (k + 1) s (bs ++ blk) =
        (absorbBlocksF F k s bs).bind fun t ↦ absorbBlockWith F t (blk.take rate)
  | 0, s, bs, blk, h => by
    have : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst this
    simp only [absorbBlocksF, List.nil_append, Option.bind_some]
    rcases absorbBlockWith F s (blk.take rate) <;> rfl
  | k + 1, s, bs, blk, h => by
    have hl : rate ≤ bs.length := by rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
    rw [absorbBlocksF, List.take_append_of_le_length hl, List.drop_append_of_le_length hl,
      absorbBlocksF]
    rw [Option.bind_assoc]
    refine congrArg _ (funext fun s' ↦ ?_)
    exact absorbBlocksF_append F k s' (bs.drop rate) blk (by simp [h, rate]; ring_nf; omega)

/-- The lanes of a block's bytes are the rates' XOR. -/
theorem littleEndianLane_blockBytes (s x : KeccakState) {i : ℕ} (hi : i < 17) :
    littleEndianLane (Fast.blockBytes s x) i = Keccak.lane s i ^^^ Keccak.lane x i := by
  rw [Wire.littleEndianLane_eq_drop]
  have hd : (Fast.blockBytes s x).drop (8 * i) =
      wordBytes (Keccak.lane s i ^^^ Keccak.lane x i) ++
        (List.range' (i + 1) (16 - i)).flatMap fun j ↦
          wordBytes (Keccak.lane s j ^^^ Keccak.lane x j) := by
    have hr : List.range 17 = List.range i ++ i :: List.range' (i + 1) (16 - i) := by
      rw [List.range_eq_range', show 17 = i + (1 + (16 - i)) by omega, ← List.range'_append,
        ← List.range'_append]
      simp [List.range_eq_range']
    have hlen : ((List.range i).flatMap fun j ↦
        wordBytes (Keccak.lane s j ^^^ Keccak.lane x j)).length = 8 * i := by
      simp [List.length_flatMap, wordBytes, List.sum_replicate, Nat.mul_comm]
    rw [Fast.blockBytes, hr, List.flatMap_append, List.drop_left' hlen, List.flatMap_cons]
  rw [hd, Wire.littleEndianLane_wordBytes_append]

theorem length_blockBytes (s x : KeccakState) : (Fast.blockBytes s x).length = rate := by
  rw [Fast.blockBytes, List.length_flatMap]
  simp [wordBytes_length, rate]

/-- Absorbing the block from `s` to `x` into `s` gives `x`, when their capacities agree. -/
theorem absorb_blockBytes {s x : KeccakState} (hcap : s.toList.drop 17 = x.toList.drop 17) :
    (Vector.ofFn fun i : Fin 25 ↦ if i.val < 17 then
      Keccak.lane s i ^^^ littleEndianLane ((Fast.blockBytes s x).take rate) i
      else Keccak.lane s i) = x := by
  rw [List.take_of_length_le (length_blockBytes s x).le]
  ext i hi
  simp only [Vector.getElem_ofFn]
  split_ifs with h
  · rw [littleEndianLane_blockBytes s x h, ← UInt64.xor_assoc, UInt64.xor_self, UInt64.zero_xor]
    simp [Keccak.lane, hi]
  · have := congrArg (·[i - 17]?) hcap
    simp only [List.getElem?_drop, Vector.getElem?_toList] at this
    rw [show 17 + (i - 17) = i by omega] at this
    simp only [Keccak.lane, Array.getD_eq_getD_getElem?, Vector.getElem?_toArray] at this ⊢
    rw [this, Vector.getElem?_eq_getElem hi]
    rfl

theorem forwardLookup_cons_isSome {E : PermutationEdges KeccakState} {x : KeccakState}
    (h : (forwardLookup E x).isSome) (e : KeccakState × KeccakState) :
    (forwardLookup (e :: E) x).isSome := by
  obtain ⟨a, b⟩ := e
  simp only [forwardLookup]
  split <;> simp_all

/-- **The replay's invariant**: every forward query's input has an edge, and every path is the
sponge over the first forward answers. -/
def ReplayInv (L : List (PermutationQuery KeccakState × KeccakState)) (σ : TranscriptReplay) :
    Prop :=
  (∀ x y, (.forward x, y) ∈ L → (forwardLookup σ.edges x).isSome) ∧
    ∀ p ∈ σ.spongePaths, p.2.length = rate * (p.2.length / rate) ∧
      absorbBlocksF (Rpm.firstForward L) (p.2.length / rate) (Vector.replicate 25 0) p.2 = some p.1

theorem firstForward_append_of_some {L : List (PermutationQuery KeccakState × KeccakState)}
    {x y : KeccakState} (h : Rpm.firstForward L x = some y) (L' : List _) :
    Rpm.firstForward (L ++ L') x = some y := by
  unfold Rpm.firstForward at h ⊢
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [List.find?_append, he]
  rfl

theorem replayInv_step {L : List (PermutationQuery KeccakState × KeccakState)}
    {σ : TranscriptReplay} (h : ReplayInv L σ) (e : PermutationQuery KeccakState × KeccakState) :
    ReplayInv (L ++ [e]) (σ.step e) := by
  obtain ⟨hE, hP⟩ := h
  have hmono : ∀ p ∈ σ.spongePaths, absorbBlocksF (Rpm.firstForward (L ++ [e]))
      (p.2.length / rate) (Vector.replicate 25 0) p.2 = some p.1 := fun p hp ↦
    absorbBlocksF_mono (fun x y hx ↦ firstForward_append_of_some hx _) _ _ _ (hP p hp).2
  obtain ⟨q, a⟩ := e
  cases q with
  | forward x =>
    simp only [TranscriptReplay.step]
    split
    · next b hb =>
      refine ⟨fun x' y' hx' ↦ ?_, fun p hp ↦ ⟨(hP p hp).1, hmono p hp⟩⟩
      rcases List.mem_append.mp hx' with hx' | hx'
      · exact hE x' y' hx'
      · simp only [List.mem_singleton, Prod.mk.injEq, PermutationQuery.forward.injEq] at hx'
        obtain ⟨rfl, -⟩ := hx'
        simp [hb]
    · next hnone =>
      have hEx : ∀ x' y', (PermutationQuery.forward x', y') ∈ L ++ [(.forward x, a)] →
          (forwardLookup ((x, a) :: σ.edges) x').isSome := fun x' y' hx' ↦ by
        rcases List.mem_append.mp hx' with hx' | hx'
        · exact forwardLookup_cons_isSome (hE x' y' hx') _
        · simp only [List.mem_singleton, Prod.mk.injEq, PermutationQuery.forward.injEq] at hx'
          obtain ⟨rfl, -⟩ := hx'
          simp [forwardLookup]
      split
      · next s bs hfind =>
        refine ⟨hEx, fun p hp ↦ ?_⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · have hmem := List.mem_of_find?_eq_some hfind
          have hcap : s.toList.drop 17 = x.toList.drop 17 := by
            simpa using List.find?_some hfind
          obtain ⟨hl, hs⟩ := hP _ hmem
          have hblk := length_blockBytes s x
          have hlen : (bs ++ Fast.blockBytes s x).length / rate = bs.length / rate + 1 := by
            rw [List.length_append, hblk]
            simp only [rate] at hl ⊢
            omega
          refine ⟨?_, ?_⟩
          · show (bs ++ Fast.blockBytes s x).length =
              rate * ((bs ++ Fast.blockBytes s x).length / rate)
            rw [hlen, List.length_append, hblk]
            simp only [rate] at hl ⊢
            omega
          · show absorbBlocksF (Rpm.firstForward (L ++ [(.forward x, a)]))
              ((bs ++ Fast.blockBytes s x).length / rate) (Vector.replicate 25 0)
              (bs ++ Fast.blockBytes s x) = some a
            rw [hlen, absorbBlocksF_append _ _ _ _ _ hl, hmono _ hmem, Option.bind_some,
              absorbBlockWith, absorb_blockBytes hcap]
            have hnf : Rpm.firstForward L x = none := by
              unfold Rpm.firstForward
              rw [Option.map_eq_none_iff, List.find?_eq_none]
              intro e he
              simp only [decide_eq_true_eq]
              intro hq
              obtain ⟨q, y⟩ := e
              simp only at hq
              subst hq
              have := hE x y he
              rw [hnone] at this
              exact absurd this (by simp)
            unfold Rpm.firstForward at hnf ⊢
            rw [List.find?_append, Option.map_eq_none_iff.mp hnf]
            simp
        · exact ⟨(hP p hp).1, hmono p hp⟩
      · exact ⟨hEx, fun p hp ↦ ⟨(hP p hp).1, hmono p hp⟩⟩
  | inverse y =>
    simp only [TranscriptReplay.step]
    have hEx : ∀ (E : PermutationEdges KeccakState), (∀ x', (forwardLookup σ.edges x').isSome →
        (forwardLookup E x').isSome) → ∀ x' y', (PermutationQuery.forward x', y') ∈
          L ++ [(.inverse y, a)] → (forwardLookup E x').isSome := fun E hE' x' y' hx' ↦ by
      rcases List.mem_append.mp hx' with hx' | hx'
      · exact hE' x' (hE x' y' hx')
      · simp at hx'
    split
    · exact ⟨hEx _ fun _ h ↦ h, fun p hp ↦ ⟨(hP p hp).1, hmono p hp⟩⟩
    · exact ⟨hEx _ fun _ h ↦ forwardLookup_cons_isSome h _, fun p hp ↦ ⟨(hP p hp).1, hmono p hp⟩⟩

theorem replay_inv (T : List (PermutationQuery KeccakState × KeccakState)) :
    ReplayInv T (T.foldl TranscriptReplay.step ⟨[], [(Vector.replicate 25 0, [])]⟩) := by
  induction T using List.reverseRecOn with
  | nil =>
    refine ⟨fun _ _ h ↦ by simp at h, fun p hp ↦ ?_⟩
    simp only [List.foldl_nil, List.mem_singleton] at hp
    subst hp
    exact ⟨rfl, rfl⟩
  | append_singleton L e ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact replayInv_step ih e

/-- Keccak-256's absorption is the absorption of its padded bytes' blocks. -/
theorem absorbWith_eq_blocks (F : KeccakState → Option KeccakState) :
    ∀ (q : ℕ) (s : KeccakState) (data : Bytes), data.length / rate = q →
      absorbWith F q s data = absorbBlocksF F (q + 1) s (keccakPadded data)
  | 0, s, data, h => by
    have hl : data.length < 136 := by simp only [rate] at h; omega
    have hp : keccakPadded data = padBlock data := by
      simp [keccakPadded, rate, show data.length / 136 = 0 by omega]
    have hpl : (padBlock data).length = rate := by
      rw [Rpm.length_padBlock _ hl]; rfl
    rw [hp, absorbWith, absorbBlocksF, List.take_of_length_le hpl.le]
    rcases absorbBlockWith F s (padBlock data) <;> rfl
  | q + 1, s, data, h => by
    have hl : 136 ≤ data.length := by simp only [rate] at h; omega
    have hd : (data.drop rate).length / rate = q := by
      simp only [List.length_drop, rate] at h ⊢; omega
    have hp : keccakPadded data = data.take rate ++ keccakPadded (data.drop rate) := by
      simp only [keccakPadded, rate] at hd ⊢
      rw [show data.length / 136 = q + 1 by simp only [rate] at h; omega, hd,
        show 136 * (q + 1) = 136 + 136 * q by ring, List.take_add, List.drop_drop,
        List.append_assoc]
    have htl : (data.take rate).length = rate := by simp [rate]; omega
    rw [absorbWith, absorbBlocksF, hp, List.take_left' htl, List.drop_left' htl]
    simp only [bind, Option.bind]
    rcases absorbBlockWith F s (data.take rate) with _ | s'
    · rfl
    · exact absorbWith_eq_blocks F q s' _ hd

/-- **Where the transcript's evaluations answer a message, Keccak-256 over its first forward
answers gives the same digest.** -/
theorem keccak256_of_lookupEvaluation {T : List (PermutationQuery KeccakState × KeccakState)}
    {m : Bytes} {dg : Digest} (h : lookupEvaluation (keccakEvaluationsOfTranscript T) m = some dg) :
    KeccakHash.keccak256With (Rpm.firstForward T) m = some dg := by
  unfold lookupEvaluation at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  have hm : e.1 = m := by simpa using List.find?_some he
  have hmem := List.mem_of_find?_eq_some he
  unfold keccakEvaluationsOfTranscript at hmem
  obtain ⟨p, hp, hpe⟩ := List.mem_filterMap.mp hmem
  obtain ⟨m', hm', hpe⟩ := Option.map_eq_some_iff.mp hpe
  subst hpe
  simp only at hm
  subst hm
  have hpad := (Rpm.unpad_eq_some_iff _ _).mp hm'
  obtain ⟨-, hs⟩ := (replay_inv T).2 p hp
  rw [← hpad, Rpm.length_padded] at hs
  rw [show 136 * (m'.length / 136 + 1) / rate = m'.length / rate + 1 by
    simp only [rate]; omega] at hs
  unfold KeccakHash.keccak256With
  simp only [bind, Option.bind]
  rw [absorbWith_eq_blocks _ _ _ _ rfl, hs]
  simp only [pure, Keccak.lane]
  congr 1
  ext i hi
  simp only [Array.getD_eq_getD_getElem?, Vector.getElem?_toArray]
  interval_cases i <;> simp

end
end LeanVM.Extraction.AS
