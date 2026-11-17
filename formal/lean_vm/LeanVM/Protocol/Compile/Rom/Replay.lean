/-
  LeanVM.Protocol.Compile.Rom.Replay

  The replay of a verifier program: the extracted run without commitments' words and with openings
  returned unverified, under partial permutation answers, and the permutation inputs it makes.
-/

module

public import LeanVM.Protocol.Compile.Rom.History

/-!
# The replay

The agreement-set extractor reads the challenges of an accepted run off the adversary's
permutation queries. It needs no hash: commitments are absorbed as their roots, and openings,
which the sponge never absorbs, are returned as the proof's leaves unverified.

* `replayU F p s`: `xrun` with the permutation answered by `F`, without the history, the
  commitments' words or the openings' authentication.
* `replayIn F p s`: the permutation inputs the replay makes, in order.
* `replayU_of_xrun`: where `xrun` returns, the replay returns the same value and state.
* `replayU_congr`: answers that agree on the replay's inputs give the same replay.
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash LeanVM.Protocol.Rom

@[expose] public section

section Replay

variable (F : KeccakState → Option KeccakState)

/-- **The replay**: `xrun` with the permutation answered by `F`, the openings unverified, no
history. -/
def replayU {α : Type} : VerifierProgram α → VerifierProgramState → Option (α × VerifierProgramState)
  | .ret a, s => some (a, s)
  | .fail, _ => none
  | .read k, s => match s.stream, s.sponge.ground with
    | x :: xs, none => (absorb (m := Option) F s.sponge x dsObserve).bind fun sp ↦
      replayU (k x) { s with sponge := sp, stream := xs }
    | _, _ => none
  | .sample k, s => (squeeze (m := Option) F s.sponge).bind fun r ↦
      replayU (k r.1) { s with sponge := r.2 }
  | .grind bits k, s => match s.stream, s.sponge.ground with
    | n :: xs, none => (absorbNonce (m := Option) F s.sponge n).bind fun r ↦
      if powOk bits r.1 then replayU k { s with sponge := r.2, stream := xs } else none
    | _, _ => none
  | .commit height width k, s => match s.stream, s.sponge.ground with
    | x0 :: x1 :: xs, none => (absorb (m := Option) F s.sponge x0 dsObserve).bind fun sp0 ↦
      (absorb (m := Option) F sp0 x1 dsObserve).bind fun sp1 ↦
      let root := digestFromHalves (x0, x1)
      replayU k { s with sponge := sp1, stream := xs, roots := s.roots ++ [(root, height, width)] }
    | _, _ => none
  | .query i _ k, s => match s.roots[i]?, s.openings with
    | some _, phase :: rest => replayU (k (phase.map (·.leaf))) { s with openings := rest }
    | _, _ => none

/-- The permutation inputs of absorbing a scalar: the waiting queue's, if it is full. -/
def absorbIn (sp : Sponge) : List KeccakState :=
  if sp.pending.length = rateScalars then [duplexInput sp] else []

/-- The permutation inputs of a squeeze: none if a grind's challenge waits. -/
def squeezeIn (sp : Sponge) : List KeccakState :=
  match sp.ground with
  | some _ => []
  | none => [duplexInput sp]

/-- **The replay's permutation inputs**, in order, up to where it stops. -/
def replayIn {α : Type} : VerifierProgram α → VerifierProgramState → List KeccakState
  | .ret _, _ => []
  | .fail, _ => []
  | .read k, s => match s.stream, s.sponge.ground with
    | x :: xs, none => absorbIn s.sponge ++
      match absorb (m := Option) F s.sponge x dsObserve with
      | some sp => replayIn (k x) { s with sponge := sp, stream := xs }
      | none => []
    | _, _ => []
  | .sample k, s => squeezeIn s.sponge ++
      match squeeze (m := Option) F s.sponge with
      | some r => replayIn (k r.1) { s with sponge := r.2 }
      | none => []
  | .grind bits k, s => match s.stream, s.sponge.ground with
    | n :: xs, none => absorbIn s.sponge ++
      match absorb (m := Option) F s.sponge n dsPowNonce with
      | some sp => [duplexInput sp] ++
        match absorbNonce (m := Option) F s.sponge n with
        | some r => if powOk bits r.1 then replayIn k { s with sponge := r.2, stream := xs } else []
        | none => []
      | none => []
    | _, _ => []
  | .commit height width k, s => match s.stream, s.sponge.ground with
    | x0 :: x1 :: xs, none => absorbIn s.sponge ++
      match absorb (m := Option) F s.sponge x0 dsObserve with
      | some sp0 => absorbIn sp0 ++
        match absorb (m := Option) F sp0 x1 dsObserve with
        | some sp1 =>
          let root := digestFromHalves (x0, x1)
          replayIn k { s with sponge := sp1, stream := xs, roots := s.roots ++ [(root, height, width)] }
        | none => []
      | none => []
    | _, _ => []
  | .query i _ k, s => match s.roots[i]?, s.openings with
    | some _, phase :: rest => replayIn (k (phase.map (·.leaf))) { s with openings := rest }
    | _, _ => []

/-! ## The sponge under agreeing answers -/

variable {F}

theorem absorb_congr {F' : KeccakState → Option KeccakState} {sp : Sponge} (x : E) (tag : ℕ)
    (h : ∀ y ∈ absorbIn sp, F' y = F y) :
    absorb (m := Option) F' sp x tag = absorb (m := Option) F sp x tag := by
  unfold absorb absorbIn at *
  split_ifs with hp
  · simp only [duplex, h (duplexInput sp) (by simp [hp])]
  · rfl

theorem squeeze_congr {F' : KeccakState → Option KeccakState} {sp : Sponge}
    (h : ∀ y ∈ squeezeIn sp, F' y = F y) :
    squeeze (m := Option) F' sp = squeeze (m := Option) F sp := by
  unfold squeeze squeezeIn at *
  split
  · rfl
  · rename_i hg
    simp only [hg] at h
    simp only [duplex, h (duplexInput sp) (by simp)]

theorem absorbNonce_congr {F' : KeccakState → Option KeccakState} {sp sp' : Sponge} (n : E)
    (habs : absorb (m := Option) F sp n dsPowNonce = some sp')
    (h : ∀ y ∈ absorbIn sp ++ [duplexInput sp'], F' y = F y) :
    absorbNonce (m := Option) F' sp n = absorbNonce (m := Option) F sp n := by
  unfold absorbNonce
  rw [absorb_congr n dsPowNonce fun y hy ↦ h y (List.mem_append_left _ hy)]
  simp only [bind, habs, Option.bind_some, duplex,
    h (duplexInput sp') (List.mem_append_right _ (List.mem_singleton_self _))]

/-! ## The replay of an extracted run -/

theorem openAllWithHash_rows {H : Bytes → Option Digest} {root : Digest} {height width : ℕ} :
    ∀ (qs : List ℕ) (os : List Opening) {rows : List (List K)} {rest : List Opening},
      openAllWithHash (m := Option) H root height width qs os = some (some (rows, rest)) →
      rows = (os.take qs.length).map (·.leaf)
  | [], os, rows, rest, h => by
    simp only [openAllWithHash, pure, Option.some.injEq, Prod.mk.injEq] at h
    simp [← h.1]
  | _ :: _, [], _, _, h => by simp [openAllWithHash, pure] at h
  | q :: qs, o :: os, rows, rest, h => by
    rw [openAllWithHash] at h
    rcases hb : openOneWithHash (m := Option) H root height width q o with _ | b
    · rw [hb] at h; exact absurd h (by simp [bind])
    · rw [hb] at h
      change (if b then (openAllWithHash (m := Option) H root height width qs os).bind
        (fun r ↦ some (r.map fun r ↦ (o.leaf :: r.1, r.2))) else some none) = _ at h
      split_ifs at h
      · rcases hr : openAllWithHash (m := Option) H root height width qs os with _ | r
        · rw [hr] at h; simp at h
        · rw [hr, Option.bind_some, Option.some.injEq] at h
          rcases r with _ | ⟨rows', rest'⟩
          · simp at h
          · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.1, openAllWithHash_rows qs os hr]
            simp
      · simp at h

theorem openPhaseWithHash_rows {H : Bytes → Option Digest} {root : Digest} {height width : ℕ}
    {ps : List ℕ} {phase : List Opening} {rows : List (List K)}
    (h : openPhaseWithHash (m := Option) H root height width ps phase = some (some rows)) :
    rows = phase.map (·.leaf) := by
  unfold openPhaseWithHash at h
  split_ifs at h with hc
  · rcases hr : openAllWithHash (m := Option) H root height width ps phase with _ | r
    · rw [hr] at h; exact absurd h (by simp [bind])
    · rw [hr] at h
      change (match r with | some (rows, _) => some (some rows) | none => some none) = _ at h
      rcases r with _ | ⟨rows', rest⟩
      · simp at h
      · simp only [Option.some.injEq] at h
        rw [← h, openAllWithHash_rows ps phase hr]
        have hlen : phase.length = ps.length := by rw [← hc.2, List.length_map]
        rw [← hlen, List.take_length]
  · simp [pure] at h

/-- **Where the extracted run returns, the replay returns the same value and state.** -/
theorem replayU_of_xrun (H : Bytes → Option Digest) (F : KeccakState → Option KeccakState)
    {α : Type} :
    ∀ (p : VerifierProgram α) (s : VerifierProgramState) (h : List Ev) {a : α}
      {s' : VerifierProgramState} {hist : List Ev},
      xrun H F p s h = some (a, s', hist) → replayU F p s = some (a, s')
  | .ret a, s, h, _, _, _, hx => by
    simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl, -⟩ := hx
    rfl
  | .fail, s, h, _, _, _, hx => by simp [xrun] at hx
  | .read k, s, h, _, _, _, hx => by
    simp only [xrun] at hx
    simp only [replayU]
    split at hx
    · rename_i x xs hs hg
      simp only [hs, hg]
      obtain ⟨sp, hsp, hx⟩ := Option.bind_eq_some_iff.mp hx
      rw [hsp, Option.bind_some]
      exact replayU_of_xrun H F (k x) _ _ hx
    · simp at hx
  | .sample k, s, h, _, _, _, hx => by
    simp only [xrun] at hx
    simp only [replayU]
    obtain ⟨r, hr, hx⟩ := Option.bind_eq_some_iff.mp hx
    rw [hr, Option.bind_some]
    exact replayU_of_xrun H F (k r.1) _ _ hx
  | .grind bits k, s, h, _, _, _, hx => by
    simp only [xrun] at hx
    simp only [replayU]
    split at hx
    · rename_i n xs hs hg
      simp only [hs, hg]
      obtain ⟨r, hr, hx⟩ := Option.bind_eq_some_iff.mp hx
      rw [hr, Option.bind_some]
      split_ifs at hx ⊢ with hp
      exact replayU_of_xrun H F k _ _ hx
    · simp at hx
  | .commit height width k, s, h, _, _, _, hx => by
    simp only [xrun] at hx
    simp only [replayU]
    split at hx
    · rename_i x0 x1 xs hs hg
      simp only [hs, hg]
      obtain ⟨sp0, hsp0, hx⟩ := Option.bind_eq_some_iff.mp hx
      obtain ⟨sp1, hsp1, hx⟩ := Option.bind_eq_some_iff.mp hx
      rw [hsp0, Option.bind_some, hsp1, Option.bind_some]
      exact replayU_of_xrun H F k _ _ hx
    · simp at hx
  | .query i ps k, s, h, _, _, _, hx => by
    simp only [xrun] at hx
    simp only [replayU]
    split at hx
    · rename_i root height width phase rest hr ho
      simp only [hr, ho]
      split at hx
      · rename_i rows hrows
        rw [← openPhaseWithHash_rows hrows]
        exact replayU_of_xrun H F (k rows) _ _ hx
      · simp at hx
    · simp at hx

/-- **Answers that agree on the replay's inputs give the same replay.** -/
theorem replayU_congr {F F' : KeccakState → Option KeccakState} {α : Type} :
    ∀ (p : VerifierProgram α) (s : VerifierProgramState),
      (∀ x ∈ replayIn F p s, F' x = F x) → replayU F' p s = replayU F p s
  | .ret _, _, _ => rfl
  | .fail, _, _ => rfl
  | .read k, s, h => by
    simp only [replayU, replayIn] at h ⊢
    split
    · rename_i x xs hs hg
      simp only [hs, hg] at h
      rw [absorb_congr x dsObserve fun y hy ↦ h y (List.mem_append_left _ hy)]
      rcases hsp : absorb (m := Option) F s.sponge x dsObserve with _ | sp
      · rfl
      · simp only [Option.bind_some]
        rw [hsp] at h
        exact replayU_congr (k x) _ fun y hy ↦ h y (List.mem_append_right _ hy)
    · rfl
  | .sample k, s, h => by
    simp only [replayU, replayIn] at h ⊢
    rw [squeeze_congr fun y hy ↦ h y (List.mem_append_left _ hy)]
    rcases hr : squeeze (m := Option) F s.sponge with _ | r
    · rfl
    · simp only [Option.bind_some]
      rw [hr] at h
      exact replayU_congr (k r.1) _ fun y hy ↦ h y (List.mem_append_right _ hy)
  | .grind bits k, s, h => by
    simp only [replayU, replayIn] at h ⊢
    split
    · rename_i n xs hs hg
      simp only [hs, hg] at h
      rcases hsp : absorb (m := Option) F s.sponge n dsPowNonce with _ | sp
      · have : absorbNonce (m := Option) F' s.sponge n = none := by
          unfold absorbNonce
          rw [absorb_congr n dsPowNonce fun y hy ↦ h y (List.mem_append_left _ hy), hsp]
          rfl
        have h2 : absorbNonce (m := Option) F s.sponge n = none := by
          unfold absorbNonce; rw [hsp]; rfl
        simp only [this, h2, Option.bind_none]
      · rw [hsp] at h
        rw [absorbNonce_congr n hsp fun y hy ↦ by
          rcases List.mem_append.mp hy with hy | hy
          · exact h y (List.mem_append_left _ hy)
          · exact h y (List.mem_append_right _ (List.mem_append_left _ hy))]
        rcases hr : absorbNonce (m := Option) F s.sponge n with _ | r
        · rfl
        · simp only [Option.bind_some]
          rw [hr] at h
          split_ifs with hp
          · simp only [hp, ↓reduceIte] at h
            exact replayU_congr k _ fun y hy ↦
              h y (List.mem_append_right _ (List.mem_append_right _ hy))
          · rfl
    · rfl
  | .commit height width k, s, h => by
    simp only [replayU, replayIn] at h ⊢
    split
    · rename_i x0 x1 xs hs hg
      simp only [hs, hg] at h
      rw [absorb_congr x0 dsObserve fun y hy ↦ h y (List.mem_append_left _ hy)]
      rcases hsp0 : absorb (m := Option) F s.sponge x0 dsObserve with _ | sp0
      · rfl
      · simp only [Option.bind_some]
        simp only [hsp0] at h
        rw [absorb_congr x1 dsObserve fun y hy ↦
          h y (List.mem_append_right _ (List.mem_append_left _ hy))]
        rcases hsp1 : absorb (m := Option) F sp0 x1 dsObserve with _ | sp1
        · rfl
        · simp only [Option.bind_some]
          simp only [hsp1] at h
          exact replayU_congr k _ fun y hy ↦
            h y (List.mem_append_right _ (List.mem_append_right _ hy))
    · rfl
  | .query i ps k, s, h => by
    simp only [replayU, replayIn] at h ⊢
    split
    · rename_i r phase rest hr ho
      simp only [hr, ho] at h
      exact replayU_congr (k (phase.map (·.leaf))) _ h
    · rfl

end Replay

end
end LeanVM.Protocol.Compile.Rom
