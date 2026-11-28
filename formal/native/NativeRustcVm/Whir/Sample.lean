module

public import NativeVm.Model.Whir

/-!
# `sampleQueries` as `sample_queries` runs it

`sampleQueriesAux` never fails: it is `auxP` (`sampleQueriesAux_run`), a pure function of the
transcript's state, each step a squeeze (`sq`) and a chunk of `min (128 / depth) remaining`
positions (`chunk`) (`auxP_succ`). A run from `count` positions after `j` steps is what the steps
gave and the rest (`auxP_split`).
-/

namespace NativeRustcVm.Whir

open NativeVm.Model

@[expose] public section

/-- A squeeze of the transcript's sponge: the challenge and the next state. -/
def sq (s : TState) : EW × TState := (s.sponge.squeeze.1, { s with sponge := s.sponge.squeeze.2 })

/-- The `n` positions of a challenge. -/
def chunk (depth : Nat) (c : EW) (n : Nat) : Array UInt64 :=
  (Array.range n).map fun i ↦ queryBits c (i * depth) depth

/-- `sampleQueriesAux`, pure. -/
def auxP (depth : Nat) : Nat → Nat → TState → Array UInt64 × TState
  | 0, _, s => (#[], s)
  | fuel + 1, remaining, s =>
    if remaining = 0 then (#[], s)
    else
      let n := min (128 / depth) remaining
      let r := auxP depth fuel (remaining - n) (sq s).2
      (chunk depth (sq s).1 n ++ r.1, r.2)

theorem sampleChallenge_run (s : TState) : sampleChallenge.run s = some (sq s) := rfl

/-- **`sampleQueriesAux` never fails.** -/
theorem sampleQueriesAux_run (depth : Nat) :
    ∀ fuel remaining s, (sampleQueriesAux depth fuel remaining).run s =
      some (auxP depth fuel remaining s)
  | 0, _, _ => rfl
  | fuel + 1, remaining, s => by
    by_cases h : remaining = 0
    · simp [sampleQueriesAux, auxP, h]
    · have ih := sampleQueriesAux_run depth fuel (remaining - min (128 / depth) remaining)
        (sq s).2
      simp only [sampleQueriesAux, auxP, h, ↓reduceIte]
      show (do
        let c ← sampleChallenge
        let rest ← sampleQueriesAux depth fuel (remaining - min (128 / depth) remaining)
        pure ((Array.range (min (128 / depth) remaining)).map
          (fun i ↦ queryBits c (i * depth) depth) ++ rest)).run s = _
      simp only [StateT.run_bind, sampleChallenge_run, Option.bind_eq_bind, Option.bind_some]
      rw [ih]
      rfl

theorem sampleQueries_run (depth count : Nat) (s : TState) :
    (sampleQueries depth count).run s = some (auxP depth count count s) :=
  sampleQueriesAux_run depth count count s

/-- A step of `auxP` with positions left. -/
theorem auxP_succ (depth fuel remaining : Nat) (s : TState) (h : remaining ≠ 0) :
    auxP depth (fuel + 1) remaining s =
      (chunk depth (sq s).1 (min (128 / depth) remaining) ++
        (auxP depth fuel (remaining - min (128 / depth) remaining) (sq s).2).1,
        (auxP depth fuel (remaining - min (128 / depth) remaining) (sq s).2).2) := by
  simp [auxP, h]

theorem auxP_zero_left (depth remaining : Nat) (s : TState) : auxP depth 0 remaining s = (#[], s) :=
  rfl

theorem auxP_zero_right (depth fuel : Nat) (s : TState) : auxP depth fuel 0 s = (#[], s) := by
  cases fuel <;> rfl

theorem chunk_size (depth : Nat) (c : EW) (n : Nat) : (chunk depth c n).size = n := by
  simp [chunk]

/-- The positions `auxP` gives number at most `remaining`. -/
theorem auxP_size (depth : Nat) : ∀ fuel remaining s, (auxP depth fuel remaining s).1.size ≤ remaining
  | 0, _, _ => by simp [auxP]
  | fuel + 1, remaining, s => by
    by_cases h : remaining = 0
    · simp [auxP, h]
    · rw [auxP_succ _ _ _ _ h]
      have := auxP_size depth fuel (remaining - min (128 / depth) remaining) (sq s).2
      simp only [Array.size_append, chunk_size]
      omega

/-- A step with no position per challenge (`128 / depth = 0`): a squeeze. -/
theorem auxP_big {depth : Nat} (hd : 128 / depth = 0) (fuel remaining : Nat) (s : TState)
    (h : remaining ≠ 0) : auxP depth (fuel + 1) remaining s = auxP depth fuel remaining (sq s).2 := by
  rw [auxP_succ _ _ _ _ h]
  simp only [hd, Nat.zero_min, chunk, Nat.sub_zero]
  rw [show (Array.range 0).map (fun i ↦ queryBits (sq s).1 (i * depth) depth) = #[] from
      Array.eq_empty_of_size_eq_zero (by simp),
    Array.empty_append]

/-- The first `i + 1` positions of a chunk. -/
theorem chunk_take_succ (depth : Nat) (c : EW) {n i : Nat} (hi : i < n) :
    (chunk depth c n).toList.take (i + 1) =
      (chunk depth c n).toList.take i ++ [queryBits c (i * depth) depth] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [chunk_size]; exact hi)]
  simp [chunk]

theorem chunk_take_all (depth : Nat) (c : EW) (n : Nat) :
    (chunk depth c n).toList.take n = (chunk depth c n).toList := by
  rw [List.take_of_length_le (by simp [chunk_size])]

/-- **A step of the outer loop** in the model: after `j` challenges with `r ≠ 0` positions left,
the next challenge's chunk appended. -/
theorem auxP_next {depth cnt j r : Nat} {s0 s : TState} {qs : List UInt64}
    (hm : auxP depth cnt cnt s0 =
      (qs.toArray ++ (auxP depth (cnt - j) r s).1, (auxP depth (cnt - j) r s).2))
    (hj : j < cnt) (hr : r ≠ 0) :
    auxP depth cnt cnt s0 =
      ((qs ++ (chunk depth (sq s).1 (min (128 / depth) r)).toList).toArray ++
        (auxP depth (cnt - (j + 1)) (r - min (128 / depth) r) (sq s).2).1,
        (auxP depth (cnt - (j + 1)) (r - min (128 / depth) r) (sq s).2).2) := by
  rw [hm, show cnt - j = cnt - (j + 1) + 1 by omega, auxP_succ _ _ _ _ hr]
  rw [← List.append_toArray, Array.toArray_toList, Array.append_assoc]

end

end NativeRustcVm.Whir
