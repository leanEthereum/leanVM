module

public import NativeVm.Model.Transcript

/-!
# The sumcheck loop and `climb` as `transcript.rs` runs them

`TState::sumcheck(claim, count, equality, out)` runs one round per slot of `out`, round `i`'s
equality factor `equality(i)`; the model's `sumcheck claim count equalities` folds over
`equalities`. With `equalities` the closure's values, `Array.ofFn fun i : Fin n ↦ E i`
(`sumcheckFn`), a round more is a `push` (`sumcheckFn_succ`); the plain mode's closure is
`fun _ ↦ None` (`sumcheckFn_none`), `gkr_step`'s and `verify_layer`'s `point.get(i)`
(`sumcheckFn_getElem?`, the whole point when `out` is as long).

`climb(node, q, path, height)` walks the levels in order; after `l` of them its accumulator and
position are the model's fold over the first `l` digests (`climbTo`, `climbTo_succ`), after all of
them `climb`'s result (`climbTo_size`).
-/

namespace NativeRustcVm.Sumcheck

open NativeVm.Model LeanVM.Protocol

@[expose] public section

/-! ## The sumcheck loop -/

/-- The model's sumcheck over `n` rounds, round `i`'s equality factor `E i`. -/
def sumcheckFn (claim : EW) (count : Nat) (E : Nat → Option EW) (n : Nat) :
    VM (Array EW × EW) :=
  sumcheck claim count (Array.ofFn fun i : Fin n ↦ E i)

/-- One round of the loop: the round polynomial, the challenge, the claim the polynomial takes
there. -/
def sumcheckRound (count : Nat) (e : Option EW) (acc : Array EW × EW) : VM (Array EW × EW) := do
  let message ← sumcheckRoundPoly count acc.2 e
  let challenge ← sampleChallenge
  pure (acc.1.push challenge, polyEval message challenge)

theorem sumcheck_push (claim : EW) (count : Nat) (es : Array (Option EW)) (e : Option EW) :
    sumcheck claim count (es.push e) =
      (sumcheck claim count es >>= sumcheckRound count e) := by
  simp only [sumcheck, Array.foldlM_push]
  rfl

/-- No round: the claim. -/
theorem sumcheckFn_zero (claim : EW) (count : Nat) (E : Nat → Option EW) (s : TState) :
    sumcheckFn claim count E 0 s = some ((#[], claim), s) := by
  simp [sumcheckFn, sumcheck]
  rfl

/-- **A round more.** -/
theorem sumcheckFn_succ (claim : EW) (count : Nat) (E : Nat → Option EW) (n : Nat) :
    sumcheckFn claim count E (n + 1) =
      (sumcheckFn claim count E n >>= sumcheckRound count (E n)) := by
  rw [sumcheckFn, Array.ofFn_succ, sumcheck_push]
  rfl

/-- The rounds after `n` of them, in state terms. -/
theorem sumcheckFn_succ_apply (claim : EW) (count : Nat) (E : Nat → Option EW) (n : Nat)
    (s : TState) :
    sumcheckFn claim count E (n + 1) s =
      (sumcheckFn claim count E n s).bind fun p ↦ sumcheckRound count (E n) p.1 p.2 := by
  rw [sumcheckFn_succ]
  rfl

/-- **A round more, the round polynomial read**: the challenge the sponge squeezes appended, the
claim the polynomial takes there. -/
theorem sumcheckFn_run_succ_some {claim : EW} {count : Nat} {E : Nat → Option EW} {i : Nat}
    {s si s1 : TState} {xs msg : Array EW} {c : EW}
    (h : (sumcheckFn claim count E i).run s = some ((xs, c), si))
    (hr : (sumcheckRoundPoly count c (E i)).run si = some (msg, s1)) :
    (sumcheckFn claim count E (i + 1)).run s =
      some ((xs.push s1.sponge.squeeze.1, polyEval msg s1.sponge.squeeze.1),
        { s1 with sponge := s1.sponge.squeeze.2 }) := by
  show sumcheckFn claim count E (i + 1) s = _
  rw [sumcheckFn_succ_apply]
  rw [show sumcheckFn claim count E i s = _ from h]
  show (sumcheckRoundPoly count c (E i) si).bind _ = _
  rw [show sumcheckRoundPoly count c (E i) si = _ from hr]
  rfl

/-- **A round more, the round polynomial rejected**: `none`. -/
theorem sumcheckFn_run_succ_none {claim : EW} {count : Nat} {E : Nat → Option EW} {i : Nat}
    {s si : TState} {xs : Array EW} {c : EW}
    (h : (sumcheckFn claim count E i).run s = some ((xs, c), si))
    (hr : (sumcheckRoundPoly count c (E i)).run si = none) :
    (sumcheckFn claim count E (i + 1)).run s = none := by
  show sumcheckFn claim count E (i + 1) s = _
  rw [sumcheckFn_succ_apply]
  rw [show sumcheckFn claim count E i s = _ from h]
  show (sumcheckRoundPoly count c (E i) si).bind _ = _
  rw [show sumcheckRoundPoly count c (E i) si = _ from hr]
  rfl

/-- **A rejection stays one** over more rounds. -/
theorem sumcheckFn_run_none_le {claim : EW} {count : Nat} {E : Nat → Option EW} {i n : Nat}
    {s : TState} (h : (sumcheckFn claim count E i).run s = none) (hle : i ≤ n) :
    (sumcheckFn claim count E n).run s = none := by
  induction n, hle using Nat.le_induction with
  | base => exact h
  | succ n _ ih =>
    show sumcheckFn claim count E (n + 1) s = _
    rw [sumcheckFn_succ_apply, show sumcheckFn claim count E n s = none from ih]
    rfl

/-- The plain mode: no equality factor. -/
theorem sumcheckFn_none (claim : EW) (count n : Nat) :
    sumcheckFn claim count (fun _ ↦ none) n = sumcheckPlain claim count n := by
  simp only [sumcheckFn, sumcheckPlain]
  congr 1
  ext i h₁ h₂
  · simp
  · simp

/-- The equality factors `point.get(i)` over as many rounds as the point has coordinates: the
point's coordinates. -/
theorem sumcheckFn_getElem? (claim : EW) (count : Nat) (point : Array EW) :
    sumcheckFn claim count (fun i ↦ point[i]?) point.size =
      sumcheck claim count (point.map some) := by
  simp only [sumcheckFn]
  congr 1
  ext i h₁ h₂
  · simp
  · simp

/-! ## `climb` -/

/-- One level: the low bit of the position chooses the side, the position halves. -/
def climbStep (acc : Digest × UInt64) (s : Digest) : Digest × UInt64 :=
  (if acc.2 % 2 = 0 then hashPair acc.1 s else hashPair s acc.1, acc.2 / 2)

/-- The accumulator and the position after the first `l` levels. -/
def climbTo (node : Digest) (q : UInt64) (path : Array Digest) (l : Nat) : Digest × UInt64 :=
  (path.toList.take l).foldl climbStep (node, q)

theorem climbTo_zero (node : Digest) (q : UInt64) (path : Array Digest) :
    climbTo node q path 0 = (node, q) := rfl

/-- A level more. -/
theorem climbTo_succ (node : Digest) (q : UInt64) (path : Array Digest) {l : Nat}
    (hl : l < path.size) :
    climbTo node q path (l + 1) = climbStep (climbTo node q path l) path[l] := by
  simp only [climbTo]
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hl), Option.toList_some,
    List.foldl_append]
  simp

/-- After every level: `climb`. -/
theorem climbTo_size (node : Digest) (q : UInt64) (path : Array Digest) :
    (climbTo node q path path.size).1 = climb node q path := by
  rw [climbTo, ← Array.length_toList, List.take_length, climb, ← Array.foldl_toList]
  rfl

end

end NativeRustcVm.Sumcheck
