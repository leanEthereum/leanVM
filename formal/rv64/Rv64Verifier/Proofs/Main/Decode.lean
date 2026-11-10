import Rv64Verifier.Proofs.Main.Stages

/-!
# `decodeInput`, piece by piece

`main` reads the input as `readInput` does, a piece at a time, each loop of it one `readList`. A
`readList` of `n` items is `rep item n` (`readList_run`), and `rep` grows at the end
(`rep_succ`), as a loop that has read `i` items has: its invariant is `(rep item i).run ws =
some (xs, rest)`. `decodeInput_of` puts the four pieces together; `readWords_rep` and
`readScalar_run`, `readDigest_run` read words, scalars and digests.
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-- `n` items, one after the other. -/
def rep {α : Type} (item : Reader α) : Nat → Reader (List α)
  | 0 => pure []
  | n + 1 => do
    let x ← item
    let xs ← rep item n
    return x :: xs

theorem mapM_const {α β : Type} (item : Reader α) :
    ∀ l : List β, l.mapM (fun _ ↦ item) = rep item l.length
  | [] => rfl
  | _ :: l => by
    rw [List.mapM_cons, mapM_const item l]
    rfl

theorem readWord_run_cons (w : Word) (ws : List Word) : readWord.run (w :: ws) = some (w, ws) :=
  rfl

theorem readWord_run_nil : readWord.run [] = none := rfl

theorem readList_run {α : Type} (item : Reader α) (w : Word) (ws : List Word) :
    (readList item).run (w :: ws) = (rep item w.toNat).run ws := by
  have e : (readList item).run (w :: ws) = ((List.range w.toNat).mapM fun _ ↦ item).run ws := rfl
  rw [e, mapM_const, List.length_range]

theorem rep_zero {α : Type} (item : Reader α) (ws : List Word) :
    (rep item 0).run ws = some ([], ws) := rfl

theorem rep_run_bind {α : Type} (item : Reader α) (n : Nat) (ws : List Word) :
    (rep item (n + 1)).run ws = ((item.run ws).bind fun p ↦
      ((rep item n).run p.2).bind fun q ↦ some (p.1 :: q.1, q.2)) := by
  simp only [rep, StateT.run_bind]
  rfl

/-- `rep` grows at the end. -/
theorem rep_succ {α : Type} (item : Reader α) :
    ∀ (n : Nat) (ws : List Word), (rep item (n + 1)).run ws = (((rep item n).run ws).bind fun p ↦
      (item.run p.2).bind fun q ↦ some (p.1 ++ [q.1], q.2))
  | 0, ws => by
    rw [rep_run_bind, rep_zero]
    rcases h : item.run ws with _ | p <;> simp [h, rep_zero]
  | n + 1, ws => by
    rw [rep_run_bind, rep_run_bind]
    rcases h1 : item.run ws with _ | p
    · simp
    · simp only [Option.bind_some]
      rw [rep_succ item n p.2]
      rcases h2 : (rep item n).run p.2 with _ | q
      · simp
      · rcases h3 : item.run q.2 with _ | r <;> simp [h3]

/-- The loop's step: one more item. -/
theorem rep_step {α : Type} {item : Reader α} {n : Nat} {ws rest rest' : List Word} {xs : List α}
    {x : α} (h : (rep item n).run ws = some (xs, rest)) (hx : item.run rest = some (x, rest')) :
    (rep item (n + 1)).run ws = some (xs ++ [x], rest') := by
  rw [rep_succ, h]
  show (item.run rest).bind _ = _
  rw [hx]
  rfl

/-- `n` words, each mapped by `f`. -/
theorem readWords_rep {α : Type} (f : Word → α) :
    ∀ (n : Nat) (ws : List Word), n ≤ ws.length →
      (rep (f <$> readWord) n).run ws = some ((ws.take n).map f, ws.drop n)
  | 0, _, _ => rfl
  | n + 1, w :: ws, h => by
    have ih := readWords_rep f n ws (by simp only [List.length_cons] at h; omega)
    rw [rep_run_bind]
    have e : (f <$> readWord).run (w :: ws) = some (f w, ws) := rfl
    rw [e]
    show ((rep (f <$> readWord) n).run ws).bind _ = _
    rw [ih]
    rfl

/-- **`decodeInput` from its four pieces.** -/
theorem decodeInput_of {words w₁ w₂ w₃ : List Word} {table : List K} {pi : Digest} {stream : List E}
    {openings : List (List Opening)}
    (h₁ : (readList (BF64.ofBitVec <$> readWord)).run words = some (table, w₁))
    (h₂ : readDigest.run w₁ = some (pi, w₂)) (h₃ : (readList readScalar).run w₂ = some (stream, w₃))
    (h₄ : (readList (readList readOpening)).run w₃ = some (openings, [])) :
    decodeInput words = some (table, pi, { stream, openings }) := by
  have hr : readInput.run words = some ((table, pi, { stream, openings }), []) := by
    simp only [readInput, StateT.run_bind, h₁]
    show (readDigest.run w₁).bind _ = _
    rw [h₂]
    show ((readList readScalar).run w₂).bind _ = _
    rw [h₃]
    show ((readList (readList readOpening)).run w₃).bind _ = _
    rw [h₄]
    rfl
  simp only [decodeInput, hr]

end Rv64Verifier.Proofs.Main
