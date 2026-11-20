/-
  Rv64mc.Model.Extra.Main

  The input reader (`EndStatement.lean`'s `Reader`) a word at a time, as `main` reads it: a word at position `pos`
  of the input (`readWord_drop`), `readMany` one item more (`readMany_snoc`), the leaf's words at once
  (`readMany_readK`), and `decodeInput` from the four reads in order (`decodeInput_of_runs`).
-/

import Rv64mc.EndStatement

namespace Rv64mc

open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

theorem readWord_run (w : Word) (ws : List Word) : readWord.run (w :: ws) = some (w, ws) := rfl

theorem readWord_drop {ws : List Word} {pos : Nat} (h : pos < ws.length) :
    readWord.run (ws.drop pos) = some (ws[pos], ws.drop (pos + 1)) := by
  rw [List.drop_eq_getElem_cons h]; rfl

theorem readCount_drop {ws : List Word} {pos : Nat} (h : pos < ws.length) :
    readCount.run (ws.drop pos) = some (ws[pos].toNat, ws.drop (pos + 1)) := by
  rw [List.drop_eq_getElem_cons h]; rfl

theorem bind_run_some {α β : Type} {x : Reader α} {f : α → Reader β} {ws ws1 : List Word} {a : α}
    (h : x.run ws = some (a, ws1)) : (x >>= f).run ws = (f a).run ws1 := by
  rw [StateT.run_bind, h]; rfl

theorem bind_run_inv {α β : Type} {x : Reader α} {f : α → Reader β} {ws : List Word} {b : β}
    {ws' : List Word} (h : (x >>= f).run ws = some (b, ws')) :
    ∃ a ws1, x.run ws = some (a, ws1) ∧ (f a).run ws1 = some (b, ws') := by
  rw [StateT.run_bind] at h
  cases h1 : x.run ws with
  | none => rw [h1] at h; cases h
  | some p => rw [h1] at h; exact ⟨p.1, p.2, rfl, h⟩

theorem pure_run_inv {α : Type} {a b : α} {ws ws' : List Word}
    (h : (pure a : Reader α).run ws = some (b, ws')) : a = b ∧ ws = ws' := by
  simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  exact h

theorem readMany_zero {α : Type} (item : Reader α) (ws : List Word) : (readMany item 0).run ws = some ([], ws) := rfl

theorem readMany_snoc {α : Type} {item : Reader α} :
    ∀ (k : Nat) (ws : List Word) (xs : List α) (ws1 : List Word) (x : α) (ws2 : List Word),
      (readMany item k).run ws = some (xs, ws1) → item.run ws1 = some (x, ws2) →
      (readMany item (k + 1)).run ws = some (xs ++ [x], ws2)
  | 0, ws, xs, ws1, x, ws2, h1, h2 => by
    simp only [readMany_zero, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    show (do let y ← item; let ys ← readMany item 0; return y :: ys : Reader (List α)).run ws = _
    rw [bind_run_some h2]; rfl
  | k + 1, ws, xs, ws1, x, ws2, h1, h2 => by
    change (do let y ← item; let ys ← readMany item k; return y :: ys : Reader (List α)).run ws = _ at h1
    obtain ⟨y, wsa, hy, h1⟩ := bind_run_inv h1
    obtain ⟨ys, wsb, hys, h1⟩ := bind_run_inv h1
    obtain ⟨rfl, rfl⟩ := pure_run_inv h1
    change (do let y ← item; let ys ← readMany item (k + 1); return y :: ys : Reader (List α)).run ws = _
    rw [bind_run_some hy, bind_run_some (readMany_snoc k wsa ys wsb x ws2 hys h2)]
    rfl

/-- `n` words read as `K`s, at once. -/
theorem readMany_readK : ∀ (n : Nat) (ws : List Word), n ≤ ws.length →
    (readMany readK n).run ws = some ((ws.take n).map BF64.ofBitVec, ws.drop n)
  | 0, ws, _ => rfl
  | n + 1, w :: ws, h => by
    change (do let y ← readK; let ys ← readMany readK n; return y :: ys : Reader (List K)).run (w :: ws) = _
    rw [bind_run_some (x := readK) (a := BF64.ofBitVec w) (ws1 := ws) rfl,
      bind_run_some (readMany_readK n ws (by simp at h; omega))]
    rfl

/-- **The input decodes** to what the four reads give, when nothing is left. -/
theorem decodeInput_of_runs {words r1 r2 r3 : List Word} {bc : List K} {pi : Digest} {st : List E}
    {ops : List (List Opening)} (h1 : (readList readK).run words = some (bc, r1))
    (h2 : readDigest.run r1 = some (pi, r2)) (h3 : (readList readScalar).run r2 = some (st, r3))
    (h4 : (readList (readList readOpening)).run r3 = some (ops, [])) :
    decodeInput words = some (bc, pi, { stream := st, openings := ops }) := by
  unfold decodeInput readInput
  rw [bind_run_some h1, bind_run_some h2, bind_run_some h3, bind_run_some h4]
  rfl

theorem readList_of {α : Type} {item : Reader α} {ws ws1 ws2 : List Word} {n : Nat} {xs : List α}
    (h1 : readCount.run ws = some (n, ws1)) (h2 : (readMany item n).run ws1 = some (xs, ws2)) :
    (readList item).run ws = some (xs, ws2) := by
  unfold readList
  rw [bind_run_some h1, h2]

theorem readOpening_of {ws ws1 ws2 ws3 : List Word} {idx : Nat} {leaf : List K} {path : List Digest}
    (h1 : readCount.run ws = some (idx, ws1)) (h2 : (readList readK).run ws1 = some (leaf, ws2))
    (h3 : (readList readDigest).run ws2 = some (path, ws3)) :
    readOpening.run ws = some ({ leafIndex := idx, leaf := leaf, path := path }, ws3) := by
  unfold readOpening
  rw [bind_run_some h1, bind_run_some h2, bind_run_some h3]
  rfl

end Rv64mc
