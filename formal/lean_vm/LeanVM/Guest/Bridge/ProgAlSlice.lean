/-
  LeanVM.Guest.Bridge.ProgAlSlice

  Slices of a long function's code chunks, for windows that walk no more of the code than they check, and its cells packed ahead.
-/

module

public import LeanVM.Guest.Bridge.AlignRun

/-!
# Slices

A window handed the whole code walks it every time; for `main_loop2` that walk outweighs the window. Here a list of parts `L` (the code's chunks) is cut at **cuts** `(p, r)`, offset `r` of part `p`: `restL L c` is what is left from the cut, `slice L a b` what lies between two cuts, built from the parts it touches only (`slice_rest`: a slice then the rest from its end is the rest from its start). The pairing's windows (`CoreMode/PairSlice.lean`) and the frame walk's (`CoreMode/FrameSlice.lean`) read them.

`AlignCtx.ofPacked`: the context from the cells packed ahead (`ofData_eq_ofPacked`), so a window builds the cell trie from the packed chunks, and one check equates them with the certificate's.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (PowTree Trie natSeq natSeq_eq)

@[expose] public section

/-- A position in a list of parts: part `p`, offset `r` in it. -/
abbrev PCut := ℕ × ℕ

/-- What is left of the parts from a cut. -/
def restL {α : Type} (L : List (List α)) (c : PCut) : List α := (L.drop c.1).flatten.drop c.2

/-- **The slice between two cuts**, from the parts it touches. -/
def slice {α : Type} (L : List (List α)) (a b : PCut) : List α :=
  (((L.drop a.1).take (b.1 - a.1)).flatten ++ (L.getD b.1 []).take b.2).drop a.2

/-- The slice's cuts are in order and within their parts. -/
def sliceOk {α : Type} (L : List (List α)) (a b : PCut) : Bool :=
  Nat.ble a.1 b.1 && Nat.ble a.2 (lenTR (((L.drop a.1).take (b.1 - a.1)).flatten ++ (L.getD b.1 []).take b.2) 0) &&
    Nat.ble b.2 (lenTR (L.getD b.1 []) 0)

/-- **The context from the cells packed ahead**, with whether each cell fits. -/
noncomputable def AlignCtx.ofPacked (pl : List ℕ) (locOk : Bool) (extra : List (ℕ × ℕ)) (entry : ℕ) (main : Bool)
    (p : B2C.Plumb) (pows : PowTree) (jt : Trie ℕ) (ents : List (String × ℕ)) (halt len : ℕ) : AlignCtx :=
  ⟨buildT 32 pl, locOk, extra, entry, main, trieOf p.stat, trieOf (p.sites.map fun s ↦ (s.q, s)), trieOf (armsOf p),
    pows, jt, trieOf (ents.map fun e ↦ (e.2, e.1)), halt, len, 1048576, p.nxt⟩

/-! ## Packing in pieces -/

/-- The chunks `packGo` completes over `l` from digit `j` of the chunk `acc`, and where it stops. -/
def packSt : List ℕ → ℕ → ℕ → List ℕ × ℕ × ℕ
  | [], j, acc => ([], j, acc)
  | c :: cs, j, acc => bif Nat.beq j 63 then (fun r ↦ (Nat.add acc (Nat.shiftLeft c (Nat.mul cellBits j)) :: r.1, r.2)) (packSt cs 0 0)
      else packSt cs (Nat.succ j) (Nat.add acc (Nat.shiftLeft c (Nat.mul cellBits j)))

end

public section

theorem packGo_append : ∀ (l1 l2 : List ℕ) (j acc : ℕ),
    packGo (l1 ++ l2) j acc = (packSt l1 j acc).1 ++ packGo l2 (packSt l1 j acc).2.1 (packSt l1 j acc).2.2
  | [], _, _, _ => rfl
  | c :: cs, l2, j, acc => by
    simp only [List.cons_append, packGo, packSt, natSeq_eq]
    cases Nat.beq j 63
    · simp only [Bool.cond_false]; exact packGo_append cs l2 _ _
    · simp only [Bool.cond_true, List.cons_append]; rw [packGo_append cs l2 0 0]

theorem ofData_eq_ofPacked (locs : List ℕ) (extra : List (ℕ × ℕ)) (entry : ℕ) (main : Bool) (p : B2C.Plumb)
    (pows : PowTree) (jt : Trie ℕ) (ents : List (String × ℕ)) (halt len : ℕ) :
    AlignCtx.ofData locs extra entry main p pows jt ents halt len =
      AlignCtx.ofPacked (packGo locs 0 0) (locs.all fun c ↦ Nat.blt c (2 ^ cellBits)) extra entry main p pows jt
        ents halt len := rfl

/-! ## Slices -/

theorem drop_flatten_getD {α : Type} : ∀ (L : List (List α)) (n : ℕ),
    (L.drop n).flatten = L.getD n [] ++ (L.drop (n + 1)).flatten
  | [], _ => by simp
  | x :: L, 0 => by simp
  | x :: L, n + 1 => by simpa using drop_flatten_getD L n

/-- **A slice then the rest from its end is the rest from its start.** -/
theorem slice_rest {α : Type} {L : List (List α)} {a b : PCut} (h : sliceOk L a b = true) :
    slice L a b ++ restL L b = restL L a := by
  simp only [sliceOk, Bool.and_eq_true, Nat.ble_eq, lenTR_eq, Nat.add_zero] at h
  obtain ⟨⟨hab, hr⟩, hs⟩ := h
  have hd : L.drop a.1 = (L.drop a.1).take (b.1 - a.1) ++ L.drop b.1 := by
    conv_lhs => rw [← List.take_append_drop (b.1 - a.1) (L.drop a.1)]
    rw [List.drop_drop, show a.1 + (b.1 - a.1) = b.1 by omega]
  simp only [slice, restL]
  rw [drop_flatten_getD L b.1]
  generalize hA : ((L.drop a.1).take (b.1 - a.1)).flatten = A at hr ⊢
  conv_rhs => rw [hd, List.flatten_append, hA, drop_flatten_getD L b.1]
  generalize L.getD b.1 [] = B at hs hr ⊢
  generalize (L.drop (b.1 + 1)).flatten = R
  rw [List.drop_append_of_le_length hs]
  conv_rhs => rw [← List.take_append_drop b.2 B, List.append_assoc, ← List.append_assoc A,
    List.drop_append_of_le_length hr]

theorem restL_end {α : Type} (L : List (List α)) : restL L (L.length, 0) = [] := by simp [restL]

end

end LeanVM.Guest.Bridge
