/-
  LeanVM.Guest.B2C.ShareStatic

  The sharing check's static part of a function of many values, its bit set of the values' cells
  computed window by window, each window's part in its own kernel evaluation.
-/

module

public import LeanVM.Guest.B2C.Share

/-!
# The static sharing check, by windows

`shareStatic` (`apartOk`) builds the bit set of every value's cell, `bitsOf (certOf j).locs`, one
bit at a time: in `verify_sig_lean_sphincs`, over a million values, the kernel keeps each of the
intermediate sets. Here the same check takes the set as an argument (`shareStaticN`, equal by
definition), and a list of sets `Ns` (`listElementOrDefault Ns 0 0 = 0`) gives it window by window:
each window's cells added to `Ns[k]` give `Ns[k + 1]` (`bitsFrom`, one kernel evaluation each), so
the set of all of them is the last (`bitsOf_flatten_of_chain`, `shareStatic_of_chain`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check

@[expose] public section

/-- `apartOk` with the bit set of the values' cells given. -/
noncomputable def apartOkN (j vb : ℕ) : Bool :=
  natSeq (Nat.lor (tmpCells (plumbOf j)) (bitsOf ((plumbOf j).runs.map Prod.snd))) fun tr ↦
  natSeq (bitsOf ((plumbOf j).stat.map Prod.fst)) fun st ↦
  natSeq (Nat.lor (Nat.lor tr st) vb) fun trsv ↦
  natSeq (bitsOf (siteCells (plumbOf j))) fun sc ↦
  natSeq (bitsOf ((plumbOf j).arms.map fun a ↦ a.2.1)) fun ac ↦
  apart st (tmpCells (plumbOf j)) && apart sc trsv && apart ac (Nat.lor trsv sc) &&
    bitsNodup ((plumbOf j).stat.map Prod.fst) 0 && bitsNodup (siteCells (plumbOf j)) 0 &&
    bitsNodup ((plumbOf j).arms.map fun a ↦ a.2.1) 0 &&
    (certOf j).facts.env.all (fun p ↦ (plumbOf j).stat.any fun q ↦ Nat.beq q.1 p.1 && q.2 == .fpg 0) &&
    (bif Nat.beq j 1 then Nat.blt (Nat.lor (Nat.lor trsv sc) ac) (2 ^ 429) else true)

/-- `shareStatic` with the bit set of the values' cells given. -/
noncomputable def shareStaticN (j vb : ℕ) : Bool :=
  (locW (certOf j) 0).seq fun loc ↦ natSeq (tmpCells (plumbOf j)) fun tc ↦
  natSeq (fpgCells (plumbOf j)) fun fc ↦ (byCell (plumbOf j).tmps).seq fun tt ↦
  (listElementOrDefault (certOf j).cells 0 []).all (fun c ↦ Nat.blt c 65536) &&
  listsOk (plumbOf j) (fsN j) && snapsOk (certOf j) (snapsOf j) &&
    apartOkN j vb && (coreOf j).params.all (valOk loc tt tc fc (fsN j))

theorem shareStatic_eq (j : ℕ) : shareStatic j = shareStaticN j (bitsOf (certOf j).locs) := rfl

/-- The bit set `s` with the cells `l` added. -/
def bitsFrom (s : ℕ) (l : List ℕ) : ℕ := l.foldl setBit s

theorem foldl_flatten_of_chain (Ns : List ℕ) : ∀ (L : List (List ℕ)) (i : ℕ),
    (∀ k < L.length, bitsFrom (listElementOrDefault Ns (i + k) 0) (listElementOrDefault L k []) =
        listElementOrDefault Ns (i + k + 1) 0) →
      L.flatten.foldl setBit (listElementOrDefault Ns i 0) = listElementOrDefault Ns (i +
          L.length) 0
  | [], i, _ => rfl
  | l :: L, i, h => by
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, bitsFrom, listElementOrDefault] at h0
    rw [List.flatten_cons, List.foldl_append, h0,
      foldl_flatten_of_chain Ns L (i + 1) fun k hk ↦ by
        have := h (k + 1) (by simp; omega)
        rw [show i + (k + 1) = i + 1 + k by omega] at this
        exact this]
    simp only [List.length_cons]
    congr 1
    omega

/-- The bit set of the cells of the lists `L`, by a chain of sets, each list adding to one the
next. -/
theorem bitsOf_flatten_of_chain (L : List (List ℕ)) (Ns : List ℕ) (h0 : listElementOrDefault Ns
    0 0 = 0)
    (h : ∀ k < L.length, bitsFrom (listElementOrDefault Ns k 0) (listElementOrDefault L k []) =
        listElementOrDefault Ns (k + 1) 0) :
    bitsOf L.flatten = listElementOrDefault Ns L.length 0 := by
  have := foldl_flatten_of_chain Ns L 0 (by simpa only [Nat.zero_add] using h)
  rw [h0, Nat.zero_add] at this
  exact this

/-- **The static sharing check of function `j`** from a chain of bit sets over its windows' cells
and the check with the last. -/
theorem shareStatic_of_chain (j : ℕ) (Ns : List ℕ) (h0 : listElementOrDefault Ns 0 0 = 0)
    (h : ∀ k < (certOf j).cells.length,
      bitsFrom (listElementOrDefault Ns k 0) (listElementOrDefault (certOf j).cells k []) =
          listElementOrDefault Ns (k + 1) 0)
    (hs : shareStaticN j (listElementOrDefault Ns (certOf j).cells.length 0) = true) : shareStatic j
        = true := by
  rw [shareStatic_eq, show (certOf j).locs = (certOf j).cells.flatten from rfl,
    bitsOf_flatten_of_chain _ _ h0 h]
  exact hs

end
end LeanVM.Guest.B2C
