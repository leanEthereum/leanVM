module

public import NativeRustcVm.Layout.Rep
public import NativeRustcVm.MemLemmas

/-!
# The layout's representations, kept and extended

`Same d d' a n`: the `n` bytes from `a` are the same in `d` and `d'` (`Same.of_sameOutside`, from a
change that misses them). A representation over bytes that stayed the same still holds
(`WordAt.of_same`, `EWAt.of_same`, `BufEWAt.of_same`, `ColumnClaimAt.of_same`), and the column
claims with one more claim, written after them and the count updated, hold the pushed array
(`ClaimsWAt.push`).
-/

namespace NativeRustcVm.Layout

open NativeVm.Model
open NativeRustcVm.Transcript (off)

public section

/-- The `n` bytes from `a` are the same in `d` and `d'`. -/
@[expose] def Same (d d' : Mem 64) (a : BitVec 64) (n : Nat) : Prop :=
  ∀ j < n, d'.get? (a + BitVec.ofNat 64 j) = d.get? (a + BitVec.ofNat 64 j)

theorem Same.of_sameOutside {d d' : Mem 64} {R : BitVec 64 → Prop} (hs : SameOutside d d' R)
    {a : BitVec 64} {n : Nat} (h : ∀ j < n, ¬R (a + BitVec.ofNat 64 j)) : Same d d' a n :=
  fun j hj ↦ hs _ (h j hj)

theorem Same.trans {d d' d'' : Mem 64} {a : BitVec 64} {n : Nat} (h : Same d d' a n)
    (h' : Same d' d'' a n) : Same d d'' a n :=
  fun j hj ↦ (h' j hj).trans (h j hj)

theorem Same.sub {d d' : Mem 64} {a : BitVec 64} {n o k : Nat} (h : Same d d' a n)
    (hk : o + k ≤ n) : Same d d' (a + BitVec.ofNat 64 o) k := fun j hj ↦ by
  rw [addr_add_add]; exact h _ (by omega)

theorem BytesAt.of_same {d d' : Mem 64} {a : BitVec 64} {bs : List UInt8} {n : Nat}
    (h : BytesAt d a bs) (hs : Same d d' a n) (hl : bs.length ≤ n) : BytesAt d' a bs :=
  fun i hi ↦ by rw [hs i (by omega)]; exact h i hi

theorem WordAt.of_same {d d' : Mem 64} {a : BitVec 64} {w : UInt64} {n : Nat}
    (h : WordAt d a w) (hs : Same d d' a n) (hl : 8 ≤ n) : WordAt d' a w :=
  BytesAt.of_same h hs (by rw [length_wordBytes]; exact hl)

theorem EWAt.of_same {d d' : Mem 64} {a : BitVec 64} {x : EW} {n : Nat}
    (h : EWAt d a x) (hs : Same d d' a n) (hl : 16 ≤ n) : EWAt d' a x :=
  BytesAt.of_same h hs (by rw [length_ewBytes]; exact hl)

theorem BufEWAt.of_same {d d' : Mem 64} {a : BitVec 64} {N : Nat} {xs : List EW} {n : Nat}
    (h : BufEWAt d a N xs) (hs : Same d d' a n) (hl : 8 + 16 * N ≤ n) : BufEWAt d' a N xs := by
  obtain ⟨hle, hw, he⟩ := h
  refine ⟨hle, WordAt.of_same hw hs (by omega), BytesAt.of_same he (hs.sub (o := 8) (k := 16 * N)
    (by omega)) ?_⟩
  rw [length_ewsBytes]; omega

/-- A column claim over bytes that stayed the same. -/
theorem ColumnClaimAt.of_same {d d' : Mem 64} {a : BitVec 64} {c : ColumnClaimW}
    (h : ColumnClaimAt d a c) (hs : Same d d' a columnClaimBytes) : ColumnClaimAt d' a c :=
  ⟨h.column_lt, WordAt.of_same h.column hs (by decide),
    BufEWAt.of_same h.point (hs.sub (o := 8) (k := 584) (by decide)) (by decide),
    EWAt.of_same h.value (hs.sub (o := 592) (k := 16) (by decide)) (by decide)⟩

/-- **One claim pushed**: the count `n + 1`, the claims before as they were, the new one at its
place. -/
theorem ClaimsWAt.push {d d' : Mem 64} {a : BitVec 64} {cs : Array ColumnClaimW}
    {x : ColumnClaimW} (h : ClaimsWAt d a cs) (hn : cs.size < claimCap)
    (hlen : WordAt d' a (cs.size + 1).toUInt64)
    (hold : ∀ i < cs.size, Same d d' (off a (8 + columnClaimBytes * i)) columnClaimBytes)
    (hnew : ColumnClaimAt d' (off a (8 + columnClaimBytes * cs.size)) x) :
    ClaimsWAt d' a (cs.push x) := by
  refine ⟨by rw [Array.size_push]; omega, by rw [Array.size_push]; exact hlen, fun i hi ↦ ?_⟩
  rw [Array.size_push] at hi
  rcases Nat.lt_or_ge i cs.size with hlt | hge
  · rw [Array.getElem_push_lt hlt]
    exact (h.claims i hlt).of_same (hold i hlt)
  · obtain rfl : i = cs.size := by omega
    rw [Array.getElem_push_eq]
    exact hnew

end

end NativeRustcVm.Layout
