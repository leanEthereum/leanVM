module

public import NativeRustcVm.MemLemmas
public import NativeRustcVm.Wire.ReaderFacts

/-!
# Words of mapped memory

Mapped bytes hold some word (`exists_wordAt`), some words (`exists_wordsAt`); words at one address
are unique (`wordsAt_unique`); a list of numbers below `2 ^ 64` is its words' numbers
(`eq_map_toNat`).
-/

namespace NativeRustcVm.Wire

public section

theorem exists_wordAt {d : Mem 64} {a : BitVec 64} (h : Mapped d a 8) : ∃ w, WordAt d a w := by
  refine ⟨UInt64.ofNat (NativeRustcVm.leNat
    ((List.range 8).map fun i ↦ (d.get? (a + BitVec.ofNat 64 i)).getD 0)), ?_⟩
  unfold WordAt
  rw [wordBytes_ofNat_leNat (by simp)]
  intro i hi
  simp only [List.length_map, List.length_range] at hi
  simp only [List.getElem_map, List.getElem_range]
  have := h i hi
  revert this
  cases d.get? (a + BitVec.ofNat 64 i) <;> simp

theorem exists_wordsAt {d : Mem 64} : ∀ (n : Nat) (a : BitVec 64), Mapped d a (8 * n) →
    ∃ L : List UInt64, L.length = n ∧ WordsAt d a L
  | 0, a, _ => ⟨[], rfl, wordsAt_nil d a⟩
  | n + 1, a, h => by
    obtain ⟨h1, h2⟩ := (mapped_append_iff (n := 8 * n) (m := 8)).mp (by rwa [Nat.mul_succ] at h)
    obtain ⟨L, hL, hW⟩ := exists_wordsAt n a h1
    obtain ⟨w, hw⟩ := exists_wordAt h2
    refine ⟨L ++ [w], by simp [hL], wordsAt_append_iff.mpr ⟨hW, ?_⟩⟩
    rw [hL, wordsAt_singleton_iff]
    exact hw

theorem wordsAt_unique {d : Mem 64} {a : BitVec 64} {L L' : List UInt64} (h : WordsAt d a L)
    (h' : WordsAt d a L') (hl : L.length = L'.length) : L = L' :=
  List.ext_getElem hl fun _ hi hi' ↦ (h.getElem hi).unique (h'.getElem hi')

theorem eq_map_toNat {l : List Nat} (h : ∀ y ∈ l, y < 2 ^ 64) :
    l = (l.map Nat.toUInt64).map UInt64.toNat := by
  rw [List.map_map]
  conv_lhs => rw [← List.map_id l]
  exact List.map_congr_left fun y hy ↦ (toNat_toUInt64_of_lt (h y hy)).symm

theorem map_toUInt64_toNat (L : List UInt64) : (L.map UInt64.toNat).map Nat.toUInt64 = L := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id L]
  exact List.map_congr_left fun y _ ↦ by simp

end

end NativeRustcVm.Wire
