/-
  Common.ByteArray

  The length of a byte array's list, and of a string's UTF-8 bytes.
-/

module

public import Init

@[expose] public section

/-!
# Byte arrays as lists

`ByteArray.toList` is a well-founded loop, which a `module` cannot evaluate (the proof of its
termination is not exported), so its length is a lemma: `ByteArray.length_toList`, and for a
string's UTF-8 bytes `String.length_toList_toUTF8`.
-/

namespace ByteArray

theorem length_toList_loop (b : ByteArray) :
    ∀ (n i : Nat) (r : List UInt8), b.size - i = n →
      (toList.loop b i r).length = r.length + (b.size - i)
  | 0, i, r, h => by
    rw [toList.loop]
    split
    · omega
    · rw [List.length_reverse, h, Nat.add_zero]
  | n + 1, i, r, h => by
    rw [toList.loop]
    split
    · rw [length_toList_loop b n (i + 1) _ (by omega), List.length_cons]
      omega
    · omega

theorem length_toList (b : ByteArray) : b.toList.length = b.size := by
  rw [toList, length_toList_loop b _ 0 [] rfl, List.length_nil, Nat.zero_add, Nat.sub_zero]

end ByteArray

theorem String.length_toList_toUTF8 (s : String) : s.toUTF8.toList.length = s.utf8ByteSize := by
  rw [ByteArray.length_toList]
  simp

end
