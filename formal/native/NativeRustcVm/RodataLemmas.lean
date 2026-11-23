module

public import NativeRustcVm.Rodata
public import NativeRustcVm.MemLemmas

/-!
# Reading the read-only data

`RodataAt`'s parts (`bytesAt`, `noWrap`, `apart`), kept by a change inside the stack
(`RodataAt.of_sameOutside`) and for a stack range inside the one it was stated for
(`RodataAt.mono`); the arrays as words and `E` elements.
-/

namespace NativeRustcVm.RodataAt

open Data

public section

variable {d : Mem 64} {addr : Item → BitVec 64} {sb : BitVec 64} {n : Nat}

theorem bytesAt (h : RodataAt d addr sb n) (t : Item) : BytesAt d (addr t) t.bytes := (h t).1

theorem noWrap (h : RodataAt d addr sb n) (t : Item) : NoWrap (addr t) t.bytes.length := (h t).2.1

theorem apart (h : RodataAt d addr sb n) (t : Item) : Apart (addr t) t.bytes.length sb n :=
  (h t).2.2

/-- The data stays where only the stack changed. -/
theorem of_sameOutside {d' : Mem 64} (h : RodataAt d addr sb n)
    (hs : SameOutside d d' (InRange sb n)) (hsb : NoWrap sb n) : RodataAt d' addr sb n := fun t ↦
  ⟨(h.bytesAt t).of_sameOutside_apart hs (h.apart t) (h.noWrap t) hsb, h.noWrap t, h.apart t⟩

/-- The data is apart from a stack range inside the one it is apart from. -/
theorem mono {sb' : BitVec 64} {n' : Nat} (h : RodataAt d addr sb n) (h1 : sb.toNat ≤ sb'.toNat)
    (h2 : sb'.toNat + n' ≤ sb.toNat + n) : RodataAt d addr sb' n' := fun t ↦
  ⟨h.bytesAt t, h.noWrap t, (h.apart t).mono_right h1 h2⟩

/-! ## The arrays -/

theorem rmfeProject (h : RodataAt d addr sb n) : WordsAt d (addr .rmfeProject) Data.rmfeProject :=
  h.bytesAt .rmfeProject

theorem keccakRC (h : RodataAt d addr sb n) : WordsAt d (addr .keccakRC) Data.keccakRC :=
  h.bytesAt .keccakRC

theorem padding (h : RodataAt d addr sb n) : EWsAt d (addr .padding) Data.padding :=
  h.bytesAt .padding

theorem one (h : RodataAt d addr sb n) : EWAt d (addr .one) ⟨1, 0⟩ := by
  have := h.bytesAt .one
  simpa [Item.bytes, Data.one, EWAt] using this

end

end NativeRustcVm.RodataAt
