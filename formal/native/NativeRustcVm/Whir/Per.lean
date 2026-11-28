module

public import NativeRustcVm.Rodata
public import NativeRustcVm.MemLemmas

/-!
# `PER_CHALLENGE`'s bytes

Byte `d` of `PER_CHALLENGE` (`d ≤ 128`) is `128 / d` (`0` at `0`, as Lean's division).
-/

namespace NativeRustcVm.Whir

open NativeRustcVm.Data

@[expose] public section

theorem perChallenge_length : Item.perChallenge.bytes.length = 129 := by decide +kernel

theorem perChallenge_getElem? :
    ∀ d : Fin 129, Item.perChallenge.bytes[d.val]? = some (UInt8.ofNat (128 / d.val)) := by
  decide +kernel

/-- **Byte `d`** of `PER_CHALLENGE` at its address. -/
theorem perChallenge_byte {m : Mem 64} {a : BitVec 64} (h : BytesAt m a Item.perChallenge.bytes)
    {d : Nat} (hd : d < 129) : BytesAt m (a + BitVec.ofNat 64 d) [UInt8.ofNat (128 / d)] := by
  have := h.slice d 1
  have e : (Item.perChallenge.bytes.drop d).take 1 = [UInt8.ofNat (128 / d)] := by
    rw [List.take_one, List.head?_drop, perChallenge_getElem? ⟨d, hd⟩]
    rfl
  rwa [e] at this

end

end NativeRustcVm.Whir
