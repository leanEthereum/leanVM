module

public import NativeRustcX64.Spec.Mem

/-!
# Read-only global-offset-table slots

`GotAt m n areas symbols` requires ordinary data-memory slots at `Labels.gotSlot` to hold the
corresponding labels' addresses. The slots do not wrap, are pairwise disjoint, and are disjoint
from the stack, including its return address, and every listed area. No slot address or contents
are supplied by the executor or fixed to a concrete loader layout.
-/

namespace NativeRustcX64

@[expose] public section

/-- The address of a symbol's ordinary-memory GOT slot. -/
def gotAddr [Labels] (l : Label) : BitVec 64 := (Labels.gotSlot l).toBitVec

/-- The loader's GOT entries, apart from the stack and the caller's areas. -/
def GotAt [Labels] (m : MachineData) (n : Nat) (areas : List (BitVec 64 × Nat))
    (symbols : List Label) : Prop :=
  (∀ l ∈ symbols,
    BytesAt m.dmem (gotAddr l) (Int.toBytes 8 (Labels.label l).toBitVec.toInt) ∧
    NoWrap (gotAddr l) 8 ∧
    Apart (gotAddr l) 8 (rspOf m - BitVec.ofNat 64 n) (n + 8) ∧
    ∀ a ∈ areas, Apart (gotAddr l) 8 a.1 a.2) ∧
  symbols.Pairwise (fun l l' => Apart (gotAddr l) 8 (gotAddr l') 8)

end

public section

/-- A subset of the symbols needs only the corresponding loader assumptions. -/
theorem GotAt.symbols [Labels] {m : MachineData} {n : Nat}
    {areas : List (BitVec 64 × Nat)} {symbols symbols' : List Label}
    (h : GotAt m n areas symbols) (hs : symbols'.Sublist symbols) :
    GotAt m n areas symbols' :=
  ⟨fun l hl => h.1 l (hs.subset hl), h.2.sublist hs⟩

/-- Forgetting protected areas does not change the slot contents or stack separation. -/
theorem GotAt.areas [Labels] {m : MachineData} {n : Nat}
    {areas areas' : List (BitVec 64 × Nat)} {symbols : List Label}
    (h : GotAt m n areas symbols) (ha : ∀ a ∈ areas', a ∈ areas) :
    GotAt m n areas' symbols := by
  refine ⟨?_, h.2⟩
  intro l hl
  obtain ⟨hb, hn, hs, harea⟩ := h.1 l hl
  exact ⟨hb, hn, hs, fun a hmem => harea a (ha a hmem)⟩

/-- A callee's frame preserves all GOT bytes when none of its writes can reach a slot. -/
theorem GotAt.bytes_sameOutside [Labels] {m m' : MachineData} {n : Nat}
    {areas : List (BitVec 64 × Nat)} {symbols : List Label} {writes : BitVec 64 → Prop}
    (h : GotAt m n areas symbols) (hsame : SameOutside m.dmem m'.dmem writes)
    (hapart : ∀ l ∈ symbols, ∀ i < 8, ¬writes (gotAddr l + BitVec.ofNat 64 i)) :
    ∀ l ∈ symbols,
      BytesAt m'.dmem (gotAddr l) (Int.toBytes 8 (Labels.label l).toBitVec.toInt) := by
  intro l hl i hi
  rw [hsame _ (hapart l hl i (by simpa only [Int.toBytes_length] using hi))]
  exact (h.1 l hl).1 i hi

/-- Moving to another state preserves the GOT when its bytes and protected geometry agree. -/
theorem GotAt.transport [Labels] {m m' : MachineData} {n n' : Nat}
    {areas areas' : List (BitVec 64 × Nat)} {symbols : List Label}
    (h : GotAt m n areas symbols)
    (hbytes : ∀ l ∈ symbols, ∀ i < 8,
      m'.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
        m.dmem.get? (gotAddr l + BitVec.ofNat 64 i))
    (hstack : ∀ l ∈ symbols,
      Apart (gotAddr l) 8 (rspOf m' - BitVec.ofNat 64 n') (n' + 8))
    (hareas : ∀ l ∈ symbols, ∀ a ∈ areas', Apart (gotAddr l) 8 a.1 a.2) :
    GotAt m' n' areas' symbols := by
  refine ⟨?_, h.2⟩
  intro l hl
  obtain ⟨hb, hn, _, _⟩ := h.1 l hl
  refine ⟨?_, hn, hstack l hl, hareas l hl⟩
  intro i hi
  rw [hbytes l hl i (by simpa only [Int.toBytes_length] using hi)]
  exact hb i hi

end

end NativeRustcX64
