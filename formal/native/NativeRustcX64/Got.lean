module

public import NativeRustcX64.Spec.Got
public import NativeRustcX64.Sym.Run

/-!
# GOT loads and preservation across calls

The loader hypothesis supplies the bytes used to seed symbolic memory, and the ordinary
`SameOutside` frame of a callee preserves them whenever its writes stay inside the stack and
protected areas. A slot is not a special memory space: stores obey the usual memory semantics.
-/

namespace NativeRustcX64

public section

/-- The GOT bytes in the representation used by symbolic memory. -/
theorem GotAt.byte [Labels] {m : MachineData} {n : Nat}
    {areas : List (BitVec 64 × Nat)} {symbols : List Label} (h : GotAt m n areas symbols)
    {l : Label} (hl : l ∈ symbols) {i : Nat} (hi : i < 8) :
    m.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
      some (Sym.byteOf (Labels.label l).toBitVec i) := by
  have hb := (h.1 l hl).1 i (by simpa only [Int.toBytes_length] using hi)
  have hv := Sym.toBytes_setWidth (Labels.label l).toBitVec 8 i hi
  simp only [BitVec.setWidth_eq] at hv
  rw [List.getElem?_eq_getElem (by simpa only [Int.toBytes_length] using hi)] at hv
  exact hb.trans hv

/-- Every byte of a GOT slot is ordinary mapped memory. -/
theorem GotAt.mapped [Labels] {m : MachineData} {n : Nat}
    {areas : List (BitVec 64 × Nat)} {symbols : List Label} (h : GotAt m n areas symbols)
    {l : Label} (hl : l ∈ symbols) : Mapped m.dmem (gotAddr l) 8 := by
  intro i hi
  rw [h.byte hl hi]
  rfl

/-- A byte of a non-wrapping range cannot lie in a disjoint non-wrapping range. -/
theorem Apart.not_inRange {a b : BitVec 64} {n k i : Nat}
    (h : Apart a n b k) (ha : NoWrap a n) (hb : NoWrap b k) (hi : i < n) :
    ¬InRange b k (a + BitVec.ofNat 64 i) := by
  rw [Sym.inRange_iff hb, Sym.toNat_add_ofNat a i (by unfold NoWrap at ha; omega)]
  unfold Apart at h
  omega

/-- A callee that writes only the protected stack and areas cannot change any GOT byte. -/
theorem GotAt.unchanged [Labels] {m m' : MachineData} {n : Nat}
    {areas : List (BitVec 64 × Nat)} {symbols : List Label}
    (h : GotAt m n areas symbols) (hstack : StackOk m n)
    (hareas : ∀ a ∈ areas, NoWrap a.1 a.2)
    (hsame : SameOutside m.dmem m'.dmem (fun p =>
      InRange (rspOf m - BitVec.ofNat 64 n) n p ∨
        ∃ a ∈ areas, InRange a.1 a.2 p)) :
    ∀ l ∈ symbols, ∀ i < 8,
      m'.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
        m.dmem.get? (gotAddr l + BitVec.ofNat 64 i) := by
  intro l hl i hi
  obtain ⟨_, hnw, hs, ha⟩ := h.1 l hl
  apply hsame
  rintro (hsp | ⟨a, hmem, hin⟩)
  · have hbase : (rspOf m - BitVec.ofNat 64 n).toNat = (rspOf m).toNat - n := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
      have := hstack.1
      have := (rspOf m).isLt
      omega
    have hsnw : NoWrap (rspOf m - BitVec.ofNat 64 n) (n + 8) := by
      unfold NoWrap
      rw [hbase]
      have := hstack.1
      have := hstack.2.1
      omega
    apply hs.not_inRange hnw hsnw hi
    exact Nat.lt_trans hsp (by omega)
  · exact (ha a hmem).not_inRange hnw (hareas a hmem) hi hin

end

end NativeRustcX64
