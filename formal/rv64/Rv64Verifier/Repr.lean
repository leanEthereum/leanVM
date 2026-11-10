import Rv64Verifier.Machine
import Rv64Verifier.Model.Ext

/-!
# Lean values in memory

How the image holds the verifier's values, as compiled: a `K` is one doubleword; an `E` is three,
`c0`, `c1`, `c2` at `a`, `a + 8`, `a + 16` (`field.rs`, `struct E { c0, c1, c2 }`); a slice of `E`
is a pointer and a length, its elements 24 bytes apart. `eAt` and `eListAt` read them back as
the statement's values, and `limbs_eAt` connects `eAt` to the field model's limbs.
-/

namespace Rv64Verifier
open RiscvZkvm.Rv64 LeanVM.Parameters CompPoly.Extension

/-- The `E` held at `a`. -/
def eAt (s : MachineState) (a : Word) : E :=
  E.ofLimbs (BF64.ofBitVec (s.getMem a)) (BF64.ofBitVec (s.getMem (a + 8)))
    (BF64.ofBitVec (s.getMem (a + 16)))

/-- The `n` elements of the slice of `E` at `p`. -/
def eListAt (s : MachineState) (p : Word) (n : Nat) : List E :=
  (List.range n).map fun i ↦ eAt s (p + BitVec.ofNat 64 (24 * i))

theorem eListAt_length (s : MachineState) (p : Word) (n : Nat) : (eListAt s p n).length = n := by
  simp [eListAt]

theorem eListAt_getElem (s : MachineState) (p : Word) (n i : Nat) (h : i < (eListAt s p n).length) :
    (eListAt s p n)[i] = eAt s (p + BitVec.ofNat 64 (24 * i)) := by
  simp [eListAt]

theorem limbs_ofLimbs (a b c : K) :
    Model.limbs (E.ofLimbs a b c) = (a.toBitVec, b.toBitVec, c.toBitVec) := by
  rfl

theorem limbs_eAt (s : MachineState) (a : Word) :
    Model.limbs (eAt s a) = (s.getMem a, s.getMem (a + 8), s.getMem (a + 16)) := by
  rw [eAt, limbs_ofLimbs]
  rfl

/-- `E` is determined by its limbs. -/
theorem eq_of_limbs {x y : E} (h : Model.limbs x = Model.limbs y) : x = y := by
  simp only [Model.limbs, Prod.mk.injEq] at h
  obtain ⟨h0, h1, h2⟩ := h
  apply Ext.ext
  rintro ⟨i, hi⟩
  have hd : BF64.ext3Params.d = 3 := rfl
  have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases this with rfl | rfl | rfl
  · rw [← Ext.coeffNat_of_lt _ (by omega), ← Ext.coeffNat_of_lt _ (by omega)]
    exact BF64.toBitVec_injective h0
  · rw [← Ext.coeffNat_of_lt _ (by omega), ← Ext.coeffNat_of_lt _ (by omega)]
    exact BF64.toBitVec_injective h1
  · rw [← Ext.coeffNat_of_lt _ (by omega), ← Ext.coeffNat_of_lt _ (by omega)]
    exact BF64.toBitVec_injective h2

/-! ## Folds over prefixes, for loop invariants -/

theorem foldl_zipWith_take_succ {α β γ δ : Type} (f : α → β → γ) (g : δ → γ → δ) (z : δ)
    (l : List α) (r : List β) (k : Nat) (hl : k < l.length) (hr : k < r.length) :
    (List.zipWith f (l.take (k + 1)) (r.take (k + 1))).foldl g z =
      g ((List.zipWith f (l.take k) (r.take k)).foldl g z) (f l[k] r[k]) := by
  rw [List.take_succ_eq_append_getElem hl, List.take_succ_eq_append_getElem hr,
    List.zipWith_append (by simp; omega), List.foldl_append]
  simp

end Rv64Verifier
