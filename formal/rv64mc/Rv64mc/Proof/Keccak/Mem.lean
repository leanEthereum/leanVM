/-
  Rv64mc.Proof.Keccak.Mem

  Arrays of `E` a Keccak loop fills, in the forms `rv_sym` computes their addresses: `PairsAt M a f n`, element `k`'s
  limbs `f k` at `a + 16 k` and `a + 16 k + 8`, kept by a store outside them (`PairsAt.store_out`), grown by the two
  stores of element `n` (`PairsAt.push`) and changed at one element by two stores (`PairsAt.set`). Each fact is
  stated with only the bounds it needs, so that no program state reaches `omega`.
-/

import Rv64mc.Core.Repr

namespace Rv64mc.Proof.Keccak

open RiscvZkvm.Rv64

/-- **Element `k < n` of an `E` array at `a`** has the limbs `f k`. -/
abbrev PairsAt (M : MachineState) (a : Word) (f : Nat → Word × Word) (n : Nat) : Prop :=
  ∀ k, k < n → M.getMem (a + BitVec.ofNat 64 (16 * k)) = (f k).1 ∧
    M.getMem (a + BitVec.ofNat 64 (16 * k) + 8#64) = (f k).2

theorem toNat_elem {a : Word} {k : Nat} (h : a.toNat + 16 * k + 16 ≤ 2 ^ 64) :
    (a + BitVec.ofNat 64 (16 * k)).toNat = a.toNat + 16 * k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem toNat_elem8 {a : Word} {k : Nat} (h : a.toNat + 16 * k + 16 ≤ 2 ^ 64) :
    (a + BitVec.ofNat 64 (16 * k) + 8#64).toNat = a.toNat + 16 * k + 8 := by
  rw [BitVec.toNat_add, toNat_elem h]; simp only [BitVec.toNat_ofNat]; omega

/-- A store outside the array keeps it. -/
theorem PairsAt.store_out {M : MachineState} {a x v : Word} {f : Nat → Word × Word} {n : Nat}
    (h : PairsAt M a f n) (ha : a.toNat + 16 * n ≤ 2 ^ 64) (hx : x.toNat < a.toNat ∨ a.toNat + 16 * n ≤ x.toNat) :
    PairsAt (M.setMem x v) a f n := by
  intro k hk
  have e0 := toNat_elem (a := a) (k := k) (by omega)
  have e8 := toNat_elem8 (a := a) (k := k) (by omega)
  have n0 : a + BitVec.ofNat 64 (16 * k) ≠ x := fun he => by rw [← he, e0] at hx; omega
  have n8 : a + BitVec.ofNat 64 (16 * k) + 8#64 ≠ x := fun he => by rw [← he, e8] at hx; omega
  rw [MachineState.getMem_setMem_ne n0, MachineState.getMem_setMem_ne n8]
  exact h k hk

/-- Memory that agrees on the array keeps it. -/
theorem PairsAt.congr {M M' : MachineState} {a : Word} {f : Nat → Word × Word} {n : Nat} (h : PairsAt M a f n)
    (ha : a.toNat + 16 * n ≤ 2 ^ 64) (hk : ∀ b, InRange a (16 * n) b → M'.getMem b = M.getMem b) :
    PairsAt M' a f n := by
  intro k hk'
  have e0 := toNat_elem (a := a) (k := k) (by omega)
  have e8 := toNat_elem8 (a := a) (k := k) (by omega)
  rw [hk _ ⟨by omega, by omega⟩, hk _ ⟨by omega, by omega⟩]
  exact h k hk'

/-- **Element `n` stored**: the array grows by one. -/
theorem PairsAt.push {M : MachineState} {a : Word} {f : Nat → Word × Word} {n : Nat} (h : PairsAt M a f n)
    (ha : a.toNat + 16 * n + 16 ≤ 2 ^ 64) :
    PairsAt ((M.setMem (a + BitVec.ofNat 64 (16 * n)) (f n).1).setMem (a + BitVec.ofNat 64 (16 * n) + 8#64) (f n).2)
      a f (n + 1) := by
  intro k hk
  have e0 := toNat_elem (a := a) (k := n) ha
  have e8 := toNat_elem8 (a := a) (k := n) ha
  have ne : a + BitVec.ofNat 64 (16 * n) ≠ a + BitVec.ofNat 64 (16 * n) + 8#64 := fun he => by
    have := congrArg BitVec.toNat he; omega
  by_cases hkn : k = n
  · subst hkn
    rw [MachineState.getMem_setMem_ne ne, MachineState.getMem_setMem_eq, MachineState.getMem_setMem_eq]
    exact ⟨rfl, rfl⟩
  have k0 := toNat_elem (a := a) (k := k) (by omega)
  have k8 := toNat_elem8 (a := a) (k := k) (by omega)
  have n1 : a + BitVec.ofNat 64 (16 * k) ≠ a + BitVec.ofNat 64 (16 * n) := fun he => by
    have := congrArg BitVec.toNat he; omega
  have n2 : a + BitVec.ofNat 64 (16 * k) ≠ a + BitVec.ofNat 64 (16 * n) + 8#64 := fun he => by
    have := congrArg BitVec.toNat he; omega
  have n3 : a + BitVec.ofNat 64 (16 * k) + 8#64 ≠ a + BitVec.ofNat 64 (16 * n) := fun he => by
    have := congrArg BitVec.toNat he; omega
  have n4 : a + BitVec.ofNat 64 (16 * k) + 8#64 ≠ a + BitVec.ofNat 64 (16 * n) + 8#64 := fun he => by
    have := congrArg BitVec.toNat he; omega
  rw [MachineState.getMem_setMem_ne n2, MachineState.getMem_setMem_ne n1, MachineState.getMem_setMem_ne n4,
    MachineState.getMem_setMem_ne n3]
  exact h k (by omega)

/-- **Element `c` stored again**: the array changes there. -/
theorem PairsAt.set {M : MachineState} {a : Word} {f : Nat → Word × Word} {n c : Nat} (h : PairsAt M a f n)
    (ha : a.toNat + 16 * n ≤ 2 ^ 64) (hc : c < n) (v : Word × Word) :
    PairsAt ((M.setMem (a + BitVec.ofNat 64 (16 * c)) v.1).setMem (a + BitVec.ofNat 64 (16 * c) + 8#64) v.2)
      a (fun k => if k = c then v else f k) n := by
  intro k hk
  have e0 := toNat_elem (a := a) (k := c) (by omega)
  have e8 := toNat_elem8 (a := a) (k := c) (by omega)
  have ne : a + BitVec.ofNat 64 (16 * c) ≠ a + BitVec.ofNat 64 (16 * c) + 8#64 := fun he => by
    have := congrArg BitVec.toNat he; omega
  by_cases hkc : k = c
  · subst hkc
    rw [MachineState.getMem_setMem_ne ne, MachineState.getMem_setMem_eq, MachineState.getMem_setMem_eq]
    simp
  have k0 := toNat_elem (a := a) (k := k) (by omega)
  have k8 := toNat_elem8 (a := a) (k := k) (by omega)
  have n1 : a + BitVec.ofNat 64 (16 * k) ≠ a + BitVec.ofNat 64 (16 * c) := fun he => by
    have := congrArg BitVec.toNat he; omega
  have n2 : a + BitVec.ofNat 64 (16 * k) ≠ a + BitVec.ofNat 64 (16 * c) + 8#64 := fun he => by
    have := congrArg BitVec.toNat he; omega
  have n3 : a + BitVec.ofNat 64 (16 * k) + 8#64 ≠ a + BitVec.ofNat 64 (16 * c) := fun he => by
    have := congrArg BitVec.toNat he; omega
  have n4 : a + BitVec.ofNat 64 (16 * k) + 8#64 ≠ a + BitVec.ofNat 64 (16 * c) + 8#64 := fun he => by
    have := congrArg BitVec.toNat he; omega
  rw [MachineState.getMem_setMem_ne n2, MachineState.getMem_setMem_ne n1, MachineState.getMem_setMem_ne n4,
    MachineState.getMem_setMem_ne n3]
  simpa [hkc] using h k hk

end Rv64mc.Proof.Keccak
