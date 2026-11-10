import Rv64Verifier.Proofs.Main.ParseSplit

/-!
# What the heap holds, across steps that write none of it

`HeapSame s t`: every doubleword below `heapEnd` is unchanged. Then the buffers a `Bytecode`'s
`Vec`s point into, which lie below `NEXT`, read the same (`blocksAt_heap`, `wordsAt_heap`,
`halvesAt_heap`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Proofs.Bytecode

def HeapSame (s t : MachineState) : Prop := ∀ a : Word, a.toNat < heapEnd → t.getMem a = s.getMem a

theorem HeapSame.trans {s t u : MachineState} (h₁ : HeapSame s t) (h₂ : HeapSame t u) :
    HeapSame s u := fun a ha ↦ (h₂ a ha).trans (h₁ a ha)

theorem toNat_add_small {p : Word} {k : Nat} (h : p.toNat + k < 2 ^ 64) :
    (p + BitVec.ofNat 64 k).toNat = p.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem blocksAt_heap {s t : MachineState} (h : HeapSame s t) {p : Word} {n : Nat}
    (hp : n = 0 ∨ p.toNat + 24 * n ≤ heapEnd) : blocksAt t p n = blocksAt s p n := by
  rcases hp with rfl | hp
  · rfl
  simp only [heapEnd] at hp
  unfold blocksAt
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  have e0 := toNat_add_small (p := p) (k := 24 * i) (by omega)
  have e8 : (p + BitVec.ofNat 64 (24 * i) + 8).toNat = p.toNat + 24 * i + 8 := by
    rw [BitVec.toNat_add, e0]; have : (8 : Word).toNat = 8 := rfl; omega
  have e16 : (p + BitVec.ofNat 64 (24 * i) + 16).toNat = p.toNat + 24 * i + 16 := by
    rw [BitVec.toNat_add, e0]; have : (16 : Word).toNat = 16 := rfl; omega
  rw [h _ (by simp only [heapEnd]; omega), h _ (by simp only [heapEnd]; omega),
    h _ (by simp only [heapEnd]; omega)]

theorem wordsAt_heap {s t : MachineState} (h : HeapSame s t) {p : Word} {n : Nat}
    (hp : n = 0 ∨ p.toNat + 16 * n ≤ heapEnd) : wordsAt t p n = wordsAt s p n := by
  rcases hp with rfl | hp
  · rfl
  simp only [heapEnd] at hp
  unfold wordsAt
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  have e0 := toNat_add_small (p := p) (k := 16 * i) (by omega)
  have e8 : (p + BitVec.ofNat 64 (16 * i) + 8).toNat = p.toNat + 16 * i + 8 := by
    rw [BitVec.toNat_add, e0]; have : (8 : Word).toNat = 8 := rfl; omega
  rw [h _ (by simp only [heapEnd]; omega), h _ (by simp only [heapEnd]; omega)]

theorem halvesAt_heap {s t : MachineState} (h : HeapSame s t) {p : Word} {n : Nat}
    (hp : n = 0 ∨ p.toNat + 2 * n ≤ heapEnd) : halvesAt t p n = halvesAt s p n := by
  rcases hp with rfl | hp
  · rfl
  simp only [heapEnd] at hp
  unfold halvesAt
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  have e0 := toNat_add_small (p := p) (k := 2 * i) (by omega)
  simp only [MachineState.getHalfword]
  rw [h _ (by rw [alignToDword, toNat_alignDown]; simp only [heapEnd]; omega)]

end Rv64Verifier.Proofs.Main
