import Rv64Verifier.Proofs.Common
import Rv64Verifier.Image

/-!
# `.rodata`

The image's read-only data is `[0xa0000000, 0xa0000f30)`: the doublewords of `Image.dataWords` in
that range (`rodataWords`), all of them but `.data`'s, the bump allocator's `NEXT` at
`0xa0000f30`. Code loads constants from it, so a function that does asks for `RodataOk`, and for
its stack apart from it. `main` starts with it (`Proofs/End.lean`), and nothing writes it: a frame
apart from it keeps it (`RodataOk.frame`, `RodataOk.frame_two`). The stack, below `0xbffffff0`, is
apart from it (`apart_rodata`, `stack_apart_rodata`).
-/

namespace Rv64Verifier
open RiscvZkvm.Rv64

@[rv_addr] def rodataBase : Word := 0xa0000000

@[rv_addr] def rodataSize : Nat := 0xf30

/-- The image's `.rodata` doublewords and their values. -/
def rodataWords : List (Word × Word) :=
  Image.dataWords.filter fun p ↦
    decide (rodataBase.toNat ≤ p.1.toNat ∧ p.1.toNat < rodataBase.toNat + rodataSize)

/-- Every `.rodata` doubleword holds the image's word. -/
def RodataOk (s : MachineState) : Prop := ∀ p ∈ rodataWords, s.getMem p.1 = p.2

theorem within_of_mem_rodataWords {p : Word × Word} (h : p ∈ rodataWords) :
    Within p.1 rodataBase rodataSize := by
  simp only [rodataWords, List.mem_filter, decide_eq_true_eq] at h
  exact h.2

/-- A `.rodata` word: `hav` is decided from the image. -/
theorem RodataOk.word {s : MachineState} (h : RodataOk s) {a v : Word}
    (hav : (a, v) ∈ rodataWords := by decide +kernel) : s.getMem a = v :=
  h (a, v) hav

/-- `clmul_low`'s mask `M3`. -/
theorem RodataOk.clmulMask {s : MachineState} (h : RodataOk s) :
    s.getMem 0xa0000008 = 0x8888888888888888 :=
  h.word

/-- A frame apart from `.rodata` keeps it. -/
theorem RodataOk.frame {s t : MachineState} {lo : Word} {n : Nat} (h : RodataOk s)
    (hf : MemFrame s t lo n) (ha : Apart lo n rodataBase rodataSize) : RodataOk t := by
  intro p hp
  have hw := within_of_mem_rodataWords hp
  rw [hf p.1 (by addr_omega [hw, ha])]
  exact h p hp

/-- A frame of two ranges, both apart from `.rodata`, keeps it. -/
theorem RodataOk.frame_two {s t : MachineState} {lo₁ lo₂ : Word} {n₁ n₂ : Nat} (h : RodataOk s)
    (hf : ∀ a, ¬ Within a lo₁ n₁ → ¬ Within a lo₂ n₂ → t.getMem a = s.getMem a)
    (ha₁ : Apart lo₁ n₁ rodataBase rodataSize) (ha₂ : Apart lo₂ n₂ rodataBase rodataSize) :
    RodataOk t := by
  intro p hp
  have hw := within_of_mem_rodataWords hp
  rw [hf p.1 (by addr_omega [hw, ha₁]) (by addr_omega [hw, ha₂])]
  exact h p hp

/-- Bytes from `.rodata`'s end on are apart from it. -/
theorem apart_rodata {lo : Word} {n : Nat} (h : 0xa0000f30 ≤ lo.toNat) :
    Apart lo n rodataBase rodataSize := by
  addr_omega [h]

/-- The `n` bytes below `sp` are apart from `.rodata` if they are above its end: a stack within
`0x1ffff0c0` bytes below `0xbffffff0`. -/
theorem stack_apart_rodata {s : MachineState} {n : Nat}
    (h : 0xa0000f30 + n ≤ (s.getReg .x2).toNat) : Apart (stackLo s n) n rodataBase rodataSize := by
  apply apart_rodata
  have := (s.getReg .x2).isLt
  simp only [stackLo, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

end Rv64Verifier
