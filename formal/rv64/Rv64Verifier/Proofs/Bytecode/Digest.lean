import Rv64Verifier.Proofs.Bytecode.DigestObl

/-!
# `Input::digest` (`guest/src/main.rs`)

```rust
fn digest(&mut self) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for chunk in bytes.as_chunks_mut::<8>().0 {
        *chunk = self.word().to_le_bytes();
    }
    bytes
}
```

compiled at `0x800000e4` (`Blocks/F1.lean`): `a0` is where the 32 bytes go, `a1` the `Input`, a
slice of words (pointer at `+0`, length at `+8`). With fewer than four words left, `0x800000e4`
or `0x800000ec` branches to `0x80000274`, which halts with `2` (a dead end); otherwise
`0x800000f4` loads the four words, stores each byte by byte (`replaceBytes_eq`), advances the
slice and returns.
-/

namespace Rv64Verifier.Proofs.Bytecode
open RiscvZkvm.Rv64 Rv64Verifier.Blocks.F1 Rv64Verifier.Runtime
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The pointer and length of the `Input` at `a`. -/
def inputPtr (s : MachineState) (a : Word) : Word := s.getMem a
def inputLen (s : MachineState) (a : Word) : Word := s.getMem (a + 8)

/-- `a0` = 32 bytes for the result, `a1` = the `Input`, both aligned and mapped, apart from each
other and from the stack; when four words are left, they are mapped, aligned and apart from the
stack. -/
structure DigestPre (s : MachineState) : Prop where
  out : Mapped (s.getReg .x10) 32
  outAlign : (s.getReg .x10).toNat % 8 = 0
  self : Mapped (s.getReg .x11) 16
  selfAlign : (s.getReg .x11).toNat % 8 = 0
  stack : StackOk s digestStack
  outSelf : Apart (s.getReg .x10) 32 (s.getReg .x11) 16
  outStack : Apart (s.getReg .x10) 32 (stackLo s digestStack) digestStack
  selfStack : Apart (s.getReg .x11) 16 (stackLo s digestStack) digestStack
  words : 4 ≤ (inputLen s (s.getReg .x11)).toNat →
    Mapped (inputPtr s (s.getReg .x11)) 32 ∧ (inputPtr s (s.getReg .x11)).toNat % 8 = 0 ∧
      Apart (inputPtr s (s.getReg .x11)) 32 (stackLo s digestStack) digestStack

/-- Four words were left; the result holds them (as doublewords, their little-endian bytes), the
slice moved past them, and memory changed only in the result, the `Input` and the stack. -/
structure DigestPost (s t : MachineState) : Prop where
  len : 4 ≤ (inputLen s (s.getReg .x11)).toNat
  words : t.readWords (s.getReg .x10) 4 = s.readWords (inputPtr s (s.getReg .x11)) 4
  ptr : inputPtr t (s.getReg .x11) = inputPtr s (s.getReg .x11) + 32
  rest : inputLen t (s.getReg .x11) = inputLen s (s.getReg .x11) - 4
  frame : ∀ a, ¬ Within a (s.getReg .x10) 32 → ¬ Within a (s.getReg .x11) 16 →
    ¬ Within a (stackLo s digestStack) digestStack → t.getMem a = s.getMem a

abbrev DigestSpec : Prop := FunSpec Image.code 0x800000e4 DigestPre DigestPost

theorem digest_halt_fetch : Image.code.fetch 0x8000027c = some (.base .ECALL) := by rfl

/-- Fewer than four words: `a0 = 2`, then the `HALT` call. -/
theorem digest_abort {t : MachineState} (hpc : t.pc = 0x80000274) :
    ∃ u, Reaches Image.code t u ∧ Dead Image.code u := by
  obtain ⟨u, hr, h⟩ := Sym.BlockSpec.reaches b80000274_spec hpc trivial
  exact ⟨u, hr, dead_of_halt (by rw [b80000274_pc h]; exact digest_halt_fetch) (b80000274_x5 h)
    (by rw [b80000274_x10 h]; decide)⟩

theorem readWords_four (u : MachineState) (a : Word) :
    u.readWords a 4 = [u.getMem a, u.getMem (a + 8), u.getMem (a + 16), u.getMem (a + 24)] := by
  simp only [MachineState.readWords, BitVec.add_assoc]
  rfl

/-- **`Input::digest` meets its contract.** -/
theorem digest_spec : DigestSpec := by
  intro s hpc hpre
  have hsp := hpre.stack.bounds (by decide) (by decide)
  have ho := hpre.out
  have hoa := hpre.outAlign
  have hi := hpre.self
  have hia := hpre.selfAlign
  obtain ⟨t₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b800000e4_spec hpc (by
    rv_eval []
    valid_in hi [hi, hia])
  have k₀ := b800000e4_keeps h₀
  have hm₀ := b800000e4_mem_same h₀
  by_cases hz : s.getMem (s.getReg .x11 + 8) = 0
  · obtain ⟨u, hu, hd⟩ := digest_abort (b800000e4_pc_taken h₀ hz)
    exact ⟨u, hr₀.trans hu, Or.inr hd⟩
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800000ec_spec (b800000e4_pc_not_taken h₀ hz)
    trivial
  have k₁ := b800000ec_keeps h₁
  have hm₁ := b800000ec_mem_same h₁
  have hx12 : t₀.getReg .x12 = s.getMem (s.getReg .x11 + 8) := b800000e4_x12 h₀
  by_cases hlt : (t₀.getReg .x12).toNat < (4 : Word).toNat
  · obtain ⟨u, hu, hd⟩ := digest_abort (b800000ec_pc_taken h₁ hlt)
    exact ⟨u, hr₀.trans (hr₁.trans hu), Or.inr hd⟩
  have hlen : 4 ≤ (inputLen s (s.getReg .x11)).toNat := by
    have := Nat.not_lt.mp hlt
    rw [hx12] at this
    exact this
  obtain ⟨hp, hpa, hps⟩ := hpre.words hlen
  simp only [inputPtr] at hp hpa hps
  have e1 : t₁.getReg .x1 = s.getReg .x1 := by rw [k₁ .x1 (by decide), k₀ .x1 (by decide)]
  have e2 : t₁.getReg .x2 = s.getReg .x2 := by rw [k₁ .x2 (by decide), k₀ .x2 (by decide)]
  have e10 : t₁.getReg .x10 = s.getReg .x10 := by rw [k₁ .x10 (by decide), k₀ .x10 (by decide)]
  have e11 : t₁.getReg .x11 = s.getReg .x11 := by rw [k₁ .x11 (by decide), k₀ .x11 (by decide)]
  have e12 : t₁.getReg .x12 = s.getMem (s.getReg .x11 + 8) := by
    rw [k₁ .x12 (by decide), hx12]
  have em : ∀ a, t₁.getMem a = s.getMem a := fun a ↦ (hm₁ a).trans (hm₀ a)
  have hlo : stackLo t₁ digestStack = stackLo s digestStack := by simp only [stackLo, e2]
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800000f4_spec
      (b800000ec_pc_not_taken h₁ (Nat.not_lt.mp hlt))
    (digest_obl (by rw [e10]; exact ho) (by rw [e10]; exact hoa) (by rw [e11]; exact hi)
      (by rw [e11]; exact hia) (by rw [e11, em]; exact hp) (by rw [e11, em]; exact hpa)
      ⟨by rw [hlo]; exact hpre.stack.valid, by rw [e2]; exact hpre.stack.aligned⟩
      (by rw [e10, e11]; exact hpre.outSelf) (by rw [e10, hlo]; exact hpre.outStack)
      (by rw [e11, hlo]; exact hpre.selfStack) (by rw [e11, em, hlo]; exact hps))
  have k₂ := b800000f4_keeps h₂
  have w0 := h₂.memAt 3 (by decide)
  have w1 := h₂.memAt 2 (by decide)
  have w2 := h₂.memAt 1 (by decide)
  have w3 := h₂.memAt 0 (by decide)
  rv_eval [e10, e11, em, replaceBytes_eq] at w0 w1 w2 w3
  have pc := b800000f4_pc h₂
  have m4 := b800000f4_m_x11_8 h₂
  have m5 := b800000f4_m_x11_0 h₂
  rw [e11, e12] at m4
  rw [e11, em] at m5
  refine ⟨t₂, hr₀.trans (hr₁.trans hr₂), Or.inl ⟨?_, ?_, hlen, ?_, m5, m4, ?_⟩⟩
  · rw [pc, e1, returnAddress_eq]
  · intro r hr
    rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _), k₀ r (mem_of_mem hr _)]
  · rw [readWords_four, readWords_four, w0, w1, w2, w3]; rfl
  · intro a h1 h2 h3
    rw [h₂.frame a (by
      rv_eval [e2, e10, e11]
      and_intros <;> addr_omega [h1, h2, h3, hsp, ho, hi]), em]

end Rv64Verifier.Proofs.Bytecode
