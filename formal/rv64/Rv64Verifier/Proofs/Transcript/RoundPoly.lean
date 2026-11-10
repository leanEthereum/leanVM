import Rv64Verifier.Proofs.Transcript.TFrame
import Rv64Verifier.Proofs.Transcript.Samples
import Rv64Verifier.Proofs.Multilinear.Basic
import Rv64Verifier.Blocks.F44

/-!
# `Transcript::sumcheck_round_poly`

```rust
let Some(eq_factor) = eq_factor else {
    let constant = self.next_scalar()?;
    let tail = self.next_scalars(count - 2)?;
    return Ok([vec![constant, claim + E::sum(tail.iter().copied())], tail].concat());
};
let tail = self.next_scalars(count - 1)?;
Ok([vec![claim + eq_factor * E::sum(tail.iter().copied())], tail].concat())
```

compiled at `0x8000c334` (`Blocks/F44.lean`), with `S` the entry's `sp`: a 160-byte frame saving
`ra`, `s0`..`s8` (`entry`), then on `eq_factor`'s tag. `Some`: `next_scalars(count - 1)` into
`S - 152` (`someTail`), 24 bytes, the tail's sum (`E::sum`, the XOR loop at `0x8000c408`), the
product by `eq_factor` into `S - 104`, plus `claim` (`someMul`). `None`: `next_scalar` into
`S - 152` (`noneConst`), `next_scalars(count - 2)` (`noneTail`), 48 bytes, the constant and
`claim` plus the sum (the loop at `0x8000c554`). Both make the two `Vec`s at `S - 152` and call
`concat` into the result (`finish`); an error goes to the result with `-1` in its capacity
(`exitErr`). `0x8000c5e4` returns.

This file holds the frame (`Fr`, what is written before the result: `V`), the return and the
error exit; `RoundPolySome*`, `RoundPolyNone*`, `RoundPolyFinish` the paths, `RoundPolySpec` the
whole.
-/

namespace Rv64Verifier.Transcript.RoundPoly
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F44
  Rv64Verifier.Contracts LeanVM.Protocol.Verifier
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-! ## The mirror, read step by step -/

theorem roundPoly_some_run (count : ℕ) (claim f : E) (T : TState) :
    (TM.sumcheckRoundPoly count claim (some f)).run T =
      ((TM.nextScalars (count - 1)).run T).bind fun r ↦
        some ([claim + f * sumE r.1] ++ r.1, r.2) := by
  simp only [TM.sumcheckRoundPoly, StateT.run_bind, StateT.run_pure]
  rfl

theorem roundPoly_none_run (count : ℕ) (claim : E) (T : TState) :
    (TM.sumcheckRoundPoly count claim none).run T =
      (TM.nextScalar.run T).bind fun p ↦ ((TM.nextScalars (count - 2)).run p.2).bind fun r ↦
        some ([p.1, claim + sumE r.1] ++ r.1, r.2) := by
  simp only [TM.sumcheckRoundPoly, StateT.run_bind, StateT.run_pure]
  rfl

theorem sumE_snoc (l : List E) (x : E) : sumE (l ++ [x]) = sumE l + x := by
  simp only [sumE, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem limbs_zero : Model.limbs (0 : E) = (0, 0, 0) := by
  have h := limbs_add (0 : E) 0
  rw [add_zero] at h
  rw [h]
  simp only [BitVec.xor_self]
  rfl

/-- The call's mirror. -/
def mirror (s : MachineState) : TM (List E) :=
  TM.sumcheckRoundPoly (s.getReg .x12).toNat (eAt s (s.getReg .x13)) (optEAt s (s.getReg .x14))

/-! ## Frames -/

abbrev W (s u : MachineState) : Word → Prop := TW 24 roundPolyStack s u

/-- What the function writes before its result: the sponge and offsets, the stack, `NEXT` and the
heap allocated. -/
def V (s u : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x11 + 8) 344 ∨ TLow roundPolyStack s (heapNext u) a

theorem V.toW {s u : MachineState} {a : Word} (h : V s u a) : W s u a := by
  rcases h with h | h
  · exact Or.inr (Or.inl h)
  · exact TLow.toW (Nat.le_refl _) h

theorem V.mono {s u v : MachineState} {a : Word} (h : heapNext u ≤ heapNext v) (hw : V s u a) :
    V s v a := by
  rcases hw with hw | hw | hw | hw
  · exact Or.inl hw
  · exact Or.inr (Or.inl hw)
  · exact Or.inr (Or.inr (Or.inl hw))
  · exact Or.inr (Or.inr (Or.inr ⟨hw.1, Nat.lt_of_lt_of_le hw.2 h⟩))

theorem bounds {s : MachineState} (h : RoundPolyPre s) :
    0xa0000000 + roundPolyStack ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000000 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧
      (stackLo s roundPolyStack).toNat = (s.getReg .x2).toNat - roundPolyStack :=
  h.toTPre.bounds (by decide) (by decide)

/-- A region the precondition keeps apart from the transcript, the stack and the free heap misses
`V`. -/
theorem V.miss {s u : MachineState} (hhi : heapNext u ≤ heapEnd) {lo : Word} {m : Nat}
    (h1 : Apart lo m (s.getReg .x11 + 8) 344) (h2 : Apart lo m (stackLo s roundPolyStack) roundPolyStack)
    (h3 : Outside s lo m) (hn : lo.toNat + m ≤ 2 ^ 64) : Misses (V s u) lo m := fun y hy hw ↦ by
  rcases hw with hw | hw | hw | hw <;> addr_omega [hy, hw, h1, h2, h3, hn, hhi]

/-- The callee-saved registers the function never touches. -/
def keptRegs : List Reg := [.x25, .x26, .x27]

/-- Inside the frame: `sp`, and the saved registers in place. -/
structure Saved (s u : MachineState) : Prop where
  x2 : u.getReg .x2 = s.getReg .x2 - 160
  kept : ∀ r ∈ keptRegs, u.getReg r = s.getReg r
  ra : u.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : u.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s1 : u.getMem (s.getReg .x2 - 24) = s.getReg .x9
  s2 : u.getMem (s.getReg .x2 - 32) = s.getReg .x18
  s3 : u.getMem (s.getReg .x2 - 40) = s.getReg .x19
  s4 : u.getMem (s.getReg .x2 - 48) = s.getReg .x20
  s5 : u.getMem (s.getReg .x2 - 56) = s.getReg .x21
  s6 : u.getMem (s.getReg .x2 - 64) = s.getReg .x22
  s7 : u.getMem (s.getReg .x2 - 72) = s.getReg .x23
  s8 : u.getMem (s.getReg .x2 - 80) = s.getReg .x24

theorem Saved.step {s u v : MachineState} (h : Saved s u) (hS : 80 ≤ (s.getReg .x2).toNat)
    (x2 : v.getReg .x2 = u.getReg .x2) (kept : ∀ r ∈ keptRegs, v.getReg r = u.getReg r)
    (mem : ∀ y : Word, (s.getReg .x2).toNat - 80 ≤ y.toNat → y.toNat + 8 ≤ (s.getReg .x2).toNat →
      v.getMem y = u.getMem y) : Saved s v where
  x2 := x2.trans h.x2
  kept := fun r hr ↦ (kept r hr).trans (h.kept r hr)
  ra := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.ra]
  s0 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s0]
  s1 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s1]
  s2 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s2]
  s3 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s3]
  s4 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s4]
  s5 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s5]
  s6 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s6]
  s7 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s7]
  s8 := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.s8]

/-- The state inside the function: the frame, the result's address in `s0`, what was written so
far (`V`), the heap. -/
structure Fr (s u : MachineState) : Prop where
  saved : Saved s u
  x8 : u.getReg .x8 = s.getReg .x10
  heap : HeapOk u
  mono : heapNext s ≤ heapNext u
  frame : DFrame s u (V s u)

theorem Fr.same {s u v : MachineState} (h : Fr s u) (hS : 80 ≤ (s.getReg .x2).toNat)
    (hr : ∀ r ∈ [Reg.x2, .x8] ++ keptRegs, v.getReg r = u.getReg r)
    (hm : ∀ a, v.getMem a = u.getMem a) : Fr s v := by
  have nx : heapNext v = heapNext u := by simp only [heapNext, hm]
  exact ⟨h.saved.step hS (hr .x2 (by decide)) (fun r h' ↦ hr r (by simp [h'])) fun y _ _ ↦ hm y,
    (hr .x8 (by decide)).trans h.x8, ⟨nx ▸ h.heap.lo, nx ▸ h.heap.hi⟩, nx ▸ h.mono,
    (h.frame.mono fun a h ↦ V.mono (Nat.le_of_eq nx.symm) h).trans (DFrame.of_same hm _)
      fun _ h ↦ h⟩

/-- What the function has not written: the claim, `eq_factor`, the result. -/
theorem Fr.keep {s u : MachineState} (h : Fr s u) {y : Word}
    (h1 : Apart y 8 (s.getReg .x11 + 8) 344)
    (h2 : Apart y 8 (stackLo s roundPolyStack) roundPolyStack) (h3 : Outside s y 8)
    (hn : y.toNat + 8 ≤ 2 ^ 64) : u.getMem y = s.getMem y :=
  h.frame y ((V.miss h.heap.hi h1 h2 h3 hn).bytes (Nat.le_refl _) (Nat.le_refl _) hn)

theorem Fr.claim {s u : MachineState} (hpre : RoundPolyPre s) (h : Fr s u) {k : Nat} (hk : k < 3) :
    u.getMem (s.getReg .x13 + BitVec.ofNat 64 (8 * k)) =
      s.getMem (s.getReg .x13 + BitVec.ofNat 64 (8 * k)) := by
  have hc := hpre.claim
  have hS := hpre.self.self
  exact h.keep (by addr_omega [hc, hpre.claimSelf, hS, hk])
    (by addr_omega [hc, hpre.claimStack, hk]) (by addr_omega [hc, hpre.claimFree, hk])
    (by addr_omega [hc, hk])

theorem Fr.eqf {s u : MachineState} (hpre : RoundPolyPre s) (h : Fr s u) {k : Nat} (hk : k < 4) :
    u.getMem (s.getReg .x14 + BitVec.ofNat 64 (8 * k)) =
      s.getMem (s.getReg .x14 + BitVec.ofNat 64 (8 * k)) := by
  have hc := hpre.eqFactor
  have hS := hpre.self.self
  exact h.keep (by addr_omega [hc, hpre.eqFactorSelf, hS, hk])
    (by addr_omega [hc, hpre.eqFactorStack, hk]) (by addr_omega [hc, hpre.eqFactorFree, hk])
    (by addr_omega [hc, hk])

theorem Fr.transcriptAt {s u v : MachineState} (hpre : RoundPolyPre s) (hu : Fr s u)
    (hv : heapNext v ≤ heapEnd) (G : DFrame u v (TLow roundPolyStack s (heapNext v))) {T : TState}
    (hT : TranscriptAt u (s.getReg .x11) T) : TranscriptAt v (s.getReg .x11) T :=
  TLow.transcriptAt hpre.toTPre hv hu.heap.hi (hu.frame.mono fun _ h ↦ h.toW) G hT

/-! ## The return -/

/-- `0x8000c5e4`: the saved registers back, return. -/
theorem epilogue {s u : MachineState} (hpre : RoundPolyPre s) (hpc : u.pc = 0x8000c5e4)
    (h : Saved s u) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      ∀ a, t.getMem a = u.getMem a := by
  have hb := bounds hpre
  obtain ⟨t, hr, h₁⟩ := Sym.BlockSpec.reaches b8000c5e4_spec hpc (by
    rv_eval [h.x2]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k := b8000c5e4_keeps h₁
  have pc := b8000c5e4_pc h₁
  have y2 := b8000c5e4_x2 h₁
  have y8 := b8000c5e4_x8 h₁
  have y9 := b8000c5e4_x9 h₁
  have y18 := b8000c5e4_x18 h₁
  have y19 := b8000c5e4_x19 h₁
  have y20 := b8000c5e4_x20 h₁
  have y21 := b8000c5e4_x21 h₁
  have y22 := b8000c5e4_x22 h₁
  have y23 := b8000c5e4_x23 h₁
  have y24 := b8000c5e4_x24 h₁
  rv_eval [h.x2] at pc y2 y8 y9 y18 y19 y20 y21 y22 y23 y24
  refine ⟨t, hr, by rw [pc, h.ra, returnAddress_eq], ?_, b8000c5e4_mem_same h₁⟩
  intro r hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact y2
  · rw [y8, h.s0]
  · rw [y9, h.s1]
  · rw [y18, h.s2]
  · rw [y19, h.s3]
  · rw [y20, h.s4]
  · rw [y21, h.s5]
  · rw [y22, h.s6]
  · rw [y23, h.s7]
  · rw [y24, h.s8]
  all_goals rw [k _ (by decide), h.kept _ (by decide)]

/-- At `0x8000c5e4` after an error: the result's capacity `-1`, and the mirror fails. -/
structure ErrState (s u : MachineState) : Prop where
  saved : Saved s u
  heap : HeapOk u
  mono : heapNext s ≤ heapNext u
  frame : DFrame s u (W s u)
  cap : vecCap u (s.getReg .x10) = errNiche
  err : u.getMem (s.getReg .x10 + 8) ≠ errNiche
  fails : ∀ T, TranscriptAt s (s.getReg .x11) T → (mirror s).run T = none

theorem exitErr {s u : MachineState} (hpre : RoundPolyPre s) (hpc : u.pc = 0x8000c5e4)
    (h : ErrState s u) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧ RoundPolyPost s t := by
  obtain ⟨t, hr, pc, pres, hm⟩ := epilogue hpre hpc h.saved
  have nx : heapNext t = heapNext u := by simp only [heapNext, hm]
  have hc : vecCap t (s.getReg .x10) = errNiche := by simp only [vecCap, hm]; exact h.cap
  refine ⟨t, hr, pc, pres, ⟨nx ▸ h.heap.lo, nx ▸ h.heap.hi⟩, nx ▸ h.mono, fun T hT ↦ ?_,
    (h.frame.mono fun a h ↦ TW.mono (Nat.le_of_eq nx.symm) h).trans (DFrame.of_same hm _)
      fun _ h ↦ h, fun hne ↦ absurd hc hne, fun _ ↦ by rw [hm]; exact h.err⟩
  have e := h.fails T hT
  simp only [mirror] at e
  rw [e]
  simp only [vecCap, hm]
  exact h.cap

/-- An error block (`0x8000c4ac`, `0x8000c5c8`, `0x8000c5d8`): the result written, `-1` in its
capacity. -/
theorem ErrState.of_write {s u v : MachineState} (hpre : RoundPolyPre s) (h : Fr s u)
    (hr : ∀ r ∈ [Reg.x2] ++ keptRegs, v.getReg r = u.getReg r) (hm : MemFrame u v (s.getReg .x10) 24) (hc : v.getMem (s.getReg .x10) = errNiche)
    (h8 : v.getMem (s.getReg .x10 + 8) ≠ errNiche)
    (hn : ∀ T, TranscriptAt s (s.getReg .x11) T → (mirror s).run T = none) : ErrState s v := by
  have hb := bounds hpre
  have ho := hpre.out
  have nx : heapNext v = heapNext u := by
    simp only [heapNext]; rw [hm _ (by addr_omega [ho, hpre.outFree])]
  exact {
    saved := h.saved.step (by addr_omega [hb]) (hr .x2 (by decide)) (fun r h' ↦ hr r (by simp [h']))
      fun y h1 h2 ↦
      hm y (by addr_omega [h1, h2, hb, ho, hpre.outStack])
    heap := ⟨nx ▸ h.heap.lo, nx ▸ h.heap.hi⟩
    mono := nx ▸ h.mono
    frame := (h.frame.mono fun a h ↦ (V.mono (Nat.le_of_eq nx.symm) h).toW).trans
      (DFrame.of_memFrame hm) fun a h ↦ Or.inl h
    cap := hc
    err := h8
    fails := hn }

end Rv64Verifier.Transcript.RoundPoly
