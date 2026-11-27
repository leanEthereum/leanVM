/-
  Rv64mc.Proof.Field.ESumCopiedSafeT

  `E::sum` over a copied slice iterator, for safety (`SafeT`): from the iterator's two pointers (`a0`, `a1`) `len`
  elements apart (`a1 = a0 + (len <<< 4)`, as a caller computes it from a vector's header), the slice empty, or
  allocated (`Live`), in a window and 8-byte aligned, it returns. Empty, its first comparison returns at once,
  whatever the pointer (`empty`); nonempty, `ESumCopiedT.specT` at the elements in memory (`elist`). `ESumCopiedT`
  asks `Live` of an empty slice's pointer too, which a vector's representation (`VecT`) does not give when its
  capacity is `0`.

  ## Main definitions

  * `PreS`, `SafeT`

  ## Main results

  * `elist`, `empty`, `safe`
-/

import Rv64mc.Proof.Field.ESumCopiedT
import Rv64mc.Proof.Runtime.WinT

namespace Rv64mc.Proof.Field.ESumCopiedSafeT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Gen.Verifier.Field.E.SumCopiedIterE (Link tmpl)

/-- The precondition: the end `len` elements past the start, the slice empty or allocated, in a window and 8-byte
    aligned. -/
def PreS (env : Env) (len : Word) (regs : Reg → Word) (m : MachineState) : Prop :=
  regs .x11 = regs .x10 + (len <<< 4) ∧ (len = 0#64 ∨
    env.Live m (regs .x10) (16 * len.toNat) ∧ InWin env (regs .x10) (16 * len.toNat) ∧ (regs .x10).toNat % 8 = 0)

/-- **`E::sum` over a copied slice iterator is safe**: from `PreS` it returns, writing nothing outside its stack. -/
def SafeT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ len, HoldsT env p i need (PreS env len) (fun _ _ _ _ => True)

/-- The `n` elements at `a` are there. -/
theorem elist {m : MachineState} {a : Word} {n : Nat} (h : a.toNat + 16 * n < 2 ^ 64) :
    EListAt m a (List.ofFn fun j : Fin n =>
      (m.getMem (a + BitVec.ofNat 64 (16 * j.1)), m.getMem (a + BitVec.ofNat 64 (16 * j.1) + 8#64))) := by
  refine ⟨by simpa [Layouts.E.byteSize] using h, fun k hk => ?_⟩
  simp [EAt, Layouts.E.c0, Layouts.E.c1, Layouts.E.byteSize]

/-- An empty iterator: the first comparison returns. -/
theorem empty (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (need : Nat) :
    HoldsT env p i need (fun regs _ => regs .x11 = regs .x10) (fun _ _ _ _ => True) := by
  rv_autoT hp
  exact absurd rfl hc

theorem safe (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (need : Nat)
    (h : ESumCopiedT.specT env p i need) : SafeT env p i need := by
  intro len Q ret top rest regs m ⟨⟨he, hs, hst, hn, ⟨h11, hc⟩, hal⟩, hW⟩ hstop hk
  rcases hc with h0 | ⟨hl, hw, ha⟩
  · subst h0
    exact empty env p i L hp need Q ret top rest regs m
      ⟨⟨he, hs, hst, hn, show regs .x11 = regs .x10 by rw [h11]; exact BitVec.add_zero _, hal⟩, hW⟩ hstop hk
  · have hlt := hw.lt
    refine h _ Q ret top rest regs m ⟨⟨he, hs, hst, hn, ⟨⟨elist (m := m) (n := len.toNat) (by omega), ?_, ?_⟩,
      .inr ⟨?_, ha⟩⟩, hal⟩, hW⟩ hstop
      fun r' m' ⟨⟨ha', hf, hs', _⟩, hc⟩ => hk r' m' ⟨⟨ha', hf, hs', trivial⟩, hc⟩
    · rw [h11, List.length_ofFn]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
      omega
    · simpa [Layouts.E.byteSize] using hl
    · simpa using hw

end Rv64mc.Proof.Field.ESumCopiedSafeT

/-- info: 'Rv64mc.Proof.Field.ESumCopiedSafeT.safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Field.ESumCopiedSafeT.safe
