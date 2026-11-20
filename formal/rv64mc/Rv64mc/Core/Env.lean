/-
  Rv64mc.Core.Env

  What every function's contract may assume of the program around it, fixed at link time and abstract in every
  function's proof (`Env`): an invariant of the static data no function writes (`Static`, which reads only the
  memory in `[staticLo, staticHi)`), the bump allocator's pointer `NEXT` (its address `nextAddr`, the heap's end
  `heapEnd`), and the lowest address the stack reaches (`stackLimit`), in the guest's order: the heap, the static
  data, `NEXT`, the stack (`guest/link.x`, `guest/src/main.rs`).

  A call may write its own stack (`[stackLimit, top)`), what it allocates (`[NEXT before, NEXT after)`), `NEXT`, and
  the addresses its contract names (`Out`); `Env.Frame` says it keeps every other word, and that `NEXT` only grows,
  within the heap. A caller's objects lie in none of these: its frame at or above the callee's `top`, its heap
  objects below `NEXT`, its static data in `[staticLo, staticHi)`.

  ## Main definitions

  * `Env`, `Env.next`, `Env.MayWrite`, `Env.Frame`

  ## Main results

  * `Env.Frame.trans`: frames compose along calls
-/

import LprogRiscV.Lsym

namespace Rv64mc

open RiscvZkvm.Rv64

/-- The link-time environment of every contract. -/
structure Env where
  /-- The invariant every function keeps: what the static data hold. -/
  Static : MachineState → Prop
  /-- The first address `Static` reads. -/
  staticLo : Word
  /-- The address after the last one `Static` reads. -/
  staticHi : Word
  /-- `Static` reads only the memory in `[staticLo, staticHi)`. -/
  static_frame : ∀ m m' : MachineState,
    (∀ a : Word, staticLo.toNat ≤ a.toNat → a.toNat < staticHi.toNat → m'.getMem a = m.getMem a) →
      Static m → Static m'
  /-- The address of the bump allocator's pointer `NEXT`. -/
  nextAddr : Word
  /-- The end of the heap: `NEXT` never passes it. -/
  heapEnd : Word
  /-- The lowest address the stack reaches. -/
  stackLimit : Word
  /-- The heap, the static data, `NEXT` and the stack, in this order. -/
  layout : heapEnd.toNat ≤ staticLo.toNat ∧ staticLo.toNat ≤ staticHi.toNat ∧ staticHi.toNat ≤ nextAddr.toNat ∧
    nextAddr.toNat + 8 ≤ stackLimit.toNat

namespace Env

variable (env : Env)

/-- The value of `NEXT` in `m`. -/
def next (m : MachineState) : Word := m.getMem env.nextAddr

/-- The words a call from `m` to `m'` with stack top `top` may change: its stack, what it allocates, `NEXT`, and
    `out`. -/
def MayWrite (top : Word) (out : Word → Prop) (m m' : MachineState) (a : Word) : Prop :=
  (env.stackLimit.toNat ≤ a.toNat ∧ a.toNat < top.toNat) ∨
    ((env.next m).toNat ≤ a.toNat ∧ a.toNat < (env.next m').toNat) ∨ a = env.nextAddr ∨ out a

/-- **The memory frame of a call**: `NEXT` grows and stays within the heap, and every word the call may not change
    is kept. -/
def Frame (top : Word) (out : Word → Prop) (m m' : MachineState) : Prop :=
  (env.next m).toNat ≤ (env.next m').toNat ∧ (env.next m').toNat ≤ env.heapEnd.toNat ∧
    ∀ a, ¬ env.MayWrite top out m m' a → m'.getMem a = m.getMem a

variable {env}

/-- **Frames compose**: a callee's frame, from a stack top no higher, with what it may write among what the caller
    may, inside the caller's. -/
theorem Frame.trans {top top' : Word} {out out' : Word → Prop} {m m1 m2 : MachineState}
    (h1 : env.Frame top out m m1) (h2 : env.Frame top' out' m1 m2) (htop : top'.toNat ≤ top.toNat)
    (hout : ∀ a, out' a → env.MayWrite top out m m2 a) : env.Frame top out m m2 := by
  obtain ⟨g1, e1, k1⟩ := h1
  obtain ⟨g2, e2, k2⟩ := h2
  refine ⟨by omega, e2, fun a ha => ?_⟩
  have ha1 : ¬ env.MayWrite top out m m1 a := by
    intro h; apply ha
    rcases h with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h.1, by omega⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have ha2 : ¬ env.MayWrite top' out' m1 m2 a := by
    intro h; apply ha
    rcases h with h | h | h | h
    · exact Or.inl ⟨h.1, by omega⟩
    · exact Or.inr (Or.inl ⟨by omega, h.2⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact hout a h
  rw [k2 a ha2, k1 a ha1]

end Env

end Rv64mc
