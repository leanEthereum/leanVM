/-
  Rv64mc.Proof.Layout.Out

  The memory frame of a function that writes a caller's object (its `out`, such as an `sret` slot), which `rv_auto`
  leaves open (it builds frames of stack stores and calls only): a store into `out` (`frame_setMem_out`, and
  `Env.static_setMem` for the static data), each slot of an owned object being in `out`, apart from `NEXT` and from
  the static data (`owned_slot`).
-/

import Rv64mc.Core.Repr

namespace Rv64mc.Proof.Layout

open RiscvZkvm.Rv64

variable {env : Env}

/-- **A store into `out`** stays in the frame. -/
theorem frame_setMem_out {top b v : Word} {out : Word → Prop} {m N : MachineState} (h : env.Frame top out m N)
    (ho : out b) (hn : b ≠ env.nextAddr) : env.Frame top out m (N.setMem b v) :=
  h.trans (Env.Frame.setMem_out h.2.1 ho hn) (Nat.le_refl _) fun _ h => Or.inr (Or.inr (Or.inr h))

/-- **A slot of an owned object** is in it, not `NEXT`, and not in the static data. -/
theorem owned_slot {m : MachineState} {top a : Word} {n : Nat} (h : env.Owned m top a n)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hlim : env.stackLimit.toNat ≤ top.toNat) {k : Nat}
    (hk : k < n) :
    InRange a n (a + BitVec.ofNat 64 k) ∧ a + BitVec.ofNat 64 k ≠ env.nextAddr ∧
      ((a + BitVec.ofNat 64 k).toNat < env.staticLo.toNat ∨ env.staticHi.toNat ≤ (a + BitVec.ofNat 64 k).toNat) := by
  have hr : InRange a n (a + BitVec.ofNat 64 k) := by
    have := h.2
    unfold InRange; rw [toNat_add_ofNat (by omega)]; omega
  exact ⟨hr, h.not_next hnx hlim hr, h.not_static hnx hlim hr⟩

/-- `owned_slot` at offset zero. -/
theorem owned_slot0 {m : MachineState} {top a : Word} {n : Nat} (h : env.Owned m top a n)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hlim : env.stackLimit.toNat ≤ top.toNat) (hn : 0 < n) :
    InRange a n a ∧ a ≠ env.nextAddr ∧ (a.toNat < env.staticLo.toNat ∨ env.staticHi.toNat ≤ a.toNat) := by
  simpa using owned_slot h hnx hlim hn

end Rv64mc.Proof.Layout
