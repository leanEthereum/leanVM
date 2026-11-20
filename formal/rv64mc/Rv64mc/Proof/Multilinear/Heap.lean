/-
  Rv64mc.Proof.Multilinear.Heap

  The memory facts a function that builds a `Vec` needs and `rv_auto` does not state (it builds frames of stack
  stores and of calls without `out` only): a callee whose `out` lies in the caller's own stack (`frame_call_own`),
  a store into a block allocated since the entry (`frame_store_heap`), a caller's object apart from the stack and
  from what was allocated since (`owned_ne_stack`, `owned_ne_fresh`), and a stack slot as a number (`slot_toNat`).
-/

import Rv64mc.Core.Repr

namespace Rv64mc.Proof.Multilinear

open RiscvZkvm.Rv64

variable {env : Env}

/-- **A callee whose `out` lies in the caller's own stack** stays in the caller's frame. -/
theorem frame_call_own {top top' : Word} {out out' : Word → Prop} {m N X : MachineState}
    (h1 : env.Frame top out m N) (h2 : env.Frame top' out' N X) (ht : top'.toNat ≤ top.toNat)
    (ho : ∀ a, out' a → env.stackLimit.toNat ≤ a.toNat ∧ a.toNat < top.toNat) : env.Frame top out m X :=
  h1.trans h2 ht fun a h => Or.inl (ho a h)

/-- **A store into a block allocated since the entry** stays in the frame. -/
theorem frame_store_heap {top a v : Word} {out : Word → Prop} {m N : MachineState} (h : env.Frame top out m N)
    (hlo : (env.next m).toNat ≤ a.toNat) (hhi : a.toNat < (env.next N).toNat) :
    env.Frame top out m (N.setMem a v) := by
  have hne : env.nextAddr ≠ a := fun he => by have := env.layout; have := h.2.1; rw [← he] at hhi; omega
  have hn : env.next (N.setMem a v) = env.next N := by
    simp [Env.next, MachineState.getMem, MachineState.setMem, hne]
  refine ⟨by rw [hn]; exact h.1, by rw [hn]; exact h.2.1, fun b hb => ?_⟩
  have hba : b ≠ a := fun he => hb (Or.inr (Or.inl ⟨he ▸ hlo, by rw [hn, he]; exact hhi⟩))
  rw [MachineState.getMem_setMem_ne hba]
  exact h.2.2 b fun hw => hb (by unfold Env.MayWrite at hw ⊢; rw [hn]; exact hw)

/-- A store below the heap's end keeps `NEXT`. -/
theorem next_store_heap {a v : Word} {N : MachineState} (ha : a.toNat < env.heapEnd.toNat) :
    env.next (N.setMem a v) = env.next N := by
  have hne : env.nextAddr ≠ a := fun he => by have := env.layout; rw [← he] at ha; omega
  simp [Env.next, MachineState.getMem, MachineState.setMem, hne]

/-- A store below the heap's end keeps the static data. -/
theorem static_store_heap {a v : Word} {m : MachineState} (hs : env.Static m) (ha : a.toNat < env.heapEnd.toNat) :
    env.Static (m.setMem a v) :=
  Env.static_setMem hs (Or.inl (by have := env.layout; omega))

/-- **A caller's object is apart from the callee's stack.** -/
theorem owned_ne_stack {m : MachineState} {top a b s : Word} {n : Nat} (h : env.Owned m top a n)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hb : InRange a n b) (hs1 : env.stackLimit.toNat ≤ s.toNat)
    (hs2 : s.toNat < top.toNat) : b ≠ s := fun he => by
  have := env.layout; rw [he] at hb; unfold InRange at hb; rcases h.1 with h1 | h1 <;> omega

/-- **A caller's object is apart from what was allocated since its call.** -/
theorem owned_ne_fresh {m : MachineState} {top a b c : Word} {n : Nat} (h : env.Owned m top a n)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (hb : InRange a n b) (hc1 : (env.next m).toNat ≤ c.toNat)
    (hc2 : c.toNat < env.heapEnd.toNat) : b ≠ c := fun he => by
  have := env.layout; rw [he] at hb; unfold InRange at hb; rcases h.1 with h1 | h1 <;> omega

/-- A stack slot `t - k` as a number. -/
theorem slot_toNat {t c : Word} {k : Nat} (hc : c.toNat = 2 ^ 64 - k) (hk : k ≤ t.toNat) (hk0 : 0 < k) :
    (t + c).toNat = t.toNat - k := by
  rw [BitVec.toNat_add, hc]; have := t.isLt; omega

end Rv64mc.Proof.Multilinear
