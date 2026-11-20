/-
  Rv64mc.Proof.Whir.Mem

  What `rv_auto` leaves of a function that writes a caller's object (an `sret` slot, `Spec.Whir.SretOut`): its
  own stack slots and the words of an owned object are apart (`owned_ne_slot`), so loads pass the other's stores;
  a store into the owned slot keeps the frame with that `out` and the static data (`sret_store`); and the frame of
  the function's own stores and calls, weakened to that `out` (`frame_own`).
-/

import Rv64mc.Core.Repr
import Rv64mc.Tactic.Frame

namespace Rv64mc.Proof.Whir

open RiscvZkvm.Rv64

variable {env : Env}

/-- A slot `top - d` of a function with `need ≥ d` bytes of stack. -/
theorem slot_toNat {top c : Word} {need d : Nat} (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hc : c.toNat = 2 ^ 64 - d) (hd : d ≤ need) : (top + c).toNat = top.toNat - d := by
  rw [BitVec.toNat_add, hc]; have := top.isLt; omega

/-- **A word of an owned object is not a slot of the stack below its owner's top.** -/
theorem owned_ne_slot {m : MachineState} {top a c : Word} {n k need d : Nat} (ho : env.Owned m top a n)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hk : k < n) (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hc : c.toNat = 2 ^ 64 - d) (hd : d ≤ need) : a + BitVec.ofNat 64 k ≠ top + c := by
  intro h
  have h1 := congrArg BitVec.toNat h
  rw [slot_toNat hstk hc hd, toNat_add_ofNat (by have := ho.2; omega)] at h1
  have := env.layout
  rcases ho.1 with h2 | h2 <;> omega

theorem owned_ne_slot0 {m : MachineState} {top a c : Word} {n need d : Nat} (ho : env.Owned m top a n)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hn : 0 < n) (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hc : c.toNat = 2 ^ 64 - d) (hd : d ≤ need) : a ≠ top + c := by
  simpa using owned_ne_slot (k := 0) ho hnx hn hstk hc hd

/-- **A store into an owned slot** keeps the frame whose `out` is the slot, and the static data. -/
theorem sret_store {m N : MachineState} {top a v : Word} {n k : Nat} (ho : env.Owned m top a n)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hlim : env.stackLimit.toNat ≤ top.toNat) (hk : k < n)
    (hf : env.Frame top (fun b => InRange a n b) m N ∧ env.Static N) :
    env.Frame top (fun b => InRange a n b) m (N.setMem (a + BitVec.ofNat 64 k) v) ∧
      env.Static (N.setMem (a + BitVec.ofNat 64 k) v) := by
  have hr : InRange a n (a + BitVec.ofNat 64 k) := by
    have := ho.2
    unfold InRange; rw [toNat_add_ofNat (by omega)]; omega
  exact ⟨hf.1.trans (Env.Frame.setMem_out hf.1.2.1 hr (ho.not_next hnx hlim hr)) (Nat.le_refl _)
      fun _ h => Or.inr (Or.inr (Or.inr h)),
    Env.static_setMem hf.2 (ho.not_static hnx hlim hr)⟩

theorem sret_store0 {m N : MachineState} {top a v : Word} {n : Nat} (ho : env.Owned m top a n)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hlim : env.stackLimit.toNat ≤ top.toNat) (hn : 0 < n)
    (hf : env.Frame top (fun b => InRange a n b) m N ∧ env.Static N) :
    env.Frame top (fun b => InRange a n b) m (N.setMem a v) ∧ env.Static (N.setMem a v) := by
  simpa using sret_store (k := 0) ho hnx hlim hn hf

/-- The frame of a function's own stack stores (`M0`) and of the calls after them (`m1`), weakened to any `out`. -/
theorem frame_own {top top' : Word} {out : Word → Prop} {m M0 m1 : MachineState}
    (h0 : env.Frame top Tactic.F m M0) (h1 : env.Frame top' (fun _ => False) M0 m1) (ht : top'.toNat ≤ top.toNat) :
    env.Frame top out m m1 :=
  Tactic.frame_weaken (Tactic.frame_call h0 h1 ht)

end Rv64mc.Proof.Whir

namespace Rv64mc.Proof.Whir

open RiscvZkvm.Rv64

variable {env : Env}

/-- A store into the stack keeps what lives in the heap. -/
theorem live_setMem_stack {N : MachineState} {a s v : Word} {n : Nat} (h : env.Live N a n)
    (hs : env.stackLimit.toNat ≤ s.toNat) : env.Live (N.setMem s v) a n := by
  unfold Env.Live at *; rw [Env.next_setMem_stack hs]; exact h

/-- A store into the stack keeps an `E` slice in the heap. -/
theorem elist_setMem_stack {N : MachineState} {a s v : Word} {es : List (Word × Word)}
    (h : EListAt N a es) (hl : env.Live N a (Layouts.E.byteSize * es.length))
    (hnx : (env.next N).toNat ≤ env.heapEnd.toNat) (hs : env.stackLimit.toNat ≤ s.toNat) :
    EListAt (N.setMem s v) a es :=
  h.keep (Keeps.setMem fun hr => by
    have := env.layout; unfold Env.Live at hl; unfold InRange at hr; omega)

/-- Stores into the stack keep what lies below it. -/
theorem keeps_slot {N : MachineState} {a s v : Word} {n : Nat} (hb : a.toNat + n ≤ env.stackLimit.toNat)
    (hs : env.stackLimit.toNat ≤ s.toNat) : Keeps N (N.setMem s v) a n :=
  Keeps.setMem fun hr => by unfold InRange at hr; omega

/-- A slot of the stack lies at or above its limit. -/
theorem slot_ge {top c : Word} {need d : Nat} (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hc : c.toNat = 2 ^ 64 - d) (hd : d ≤ need) : env.stackLimit.toNat ≤ (top + c).toNat := by
  rw [slot_toNat hstk hc hd]; omega

/-- A slot lies below the stack top. -/
theorem slot_lt {top c : Word} {need d : Nat} (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hc : c.toNat = 2 ^ 64 - d) (h0 : 0 < d) (hd : d ≤ need) : (top + c).toNat < top.toNat := by
  rw [slot_toNat hstk hc hd]; omega

/-- A lower slot of the stack is below a higher one. -/
theorem slot_le {top c c' : Word} {need d d' : Nat} (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hc : c.toNat = 2 ^ 64 - d) (hc' : c'.toNat = 2 ^ 64 - d') (hd : d ≤ need) (hd' : d' ≤ d) :
    top + c ≤ top + c' := by
  rw [BitVec.le_def, slot_toNat hstk hc hd, slot_toNat hstk hc' (by omega)]; omega

/-- Two slots at different offsets are apart. -/
theorem slot_ne {top c c' : Word} (h : c ≠ c') : top + c ≠ top + c' := fun he => h (by
  rwa [BitVec.add_right_inj] at he)

/-- Two words of an object at different offsets are apart. -/
theorem off_ne {a : Word} {i j : Nat} (hi : a.toNat + i < 2 ^ 64) (hj : a.toNat + j < 2 ^ 64) (h : i ≠ j) :
    a + BitVec.ofNat 64 i ≠ a + BitVec.ofNat 64 j := fun he => h (by
  have := congrArg BitVec.toNat he; rw [toNat_add_ofNat hi, toNat_add_ofNat hj] at this; omega)

theorem off_ne0 {a : Word} {j : Nat} (hj : a.toNat + j < 2 ^ 64) (h : 0 < j) : a + BitVec.ofNat 64 j ≠ a := by
  simpa using off_ne (i := j) (j := 0) hj (by omega) (by omega)

/-- A live object lies below the stack. -/
theorem live_below {m : MachineState} {a : Word} {n : Nat} (hl : env.Live m a n)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) : a.toNat + n ≤ env.stackLimit.toNat := by
  have := env.layout; unfold Env.Live at hl; omega

/-- The header of a `Vec` at `a + o`: its pointer and its length, at the addresses the code computes. -/
theorem vec_fields {α : Type} {P : MachineState → Word → List α → Prop} {m : MachineState} {a ptr : Word}
    {o cap : Nat} {xs : List α} (h : VecAt P m (a + BitVec.ofNat 64 o) ptr cap xs) :
    m.getMem (a + BitVec.ofNat 64 (o + Layouts.Vec.ptr)) = ptr ∧
      m.getMem (a + BitVec.ofNat 64 (o + Layouts.Vec.len)) = BitVec.ofNat 64 xs.length ∧
      m.getMem (a + BitVec.ofNat 64 (o + Layouts.Vec.cap)) = BitVec.ofNat 64 cap := by
  have e : ∀ k, a + BitVec.ofNat 64 (o + k) = a + BitVec.ofNat 64 o + BitVec.ofNat 64 k := fun k => by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  refine ⟨?_, ?_, ?_⟩ <;> rw [e]
  · exact h.ptr_eq
  · exact h.len_eq
  · exact h.cap_eq

end Rv64mc.Proof.Whir
