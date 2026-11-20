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

namespace Rv64mc.Proof.Whir

open RiscvZkvm.Rv64

variable {env : Env}

/-- `owned_ne_slot` with the slot's depth read off its offset, for a discharger. -/
theorem owned_ne_slot' {m : MachineState} {top a c : Word} {n k need : Nat} (ho : env.Owned m top a n)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hk : k < n) (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hc : 2 ^ 64 - c.toNat ≤ need) : a + BitVec.ofNat 64 k ≠ top + c :=
  owned_ne_slot (d := 2 ^ 64 - c.toNat) ho hnx hk hstk (by have := c.isLt; omega) hc

theorem owned_ne_slot0' {m : MachineState} {top a c : Word} {n need : Nat} (ho : env.Owned m top a n)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hn : 0 < n) (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hc : 2 ^ 64 - c.toNat ≤ need) : a ≠ top + c := by
  simpa using owned_ne_slot' (k := 0) ho hnx hn hstk hc

end Rv64mc.Proof.Whir

/-- **Loads of an owned object past the function's own stack stores**: every `(N.setMem (top + c) v).getMem a` with
    `a` a word of the object `ho` names rewritten to `N.getMem a`, in the goal and every hypothesis. -/
macro "owned_loads" ho:term:max hnx:term:max hstk:term:max : tactic => `(tactic|
  simp (disch := first
    | (apply Rv64mc.Proof.Whir.slot_ne; decide)
    | (apply Rv64mc.Proof.Whir.owned_ne_slot' $ho $hnx _ $hstk <;>
        first | decide | (simp only [BitVec.toNat_ofNat]; omega))
    | (apply Rv64mc.Proof.Whir.owned_ne_slot0' $ho $hnx _ $hstk <;>
        first | decide | (simp only [BitVec.toNat_ofNat]; omega)))
    only [RiscvZkvm.Rv64.MachineState.getMem_setMem_ne] at *)

namespace Rv64mc.Proof.Whir

open RiscvZkvm.Rv64

variable {env : Env}

theorem keeps_refl {m : MachineState} {a : Word} {n : Nat} : Keeps m m a n := fun _ _ => rfl

/-- A slot below the stack top, its depth read off its offset. -/
theorem slot_ge' {top c : Word} {need : Nat} (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hc : 2 ^ 64 - c.toNat ≤ need) : env.stackLimit.toNat ≤ (top + c).toNat := by
  rcases Nat.eq_zero_or_pos c.toNat with h0 | h0
  · rw [BitVec.toNat_add, h0]; have := top.isLt; omega
  · exact slot_ge (d := 2 ^ 64 - c.toNat) hstk (by have := c.isLt; omega) hc

end Rv64mc.Proof.Whir

/-- **An object below the stack is kept by the function's own stack stores**: `Keeps m M a n` for `M` a chain of
    stores into the stack from `m`, from `hb : a.toNat + n ≤ env.stackLimit.toNat` and the stack bound `hstk`. -/
macro "keeps_stack" hb:term:max hstk:term:max : tactic => `(tactic| (
  repeat (refine Rv64mc.Keeps.trans ?_ (Rv64mc.Proof.Whir.keeps_slot $hb ?_))
  · exact Rv64mc.Proof.Whir.keeps_refl
  all_goals exact Rv64mc.Proof.Whir.slot_ge' $hstk (by simp only [BitVec.toNat_ofNat]; omega)))

/-- **A live object stays live across the function's own stack stores.** -/
macro "live_stack" hl:term:max hstk:term:max : tactic => `(tactic| (
  repeat (refine Rv64mc.Proof.Whir.live_setMem_stack ?_ ?_)
  · exact $hl
  all_goals exact Rv64mc.Proof.Whir.slot_ge' $hstk (by simp only [BitVec.toNat_ofNat]; omega)))

namespace Rv64mc.Proof.Whir

open RiscvZkvm.Rv64

variable {env : Env}

/-- A part of an owned object is owned. -/
theorem Owned.sub {m : MachineState} {top a : Word} {n k n' : Nat} (h : env.Owned m top a n) (hk : k + n' ≤ n) :
    env.Owned m top (a + BitVec.ofNat 64 k) n' := by
  have h2 := h.2
  rw [Env.Owned, toNat_add_ofNat (by omega)]
  refine ⟨?_, by omega⟩
  rcases h.1 with h1 | h1
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- A store into the stack below `top` keeps an object owned at `top`. -/
theorem keeps_slot_owned {m N : MachineState} {top a c v : Word} {n need : Nat} (ho : env.Owned m top a n)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hc : 2 ^ 64 - c.toNat ≤ need) (hc0 : 0 < c.toNat) : Keeps N (N.setMem (top + c) v) a n :=
  Keeps.setMem fun hr => by
    have h1 := slot_toNat (c := c) (d := 2 ^ 64 - c.toNat) hstk (by have := c.isLt; omega) hc
    unfold InRange at hr; rw [h1] at hr; have := env.layout; rcases ho.1 with h2 | h2 <;> omega

end Rv64mc.Proof.Whir

/-- **An owned object is kept by the function's own stack stores**: `Keeps m M a n` for `M` a chain of stores into
    the stack from `m`. -/
macro "keeps_stack_owned" ho:term:max hnx:term:max hstk:term:max : tactic => `(tactic| (
  repeat (refine Rv64mc.Keeps.trans ?_ (Rv64mc.Proof.Whir.keeps_slot_owned $ho $hnx $hstk ?_ ?_))
  · exact Rv64mc.Proof.Whir.keeps_refl
  all_goals first | decide | (simp only [BitVec.toNat_ofNat]; omega)))

namespace Rv64mc.Proof.Whir

open RiscvZkvm.Rv64

variable {env : Env}

/-- **A callee keeps an object owned by its caller**, from a stack top no higher than the caller's. -/
theorem keeps_owned_frame {m M m' : MachineState} {top t a : Word} {n : Nat} {out : Word → Prop}
    (ho : env.Owned m top a n) (hf : env.Frame t out M m') (hnext : (env.next m).toNat ≤ (env.next M).toNat)
    (ht : t.toNat ≤ top.toNat) (hlim : env.stackLimit.toNat ≤ t.toNat) (hout : ∀ b, InRange a n b → ¬ out b) :
    Keeps M m' a n := by
  rcases ho.1 with h1 | h1
  · exact fun b hb => hf.2.2 b fun hw => by
      unfold InRange at hb; have := env.layout; have := env.stackLimit.isLt
      rcases hw with hw | hw | hw | hw
      · have := hf.1; have := hf.2.1; omega
      · omega
      · subst hw; have := hf.1; have := hf.2.1; omega
      · exact hout b ⟨hb.1, hb.2⟩ hw
  · exact Env.Frame.keeps_above hf hlim (by omega) hout

/-- A prefix of an `E` slice. -/
theorem EListAt.take {m : MachineState} {a : Word} {es : List (Word × Word)} (h : EListAt m a es) (k : Nat) :
    EListAt m a (es.take k) :=
  ⟨by have := h.1; simp only [List.length_take]; have : min k es.length ≤ es.length := Nat.min_le_right _ _;
      simp only [Layouts.E.byteSize] at *; omega,
    fun j hj => by
      simp only [List.length_take] at hj
      simpa using h.2 j (by omega)⟩

end Rv64mc.Proof.Whir

namespace Rv64mc.Proof.Whir

open RiscvZkvm.Rv64

variable {env : Env}

theorem slot_lt' {top c : Word} {need : Nat} (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hc : 2 ^ 64 - c.toNat ≤ need) (hc0 : 0 < c.toNat) : (top + c).toNat < top.toNat :=
  slot_lt (d := 2 ^ 64 - c.toNat) hstk (by have := c.isLt; omega) (by have := c.isLt; omega) hc

theorem ofNat_le_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : BitVec.ofNat 64 a ≤ BitVec.ofNat 64 b) : a ≤ b := by
  rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  exact h

end Rv64mc.Proof.Whir

/-- **The frame of the function's own stack stores**: `env.Frame top Tactic.F m M` for `M` a chain of stores into
    the stack from `m`. -/
macro "frame_stack" hnx:term:max hstk:term:max : tactic => `(tactic| (
  repeat (refine Rv64mc.Tactic.frame_store ?_ ?_ ?_)
  · exact Rv64mc.Tactic.frame_refl $hnx
  all_goals first
    | exact Rv64mc.Proof.Whir.slot_ge' $hstk (by simp only [BitVec.toNat_ofNat]; omega)
    | exact Rv64mc.Proof.Whir.slot_lt' $hstk (by simp only [BitVec.toNat_ofNat]; omega) (by decide)))
