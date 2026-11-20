/-
  Rv64mc.Tactic.Frame

  The facts about `Holds`'s memory frame (`Env.Frame`, `Core/Env.lean`) that `rv_sym` uses, in the forms it states
  them: a function's own stack slots (`t + c` below its stack top `t`, which `Holds.pre` puts `need` bytes above
  `env.stackLimit`), the room a callee's stack needs, a frame that writes nothing beyond the stack and the heap
  (`out` empty, `F`) built store by store and call by call, and what such a frame keeps. The side conditions on
  offsets are Booleans the kernel evaluates (`slotOk`, `roomOk`).

  ## Main results

  * `slot_ge`, `slot_lt`, `slot_le`, `room`, `room0`: stack slots and a callee's room
  * `frame_refl`, `frame_store`, `frame_call`, `frame_weaken`: a function's frame, store by store and call by call
  * `static_of_frame`, `frame_above`: what a frame without `out` keeps
-/

import Rv64mc.Core.Holds

namespace Rv64mc.Tactic

open RiscvZkvm.Rv64

/-- A negative offset `c` (signed) of at most `need` bytes. -/
def slotOk (need : Nat) (c : BitVec 64) : Bool := decide (c.toInt < 0 ∧ 0 ≤ (need : Int) + c.toInt)

/-- A non-positive offset `c` that leaves `need'` of the `need` bytes. -/
def roomOk (need need' : Nat) (c : BitVec 64) : Bool := decide (c.toInt ≤ 0 ∧ (need' : Int) - c.toInt ≤ need)

theorem toNat_add_neg {t c : BitVec 64} (h0 : c.toInt ≤ 0) (h1 : 0 ≤ (t.toNat : Int) + c.toInt) :
    ((t + c).toNat : Int) = t.toNat + c.toInt := by
  rw [BitVec.toNat_add]
  have := c.isLt
  have := t.isLt
  rw [BitVec.toInt_eq_toNat_cond] at h0 h1 ⊢
  by_cases hc : 2 * c.toNat < 2 ^ 64 <;> simp only [hc, ite_true, ite_false] at h0 h1 ⊢ <;> omega

theorem slot_ge {S need : Nat} {t c : BitVec 64} (h : S + need ≤ t.toNat) (hc : slotOk need c = true) :
    S ≤ (t + c).toNat := by
  simp only [slotOk, decide_eq_true_eq] at hc
  have := toNat_add_neg (t := t) (c := c) (by omega) (by omega); omega

theorem slot_lt {S need : Nat} {t c : BitVec 64} (h : S + need ≤ t.toNat) (hc : slotOk need c = true) :
    (t + c).toNat < t.toNat := by
  simp only [slotOk, decide_eq_true_eq] at hc
  have := toNat_add_neg (t := t) (c := c) (by omega) (by omega); omega

theorem slot_le {S need : Nat} {t c : BitVec 64} (h : S + need ≤ t.toNat) (hc : slotOk need c = true) :
    (t + c).toNat ≤ t.toNat := Nat.le_of_lt (slot_lt h hc)

theorem room {S need need' : Nat} {t c : BitVec 64} (h : S + need ≤ t.toNat) (hc : roomOk need need' c = true) :
    S + need' ≤ (t + c).toNat := by
  simp only [roomOk, decide_eq_true_eq] at hc
  have := toNat_add_neg (t := t) (c := c) (by omega) (by omega); omega

theorem room0 {S need need' : Nat} {t : BitVec 64} (h : S + need ≤ t.toNat) (hc : decide (need' ≤ need) = true) :
    S + need' ≤ t.toNat := by
  simp only [decide_eq_true_eq] at hc; omega

/-- A bound `k ≤ t.toNat` from the stack's. -/
theorem lo_of_room {S need : Nat} {t : BitVec 64} (h : S + need ≤ t.toNat) : need ≤ t.toNat := by omega

theorem toNat_le_max (t : BitVec 64) : t.toNat ≤ 18446744073709551615 := by have := t.isLt; omega

/-- The frame that writes nothing beyond the stack and the heap. -/
abbrev F : Word → Prop := fun _ => False

variable {env : Env}

theorem frame_refl {top : Word} {m : MachineState} (h : (env.next m).toNat ≤ env.heapEnd.toNat) :
    env.Frame top F m m := Env.Frame.refl h

theorem frame_store {top a v : Word} {m N : MachineState} (h1 : env.Frame top F m N)
    (hlo : env.stackLimit.toNat ≤ a.toNat) (hhi : a.toNat < top.toNat) : env.Frame top F m (N.setMem a v) :=
  h1.trans (Env.Frame.setMem_stack h1.2.1 hlo hhi) (Nat.le_refl _) fun _ h => False.elim h

theorem frame_call {top top' : Word} {m N X : MachineState} (h1 : env.Frame top F m N) (h2 : env.Frame top' F N X)
    (ht : top'.toNat ≤ top.toNat) : env.Frame top F m X :=
  h1.trans h2 ht fun _ h => False.elim h

theorem frame_weaken {top : Word} {out : Word → Prop} {m X : MachineState} (h : env.Frame top F m X) :
    env.Frame top out m X := by
  refine ⟨h.1, h.2.1, fun a ha => h.2.2 a fun hw => ha ?_⟩
  rcases hw with hw | hw | hw | hw
  · exact Or.inl hw
  · exact Or.inr (Or.inl hw)
  · exact Or.inr (Or.inr (Or.inl hw))
  · exact hw.elim

theorem frame_next {top : Word} {out : Word → Prop} {m X : MachineState} (h : env.Frame top out m X) :
    (env.next X).toNat ≤ env.heapEnd.toNat := h.2.1

/-- **A frame without `out` keeps the static data**: they lie between the heap and `NEXT`, below the stack. -/
theorem static_of_frame {top : Word} {m X : MachineState} (hs : env.Static m) (h : env.Frame top F m X) :
    env.Static X := by
  have := env.layout
  refine env.static_frame m X (fun a h1 h2 => h.2.2 a fun hw => ?_) hs
  rcases hw with hw | hw | hw | hw
  · omega
  · have := h.2.1; omega
  · rw [hw] at h2; omega
  · exact hw

/-- **A frame without `out` keeps what is at or above its stack top.** -/
theorem frame_above {top : Word} {M X : MachineState} (h : env.Frame top F M X)
    (hlim : env.stackLimit.toNat ≤ top.toNat) : ∀ a : Word, top ≤ a → X.getMem a = M.getMem a :=
  fun _ ha => h.getMem_above hlim (BitVec.le_def.1 ha) id

end Rv64mc.Tactic
