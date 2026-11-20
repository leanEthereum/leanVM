/-
  Rv64mc.Tactic.Heap

  The facts about stores outside a function's own stack that `rv_sym` uses: into memory the function allocated
  (between `NEXT` at entry and `NEXT` now) and into its contract's `out` (a caller's `sret` slot or buffer), and
  calls whose callee has an `out` of its own. Each frame here has any `out`, where `Tactic/Frame.lean`'s have none.
  The side conditions are linear facts over the words' numbers, which `rv_sym` proves by `omega` from the context
  (`Sym.arith`), each address `b + c` given to it as `(b.toNat + c) % 2^64`, or as `t.toNat - k` for a slot `t - k`
  of the stack (`slot_eq`).

  ## Main results

  * `frame_slot`, `frame_fresh`, `frame_out`, `frame_callF`, `frame_trans`: a frame with any `out`, store by store and
    call by call
  * `static_out`: the static data kept by a frame whose `out` misses them
  * `next_setMem`, `next_ne_of_stack`: `NEXT` through a store elsewhere
-/

import Rv64mc.Tactic.Frame
import Rv64mc.Core.Repr

namespace Rv64mc.Tactic

open RiscvZkvm.Rv64

/-- `c` is `-k` for a positive `k` of at most `need` bytes. -/
def slotK (need : Nat) (c : BitVec 64) (k : Nat) : Bool := decide (0 < k ∧ k ≤ need ∧ c.toNat + k = 2 ^ 64)

/-- **A slot's number**: `t - k` for the stack top `t`. -/
theorem slot_eq {S need k : Nat} {t c : BitVec 64} (h : S + need ≤ t.toNat) (hc : slotK need c k = true) :
    (t + c).toNat + k = t.toNat := by
  simp only [slotK, decide_eq_true_eq] at hc
  rw [BitVec.toNat_add]
  have : (t.toNat + c.toNat) = (t.toNat - k) + 2 ^ 64 := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := t.isLt; omega)]
  omega

/-- **A callee's stack top is 16-aligned** when the caller's is and its frame a multiple of 16. -/
theorem align_slot {S need k : Nat} {t c : BitVec 64} (h : S + need ≤ t.toNat) (ht : t.toNat % 16 = 0)
    (hc : slotK need c k = true) (hk : k % 16 = 0) : (t + c).toNat % 16 = 0 := by
  have := slot_eq h hc; omega

/-- **`t - k` is 16-aligned** when `t` and `k` are (`c` is `-k`). -/
theorem align_off {t c : BitVec 64} {k : Nat} (ht : t.toNat % 16 = 0) (hc : c.toNat + k = 2 ^ 64)
    (h16 : k % 16 = 0) : (t + c).toNat % 16 = 0 := by
  rw [BitVec.toNat_add]
  have := t.isLt
  omega

/-- An address off the stack is no slot of it. -/
theorem ne_of_off_stack {S : Nat} {t x y : Word} (hoff : x.toNat < S ∨ t.toNat ≤ x.toNat) (hlo : S ≤ y.toNat)
    (hhi : y.toNat < t.toNat) : x ≠ y := fun e => by subst e; omega

/-- An offset's number, for `omega`. -/
theorem toNat_add_lit (b c : BitVec 64) (n : Nat) (h : c.toNat = n) : (b + c).toNat = (b.toNat + n) % 2 ^ 64 := by
  rw [BitVec.toNat_add, h]

/-- A negative offset's number, for `omega`, without a 64-bit constant: `b - k`, or it wraps. -/
theorem toNat_add_negk (b c : BitVec 64) (k : Nat) (h : c.toNat + k = 2 ^ 64) :
    b.toNat < k ∨ (b + c).toNat + k = b.toNat := by
  rw [BitVec.toNat_add]; have := b.isLt; omega

theorem ne_of_toNat {a b : BitVec 64} (h : a.toNat ≠ b.toNat) : a ≠ b := fun e => h (congrArg BitVec.toNat e)

theorem le_of_toNat {a b : BitVec 64} (h : a.toNat ≤ b.toNat) : a ≤ b := BitVec.le_def.2 h

theorem lt_of_toNat {a b : BitVec 64} (h : a.toNat < b.toNat) : a < b := BitVec.lt_def.2 h

theorem toNat_congr {a b : BitVec 64} (h : a = b) : a.toNat = b.toNat := congrArg BitVec.toNat h

variable {env : Env}

/-- A word of the stack is not `NEXT`'s. -/
theorem next_ne_of_stack {a : Word} (h : env.stackLimit.toNat ≤ a.toNat) : a ≠ env.nextAddr := fun e => by
  have := env.layout; rw [e] at h; omega

theorem next_setMem {N : MachineState} {a v : Word} (h : a ≠ env.nextAddr) : env.next (N.setMem a v) = env.next N :=
  MachineState.getMem_setMem_ne (Ne.symm h)

theorem frame_slot {top a v : Word} {out : Word → Prop} {m N : MachineState} (h1 : env.Frame top out m N)
    (hlo : env.stackLimit.toNat ≤ a.toNat) (hhi : a.toNat < top.toNat) : env.Frame top out m (N.setMem a v) :=
  h1.trans (Env.Frame.setMem_stack (out := F) h1.2.1 hlo hhi) (Nat.le_refl _) fun _ h => False.elim h

/-- **A store into what the function allocated**: at or above `NEXT` at entry and below `NEXT` now. -/
theorem frame_fresh {top a v : Word} {out : Word → Prop} {m N B : MachineState} (h1 : env.Frame top out m N)
    (hn : env.next N = env.next B) (hlo : (env.next m).toNat ≤ a.toNat) (hhi : a.toNat < (env.next B).toNat) :
    env.Frame top out m (N.setMem a v) := by
  have := env.layout
  have h2 := h1.2.1
  rw [hn] at h2
  have hne : a ≠ env.nextAddr := fun e => by rw [e] at hhi; omega
  have hn' := next_setMem (N := N) (v := v) hne
  refine ⟨by rw [hn']; exact h1.1, by rw [hn', hn]; exact h2, fun b hb => ?_⟩
  have hba : b ≠ a := fun e => hb (Or.inr (Or.inl ⟨e ▸ hlo, by rw [e, hn', hn]; exact hhi⟩))
  rw [MachineState.getMem_setMem_ne hba]
  exact h1.2.2 b fun hw => hb (by
    rcases hw with hw | hw | hw | hw
    · exact Or.inl hw
    · exact Or.inr (Or.inl ⟨hw.1, by rw [hn']; exact hw.2⟩)
    · exact Or.inr (Or.inr (Or.inl hw))
    · exact Or.inr (Or.inr (Or.inr hw)))

/-- **A store into `out`**, not `NEXT`. -/
theorem frame_out {top a v : Word} {out : Word → Prop} {m N : MachineState} (h1 : env.Frame top out m N)
    (hb : out a) (hn : a ≠ env.nextAddr) : env.Frame top out m (N.setMem a v) :=
  h1.trans (Env.Frame.setMem_out (top := top) h1.2.1 hb hn) (Nat.le_refl _) fun _ h => Or.inr (Or.inr (Or.inr h))

/-- A callee without `out`, from a stack top no higher. -/
theorem frame_callF {top top' : Word} {out : Word → Prop} {m N X : MachineState} (h1 : env.Frame top out m N)
    (h2 : env.Frame top' F N X) (ht : top'.toNat ≤ top.toNat) : env.Frame top out m X :=
  h1.trans h2 ht fun _ h => False.elim h

/-- **A callee with an `out`**, each word of which the caller may write. -/
theorem frame_trans {top top' : Word} {out out' : Word → Prop} {m N X : MachineState} (h1 : env.Frame top out m N)
    (h2 : env.Frame top' out' N X) (ht : top'.toNat ≤ top.toNat) (hout : ∀ a, out' a → env.MayWrite top out m X a) :
    env.Frame top out m X :=
  h1.trans h2 ht hout

theorem mw_stack {top a : Word} {out : Word → Prop} {m X : MachineState}
    (h : env.stackLimit.toNat ≤ a.toNat ∧ a.toNat < top.toNat) : env.MayWrite top out m X a := Or.inl h

theorem mw_fresh {top a : Word} {out : Word → Prop} {m X : MachineState}
    (h : (env.next m).toNat ≤ a.toNat ∧ a.toNat < (env.next X).toNat) : env.MayWrite top out m X a := Or.inr (Or.inl h)

theorem mw_out {top a : Word} {out : Word → Prop} {m X : MachineState} (h : out a) : env.MayWrite top out m X a :=
  Or.inr (Or.inr (Or.inr h))

/-- **A frame whose `out` misses the static data keeps them.** -/
theorem static_out {top : Word} {out : Word → Prop} {m X : MachineState} (hs : env.Static m)
    (h : env.Frame top out m X) (hout : ∀ a, out a → a.toNat < env.staticLo.toNat ∨ env.staticHi.toNat ≤ a.toNat) :
    env.Static X := by
  have := env.layout
  refine env.static_frame m X (fun a h1 h2 => h.2.2 a fun hw => ?_) hs
  rcases hw with hw | hw | hw | hw
  · omega
  · have := h.2.1; omega
  · rw [hw] at h2; omega
  · rcases hout a hw with h3 | h3 <;> omega

theorem static_store {N : MachineState} {a v : Word} (hs : env.Static N)
    (h : a.toNat < env.staticLo.toNat ∨ env.staticHi.toNat ≤ a.toNat) : env.Static (N.setMem a v) :=
  Env.static_setMem hs h

/-! What a callee's frame keeps, as `rv_sym` reads through it (`keep<k>_j`) -/

theorem frame_above_out {top : Word} {out : Word → Prop} {M X : MachineState} (h : env.Frame top out M X)
    (hlim : env.stackLimit.toNat ≤ top.toNat) : ∀ a : Word, top ≤ a → ¬ out a → X.getMem a = M.getMem a :=
  fun _ ha ho => h.getMem_above hlim (BitVec.le_def.1 ha) ho

/-- **A callee keeps the heap below `NEXT` at the call and what is at or above its stack top.** -/
theorem frame_keep {top : Word} {M X : MachineState} (h : env.Frame top F M X)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (hnx : (env.next M).toNat ≤ env.heapEnd.toNat) :
    ∀ a : Word, a.toNat < (env.next M).toNat ∨ top.toNat ≤ a.toNat → X.getMem a = M.getMem a :=
  fun _ ha => ha.elim (fun ha => h.getMem_below_next hnx ha id) (fun ha => h.getMem_above hlim ha id)

theorem frame_keep_out {top : Word} {out : Word → Prop} {M X : MachineState} (h : env.Frame top out M X)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (hnx : (env.next M).toNat ≤ env.heapEnd.toNat) :
    ∀ a : Word, a.toNat < (env.next M).toNat ∨ top.toNat ≤ a.toNat → ¬ out a → X.getMem a = M.getMem a :=
  fun _ ha ho => ha.elim (fun ha => h.getMem_below_next hnx ha ho) (fun ha => h.getMem_above hlim ha ho)

end Rv64mc.Tactic
