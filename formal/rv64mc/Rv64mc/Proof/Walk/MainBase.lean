/-
  Rv64mc.Proof.Walk.MainBase

  What every cut point of `main` keeps (`Base`): its stack pointer, its frame from the entry, the static data, the
  prologue's saved registers, the `Bytecode` and the public input in its frame (`[sp + 88, sp + 184)`) and the heap
  below `NEXT` as they were at the snapshot `M1` (after `Input::digest`), and `NEXT` within the heap. A store into
  the stack outside those slots or into a block allocated after `M1` keeps it (`Base.store`), and so does a call
  that writes only such words (`Base.call`). The snapshot holds the input words (`Fix`), read through `Base`.
-/

import Rv64mc.Tactic.Sym
import Rv64mc.Final.MainSpec

namespace Rv64mc.Proof.Walk.Main

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- The prologue's stores: `ra` and `s0`..`s11` below `top`. -/
def saved (m : MachineState) (ret top : Word) (regs : Reg → Word) : MachineState :=
  (((((((((((((m.setMem (top + 0xfffffffffffffff8#64) ret).setMem (top + 0xfffffffffffffff0#64) (regs .x8)).setMem
    (top + 0xffffffffffffffe8#64) (regs .x9)).setMem (top + 0xffffffffffffffe0#64) (regs .x18)).setMem
    (top + 0xffffffffffffffd8#64) (regs .x19)).setMem (top + 0xffffffffffffffd0#64) (regs .x20)).setMem
    (top + 0xffffffffffffffc8#64) (regs .x21)).setMem (top + 0xffffffffffffffc0#64) (regs .x22)).setMem
    (top + 0xffffffffffffffb8#64) (regs .x23)).setMem (top + 0xffffffffffffffb0#64) (regs .x24)).setMem
    (top + 0xffffffffffffffa8#64) (regs .x25)).setMem (top + 0xffffffffffffffa0#64) (regs .x26)).setMem
    (top + 0xffffffffffffff98#64) (regs .x27))

/-- The facts of the entry and the snapshot `M1` no cut point changes. -/
structure Fix (env : Env) (words : List Word) (top : Word) (m M1 : MachineState) : Prop where
  input : WordsAt M1 0x10000000#64 words
  next1 : (env.next m).toNat ≤ (env.next M1).toNat
  inputEnd : 0x10000000 + 8 * words.length ≤ (env.next m).toNat
  room : env.stackLimit.toNat + 416 ≤ top.toNat
  align : top.toNat % 16 = 0

/-- **What every cut point keeps.** -/
def Base (env : Env) (ret top : Word) (regs : Reg → Word) (m M1 : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 0xfffffffffffffe60#64 ∧ env.Frame top Tactic.F m M ∧ env.Static M ∧
    (∀ a, top + 0xffffffffffffff98#64 ≤ a → M.getMem a = (saved m ret top regs).getMem a) ∧
    Keeps M1 M (top + 0xfffffffffffffeb8#64) 96 ∧
    (∀ b : Word, b.toNat < (env.next M1).toNat → M.getMem b = M1.getMem b) ∧
    (env.next M1).toNat ≤ (env.next M).toNat ∧ (env.next M).toNat ≤ env.heapEnd.toNat

/-- A word main may write: a stack slot below the saved registers and off the `Bytecode` and the public input, or a
    block allocated after the snapshot. -/
def Writable (env : Env) (top : Word) (M1 M : MachineState) (a : Word) : Prop :=
  (env.stackLimit.toNat ≤ a.toNat ∧ a.toNat + 104 < top.toNat ∧
      (a.toNat + 336 ≤ top.toNat ∨ top.toNat ≤ a.toNat + 232)) ∨
    ((env.next M1).toNat ≤ a.toNat ∧ a.toNat < (env.next M).toNat)

theorem toNat_top (top : Word) {c : Word} {k : Nat} (hc : c.toNat + k = 2 ^ 64) (hk : k ≤ top.toNat) :
    (top + c).toNat = top.toNat - k := by
  rw [BitVec.toNat_add]; have := top.isLt; omega

section

variable {env : Env} {words : List Word} {ret top : Word} {regs : Reg → Word} {m M1 : MachineState}

theorem Base.next_le {R : Reg → Word} {M : MachineState} (h : Base env ret top regs m M1 R M) :
    (env.next m).toNat ≤ (env.next M).toNat := h.2.1.1

/-- **A store main may make keeps `Base`.** -/
theorem Base.store {R R' : Reg → Word} {M : MachineState} {a v : Word} (fx : Fix env words top m M1)
    (h : Base env ret top regs m M1 R M) (hR : R' .x2 = top + 0xfffffffffffffe60#64)
    (ha : Writable env top M1 M a) : Base env ret top regs m M1 R' (M.setMem a v) := by
  obtain ⟨_, hF, hS, hsv, hK, hB, hn1, hN⟩ := h
  have hl := env.layout
  have hnx1 := fx.next1
  have hroom := fx.room
  have hne : a ≠ env.nextAddr := fun e => by subst e; unfold Writable at ha; omega
  have hnx := Tactic.next_setMem (N := M) (v := v) hne
  have h104 : (top + 0xffffffffffffff98#64).toNat = top.toNat - 104 := toNat_top top (by decide) (by omega)
  have h328 : (top + 0xfffffffffffffeb8#64).toNat = top.toNat - 328 := toNat_top top (by decide) (by omega)
  refine ⟨hR, ?_, ?_, ?_, ?_, ?_, by rw [hnx]; exact hn1, by rw [hnx]; exact hN⟩
  · rcases ha with ha | ha
    · exact Tactic.frame_slot hF ha.1 (by omega)
    · exact Tactic.frame_fresh hF rfl (by omega) ha.2
  · exact Tactic.static_store hS (by unfold Writable at ha; omega)
  · intro b hb
    have : b ≠ a := fun e => by subst e; rw [BitVec.le_def, h104] at hb; unfold Writable at ha; omega
    rw [MachineState.getMem_setMem_ne this, hsv b hb]
  · refine Keeps.trans hK (Keeps.setMem fun hr => ?_)
    unfold InRange at hr; rw [h328] at hr; unfold Writable at ha; omega
  · intro b hb
    have : b ≠ a := fun e => by subst e; unfold Writable at ha; omega
    rw [MachineState.getMem_setMem_ne this, hB b hb]

/-- **A call that writes only words main may write keeps `Base`.** -/
theorem Base.call {R R' : Reg → Word} {M M' : MachineState} {out : Word → Prop} (fx : Fix env words top m M1)
    (h : Base env ret top regs m M1 R M) (hR : R' .x2 = top + 0xfffffffffffffe60#64)
    (hf : env.Frame (top + 0xfffffffffffffe60#64) out M M') (hs : env.Static M')
    (hout : ∀ b, out b → Writable env top M1 M' b) : Base env ret top regs m M1 R' M' := by
  obtain ⟨_, hF, hS, hsv, hK, hB, hn1, hN⟩ := h
  have hl := env.layout
  have hnx1 := fx.next1
  have hroom := fx.room
  have h416 : (top + 0xfffffffffffffe60#64).toNat = top.toNat - 416 := toNat_top top (by decide) (by omega)
  have h104 : (top + 0xffffffffffffff98#64).toNat = top.toNat - 104 := toNat_top top (by decide) (by omega)
  have h328 : (top + 0xfffffffffffffeb8#64).toNat = top.toNat - 328 := toNat_top top (by decide) (by omega)
  have hn' := hf.1
  have hN' := hf.2.1
  refine ⟨hR, ?_, hs, ?_, ?_, ?_, by omega, hN'⟩
  · refine hF.trans hf (by omega) fun b hb => ?_
    rcases hout b hb with hw | hw
    · exact Or.inl ⟨hw.1, by omega⟩
    · exact Or.inr (Or.inl ⟨by omega, hw.2⟩)
  · intro b hb
    rw [BitVec.le_def, h104] at hb
    rw [hf.getMem_above (by omega) (by omega) fun ho => by have := hout b ho; unfold Writable at this; omega]
    exact hsv b (by rw [BitVec.le_def, h104]; exact hb)
  · refine Keeps.trans hK fun b hb => ?_
    unfold InRange at hb; rw [h328] at hb
    exact hf.getMem_above (by omega) (by omega) fun ho => by have := hout b ho; unfold Writable at this; omega
  · intro b hb
    rw [hf.getMem_below_next hN (by omega) fun ho => by have := hout b ho; unfold Writable at this; omega]
    exact hB b hb

/-- An input word, read through `Base`. -/
theorem Base.input {R : Reg → Word} {M : MachineState} (fx : Fix env words top m M1)
    (h : Base env ret top regs m M1 R M) {q : Nat} (hq : q < words.length) :
    M.getMem (0x10000000#64 + BitVec.ofNat 64 (8 * q)) = words[q] := by
  have h1 := fx.input.1
  have := fx.inputEnd
  have := fx.next1
  rw [h.2.2.2.2.2.1 _ (by rw [toNat_add_ofNat (by simp only [BitVec.toNat_ofNat]; omega)]; simp; omega)]
  exact fx.input.2 q hq

end

/-! ## Words and addresses -/

theorem add_ofNat (b : Word) (x y : Nat) : b + BitVec.ofNat 64 x + BitVec.ofNat 64 y = b + BitVec.ofNat 64 (x + y) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem add_lit (b : Word) (x y : Nat) (c : Word) (hc : c = BitVec.ofNat 64 y) :
    b + BitVec.ofNat 64 x + c = b + BitVec.ofNat 64 (x + y) := by
  rw [hc, add_ofNat]

theorem sub_lit {a k : Nat} (c : Word) (hc : c.toNat + k = 2 ^ 64) (hk : k ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a + c = BitVec.ofNat 64 (a - k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := c.isLt
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (show a - k < 2 ^ 64 by omega)]
  omega

theorem ofNat_eq_iff {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem ofNat_eq_lit {a : Nat} (c : Word) (ha : a < 2 ^ 64) : BitVec.ofNat 64 a = c ↔ a = c.toNat := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

end Rv64mc.Proof.Walk.Main
