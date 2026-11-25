/-
  Rv64mc.Proof.Runtime.MemcmpT

  `memcmp` is total: it returns `CmpPost`'s comparison (`Spec.Runtime.Mem`), over any program holding its template.
  The total counterpart of `Memcmp.lean`, whose lemmas it reuses. Its loads go through the caller's two pointers, so
  the precondition (`CmpPreT`) puts both byte strings in windows (`InWin`, `MemsetT.lean`'s) unless they are empty:
  `Form::add_scaled` compares two vectors' buffers, whose pointer is dangling when they are empty, and
  `Transcript::merkle` a digest in its frame with the one it is passed. The loop is `Total.loop` at its head with the
  bytes left as the measure (`LoopInv`); `rv_symT` steps its body and closes each byte load's window.

  ## Main definitions

  * `CmpPreT`, `MemcmpSpecT`, `LoopInv`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Runtime.Memcmp
import Rv64mc.Proof.Runtime.MemsetT
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Runtime.MemcmpT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Proof.Runtime.Memcmp
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Gen.Memcmp (Link tmpl)

/-- `memcmp`'s total precondition: no bytes, or the `n` bytes from each pointer in a window. -/
def CmpPreT (env : Env) (regs : Reg → Word) (_m : MachineState) : Prop :=
  (regs .x12).toNat = 0 ∨ (InWin env (regs .x10) (regs .x12).toNat ∧ InWin env (regs .x11) (regs .x12).toNat)

/-- **The total contract of `memcmp`**: `MemcmpSpec`'s, as a `HoldsT`, from `CmpPreT`. -/
def MemcmpSpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (CmpPreT env) CmpPost

/-- The loop at its head with `k + 1` bytes left from `R .x10` and `R .x11`, in windows, whose comparison is the whole
    one `V`; the memory and the registers the contract keeps as at the entry. -/
def LoopInv (env : Env) (top ret : Word) (regs : Reg → Word) (m : MachineState) (V : Word) (k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  M = m ∧ AbiRegs top regs R ∧ R .x1 = ret ∧ R .x12 = BitVec.ofNat 64 (k + 1) ∧ k + 1 < 2 ^ 64 ∧
    InWin env (R .x10) (k + 1) ∧ InWin env (R .x11) (k + 1) ∧
    memcmpVal (bytesFrom m (R .x10) (k + 1)) (bytesFrom m (R .x11) (k + 1)) = V

variable {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link}

/-- **`memcmp` is total**, with no stack. -/
theorem total (hp : p[i]? = some (tmpl L)) : MemcmpSpecT env p i 0 := by
  rv_autoT hp
  -- nothing to compare
  · rw [hc]; rfl
  -- the loop, with every byte left
  · obtain ⟨k, hn⟩ : ∃ k, (regs .x12).toNat = k + 1 :=
      ⟨(regs .x12).toNat - 1, by have : (regs .x12).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h); omega⟩
    have hw := hpre_6.resolve_left (by omega)
    refine Total.loop (LoopInv env top ret regs m (memcmpVal (bytesFrom m (regs .x10) (regs .x12).toNat)
      (bytesFrom m (regs .x11) (regs .x12).toNat))) ?_ k _ _ ?_
    · intro k R M hI ih
      obtain ⟨rfl, hI⟩ := hI
      rv_introT hI
      rv_symT hp
      -- the bytes differ: their difference
      · rw [← hI_19, bytesFrom_succ, bytesFrom_succ,
          memcmpVal_ne fun h => hc (congrArg (BitVec.setWidth 64) h), BitVec.sub_eq_add_neg]
      -- equal, and bytes left: the next one
      · cases k with
        | zero => exact absurd (by decide) hc
        | succ k =>
          have h10 : (R .x10 + 1#64).toNat = (R .x10).toNat + 1 := toNat_add_ofNat (by omega)
          have h11 : (R .x11 + 1#64).toNat = (R .x11).toNat + 1 := toNat_add_ofNat (by omega)
          refine ih k _ _ (by omega) ⟨rfl, by unfold AbiRegs; and_intros <;> rfl, rfl, pred_ofNat k, by omega,
            by show InWin env (R .x10 + 1#64) (k + 1); unfold InWin; omega,
            by show InWin env (R .x11 + 1#64) (k + 1); unfold InWin; omega, ?_⟩
          rw [← hI_19, bytesFrom_succ M (R .x10) (k + 1), bytesFrom_succ M (R .x11) (k + 1),
            memcmpVal_eq (setWidth_inj hc_2)]
          rfl
      -- equal, and none left: zero
      · cases k with
        | zero => rw [← hI_19, bytesFrom_succ, bytesFrom_succ, memcmpVal_eq (setWidth_inj hc_2)]; rfl
        | succ k => exact absurd hc (pred_ne (by omega))
    · refine ⟨rfl, by unfold AbiRegs; and_intros <;> rfl, rfl, ?_, hn ▸ (regs .x12).isLt, hn ▸ hw.1, hn ▸ hw.2, ?_⟩
      · show regs .x12 = _
        rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · show memcmpVal (bytesFrom m (regs .x10) (k + 1)) (bytesFrom m (regs .x11) (k + 1)) = _
        rw [hn]

end Rv64mc.Proof.Runtime.MemcmpT

/-- info: 'Rv64mc.Proof.Runtime.MemcmpT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.MemcmpT.total
