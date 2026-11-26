/-
  Rv64mc.Proof.Runtime.DropSliceT

  The drop glue of `Vec<Vec<Form>>` and of `Vec<BusBlock>` is total: called with a vector's elements (`a0` its
  buffer, `a1` its length), it walks them, calling `drop_glue::<Vec<Form>>` (which returns at once,
  `DropT.vecForm_total`) on each element's inner slice, and writes nothing a caller sees (`DropSpec`'s, as a
  `HoldsT`). Its precondition is that the elements are a vector's buffer (`VecReprT.BufT`, with the length for the
  capacity): none, or allocated below `NEXT` and 8-byte aligned, since it reads two words of each element. The loop
  is `Total.loop` at its head with the elements left as the measure (`LoopInv`). The two templates differ only in
  the element's size, so both proofs are one script over it (`drop_slice`).

  The executor's closer runs `omega` over the whole context, and a branch's outcome on two words is a bit-vector
  equation it splits on: each proof clears it once the step past the branch has its value as a number.

  ## Main definitions

  * `DropSliceSpecT`, `LoopInv`

  ## Main results

  * `vecVecForm_total`, `vecBusBlock_total`
  * `BufT.of_le`: a vector's buffer with its length for the capacity
-/

import Rv64mc.Proof.Runtime.DropT
import Rv64mc.Proof.Runtime.VecReprT
import Rv64mc.Gen.Tmpl.Core.Ptr.DropGlueVecVecForm
import Rv64mc.Gen.Tmpl.Core.Ptr.DropGlueVecBusBlock
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Runtime.DropSliceT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.DropT (DropSpecT)
open Rv64mc.Proof.Runtime.VecReprT (BufT)

/-- A buffer of `cap` elements holds its first `len`. -/
theorem BufT.of_le {env : Env} {m : MachineState} {cap len ptr : Word} {size : Nat} (h : BufT env m cap ptr size)
    (hl : len.toNat ≤ cap.toNat) : BufT env m len ptr size := by
  rcases h with h | ⟨h1, h2, h3⟩
  · exact .inl (by omega)
  · refine .inr ⟨h1, ?_, h3⟩
    unfold Env.Live at h2 ⊢
    have := Nat.mul_le_mul_right size hl
    omega

/-- **The total contract of a drop over a vector's elements** of `size` bytes, its buffer `a0` and length `a1`: it
    writes nothing a caller sees. -/
def DropSliceSpecT (env : Env) (size : Nat) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun regs m => BufT env m (regs .x11) (regs .x10) size) (fun _ _ _ _ => True)

/-- The loop's head with `k + 1` elements left, the cursor `x8` 16 bytes into the next one and `x9` 16 bytes past
    the last, below `NEXT` at entry: the registers and the frame's slots as the prologue left them, the code map
    kept. -/
def LoopInv (env : Env) (size : Nat) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  0x10000000 + 16 ≤ (R .x8).toNat ∧ (R .x8).toNat + size * (k + 1) = (R .x9).toNat ∧
    (R .x9).toNat ≤ (env.next m).toNat + 16 ∧ (R .x8).toNat % 8 = 0 ∧
    R .x2 = top + 0xffffffffffffffe0#64 ∧
    R .x18 = regs .x18 ∧ R .x19 = regs .x19 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧
    R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    env.Frame top Tactic.F m M ∧
    (∀ a, top + 0xffffffffffffffe0#64 ≤ a → M.getMem a =
      (((m.setMem (top + 0xfffffffffffffff8#64) ret).setMem (top + 0xfffffffffffffff0#64) (regs .x8)).setMem
        (top + 0xffffffffffffffe8#64) (regs .x9)).getMem a) ∧
    M.code = m.code

/-- The prologue's bound: the elements' end as the code computes it, `x << a + x << b`. -/
theorem shl_add_shl {x : Word} {a b : Nat} (h : (2 ^ a + 2 ^ b) * x.toNat < 2 ^ 64) :
    (x <<< a + x <<< b).toNat = (2 ^ a + 2 ^ b) * x.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (a := x.toNat * 2 ^ a) (by rw [Nat.add_mul] at h; rw [Nat.mul_comm]; omega),
    Nat.mod_eq_of_lt (a := x.toNat * 2 ^ b) (by rw [Nat.add_mul] at h; rw [Nat.mul_comm]; omega), Nat.add_mul,
    Nat.mul_comm x.toNat, Nat.mul_comm x.toNat]
  exact Nat.mod_eq_of_lt (by rw [Nat.add_mul] at h; exact h)

set_option hygiene false in
/-- What is left after `rv_autoT` of either template, for elements of `n = 2 ^ a + 2 ^ b` bytes: the loop's body,
    from its head to its head or to the return, then its entry. -/
local macro "drop_slice " n:num a:num b:num : tactic => `(tactic| (
    refine Total.loop (LoopInv env $n ret top regs m) ?_ ((regs .x11).toNat - 1) _ _ ?_
    · intro k R M hI ih
      rv_introT hI
      clear hpre_6 hc
      rv_symT hp stop [20, 32] with [hL] using [hd]
      · have hl := env.layout
        have hx8 : (R .x8 + BitVec.ofNat 64 $n).toNat = (R .x8).toNat + $n :=
          toNat_add_ofNat (by have := env.heapEnd.isLt; omega)
        have hk : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [hx8]; subst h0; omega))
        clear hc
        refine ih (k - 1) _ _ (by omega) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals try simp only [Tactic.rf]
        all_goals rv_closeT
      · clear hc
        rv_symT hp with [hL] using [hd]
    · have hl := env.layout
      have hn0 : (regs .x11).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
      obtain ⟨hq1, hq2, hq3⟩ := hpre_6.resolve_left hn0
      unfold Env.Live at hq2
      have hq : (regs .x10).toNat + 16 + $n * (regs .x11).toNat < 2 ^ 64 := by have := env.heapEnd.isLt; omega
      have h16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by omega)
      have h9 : (regs .x10 + 16#64 + (regs .x11 <<< $a + regs .x11 <<< $b)).toNat =
          (regs .x10).toNat + 16 + $n * (regs .x11).toNat := by
        rw [BitVec.toNat_add, h16, shl_add_shl (by omega)]; omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals try simp only [Tactic.rf]
      all_goals rv_closeT))

set_option rv_sym.heap true in
/-- **The drop glue of `Vec<Vec<Form>>` is total**, with 32 bytes of stack beyond the inner drop's. -/
theorem vecVecForm_total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Gen.Core.Ptr.DropGlueVecVecForm.Link)
    (hp : p[i]? = some (Gen.Core.Ptr.DropGlueVecVecForm.tmpl L)) (hL : L.WF p) {need nd : Nat} (hn : 32 + nd ≤ need)
    (hd : DropSpecT env p L.dropGlueVecForm.idx nd) : DropSliceSpecT env 24 p i need := by
  rv_autoT hp with [hL] using [hd]
  drop_slice 24 4 3

set_option rv_sym.heap true in
/-- **The drop glue of `Vec<BusBlock>` is total**, with 32 bytes of stack beyond the inner drop's. -/
theorem vecBusBlock_total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Gen.Core.Ptr.DropGlueVecBusBlock.Link)
    (hp : p[i]? = some (Gen.Core.Ptr.DropGlueVecBusBlock.tmpl L)) (hL : L.WF p) {need nd : Nat}
    (hn : 32 + nd ≤ need) (hd : DropSpecT env p L.dropGlueVecForm.idx nd) : DropSliceSpecT env 48 p i need := by
  rv_autoT hp with [hL] using [hd]
  drop_slice 48 5 4

end Rv64mc.Proof.Runtime.DropSliceT

/--
info: 'Rv64mc.Proof.Runtime.DropSliceT.vecVecForm_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.DropSliceT.vecVecForm_total

/--
info: 'Rv64mc.Proof.Runtime.DropSliceT.vecBusBlock_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.DropSliceT.vecBusBlock_total
