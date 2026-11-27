/-
  Rv64mc.Proof.Runtime.DropTablesT

  The drop glue of `Vec<Table>` is total: called with a vector's elements (`a0` its buffer, `a1` its length), it
  walks the 80-byte `Table`s, dropping each one's `Flushes`' `push` and `pull` vectors of `Vec<Form>` headers
  (`drop_glue::<Vec<Vec<Form>>>`, `DropSliceT`), and writes nothing a caller sees. A safety-only contract: the
  `Table`s a buffer (`BufT`, the length for the capacity) and each one's two vectors buffers of 24-byte elements
  (`TablesT`), since it reads their pointers and lengths. The loop is `Total.loop` at its head with the `Table`s
  left as the measure (`LoopInv`, `DropSliceT.LoopInv`'s shape).

  ## Main definitions

  * `TablesT`, `PreT`, `SpecT`, `LoopInv`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Runtime.DropSliceT
import Rv64mc.Proof.Runtime.SpecExtendT
import Rv64mc.Gen.Tmpl.Core.Ptr.DropGlueVecTable

namespace Rv64mc.Proof.Runtime.DropTablesT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.VecReprT (BufT)
open Rv64mc.Proof.Runtime.DropSliceT (DropSliceSpecT shl_add_shl)
open Rv64mc.Gen.Core.Ptr.DropGlueVecTable (Link tmpl)

/-- **`n` `Table`s from `q`**, 80 bytes each: each one's `push` and `pull` vectors (pointer and length at offsets
    `0x20`, `0x28` and `0x38`, `0x40`) buffers of 24-byte elements. -/
def TablesT (env : Env) (m : MachineState) (q : Word) (n : Nat) : Prop :=
  ∀ i, i < n →
    BufT env m (m.getMem (q + BitVec.ofNat 64 (80 * i + 0x28))) (m.getMem (q + BitVec.ofNat 64 (80 * i + 0x20))) 24 ∧
    BufT env m (m.getMem (q + BitVec.ofNat 64 (80 * i + 0x40))) (m.getMem (q + BitVec.ofNat 64 (80 * i + 0x38))) 24

/-- The total precondition: the `Table`s a vector's buffer (`a0`, with the length `a1` for the capacity), each one's
    two vectors of `Vec<Form>` headers buffers. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  BufT env m (regs .x11) (regs .x10) 80 ∧ TablesT env m (regs .x10) (regs .x11).toNat

/-- **The total contract of the drop glue of `Vec<Table>`** over its elements: it writes nothing a caller sees. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (fun _ _ _ _ => True)

/-- The loop's head with `k + 1` `Table`s left, the cursor `x8` 64 bytes into the next one and `x9` 64 bytes past the
    last, below `NEXT` at entry: the registers and the frame's slots as the prologue left them, the code map kept. -/
def LoopInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  k < (regs .x11).toNat ∧ (R .x8).toNat = (regs .x10).toNat + 64 + 80 * ((regs .x11).toNat - 1 - k) ∧
    (R .x9).toNat = (regs .x10).toNat + 64 + 80 * (regs .x11).toNat ∧
    R .x2 = top + 0xffffffffffffffe0#64 ∧
    R .x18 = regs .x18 ∧ R .x19 = regs .x19 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧
    R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    env.Frame top Tactic.F m M ∧
    (∀ a, top + 0xffffffffffffffe0#64 ≤ a → M.getMem a =
      (((m.setMem (top + 0xfffffffffffffff8#64) ret).setMem (top + 0xfffffffffffffff0#64) (regs .x8)).setMem
        (top + 0xffffffffffffffe8#64) (regs .x9)).getMem a) ∧
    M.code = m.code

set_option rv_sym.heap true in
/-- **The drop glue of `Vec<Table>` is total**, with 32 bytes of stack beyond the inner drops'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need nd : Nat} (hn : 32 + nd ≤ need) (hd : DropSliceSpecT env 24 p L.dropGlueVecVecForm.idx nd) :
    SpecT env p i need := by
  rv_autoT hp with [hL] using [hd]
  have hl := env.layout
  have hn0 : (regs .x11).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
  obtain ⟨hq1, hq2, hq3⟩ := hpre_6.resolve_left hn0
  unfold Env.Live at hq2
  have hq : (regs .x10).toNat + 64 + 80 * (regs .x11).toNat < 2 ^ 64 := by have := hpre_9.heapEnd_le; omega
  refine Total.loop (LoopInv env ret top regs m) ?_ ((regs .x11).toNat - 1) _ _ ?_
  · intro k R M hI ih
    obtain ⟨hk, h8, h9, -, -, -, -, -, -, -, -, -, -, -, hF, -, -⟩ := id hI
    have hnM := hF.2.1
    have hnm := hF.1
    have kM := SpecExtendT.keep_of_frame hF (by omega)
    have hj : (regs .x11).toNat - 1 - k < (regs .x11).toNat := by omega
    obtain ⟨hb1, hb2⟩ := hpre_7 _ hj
    have ea : ∀ c o : Nat, c + o = 2 ^ 64 → o ≤ 64 → (R .x8 + BitVec.ofNat 64 c) =
        regs .x10 + BitVec.ofNat 64 (80 * ((regs .x11).toNat - 1 - k) + (64 - o)) := fun c o hco ho => by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, h8, toNat_add_ofNat (by omega)]
      simp only [BitVec.toNat_ofNat]
      omega
    have hb1' : BufT env M (m.getMem (R .x8 + 0xffffffffffffffe8#64)) (m.getMem (R .x8 + 0xffffffffffffffe0#64)) 24 := by
      rw [ea 0xffffffffffffffe8 24 rfl (by omega), ea 0xffffffffffffffe0 32 rfl (by omega)]
      exact hb1.mono hnm
    have hb2' : BufT env M (m.getMem (R .x8)) (m.getMem (R .x8 + 0xfffffffffffffff8#64)) 24 := by
      have e0 : R .x8 = regs .x10 + BitVec.ofNat 64 (80 * ((regs .x11).toNat - 1 - k) + 0x40) :=
        BitVec.eq_of_toNat_eq (by rw [h8, toNat_add_ofNat (by omega)]; omega)
      rw [ea 0xfffffffffffffff8 8 rfl (by omega), e0]
      exact hb2.mono hnm
    clear hpre_6 hpre_7 hc
    rv_introT hI
    rv_symT hp stop [20, 40] with [hL] using [hd]
    · have hx8 : (R .x8 + 80#64).toNat = (R .x8).toNat + 80 := toNat_add_ofNat (by omega)
      have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [hx8, h8, h9]; subst h0; omega))
      clear hc
      refine ih (k - 1) _ _ (by omega) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals try simp only [Tactic.rf]
      all_goals rv_closeT
    · clear hc
      rv_symT hp with [hL] using [hd]
  · have h64 : (regs .x10 + 64#64).toNat = (regs .x10).toNat + 64 := toNat_add_ofNat (by omega)
    have h9 : (regs .x10 + 64#64 + (regs .x11 <<< 6 + regs .x11 <<< 4)).toNat =
        (regs .x10).toNat + 64 + 80 * (regs .x11).toNat := by
      rw [BitVec.toNat_add, h64, shl_add_shl (by omega)]; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    all_goals rv_closeT

end Rv64mc.Proof.Runtime.DropTablesT

/-- info: 'Rv64mc.Proof.Runtime.DropTablesT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.DropTablesT.total
