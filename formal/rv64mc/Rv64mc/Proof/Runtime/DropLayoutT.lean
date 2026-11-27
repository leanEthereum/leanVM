/-
  Rv64mc.Proof.Runtime.DropLayoutT

  The drop glue of `Layout` is total: called with the `Layout`'s address (`a0`), it drops its `tables`
  (`drop_glue::<Vec<Table>>`, `DropTablesT`) and its `push`, `pull` and `count` vectors of `BusBlock`s
  (`drop_glue::<Vec<BusBlock>>`, `DropSliceT`, the last a tail call), and writes nothing a caller sees. A
  safety-only contract over the four vectors' buffers it reads (the allocator never frees, so the drops only walk).

  The precondition: the `Layout`'s first 96 bytes a caller's object in a window, 8-byte aligned; `tables`
  (pointer and length at offsets `8`, `16`) a buffer of 80-byte `Table`s each with its `Flushes`' two buffers
  (`DropTablesT.TablesT`); `push`, `pull` and `count` (at `0x20`, `0x38`, `0x50`, lengths after) buffers of
  48-byte `BusBlock`s.

  ## Main definitions

  * `PreT`, `SpecT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Runtime.DropTablesT
import Rv64mc.Gen.Tmpl.Core.Ptr.DropGlueLayout

namespace Rv64mc.Proof.Runtime.DropLayoutT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT)
open Rv64mc.Proof.Runtime.DropSliceT (DropSliceSpecT)
open Rv64mc.Proof.Runtime.DropTablesT (TablesT)
open Rv64mc.Gen.Core.Ptr.DropGlueLayout (Link tmpl)

/-- The total precondition: the `Layout`'s 96 bytes a caller's, in a window, aligned; its four vectors' buffers. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) 96 ∧ InWin env (regs .x10) 96 ∧ (regs .x10).toNat % 8 = 0 ∧
    BufT env m (m.getMem (regs .x10 + 16#64)) (m.getMem (regs .x10 + 8#64)) 80 ∧
    TablesT env m (m.getMem (regs .x10 + 8#64)) (m.getMem (regs .x10 + 16#64)).toNat ∧
    BufT env m (m.getMem (regs .x10 + 40#64)) (m.getMem (regs .x10 + 32#64)) 48 ∧
    BufT env m (m.getMem (regs .x10 + 64#64)) (m.getMem (regs .x10 + 56#64)) 48 ∧
    BufT env m (m.getMem (regs .x10 + 88#64)) (m.getMem (regs .x10 + 80#64)) 48

/-- **The total contract of the drop glue of `Layout`**: it writes nothing a caller sees. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (fun _ _ _ _ => True)

/-- **`TablesT` is kept** by a memory agreeing below `NEXT`, `NEXT` no lower, the `Table`s a buffer. -/
theorem TablesT.keep {env : Env} {m M : MachineState} {q : Word} {n : Word} (h : TablesT env m q n.toNat)
    (hb : BufT env m n q 80) (hn : (env.next m).toNat ≤ (env.next M).toNat)
    (hk : ∀ b : Word, b.toNat < (env.next m).toNat → M.getMem b = m.getMem b) : TablesT env M q n.toNat := by
  intro i hi
  obtain ⟨h1, h2⟩ := h i hi
  obtain ⟨hq1, hq2, -⟩ := hb.resolve_left (by omega)
  unfold Env.Live at hq2
  have hqn : q.toNat + 80 * n.toNat < 2 ^ 64 := by have := (env.next m).isLt; omega
  have h80 : 80 * i + 80 ≤ 80 * n.toNat := by omega
  have e : ∀ o, o < 80 → (q + BitVec.ofNat 64 (80 * i + o)).toNat = q.toNat + 80 * i + o := fun o ho => by
    rw [toNat_add_ofNat (show q.toNat + (80 * i + o) < 2 ^ 64 by omega)]; omega
  rw [hk _ (by rw [e _ (by omega)]; omega), hk _ (by rw [e _ (by omega)]; omega),
    hk _ (by rw [e _ (by omega)]; omega), hk _ (by rw [e _ (by omega)]; omega)]
  exact ⟨h1.mono hn, h2.mono hn⟩

-- Each of the three later calls' buffer is closed through the earlier calls' frames: three times the default.
set_option maxHeartbeats 600000 in
set_option rv_sym.heap true in
/-- **The drop glue of `Layout` is total**, with 16 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need nt nb : Nat} (hnt : 16 + nt ≤ need) (hnb : 16 + nb ≤ need)
    (ht : DropTablesT.SpecT env p L.dropGlueVecTable.idx nt)
    (hb : DropSliceSpecT env 48 p L.dropGlueVecBusBlock.idx nb) : SpecT env p i need := by
  rv_autoT hp stop [14] with [hL] using [ht, hb]
  have hlay := env.layout
  have hlim : env.stackLimit.toNat + 16 ≤ top.toNat := by omega
  have hk : ∀ b : Word, b.toNat < (env.next m).toNat →
      ((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).getMem b =
        m.getMem b := fun b hb' => by
    have ne : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 16 → b ≠ top + c := fun c k hc hk' he => by
      have := congrArg BitVec.toNat he; rw [CloneT.toNat_add_neg hc (by omega)] at this; omega
    rw [MachineState.getMem_setMem_ne (ne _ 16 rfl (by omega)), MachineState.getMem_setMem_ne (ne _ 8 rfl (by omega))]
  have hn : env.next ((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64)
      (regs .x8)) = env.next m := by
    rw [Env.next_setMem_stack (by rw [CloneT.toNat_add_neg (k := 16) rfl (by omega)]; omega),
      Env.next_setMem_stack (by rw [CloneT.toNat_add_neg (k := 8) rfl (by omega)]; omega)]
  have hTc := TablesT.keep hpre_11 hpre_10 (by rw [hn]) hk
  have hBc := VecReprT.BufT.mono hpre_10 (m' := (m.setMem (top + 18446744073709551608#64) ret).setMem
    (top + 18446744073709551600#64) (regs .x8)) (by rw [hn])
  clear hk
  rv_symT hp stop [16] with [hL] using [ht, hb]
  · exact hTc
  · have hn1 : (env.next m).toNat ≤ (env.next m1).toNat := by rw [← hn]; exact hret1_14.1
    clear hTc hBc hpre_10 hpre_11
    rv_symT hp stop [24] with [hL] using [hb]
    rv_symT hp stop [32] with [hL] using [hb]
    rv_symT hp with [hL] using [hb]

end Rv64mc.Proof.Runtime.DropLayoutT

/-- info: 'Rv64mc.Proof.Runtime.DropLayoutT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.DropLayoutT.total
