/-
  Rv64mc.Proof.Layout.PlacementNextT

  `GenericShunt::next` over `build_layout`'s `kappas.iter().enumerate().map(placement)` is total: called with the
  result's slot `sret` (`a0`) and the shunt at `it` (`a1`: the slice iterator's `cur` and `end`, the enumeration's
  count, the closure's environment `c`, whose first word is the vector `offsets`, and the residual `r`), it returns
  tag `2` at the end of the slice; otherwise it reads `kappa = *cur`, advances `cur` by 8, and calls `qkeccak_slot`
  and `is_output_lane` on the count, reading `offsets[4]` or `offsets[count]` (each checked against the vector's
  length, else `panic_bounds_check`); a `None` offset stores the error (`28`) at `r` and returns tag `2`, any other
  outcome a placement or `None` (tags `1`, `0`). The run ends with the guest's abort (`AbortStop`) where a bounds
  check does. Safety only: it states the end or the cursor's advance, which its caller's loop needs to end, not the
  placement.

  The precondition (`IterT`): the shunt's 40 bytes in a caller's frame (at or above the stack pointer), in a window,
  aligned; the slice `[cur, end)` whole words, in a window unless empty; `c` and `r` in windows and aligned, `r` a
  caller's to write; `offsets` a vector's of 16-byte elements (`VecT`); `c`, `offsets`' header, `r` and `sret` apart
  from the cursor's word, which the function writes before it reads them. At the image's two call sites
  (`build_layout`, the shunt at `sp + 0x148` and `sp + 0xd8`) all of them but `offsets`' buffer lie in its frame.

  ## Main definitions

  * `IterT`, `PreT`, `PostT`, `OutT`, `SpecT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Keccak.TryFromFnT
import Rv64mc.Proof.Runtime.ReserveT
import Rv64mc.Proof.Layout.QkeccakSlotT
import Rv64mc.Proof.Layout.IsOutputLaneT
import Rv64mc.Gen.Tmpl.Core.Iter.Adapters.GenericShuntMapEnumerateHad7e794e.AsIterator.Next

namespace Rv64mc.Proof.Layout.PlacementNextT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT VecT)
open Rv64mc.Proof.Keccak.TryFromFnT (SliceT elem_ok)
open Rv64mc.Gen.Core.Iter.Adapters.GenericShuntMapEnumerateHad7e794e.AsIterator.Next (Link tmpl)

/-- `[a, a + n)` in a caller's frame: at or above the stack pointer `sp`, below the stack window's end. -/
def StackObj (sp a : Word) (n : Nat) : Prop := sp.toNat ≤ a.toNat ∧ a.toNat + n ≤ 0xc0000000

/-- The shunt at `it`, a caller's object, aligned, below the result's slot `s`: its slice `[cur, end)` whole words,
    in a window and aligned unless empty; the closure's environment `c` a caller's word below the shunt, aligned,
    holding the address of the vector `offsets` of 16-byte elements (`VecT`), whose header is a caller's below the
    shunt; the residual `r` a caller's word apart from the cursor's, aligned. -/
def IterT (env : Env) (m : MachineState) (sp s it : Word) : Prop :=
  StackObj sp it 40 ∧ it.toNat % 8 = 0 ∧ it.toNat + 8 ≤ s.toNat ∧
    (m.getMem it).toNat ≤ (m.getMem (it + 8#64)).toNat ∧
    ((m.getMem (it + 8#64)).toNat - (m.getMem it).toNat) % 8 = 0 ∧
    (m.getMem it = m.getMem (it + 8#64) ∨
      (InWin env (m.getMem it) ((m.getMem (it + 8#64)).toNat - (m.getMem it).toNat) ∧
        (m.getMem it).toNat % 8 = 0)) ∧
    sp.toNat ≤ (m.getMem (it + 24#64)).toNat ∧ (m.getMem (it + 24#64)).toNat + 8 ≤ it.toNat ∧
    (m.getMem (it + 24#64)).toNat % 8 = 0 ∧
    sp.toNat ≤ (m.getMem (m.getMem (it + 24#64))).toNat ∧
    (m.getMem (m.getMem (it + 24#64))).toNat + 24 ≤ it.toNat ∧
    VecT env m (m.getMem (m.getMem (it + 24#64))) 16 ∧
    StackObj sp (m.getMem (it + 32#64)) 8 ∧ (m.getMem (it + 32#64)).toNat % 8 = 0 ∧
    ((m.getMem (it + 32#64)).toNat + 8 ≤ it.toNat ∨ it.toNat + 8 ≤ (m.getMem (it + 32#64)).toNat)

/-- The total precondition: the result's slot a caller's 24 bytes, aligned; the shunt `IterT`. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  StackObj (regs .x2) (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧ IterT env m (regs .x2) (regs .x10) (regs .x11)

/-- The total postcondition: the end (tag `2`), or the cursor advanced by a word from below the slice's end. -/
def PostT (_env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  m'.getMem (regs .x10) = 2#64 ∨
    ((m.getMem (regs .x11)).toNat < (m.getMem (regs .x11 + 8#64)).toNat ∧
      m'.getMem (regs .x11) = m.getMem (regs .x11) + 8#64)

/-- What `next` writes besides its stack: the result, the shunt's cursor and count, the residual. -/
def OutT (regs : Reg → Word) (m : MachineState) (b : Word) : Prop :=
  InRange (regs .x10) 24 b ∨ InRange (regs .x11) 24 b ∨ InRange (m.getMem (regs .x11 + 32#64)) 8 b

/-- **The total contract of `GenericShunt::next` over `build_layout`'s placements**, or the guest's abort. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) OutT AbortStop

/-- Element `4` of a vector's buffer of 16-byte elements, below its length, in a window and aligned. -/
theorem elem4_ok {env : Env} {top : Word} {m : MachineState} {q : Word} {n : Nat} (hW : Windows env top m)
    (hs : SliceT env q n) (hj : 4 < n) :
    (inWindow (q + 64#64) 8 = true ∧ (q + 64#64).toNat % 8 = 0) ∧
      (inWindow (q + 72#64) 8 = true ∧ (q + 72#64).toNat % 8 = 0) := by
  rcases hs with h0 | ⟨hw, hal⟩
  · omega
  have hlt := hw.lt
  exact ⟨hw.dword hW hal (o := 64) (toNat_add_ofNat (by omega)) (by omega) (by omega),
    hw.dword hW hal (o := 72) (toNat_add_ofNat (by omega)) (by omega) (by omega)⟩

/-- The slice's word at `cur`, past the check `cur ≠ end`, in a window and aligned. -/
theorem cur_ok {env : Env} {top : Word} {m : MachineState} {c e : Word} (hW : Windows env top m)
    (hle : c.toNat ≤ e.toNat) (h8 : (e.toNat - c.toNat) % 8 = 0)
    (hs : c = e ∨ (InWin env c (e.toNat - c.toNat) ∧ c.toNat % 8 = 0)) (hne : ¬ c = e) :
    inWindow c 8 = true ∧ c.toNat % 8 = 0 := by
  have hlt : c.toNat < e.toNat := Nat.lt_of_le_of_ne hle fun h => hne (BitVec.eq_of_toNat_eq h)
  rcases hs with h | ⟨hw, hal⟩
  · exact absurd h hne
  · exact hw.dword hW hal (o := 0) rfl (by omega) rfl

set_option rv_sym.heap true in
/-- **`GenericShunt::next` over `build_layout`'s placements is total**, with 48 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needQ needO needP : Nat} (hnQ : 48 + needQ ≤ need) (hnO : 48 + needO ≤ need) (hnP : 48 + needP ≤ need)
    (hqs : QkeccakSlotT.specT env p L.qkeccakSlot.idx needQ)
    (hio : IsOutputLaneT.specT env p L.isOutputLane.idx needO)
    (hpb : Aborts env p L.panicBoundsCheck.idx needP) : SpecT env p i need := by
  rv_autoT hp with [hL] using [hqs, hio, hpb]
  all_goals
    have hsl : SliceT env (m.getMem (m.getMem (m.getMem (regs .x11 + 24#64)) + 8#64))
        (m.getMem (m.getMem (m.getMem (regs .x11 + 24#64)) + 16#64)).toNat := by
      have hb := hpre_24
      have hl := hpre_26
      simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero] at hb
      rw [Runtime.ReserveT.vecLen_eq, Runtime.ReserveT.vecCap_eq] at hl
      exact SliceT.of_buf hb hpre_5 hl
  all_goals try first
    | exact Or.inl rfl
    | exact Or.inr ⟨Nat.lt_of_le_of_ne hpre_13 fun h =>
        ‹¬ m.getMem (regs .x11) = m.getMem (regs .x11 + 8#64)› (BitVec.eq_of_toNat_eq h), rfl⟩
  · exact (cur_ok hpre_32 hpre_13 hpre_14 hpre_15 hc).1
  · exact (cur_ok hpre_32 hpre_13 hpre_14 hpre_15 hc).2
  all_goals try
    have hj : m.getMem (regs .x11 + 16#64) <
        m.getMem (m.getMem (m.getMem (regs .x11 + 24#64)) + 16#64) := ‹_›
  · exact (elem_ok hpre_32 hsl (BitVec.lt_def.1 hj)).1.1
  · exact (elem_ok hpre_32 hsl (BitVec.lt_def.1 hj)).1.2
  · exact (elem_ok hpre_32 hsl (BitVec.lt_def.1 hj)).2.1
  · exact (elem_ok hpre_32 hsl (BitVec.lt_def.1 hj)).2.2
  all_goals
    have h4 : 4 < (m.getMem (m.getMem (m.getMem (regs .x11 + 24#64)) + 16#64)).toNat := by
      simpa using BitVec.lt_def.1 ‹(4#64 : Word) < m.getMem (m.getMem (m.getMem (regs .x11 + 24#64)) + 16#64)›
  · exact (elem4_ok hpre_32 hsl h4).1.1
  · exact (elem4_ok hpre_32 hsl h4).1.2
  · exact (elem4_ok hpre_32 hsl h4).2.1
  · exact (elem4_ok hpre_32 hsl h4).2.2

end Rv64mc.Proof.Layout.PlacementNextT

/-- info: 'Rv64mc.Proof.Layout.PlacementNextT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.PlacementNextT.total
