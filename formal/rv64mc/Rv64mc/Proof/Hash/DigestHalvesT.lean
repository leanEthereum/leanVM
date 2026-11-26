/-
  Rv64mc.Proof.Hash.DigestHalvesT

  `Digest::halves` is total: `DigestHalves.Post`'s two field elements (`Spec.Hash.DigestHalves`), over any program
  holding its template, from `Digest::words`'s total contract (`DigestWordsT.specT`). The partial proof
  (`DigestHalves.lean`) ported by `rv_autoT`. The precondition (`PreT`) adds the slot written in a window, 8-byte
  aligned, and the digest's bytes in a window apart from the stack below the stack pointer, which `Digest::words`'
  precondition asks of its source.

  ## Main definitions

  * `PreT`, `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Hash.DigestHalves
import Rv64mc.Proof.Hash.DigestWordsT

namespace Rv64mc.Proof.Hash.DigestHalvesT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Hash.DigestHalves Rv64mc.Spec.Runtime
open Rv64mc.Proof.Hash.DigestHalves
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Gen.Verifier.Hash.Digest.Halves (Link tmpl)

/-- The total precondition: `Pre`, the slot in a window and 8-byte aligned, the digest in a window apart from the
    stack below the stack pointer. -/
def PreT (env : Env) (d : List (BitVec 8)) (regs : Reg → Word) (m : MachineState) : Prop :=
  Pre env d regs m ∧ InWin env (regs .x10) (2 * Layouts.E.byteSize) ∧ (regs .x10).toNat % 8 = 0 ∧
    inWindow (regs .x11) Layouts.Digest.byteSize = true ∧ OffStack env (regs .x2) (regs .x11) Layouts.Digest.byteSize

/-- **The total contract of `Digest::halves`**: `DigestHalves.spec`'s, as a `HoldsT`, from `PreT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ d, HoldsT env p i need (PreT env d) (Post d) Out

set_option rv_sym.heap true in
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needW : Nat} (hnW : 48 + needW ≤ need) (hw : DigestWordsT.specT env p L.words.idx needW) :
    specT env p i need := by
  intro d
  rv_autoT hp with [hL] using [hw d]
  · have hlim : env.stackLimit.toNat + 48 ≤ top.toNat := by omega
    have h8 := slot_toNat (top := top) (c := 8) (by omega) (by decide) (by decide)
    have h16 := slot_toNat (top := top) (c := 16) (by omega) (by decide) (by decide)
    simp only [show (2 : Nat) ^ 64 - 8 = 18446744073709551608 from rfl,
      show (2 : Nat) ^ 64 - 16 = 18446744073709551600 from rfl] at h8 h16
    refine ⟨hpre_6.1, hpre_6.2.1, fun k hk => ?_⟩
    have hk' : k < Layouts.Digest.byteSize := by rw [← hpre_6.1]; exact hk
    rw [getByte_setMem_ne (slot_ne_align ⟨hpre_7, hpre_8⟩ hk' hpre_5 (by rw [h16]; omega) (by rw [h16, hpre_2]; omega)
        (by rw [hpre_2]; omega)),
      getByte_setMem_ne (slot_ne_align ⟨hpre_7, hpre_8⟩ hk' hpre_5 (by rw [h8]; omega) (by rw [h8, hpre_2]; omega)
        (by rw [hpre_2]; omega)), hpre_6.2.2 k hk]
  all_goals
    have hl : (Model.digestWordsRust d).length = 4 := by simp [Model.digestWordsRust]
    have g : ∀ k (hk : k < 4), (Model.digestWordsRust d).getD k 0 =
        m1.getMem (top + 18446744073709551568#64 + BitVec.ofNat 64 (8 * k)) := fun k hk => by
      rw [List.getD_eq_getElem _ _ (by omega), hret1_16.2 k (by omega)]
    have g0 := g 0 (by decide); have g1 := g 1 (by decide); have g2 := g 2 (by decide); have g3 := g 3 (by decide)
    simp only [Nat.mul_zero, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc,
      BitVec.reduceAdd] at g0 g1 g2 g3
    simp (config := { decide := true }) only [EAt, Layouts.E.c0, Layouts.E.c1, Layouts.E.byteSize,
      Model.digestHalvesRust, g0, g1, g2, g3, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc,
      BitVec.reduceAdd, MachineState.getMem_setMem_eq, MachineState.getMem_setMem_ne, ne_eq, BitVec.add_right_inj,
      Tactic.ne_add]

end Rv64mc.Proof.Hash.DigestHalvesT

/-- info: 'Rv64mc.Proof.Hash.DigestHalvesT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Hash.DigestHalvesT.total
