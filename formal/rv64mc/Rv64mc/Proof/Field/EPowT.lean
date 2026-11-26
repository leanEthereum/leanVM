/-
  Rv64mc.Proof.Field.EPowT

  `GEN.pow` is total: `Spec.Field.EPow`'s postcondition, over any program holding its template, from the total
  contracts of `E::square` (`ESquareT`) and `E::mul` (`EMulT`). The partial proof (`EPow.lean`) ported: its loop,
  there an induction on the exponent's bits, is `Total.loop` at instruction 28 with the bits left as the measure
  (`LoopInv`, the partial `Inv` and what the windows need: the code map kept and `NEXT` not lowered).

  ## Main definitions

  * `specT`, `LoopInv`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Field.EPow
import Rv64mc.Proof.Field.ESquareT
import Rv64mc.Proof.Field.EMulT
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Field.EPowT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Field Rv64mc.Proof.Field.EPow
open Rv64mc.Gen.Verifier.Field.E.Pow (Link tmpl)
open Model (ePowLoop eSquare eMul)

/-- **The total contract of `GEN.pow`**: `EPow.spec`'s, as a `HoldsT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun _ _ => True) EPow.Post

/-- The loop's head with the shifted exponent below `2 ^ k`: the partial proof's `Inv` and what is left of the
    power, the code map kept and `NEXT` not lowered since the entry. -/
def LoopInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  ∃ (b o : Model.Limbs) (N : Word), (N >>> 1).toNat < 2 ^ k ∧
    Model.ePow Model.eGen (regs .x10) = ePowLoop (eSquare b) o (N >>> 1) ∧
    Inv env ret top regs m b o N R M ∧ M.code = m.code ∧ (env.next m).toNat ≤ (env.next M).toNat

set_option rv_sym.heap true in
/-- **`GEN.pow` is total.** -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needS needM : Nat} (hnS : 48 + needS ≤ need) (hnM : 48 + needM ≤ need)
    (hsq : ESquareT.specT env p L.square.idx needS) (hmul : EMulT.specT env p L.mul.idx needM) :
    specT env p i need := by
  rv_autoT hp with [hL] using [hsq, hmul]
  · rw [hc, Model.ePow, ePowLoop_zero]; rfl
  · rw [hc, Model.ePow, ePowLoop_zero]; rfl
  all_goals refine Total.loop (LoopInv env ret top regs m) ?_ 64 _ _ ?_
  -- the loop's body, from its head to its head or to the return
  any_goals
    intro k R M hI ih
    obtain ⟨b, o, N, hb, ht, hinv, hcode, hnm⟩ := hI
    rv_introT hinv
    rv_symT hp with [hL] using [hsq, hmul]
    · rw [ht, hc, ePowLoop_zero]
    · rw [ht, hc, ePowLoop_zero]
    all_goals rcases k with _ | k
    · exact absurd (half_zero hb) hc_3
    · refine ih k _ _ (by omega) ?_
      refine ⟨eSquare b, o, N >>> 1, half_lt hb, ?_, ?_, by rw [hret1_18, hcode], by have := hret1_14.1; omega⟩
      · rw [ht, ePowLoop_step _ _ hc_3, ite_eq_right (bit_eq hc)]
      · rv_closeT
    · exact absurd (half_zero hb) hc_3
    · refine ih k _ _ (by omega) ?_
      refine ⟨eSquare b, eMul o (eSquare b), N >>> 1, half_lt hb, ?_, ?_, by rw [hret2_18, hret1_18, hcode],
        by have := hret1_14.1; have := hret2_14.1; omega⟩
      · rw [ht, ePowLoop_step _ _ hc_3, ite_eq_left (bit_ne hc)]
      · rv_closeT
  -- the loop's entry, after the first bit
  · refine ⟨Model.eGen, Model.eOne, regs .x10, BitVec.isLt _, ?_, ?_, rfl, by rv_closeT⟩
    · rw [Model.ePow, ePowLoop_step _ _ hc_1, ite_eq_right (bit_eq hc)]
    · rv_closeT
  · refine ⟨Model.eGen, eMul Model.eOne Model.eGen, regs .x10, BitVec.isLt _, ?_, ?_, by rv_closeT, by rv_closeT⟩
    · rw [Model.ePow, ePowLoop_step _ _ hc_1, ite_eq_left (bit_ne hc)]
    · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> rv_closeT

end Rv64mc.Proof.Field.EPowT

/-- info: 'Rv64mc.Proof.Field.EPowT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Field.EPowT.total
