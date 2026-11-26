/-
  Rv64mc.Proof.Keccak.LinearTransposeT

  `linear_transpose::<E>`'s partial proof (`LinearTranspose.lean`) ported to `HoldsT`, loop by loop: each loop of
  the partial proof, there an induction on the positions left with a continuation, is `Total.loop` here with them as
  the measure, the partial invariant and the code map kept.

  ## Main definitions

  * `LInv2`

  ## Main results

  * `loop2`: the column sums
-/

import Rv64mc.Proof.Keccak.LinearTranspose
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Keccak.LinearTransposeT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters
open Rv64mc.Proof.Keccak.LinearTranspose
open Rv64mc.Gen.Verifier.Keccak.LinearTransposeE (Link tmpl)
open Rv64mc.Proof.Multilinear (step_ptr)

/-- The column loop's head with `k + 1` positions left: `Inv2` after the others, and the code map kept. -/
def LInv2 (env : Env) (ws : List E) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  ∃ j, j + k + 1 = 1600 ∧ Inv2 env ws ret top regs m j R M ∧ M.code = m.code

set_option rv_sym.heap true in
/-- **The column sums**, from the loop's head to its exit (instruction 190). -/
theorem loop2 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} {ws : List E}
    (hp : p[i]? = some (tmpl L)) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState} (htop : env.stackLimit.toNat + 30816 ≤ top.toNat)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hnext : ∀ R M, Exit2 env ws ret top regs m R M → M.code = m.code →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 190, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, LInv2 env ws ret top regs m k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 154, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv2 env ws ret top regs m) fun k R M hI ih => ?_
  obtain ⟨j, hj, hI, hcode⟩ := hI
  have hjl : j < 1600 := by omega
  have := top.isLt
  have hgb := gBase_toNat (top := top) (by omega)
  have hcb := colsBase_toNat (top := top) (by omega)
  have g0 : (top + 18446744073709520824#64 + BitVec.ofNat 64 (16 * j)).toNat = top.toNat - 30792 + 16 * j := by
    rw [toNat_elem (by omega), hgb]
  have g8 : (top + 18446744073709520824#64 + BitVec.ofNat 64 (16 * j) + 8#64).toNat =
      top.toNat - 30792 + 16 * j + 8 := by
    rw [toNat_elem8 (by omega), hgb]
  obtain ⟨c0, c8⟩ := cols_elem (top := top) (by omega) (Nat.mod_lt j (show 320 > 0 by decide))
  rv_introT hI
  rv_symT hp stop [168]
  rw [cols_addr _ hjl, cols_addr8 _ hjl]
  rv_symT hp stop [154, 190]
  all_goals simp only [(hI_23 _ (Nat.mod_lt _ (show 320 > 0 by decide))).1,
    (hI_23 _ (Nat.mod_lt _ (show 320 > 0 by decide))).2, (hI_22 _ hjl).1, (hI_22 _ hjl).2]
  all_goals obtain ⟨f1, f2, f3, f4⟩ := loop2_mem htop hjl hI_13 hI_14 hI_22 hI_23
  · -- back to the head
    have hk0 : k ≠ 0 := fun h0 => hc (by rw [succ_ofNat, show j + 1 = 1600 by omega])
    clear hc
    refine ih (k - 1) _ _ (by omega) ⟨j + 1, by omega, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, f1, f2⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, f3, f4⟩, hcode⟩
    all_goals rv_closeT
    · exact step16 _ _
    · exact succ_ofNat _
    · exact step_ptr _ _
    · exact step_ptr _ _
  · have hj1 : j + 1 = 1600 := by
      rw [succ_ofNat] at hc; exact (ofNat_inj (by omega) (by decide)).1 hc
    clear hc
    refine hnext _ _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, f1, f2⟩, f3, by rw [← hj1]; exact f4⟩ hcode
    all_goals rv_closeT

end Rv64mc.Proof.Keccak.LinearTransposeT
