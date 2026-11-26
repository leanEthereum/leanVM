/-
  Rv64mc.Proof.Multilinear.ScalerNew

  `Scaler::new` keeps its contract (`Spec.Multilinear.Scaler.newSpec`), over any program holding its template, from
  `Scaled::new`'s: below `256` uses it stores `Plain(r)` at `sret` (the frame of the stores by `Proof.Layout.Out`),
  otherwise it tail-calls `Scaled::new` on the same slot.
-/

import Rv64mc.Spec.Multilinear.Scaler
import Rv64mc.Spec.Field.Scaled
import Rv64mc.Proof.Layout.Out
import Rv64mc.Gen.Tmpl.Verifier.Multilinear.Scaler.New
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Multilinear.ScalerNew

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Multilinear.Scaler Rv64mc.Proof.Layout
open Rv64mc.Gen.Verifier.Multilinear.Scaler.New (Link tmpl)

theorem ne8 (a : Word) : a + 8#64 ≠ a := Tactic.add_ne (by decide)
theorem ne16 (a : Word) : a + 16#64 ≠ a := Tactic.add_ne (by decide)
theorem ne8_16 (a : Word) : a + 8#64 ≠ a + 16#64 := Tactic.add_ne_add (by decide)

theorem uses_le {u : Word} (h : u ≤ 255#64) : ¬ 256 ≤ u.toNat := by
  rw [BitVec.le_def] at h; simp at h; omega

theorem uses_gt {u : Word} (h : 255#64 < u) : 256 ≤ u.toNat := by
  rw [BitVec.lt_def] at h; simp at h; omega

/-- **`Scaler::new` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needS : Nat} (hnS : needS ≤ need) (hsn : Spec.Field.Scaled.newSpec env p L.new.idx needS) :
    newSpec env p i need := by
  intro r
  rv_auto hp with [hL] using [hsn]
  all_goals
    have hlim : env.stackLimit.toNat ≤ top.toNat := by omega
    rw [hpre_2] at hpre_6
    have hown : env.Owned m top (regs .x10) byteSize := ⟨hpre_6, hpre_7⟩
    have s0 := owned_slot0 hown hpre_5 hlim (by decide)
    have s8 := owned_slot (k := 8) hown hpre_5 hlim (by decide)
    have s16 := owned_slot (k := 16) hown hpre_5 hlim (by decide)
  · exact frame_setMem_out (frame_setMem_out (frame_setMem_out (Env.Frame.refl hpre_5) s0.1 s0.2.1) s8.1 s8.2.1)
      s16.1 s16.2.1
  · exact Env.static_setMem (Env.static_setMem (Env.static_setMem hpre_4 s0.2.2) s8.2.2) s16.2.2
  · simp only [Model.Scaler.new, uses_le hc, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩
    · rw [MachineState.getMem_setMem_ne (ne16 _).symm, MachineState.getMem_setMem_ne (ne8 _).symm,
        MachineState.getMem_setMem_eq]
    · rw [MachineState.getMem_setMem_ne (ne8_16 _), MachineState.getMem_setMem_eq]
    · rw [MachineState.getMem_setMem_eq]
  · omega
  · exact hpre_6
  · exact hpre_7
  · exact hret1_14
  · simp only [Model.Scaler.new, uses_gt hc, ↓reduceIte]
    obtain ⟨ptr, cap, hv, hf⟩ := hret1_16
    refine ⟨ptr, cap, hv, ?_⟩
    have := hf.live; have := hv.len_le
    rw [show Model.scaledNewE r = Model.scaledNew ((Model.limbs r).1, (Model.limbs r).2) from rfl]
    unfold Env.Live at *; simp only [Layouts.E.byteSize] at *; omega

end Rv64mc.Proof.Multilinear.ScalerNew
