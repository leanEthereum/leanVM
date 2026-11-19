module

public import NativeVm.Code.Phase7.RingSwitch

/-!
# Phase 7a's contract

`ringSwitchC_runs`: from a state holding the model's (`CodeRel`), the inputs and `q_keccak`'s point
and slices (`KeccakOutAt`), `ringSwitchC` runs `Model.ringSwitch` (`Runs`), writing `ringR` and
`scratchR` only: where it returns, the point handed back is `q_keccak`'s and the target and the
coefficients are at `ringR` (`RingAt`).
-/

@[expose] public section

namespace NativeVm.Code.Ring

open Native NativeVm.Model NativeVm.Transcript LeanVM.Parameters
open NativeVm.Field (EArr ew)
open LeanVM.Protocol.Verifier (ringMapWidth ringCoefficients ringTarget)

theorem keccak_mem : keccakR ∈ regions := by decide +kernel

theorem keccak_apart : ∀ r ∈ ringRegs, keccakR.Apart r := by decide +kernel

theorem toList_map_extract_drop (x : Array EW) (n : Nat) :
    (x.extract n x.size).toList.map EW.toE = (x.toList.map EW.toE).drop n := by
  simp [Array.toList_extract, List.extract_eq_take_drop, List.map_drop]

theorem wd_eq_ew (b : UInt64) (k : Nat) : wd b k = NativeVm.Field.ew b k := rfl

theorem ew_succ8 (b : UInt64) (k : Nat) : ew b k + 8 = ew b (k + 1) := by
  simp only [ew, Nat.toUInt64_eq, Nat.mul_add, UInt64.ofNat_add, Nat.mul_one, UInt64.add_assoc]
  rfl

/-- **The arithmetic**, from the sixteen challenges. -/
theorem ringPure_ref {env : Env} {inp : Input} {s0 : QState} (hin : Inputs env inp s0.mem)
    {point slices : Array EW} (hk : KeccakOutAt s0.mem (keccakR.at env.work) point slices)
    (ch : Array EW) :
    Refines (fun t s ↦ CodeRel env t s ∧ Fr env ringRegs s0 (RingX env 16 ch) s) ringPure
      (pure (Model.ringTarget slices (ch.extract 0 ringMapWidth) (ch.extract ringMapWidth ch.size),
        point, Model.ringCoefficients (ch.extract 0 ringMapWidth) (ch.extract ringMapWidth ch.size)))
      (fun r t s ↦ CodeRel env t s ∧ (r.2.1 = point ∧ RingAt s.mem (ringR.at env.work) r.1 r.2.2) ∧
        Kept env ringRegs s0 s)
      (Kept env ringRegs s0) := by
  refine Refines.pure ?_
  rintro t s ⟨hc, ⟨hb, -, h2, -, -, h5, h6⟩⟩
  have hinS : Inputs env inp s.mem :=
    hin.kept hb.1 (fun r hr ↦ stop_le_of_mem (ringRegs_regions r hr) _) hb.2
  have hkS := hk.congr (hb.same hin ringRegs_regions keccak_mem keccak_apart)
  obtain ⟨-, hsz, hsl⟩ := hkS
  set chL := ch.toList.map EW.toE with hchL
  have hchl : chL.length = 16 := by rw [hchL, List.length_map, Array.length_toList, h2]
  have hch : EArr s.mem (ew env.work chO) chL := by
    have := EWArr_iff_EArr.mp h6
    rwa [wd_eq_ew, show scratchR.off = chO by decide] at this
  have hS : EArr s.mem (ew env.work slO) (slices.toList.map EW.toE) := by
    have := EWArr_iff_EArr.mp hsl
    rwa [Region.at, wd_wd, wd_eq_ew, show keccakR.off + vecWords pointCap = slO by decide] at this
  have hslL : (slices.toList.map EW.toE).length = 64 := by
    rw [List.length_map, Array.length_toList, hsz]; rfl
  have hroff : ringR.off = 27931 := by decide
  have hsoff := scratch_off
  have hrsz : ringR.size = 130 := by decide
  have hdomR : ∀ k < 130, (s.mem (ew env.work (tgO + k))).isSome := fun k hk ↦ by
    have := hin.region_some hb ring_mem (j := k) (by omega)
    rwa [wd_eq_ew, hroff] at this
  have hdomS : ∀ k < 130, (s.mem (ew env.work (imgO + k))).isSome := fun k hk ↦ by
    have := hin.region_some hb scratch_mem (j := 32 + k) (by rw [scratch_size]; omega)
    rwa [wd_eq_ew, hsoff, ← Nat.add_assoc] at this
  have hG : EArr s.mem (ew env.work (chO + 16)) (chL.drop 8) := by
    have := Ring.EArr.drop hch (k := 8) (by omega)
    rwa [ew_ew] at this
  refine WP.mono (WP.frames ringPure_writes.1 ringPure_writes.2 (ringPure_spec (F := fun _ ↦ False)
    (W := env.work) h5 (Ring.EArr.take hch 8) (by rw [List.length_take]; omega) hG
    (by rw [List.length_drop]; omega) hS hslL hdomR hdomS))
    (fun s' ⟨⟨_, hT, hC, hF⟩, hrdi, _, hdom⟩ ↦ ?_) fun _ h ↦ h
  have hf : (ch.extract 0 ringMapWidth).toList.map EW.toE = chL.take 8 :=
    toList_map_extract ch 8
  have hg : (ch.extract ringMapWidth ch.size).toList.map EW.toE = chL.drop 8 :=
    toList_map_extract_drop ch 8
  refine ⟨codeRel_ringPure hc hinS hrdi hdom hF, ⟨rfl, ?_, ?_, ?_⟩,
    (Base.ringPure hb hrdi hdom hF).1⟩
  · rw [EWAt_iff_EAt, Equiv.toE_ringTarget, hf, hg]
    obtain ⟨t0, t1⟩ := hT
    simp only [ew_ew, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at t0 t1
    have ho : ringR.off = tgO := by decide
    refine ⟨?_, ?_⟩
    · rw [Region.at, wd_eq_ew, ho]; exact t0
    · rw [Region.at, wd_eq_ew, ho, ew_succ8]; exact t1
  · have := congrArg List.length (Equiv.toList_map_ringCoefficients (ch.extract 0 ringMapWidth)
      (ch.extract ringMapWidth ch.size))
    rw [List.length_map, Array.length_toList, hf, hg, ringCoefficients_length, List.length_take,
      List.length_drop, hchl] at this
    rw [this]; rfl
  · rw [EWArr_iff_EArr, Equiv.toList_map_ringCoefficients, hf, hg, Region.at, wd_wd, wd_eq_ew,
      hroff]
    exact hC

/-- **Phase 7a's contract**: `ringSwitchC` runs `Model.ringSwitch`, writing `ringR` and
`scratchR` only; where it returns, the point is `q_keccak`'s and `RingAt` holds the target and the
coefficients. -/
theorem ringSwitchC_runs {env : Env} {inp : Input} {t : TState} {s : QState}
    {point slices : Array EW} (h : CodeRel env t s) (hin : Inputs env inp s.mem)
    (hk : KeccakOutAt s.mem (keccakR.at env.work) point slices) :
    Runs env ringSwitchC (Model.ringSwitch point slices) t s ringRegs fun r s' ↦
      r.2.1 = point ∧ RingAt s'.mem (ringR.at env.work) r.1 r.2.2 := by
  apply runs_of_refines
  unfold Model.ringSwitch ringSwitchC
  refine Refines.pre_blk (P' := fun t' s' ↦ CodeRel env t' s' ∧
    Fr env ringRegs s (fun _ ↦ True) s' ∧ s'.reg .rsi = Whir.batchGrindingBits.toUInt64) ?_ ?_
  · rintro t' s' ⟨rfl, rfl⟩
    exact WP.ins rfl ⟨h.setReg (by decide) _, ⟨(Base.start h.rdi).setReg (by decide) _, trivial⟩,
      by reg_simp; rfl⟩
  refine Refines.blk_cons (grind_fr (by decide) (by decide) stable_true) fun _ ↦ ?_
  refine Refines.pre_blk (P' := fun t' s' ↦ CodeRel env t' s' ∧
    Fr env ringRegs s (RingX env 0 #[]) s') ?_ ?_
  · rintro t' s' ⟨hc', hb', -⟩
    have hrdi : s'.reg .rdi = env.ctx := hb'.1.1
    unfold ringStart
    refine wp_load (eval_cw hrdi _) hc'.layout.workPtr ?_
    refine wp_reg rfl (wp_reg rfl (wp_done ⟨?_, ⟨?_, by omega, rfl, ?_, ?_, ?_,
      fun i h ↦ absurd h (Nat.not_lt_zero _)⟩⟩))
    · exact ((hc'.setReg (by decide) _).setReg (by decide) _).setReg (by decide) _
    · exact ((hb'.setReg (by decide) _).setReg (by decide) _).setReg (by decide) _
    · reg_simp; rfl
    · reg_simp
      rw [eval_work (w := env.work) (by reg_simp) _, scratch_off]
    · reg_simp
  refine Refines.blk_cons (ringLoop_ref hin) fun ch ↦ ?_
  exact ringPure_ref hin hk ch

end NativeVm.Code.Ring
