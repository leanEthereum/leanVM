module

public import NativeVm.Code.Phase7.RingFrame

/-!
# Phase 7a: ring switching

`ringSwitchC` refines `Model.ringSwitch`: the grind of `batchGrindingBits = 13` bits, the sixteen
challenges (`f` then `g`) sampled into the scratch's first 32 words (`ringLoopStep`, `r12`
counting down, `r13` at the next element), then `ringPure`: the coefficients and the target into
`ringR` (`RingAt`), from `q_keccak`'s slices (`KeccakOutAt`). `ringSwitchC_runs`: its contract,
writing `ringR` and `scratchR` only.
-/

@[expose] public section

namespace NativeVm.Code.Ring

open Native NativeVm.Model NativeVm.Transcript LeanVM.Parameters

/-! ## The code -/

/-- One challenge, stored at `r13`. -/
def ringLoopStep : Stmt := blk [
  Transcript.sampleChallenge,
  I (.store (at_ .r13 (wdisp 0)) .r9), I (.store (at_ .r13 (wdisp 1)) .r10),
  I (.addi .r13 (wdisp 2)), I (.subi .r12 1)]

/-- The work pointer in `rbp`, the count in `r12`, the first challenge's address in `r13`. -/
def ringStart : Stmt := blk [
  I (.load .rbp (cw ctxWork)), I (.movi .r12 16), I (.lea .r13 (at_ .rbp (wdisp chO)))]

/-- **Phase 7a**: the grind, the sixteen challenges, the coefficients and the target. -/
def ringSwitchC : Stmt := blk [
  I (.movi .rsi 13), Transcript.grind, ringStart, .loop (.cmp .ne .r12 (.imm 0)) ringLoopStep,
  ringPure]

/-! ## The challenges -/

theorem scratch_off : scratchR.off = 52670 := by decide
theorem scratch_size : scratchR.size = 32768 := by decide
theorem scratch_mem : scratchR ∈ regions := by decide +kernel
theorem ring_mem : ringR ∈ regions := by decide +kernel
theorem ringRegs_regions : ∀ r ∈ ringRegs, r ∈ regions := by decide +kernel

/-- After `k` challenges `acc`: the counters, the work pointer, the challenges. -/
def RingX (env : Env) (k : Nat) (acc : Array EW) (s : QState) : Prop :=
  k ≤ 16 ∧ acc.size = k ∧ s.reg .r12 = (16 - k).toUInt64 ∧
    s.reg .r13 = wd env.work (scratchR.off + 2 * k) ∧ s.reg .rbp = env.work ∧
    EWArr s.mem (wd env.work scratchR.off) acc

theorem RingX.stable {env : Env} {inp : Input} {mem : UInt64 → Option UInt64}
    (hin : Inputs env inp mem) {k : Nat} {acc : Array EW} : Stable env (RingX env k acc) := by
  rintro s s' ⟨h1, h2, h3, h4, h5, h6⟩ hk
  have hS := hin.keeps_same hk scratch_mem
  refine ⟨h1, h2, (hk.reg (by decide)).trans h3, (hk.reg (by decide)).trans h4,
    (hk.reg (by decide)).trans h5, h6.congr (n := 2 * acc.size) ?_ le_rfl⟩
  have := hS.sub (a := 0) (m := 2 * acc.size) (by rw [scratch_size]; omega)
  rwa [Region.at, wd_wd, Nat.add_zero] at this

theorem EWArr_push {mem : UInt64 → Option UInt64} {p : UInt64} {xs : Array EW} {x : EW}
    (h : EWArr mem p xs) (hx : EWAt mem (wd p (2 * xs.size)) x) : EWArr mem p (xs.push x) := by
  intro i hi
  rw [Array.size_push] at hi
  rw [Array.getElem_push]
  split
  · exact h i (by omega)
  · rw [show i = xs.size by omega]
    exact hx

/-- **One challenge.** -/
theorem ringLoopStep_ref {env : Env} {inp : Input} {s0 : QState} (hin : Inputs env inp s0.mem)
    {k : Nat} (hk : k < 16) (acc : Array EW) :
    Refines (fun t s ↦ CodeRel env t s ∧ Fr env ringRegs s0 (RingX env k acc) s) ringLoopStep
      (Model.sampleChallenge >>= fun x ↦ pure (acc.push x))
      (fun acc' t' s' ↦ CodeRel env t' s' ∧ Fr env ringRegs s0 (RingX env (k + 1) acc') s')
      (Kept env ringRegs s0) := by
  unfold ringLoopStep
  refine Refines.blk_cons (sampleChallenge_fr (RingX.stable hin)) fun x ↦ Refines.pure ?_
  rintro t s ⟨hc, ⟨hb, h1, h2, h3, h4, h5, h6⟩, h9, h10⟩
  have hww := workWords_lt hin
  have ho := scratch_off
  have e0 : wd (wd env.work (scratchR.off + 2 * k)) 0 = wd env.work (scratchR.off + 2 * k) := by
    rw [wd_wd, Nat.add_zero]
  have e1 : wd (wd env.work (scratchR.off + 2 * k)) 1 = wd env.work (scratchR.off + (2 * k + 1)) := by
    rw [wd_wd, Nat.add_assoc]
  have hj0 : 2 * k < scratchR.size := by rw [scratch_size]; omega
  have hj1 : 2 * k + 1 < scratchR.size := by rw [scratch_size]; omega
  have hs0 := hin.region_some hb scratch_mem hj0
  refine wp_store ((eval_work h4 0).trans e0) hs0 ?_
  have hb1 := hb.setMem (q := scratchR) (by simp) hj0 rfl hs0 (s.reg .r9)
  have hs1 := hin.region_some hb1 scratch_mem hj1
  refine wp_store ((eval_work (by reg_simp; exact h4) 1).trans e1) hs1 ?_
  have hb2 := hb1.setMem (q := scratchR) (by simp) hj1 rfl hs1 (s.reg .r10)
  refine wp_reg rfl (wp_reg rfl (wp_done ?_))
  simp only [QState.setMem_reg] at hb2 ⊢
  refine ⟨((((hc.setMem hin scratch_mem hj0 rfl hs0 _).setMem hin scratch_mem hj1 rfl hs1 _).setReg
    (by decide) _).setReg (by decide) _),
    ⟨(hb2.setReg (by decide) _).setReg (by decide) _, by omega, by rw [Array.size_push, h2],
      ?_, ?_, ?_, ?_⟩⟩
  · reg_simp
    rw [h3, toUInt64_sub1 (by omega)]
    congr 1
  · reg_simp
    rw [h4, wdisp_toUInt64, wd_add]
    congr 1
  · reg_simp
    exact h5
  · simp only [QState.setReg_mem]
    refine EWArr_push (h6.congr (n := 2 * acc.size) (fun j hj ↦ ?_) le_rfl) ⟨?_, ?_⟩
    · rw [wd_wd, setMem_wd_ne _ _ (by omega) (by omega) (by omega),
        setMem_wd_ne _ _ (by omega) (by omega) (by omega)]
    · rw [wd_wd, h2, setMem_wd_ne _ _ (by omega) (by omega) (by omega),
        setMem_wd_eq _ _ (by omega), h9]
    · rw [wd_wd, wd_wd, h2, setMem_wd_eq _ _ (by omega), h10]

/-- **The sixteen challenges.** -/
theorem ringLoop_ref {env : Env} {inp : Input} {s0 : QState} (hin : Inputs env inp s0.mem) :
    Refines (fun t s ↦ CodeRel env t s ∧ Fr env ringRegs s0 (RingX env 0 #[]) s)
      (.loop (.cmp .ne .r12 (.imm 0)) ringLoopStep) (sampleChallenges 16)
      (fun ch t s ↦ CodeRel env t s ∧ Fr env ringRegs s0 (RingX env 16 ch) s)
      (Kept env ringRegs s0) := by
  refine Refines.mono (Refines.foldlM (l := List.range 16)
    (Inv := fun k acc t s ↦ CodeRel env t s ∧ Fr env ringRegs s0 (RingX env k acc) s)
    ?_ ?_ (init := #[])) (fun _ _ h ↦ h) (fun _ _ _ h ↦ by rwa [List.length_range] at h)
    (fun _ h ↦ h)
  · rintro k acc t s ⟨-, -, h1, -, h3, -⟩
    rw [List.length_range, cond_ne, rhs_imm, h3,
      show ((0 : Int64).toUInt64) = (0 : Nat).toUInt64 from rfl, bne_iff_ne, ne_eq,
      NativeVm.Transcript.toUInt64_inj (by omega) (by omega)]
    omega
  · intro k hk acc
    rw [List.length_range] at hk
    exact ringLoopStep_ref hin hk acc

end NativeVm.Code.Ring
