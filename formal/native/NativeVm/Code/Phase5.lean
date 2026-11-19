module

public import NativeVm.Code.Phase5.Setup

/-!
# Phase 5: the public input

The code of `Model.publicInputPhase`, proved against it (`phase5_ok : Phase5Ok phase5`).

The challenge `c` (`sampleChallenge`); `pubSetup` saves it, finds the first free claim slot and
raises the claims' count by two, and counts the point's coordinates `1 + (κ − 1)`; `pubClaim 0` and
`pubClaim 1` write memory columns `0` and `1`'s claims into the two slots: the point `(c, 0, …, 0)`
and limb `l`'s value, the line through `w[l]`, `w[2 + l]` at `c`. The model's step is the challenge
and these two claims (`publicInputPhase_eq`).
-/

@[expose] public section

namespace NativeVm.Code

open Native NativeVm.Model NativeVm.Transcript LeanVM.Parameters LeanVM.Protocol.Verifier

/-! ## The code -/

/-- **Phase 5**: the public input's two column claims, appended at `claimsR`. -/
def phase5 : Stmt := blk [
  Transcript.sampleChallenge, pubSetup, pubClaim 0, I (.addi .r12 (wdisp claimWords)), pubClaim 1]

/-! ## The model -/

/-- The two claims at the challenge `c`. -/
def pubClaims (layout : LayoutW) (pub : Vector UInt64 4) (c : EW) : Array ColumnClaimW :=
  #[⟨0, #[c] ++ Array.replicate ((layout.placement memory0).variableCount - 1) 0,
      multilinearEval #[EW.ofK pub[0], EW.ofK pub[2]] #[c]⟩,
    ⟨1, #[c] ++ Array.replicate ((layout.placement memory0).variableCount - 1) 0,
      multilinearEval #[EW.ofK pub[1], EW.ofK pub[3]] #[c]⟩]

theorem publicInputPhase_eq (layout : LayoutW) (pub : Vector UInt64 4) :
    Model.publicInputPhase layout pub =
      (Model.sampleChallenge >>= fun c ↦ pure (pubClaims layout pub c)) := by
  unfold Model.publicInputPhase
  congr 1
  funext c
  simp [pubClaims, memory0, memory1]

/-! ## The contract -/

theorem claimsAt_stable {env : Env} {inp : Input} {mem : UInt64 → Option UInt64}
    (hin : Inputs env inp mem) {acc : Array ColumnClaimW} :
    Stable env fun s ↦ ClaimsAt s.mem (claimsR.at env.work) acc :=
  fun _ _ h hk ↦ h.congr (hin.keeps_same hk claimsR_mem)

/-- Memory column `0`'s variable count is within `pointCap`. -/
theorem memory0_vars {mem : UInt64 → Option UInt64} {p : UInt64} {bc : Array UInt64}
    {layout : LayoutW} {rate : Nat} (hlay : LayoutAt mem p bc layout rate) :
    (layout.placement memory0).variableCount ≤ pointCap := by
  rw [placement_memory0]
  cases h : layout.placements.getD 0 none with
  | none => exact Nat.zero_le _
  | some pl => exact hlay.placementsBound 0 (by rw [columnCount_val]; omega) pl h

/-- **Phase 5 computes `publicInputPhase`.** -/
theorem phase5_ok : Phase5Ok phase5 := by
  intro env inp t0 s0 layout rate acc hc hin hlay hcl hsz
  have hcw := claimWords_val
  have hcs := claimsR_size
  have hO := claimsR_off
  have htc := tableClaimCount_val
  have hpc := pointCap_val
  have hvc := memory0_vars hlay
  have hn : acc.size ≤ 157 := by unfold busClaimCount at hsz; omega
  have hpub : ∀ s, Base env rs5 s0 s → ∀ i (h : i < 4),
      s.mem (wd env.ctx (ctxPublic + i)) = some inp.pub[i] := fun s hb i h ↦
    (hb.1.ctx hin (fun r hr ↦ stop_le_of_mem (rs5_regions r hr) _)
      (by unfold ctxPublic; rw [scratchW_val]; omega)).trans (hin.pubWords i h)
  apply runs_of_refines
  rw [publicInputPhase_eq]
  unfold phase5
  refine Refines.blk_cons (Refines.mono (sampleChallenge_fr (rs := rs5) (s0 := s0)
    (claimsAt_stable hin)) (by rintro t s ⟨rfl, rfl⟩; exact ⟨hc, Base.start hc.rdi, hcl⟩)
    (fun _ _ _ h ↦ h) (fun _ h ↦ h)) fun c ↦ Refines.pure ?_
  rintro t s ⟨hc1, ⟨hb1, hcl1⟩, h9, h10⟩
  refine wp_then (pubSetup_spec hin hlay hc1 hb1 hcl1 h9 h10)
    fun s1 ⟨hc2, hb2, h12, h13, h14, h15, hcnt, hfr1⟩ ↦ ?_
  rw [hcw] at h12
  have hP1 : 1 ≤ 1 + ((layout.placement memory0).variableCount - 1) := by omega
  have hP : 1 + ((layout.placement memory0).variableCount - 1) ≤ pointCap := by omega
  refine wp_then (pubClaim_spec (l := 0) rfl (by omega) (j0 := 1 + 76 * acc.size)
    (by rw [hcw]; omega) hP1 hP (by simp) hin hc2 hb2 h12 h13 h14 h15
    (hpub s1 hb2 0 (by omega)) (hpub s1 hb2 2 (by omega)))
    fun s2 ⟨hc3, hb3, g12, g13, g14, g15, hcl0, hfr2⟩ ↦ ?_
  refine wp_reg_rel rfl (by decide) hc3 hb3 fun hc4 hb4 ↦ ?_
  refine wp_then (pubClaim_spec (l := 1) rfl (by omega) (j0 := 1 + 76 * (acc.size + 1)) (c := c)
    (by rw [hcw]; omega) hP1 hP (by simp) hin hc4 hb4
    (by reg_simp; rw [g12, h12, wdisp_toUInt64, wd_add, hcw]; congr 1)
    (by reg_simp; rw [g13, h13]) (by reg_simp; rw [g14, h14]) (by reg_simp; rw [g15, h15])
    (hpub _ hb4 1 (by omega)) (hpub _ hb4 3 (by omega)))
    fun s3 ⟨hc5, hb5, _, _, _, _, hcl1', hfr3⟩ ↦ ?_
  simp only [QState.setReg_mem, hcw] at hfr3 hfr2
  have hall : ∀ x, 0 < x → x < 1 + 76 * acc.size →
      s3.mem (wd env.work (claimsR.off + x)) = s.mem (wd env.work (claimsR.off + x)) :=
    fun x h0 hx ↦ (hfr3 x (by omega) (by omega)).trans
      ((hfr2 x (by omega) (by omega)).trans (hfr1 x h0 (by omega)))
  have hpcs : (pubClaims layout inp.pub c).size = 2 := rfl
  rw [Nat.add_sub_cancel_left] at hcl0 hcl1'
  refine WP.blk_nil ⟨hc5, ⟨⟨by rw [Array.size_append, hpcs, claimCap_val]; omega, ⟨by
    rw [Array.size_append, hpcs]; omega, ?_⟩, fun i hi ↦ ?_⟩, by rw [hpcs]; rfl⟩, hb5.1⟩
  · rw [Region.at, Array.size_append, hpcs]
    refine mem_congr_idx (y := claimsR.off + 0) rfl ?_
    rw [hfr3 0 (by omega) (by omega), hfr2 0 (by omega) (by omega)]
    exact hcnt
  · rw [Array.size_append, hpcs] at hi
    rw [Region.at, wd_wd]
    by_cases h1 : i < acc.size
    · rw [Array.getElem_append_left h1]
      have := hcl1.2.2 i h1
      rw [Region.at, wd_wd] at this
      refine this.congr fun k hk ↦ ?_
      rw [wd_wd, Nat.add_assoc]
      exact hall _ (by omega) (by rw [hcw] at hk ⊢; nlinarith)
    · rw [Array.getElem_append_right (by omega)]
      by_cases h2 : i = acc.size
      · subst h2
        simp only [Nat.sub_self]
        refine hcl0.congr fun k hk ↦ ?_
        rw [wd_wd, Nat.add_assoc]
        exact hfr3 _ (by rw [hcw] at hk ⊢; omega) (by rw [hcw] at hk ⊢; left; nlinarith)
      · have h3 : i = acc.size + 1 := by omega
        subst h3
        simp only [Nat.add_sub_cancel_left]
        exact hcl1'

end NativeVm.Code
