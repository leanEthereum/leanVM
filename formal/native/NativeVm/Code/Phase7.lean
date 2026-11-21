module

public import NativeVm.Code.Phase7.Whir
public import NativeVm.Code.Phase7.RingRuns

/-!
# Phase 7: ring switching and the stacked opening

The code of `phase7M` (`ringSwitch`, `verifyStackedOpening`), proved against it
(`phase7_ok : Phase7Ok phase7`): the ring switching (`Ring.ringSwitchC_runs`, writing `ringR` and
`scratchR`), then from the state it leaves the stacked opening (`P7.whirC_b`, writing the WHIR
part's regions), on the stack claims `stackClaims`: the ring-switched claim at `q_keccak`'s point,
the column claims on the stack, the out-of-domain claim.
-/

@[expose] public section

namespace NativeVm.Code

open Native NativeVm.Model LeanVM.Parameters
open NativeVm.Transcript (Env)

/-- **Phase 7**: ring switching, the stack claims' batching, the opening's start, the non-final
levels, the final level. -/
def phase7 : Stmt := blk [Ring.ringSwitchC, P7.batchingC, P7.initC,
  .loop (.cmp .ne .r15 (.imm 0)) P7.levelC, P7.finalC]

theorem ringSwitch_keeps (point slices : Array EW) : KeepsRoots (Model.ringSwitch point slices) := by
  unfold Model.ringSwitch
  keeps

theorem ringRegs_stop (n : Nat) : ∀ r ∈ Ring.ringRegs, r.stop ≤ workWords n := fun r hr ↦
  stop_le_of_mem (by revert r; decide) n

theorem phase7_kept {env : Env} {s s₁ s₂ : QState} (h₁ : Kept env Ring.ringRegs s s₁)
    (h₂ : Kept env P7.whirRegs s₁ s₂) : Kept env phase7Regions s s₂ :=
  (h₁.mono (by decide)).trans (h₂.mono (by decide))

/-- **Phase 7 computes `phase7M`.** -/
theorem phase7_ok : Phase7Ok phase7 := by
  intro env inp t s layout rate ood claims point slices hc hroots hin hlay hood hcl hk
  unfold Runs phase7
  refine WP.blk_cons (WP.mono (NativeVm.Transcript.WP.frame (Ring.ringSwitchC_runs hc hin hk))
    ?_ fun s₁ ⟨⟨hr, hkept⟩, _⟩ ↦ ⟨Refines.run_bind_none hr, hkept.mono (by decide)⟩)
  rintro s₁ ⟨⟨⟨target, rp, coeffs⟩, t₁, hrun, hc₁, ⟨hrp, hring⟩, hkept⟩, hdom, -⟩
  simp only at hrp
  subst hrp
  have hst := ringRegs_stop inp.bytecode.size
  have hin₁ : Inputs env inp s₁.mem := hin.kept hkept hst hdom
  have same : ∀ q ∈ regions, (∀ r ∈ Ring.ringRegs, q.Apart r) →
      Same s.mem s₁.mem (q.at env.work) q.size := fun q hq hap ↦ hkept.same hin hst hq hap
  have hR : P7.Regs s₁.mem env.work inp.bytecode layout rate claims ood target coeffs rp slices :=
    ⟨hlay.congr (same _ (by decide) (by decide)), hcl.congr (same _ (by decide) (by decide)),
      hood.congr (same _ (by decide) (by decide)), hring,
      hk.congr (same _ (by decide) (by decide))⟩
  have hroots₁ : t₁.roots.size ≤ 1 := by
    rw [(ringSwitch_keeps rp slices).keeps t _ t₁ hrun]; exact hroots
  have hmodel : (phase7M layout rate ood claims rp slices).run t =
      (verifyStackedOpening layout.stackLog rate
        (P7.stackClaims layout target rp coeffs claims ood)).run t₁ := by
    unfold phase7M
    rw [Refines.run_bind_some hrun]
    rfl
  let pp : P7.Par := ⟨env, inp, s₁, layout.stackLog, [], ⟨#[], #[]⟩⟩
  refine WP.mono (P7.whirC_b (p := pp) hR t₁ s₁ ⟨⟨hc₁, P7.Fr.refl s₁, hin₁⟩, rfl, hroots₁⟩)
    (fun s' ⟨x, t', hr, hb⟩ ↦ ⟨x, t', hmodel ▸ hr, hb.rel, trivial,
      phase7_kept hkept (P7.kept_of_fr hb.fr hc₁.rdi)⟩)
    fun s' ⟨hr, hfr⟩ ↦ ⟨hmodel ▸ hr, phase7_kept hkept (P7.kept_of_fr hfr hc₁.rdi)⟩

/-- info: 'NativeVm.Code.phase7_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phase7_ok

/-- Phase 7 never writes the stack pointer. -/
theorem phase7_writes_rsp : phase7.writes .rsp = false := by decide +kernel

end NativeVm.Code
