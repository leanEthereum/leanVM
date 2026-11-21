module

public import NativeVm.Code.Phase3.ShareStart
public import NativeVm.Code.Phase3.ShareCheck

/-!
# The bytecode share: `bytecodeShare`

`share_spec`: `shareCode` runs `bytecodeShare weights bytecodeLow`: the share (`shStart_spec`), the
four plain rounds as a loop (`Refines.foldlM` over `shRound_refines`, the rounds grinding no bits:
`share_sumcheck_run`), the value, the check (`shCheck_spec`). It writes `shareR`, `valueR`, `slotR`
and `tmpR`.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Field NativeVm.Transcript NativeVm.Code
open LeanVM.Protocol.Verifier (busBits)

/-- **`bytecodeShare`**. -/
theorem share_spec {env : Env} {inp : Input} {t : TState} {s : QState} {weights : Array EW}
    (bytecodeLow : Array EW) (h : CodeRel env t s) (hi : Inputs env inp s.mem)
    (hw : EWArr s.mem (wR.at env.work) weights) (hws : weights.size = 2 ^ busBits) :
    WP shareCode s
      (fun s' ↦ ∃ r t', (bytecodeShare weights bytecodeLow).run t = some (r, t') ∧
        CodeRel env t' s' ∧ EWAt s'.mem (shareR.at env.work) r.1 ∧
        EWAt s'.mem (valueR.at env.work) r.2.2 ∧
        (∃ slot, r.2.1 = bytecodeLow ++ slot ∧ slot.size = busBits ∧
          EWArr s'.mem (slotR.at env.work) slot) ∧
        Step3 env allRegs [shareR, valueR, slotR, tmpR] s s')
      (fun s' ↦ (bytecodeShare weights bytecodeLow).run t = none ∧
        Step3 env allRegs [shareR, valueR, slotR, tmpR] s s') := by
  have hws16 : weights.size = 16 := hws
  have hokW : ∀ r ∈ shW, Ok3 r := by sh_reg
  unfold shareCode
  refine WP.blk_cons (WP.mono (shStart_spec h hi) (fun s1 ⟨share, t1, hr1, hinv⟩ ↦ ?_)
    (fun s1 ⟨hr1, hst⟩ ↦ ⟨by unfold bytecodeShare; exact Refines.run_bind_none hr1, hst⟩))
  have key := Refines.foldlM (l := List.replicate 4 (none : Option EW))
    (f := fun acc _ ↦ shareRoundM acc) (cond := .cmp .ne .r13 (.imm 0)) (body := shRound)
    (Inv := fun k acc t s' ↦ shInv env inp s share k acc t s')
    (E := fun s' ↦ Step3 env allRegs shW s s') ?_ ?_ (init := (#[], share))
  rotate_left
  · rintro k acc t' s' ⟨-, -, -, -, -, h13, -⟩
    rw [List.length_replicate, cond_ne, rhs_imm, h13, int64Zero_toUInt64, bne_iff_ne, ne_eq]
    constructor
    · intro hne
      by_contra hk
      exact hne (by rw [show 4 - k = 0 by omega]; rfl)
    · intro hk e
      have := toUInt64_eq_zero (show 4 - k < 2 ^ 64 by omega) e
      omega
  · intro k hk acc
    rw [List.length_replicate] at hk
    exact shRound_refines hk acc
  refine WP.blk_cons (WP.mono (key t1 s1 hinv) (fun s2 ⟨⟨slot, claim⟩, t2, hr2, hinv2⟩ ↦ ?_)
    (fun s2 ⟨hr2, hst⟩ ↦ ⟨?_, hst⟩))
  rotate_left
  · unfold bytecodeShare
    rw [Refines.run_bind_some hr1, Refines.run_bind_none (by rw [share_sumcheck_run]; exact hr2)]
  have hr2' : (sumcheckPlain share 3 busBits).run t1 = some ((slot, claim), t2) := by
    rw [share_sumcheck_run]; exact hr2
  obtain ⟨hc2, hi2, hsz, hslot, hcl, -, -, hsh, hst2⟩ := hinv2
  simp only [List.length_replicate] at hsz
  refine WP.blk_cons (WP.mono (readTo_spec (r := valueR) (k := valueR.off) (by sh_reg) le_rfl
    (by sh_reg) hc2 hi2) (fun s3 ⟨value, t3, hr3, hc3, hv3, hs3⟩ ↦ ?_)
    (fun s3 ⟨hr3, hs3⟩ ↦ ⟨?_, hst2.trans (sh_step hs3 (by sh_reg))⟩))
  rotate_left
  · unfold bytecodeShare
    rw [Refines.run_bind_some hr1, Refines.run_bind_some hr2', Refines.run_bind_none hr3]
  have hok3 : ∀ r ∈ [valueR], Ok3 r := by sh_reg
  have hi3 : Inputs env inp s3.mem := hi2.step3 hok3 hs3 hc2.rdi
  have hst3 : Step3 env allRegs shW s s3 := hst2.trans (sh_step hs3 (by sh_reg))
  have hw3 : EWArr s3.mem (wd env.work wR.off) weights :=
    ewarr_keep hst3 hi hokW (q := wR) (by sh_reg) (by sh_reg) le_rfl (by rw [hws16]; sh_reg) hw
  have hslot3 : EWArr s3.mem (wd env.work slotR.off) slot :=
    ewarr_keep hs3 hi2 hok3 (q := slotR) (by sh_reg) (by sh_reg) le_rfl (by rw [hsz]; sh_reg) hslot
  have hcl3 : EWAt s3.mem (wd env.work shClaimW) claim :=
    ewat_keep hs3 hi2 hok3 (q := shClaimR) (by sh_reg) (by sh_reg) le_rfl (by sh_reg) hcl
  have hsh3 : EWAt s3.mem (wd env.work shareR.off) share :=
    ewat_keep hs3 hi2 hok3 (q := shareR) (by sh_reg) (by sh_reg) le_rfl (by sh_reg) hsh
  have hrunE : (bytecodeShare weights bytecodeLow).run t =
      (Model.require (claim == dot (eqKernel slot) weights * value) >>= fun _ ↦
        (pure (share, bytecodeLow ++ slot, value) : VM _)).run t3 := by
    unfold bytecodeShare
    rw [Refines.run_bind_some hr1, Refines.run_bind_some hr2', Refines.run_bind_some hr3]
  have hokF : ∀ r ∈ [shFoldR], Ok3 r := by sh_reg
  refine WP.blk_cons (shCheck_spec hc3.rdi hc3.workPtr3 hi3 hw3 hws16 hslot3 (by rw [hsz]) hcl3 hv3
    (fun sF hb hwF ↦ WP.blk_nil ⟨(share, bytecodeLow ++ slot, value), t3, ?_,
      hc3.wrote3 hi3 hokF hwF, ?_, ?_, ⟨slot, rfl, hsz, ?_⟩, ?_⟩)
    (fun sF hb hwF ↦ ⟨?_, ?_⟩))
  · rw [hrunE, Refines.run_bind_some (by rw [Refines.require_run, hb]; rfl)]; rfl
  · exact ewat_keep hwF.step hi3 hokF (q := shareR) (by sh_reg) (by sh_reg) le_rfl (by sh_reg) hsh3
  · exact ewat_keep hwF.step hi3 hokF (q := valueR) (by sh_reg) (by sh_reg) le_rfl (by sh_reg) hv3
  · exact ewarr_keep hwF.step hi3 hokF (q := slotR) (by sh_reg) (by sh_reg) le_rfl
      (by rw [hsz]; sh_reg) hslot3
  · exact hst3.trans (sh_step hwF.step (by sh_reg))
  · rw [hrunE, Refines.run_bind_none (by rw [Refines.require_run, hb]; rfl)]
  · exact hst3.trans (sh_step hwF.step (by sh_reg))

end NativeVm.Code.P3
