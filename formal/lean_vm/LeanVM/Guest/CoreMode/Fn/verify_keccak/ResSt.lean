/-
  LeanVM.Guest.CoreMode.Fn.verify_keccak.ResSt

  `verify_keccak`'s cursor in the proof stream (`VkQ`), carried down from `verify_sub`'s front.
-/

module

public import LeanVM.Guest.CoreMode.Gen.TermCallers
public import LeanVM.Guest.CoreMode.Fn.verify_sub.Front
public import LeanVM.Guest.CoreMode.Fam.MonoChain
public import LeanVM.Guest.CoreMode.Fam.RefAll
public import LeanVM.Guest.CoreMode.Fam.ResF
public import LeanVM.Guest.EndExecCoreFn
public import LeanVM.Guest.CoreMode.Fam.TermDefs
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_keccak»
import LeanVM.Guest.Data.ValNames.«verify_sub»

/-!
# `verify_keccak`'s cursor

`VkQ J`: at an instance of `verify_keccak`, its cursor is `stream·g^p`, its table's log-height `τ`
(`tau_g = g^τ`, `9 ≤ τ ≤ 28`), and `p + vkNeed τ ≤ 8192`: room for the word before its first layer,
its twelve layers, each reading `84 + 2(τ - 3)` words, and the words after them.

`vkQ_all`: at every honest instance of `verify_keccak`, by `Res.insts_down`: its only caller is
`verify_sub` (`Res.termCallers_all`), whose only call of it is at `vkArgsV` (`vs_vk_sites`), whose
front (`B1.VerifySub.vs_front`) puts the cursor at `stream·g^(13 + |xsG| + |xsT|)`, within its room
(`verify_sub/Front.lean`: `front_carried`, `reads_gkrPhase`, `reads_tablesSeg`, `vk_room`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **`verify_keccak`'s cursor in its stream**: `cursor = stream·g^p`, `tau_g = g^τ`, `9 ≤ τ ≤ 28`,
and room for its reads. -/
def VkQ (J : Inst) : Prop :=
  ∀ σ bufs kids, J.t = .node "verify_keccak" σ bufs kids →
    ∃ p τ, σ (.n (val% «verify_keccak» "cursor@1")) = σ (.n (val% «verify_keccak» "stream")) * gen ^ p ∧ σ (.n (val% «verify_keccak» "tau_g")) = gen ^ τ ∧ 9 ≤ τ ∧ τ ≤ 28 ∧ p + vkNeed τ ≤ 8192

/-- `verify_keccak`'s call arguments in `verify_sub`. -/
def vkArgsV : List V := [val% «verify_sub» "fs0@4", val% «verify_sub» "fs1@4", val% «verify_sub» "fs2@4", val% «verify_sub» "fs3@4", val% «verify_sub» "fs4@4", val% «verify_sub» "cursor@3", val% «verify_sub» "tau_keccak_g", val% «verify_sub» "chi", val% «verify_sub» "fs0@5~8", val% «verify_sub» "z_vals", val% «verify_sub» "slices", val% «verify_sub» "fs0@5~10", val% «verify_sub» "stream"].map .n

end

public section

/-! ## Down from `verify_sub` -/

/-- **`verify_sub` calls `verify_keccak` only at `vkArgsV`.** -/
theorem vs_vk_sites :
    Res.sitesB (fun f args _ ↦ f != "verify_keccak" || args == vkArgsV) VerifySub.vsT = true := by
  decide +kernel

theorem vk_params : (fn% «verify_keccak»).params = (List.range 13).map V.n := rfl

variable {r : Ref}

/-- **`verify_keccak`'s cursor passes down from `verify_sub`.** -/
theorem vkQ_step (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) VkQ := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ _ hname hval hph _
    σ bufs kids hJt
  have hct : c.taken = true := by
    cases h : c.taken
    · obtain ⟨g', σ', h'⟩ := hph h
      rw [hJt] at h'; cases h'
    · rfl
  have hJv := hval hct
  rw [hJt] at hJv
  obtain ⟨fn, hfn, hpar, -⟩ := hJv
  have hcf : c.f = "verify_keccak" := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  -- the caller is `verify_sub`
  have hcal := List.all_eq_true.mp (Res.calls_sites (Res.termCallers_all fnI (List.mem_of_find?_eq_some hfI)) hw c hc)
    (name% «verify_keccak», name% «verify_sub») (by decide)
  have hnI := Da.fn_name_of_find hfI
  rw [hcf] at hcal
  simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcal
  have hvs : fI = name% «verify_sub» := by
    rcases hcal with h | ⟨h, hl⟩
    · rw [← hnI, h]
    · exfalso
      rw [hnI] at h
      subst h
      obtain rfl : fnI = fn% «verify_keccak» := Option.some.inj (hfI.symm.trans VerifySub.find_vk)
      exact absurd hl (by decide +kernel)
  subst hvs
  obtain rfl : fnI = fn% «verify_sub» := Option.some.inj (hfI.symm.trans VerifySub.find_vs)
  obtain rfl : fn = fn% «verify_keccak» := Option.some.inj (hfn.symm.trans VerifySub.find_vk)
  -- its call of `verify_keccak`
  have hs := Res.calls_sites (show Res.sitesB _ (fn% «verify_sub»).body = true by
    rw [VerifySub.vs_body]; exact vs_vk_sites) hw c hc
  rw [hcf] at hs
  simp only [bne_self_eq_false, Bool.false_or, beq_iff_eq] at hs
  rw [hs, vk_params] at hpar
  have e5 := params_get hpar (k := 5) (by decide) rfl
  have e6 := params_get hpar (k := 6) (by decide) rfl
  have e12 := params_get hpar (k := 12) (by decide) rfl
  -- its front
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
  have hfs : ∀ f', 1 ≤ B2C.fs f' := Res.fs_pos
  obtain ⟨-, hb⟩ := Res.holds_of_valid hfs hv hfI
  rw [VerifySub.vs_body] at hb
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  have hQ := carryQ_all hr I hI _ σI bufsI kidsI hIt _ hfI (name% «verify_sub», 4, .tab) (by decide) rfl
    (.n 4) (by rw [VerifySub.vs_params]; rfl)
  obtain ⟨hexp, hwin⟩ := hQ
  obtain ⟨⟨F⟩, -⟩ := VerifySub.vs_front (by omega) r.img (fun _ _ _ h ↦ Res.KidRel.rel h)
    (bytecode := List.replicate (2 ^ 23) 0) List.length_replicate hexp hwin hb
  -- the words before the cursor
  obtain ⟨sp, hsp⟩ := front_carried F
  obtain ⟨hlG, sp', hsp'⟩ := runsTo_reads (reads_gkrPhase _) F.hG hsp
  have hhl : ∀ h ∈ (Tables.layoutOf (List.replicate (2 ^ 23) 0) F.logMem F.rowsN).tableLogHeights,
      h ≤ 30 := by
    rw [VerifySub.layoutOf_heights]
    intro h hh'
    have := F.hh31 h hh'
    omega
  obtain ⟨hlT, -⟩ := runsTo_reads (reads_tablesSeg _ (fun w p v ↦ Child.reads_claimedBytecodeValue _ w p v)
    _ hhl _ _ _ _ _) F.hT hsp'
  have hτ9 := VerifySub.tau_ge F.hrowsL
  have hτ24 := VerifySub.tau_le_of_kappasBelow (VerifySub.tableHeights_length _ F.hrowsL) F.hKB
  refine ⟨13 + F.xsG.length + F.xsT.length, (Tables.tableHeightsOf F.rowsN).getD 5 0, ?_, ?_, hτ9,
    by omega, ?_⟩
  · rw [e5, e12, F.h578, F.h567, F.h320, F.h312]
    simp only [mul_assoc, ← pow_add]
  · rw [e6, F.h583]
  · have := vk_room F.hdep34 hlG hlT (show (Tables.tableHeightsOf F.rowsN).getD 5 0 ≤ 28 by omega)
    omega

/-- **`verify_keccak`'s cursor at every honest instance.** -/
theorem vkQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, VkQ J := by
  refine insts_all hr (vkQ_step hr) fun J hm ↦ ?_
  intro σ bufs kids hJt
  have hn := hm _ _ _ _ hJt
  exact absurd hn (by decide)

end

end LeanVM.Guest.EndExec
