/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.VkCarry

  `verify_keccak`'s `tau_g` at the honest instances of b2c's aligned tree (`VkQ`), carried from `verify_sub`'s
  certified sizes.
-/

module

public import LeanVM.Guest.CoreMode.Fn.column_selector.CsChain
import LeanVM.Guest.Data.Consts
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»

/-!
# `verify_keccak`'s `tau_g`, carried down

`verify_keccak`'s only caller is `verify_sub` (`Own.verify_sub.stCallers`, the whole program's check
`Res.termCallers_all`), which passes as its `tau_g` (parameter `6`) the Keccak table's height word
`kb[2 + TABLE_KECCAK]` (`B1.VerifySub.vsHeight5`): `g^h`, `h` the layout's Keccak log height, at least its floor
`keccakMinStepsLog = 9` (`buildLayout`'s `max (log2Ceil rows) floor`) and at most `24` (`SizesOk.heights24`).

`vkQ_allA`: `VkQ` at every honest instance (`insts_allA`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **`verify_keccak`'s `tau_g` at an instance**: `g^h`, `keccakMinStepsLog ≤ h ≤ 24`. -/
def VkQ (J : Inst) : Prop :=
  ∀ σ bufs kids, J.t = .node name% «verify_keccak» σ bufs kids →
    ∃ h, keccakMinStepsLog ≤ h ∧ h ≤ 24 ∧ σ (.n 6) = gen ^ h

end

public section

/-- `verify_sub` passes its Keccak height word `kb[2 + TABLE_KECCAK]` as `verify_keccak`'s `tau_g`. -/
theorem vs_vk_sites : Res.sitesB (fun g args _ ↦ g != name% «verify_keccak» || args[6]? == some (.n (115 + 5)))
    (fn% «verify_sub»).body = true := by
  decide +kernel

theorem vk_facts : (fn% «verify_keccak»).params[6]? = some (.n 6) ∧ (fn% «verify_keccak»).loop = false := by
  decide +kernel

theorem find_vk : coreProgram.find? name% «verify_keccak» = some fn% «verify_keccak» :=
  coreProgram_find?_at (j := idx% «verify_keccak») rfl

/-- A table's log height is at least its floor: the Keccak table's at least `keccakMinStepsLog`. -/
theorem floor_le_height5 {rows : List ℕ} (h : rows.length = 6) :
    keccakMinStepsLog ≤
      (List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) rows tableLogFloors).getD 5 0 := by
  match rows, h with
  | [_, _, _, _, _, _], _ => simp [tableLogFloors]

end

end LeanVM.Guest.EndExec

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

public section

/-- **The Keccak table's log height lies in `[keccakMinStepsLog, 24]`**, and `kb[2 + TABLE_KECCAK]` is `g` to it. -/
theorem vsHeight5_range {bytecode : List K} {rd : Reader} {σ : Val} (S : SizesOk bytecode rd σ) :
    ∃ h, keccakMinStepsLog ≤ h ∧ h ≤ 24 ∧ σ (.n (115 + 5)) = gen ^ h := by
  refine ⟨_, ?_, S.heights24 5 (by decide), vsHeight5 S⟩
  obtain ⟨-, -, -, hth, -⟩ := Stack.buildLayout_some S.build
  rw [hth]
  exact EndExec.floor_le_height5 (by simp [vsRows, vsAnnounced, nTables])

end

end LeanVM.Guest.B1.VerifySub

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

section

variable {al : String → Bool} {D : Ref → RefD} {r : Ref}

public section

/-- **`VkQ` passes down a call**: from `verify_sub`'s certified sizes, its exponent tables `CsQ`'s. -/
theorem vkQ_stepA (hR : RefH (layB al) (D r) r) (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (instsR al D r) VkQ := by
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
  have hcf : c.f = name% «verify_keccak» := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  obtain rfl : fn = fn% «verify_keccak» := Option.some.inj (hfn.symm.trans find_vk)
  obtain ⟨hp6, hpl⟩ := vk_facts
  -- the caller is `verify_sub`
  have hmem : (name% «verify_keccak», name% «verify_sub») ∈ Res.termCallers :=
    CoreMode.FnReg.stCallers_of_verify_sub _ (by simp [CoreMode.Own.verify_sub.stCallers])
  have hcal := List.all_eq_true.mp (Res.calls_sites (Res.termCallers_all fnI (List.mem_of_find?_eq_some hfI))
    hw c hc) _ hmem
  have hnI := find_name' hfI
  rw [hcf] at hcal
  simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcal
  have hvs : fI = name% «verify_sub» := by
    rcases hcal with h | ⟨h, hl⟩
    · rw [← hnI, h]
    · exfalso
      rw [hnI] at h
      subst h
      obtain rfl : fnI = fn% «verify_keccak» := Option.some.inj (hfI.symm.trans find_vk)
      rw [hpl] at hl; cases hl
  subst hvs
  obtain rfl : fnI = fn% «verify_sub» := Option.some.inj (hfI.symm.trans find_vs)
  -- the site: `tau_g` is `verify_sub`'s `kb[2 + TABLE_KECCAK]`
  have hs := Res.calls_sites vs_vk_sites hw c hc
  rw [hcf] at hs
  simp only [bne_self_eq_false, Bool.false_or, beq_iff_eq] at hs
  have h6 : σ (.n 6) = σI (.n (115 + 5)) := param_of hpar hp6 hs
  -- `verify_sub`'s sizes
  have hexp : B1.ExpTables r.img.read (σI (.n (val% «verify_sub» "g_squares"))) :=
    (csQ_allA hR hr I hI _ _ _ _ hIt).2.1 rfl
  have hκ28 : r.κ ≤ 28 := hr.log
  have hκ23 : 23 ≤ r.κ := by rw [hR.κ]; exact twentyThree_le_logMem _
  obtain ⟨args, rets, hv⟩ := inst_validA hR hI hIt
  obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv find_vs
  rw [B1.VerifySub.vs_body_eq, Core.holdsList_append] at hb
  have hpre := ((Core.holdsList_noRet _ B1.VerifySub.vsPre_noRet _ _).mp hb).1
  have hbl : (List.replicate (2 ^ (B1.Main.bytecodeLog + bytecodeSlotBits)) (0 : K)).length =
      2 ^ (B1.Main.bytecodeLog + bytecodeSlotBits) := List.length_replicate
  have S := B1.VerifySub.sizesOk (by omega) (by omega) r.img (fun _ _ _ h ↦ Res.KidRel.rel h) hbl hexp
    (vs_slice hpre B1.VerifySub.vsReadsT_eq) (vs_slice hpre B1.VerifySub.vsHeightsT_eq)
    (vs_slice hpre B1.VerifySub.vsStackT_eq)
  obtain ⟨h, h1, h2, he⟩ := B1.VerifySub.vsHeight5_range S
  exact ⟨h, h1, h2, h6.trans he⟩

/-- **`verify_keccak`'s `tau_g` at every honest instance.** -/
theorem vkQ_allA (hR : RefH (layB al) (D r) r) (hr : r.Ok) : ∀ J ∈ instsR al D r, VkQ J := by
  refine insts_allA hR (vkQ_stepA hR hr) fun J hm ↦ ?_
  intro σ bufs kids hJt
  have hn := hm _ _ _ _ hJt
  exact absurd hn (by decide +kernel)

end

end

end LeanVM.Guest.EndExec
