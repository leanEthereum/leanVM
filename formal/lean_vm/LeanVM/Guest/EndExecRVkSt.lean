/-
  LeanVM.Guest.EndExecRVkSt

  `verify_keccak`'s reads past its layers' returned cursors (`Res.vkStB`), sound at the honest frames.
-/

module

public import LeanVM.Guest.EndExecRVk
public import LeanVM.Guest.EndExecRKid
public import LeanVM.Guest.EndExecRVtB

/-!
# `verify_keccak`'s reads past its layers

`call_of_pre`: a call of a block's prefix without `ret` is on every returning path. `vkSt_top`: at an
honest frame of `verify_keccak`, step `s`'s call is on the path, its callee's frame pointer in the
site's cell (`FrameHolds.site`) and its returned cursor in that frame's cell `23` (`kid_rets`): the
cursor `1 + (s + 1)·(84 + 2(τ - 3))` words past `verify_keccak`'s (`vk_vals`), inside the stream with
room for the words read there (`VkQ`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B2C (fsN cellJ siteOf)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (vkStB vkStSites stResB)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

section

variable {σ : Core.Val}

/-- **A call of a block without `ret` is on its path.** -/
theorem call_on_path {f : String} {as bs : List V} : ∀ {l : List Stmt} {es : List Ev},
    Memory.Stmt.noRetListS l = true → Memory.walk σ l = .fall es → Stmt.call f as bs ∈ l → Ev.call f as bs ∈ es
  | [], _, _, _, hm => (List.not_mem_nil hm).elim
  | s :: l, es, hn, hw, hm => by
      simp only [Memory.Stmt.noRetListS, Bool.and_eq_true] at hn
      rw [Memory.walk] at hw
      rcases Memory.walk1_noRet (σ := σ) s hn.1 with ⟨es1, h1⟩ | h1
      · rw [h1] at hw
        rcases Memory.walk_noRet (σ := σ) l hn.2 with ⟨es2, h2⟩ | h2
        · rw [h2] at hw
          simp only [Out.seq, Out.pre, Out.fall.injEq] at hw
          subst hw
          rcases List.mem_cons.mp hm with rfl | hm
          · simp only [Memory.walk1, Out.fall.injEq] at h1
            subst h1
            exact List.mem_append_left _ List.mem_cons_self
          · exact List.mem_append_right _ (call_on_path hn.2 h2 hm)
        · rw [h2] at hw; simp [Out.seq, Out.pre] at hw
      · rw [h1] at hw; simp [Out.seq] at hw

/-- **A call of a prefix without `ret` is on a returning path.** -/
theorem call_of_pre {l1 l2 : List Stmt} {es : List Ev} {vs : List V}
    (hw : Memory.walk σ (l1 ++ l2) = .ret es vs)
    (hk : Memory.Stmt.noRetListS l1 = true) {f : String} {as bs : List V} (hm : Stmt.call f as bs ∈ l1) :
    Ev.call f as bs ∈ es := by
  rw [Memory.walk_append] at hw
  rcases Memory.walk_noRet (σ := σ) _ hk with ⟨es1, h1⟩ | h1
  · rw [h1] at hw
    cases h2 : Memory.walk σ l2 with
    | fall _ => rw [h2] at hw; simp [Out.seq, Out.pre] at hw
    | ret es2 _ =>
      rw [h2] at hw
      simp only [Out.seq, Out.pre, Out.ret.injEq] at hw
      rw [← hw.1]
      exact List.mem_append_left _ (call_on_path hk h1 hm)
    | stuck => rw [h2] at hw; simp [Out.seq, Out.pre] at hw
  · rw [h1] at hw; simp [Out.seq] at hw

end

theorem vkStSites_eq : vkStSites = (List.range 12).map fun s ↦ (vkSiteQ s, if s = 11 then 97 else 48) := by
  decide

theorem vkT_pre : vkT = (vkHeadT ++ vkFirstT ++ vkStepsT) ++ (vkOutT ++ vkInT ++ vkFinT) := by
  rw [vkT]; simp only [List.append_assoc]

theorem vkPre_noRet : Memory.Stmt.noRetListS (vkHeadT ++ vkFirstT ++ vkStepsT) = true := by decide +kernel

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

/-- **`verify_keccak`'s reads past its layers' returned cursors** lie in its stream. -/
theorem vkSt_top (t : TopAt A r K i e j) (hr : r.Ok) {x : Mode.Res} (hx : vkStB j x = true) :
    RRes (refMem r.img) e.I.fp x := by
  match x, hx with
  | .sub a bs, hx =>
    simp only [vkStB, Bool.and_eq_true, beq_iff_eq, List.any_eq_true, decide_eq_true_eq] at hx
    obtain ⟨hname, ⟨q, n⟩, hm, hc, hxe⟩ := hx
    rw [hxe]
    rw [vkStSites_eq] at hm
    obtain ⟨s, hs, hsq⟩ := List.mem_map.mp hm
    simp only [Prod.mk.injEq] at hsq
    obtain ⟨rfl, rfl⟩ := hsq
    replace hs := List.mem_range.mp hs
    obtain ⟨f, bufs, kids, hJ, hfj, hfn⟩ := t.found
    rw [hname] at hfn
    subst hfn
    have hcf : coreOf j = fn% «verify_keccak» := Option.some.inj (hfj.symm.trans find_vk)
    obtain ⟨rfl, p, τ, hτ9, hτ28, hroom, e5, -, -, -, -, -, hrets⟩ := vk_vals t hr hname
    obtain ⟨-, m14, -⟩ := vk_cells t hr hname
    obtain ⟨-, -, -, -, -, -, -, hfs⟩ := vk_cellsJ
    obtain ⟨vs, hw, hF, -⟩ := t.events hr
    have hf := List.all_eq_true.mp vkCall_facts s (List.mem_range.mpr hs)
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hf
    obtain ⟨⟨⟨⟨⟨⟨⟨hl16, -⟩, -⟩, -⟩, -⟩, hl6⟩, -⟩, -⟩ := hf
    -- step `s`'s call on the path, its callee frame
    have hw' := hw
    rw [show (coreOf (fn_idx% «verify_keccak»)).body = vkT by rw [hcf]; exact vk_body, vkT_pre] at hw'
    have hev := call_of_pre hw' vkPre_noRet (List.mem_append_right _ (vkCall_mem hs))
    set c : Call := ⟨(vkCall s).1, (vkCall s).2.1, (vkCall s).2.2, true⟩ with hcdef
    have hcm : c ∈ calls (e.pre ++ e.es) := List.mem_filterMap.mpr ⟨_, hev, rfl⟩
    obtain ⟨ii, hii⟩ := List.mem_iff_getElem?.mp hcm
    obtain ⟨kfp, hkfp⟩ : ∃ kfp, e.I.kidFps[ii]? = some kfp := by
      have hl := hF.len
      have : ii < (calls (e.pre ++ e.es)).length := (List.getElem?_eq_some_iff.mp hii).1
      exact ⟨e.I.kidFps[ii], List.getElem?_eq_getElem (by omega)⟩
    have hsite := List.all_eq_true.mp vk_sites s (List.mem_range.mpr hs)
    simp only [beq_iff_eq] at hsite
    obtain ⟨st, hst, hstq⟩ := Option.map_eq_some_iff.mp hsite
    have hq8 : vkSiteQ s ≤ 738 := by
      interval_cases s <;> decide
    have hrdq := (hF.site ii c kfp st hii hkfp hst).1 (by rw [hstq]; interval_cases s <;> decide)
      (by rw [hstq]; omega)
    rw [hstq] at hrdq
    obtain ⟨-, hmq⟩ := ref_read hr (by have := t.fb; omega) hrdq
    have hret := kid_rets hr t.inst hJ hfj hw hii hkfp rfl 5
      (by show 5 < (vkCall s).2.2.length; omega)
    simp only [hcdef, hl16] at hret
    -- the returned cursor is the base's word
    have hst14 : ∀ v, RBase (refMem r.img) e.I.fp (.fr 14) v → v = e.σ (.n 12) := fun v hv ↦ by
      change refMem r.img (e.I.fp + 14) = v at hv
      rw [← hv, m14]
    have hcur : ∀ v, RBase (refMem r.img) e.I.fp (.hp (vkSiteQ s) 23) v →
        v = e.σ (.n 12) * gen ^ (p + (1 + (s + 1) * (84 + 2 * (τ - 3)))) := fun v hv ↦ by
      obtain ⟨x, hxn, hxM⟩ := hv
      have hxa : Parameters.addressOfIndex (kfp + (2 + 16 + 5)) = Parameters.addressOfIndex x := by
        have hy := hxn.1
        simp only [hmq, Mode.limb_mul_ofK, limb_ofK, Fin.isValue, Fin.val_zero, ↓reduceIte, addressOfIndex] at hy
        rw [← pow_add] at hy
        simpa [addressOfIndex] using hy
      rw [hxa] at hret
      obtain ⟨-, hmx⟩ := ref_read hr (by have := hxn.2; unfold maxCells at this; omega) hret
      rw [← hxM, hmx, hrets s hs, e5, mul_assoc, ← pow_add]
    refine stResB_of hst14 hcur ?_
    unfold vkNeed at hroom
    by_cases h11 : s = 11
    · subst h11
      simp only [↓reduceIte] at hc
      omega
    · simp only [h11, ↓reduceIte] at hc
      have : (s + 1) * (84 + 2 * (τ - 3)) ≤ 11 * (84 + 2 * (τ - 3)) := Nat.mul_le_mul_right _ (by omega)
      omega
  | .lt _ _, hx => simp [vkStB] at hx
  | .nz _, hx => simp [vkStB] at hx
  | .name _, hx => simp [vkStB] at hx

end

end LeanVM.Guest.EndExec
