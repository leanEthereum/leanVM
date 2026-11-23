/-
  LeanVM.Guest.CoreMode.Fn.certify_placement.Sound

  `certify_placement`'s own routing facts and families, sound (`CoreMode/FnReg.lean`): its divisor, its family.
-/

module

public import LeanVM.Guest.EndExecCoreRes
public import LeanVM.Guest.CoreMode.Fn.certify_placement.ResCp
public import LeanVM.Guest.CoreMode.Fn.certify_placement.Data
public import LeanVM.Guest.CoreMode.Fn.certify_placement.Fam
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«certify_placement»

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CFun CRes CIdx ResF LtF rep_of capE resFam idxC baseC vw csSub)

public section

/-- **`certify_placement`'s cell `[137]·g^k`, `k < 9`, is one of `[137]·[v]` over its ranks' groups** (`cpPerm`): the
ranks' groups are onto (`cp_onto`). -/
theorem cpPerm_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {x : CRes} (h : CoreMode.cpPerm fn x = true) : x.Holds σ := by
  match x, h with
  | .subP ⟨cb, k⟩ cs, h =>
    simp only [CoreMode.cpPerm, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hn, hcb⟩, hco⟩, rfl⟩ := h
    subst hcb
    have hf' : f = "certify_placement" := by rw [← find_name' hf, hn]
    subst hf'
    obtain ⟨args0, rets0, hv⟩ := inst_valid' hr hI ht
    obtain ⟨fn0, hfn, hps, hbody⟩ := B1.Tables.cpFound
    obtain rfl : fn = fn0 := Option.some.inj (hf.symm.trans hfn)
    obtain ⟨-, hb⟩ := LeanVM.Guest.Res.holds_of_valid LeanVM.Guest.Res.fs_pos hv hfn
    rw [hbody, holdsList_append, holdsList_noRet _ B1.Tables.cpPre_noRet] at hb
    have htab : B1.ExpTables r.img.read (σ (.n (val% «certify_placement» "g_squares"))) :=
      (carryQ_all hr I hI _ σ bufs kids ht fn hfn ("certify_placement", 1, .tab) (by decide) rfl (.n (val% «certify_placement» "g_squares"))
        (by rw [hps]; rfl)).1
    have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
    obtain ⟨hK, hfc, -⟩ := cp_keys (by omega) r.img hb.1 htab
    obtain ⟨π, hπ, hon⟩ := cp_onto hK hfc
    obtain ⟨r0, hr0, hπr⟩ := hon k hco
    have hranks : CoreMode.cpRanks = (List.range 9).map B1.Tables.cpRB := by decide
    refine ⟨⟨[(val% «certify_placement» "group_base", 1), (B1.Tables.cpRB r0, 1)], 0⟩, ?_, ?_⟩
    · rw [hranks, List.map_map]
      exact List.mem_map.mpr ⟨r0, List.mem_range.mpr hr0, rfl⟩
    · simp only [CoreMode.CCell.addrW, CoreMode.CCell.valW, CoreMode.prodW, vw, pow_one, mul_one, hπ r0 hr0, hπr,
        Value.gen_pow_eq_ofK, addressOfIndex, pow_zero, show ofK (1 : Parameters.K) = 1 from map_one (algebraMap Parameters.K Parameters.E)]
  | .lt _ _, h | .nz _, h | .sub _ _, h | .subR _ _, h | .under _ _, h => simp [CoreMode.cpPerm] at h

end

end LeanVM.Guest.EndExec

namespace LeanVM.Guest.CoreMode.Own.certify_placement

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec
open LeanVM.Protocol.Verifier (gen)

public section

/-- **Its divisor, nonzero.** -/
theorem nzs_ok : ∀ c ∈ nzs, NzOk c := by
  simp only [nzs, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact nzVal_cp155

/-- **Its family.** -/
theorem fams_ok : ∀ c ∈ fams, OwnOk c := by
  simp only [fams, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact fun hr I hI σ bufs kids ht fn hf x h ↦ cpPerm_inst hr hI ht hf h

end

end LeanVM.Guest.CoreMode.Own.certify_placement
