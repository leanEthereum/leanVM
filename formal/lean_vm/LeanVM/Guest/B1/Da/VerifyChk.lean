/-
  LeanVM.Guest.B1.Da.VerifyChk

  `da_verify`'s body, its loops and the roots' tree's, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.VerifyDefs
public import LeanVM.Guest.B1.Common.Find
public import LeanVM.Guest.Data.NameStrings

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.B1.Digest

@[expose] public section

set_option maxRecDepth 100000 in
theorem dv_ok : dvOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ws_ok : wsOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem b_ok : bOk (coreProgram.getD idx% «da_verify_loop0» default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem padL_ok : padLOk (coreProgram.getD idx% «da_pad_loop0» default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem pad_ok : padOk fn% «da_pad» = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dv_loops_idx : coreProgram.indexOf? name% «da_verify_loop0» = some idx% «da_verify_loop0» ∧
    coreProgram.indexOf? name% «da_pad_loop0» = some idx% «da_pad_loop0» :=
  ⟨coreProgram_indexOf?_at (j := idx% «da_verify_loop0») rfl,
    coreProgram_indexOf?_at (j := idx% «da_pad_loop0») rfl⟩

theorem find_da_weights : coreProgram.find? name% «da_weights» = some fn% «da_weights» :=
  coreProgram_find?_at (j := idx% «da_weights») rfl

theorem find_da_pad : coreProgram.find? name% «da_pad» = some fn% «da_pad» :=
  coreProgram_find?_at (j := idx% «da_pad») rfl

/-- The roots' tree's arms: their core indices, by `k`. -/
def rtIdx : List ℕ :=
  [idx% «da_roots_tree__L0», idx% «da_roots_tree__L1», idx% «da_roots_tree__L2», idx% «da_roots_tree__L3»,
    idx% «da_roots_tree__L4», idx% «da_roots_tree__L5», idx% «da_roots_tree__L6», idx% «da_roots_tree__L7»,
    idx% «da_roots_tree__L8», idx% «da_roots_tree__L9», idx% «da_roots_tree__L10»]

set_option maxRecDepth 100000 in
/-- **The roots' tree's arms, checked**: each at its index, its body `rtBody k`. -/
theorem rt_ok : (List.range 11).all (fun k => decide ((coreProgram[rtIdx.getD k 0]?).map Fn.name = some (rtName k)) &&
    rtOk k (coreProgram.getD (rtIdx.getD k 0) default)) = true := by decide +kernel

/-- The roots' tree's arm `k`, found, checked. -/
theorem rt_find {k : ℕ} (hk : k < 11) :
    coreProgram.find? (rtName k) = some (coreProgram.getD (rtIdx.getD k 0) default) ∧
      rtOk k (coreProgram.getD (rtIdx.getD k 0) default) = true := by
  have h := List.all_eq_true.mp rt_ok k (List.mem_range.mpr hk)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hn, hok⟩ := h
  obtain ⟨f, hf, hfn⟩ := Option.map_eq_some_iff.mp hn
  have hj := (List.getElem?_eq_some_iff.mp hf).1
  have hg : coreProgram.getD (rtIdx.getD k 0) default = f := by
    rw [List.getD_eq_getElem?_getD, hf, Option.getD_some]
  rw [hg]
  exact ⟨coreProgram_find?_at hf hfn, hg ▸ hok⟩

end
end LeanVM.Guest.B1.Da
