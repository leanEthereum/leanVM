/-
  LeanVM.Guest.CoreMode.Fn.shared_selector_tables.Sound

  `shared_selector_tables`'s own routing facts and families, sound (`CoreMode/FnReg.lean`): its split.
-/

module

public import LeanVM.Guest.EndExecCoreRes
public import LeanVM.Guest.EndExecCoreSplit
public import LeanVM.Guest.B1.Exact.SharedTables
public import LeanVM.Guest.CoreMode.Fn.shared_selector_tables.Fam
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«shared_selector_tables»

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CRes CCond CCell CRun CIdx LtF rep_of capE idxC vw prodW SplitC powB splitRes)
open LeanVM.Protocol.Verifier (gen)

public section

/-- **`shared_selector_tables`' split** (`spSst`): its `len = q^4·r_g`, `q = q_g@1·q_g@2~3·q_g@3~3·q_g@4~3`,
`r_g = r_g~3·r_g~7`. -/
theorem splitW_sst : SplitW (fn% «shared_selector_tables»)
    ⟨[(val% «shared_selector_tables» "q_g@1", 1), (val% «shared_selector_tables» "q_g@2~3", 1), (val% «shared_selector_tables» "q_g@3~3", 1),
      (val% «shared_selector_tables» "q_g@4~3", 1)], [(val% «shared_selector_tables» "r_g~3", 1), (val% «shared_selector_tables» "r_g~7", 1)], val% «shared_selector_tables» "r_g", 5, 4, 16⟩ := by
  intro rd σ es vs hw hev
  have h : Stmt.HoldsList (fun _ _ _ => True) rd σ (fn% «shared_selector_tables»).body False (fun _ => True) :=
    holdsList_of_walk _ (by rw [hw]; exact ⟨fun e he => ⟨hev e he, fun _ _ _ _ => trivial⟩, trivial⟩)
  have hbody : (fn% «shared_selector_tables»).body = Fn.«shared_selector_tables».core.body := rfl
  rw [hbody] at h
  have w3 := B1.word_gpow_one 0 (by norm_num) 3 (by decide)
  have w5 := B1.word_gpow_one 1 (by norm_num) 5 (by decide)
  have w17 := B1.word_gpow_one 2 (by norm_num) 17 (by decide)
  have w257 := B1.word_gpow_one 3 (by norm_num) 257 (by decide)
  simp only [Fn.«shared_selector_tables».core.body, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and] at h
  obtain ⟨m6, m7, m8, m9, m10, m11, c12, c13, h14, h15, c16, c17, h18, h19, h20, c21, c22, h23, h24, c25, c26, h27,
    h28, h29, c30, c31, h32, h33, h34, c35, c36, h37, h38, h39, h40, h41, h42, ha, -⟩ := h
  have hlo : ∀ j < 2, σ (.n (val% «shared_selector_tables» "nb[0]" + j)) * σ (.n (val% «shared_selector_tables» "nb[0]" + j)) = σ (.n (val% «shared_selector_tables» "nb[0]" + j)) := by
    intro j hj; interval_cases j
    exacts [m6.symm, m7.symm]
  have hhi : ∀ j < 4, σ (.n (val% «shared_selector_tables» "nb[2]" + j)) * σ (.n (val% «shared_selector_tables» "nb[2]" + j)) = σ (.n (val% «shared_selector_tables» "nb[2]" + j)) := by
    intro j hj; interval_cases j
    exacts [m8.symm, m9.symm, m10.symm, m11.symm]
  have rg : σ (.n (val% «shared_selector_tables» "r_g")) = ∏ j ∈ Finset.range 2, (1 + σ (.n (val% «shared_selector_tables» "nb[0]" + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h20, h15, h19, c12, h14, c13, c16, h18, c17, w3, w5, B1.word_one]
  have qg : σ (.n (val% «shared_selector_tables» "q_g@4")) = ∏ j ∈ Finset.range 4, (1 + σ (.n (val% «shared_selector_tables» "nb[2]" + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h39, h34, h29, h24, h28, h33, h38, c21, h23, c22, c25, h27, c26, c30, h32, c31, c35, h37, c36, w3, w5, w17,
      w257, B1.word_one]
  obtain ⟨bb, hbb, hb⟩ := split_bits_gpow (b := fun j ↦ σ (.n (val% «shared_selector_tables» "nb[0]" + j))) hlo
  obtain ⟨aa, haa, hab⟩ := split_bits_gpow (b := fun j ↦ σ (.n (val% «shared_selector_tables» "nb[2]" + j))) hhi
  replace rg := rg.trans hb
  replace qg := qg.trans hab
  have h5 : σ (.n (val% «shared_selector_tables» "len_g")) = gen ^ (4 * aa + bb) := by
    rw [← Value.e_add_eq_zero_iff.mp ha, h42, h41, h40, qg, rg, pow_add, pow_mul']
    ring
  have haa' : aa < 16 := by simpa using haa
  have hbb' : bb < 4 := by simpa using hbb
  refine ⟨aa, bb, ⟨haa', hbb', show 4 * aa + bb < capE by unfold capE; omega, ?_, ?_, rg, h5⟩⟩
  · simp only [CoreMode.prodW, vw, pow_one, mul_one]
    rw [← qg, h39, h34, h29, mul_assoc, mul_assoc]
  · simp only [CoreMode.prodW, vw, pow_one, mul_one]
    rw [← rg, h20]

end

end LeanVM.Guest.EndExec

namespace LeanVM.Guest.CoreMode.Own.shared_selector_tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec
open LeanVM.Protocol.Verifier (gen)

public section

/-- **Its family**: its split's residuals (`splitRes_inst`, `splitW_sst`). -/
theorem fams_ok : ∀ c ∈ fams, OwnOk c := by
  simp only [fams, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  intro r hr I hI σ bufs kids ht fn hf x h
  have hw : SplitW fn CoreMode.spSst := by
    rw [B1.find_sst] at hf
    obtain rfl := Option.some.inj hf
    exact splitW_sst
  exact splitRes_inst hr hI ht hf hw h

end

end LeanVM.Guest.CoreMode.Own.shared_selector_tables
