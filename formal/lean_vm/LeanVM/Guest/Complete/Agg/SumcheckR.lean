module

public import LeanVM.Guest.Complete.Agg.SumcheckA
public import LeanVM.Guest.Complete.Agg.Calls
public import LeanVM.Guest.B1.VsC.SlowA
import LeanVM.Guest.CoreRef

/-!
# `batch_sumcheck__L25` in its two arrays

`agg_bs_callCompletesA` loads from `argRegion`, which admits every index with a pointer's address
(`addressOfIndex` has period `2^64 - 1`), so no bounded region contains it. `agg_bs_atEvery'` loads
from the two arrays' indices themselves (`bsReg`), by `loadsR_mono'`.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.VsC LeanVM.Guest.Complete

@[expose] public section

/-- The batching sumcheck's arrays: `50` cells from `bm`, `25` from `bp`. -/
def bsReg (bm bp : ℕ) (i : ℕ) : Prop := (bm ≤ i ∧ i < bm + 50) ∨ (bp ≤ i ∧ i < bp + 25)

theorem argRegion_bsReg {args : List E} {bm bp : ℕ} (hm : args.getD 5 0 = ptrAt bm)
    (hp : args.getD 7 0 = ptrAt bp) (i : ℕ) (h : argRegion args [(5, 50), (7, 25)] i) :
    ∃ i', addressOfIndex i = addressOfIndex i' ∧ bsReg bm bp i' := by
  obtain ⟨q, hq, b, hb, h1, h2⟩ := h
  have shift : ∀ a, addressOfIndex a = addressOfIndex b → addressOfIndex i = addressOfIndex (a + (i - b)) :=
    fun a he => by rw [← gpow_add', he, gpow_add', show b + (i - b) = i by omega]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨bm + (i - b), shift bm (ptrAt_inj (hm.symm.trans hb)), Or.inl ⟨by omega, by simp at h2; omega⟩⟩
  · exact ⟨bp + (i - b), shift bp (ptrAt_inj (hp.symm.trans hb)), Or.inr ⟨by omega, by simp at h2; omega⟩⟩

/-- **`callCompletesA_of_loadOk` in a region holding, for each cell of the arrays, a cell of the
same address**, at each position: block `fs f`, ending at its cursor. -/
theorem callAtA_of_loadOk' {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}
    {S : List String} (hS : coreProgram.PureIn S) {k : ℕ} {f : String} (hf : f ∈ S)
    (hlp : coreProgram.loop f = false) {fn : Fn} {ps : List (ℕ × ℕ)} {args rets : List E}
    {Pre : Reader → Prop} {Post : Reader → Tree → Prop} (hfind : coreProgram.find? f = some fn)
    (hparams : fn.params = (List.range args.length).map V.n)
    (hL : (atomsOf fn.body).all (loadOkB ps) = true) (hr : (retOf fn.body).isSome = true)
    (hargs : ∀ q ∈ ps, q.1 < args.length) (hptr : ∀ q ∈ ps, ∃ b, args.getD q.1 0 = ptrAt b)
    {R' : ℕ → Prop} (hR : ∀ i, argRegion args ps i → ∃ i', addressOfIndex i = addressOfIndex i' ∧ R' i')
    (h : CallCompletes0 k f args rets Pre Post) (fp c : ℕ) :
    CallAtA fs al cert k f args rets R' (fun _ => False) (fun _ => True) Pre Post (fs f) fp c c := by
  obtain ⟨vs0, hr'⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr'
  have hnc : ∀ fn' σ es vs, coreProgram.find? f = some fn' → walk σ fn'.body = .ret es vs → calls es = [] :=
    fun fn' σ es vs hfn hw => by
      rw [hfind] at hfn
      cases hfn
      have hb' : fn.body = (atomsOf ss).map Stmt.atom ++ [.ret vs0] := by rw [hbody, ← eq_map_atomsOf hss]
      have hw' : walk σ fn.body = .ret ((atomsOf ss).map Ev.atom) vs0 := by rw [hb']; exact walk_atoms _ _ _
      rw [hw'] at hw
      cases hw
      exact calls_atoms _
  refine callAtA_of_callCompletes0 hS hf le_rfl h fun rd t _ _ hn hv hb _ => ?_
  have hbe := block_endA_leaf (fs := fs) (al := al) hS hf hlp hnc hn hv hb c
  have h' := loadsR_hintsR_of_loadOk R' hfind hparams hL hr hargs hptr hn hv
  exact ⟨hbe.1, hbe.2, loadsR_mono' hR t h'.1, h'.2⟩

/-- **`callCompletesA_of_loadOk` in a region holding, for each cell of the arrays, a cell of the
same address.** -/
theorem callCompletesA_of_loadOk' {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}
    {S : List String} (hS : coreProgram.PureIn S) {k : ℕ} {f : String} (hf : f ∈ S)
    (hlp : coreProgram.loop f = false) {fn : Fn} {ps : List (ℕ × ℕ)} {args rets : List E}
    {Pre : Reader → Prop} {Post : Reader → Tree → Prop} (hfind : coreProgram.find? f = some fn)
    (hparams : fn.params = (List.range args.length).map V.n)
    (hL : (atomsOf fn.body).all (loadOkB ps) = true) (hr : (retOf fn.body).isSome = true)
    (hargs : ∀ q ∈ ps, q.1 < args.length) (hptr : ∀ q ∈ ps, ∃ b, args.getD q.1 0 = ptrAt b)
    {R' : ℕ → Prop} (hR : ∀ i, argRegion args ps i → ∃ i', addressOfIndex i = addressOfIndex i' ∧ R' i')
    (h : CallCompletes0 k f args rets Pre Post) :
    CallCompletesA fs al cert k f args rets R' (fun _ _ _ => False) (fun _ => True) Pre Post :=
  ⟨fs f, fun fp c _ => ⟨c, (callAtA_of_loadOk' (fs := fs) (al := al) (cert := cert) hS hf hlp hfind hparams hL hr
    hargs hptr hR h fp c).mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ _ _ h => h)⟩⟩

/-- **The batching sumcheck placed at every position, loading from its two arrays.** -/
theorem agg_bs_atEvery' {al : String → Bool} {k : ℕ} {Pre : Reader → Prop} (hwf : coreProgram.Wf)
    {args rets : List E} (hlen : args.length = 9) {bm bp : ℕ} (hm : args.getD 5 0 = ptrAt bm)
    (hp : args.getD 7 0 = ptrAt bp) (hpre : ∀ rd, Pre rd → MeaningBatchSumcheck 25 rd args rets) :
    ∃ B, AtEvery al k "batch_sumcheck__L25" args rets (bsReg bm bp) Pre FreePost B 0 :=
  atEvery_of_completesA (callCompletesA_of_loadOk' bs_pureIn List.mem_cons_self bs_not_loop find_bs
    (by rw [hlen]; rfl) (by decide +kernel) (by decide +kernel)
    (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp [hlen])
    (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨bm, hm⟩
      · exact ⟨bp, hp⟩)
    (argRegion_bsReg hm hp)
    (callCompletes0_free hwf agg_bs_free.1 agg_bs_free.2 fun rd _ hp' =>
      (batch_sumcheck_holds rd args rets).mpr (hpre rd hp')))

/-- **The batching sumcheck placed at every position, loading from its two arrays**, its block its
frame, ending at its cursor. -/
theorem agg_bs_atEveryB {al : String → Bool} {k : ℕ} {Pre : Reader → Prop} (hwf : coreProgram.Wf)
    {args rets : List E} (hlen : args.length = 9) {bm bp : ℕ} (hm : args.getD 5 0 = ptrAt bm)
    (hp : args.getD 7 0 = ptrAt bp) (hpre : ∀ rd, Pre rd → MeaningBatchSumcheck 25 rd args rets) {T β : ℕ} :
    AtEveryB al k "batch_sumcheck__L25" args rets (bsReg bm bp) Pre FreePost (B2C.fs "batch_sumcheck__L25") 0 T β :=
  atEveryB_of_le fun fp c _ _ => ⟨c, le_rfl, callAtA_of_loadOk' bs_pureIn List.mem_cons_self bs_not_loop find_bs
    (by rw [hlen]; rfl) (by decide +kernel) (by decide +kernel)
    (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp [hlen])
    (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨bm, hm⟩
      · exact ⟨bp, hp⟩)
    (argRegion_bsReg hm hp)
    (callCompletes0_free hwf agg_bs_free.1 agg_bs_free.2 fun rd _ hp' =>
      (batch_sumcheck_holds rd args rets).mpr (hpre rd hp')) fp c⟩

end
end LeanVM.Guest.Complete.Agg
