/-
  LeanVM.Guest.CoreMode.Fn.verify_tables.Sound

  `verify_tables`'s own routing facts and families, sound (`CoreMode/FnReg.lean`): its exponent facts, its rounds loop's cursor, its divisors, its families.
-/

module

public import LeanVM.Guest.EndExecCoreRes
public import LeanVM.Guest.EndExecCoreSt
public import LeanVM.Guest.CoreMode.Fn.verify_tables.EndExecCoreVt
public import LeanVM.Guest.CoreMode.Fn.verify_tables.ExpQv
public import LeanVM.Guest.CoreMode.Fn.verify_tables.ResVtL
public import LeanVM.Guest.CoreMode.Fn.verify_tables.ResVtG
public import LeanVM.Guest.CoreMode.Fn.verify_tables.Data
public import LeanVM.Guest.CoreMode.Fn.verify_tables.Fam
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»
import LeanVM.Guest.Data.ValNames.«verify_tables_loop0»

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CFun CRes CIdx ResF LtF rep_of capE resFam idxC baseC vw)

public section

/-- **`verify_tables`' reads past its table sumcheck** (`vtStC`) at an honest instance: the last record's cursor
`σ cursor@5` is `14 + 3n` words past the frame's cursor (`Tables.vt_zc_run`, `vt_cur13`), which `VtQ` puts `p` words into
the stream with room for `1009`. -/
theorem vtStC_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {x : CRes} (h : CoreMode.vtStC fn x = true) : x.Holds σ := by
  match x, h with
  | .sub c q, h =>
    simp only [CoreMode.vtStC, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hn, hcb⟩, hco⟩, rfl⟩ := h
    have hf' : f = name% «verify_tables» := by rw [← find_name' hf, hn]
    subst hf'
    obtain rfl : fn = fn% «verify_tables» := Option.some.inj (hf.symm.trans B1.VerifySub.find_vt)
    obtain ⟨p, n, e5, hgn, hn34, hroom⟩ := vtQ_all hr I hI σ bufs kids ht
    obtain ⟨args, rets, hv⟩ := inst_valid' hr hI ht
    have hfs : ∀ f', 1 ≤ B2C.fs f' := Res.fs_pos
    obtain ⟨-, hb⟩ := Res.holds_of_valid hfs hv hf
    obtain ⟨hH, -⟩ := vt_holds (fun _ _ _ h ↦ Res.KidRel.rel h) hf hb
    obtain ⟨-, xs, pts, cl, -, -, -, -, e2647, -⟩ := B1.Tables.vt_zc_run hH hn34 hgn
    have hcur : σ (.n (val% «verify_tables» "cursor@5")) = σ (.n (val% «verify_tables» "stream")) * Protocol.Verifier.gen ^ (p + 14 + 3 * n) := by
      rw [e2647, vt_cur13 hH, e5]; ring
    have hcap : (8192 : ℕ) < CoreMode.capE := by rw [CoreMode.capE_eq]; norm_num
    refine ⟨0, 8192, p + 14 + 3 * n + c.off, CoreMode.rep_const (by rw [CoreMode.capE_eq]; norm_num),
      CoreMode.rep_const hcap, Nat.zero_le _, by omega, ?_⟩
    obtain ⟨cb, co⟩ := c
    simp only at hcb
    subst hcb
    simp only [CoreMode.CCell.addrW, CoreMode.CCell.valW, CoreMode.prodW, vw, pow_one, mul_one, one_mul, hcur,
      ← Value.gen_pow_eq_ofK, addressOfIndex]
    rw [mul_assoc, ← pow_add]
    ring_nf
  | .lt _ _, h | .nz _, h | .subR _ _, h | .subP _ _, h | .under _ _, h => simp [CoreMode.vtStC] at h

end

end LeanVM.Guest.EndExec

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CFun CRes stK stSub GlF setG setG_eq ownG ownG_setG prodW vw capE rep_of
  rep_const idxC baseC valW_baseC)
open LeanVM.Guest.Value (gen_pow_eq_ofK gen_pow_inj)
open LeanVM.Guest.B1 (loadHolds_unique)
open LeanVM.Guest.Res (topAtoms)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

/-- The rounds loop's atoms, on its core function: the record `rounds·x^7` and its cursor's load. -/
theorem l10_atoms_fn :
    let as := topAtoms (fn% «verify_tables_loop0»).body
    as.contains (.mul (.n (val% «verify_tables_loop0» "rd~0")) (.n (val% «verify_tables_loop0» "xk")) (.n (val% «verify_tables_loop0» "xk"))) = true ∧ as.contains (.mul (.n (val% «verify_tables_loop0» "rd~1")) (.n (val% «verify_tables_loop0» "rd~0")) (.n (val% «verify_tables_loop0» "xk"))) = true ∧
      as.contains (.mul (.n (val% «verify_tables_loop0» "rd~2")) (.n (val% «verify_tables_loop0» "rd~1")) (.n (val% «verify_tables_loop0» "rd~1"))) = true ∧ as.contains (.mul (.n (val% «verify_tables_loop0» "rd~3")) (.n (val% «verify_tables_loop0» "rd~2")) (.n (val% «verify_tables_loop0» "xk"))) = true ∧
      as.contains (.mul (.n (val% «verify_tables_loop0» "rd")) (.n (val% «verify_tables_loop0» "zc_rounds")) (.n (val% «verify_tables_loop0» "rd~3"))) = true ∧ as.contains (.load (.n (val% «verify_tables_loop0» "s1#0")) (.n (val% «verify_tables_loop0» "rd")) 5) = true := by
  decide +kernel

/-- **`verify_tables`' rounds loop's cursor** in the stream: `VtLQ` and the iteration's record and load. -/
theorem st_vt {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node name% «verify_tables_loop0» σ bufs kids) :
    ∃ a q, I.hdr.2 = ofK (addressOfIndex a) ∧ a + (2 + val% «verify_tables» "stream") < maxCells ∧
      σ (.n (val% «verify_tables_loop0» "s1#0")) = refMem r.img (a + (2 + val% «verify_tables» "stream")) * gen ^ q ∧ q + 3 ≤ 8192 := by
  obtain ⟨a, jj, n, q, hhd, ha22, -, -, hjn, -, hld, hroom⟩ := vtLQ_all hr I hI σ bufs kids ht
  obtain ⟨args, rets, fn', hf', -, es0, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
  obtain rfl : fn' = fn% «verify_tables_loop0» := Option.some.inj (hf'.symm.trans find_l10)
  obtain ⟨t6, t7, t8, t9, t10, tl⟩ := l10_atoms_fn
  have m6 : σ (.n (val% «verify_tables_loop0» "rd~0")) = σ (.n (val% «verify_tables_loop0» "xk")) * σ (.n (val% «verify_tables_loop0» "xk")) := hh _ (topAtoms_on_path hw (List.contains_iff_mem.mp t6))
  have m7 : σ (.n (val% «verify_tables_loop0» "rd~1")) = σ (.n (val% «verify_tables_loop0» "rd~0")) * σ (.n (val% «verify_tables_loop0» "xk")) := hh _ (topAtoms_on_path hw (List.contains_iff_mem.mp t7))
  have m8 : σ (.n (val% «verify_tables_loop0» "rd~2")) = σ (.n (val% «verify_tables_loop0» "rd~1")) * σ (.n (val% «verify_tables_loop0» "rd~1")) := hh _ (topAtoms_on_path hw (List.contains_iff_mem.mp t8))
  have m9 : σ (.n (val% «verify_tables_loop0» "rd~3")) = σ (.n (val% «verify_tables_loop0» "rd~2")) * σ (.n (val% «verify_tables_loop0» "xk")) := hh _ (topAtoms_on_path hw (List.contains_iff_mem.mp t9))
  have m10 : σ (.n (val% «verify_tables_loop0» "rd")) = σ (.n (val% «verify_tables_loop0» "zc_rounds")) * σ (.n (val% «verify_tables_loop0» "rd~3")) := hh _ (topAtoms_on_path hw (List.contains_iff_mem.mp t10))
  have l11 : LoadHolds r.img.read (σ (.n (val% «verify_tables_loop0» "rd"))) 5 (σ (.n (val% «verify_tables_loop0» "s1#0"))) :=
    hh _ (topAtoms_on_path hw (List.contains_iff_mem.mp tl))
  have e10 : σ (.n (val% «verify_tables_loop0» "rd")) = σ (.n (val% «verify_tables_loop0» "zc_rounds")) * σ (.n (val% «verify_tables_loop0» "xk")) ^ 7 := by rw [m10, m9, m8, m7, m6]; ring
  rw [e10] at l11
  exact ⟨a, q, hhd, ha22, loadHolds_unique l11 hld, room_of hjn hroom⟩

end

end LeanVM.Guest.EndExec

namespace LeanVM.Guest.CoreMode.Own.verify_tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec
open LeanVM.Protocol.Verifier (gen)

public section

/-- **Its exponent facts** at its honest instances: `g_bus_mu` and `dims_g`'s first word by its precondition
(`vtPQ_all`), the tables' log-heights by its body (`B1.Tables.vt_pads`). -/
theorem expFacts_ok : ∀ c ∈ expFacts, ExpOk c := by
  intro c hc r hr J hJ σ bufs kids hJt fn hf v hv
  simp only [expFacts, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
    or_false] at hc
  rcases hc with (rfl | rfl) | ⟨k, hk, rfl⟩
  all_goals
    dsimp only at hJt hf hv ⊢
    obtain rfl : fn = fn% «verify_tables» := Option.some.inj (hf.symm.trans B1.VerifySub.find_vt)
    rw [vt_params] at hv
    simp only [List.getElem?_map, List.getElem?_range (by decide : val% «verify_tables» "g_bus_mu" < 21),
      List.getElem?_range (by decide : val% «verify_tables» "dims_g" < 21), Option.map_some, Option.some.injEq] at hv
    subst hv
    obtain ⟨pi, lm, w, pt, vals, hP⟩ := vtPQ_all hr J hJ σ bufs kids hJt
    rw [show (List.range 21).map (fun k ↦ σ (.n k)) = [σ (.n (val% «verify_tables» "fs0")), σ (.n (val% «verify_tables» "fs1")), σ (.n (val% «verify_tables» "fs2")), σ (.n (val% «verify_tables» "fs3")), σ (.n (val% «verify_tables» "fs4")),
      σ (.n (val% «verify_tables» "cursor@1")), σ (.n (val% «verify_tables» "pi_0")), σ (.n (val% «verify_tables» "pi_1")), σ (.n (val% «verify_tables» "zeta")), σ (.n (val% «verify_tables» "g_bus_mu")), σ (.n (val% «verify_tables» "dims_g")), σ (.n (val% «verify_tables» "table_rows")), σ (.n (val% «verify_tables» "g_squares")), σ (.n (val% «verify_tables» "fp_w")),
      σ (.n (val% «verify_tables» "beta")), σ (.n (val% «verify_tables» "claim_pool")), σ (.n (val% «verify_tables» "chi")), σ (.n (val% «verify_tables» "gkr_leaves")), σ (.n (val% «verify_tables» "tabs")), σ (.n (val% «verify_tables» "bc_point")), σ (.n (val% «verify_tables» "stream"))] from rfl] at hP
    obtain ⟨-, -, hgmu, hlen, -, hlm, ⟨ds, -, hds⟩, -⟩ := hP
  · exact ⟨pt.length, hlen, hgmu⟩
  · exact ⟨lm, show lm < 33 by omega, hds 0 (by simp)⟩
  · -- `dims_g`'s other words: the tables' log-heights, below `31`, by its body (`vt_pads`)
    obtain ⟨args, rets, hJv⟩ := inst_valid' hr hJ hJt
    have hfs : ∀ f', 1 ≤ B2C.fs f' := Res.fs_pos
    obtain ⟨-, hbJ⟩ := Res.holds_of_valid hfs hJv B1.VerifySub.find_vt
    obtain ⟨hVt, -⟩ := vt_holds (fun _ _ _ h ↦ Res.KidRel.rel h) B1.VerifySub.find_vt hbJ
    have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
    obtain ⟨τ, -, -, h1, h2, -⟩ := B1.Tables.vt_pads (by omega) r.img σ hVt k hk
    exact ⟨τ, h1, h2⟩


/-- **Its word `g_zc_n = g^n`, `n < 34`** (`VtQ`). -/
theorem expVals_ok : ∀ c ∈ expVals, ExpValOk c := by
  intro c hc r hr J hJ σ bufs kids hJt
  simp only [expVals, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  obtain ⟨-, n, -, hz, hn34, -⟩ := vtQ_all hr J hJ σ bufs kids hJt
  exact ⟨n, hn34, hz⟩

/-- **Its rounds loop's cursor** (`st_vt`). -/
theorem stLoops_ok : ∀ c ∈ stLoops, StLoopOk c := by
  intro c hc
  simp only [stLoops, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  exact ⟨by decide, by unfold CoreMode.GB; decide, fun hr I hI σ bufs kids ht _ _ ↦ st_vt hr hI ht⟩

/-- **Its divisors, nonzero.** -/
theorem nzs_ok : ∀ c ∈ nzs, NzOk c := by
  simp only [nzs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨nzVal_vt133, nzVal_vt430, nzVal_vtKb (t := 0) (by decide), nzVal_vtKb (t := 1) (by decide),
    nzVal_vtKb (t := 2) (by decide), nzVal_vtKb (t := 3) (by decide), nzVal_vtKb (t := 4) (by decide),
    nzVal_vtKb (t := 5) (by decide)⟩

/-- **Its families.** -/
theorem fams_ok : ∀ c ∈ fams, OwnOk c := by
  simp only [fams, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨fun hr I hI σ bufs kids ht fn hf x h ↦ vtStC_inst hr hI ht hf h,
    fun hr I hI σ bufs kids ht fn hf x h ↦ vtPerm_inst hr hI ht hf h⟩

/-- **Its exponent family.** -/
theorem gwFams_ok : ∀ c ∈ gwFams, GwFamOk c := by
  simp only [gwFams, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact fun hr I hI σ bufs kids ht fn hf σ' hag hng G hgw x h ↦ vtExp_inst hr hI ht hf hag hng hgw h

end

end LeanVM.Guest.CoreMode.Own.verify_tables
