/-
  LeanVM.Guest.B1.VerifySub.CPlaced4

  `verify_sub` placed: its callees as `Kid`s, each complete in the uniform placed form.
-/

module

public import LeanVM.Guest.B1.VerifySub.CLog2c
public import LeanVM.Guest.B1.VerifySub.Inv5
public import LeanVM.Guest.Memory.GuestSize
public import LeanVM.Guest.B1.Tables.Kappas
public import LeanVM.Guest.B1.Main.WeightB
public import LeanVM.Guest.B1.VerifySub.StaticW

/-!
# `verify_sub`'s callees, placed

`vsKids1`: the twelve calls before the dispatch, `vsOpenKid`: the opening, `vsTermKid`: the
terminal, each with the words it reads (`vsAllL`, `verify_sub`'s own and the caller's, and for the
terminal the buffers the placement and the opening return) and what it returns. Each is
`CompleteAt` (`vsKids1_completeB`, `vsOpenKid_completeB`, `vsTermKid_completeB`) from the callees'
placed completeness, group 1's `g_power_of_word` (`gpw6_completeAt`) and
`log2_ceil_in_the_exponent` (`CLog2c`), `assert_canonical` and the two loops (pure,
`completeAt_of_rel_pure`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-! ## Group 1 and the pure callees -/

theorem gpw6_completeAt' (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {N : ℕ} (hN : N < 64)
    (qb : ℕ) :
    CompleteAtB fs cert k "g_power_of_word__L6" [(qb, gpwSq)] [eOfNat N, ofK (Parameters.gpow qb)]
      (Returns [gen ^ N]) (fs "g_power_of_word__L6" + 6) := by
  have h := gpw6_completeAt fs cert k hN qb
  rwa [gpwProd_pow (n := 6) (fun j hj => by simp [gpwSq, hj]) (by omega)] at h

theorem pure_one {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hb : Stmt.pureList [f] fn.body = true) : coreProgram.PureIn [f] := by
  intro g hg fn' hf'
  rw [List.mem_singleton] at hg
  subst hg
  rw [hf, Option.some.injEq] at hf'
  subst hf'
  exact hb

set_option maxRecDepth 100000 in
theorem ac_pure : coreProgram.PureIn ["assert_canonical"] :=
  pure_one find_assert_canonical (by decide +kernel)

set_option maxRecDepth 100000 in
theorem loop84_pure : coreProgram.PureIn ["__loop84"] := pure_one find_loop84 (by decide +kernel)

set_option maxRecDepth 100000 in
theorem loop85_pure : coreProgram.PureIn ["__loop85"] := pure_one find_loop85 (by decide +kernel)

/-! ## The words the callees read -/

variable (fs : String → ℕ) (cert : String → V → ℕ) (bytecode : List K) (D : VsData)

/-- `verify_sub`'s own words and the caller's. -/
def vsAllL (fp lpA sqA outA : ℕ) : Main.Layout := vsOwnL fs fp D ++ vsExtL lpA sqA outA D

variable {fs cert bytecode D}
variable {rd : Reader} {fp lpA sqA outA : ℕ} {off kap pt : E}

theorem vsAll_mem (h : MemL rd (vsAllL fs D fp lpA sqA outA)) :
    VsMem0 rd D (vsPtrsAt fs fp D off kap pt) (ofK (Parameters.gpow outA)) ∧
      ExpTables rd (ofK (Parameters.gpow lpA)) (ofK (Parameters.gpow sqA)) ∧
      ReadsAt rd (vsPtrsAt fs fp D off kap pt).chi D.chis ∧
      ReadsAt rd (vsPtrsAt fs fp D off kap pt).cplen (cplenWords D) := by
  obtain ⟨h1, h2⟩ := Main.memL_append.mp h
  obtain ⟨h3, h4⟩ := Main.memL_append.mp h2
  exact ⟨vsMem0_of h1 (h4 _ List.mem_cons_self), expTables_of h3, chis_of h1, cplen_of h1⟩

theorem gpwSq_mem (h : MemL rd (vsAllL fs D fp lpA sqA outA)) : MemL rd [(sqA, gpwSq)] := by
  have h2 := h (sqA, (List.range sizeBits).map fun j => gen ^ 2 ^ j) (by simp [vsAllL, vsExtL, expL])
  intro q hq
  simp only [List.mem_singleton] at hq
  subst hq
  intro j hj
  have := h2 j (by simp [gpwSq, sizeBits] at hj ⊢; omega)
  simpa [gpwSq] using this

/-! ## The callees -/

variable (fs bytecode D)

/-- What `certify_placement` returns: the stack's total, and the two buffers `PCtx` reads. -/
def PlaceOut (rets : List E) (Lout : Main.Layout) : Prop :=
  ∃ off kap, rets = [gen ^ D.stackTot, off, kap] ∧
    ∀ rd, MemL rd Lout → PCtx rd (columnKappas D.logMem 18 D.hs) off kap

/-- What the opening returns: `w`'s claim, its point's buffer, its weight and its residual. -/
def OpenOutK (rets : List E) (Lout : Main.Layout) : Prop :=
  ∃ b, rets = [D.w.target, ofK (Parameters.gpow b), D.w.inner, D.w.residual] ∧
    Lout = [(b, D.w.point ++ List.replicate (pointCap - D.w.point.length) 0)]

/-- **The calls before the dispatch**, at the pointers of `verify_sub`'s buffers at `fp`. -/
noncomputable def vsKids1 (fp lpA sqA outA : ℕ) : List Kid :=
  let P := vsPtrsAt fs fp D 0 0 0
  let lp := ofK (Parameters.gpow lpA)
  let sq := ofK (Parameters.gpow sqA)
  let LA := vsAllL fs D fp lpA sqA outA
  [⟨"g_power_of_word__L6", true, [eOfNat D.rate, sq], [(sqA, gpwSq)], Returns [gen ^ D.rate]⟩,
    ⟨"g_power_of_word__L6", true, [eOfNat D.logMem, sq], [(sqA, gpwSq)], Returns [gen ^ D.logMem]⟩,
    ⟨"log2_ceil_in_the_exponent__L0_L34", true, [gen ^ D.pushTotal, lp, sq], LA,
      Returns [gen ^ log2Ceil D.pushTotal]⟩,
    ⟨"assert_canonical", true, [D.x0], [], Returns [0]⟩,
    ⟨"assert_canonical", true, [D.x1], [], Returns [0]⟩,
    ⟨"verify_bus_gkr", true, [(digestScalars D.cvB).1, (digestScalars D.cvB).2, curG P,
      gen ^ log2Ceil D.pushTotal, P.zeta], LA,
      Returns [(digestScalars D.cvG).1, (digestScalars D.cvG).2, curT D P, D.gr.2.2.getD 0 0,
        D.gr.2.2.getD 1 0, D.gr.2.2.getD 2 0]⟩,
    ⟨"verify_tables", true, [(digestScalars D.cvG).1, (digestScalars D.cvG).2, curT D P,
      (digestScalars D.pi).1, (digestScalars D.pi).2, P.zeta, gen ^ log2Ceil D.pushTotal, P.dims,
      P.rows, P.bk, sq, P.fpw, D.beta, P.pool, P.cplen, P.chi, D.gr.2.2.getD 0 0, D.gr.2.2.getD 1 0,
      D.gr.2.2.getD 2 0], LA,
      Returns [(digestScalars D.cvT).1, (digestScalars D.cvT).2, curF D P, D.gzcn, D.bv, D.rm]⟩,
    ⟨"verify_flock", true, [(digestScalars D.cvT).1, (digestScalars D.cvT).2, curF D P, gen ^ D.tau,
      P.zchis, P.lrs, P.zpart], LA,
      Returns [(digestScalars D.cvF).1, (digestScalars D.cvF).2, curW D P, D.zSkip, D.alpha, D.mv]⟩,
    ⟨"__loop84", true, [word 1 0 0, P.zpart, P.mcs, P.rs], LA, Returns []⟩,
    ⟨"__loop85", decide (word 1 0 0 + gen ^ D.tau ≠ 0),
      [word 1 0 0, gen ^ D.tau, P.zvals * word 256 0 0, P.zchis * word 256 0 0], LA, Returns []⟩,
    ⟨"certify_placement", true, [P.kbase, sq], LA, PlaceOut D⟩,
    ⟨"log2_ceil_in_the_exponent__L15_L34", true, [gen ^ D.stackTot, lp, sq], LA,
      Returns [gen ^ max 15 (log2Ceil D.stackTot)]⟩]

/-- **The opening.** -/
noncomputable def vsOpenKid (fp lpA sqA outA : ℕ) : Kid :=
  ⟨openName (layoutOf bytecode D.logMem D.rows).stackLog D.rate, true,
    [(digestScalars D.cvL).1, (digestScalars D.cvL).2, D.target, D.x0, D.x1,
      curW D (vsPtrsAt fs fp D 0 0 0)], vsAllL fs D fp lpA sqA outA, OpenOutK D⟩

/-- **The terminal**, at the placement's buffers `off`, `kap` (held by `Lc`) and the opening's
point `pt` (held by `Lo`). -/
noncomputable def vsTermKid (fp lpA sqA outA : ℕ) (off kap pt : E) (Lc Lo : Main.Layout) : Kid :=
  let P := vsPtrsAt fs fp D off kap pt
  ⟨"check_opening_terminal", true, [P.zeta, P.chi, D.rm, gen ^ log2Ceil D.pushTotal, D.gzcn,
    gen ^ D.logMem, gen ^ D.tau, P.cplen, P.lam, P.off, P.kap, P.zvals, P.ctab, P.pt, D.w.inner,
    D.w.residual, D.w.target], vsAllL fs D fp lpA sqA outA ++ Lc ++ Lo, Returns []⟩

variable {fs bytecode D}

/-! ## Their completeness -/

/-- The bounds of `verify_sub`'s callees' trees. -/
structure VsBounds where
  gkr : ℕ
  tab : ℕ
  fl : ℕ
  pl : ℕ
  op : ℕ
  term : ℕ

/-- A call before the dispatch: its callee's bound. -/
def vsBd (fs : String → ℕ) (Bs : VsBounds) (k : Kid) : ℕ :=
  if k.f = "g_power_of_word__L6" then fs "g_power_of_word__L6" + 6
  else if k.f = "log2_ceil_in_the_exponent__L0_L34" then log2Bound0 fs
  else if k.f = "assert_canonical" then fs "assert_canonical"
  else if k.f = "verify_bus_gkr" then Bs.gkr
  else if k.f = "verify_tables" then Bs.tab
  else if k.f = "verify_flock" then Bs.fl
  else if k.f = "__loop84" then 64 * (2 * fs "__loop84")
  else if k.f = "__loop85" then 28 * (2 * fs "__loop85")
  else if k.f = "certify_placement" then Bs.pl
  else log2Bound15 fs

/-- Read a callee's bound off `vsBd`. -/
macro "vs_bd" : tactic => `(tactic| simp (config := { decide := true }) [vsBd])

theorem pushTotal_bounds (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) :
    D.pushTotal < 2 ^ 34 ∧ log2Ceil D.pushTotal < 34 := by
  have hdep : log2Ceil D.pushTotal < 33 := by
    rw [← depth_eq hb hok, hok.point_length]; exact hok.depth_lt
  exact ⟨lt_of_le_of_lt (le_two_pow_log2Ceil _) (Nat.pow_lt_pow_right (by decide) (by omega)),
    by omega⟩

/-- **The calls before the dispatch are complete.** -/
theorem vsKids1_completeB {κ : ℕ} (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode)
    (htok : D.TOk bytecode) {Bs : VsBounds} (hG : CompleteGkrAtB fs cert κ Bs.gkr)
    (hT : CompleteTablesAtB fs cert κ bytecode TCtx Bs.tab) (hF : CompleteFlockAtB fs cert κ Bs.fl)
    (hPl : CompletePlaceAtB fs cert κ PCtx Bs.pl) 
    (hκ : 7 ≤ κ) :
    ∀ k ∈ vsKids1 fs D fp lpA sqA outA, k.taken = true →
      CompleteAtB fs cert κ k.f k.Lin k.args k.Out (vsBd fs Bs k) := by
  intro k hk ht
  have hc : ∀ x : E, IsCanonical128 x →
      CompleteAtB fs cert κ "assert_canonical" [] [x] (Returns [0]) (fs "assert_canonical") :=
    fun x hx => completeAt_of_rel_pureBat ac_pure (by simp)
      (fun rd _ => (assert_canonical_iff rd [x] [0]).mpr ⟨hx, rfl⟩) κ
      fun rd t hn hv hb => assert_canonical_totalLe fs rd t _ _ hn hv hb
  obtain ⟨hN, hl⟩ := pushTotal_bounds hb hok
  have M := fun rd (hm : MemL rd (vsAllL fs D fp lpA sqA outA)) =>
    vsAll_mem (off := 0) (kap := 0) (pt := 0) hm
  have CE := cur_eqs (fs := fs) (fp := fp) (D := D) (off := 0) (kap := 0) (pt := 0)
  obtain ⟨-, hl28, hst⟩ := stack_facts hb hok
  have hq8 : D.hs.getD 5 0 + 8 < 34 := by
    have := qflock_bound hb hok.rows_length hok.stack_le; simp only [VsData.hs]; omega
  have hE : ∀ q ∈ expL lpA sqA, q ∈ vsAllL fs D fp lpA sqA outA := fun q hq =>
    List.mem_append_right _ (List.mem_append_left _ hq)
  simp only [vsKids1, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (gpw6_completeAt' fs cert κ (by have := hok.rate_le; omega) sqA).mono le_rfl (by vs_bd)
  · exact (gpw6_completeAt' fs cert κ (by have := hok.logMem_le; omega) sqA).mono le_rfl
      (by vs_bd)
  · exact (log2L0_completeAt (by omega) hN hl lpA sqA _ hE).mono le_rfl (by vs_bd)
  · exact (hc _ (isCanonical128_digestScalars _).1).mono le_rfl (by vs_bd)
  · exact (hc _ (isCanonical128_digestScalars _).2).mono le_rfl (by vs_bd)
  · have h := hG D.cvB _ D.xsG D.gr D.cvG (vsB fs fp D 2 + 10) (vsB fs fp D 7) _ hok.depth_lt hok.gkr
      hok.point_length hok.values_length fun rd _ hm => ⟨by
        have := (stream_at hok.rows_length (M rd hm).1.stream).1
        rwa [CE.1] at this, (M rd hm).1.zeta⟩
    rw [← hok.point_length, depth_eq hb hok, values_eq hok, ← CE.1] at h
    exact h.mono le_rfl (by vs_bd)
  · have h := hT D.pi D.logMem D.alphas D.gr.2.1 D.gr.2.2 D.cvG D.xsT D.cvT D.rows D.bus D.claims
      D.beta D.bv D.rm D.gzcn (vsB fs fp D 2 + 10 + D.xsG.length) (vsB fs fp D 7) lpA sqA
      (vsB fs fp D 4) (vsB fs fp D 3) (vsB fs fp D 6) (vsB fs fp D 9) (vsB fs fp D 0)
      (vsB fs fp D 1) (vsB fs fp D 10) _ hb (by
        rw [hok.point_length]; unfold pushDepth; rw [layoutOf_logBytecode hb]; rfl)
      (by rw [hok.point_length]; exact hok.depth_lt) (by rw [htok.gzcn, htok.chis_len])
      hok.logMem_ge hok.logMem_le (by simp [VsData.alphas, sqAll_eq]) hok.values_length
      hok.rows_length hok.rows_log hok.claims_length hok.tables fun rd _ hm => by
        obtain ⟨h0, ht, hc, hp⟩ := M rd hm
        refine ⟨?_, h0.zeta, ht, h0.rows, ?_, ?_, h0.fpw, h0.pool, tctx_of hok htok h0.zeta hc hp⟩
        · have := (stream_at hok.rows_length h0.stream).2.1
          rwa [CE.2.1] at this
        · have := h0.dims
          rwa [dims_eq] at this
        · have := h0.bk
          rwa [hsMap_eq] at this
    rw [← CE.2.1, depth_eq hb hok] at h
    exact h.mono le_rfl (by vs_bd)
  · have h := hF D.tau D.cvT D.xsF D.cvF D.zSkip D.alpha D.mv D.chi D.rcs D.s
      (vsB fs fp D 2 + 10 + D.xsG.length + D.xsT.length) (vsB fs fp D 11) (vsB fs fp D 12)
      (vsB fs fp D 13) _ (tau_lt hok) hok.chi_length hok.rcs_length hok.s_length hok.flock
      fun rd _ hm => ⟨by
        have := (stream_at hok.rows_length (M rd hm).1.stream).2.2.1
        rwa [CE.2.2.1] at this, (M rd hm).1.zchis, (M rd hm).1.lrs, (M rd hm).1.zpart⟩
    rw [← CE.2.2.1] at h
    exact h.mono le_rfl (by vs_bd)
  · refine (completeAt_of_rel_pureBat loop84_pure (by simp) (fun rd hm => ?_) κ
      (B := 64 * (2 * fs "__loop84")) fun rd t hn hv hb => ?_).mono le_rfl (by vs_bd)
    swap
    · have e0 : word 1 0 0 = ofK (Parameters.gpow 0) := by
        rw [word_one, Parameters.gpow, pow_zero, ofK_one]
      have h := loop84_totalLe fs rd t [word 1 0 0, (vsPtrsAt fs fp D 0 0 0).zpart,
        (vsPtrsAt fs fp D 0 0 0).mcs, (vsPtrsAt fs fp D 0 0 0).rs] _ hn ⟨0, e0, by decide⟩ hv hb
      simp only [List.getD_cons_zero, e0, logG_spec (show (0 : ℕ) < 2 ^ 64 - 1 by decide),
        Nat.sub_zero] at h
      exact h
    rw [word_one, ← pow_zero gen]
    exact loop84_complete (loop84_bodies (M rd hm).1 hok.s_length mcs_length)
  · have hτ : D.tau ≠ 0 := by
      intro h0
      simp only [h0, pow_zero, word_one, CharTwo.add_self_eq_zero, ne_eq, not_true_eq_false,
        decide_false, Bool.false_eq_true] at ht
    have hτ29 := tau_lt hok
    have e0 : word 1 0 0 = ofK (Parameters.gpow 0) := by
      rw [word_one, Parameters.gpow, pow_zero, ofK_one]
    refine (completeAt_of_rel_pureBat loop85_pure (by simp) (fun rd hm => ?_) κ
      (B := D.tau * (2 * fs "__loop85")) fun rd t hn hv hb => ?_).mono le_rfl
      (le_trans (Nat.mul_le_mul_right _ (show D.tau ≤ 28 by omega)) (by vs_bd))
    swap
    · have h := loop85_totalLe fs rd t [word 1 0 0, gen ^ D.tau,
        (vsPtrsAt fs fp D 0 0 0).zvals * word 256 0 0, (vsPtrsAt fs fp D 0 0 0).zchis * word 256 0 0]
        _ hn ⟨0, D.tau, e0, gen_pow_eq_ofK _, Nat.pos_of_ne_zero hτ, by omega⟩ hv hb
      simp only [List.getD_cons_zero, List.getD_cons_succ, e0, gen_pow_eq_ofK,
        logG_spec (show (0 : ℕ) < 2 ^ 64 - 1 by decide),
        logG_spec (show D.tau < 2 ^ 64 - 1 by omega), Nat.sub_zero] at h
      exact h
    have w8 : word 256 0 0 = gen ^ 8 := word_two_pow (a := 8) (by decide)
    have hm0 := (M rd hm).1
    rw [word_one, ← pow_zero gen, w8]
    refine loop85_complete (Nat.pos_of_ne_zero hτ) (by have := tau_lt hok; unfold ordG; omega) rfl
      fun j _ hj => ?_
    have hcl := hok.chi_length
    refine ⟨D.chi.getD (8 + j) 0, ?_, ?_⟩
    · rw [mul_assoc, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero]
      exact readsAt_getD hm0.zchis (by omega)
    · rw [mul_assoc, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero]
      have : D.fpoint.getD (8 + j) 0 = D.chi.getD (8 + j) 0 := by
        rw [VsData.fpoint, List.getD_eq_getElem _ _ (by simp [hok.rcs_length]; omega),
          List.getElem_append_right (by simp [hok.rcs_length]), List.getElem_drop,
          List.getD_eq_getElem _ _ (by omega)]
        simp only [List.length_reverse, hok.rcs_length]
        congr 1; omega
      rw [← this]; exact readsAt_getD hm0.zvals (by simp [VsData.fpoint, hok.rcs_length]; omega)
  · exact (hPl _ _ _ D.logMem D.hs _ hok.logMem_le (hs_length hok) (hs_lt hok) hq8 fun rd _ hm =>
      placePre_of (M rd hm).2.1 (M rd hm).1).mono le_rfl (by vs_bd)
  · exact (log2L15_completeAt (by omega) hst (by omega) lpA sqA _ hE).mono le_rfl (by vs_bd)

/-- **The opening is complete**, on its run and the agreement `CapOk` at the cap. -/
theorem vsOpenKid_completeB {κ : ℕ} {CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop}
    {B : ℕ} (hok : D.Ok bytecode) (hO : CompleteOpenAtB fs cert κ CapOk B)
    (hcap : CapOk (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.root D.cvL D.xsW D.os
      D.target) :
    let k := vsOpenKid fs bytecode D fp lpA sqA outA
    CompleteAtB fs cert κ k.f k.Lin k.args k.Out B := by
  intro k
  have h := hO _ D.rate hok.stack_ge hok.stack_le hok.rate_ge hok.rate_le D.root D.cvL D.xsW D.os D.w
    D.cvW D.roots' D.target _ (vsAllL fs D fp lpA sqA outA) hok.opening hcap fun rd _ hm => by
      have := (stream_at hok.rows_length (vsAll_mem (off := 0) (kap := 0) (pt := 0) hm).1.stream).2.2.2
      rwa [curW_eq] at this
  rw [← curW_eq] at h
  exact h

/-- **The terminal is complete**, on the placement's and the opening's buffers. -/
theorem vsTermKid_completeB {κ : ℕ} (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode)
    (htok : D.TOk bytecode) {B : ℕ} (hE : CompleteTermAtB fs cert κ TCtx PCtx B) {Lc : Main.Layout}
    {b : ℕ}
    (hc : ∀ rd, MemL rd Lc → PCtx rd (columnKappas D.logMem 18 D.hs) off kap) :
    let k := vsTermKid fs D fp lpA sqA outA off kap (ofK (Parameters.gpow b)) Lc
      [(b, D.w.point ++ List.replicate (pointCap - D.w.point.length) 0)]
    CompleteAtB fs cert κ k.f k.Lin k.args k.Out B := by
  intro k
  refine hE (layoutOf bytecode D.logMem D.rows) D.bus D.claims D.lam D.fpoint (ringCoefficients D.mcs)
    D.w D.chis _ _ hok.accepts htok.point_vars htok.gzcn fun rd _ hm => ?_
  obtain ⟨h12, h3⟩ := Main.memL_append.mp hm
  obtain ⟨h1, h2⟩ := Main.memL_append.mp h12
  obtain ⟨hm0, -, hchi, hcp⟩ := vsAll_mem (off := off) (kap := kap) (pt := ofK (Parameters.gpow b)) h1
  have htc := tctx_of hok htok hm0.zeta hchi hcp
  rw [depth_eq hb hok] at htc
  exact ⟨termPre_of hb hok htc (hc rd h2) (hypKappa rd) hm0.lam hm0.zvals hm0.ctab
    (h3 _ List.mem_cons_self), hchi⟩

/-! ## Within weights -/

section Weights

variable {Θ : Type}

/-- **The weights of `verify_sub`'s statically bounded callees** at the frame weights `w θ`, every
valid tree within them: `g_power_of_word__L6`, the two `log2_ceil_in_the_exponent` arms,
`assert_canonical`, `certify_placement`, and `open_stacked` at every configuration. -/
structure VsWeightHyps (w : Θ → String → ℕ) : Type where
  gpw : Θ → ℕ
  gpw_le : ∀ θ, WeightLe coreProgram (w θ) "g_power_of_word__L6" fun _ => gpw θ
  l2a : Θ → ℕ
  l2a_le : ∀ θ, WeightLe coreProgram (w θ) "log2_ceil_in_the_exponent__L0_L34" fun _ => l2a θ
  l2b : Θ → ℕ
  l2b_le : ∀ θ, WeightLe coreProgram (w θ) "log2_ceil_in_the_exponent__L15_L34" fun _ => l2b θ
  ac : Θ → ℕ
  ac_le : ∀ θ, WeightLe coreProgram (w θ) "assert_canonical" fun _ => ac θ
  pl : Θ → ℕ
  pl_le : ∀ θ, WeightLe coreProgram (w θ) "certify_placement" fun _ => pl θ
  os : Θ → ℕ
  os_le : ∀ θ μ r, 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 →
    WeightLe coreProgram (w θ) (openName μ r) fun _ => os θ

/-- At no weights, vacuously. -/
def VsWeightHyps.empty (w : Empty → String → ℕ) : VsWeightHyps w :=
  ⟨fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim,
    fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim⟩

/-- The hypotheses from a weight of each callee at every `w θ`. -/
def VsWeightHyps.ofStat {w : Θ → String → ℕ} (c : Θ → VsStat) (h : ∀ θ, VsStatOk (w θ) (c θ)) :
    VsWeightHyps w :=
  ⟨fun θ => (c θ).gpw, fun θ => (h θ).gpw, fun θ => (c θ).l2a, fun θ => (h θ).l2a, fun θ => (c θ).l2b,
    fun θ => (h θ).l2b, fun θ => (c θ).ac, fun θ => (h θ).ac, fun θ => (c θ).pl, fun θ => (h θ).pl,
    fun θ => (c θ).os, fun θ => (h θ).os⟩

/-- The weights of `verify_sub`'s other callees' trees. -/
structure VsBoundsW (Θ : Type) where
  gkr : Θ → ℕ
  tab : Θ → ℕ
  fl : Θ → ℕ
  term : Θ → ℕ

/-- A call before the dispatch: its callee's weight. -/
def vsBdW (w : Θ → String → ℕ) (H : VsWeightHyps w) (Bsw : VsBoundsW Θ) (k : Kid) (θ : Θ) : ℕ :=
  if k.f = "g_power_of_word__L6" then H.gpw θ
  else if k.f = "log2_ceil_in_the_exponent__L0_L34" then H.l2a θ
  else if k.f = "assert_canonical" then H.ac θ
  else if k.f = "verify_bus_gkr" then Bsw.gkr θ
  else if k.f = "verify_tables" then Bsw.tab θ
  else if k.f = "verify_flock" then Bsw.fl θ
  else if k.f = "__loop84" then 64 * (2 * w θ "__loop84")
  else if k.f = "__loop85" then 28 * (2 * w θ "__loop85")
  else if k.f = "certify_placement" then H.pl θ
  else H.l2b θ

/-- Read a callee's weight off `vsBdW`. -/
macro "vs_bdw" : tactic => `(tactic| simp (config := { decide := true }) [vsBdW])

/-- **The calls before the dispatch are complete within weights.** -/
theorem vsKids1_completeW {κ : ℕ} (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode)
    (htok : D.TOk bytecode) {Bs : VsBounds} {w : Θ → String → ℕ} (H : VsWeightHyps w) {Bsw : VsBoundsW Θ}
    (hG : CompleteGkrAtW fs cert κ w Bs.gkr Bsw.gkr)
    (hT : CompleteTablesAtW fs cert κ bytecode TCtx w Bs.tab Bsw.tab)
    (hF : CompleteFlockAtW fs cert κ w Bs.fl Bsw.fl) (hPl : CompletePlaceAtB fs cert κ PCtx Bs.pl)
    (hκ : 7 ≤ κ) :
    ∀ k ∈ vsKids1 fs D fp lpA sqA outA, k.taken = true →
      Main.CompleteAtW fs cert w κ k.f k.Lin k.args k.Out (vsBd fs Bs k) (vsBdW w H Bsw k) := by
  intro k hk ht
  have hc : ∀ x : E, IsCanonical128 x →
      CompleteAtB fs cert κ "assert_canonical" [] [x] (Returns [0]) (fs "assert_canonical") :=
    fun x hx => completeAt_of_rel_pureBat ac_pure (by simp)
      (fun rd _ => (assert_canonical_iff rd [x] [0]).mpr ⟨hx, rfl⟩) κ
      fun rd t hn hv hb => assert_canonical_totalLe fs rd t _ _ hn hv hb
  obtain ⟨hN, hl⟩ := pushTotal_bounds hb hok
  have M := fun rd (hm : MemL rd (vsAllL fs D fp lpA sqA outA)) =>
    vsAll_mem (off := 0) (kap := 0) (pt := 0) hm
  have CE := cur_eqs (fs := fs) (fp := fp) (D := D) (off := 0) (kap := 0) (pt := 0)
  obtain ⟨-, hl28, hst⟩ := stack_facts hb hok
  have hq8 : D.hs.getD 5 0 + 8 < 34 := by
    have := qflock_bound hb hok.rows_length hok.stack_le; simp only [VsData.hs]; omega
  have hE : ∀ q ∈ expL lpA sqA, q ∈ vsAllL fs D fp lpA sqA outA := fun q hq =>
    List.mem_append_right _ (List.mem_append_left _ hq)
  have e0 : word 1 0 0 = ofK (Parameters.gpow 0) := by
    rw [word_one, Parameters.gpow, pow_zero, ofK_one]
  simp only [vsKids1, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (Main.CompleteAtB.toW_weightLe ((gpw6_completeAt' fs cert κ (by have := hok.rate_le; omega)
      sqA).mono le_rfl (by vs_bd)) H.gpw_le).wmono fun θ => by vs_bdw
  · exact (Main.CompleteAtB.toW_weightLe ((gpw6_completeAt' fs cert κ (by have := hok.logMem_le; omega)
      sqA).mono le_rfl (by vs_bd)) H.gpw_le).wmono fun θ => by vs_bdw
  · exact (Main.CompleteAtB.toW_weightLe ((log2L0_completeAt (by omega) hN hl lpA sqA _ hE).mono le_rfl
      (by vs_bd)) H.l2a_le).wmono fun θ => by vs_bdw
  · exact (Main.CompleteAtB.toW_weightLe ((hc _ (isCanonical128_digestScalars _).1).mono le_rfl (by vs_bd))
      H.ac_le).wmono fun θ => by vs_bdw
  · exact (Main.CompleteAtB.toW_weightLe ((hc _ (isCanonical128_digestScalars _).2).mono le_rfl (by vs_bd))
      H.ac_le).wmono fun θ => by vs_bdw
  · have h := hG D.cvB _ D.xsG D.gr D.cvG (vsB fs fp D 2 + 10) (vsB fs fp D 7) _ hok.depth_lt hok.gkr
      hok.point_length hok.values_length fun rd _ hm => ⟨by
        have := (stream_at hok.rows_length (M rd hm).1.stream).1
        rwa [CE.1] at this, (M rd hm).1.zeta⟩
    rw [← hok.point_length, depth_eq hb hok, values_eq hok, ← CE.1] at h
    exact (Main.CompleteAtW.bmono h (by vs_bd)).wmono fun θ => by vs_bdw
  · have h := hT D.pi D.logMem D.alphas D.gr.2.1 D.gr.2.2 D.cvG D.xsT D.cvT D.rows D.bus D.claims
      D.beta D.bv D.rm D.gzcn (vsB fs fp D 2 + 10 + D.xsG.length) (vsB fs fp D 7) lpA sqA
      (vsB fs fp D 4) (vsB fs fp D 3) (vsB fs fp D 6) (vsB fs fp D 9) (vsB fs fp D 0)
      (vsB fs fp D 1) (vsB fs fp D 10) _ hb (by
        rw [hok.point_length]; unfold pushDepth; rw [layoutOf_logBytecode hb]; rfl)
      (by rw [hok.point_length]; exact hok.depth_lt) (by rw [htok.gzcn, htok.chis_len])
      hok.logMem_ge hok.logMem_le (by simp [VsData.alphas, sqAll_eq]) hok.values_length
      hok.rows_length hok.rows_log hok.claims_length hok.tables fun rd _ hm => by
        obtain ⟨h0, ht, hc, hp⟩ := M rd hm
        refine ⟨?_, h0.zeta, ht, h0.rows, ?_, ?_, h0.fpw, h0.pool, tctx_of hok htok h0.zeta hc hp⟩
        · have := (stream_at hok.rows_length h0.stream).2.1
          rwa [CE.2.1] at this
        · have := h0.dims
          rwa [dims_eq] at this
        · have := h0.bk
          rwa [hsMap_eq] at this
    rw [← CE.2.1, depth_eq hb hok] at h
    exact (Main.CompleteAtW.bmono h (by vs_bd)).wmono fun θ => by vs_bdw
  · have h := hF D.tau D.cvT D.xsF D.cvF D.zSkip D.alpha D.mv D.chi D.rcs D.s
      (vsB fs fp D 2 + 10 + D.xsG.length + D.xsT.length) (vsB fs fp D 11) (vsB fs fp D 12)
      (vsB fs fp D 13) _ (tau_lt hok) hok.chi_length hok.rcs_length hok.s_length hok.flock
      fun rd _ hm => ⟨by
        have := (stream_at hok.rows_length (M rd hm).1.stream).2.2.1
        rwa [CE.2.2.1] at this, (M rd hm).1.zchis, (M rd hm).1.lrs, (M rd hm).1.zpart⟩
    rw [← CE.2.2.1] at h
    exact (Main.CompleteAtW.bmono h (by vs_bd)).wmono fun θ => by vs_bdw
  · have L : ∀ (fs' : String → ℕ) (rd : Reader) (t : Tree) (rets : List E), t.name = "__loop84" →
        t.Valid coreProgram rd [word 1 0 0, (vsPtrsAt fs fp D 0 0 0).zpart,
          (vsPtrsAt fs fp D 0 0 0).mcs, (vsPtrsAt fs fp D 0 0 0).rs] rets → t.BufsOk coreProgram →
        t.total fs' ≤ 64 * (2 * fs' "__loop84") := fun fs' rd t rets hn hv hb => by
      have h := loop84_totalLe fs' rd t [word 1 0 0, (vsPtrsAt fs fp D 0 0 0).zpart,
        (vsPtrsAt fs fp D 0 0 0).mcs, (vsPtrsAt fs fp D 0 0 0).rs] _ hn ⟨0, e0, by decide⟩ hv hb
      simp only [List.getD_cons_zero, e0, logG_spec (show (0 : ℕ) < 2 ^ 64 - 1 by decide),
        Nat.sub_zero] at h
      exact h
    refine (Main.CompleteAtB.toW_total ((completeAt_of_rel_pureBat loop84_pure (by simp)
      (fun rd hm => ?_) κ (B := 64 * (2 * fs "__loop84")) fun rd t hn hv hb => L fs rd t _ hn hv hb).mono
        le_rfl (by vs_bd)) (Bw := vsBdW w H Bsw _) fun θ rd t rets hn hv hb =>
      (L (w θ) rd t rets hn hv hb).trans (by vs_bdw))
    rw [word_one, ← pow_zero gen]
    exact loop84_complete (loop84_bodies (M rd hm).1 hok.s_length mcs_length)
  · have hτ : D.tau ≠ 0 := by
      intro h0
      simp only [h0, pow_zero, word_one, CharTwo.add_self_eq_zero, ne_eq, not_true_eq_false,
        decide_false, Bool.false_eq_true] at ht
    have hτ29 := tau_lt hok
    have L : ∀ (fs' : String → ℕ) (rd : Reader) (t : Tree) (rets : List E), t.name = "__loop85" →
        t.Valid coreProgram rd [word 1 0 0, gen ^ D.tau,
          (vsPtrsAt fs fp D 0 0 0).zvals * word 256 0 0, (vsPtrsAt fs fp D 0 0 0).zchis * word 256 0 0]
          rets → t.BufsOk coreProgram → t.total fs' ≤ 28 * (2 * fs' "__loop85") := fun fs' rd t rets hn hv hb => by
      have h := loop85_totalLe fs' rd t [word 1 0 0, gen ^ D.tau,
        (vsPtrsAt fs fp D 0 0 0).zvals * word 256 0 0, (vsPtrsAt fs fp D 0 0 0).zchis * word 256 0 0]
        _ hn ⟨0, D.tau, e0, gen_pow_eq_ofK _, Nat.pos_of_ne_zero hτ, by omega⟩ hv hb
      simp only [List.getD_cons_zero, List.getD_cons_succ, e0, gen_pow_eq_ofK,
        logG_spec (show (0 : ℕ) < 2 ^ 64 - 1 by decide),
        logG_spec (show D.tau < 2 ^ 64 - 1 by omega), Nat.sub_zero] at h
      exact le_trans h (Nat.mul_le_mul_right _ (by omega))
    refine (Main.CompleteAtB.toW_total ((completeAt_of_rel_pureBat loop85_pure (by simp)
      (fun rd hm => ?_) κ (B := 28 * (2 * fs "__loop85")) fun rd t hn hv hb => L fs rd t _ hn hv hb).mono
        le_rfl (by vs_bd)) (Bw := vsBdW w H Bsw _) fun θ rd t rets hn hv hb =>
      (L (w θ) rd t rets hn hv hb).trans (by vs_bdw))
    have w8 : word 256 0 0 = gen ^ 8 := word_two_pow (a := 8) (by decide)
    have hm0 := (M rd hm).1
    rw [word_one, ← pow_zero gen, w8]
    refine loop85_complete (Nat.pos_of_ne_zero hτ) (by have := tau_lt hok; unfold ordG; omega) rfl
      fun j _ hj => ?_
    have hcl := hok.chi_length
    refine ⟨D.chi.getD (8 + j) 0, ?_, ?_⟩
    · rw [mul_assoc, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero]
      exact readsAt_getD hm0.zchis (by omega)
    · rw [mul_assoc, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero]
      have : D.fpoint.getD (8 + j) 0 = D.chi.getD (8 + j) 0 := by
        rw [VsData.fpoint, List.getD_eq_getElem _ _ (by simp [hok.rcs_length]; omega),
          List.getElem_append_right (by simp [hok.rcs_length]), List.getElem_drop,
          List.getD_eq_getElem _ _ (by omega)]
        simp only [List.length_reverse, hok.rcs_length]
        congr 1; omega
      rw [← this]; exact readsAt_getD hm0.zvals (by simp [VsData.fpoint, hok.rcs_length]; omega)
  · exact (Main.CompleteAtB.toW_weightLe ((hPl _ _ _ D.logMem D.hs _ hok.logMem_le (hs_length hok)
      (hs_lt hok) hq8 fun rd _ hm => placePre_of (M rd hm).2.1 (M rd hm).1).mono le_rfl (by vs_bd))
      H.pl_le).wmono fun θ => by vs_bdw
  · exact (Main.CompleteAtB.toW_weightLe ((log2L15_completeAt (by omega) hst (by omega) lpA sqA _ hE).mono
      le_rfl (by vs_bd)) H.l2b_le).wmono fun θ => by vs_bdw

/-- **The opening is complete within weights**: `open_stacked` at its configuration. -/
theorem vsOpenKid_completeW {κ : ℕ} {CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop}
    {B : ℕ} {w : Θ → String → ℕ} (H : VsWeightHyps w) (hok : D.Ok bytecode)
    (hO : CompleteOpenAtB fs cert κ CapOk B)
    (hcap : CapOk (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.root D.cvL D.xsW D.os
      D.target) :
    let k := vsOpenKid fs bytecode D fp lpA sqA outA
    Main.CompleteAtW fs cert w κ k.f k.Lin k.args k.Out B fun θ => H.os θ :=
  Main.CompleteAtB.toW_weightLe (vsOpenKid_completeB hok hO hcap) fun θ =>
    H.os_le θ _ _ hok.stack_ge hok.stack_le hok.rate_ge hok.rate_le

/-- **The terminal is complete within weights**, on the placement's and the opening's buffers. -/
theorem vsTermKid_completeW {κ : ℕ} (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode)
    (htok : D.TOk bytecode) {B : ℕ} {w : Θ → String → ℕ} {Bw : Θ → ℕ}
    (hE : CompleteTermAtW fs cert κ TCtx PCtx w B Bw) {Lc : Main.Layout} {b : ℕ}
    (hc : ∀ rd, MemL rd Lc → PCtx rd (columnKappas D.logMem 18 D.hs) off kap) :
    let k := vsTermKid fs D fp lpA sqA outA off kap (ofK (Parameters.gpow b)) Lc
      [(b, D.w.point ++ List.replicate (pointCap - D.w.point.length) 0)]
    Main.CompleteAtW fs cert w κ k.f k.Lin k.args k.Out B Bw := by
  intro k
  refine hE (layoutOf bytecode D.logMem D.rows) D.bus D.claims D.lam D.fpoint (ringCoefficients D.mcs)
    D.w D.chis _ _ hok.accepts htok.point_vars htok.gzcn fun rd _ hm => ?_
  obtain ⟨h12, h3⟩ := Main.memL_append.mp hm
  obtain ⟨h1, h2⟩ := Main.memL_append.mp h12
  obtain ⟨hm0, -, hchi, hcp⟩ := vsAll_mem (off := off) (kap := kap) (pt := ofK (Parameters.gpow b)) h1
  have htc := tctx_of hok htok hm0.zeta hchi hcp
  rw [depth_eq hb hok] at htc
  exact ⟨termPre_of hb hok htc (hc rd h2) (hypKappa rd) hm0.lam hm0.zvals hm0.ctab
    (h3 _ List.mem_cons_self), hchi⟩

end Weights

/-! ## On disjoint layouts, without bounds (`CompleteAtD`) -/

/-- **The calls before the dispatch are complete.** -/
theorem vsKids1_complete {κ : ℕ} (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode)
    (htok : D.TOk bytecode) (hG : CompleteGkrAt fs cert κ)
    (hT : CompleteTablesAt fs cert κ bytecode TCtx) (hF : CompleteFlockAt fs cert κ)
    (hPl : CompletePlaceAt fs cert κ PCtx)
    (hκ : 7 ≤ κ) :
    ∀ k ∈ vsKids1 fs D fp lpA sqA outA, k.taken = true →
      CompleteAtD fs cert κ k.f k.Lin k.args k.Out := by
  intro k hk ht
  have hc : ∀ x : E, IsCanonical128 x → CompleteAtD fs cert κ "assert_canonical" [] [x] (Returns [0]) :=
    fun x hx => completeAt_of_rel_pureD ac_pure (by simp)
      (fun rd _ => (assert_canonical_iff rd [x] [0]).mpr ⟨hx, rfl⟩) κ
  obtain ⟨hN, hl⟩ := pushTotal_bounds hb hok
  have M := fun rd (hm : MemL rd (vsAllL fs D fp lpA sqA outA)) =>
    vsAll_mem (off := 0) (kap := 0) (pt := 0) hm
  have CE := cur_eqs (fs := fs) (fp := fp) (D := D) (off := 0) (kap := 0) (pt := 0)
  obtain ⟨-, hl28, hst⟩ := stack_facts hb hok
  have hq8 : D.hs.getD 5 0 + 8 < 34 := by
    have := qflock_bound hb hok.rows_length hok.stack_le; simp only [VsData.hs]; omega
  have hE : ∀ q ∈ expL lpA sqA, q ∈ vsAllL fs D fp lpA sqA outA := fun q hq =>
    List.mem_append_right _ (List.mem_append_left _ hq)
  simp only [vsKids1, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (gpw6_completeAt' fs cert κ (by have := hok.rate_le; omega) sqA).toCompleteAtD
  · exact (gpw6_completeAt' fs cert κ (by have := hok.logMem_le; omega) sqA).toCompleteAtD
  · exact (log2L0_completeAt (by omega) hN hl lpA sqA _ hE).toCompleteAtD
  · exact hc _ (isCanonical128_digestScalars _).1
  · exact hc _ (isCanonical128_digestScalars _).2
  · have h := hG D.cvB _ D.xsG D.gr D.cvG (vsB fs fp D 2 + 10) (vsB fs fp D 7) _ hok.depth_lt hok.gkr
      hok.point_length hok.values_length fun rd _ hm => ⟨by
        have := (stream_at hok.rows_length (M rd hm).1.stream).1
        rwa [CE.1] at this, (M rd hm).1.zeta⟩
    rw [← hok.point_length, depth_eq hb hok, values_eq hok, ← CE.1] at h
    exact h
  · have h := hT D.pi D.logMem D.alphas D.gr.2.1 D.gr.2.2 D.cvG D.xsT D.cvT D.rows D.bus D.claims
      D.beta D.bv D.rm D.gzcn (vsB fs fp D 2 + 10 + D.xsG.length) (vsB fs fp D 7) lpA sqA
      (vsB fs fp D 4) (vsB fs fp D 3) (vsB fs fp D 6) (vsB fs fp D 9) (vsB fs fp D 0)
      (vsB fs fp D 1) (vsB fs fp D 10) _ hb (by
        rw [hok.point_length]; unfold pushDepth; rw [layoutOf_logBytecode hb]; rfl)
      (by rw [hok.point_length]; exact hok.depth_lt) (by rw [htok.gzcn, htok.chis_len])
      hok.logMem_ge hok.logMem_le (by simp [VsData.alphas, sqAll_eq]) hok.values_length
      hok.rows_length hok.rows_log hok.claims_length hok.tables fun rd _ hm => by
        obtain ⟨h0, ht, hc, hp⟩ := M rd hm
        refine ⟨?_, h0.zeta, ht, h0.rows, ?_, ?_, h0.fpw, h0.pool, tctx_of hok htok h0.zeta hc hp⟩
        · have := (stream_at hok.rows_length h0.stream).2.1
          rwa [CE.2.1] at this
        · have := h0.dims
          rwa [dims_eq] at this
        · have := h0.bk
          rwa [hsMap_eq] at this
    rw [← CE.2.1, depth_eq hb hok] at h
    exact h
  · have h := hF D.tau D.cvT D.xsF D.cvF D.zSkip D.alpha D.mv D.chi D.rcs D.s
      (vsB fs fp D 2 + 10 + D.xsG.length + D.xsT.length) (vsB fs fp D 11) (vsB fs fp D 12)
      (vsB fs fp D 13) _ (tau_lt hok) hok.chi_length hok.rcs_length hok.s_length hok.flock
      fun rd _ hm => ⟨by
        have := (stream_at hok.rows_length (M rd hm).1.stream).2.2.1
        rwa [CE.2.2.1] at this, (M rd hm).1.zchis, (M rd hm).1.lrs, (M rd hm).1.zpart⟩
    rw [← CE.2.2.1] at h
    exact h
  · refine completeAt_of_rel_pureD loop84_pure (by simp) (fun rd hm => ?_) κ
    rw [word_one, ← pow_zero gen]
    exact loop84_complete (loop84_bodies (M rd hm).1 hok.s_length mcs_length)
  · refine completeAt_of_rel_pureD loop85_pure (by simp) (fun rd hm => ?_) κ
    have hτ : D.tau ≠ 0 := by
      intro h0
      simp only [h0, pow_zero, word_one, CharTwo.add_self_eq_zero, ne_eq, not_true_eq_false,
        decide_false, Bool.false_eq_true] at ht
    have w8 : word 256 0 0 = gen ^ 8 := word_two_pow (a := 8) (by decide)
    have hm0 := (M rd hm).1
    rw [word_one, ← pow_zero gen, w8]
    refine loop85_complete (Nat.pos_of_ne_zero hτ) (by have := tau_lt hok; unfold ordG; omega) rfl
      fun j _ hj => ?_
    have hcl := hok.chi_length
    refine ⟨D.chi.getD (8 + j) 0, ?_, ?_⟩
    · rw [mul_assoc, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero]
      exact readsAt_getD hm0.zchis (by omega)
    · rw [mul_assoc, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero]
      have : D.fpoint.getD (8 + j) 0 = D.chi.getD (8 + j) 0 := by
        rw [VsData.fpoint, List.getD_eq_getElem _ _ (by simp [hok.rcs_length]; omega),
          List.getElem_append_right (by simp [hok.rcs_length]), List.getElem_drop,
          List.getD_eq_getElem _ _ (by omega)]
        simp only [List.length_reverse, hok.rcs_length]
        congr 1; omega
      rw [← this]; exact readsAt_getD hm0.zvals (by simp [VsData.fpoint, hok.rcs_length]; omega)
  · exact hPl _ _ _ D.logMem D.hs _ hok.logMem_le (hs_length hok) (hs_lt hok) hq8 fun rd _ hm =>
      placePre_of (M rd hm).2.1 (M rd hm).1
  · exact (log2L15_completeAt (by omega) hst (by omega) lpA sqA _ hE).toCompleteAtD

/-- **The opening is complete**, on its run and the agreement `CapOk` at the cap. -/
theorem vsOpenKid_complete {κ : ℕ} {CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop}
    (hok : D.Ok bytecode) (hO : CompleteOpenAt fs cert κ CapOk)
    (hcap : CapOk (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.root D.cvL D.xsW D.os
      D.target) :
    let k := vsOpenKid fs bytecode D fp lpA sqA outA
    CompleteAtD fs cert κ k.f k.Lin k.args k.Out := by
  intro k
  have h := hO _ D.rate hok.stack_ge hok.stack_le hok.rate_ge hok.rate_le D.root D.cvL D.xsW D.os D.w
    D.cvW D.roots' D.target _ (vsAllL fs D fp lpA sqA outA) hok.opening hcap fun rd _ hm => by
      have := (stream_at hok.rows_length (vsAll_mem (off := 0) (kap := 0) (pt := 0) hm).1.stream).2.2.2
      rwa [curW_eq] at this
  rw [← curW_eq] at h
  exact h

/-- **The terminal is complete**, on the placement's and the opening's buffers. -/
theorem vsTermKid_complete {κ : ℕ} (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode)
    (htok : D.TOk bytecode) (hE : CompleteTermAt fs cert κ TCtx PCtx) {Lc : Main.Layout} {b : ℕ}
    (hc : ∀ rd, MemL rd Lc → PCtx rd (columnKappas D.logMem 18 D.hs) off kap) :
    let k := vsTermKid fs D fp lpA sqA outA off kap (ofK (Parameters.gpow b)) Lc
      [(b, D.w.point ++ List.replicate (pointCap - D.w.point.length) 0)]
    CompleteAtD fs cert κ k.f k.Lin k.args k.Out := by
  intro k
  refine hE (layoutOf bytecode D.logMem D.rows) D.bus D.claims D.lam D.fpoint (ringCoefficients D.mcs)
    D.w D.chis _ _ hok.accepts htok.point_vars htok.gzcn fun rd _ hm => ?_
  obtain ⟨h12, h3⟩ := Main.memL_append.mp hm
  obtain ⟨h1, h2⟩ := Main.memL_append.mp h12
  obtain ⟨hm0, -, hchi, hcp⟩ := vsAll_mem (off := off) (kap := kap) (pt := ofK (Parameters.gpow b)) h1
  have htc := tctx_of hok htok hm0.zeta hchi hcp
  rw [depth_eq hb hok] at htc
  exact ⟨termPre_of hb hok htc (hc rd h2) (hypKappa rd) hm0.lam hm0.zvals hm0.ctab
    (h3 _ List.mem_cons_self), hchi⟩

end
end LeanVM.Guest.B1.VerifySub
