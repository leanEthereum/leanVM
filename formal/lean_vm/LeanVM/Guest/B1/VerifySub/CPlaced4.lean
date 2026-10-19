/-
  LeanVM.Guest.B1.VerifySub.CPlaced4

  `verify_sub` placed: its callees as `Kid`s, each complete in the uniform placed form.
-/

module

public import LeanVM.Guest.B1.VerifySub.CPlaced3
public import LeanVM.Guest.B1.Tables.Kappas

/-!
# `verify_sub`'s callees, placed

`vsKids1`: the twelve calls before the dispatch, `vsOpenKid`: the opening, `vsTermKid`: the
terminal, each with the words it reads (`vsAllL`, `verify_sub`'s own and the caller's, and for the
terminal the buffers the placement and the opening return) and what it returns. Each is
`CompleteAt` (`vsKids1_complete`, `vsOpenKid_complete`, `vsTermKid_complete`) from the callees'
placed completeness, group 1's `g_power_of_word` (`gpw6_completeAt`), `assert_canonical` and
the two loops (pure, `completeAt_of_rel_pure`).
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
    CompleteAt fs cert k "g_power_of_word__L6" [(qb, gpwSq)] [eOfNat N, ofK (Parameters.gpow qb)]
      (Returns [gen ^ N]) := by
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

theorem pushTotal_bounds (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) :
    D.pushTotal < 2 ^ 34 ∧ log2Ceil D.pushTotal < 34 := by
  have hdep : log2Ceil D.pushTotal < 33 := by
    rw [← depth_eq hb hok, hok.point_length]; exact hok.depth_lt
  exact ⟨lt_of_le_of_lt (le_two_pow_log2Ceil _) (Nat.pow_lt_pow_right (by decide) (by omega)),
    by omega⟩

/-- **The calls before the dispatch are complete.** -/
theorem vsKids1_complete {κ : ℕ} (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode)
    (htok : D.TOk bytecode) (hG : CompleteGkrAt fs cert κ)
    (hT : CompleteTablesAt fs cert κ bytecode TCtx) (hF : CompleteFlockAt fs cert κ)
    (hPl : CompletePlaceAt fs cert κ PCtx)
    (hL0 : CompleteRel fs cert κ "log2_ceil_in_the_exponent__L0_L34" (Log2Pre 0))
    (hL15 : CompleteRel fs cert κ "log2_ceil_in_the_exponent__L15_L34" (Log2Pre 15)) :
    ∀ k ∈ vsKids1 fs D fp lpA sqA outA, k.taken = true →
      CompleteAt fs cert κ k.f k.Lin k.args k.Out := by
  intro k hk ht
  have hc : ∀ x : E, IsCanonical128 x → CompleteAt fs cert κ "assert_canonical" [] [x] (Returns [0]) :=
    fun x hx => completeAt_of_rel_pure ac_pure (by simp)
      (fun rd _ => (assert_canonical_iff rd [x] [0]).mpr ⟨hx, rfl⟩) κ
  obtain ⟨hN, hl⟩ := pushTotal_bounds hb hok
  have M := fun rd (hm : MemL rd (vsAllL fs D fp lpA sqA outA)) =>
    vsAll_mem (off := 0) (kap := 0) (pt := 0) hm
  obtain ⟨-, hl28, hst⟩ := stack_facts hb hok
  simp only [vsKids1, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact gpw6_completeAt' fs cert κ (by have := hok.rate_le; omega) sqA
  · exact gpw6_completeAt' fs cert κ (by have := hok.logMem_le; omega) sqA
  · exact hL0 _ _ _ fun rd _ hm =>
      ⟨D.pushTotal, _, _, rfl, by simp, hN, by simpa using hl, (M rd hm).2.1⟩
  · exact hc _ (isCanonical128_digestScalars _).1
  · exact hc _ (isCanonical128_digestScalars _).2
  · exact hG _ _ _ fun rd _ hm => gkrPre_of hb hok (M rd hm).1
  · exact hT _ _ _ fun rd _ hm =>
      tablesPre_of hb hok htok (M rd hm).2.1 (M rd hm).1 (M rd hm).2.2.1
        (M rd hm).2.2.2
  · exact hF _ _ _ fun rd _ hm => flockPre_of hok (M rd hm).1
  · refine completeAt_of_rel_pure loop84_pure (by simp) (fun rd hm => ?_) κ
    rw [word_one, ← pow_zero gen]
    exact loop84_complete (loop84_bodies (M rd hm).1 hok.s_length mcs_length)
  · refine completeAt_of_rel_pure loop85_pure (by simp) (fun rd hm => ?_) κ
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
  · exact hPl _ _ _ D.logMem D.hs _ hok.logMem_le (hs_length hok) (hs_lt hok) fun rd _ hm =>
      placePre_of (M rd hm).2.1 (M rd hm).1
  · exact hL15 _ _ _ fun rd _ hm =>
      ⟨D.stackTot, _, _, rfl, rfl, hst, by omega, (M rd hm).2.1⟩

/-- **The opening is complete**, on its run and the agreement `CapOk` at the cap. -/
theorem vsOpenKid_complete {κ : ℕ} {CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop}
    (hok : D.Ok bytecode) (hO : CompleteOpenAt fs cert κ CapOk)
    (hcap : CapOk (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.root D.cvL D.xsW D.os
      D.target) :
    let k := vsOpenKid fs bytecode D fp lpA sqA outA
    CompleteAt fs cert κ k.f k.Lin k.args k.Out := by
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
    CompleteAt fs cert κ k.f k.Lin k.args k.Out := by
  intro k
  refine hE _ _ _ fun rd _ hm => ?_
  obtain ⟨h12, h3⟩ := Main.memL_append.mp hm
  obtain ⟨h1, h2⟩ := Main.memL_append.mp h12
  obtain ⟨hm0, -, hchi, hcp⟩ := vsAll_mem (off := off) (kap := kap) (pt := ofK (Parameters.gpow b)) h1
  exact termPre_acc hb hok htok hm0 hchi hcp (hc rd h2) (hypKappa rd) (h3 _ List.mem_cons_self)

end
end LeanVM.Guest.B1.VerifySub
