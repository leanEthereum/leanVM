/-
  LeanVM.Guest.B1.VerifySub.CRel

  `verify_sub`'s completeness at the level of `Program.Rel`: its calls hold of the program's
  relation by the callees' completeness, and the body composed gives the relation.
-/

module

public import LeanVM.Guest.B1.VerifySub.CAssemble

/-!
# `verify_sub` is complete (`Rel`)

`callsOk_rel`: over the honest memory, each call of the body holds of `coreProgram.Rel`, by group
1's completeness (`g_power_of_word`, `log2_ceil_in_the_exponent`, `assert_canonical`), the two
loops (`CLoops`), and the callees' completeness shapes (`CompleteIface`). `verify_sub_complete_rel`:
`verify_sub`'s relation at the honest run.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

variable {rd : Reader} {D : VsData} {P : VsPtrs} {out lp sq : E} {bytecode : List K}

/-! ## The terminal's precondition -/

/-- **The terminal's context at the honest run**, from `verify_tables`' honest memory. -/
theorem tctx_honest {TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop}
    {GMem TMem FMem PMem : Reader → List E → List E → List E → Prop}
    {OMem : ℕ → ℕ → Reader → List E → List E → List E → Prop}
    {EMem : Reader → List E → List E → Prop} (hok : D.Ok bytecode) (ht : ExpTables rd lp sq)
    (hm : VsMem rd D P out) (hcal : VsCallees GMem TMem FMem PMem OMem EMem bytecode rd D P lp sq)
    (hTC : HypTCtx bytecode TCtx rd TMem) :
    TCtx rd (layoutOf bytecode D.logMem D.rows) D.bus D.claims
      [P.zeta, P.chi, D.rm, gen ^ D.gr.2.1.length, D.gzcn, P.cplen] := by
  obtain ⟨-, hxT, -, -⟩ := stream_at hok.rows_length hm.stream
  have h := hTC (fun _ l b c _ ↦ l = layoutOf bytecode D.logMem D.rows ∧ b = D.bus ∧ c = D.claims)
    P.tab lp D.pi D.logMem D.alphas D.gr.2.1 D.gr.2.2 (tabArgs D P sq) (tabRets D P)
    (tablesPre_honest hok ht hm.toVsMem0) (tablesOut_honestQ hok hm.toVsMem0 hxT ⟨rfl, rfl, rfl⟩) hcal.tab
  obtain ⟨-, -, -, rowsN, bus, claims, -, -, -, -, -, -, -, -, -, ⟨⟨hl, hb, hc⟩, hT⟩, -, -⟩ := h
  rw [hl, hb, hc] at hT
  exact hT

theorem stack_facts (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) :
    (layoutOf bytecode D.logMem D.rows).stackLog = max 15 (log2Ceil D.stackTot) ∧
      log2Ceil D.stackTot ≤ 28 ∧ D.stackTot < 2 ^ 34 := by
  have h : (layoutOf bytecode D.logMem D.rows).stackLog = max 15 (log2Ceil D.stackTot) :=
    stackLog_eq hb D.logMem D.rows
  have h2 := hok.stack_le
  refine ⟨h, by rw [h] at h2; exact le_trans (le_max_right _ _) h2, ?_⟩
  rw [h] at h2
  exact lt_of_le_of_lt (le_two_pow_log2Ceil _) (Nat.pow_lt_pow_right (by decide) (by omega))

theorem busPoint_length (hok : D.Ok bytecode) : D.bus.point.length < 33 := by
  have hT0 := hok.tables (.claimed ⟨D.gr.2.1.take (layoutOf bytecode D.logMem D.rows).logBytecode ++
    D.alphas, D.bv, 0, 0, [], [], [], 0⟩) (bytecodeAt_claimed _ bytecode)
  rw [tablesSeg_point hT0, hok.point_length]; exact hok.depth_lt

/-- **The terminal's precondition at the honest run.** -/
theorem termPre_honest {TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop}
    {PCtx : Reader → List ℕ → E → E → Prop}
    {GMem TMem FMem PMem : Reader → List E → List E → List E → Prop}
    {OMem : ℕ → ℕ → Reader → List E → List E → List E → Prop}
    {EMem : Reader → List E → List E → Prop} (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode)
    (ht : ExpTables rd lp sq) (hm : VsMem rd D P out)
    (hcal : VsCallees GMem TMem FMem PMem OMem EMem bytecode rd D P lp sq)
    (hTC : HypTCtx bytecode TCtx rd TMem) (hPC : HypPCtx PCtx rd PMem) (hK : HypKappa PCtx rd) :
    TermPre TCtx PCtx rd (layoutOf bytecode D.logMem D.rows) D.bus D.claims D.lam D.fpoint
      (ringCoefficients D.mcs) D.w [P.zeta, P.chi, D.rm, gen ^ log2Ceil D.pushTotal, D.gzcn,
        gen ^ D.logMem, gen ^ D.tau, P.cplen, P.lam, P.off, P.kap, P.zvals, P.ctab, P.pt, D.w.inner,
        D.w.residual, D.w.target] := by
  have hpc : PCtx rd (columnKappas D.logMem 18 D.hs) P.off P.kap :=
    hPC P.pl lp sq P.kbase D.logMem D.hs P.off P.kap ht hok.logMem_le (hs_length hok) (hs_lt hok)
      hm.kbase hcal.pl
  obtain ⟨hsl, hl28, -⟩ := stack_facts hb hok
  have htc := tctx_honest hok ht hm hcal hTC
  rw [depth_eq hb hok] at htc
  refine ⟨htc, ?_, ?_, rfl, rfl, ?_, hm.zvals, hm.ctab, hm.pt, rfl, rfl, rfl, ?_⟩
  · rw [layoutOf_logBytecode hb]; exact hpc
  · exact hK _ _ _ hpc hl28
  · rw [hok.claims_length]; exact hm.lam
  · refine ⟨by simp only [layoutOf], by simp only [layoutOf], hok.stack_le,
      by rw [layoutOf_logMemory]; have := hok.logMem_ge; omega, busPoint_length hok, hok.open_point,
      ?_, by simp [ringCoefficients, kBits]⟩
    rw [layoutOf_heights]
    simp [VsData.fpoint, hok.rcs_length, hok.chi_length, VsData.tau, VsData.hs, opBlake2s]
    omega

/-! ## The calls -/

/-- **Every call of the body holds of `coreProgram.Rel`**, over the honest memory, from the
callees' completeness. -/
theorem callsOk_rel {TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop}
    {PCtx : Reader → List ℕ → E → E → Prop}
    {GMem TMem FMem PMem : Reader → List E → List E → List E → Prop}
    {OMem : ℕ → ℕ → Reader → List E → List E → List E → Prop}
    {EMem : Reader → List E → List E → Prop} {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ)
    (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) (ht : ExpTables Lm.read lp sq)
    (hm : VsMem Lm.read D P out)
    (hcal : VsCallees GMem TMem FMem PMem OMem EMem bytecode Lm.read D P lp sq)
    (hG : CompleteGkr Lm.read GMem) (hT : CompleteTables bytecode Lm.read TMem)
    (hF : CompleteFlock Lm.read FMem) (hPl : CompletePlace Lm.read PMem)
    (hO : CompleteOpen Lm.read OMem) (hE : CompleteTerm TCtx PCtx Lm.read EMem)
    (hTC : HypTCtx bytecode TCtx Lm.read TMem) (hPC : HypPCtx PCtx Lm.read PMem)
    (hK : HypKappa PCtx Lm.read) :
    VsCallsOk (coreProgram.Rel Lm.read) bytecode D P lp sq := by
  obtain ⟨-, -, -, hxW⟩ := stream_at hok.rows_length hm.stream
  obtain ⟨hsl, hl28, hst⟩ := stack_facts hb hok
  have hdep : log2Ceil D.pushTotal < 33 := by
    rw [← depth_eq hb hok, hok.point_length]; exact hok.depth_lt
  have hN : D.pushTotal < 2 ^ 34 :=
    lt_of_le_of_lt (le_two_pow_log2Ceil _) (Nat.pow_lt_pow_right (by decide) (by omega))
  have hc : ∀ x : E, IsCanonical128 x → coreProgram.Rel Lm.read "assert_canonical" [x] [0] :=
    fun x hx => (assert_canonical_iff _ _ _).mpr ⟨hx, rfl⟩
  have w8 : word 256 0 0 = gen ^ 8 := word_two_pow (a := 8) (by decide)
  refine ⟨gpw6_complete ht (by have := hok.rate_le; omega) hm.gpwRate,
    gpw6_complete ht (by have := hok.logMem_le; omega) hm.gpwMem,
    log2L0_complete hκ hκ6 Lm ht hN (by omega) hm.bpPush hm.psPush,
    hc _ (isCanonical128_digestScalars _).1, hc _ (isCanonical128_digestScalars _).2,
    gkr_rel hb hok hm.toVsMem0 hcal hG, tables_rel hb hok ht hm.toVsMem0 hcal hT,
    flock_rel hok hm.toVsMem0 hcal hF, ?_, ?_,
    hPl P.pl lp sq P.kbase D.logMem D.hs P.off P.kap ht hok.logMem_le (hs_length hok) (hs_lt hok)
      hm.kbase hcal.pl,
    log2L15_complete hκ hκ6 Lm ht hst (by omega) hm.bpStack hm.psStack, ?_,
    hE P.term _ _ _ _ _ _ _ _ (termPre_honest hb hok ht hm hcal hTC hPC hK) hok.accepts hcal.term⟩
  · rw [word_one, ← pow_zero gen]
    exact loop84_complete (loop84_bodies hm.toVsMem0 hok.s_length mcs_length)
  · intro hτ
    rw [word_one, ← pow_zero gen, w8]
    refine loop85_complete (Nat.pos_of_ne_zero hτ) (by have := tau_lt hok; unfold ordG; omega) rfl
      fun j _ hj => ?_
    have hcl := hok.chi_length
    refine ⟨D.chi.getD (8 + j) 0, ?_, ?_⟩
    · rw [mul_assoc, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero]
      exact readsAt_getD hm.zchis (by omega)
    · rw [mul_assoc, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero]
      have : D.fpoint.getD (8 + j) 0 = D.chi.getD (8 + j) 0 := by
        rw [VsData.fpoint, List.getD_eq_getElem _ _ (by simp [hok.rcs_length]; omega),
          List.getElem_append_right (by simp [hok.rcs_length]), List.getElem_drop,
          List.getD_eq_getElem _ _ (by omega)]
        simp only [List.length_reverse, hok.rcs_length]
        congr 1; omega
      rw [← this]; exact readsAt_getD hm.zvals (by simp [VsData.fpoint, hok.rcs_length]; omega)
  · exact hO _ D.rate hok.stack_ge hok.stack_le hok.rate_ge hok.rate_le D.root P.op _ _ _ _ _ _ _ rfl
      ⟨D.cvL, D.xsW, D.os, D.w, D.cvW, D.roots', rfl, hxW, hok.opening, P.pt, rfl, hm.pt,
        hok.open_point⟩ hcal.op

/-! ## `verify_sub` -/

theorem core15_body' : Fn.body Data.core15 = vsBody ++ [.ret []] := by
  rw [core15_body, vsPre_eq]

/-- **`verify_sub` is complete** (`Program.Rel`): over the honest memory of an accepting run within
the deployed limits, its callees' completeness and their honest scratch, `verify_sub` holds of the
run's public input and seed, at any `defer_out` holding the run's claims. -/
theorem verify_sub_complete_rel {TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop}
    {PCtx : Reader → List ℕ → E → E → Prop}
    {GMem TMem FMem PMem : Reader → List E → List E → List E → Prop}
    {OMem : ℕ → ℕ → Reader → List E → List E → List E → Prop}
    {EMem : Reader → List E → List E → Prop} {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ)
    (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) (ht : ExpTables Lm.read lp sq)
    (hm : VsMem Lm.read D P out)
    (hcal : VsCallees GMem TMem FMem PMem OMem EMem bytecode Lm.read D P lp sq)
    (hG : CompleteGkr Lm.read GMem) (hT : CompleteTables bytecode Lm.read TMem)
    (hF : CompleteFlock Lm.read FMem) (hPl : CompletePlace Lm.read PMem)
    (hO : CompleteOpen Lm.read OMem) (hE : CompleteTerm TCtx PCtx Lm.read EMem)
    (hTC : HypTCtx bytecode TCtx Lm.read TMem) (hPC : HypPCtx PCtx Lm.read PMem)
    (hK : HypKappa PCtx Lm.read) :
    coreProgram.Rel Lm.read "verify_sub" [(digestScalars D.pi).1, (digestScalars D.pi).2,
      (digestScalars D.seed).1, (digestScalars D.seed).2, lp, sq, out] [] := by
  have hC := callsOk_rel hκ hκ6 Lm hb hok ht hm hcal hG hT hF hPl hO hE hTC hPC hK
  set σ0 := upds (fun _ => 0) (vsG0 D lp sq out)
  have h0 : Fixes σ0 (vsG0 D lp sq out) := by
    intro p hp; simp only [vsG0, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [σ0, vsG0, upds_n]
  obtain ⟨σ, he, -, hh⟩ := vs_body ((lowDef_memImage hκ Lm).mono hκ6) hb hok ht hm.toVsMem0 hC σ0 h0
  rw [rel_iff_sem find_verify_sub, core15_body', core15_params]
  refine ⟨σ, ?_, ?_⟩
  · have hp : ∀ k < 7, σ (.n k) = σ0 (.n k) := fun k hk => he.apply (Or.inl hk)
    simp only [List.map_cons, List.map_nil, hp 0 (by omega), hp 1 (by omega), hp 2 (by omega),
      hp 3 (by omega), hp 4 (by omega), hp 5 (by omega), hp 6 (by omega)]
    simp [σ0, vsG0, upds_n]
  · rw [holdsList_append]
    exact hh _ _ rfl

end
end LeanVM.Guest.B1.VerifySub
