/-
  LeanVM.Guest.B1.VerifySub.CPlaced2

  `verify_sub` placed: the honest calls as a relation, the calls a path's events hold of it, and
  the tables' and the terminal's contexts on a memory.
-/

module

public import LeanVM.Guest.B1.VerifySub.CPlaced1
public import LeanVM.Guest.B1.VerifySub.CRel

/-!
# `verify_sub` placed: the honest calls and the contexts

* `vsTriples`, `vsC`: the calls of the honest run, as a list and as the relation of membership in
  it, of which the body's calls hold (`vsCallsOk_mem`);
* `calls_ok`: the entered frames of a path whose events hold of `C` hold of `C`;
* `tctx_of`, `termPre_of`: the tables' context and the terminal's precondition on any memory
  holding the run's buffers.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory

@[expose] public section

/-! ## The honest calls -/

/-- The calls of the honest run: callee, argument words, return words. -/
noncomputable def vsTriples (bytecode : List K) (D : VsData) (P : VsPtrs) (lp sq : E) :
    List (String × List E × List E) :=
  [("g_power_of_word__L6", [eOfNat D.rate, sq], [gen ^ D.rate]),
    ("g_power_of_word__L6", [eOfNat D.logMem, sq], [gen ^ D.logMem]),
    ("log2_ceil_in_the_exponent__L0_L34", [gen ^ D.pushTotal, lp, sq], [gen ^ log2Ceil D.pushTotal]),
    ("assert_canonical", [D.x0], [0]), ("assert_canonical", [D.x1], [0]),
    ("verify_bus_gkr", [(digestScalars D.cvB).1, (digestScalars D.cvB).2, curG P,
      gen ^ log2Ceil D.pushTotal, P.zeta],
      [(digestScalars D.cvG).1, (digestScalars D.cvG).2, curT D P, D.gr.2.2.getD 0 0,
        D.gr.2.2.getD 1 0, D.gr.2.2.getD 2 0]),
    ("verify_tables", [(digestScalars D.cvG).1, (digestScalars D.cvG).2, curT D P,
      (digestScalars D.pi).1, (digestScalars D.pi).2, P.zeta, gen ^ log2Ceil D.pushTotal, P.dims,
      P.rows, P.bk, sq, P.fpw, D.beta, P.pool, P.cplen, P.chi, D.gr.2.2.getD 0 0, D.gr.2.2.getD 1 0,
      D.gr.2.2.getD 2 0], [(digestScalars D.cvT).1, (digestScalars D.cvT).2, curF D P, D.gzcn, D.bv,
        D.rm]),
    ("verify_flock", [(digestScalars D.cvT).1, (digestScalars D.cvT).2, curF D P, gen ^ D.tau, P.zchis,
      P.lrs, P.zpart], [(digestScalars D.cvF).1, (digestScalars D.cvF).2, curW D P, D.zSkip, D.alpha,
        D.mv]),
    ("__loop84", [word 1 0 0, P.zpart, P.mcs, P.rs], []),
    ("__loop85", [word 1 0 0, gen ^ D.tau, P.zvals * word 256 0 0, P.zchis * word 256 0 0], []),
    ("certify_placement", [P.kbase, sq], [gen ^ D.stackTot, P.off, P.kap]),
    ("log2_ceil_in_the_exponent__L15_L34", [gen ^ D.stackTot, lp, sq],
      [gen ^ max 15 (log2Ceil D.stackTot)]),
    (openName (layoutOf bytecode D.logMem D.rows).stackLog D.rate,
      [(digestScalars D.cvL).1, (digestScalars D.cvL).2, D.target, D.x0, D.x1, curW D P],
      [D.w.target, P.pt, D.w.inner, D.w.residual]),
    ("check_opening_terminal", [P.zeta, P.chi, D.rm, gen ^ log2Ceil D.pushTotal, D.gzcn,
      gen ^ D.logMem, gen ^ D.tau, P.cplen, P.lam, P.off, P.kap, P.zvals, P.ctab, P.pt, D.w.inner,
      D.w.residual, D.w.target], [])]

/-- **Membership in the honest calls**, as a call relation. -/
noncomputable def vsC (bytecode : List K) (D : VsData) (P : VsPtrs) (lp sq : E) : CallRel :=
  fun f a r => (f, a, r) ∈ vsTriples bytecode D P lp sq

theorem vsCallsOk_mem {bytecode : List K} {D : VsData} {P : VsPtrs} {lp sq : E} :
    VsCallsOk (vsC bytecode D P lp sq) bytecode D P lp sq := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [vsC, vsTriples, List.mem_cons, true_or, or_true]

/-- No other callee is an opening. -/
theorem ne_openName {s : String} (hs : (openNames.all fun t => t != s) = true) (hs0 : s ≠ "")
    (μ r : ℕ) :
    s ≠ openName μ r := by
  intro h
  unfold openName at h
  by_cases hl : μ - 22 + 7 * (r - 1) < openNames.length
  · rw [List.getD_eq_getElem _ _ hl] at h
    have := List.all_eq_true.mp hs _ (List.getElem_mem hl)
    rw [← h] at this
    simp at this
  · rw [List.getD_eq_default _ _ (by omega)] at h
    exact hs0 h

/-! ## The calls of a path -/

/-- **A path's entered frames hold of `C`** when its events do. -/
theorem calls_ok {C : CallRel} {rd : Reader} {σ : Val} {es : List Memory.Ev}
    (h : ∀ e ∈ es, e.Ok C rd σ) :
    ∀ c ∈ calls es, c.taken = true → C c.f (c.args.map σ) (c.rets.map σ) := by
  intro c hc ht
  obtain ⟨e, he, hce⟩ := List.mem_filterMap.mp hc
  match e, hce with
  | .call f args rets, hce =>
    simp only [Ev.call?, Option.some.injEq] at hce
    subst hce
    exact (h _ he).2 f args rets rfl
  | .skip f args, hce =>
    simp only [Ev.call?, Option.some.injEq] at hce
    subst hce
    simp at ht

/-! ## The tables' context and the terminal's precondition on a memory -/

variable {rd : Reader} {D : VsData} {P : VsPtrs} {bytecode : List K}

theorem bus_point (hok : D.Ok bytecode) : D.bus.point = D.gr.2.1 := by
  have hT0 := hok.tables (.claimed ⟨D.gr.2.1.take (layoutOf bytecode D.logMem D.rows).logBytecode ++
    D.alphas, D.bv, 0, 0, [], [], [], 0⟩) (bytecodeAt_claimed _ bytecode)
  rw [tablesSeg_point hT0]

/-- **The tables' context** on a memory holding the GKR point, the sumcheck's point and the
pooled claims' point lengths at their buffers. -/
theorem tctx_of (hok : D.Ok bytecode) (htok : D.TOk bytecode) (hz : ReadsAt rd P.zeta D.gr.2.1)
    (hchi : ReadsAt rd P.chi D.chis) (hcp : ReadsAt rd P.cplen (cplenWords D)) :
    TCtx rd (layoutOf bytecode D.logMem D.rows) D.bus D.claims
      [P.zeta, P.chi, D.rm, gen ^ D.gr.2.1.length, D.gzcn, P.cplen] := by
  have hbp := bus_point hok
  refine ⟨D.chis, by rw [hbp]; exact hz, by rw [hbp], hchi, htok.gzcn,
    by rw [hbp]; exact htok.chis_le, hok.claims_length, htok.columns, fun j p hj => ?_⟩
  obtain ⟨h1, h2, h3⟩ := htok.points j p hj
  refine ⟨fun hjn => ?_, fun h5 => by rw [hbp]; exact h1 h5, h2, h3⟩
  have hcl : (cplenWords D).length = nPooled := by
    simp [cplenWords, hok.claims_length, nPooled, nClaims]
  have hjl : j < (cplenWords D).length := by rw [hcl]; exact hjn
  have := hcp j hjl
  convert this using 2
  simp only [List.getElem?_map] at hj
  simp only [cplenWords, List.getElem_map, List.getElem_take]
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hj
  obtain ⟨_, hcj⟩ := List.getElem?_eq_some_iff.mp hc
  simp only [hcj]

/-- **The terminal's precondition** on a memory holding the tables' context, the placement's
words and the terminal's buffers. -/
theorem termPre_of {TC : Reader → Layout → BusResult → List ColumnClaim → List E → Prop}
    {PC : Reader → List ℕ → E → E → Prop} (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode)
    (htc : TC rd (layoutOf bytecode D.logMem D.rows) D.bus D.claims
      [P.zeta, P.chi, D.rm, gen ^ log2Ceil D.pushTotal, D.gzcn, P.cplen])
    (hpc : PC rd (columnKappas D.logMem 18 D.hs) P.off P.kap) (hK : HypKappa PC rd)
    (hlam : ReadsAt rd P.lam (powersFrom D.lam D.lam nClaims)) (hzv : ReadsAt rd P.zvals D.fpoint)
    (hct : ReadsAt rd P.ctab (ringCoefficients D.mcs))
    (hpt : ReadsAt rd P.pt (D.w.point ++ List.replicate (pointCap - D.w.point.length) 0)) :
    TermPre TC PC rd (layoutOf bytecode D.logMem D.rows) D.bus D.claims D.lam D.fpoint
      (ringCoefficients D.mcs) D.w [P.zeta, P.chi, D.rm, gen ^ log2Ceil D.pushTotal, D.gzcn,
        gen ^ D.logMem, gen ^ D.tau, P.cplen, P.lam, P.off, P.kap, P.zvals, P.ctab, P.pt, D.w.inner,
        D.w.residual, D.w.target] := by
  obtain ⟨hsl, hl28, -⟩ := stack_facts hb hok
  refine ⟨htc, ?_, ?_, rfl, rfl, ?_, hzv, hct, hpt, rfl, rfl, rfl, ?_⟩
  · rw [layoutOf_logBytecode hb]; exact hpc
  · exact hK _ _ _ hpc hl28
  · rw [hok.claims_length]; exact hlam
  · refine ⟨by simp only [layoutOf], by simp only [layoutOf], hok.stack_le,
      by rw [layoutOf_logMemory]; have := hok.logMem_ge; omega, busPoint_length hok, hok.open_point,
      ?_, by simp [ringCoefficients, kBits]⟩
    rw [layoutOf_heights]
    simp [VsData.fpoint, hok.rcs_length, hok.chi_length, VsData.tau, VsData.hs, opBlake2s]
    omega

end
end LeanVM.Guest.B1.VerifySub
