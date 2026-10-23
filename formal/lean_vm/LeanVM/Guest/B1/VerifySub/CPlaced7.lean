/-
  LeanVM.Guest.B1.VerifySub.CPlaced7

  `verify_sub` placed: its `HeapBuf`s at the allocator's bases, and where its loads read.
-/

module

public import LeanVM.Guest.B1.VerifySub.CPlaced6
public import LeanVM.Guest.B1.EqWeight

/-!
# `verify_sub`'s buffers and loads, placed

* `vsBufs_fit`: the honest words fit the buffers; `fixedCells_length`: `defer_out` has `106`
  cells;
* `vs_allocs`: the path's `HeapBuf` sizes are `vsSizes`, its pointers the allocator's bases;
* `vs_load`: each load of the body reads one of `verify_sub`'s buffers below its size, or the
  caller's words (the exponent tables, `defer_out`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Sig
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {bytecode : List K} {D : VsData} {fp lpA sqA outA : ℕ} {off kap pt : E}

/-! ## The buffers -/

theorem vsBufs_fit (hok : D.Ok bytecode) (htok : D.TOk bytecode) :
    List.Forall₂ (fun c s => c.length ≤ s) (vsBufs D) (vsSizes D) := by
  have hd : D.gr.2.1.length < 33 := by rw [hok.point_length]; exact hok.depth_lt
  have hτ := tau_lt hok
  have hal : D.alphas.length = 4 := by simp [VsData.alphas, sqAll_eq]
  simp only [vsBufs, vsSizes, List.forall₂_cons, List.Forall₂.nil, and_true]
  refine ⟨by rw [List.length_map, hok.claims_length], by simp [cplenWords, hok.claims_length, nClaims], htok.stream_le,
    by simp [hok.rows_length], by simp [hs_length hok], by simp [kappaBase, hs_length hok],
    by simp [blockKappas], le_rfl, by omega, by rw [length_eqKernel, hal]; rfl,
    by have := htok.chis_le; omega, by rw [hok.chi_length]; omega, by rw [hok.rcs_length],
    by rw [hok.s_length], by rw [mcs_length], by simp [ringCoefficients, kBits],
    by simp [VsData.fpoint, hok.rcs_length, hok.chi_length]; omega,
    by rw [(rsChain_at (D := D) (j := 0) (by omega)).2.2], by rw [length_powersFrom]⟩

theorem fixedCells_length (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) :
    (Node.fixedCells D.fresh).length = 106 := by
  have := depth_ge hb hok
  have hal : D.alphas.length = 4 := by simp [VsData.alphas, sqAll_eq]
  simp [Node.fixedCells, VsData.fresh, hal, hok.rcs_length, hok.s_length, hok.chi_length]
  omega

theorem vs_allocs (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) {σ : Val} {lp sq out : E}
    (hfix : Fixes σ (vsG11 D (vsPtrsAt fs fp D off kap pt) lp sq out)) (sel : ℕ) :
    allocs σ (vsEvs σ sel) = vsSizes D ∧
      (allocDsts (vsEvs σ sel)).map σ =
        (bases (fp + fs "verify_sub") (vsSizes D)).map fun b => ofK (Parameters.gpow b) := by
  obtain ⟨h1, h2, -⟩ := vs_parts σ sel
  rw [vsPre1_allocs] at h1 h2
  have e417 : σ (.n 417) = gen ^ log2Ceil D.pushTotal := hfix.get (by vs_mem)
  have e720 : σ (.n 720) = ofK (Parameters.gpow (D.tau + 8)) := by
    rw [hfix.get (k := 720) (e := gen ^ D.tau * word 256 0 0) (by vs_mem),
      show word 256 0 0 = gen ^ 8 from word_two_pow (a := 8) (by decide), ← pow_add, gen_pow_eq_ofK]
  have hA : Fixes σ (allocFix (vsPtrsAt fs fp D off kap pt)) := hfix.sub (by
    intro p hp; simp only [allocFix, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> vs_mem)
  have hl : log2Ceil D.pushTotal < 2 ^ 64 - 1 := by
    have := (pushTotal_bounds hb hok).2; omega
  refine ⟨?_, ?_⟩
  · rw [h2]
    simp only [List.map_cons, List.map_nil, Sum.elim_inl, Sum.elim_inr, id, e417, e720,
      gen_pow_eq_ofK, logG_spec hl, logG_spec (show D.tau + 8 < 2 ^ 64 - 1 by have := tau_lt hok; omega)]
    rw [← depth_eq hb hok]
    rfl
  · rw [h1]
    simp only [allocFix, Fixes, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
      forall_eq] at hA
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ := hA
    simp only [List.map_cons, List.map_nil, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
      a13, a14, a15, a16, a17, a18, vsPtrsAt, vsBases, vsSizes, bases]
    simp

/-! ## The loads -/

/-- The address `i` lies in `verify_sub`'s buffer `t`. -/
def InBuf (fs : String → ℕ) (fp : ℕ) (D : VsData) (i : ℕ) : Prop :=
  ∃ t < 19, vsB fs fp D t ≤ i ∧ i < vsB fs fp D t + (vsSizes D).getD t 0

theorem inBuf_own {i : ℕ} (h : InBuf fs fp D i) :
    ∃ q ∈ (vsSizes D).zip (bases (fp + fs "verify_sub") (vsSizes D)), q.2 ≤ i ∧ i < q.2 + q.1 := by
  obtain ⟨t, ht, h1, h2⟩ := h
  have hl : t < (vsSizes D).length := by simp [vsSizes]; omega
  have hb : t < (bases (fp + fs "verify_sub") (vsSizes D)).length := by rw [length_bases]; exact hl
  have hz : t < ((vsSizes D).zip (bases (fp + fs "verify_sub") (vsSizes D))).length := by
    simp [List.length_zip, hl, hb]
  refine ⟨_, List.getElem_mem hz, ?_, ?_⟩
  · simp only [List.getElem_zip]
    simp only [vsB, vsBases, List.getD_eq_getElem _ _ hb] at h1; exact h1
  · simp only [List.getElem_zip]
    simp only [vsB, vsBases, List.getD_eq_getElem _ _ hb, List.getD_eq_getElem _ _ hl] at h2
    exact h2

/-- **Each load of the body reads `verify_sub`'s buffers or the caller's words.** -/
theorem vs_load (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) {σ : Val}
    (hfix : Fixes σ (vsG11 D (vsPtrsAt fs fp D off kap pt) (ofK (Parameters.gpow lpA))
      (ofK (Parameters.gpow sqA)) (ofK (Parameters.gpow outA))))
    (q : V × ℕ) (hq : loadOkB q = true) :
    ∃ i, (σ q.1).limb 0 * Parameters.gpow q.2 = Parameters.gpow i ∧
      (InBuf fs fp D i ∨ RegionL (vsExtL lpA sqA outA D) i) := by
  set P := vsPtrsAt fs fp D off kap pt
  have own : ∀ t, t < 19 → ∀ v, σ (.n v) = ofK (Parameters.gpow (vsB fs fp D t)) → ∀ o,
      o < (vsSizes D).getD t 0 → ∃ i, (σ (.n v)).limb 0 * Parameters.gpow o = Parameters.gpow i ∧
        (InBuf fs fp D i ∨ RegionL (vsExtL lpA sqA outA D) i) :=
    fun t ht v hv o ho => ⟨vsB fs fp D t + o, by rw [hv, Main.addr_ofK],
      Or.inl ⟨t, ht, by omega, by omega⟩⟩
  have hd := depth_ge hb hok
  have hτ := tau_lt hok
  obtain ⟨p, o⟩ := q
  simp only [loadOkB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.any_eq_true, List.mem_range, or_assoc] at hq
  rcases hq with ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ |
    ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ |
    ⟨rfl, ho⟩ | ⟨rfl, rfl⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨⟨b, hb37, rfl⟩, rfl⟩
  · exact own 0 (by omega) 7 (hfix.get (k := 7) (e := P.pool) (by vs_mem)) _ (by simp [vsSizes]; omega)
  · exact own 2 (by omega) 14 (hfix.get (k := 14) (e := P.stream) (by vs_mem)) _
      (by simp [vsSizes]; omega)
  · exact own 3 (by omega) 30 (hfix.get (k := 30) (e := P.rows) (by vs_mem)) _ (by simp [vsSizes]; omega)
  · exact own 4 (by omega) 143 (hfix.get (k := 143) (e := P.dims) (by vs_mem)) _
      (by simp [vsSizes]; omega)
  · exact own 5 (by omega) 155 (hfix.get (k := 155) (e := P.kbase) (by vs_mem)) _
      (by simp [vsSizes]; omega)
  · exact own 6 (by omega) 163 (hfix.get (k := 163) (e := P.bk) (by vs_mem)) _
      (by simp [vsSizes]; omega)
  · exact own 7 (by omega) 418 (hfix.get (k := 418) (e := P.zeta) (by vs_mem)) _
      (by simp [vsSizes]; omega)
  · exact own 8 (by omega) 451 (hfix.get (k := 451) (e := P.alpha) (by vs_mem)) _
      (by simp [vsSizes]; omega)
  · exact own 9 (by omega) 508 (hfix.get (k := 508) (e := P.fpw) (by vs_mem)) _
      (by simp [vsSizes]; omega)
  · exact own 11 (by omega) 721 (hfix.get (k := 721) (e := P.zchis) (by vs_mem)) _
      (by simp [vsSizes]; omega)
  · exact own 12 (by omega) 722 (hfix.get (k := 722) (e := P.lrs) (by vs_mem)) _
      (by simp [vsSizes]; omega)
  · exact own 13 (by omega) 723 (hfix.get (k := 723) (e := P.zpart) (by vs_mem)) _
      (by simp [vsSizes]; omega)
  · exact own 14 (by omega) 732 (hfix.get (k := 732) (e := P.mcs) (by vs_mem)) _
      (by simp [vsSizes]; omega)
  · exact own 15 (by omega) 733 (hfix.get (k := 733) (e := P.ctab) (by vs_mem)) _
      (by simp [vsSizes]; omega)
  · exact own 16 (by omega) 734 (hfix.get (k := 734) (e := P.zvals) (by vs_mem)) _
      (by simp [vsSizes]; omega)
  · exact own 17 (by omega) 1144 (hfix.get (k := 1144) (e := P.rs) (by vs_mem)) _
      (by simp [vsSizes]; omega)
  · have h1149 : σ (.n 1149) = ofK (Parameters.gpow (vsB fs fp D 17 + 128)) := by
      have hrs : P.rs = ofK (Parameters.gpow (vsB fs fp D 17)) := rfl
      rw [hfix.get (k := 1149) (e := P.rs * word 325 0 0) (by vs_mem), word325, gen_pow_eq_ofK, hrs,
        ← Parameters.ofK_mul, Parameters.gpow, Parameters.gpow, ← pow_add]
    refine ⟨vsB fs fp D 17 + 128 + 1, by rw [h1149, Main.addr_ofK], Or.inl ⟨17, by omega, by omega, ?_⟩⟩
    simp [vsSizes]
  · exact own 18 (by omega) 1180 (hfix.get (k := 1180) (e := P.lam) (by vs_mem)) _
      (by simp [vsSizes]; omega)
  · have h6 : σ (.n 6) = ofK (Parameters.gpow outA) := hfix.get (by vs_mem)
    refine ⟨outA + o, by rw [h6, Main.addr_ofK], Or.inr ⟨(outA, Node.fixedCells D.fresh),
      by simp [vsExtL], by simp, by simp [fixedCells_length hb hok]; omega⟩⟩
  · have hk : pkap D b < 34 := by
      have := pushKappas_le D.logMem D.hs (hs_length hok) hok.logMem_le (hs_lt hok) b hb37
      unfold pkap; omega
    have hp : σ (.n (pushK b + 1)) = ofK (Parameters.gpow (sqA + pkap D b)) := by
      rw [hfix.get (k := pushK b + 1) (e := ofK (Parameters.gpow sqA) * gen ^ pkap D b)
        (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
          (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
            (List.mem_append_right _ (List.mem_map.mpr ⟨b, List.mem_range.mpr (by omega), rfl⟩))))))))]
      rw [gen_pow_eq_ofK, ← Parameters.ofK_mul, Parameters.gpow, Parameters.gpow, ← pow_add]
    refine ⟨sqA + pkap D b + 0, by rw [hp, Main.addr_ofK], Or.inr ⟨(sqA, (List.range sizeBits).map
      fun j => gen ^ 2 ^ j), by simp [vsExtL, expL], by simp, by simp [sizeBits]; omega⟩⟩

end
end LeanVM.Guest.B1.VerifySub
