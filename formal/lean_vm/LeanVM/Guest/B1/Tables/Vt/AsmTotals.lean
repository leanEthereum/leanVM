/-
  LeanVM.Guest.B1.Tables.Vt.AsmTotals

  `verify_tables`' three bus totals are the specification's: the push, pull and count totals of
  `busRest` on the layout of the announced sizes.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.SpecPhase
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# The totals

`vt_asm_totals`: with the facts `verify_sub` hands `verify_tables` (the point, the heights and
row counts, `kappa_base`, the exponent tables, the sixteen slot weights), `bus_table_total[PUSH]`,
`bus_table_total[PULL]` and `bus_table_total[COUNT]` are the totals of `vtBus` (`vtAcc0`,
`vtAcc1`, `vtAcc2`), at the GKR leaves the guest loads.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (blockSel)

@[expose] public section

theorem vt_length_eqKernel_foldl : ∀ (pt out : List E),
    (pt.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) out).length =
      out.length * 2 ^ pt.length
  | [], out => by simp
  | r :: pt, out => by
    rw [List.foldl_cons, vt_length_eqKernel_foldl pt, List.length_append, List.length_map,
      List.length_map, List.length_cons, pow_succ]
    ring

theorem vt_take3 (W : List E) (h : 3 ≤ W.length) :
    W.take 3 = [W.getD 0 0, W.getD 1 0, W.getD 2 0] := by
  match W, h with
  | a :: b :: c :: _, _ => rfl

theorem vt_take5 (W : List E) (h : 5 ≤ W.length) :
    W.take 5 = [W.getD 0 0, W.getD 1 0, W.getD 2 0, W.getD 3 0, W.getD 4 0] := by
  match W, h with
  | a :: b :: c :: d :: e :: _, _ => rfl

theorem vtWFinalPc_eq : vtWFinalPc = Verifier.gpow (2 ^ 19 - 1) := by
  rw [vtWFinalPc, vt_word_ofK, Verifier.gpow, gen_pow_eq_ofK,
    show K.ofBits 12261764870545049476 = Parameters.addressOfIndex (2 ^ 19 - 1) by decide +kernel]

theorem vt_beta1 {rd : Reader} {σ : Val} (h : VtH rd σ) : σ (.n (val% «verify_tables» "beta_1")) = σ (.n (val% «verify_tables» "beta")) + 1 := by
  have a1 := h.atomAt 1716 (.const (.n (val% «verify_tables» "beta_1~0")) (word 1 0)) (by decide +kernel)
  have a2 := h.atomAt 1717 (.add (.n (val% «verify_tables» "beta_1")) (.n (val% «verify_tables» "beta")) (.n (val% «verify_tables» "beta_1~0"))) (by decide +kernel)
  simp only [Atom.Holds] at a1 a2
  rw [a2, a1, tb_word_one]

/-- The framework blocks' copies the totals read: the coordinate values and the pull side's eq
weights. -/
theorem vt_fw_copies {rd : Reader} {σ : Val} (h : VtH rd σ) :
    σ (.n (val% «verify_tables» "coord_vals[4]")) = σ (.n (val% «verify_tables» "coord_val@1")) ∧ σ (.n (val% «verify_tables» "coord_vals[6]")) = σ (.n (val% «verify_tables» "x@1")) ∧ σ (.n (val% «verify_tables» "coord_vals[7]")) = σ (.n (val% «verify_tables» "x@2")) ∧
      σ (.n (val% «verify_tables» "coord_vals[9]")) = σ (.n (val% «verify_tables» "coord_val@2")) ∧ σ (.n (val% «verify_tables» "public_eqs[0]")) = σ (.n (val% «verify_tables» "eq_hi@3")) ∧ σ (.n (val% «verify_tables» "block_eq_hi[54]")) = σ (.n (val% «verify_tables» "block_eq_hi[0]")) ∧
      σ (.n (val% «verify_tables» "block_eq_hi[55]")) = σ (.n (val% «verify_tables» "block_eq_hi[1]")) ∧ σ (.n (val% «verify_tables» "block_eq_hi[56]")) = σ (.n (val% «verify_tables» "block_eq_hi[2]")) ∧ σ (.n (val% «verify_tables» "public_eqs[1]")) = σ (.n (val% «verify_tables» "block_eq_hi[2]")) ∧
      σ (.n (val% «verify_tables» "coord_vals[303]")) = σ (.n (val% «verify_tables» "x@3")) ∧ σ (.n (val% «verify_tables» "coord_vals[304]")) = σ (.n (val% «verify_tables» "coord_val@3")) ∧ σ (.n (val% «verify_tables» "coord_vals[305]")) = σ (.n (val% «verify_tables» "coord_val@4")) ∧
      σ (.n (val% «verify_tables» "coord_vals[308]")) = σ (.n (val% «verify_tables» "x@4")) := by
  have a1 := h.atomAt 840 (.copy (.n (val% «verify_tables» "coord_vals[4]")) (.n (val% «verify_tables» "coord_val@1"))) (by decide +kernel)
  have a2 := h.atomAt 847 (.copy (.n (val% «verify_tables» "coord_vals[6]")) (.n (val% «verify_tables» "x@1"))) (by decide +kernel)
  have a3 := h.atomAt 852 (.copy (.n (val% «verify_tables» "coord_vals[7]")) (.n (val% «verify_tables» "x@2"))) (by decide +kernel)
  have a4 := h.atomAt 870 (.copy (.n (val% «verify_tables» "coord_vals[9]")) (.n (val% «verify_tables» "coord_val@2"))) (by decide +kernel)
  have a5 := h.atomAt 1193 (.copy (.n (val% «verify_tables» "public_eqs[0]")) (.n (val% «verify_tables» "eq_hi@3"))) (by decide +kernel)
  have a6 := h.atomAt 1194 (.copy (.n (val% «verify_tables» "block_eq_hi[54]")) (.n (val% «verify_tables» "block_eq_hi[0]"))) (by decide +kernel)
  have a7 := h.atomAt 1199 (.copy (.n (val% «verify_tables» "block_eq_hi[55]")) (.n (val% «verify_tables» "block_eq_hi[1]"))) (by decide +kernel)
  have a8 := h.atomAt 1214 (.copy (.n (val% «verify_tables» "block_eq_hi[56]")) (.n (val% «verify_tables» "block_eq_hi[2]"))) (by decide +kernel)
  have a9 := h.atomAt 1338 (.copy (.n (val% «verify_tables» "public_eqs[1]")) (.n (val% «verify_tables» "block_eq_hi[2]"))) (by decide +kernel)
  have a10 := h.atomAt 1206 (.copy (.n (val% «verify_tables» "coord_vals[303]")) (.n (val% «verify_tables» "x@3"))) (by decide +kernel)
  have a11 := h.atomAt 1208 (.copy (.n (val% «verify_tables» "coord_vals[304]")) (.n (val% «verify_tables» "coord_val@3"))) (by decide +kernel)
  have a12 := h.atomAt 1210 (.copy (.n (val% «verify_tables» "coord_vals[305]")) (.n (val% «verify_tables» "coord_val@4"))) (by decide +kernel)
  have a13 := h.atomAt 1221 (.copy (.n (val% «verify_tables» "coord_vals[308]")) (.n (val% «verify_tables» "x@4"))) (by decide +kernel)
  simp only [Atom.Holds] at a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩

section
variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ)
include hμ

/-- **The three totals.** -/
theorem vt_asm_totals {σ : Val} (h : VtH Lm.read σ) {bc : List K} (hbc : bc.length = 2 ^ 23)
    {point : List E} (hz : TbReadsAt Lm.read (σ (.n (val% «verify_tables» "zeta"))) point)
    (hmu : σ (.n (val% «verify_tables» "g_bus_mu")) = gen ^ point.length) (hml : point.length < 33)
    (hE : ExpTablesAt Lm.read (σ (.n (val% «verify_tables» "g_squares")))) {lm : ℕ} (hlm : lm ≤ 32)
    {rows : List ℕ} (hr : rows.length = 6) (hτ : ∀ t < 6, vtHt rows t < 33)
    (hkb : ∀ i < 8, σ (.n ((val% «verify_tables» "kb[0]") + i)) = gen ^ ([0, lm] ++ vtTauList (vtHt rows)).getD i 0)
    {weights : List E} (hwl : weights.length = 16)
    (hW : TbReadsAt Lm.read (σ (.n (val% «verify_tables» "fp_w"))) weights)
    (hpw : ∀ t < 6, σ (.n (vtPadV t)) = paddingWeight (point.take (vtHt rows t)) (vtRw rows t)) :
    σ (.n (val% «verify_tables» "bus_table_total[0]")) = (vtAcc0 (layoutOf bc lm rows) weights (σ (.n (val% «verify_tables» "beta"))) point
      [σ (.n (val% «verify_tables» "x@1")), σ (.n (val% «verify_tables» "x@2"))] (σ (.n (val% «verify_tables» "x@5"))) (σ (.n (val% «verify_tables» "s53.u0.s5#0")))).2 ∧
    σ (.n (val% «verify_tables» "bus_table_total[1]")) = (vtAcc1 (layoutOf bc lm rows) weights (σ (.n (val% «verify_tables» "beta"))) point
      [σ (.n (val% «verify_tables» "x@1")), σ (.n (val% «verify_tables» "x@2"))] (σ (.n (val% «verify_tables» "x@3"))) (σ (.n (val% «verify_tables» "x@4"))) (σ (.n (val% «verify_tables» "x@5")))
      (σ (.n (val% «verify_tables» "s53.u0.s5#0"))) (σ (.n (val% «verify_tables» "s53.u1.s5#0")))).2 ∧
    σ (.n (val% «verify_tables» "bus_table_total[2]")) = (vtAcc2 (layoutOf bc lm rows) weights (σ (.n (val% «verify_tables» "beta"))) point
      [σ (.n (val% «verify_tables» "x@1")), σ (.n (val% «verify_tables» "x@2"))] (σ (.n (val% «verify_tables» "x@3"))) (σ (.n (val% «verify_tables» "x@4"))) (σ (.n (val% «verify_tables» "x@5")))
      (σ (.n (val% «verify_tables» "s53.u0.s5#0"))) (σ (.n (val% «verify_tables» "s53.u1.s5#0"))) (σ (.n (val% «verify_tables» "s53.u2.s5#0")))).2 := by
  obtain ⟨l1, l2, s0, s1, s2, c0, c1, c2, hS, hsum, hSC, hsumC⟩ :=
    vt_sels hμ Lm h hz hmu hml hE hlm hτ hkb
  have k1 : σ (.n (val% «verify_tables» "kb[1]")) = gen ^ lm := by simpa using hkb 1 (by norm_num)
  have k2 : σ (.n (val% «verify_tables» "kappa_g@2")) = gen ^ 19 := by
    have e0 : σ (.n (val% «verify_tables» "kb[0]")) = 1 := by simpa using hkb 0 (by norm_num)
    rw [vt_fw2_kappa h, e0, one_mul]
  obtain ⟨i1, i1', i2, i2', m0, m1, -⟩ := vt_fw h hz l1 (by omega) l2 k1 k2
  obtain ⟨d810, d815, d819, d838, d1293, d1294, d1299, d1313, d1436, d1305, d1307, d1309,
    d1319⟩ := vt_fw_copies h
  obtain ⟨-, -, -, d1843, -, -⟩ := vt_fresh h
  set W : ℕ → E := fun i ↦ weights.getD i 0 with hWd
  have hw : ∀ i < 16, LoadHolds Lm.read (σ (.n (val% «verify_tables» "fp_w"))) i (W i) := fun i hi ↦ by
    have := hW i (by omega)
    rwa [← List.getD_eq_getElem _ 0] at this
  have hpw' : ∀ t < 6, paddingWeight (point.take (vtHt rows t)) (vtRw rows t) =
      σ (.n (vtPadV t)) := fun t ht ↦ (hpw t ht).symm
  have e0 := vt_total0 hbc weights (σ (.n (val% «verify_tables» "beta"))) point [σ (.n (val% «verify_tables» "x@1")), σ (.n (val% «verify_tables» "x@2"))]
    (σ (.n (val% «verify_tables» "x@5"))) (σ (.n (val% «verify_tables» "s53.u0.s5#0"))) _ _ _ (fun c ↦ σ (.n c)) (fun t ↦ σ (.n (vtPadV t)))
    s0.symm s1.symm s2.symm (fun i hi ↦ hS i hi) hpw' hr
  have e1 := vt_total1 hbc weights (σ (.n (val% «verify_tables» "beta"))) point [σ (.n (val% «verify_tables» "x@1")), σ (.n (val% «verify_tables» "x@2"))]
    (σ (.n (val% «verify_tables» "x@3"))) (σ (.n (val% «verify_tables» "x@4"))) (σ (.n (val% «verify_tables» "x@5"))) (σ (.n (val% «verify_tables» "s53.u0.s5#0"))) (σ (.n (val% «verify_tables» "s53.u1.s5#0"))) _ _ _
    (fun c ↦ σ (.n c)) (fun t ↦ σ (.n (vtPadV t))) s0.symm s1.symm s2.symm (fun i hi ↦ hS i hi)
    hpw' hr
  have e2 := vt_total2 (bc := bc) (lm := lm) weights (σ (.n (val% «verify_tables» "beta"))) point
    [σ (.n (val% «verify_tables» "x@1")), σ (.n (val% «verify_tables» "x@2"))] (σ (.n (val% «verify_tables» "x@3"))) (σ (.n (val% «verify_tables» "x@4"))) (σ (.n (val% «verify_tables» "x@5")))
    (σ (.n (val% «verify_tables» "s53.u0.s5#0"))) (σ (.n (val% «verify_tables» "s53.u1.s5#0"))) (σ (.n (val% «verify_tables» "s53.u2.s5#0"))) (fun c ↦ σ (.n c)) (fun t ↦ σ (.n (vtPadV t))) W
    (fun i hi ↦ hSC i hi) hpw' hr
  have hpad := vt_push_pad h hw
  rw [vt_beta1 h] at hpad
  have hfp : ∀ (L : Layout), L.logMemory = lm → L.logBytecode = 19 →
      vtFpPush L weights point [σ (.n (val% «verify_tables» "x@1")), σ (.n (val% «verify_tables» "x@2"))] (σ (.n (val% «verify_tables» "x@5"))) =
        [W 0 + W 1 + W 2, W 0 * gen + W 1 * σ (.n (val% «verify_tables» "coord_val@1")) + W 2 + W 3 * σ (.n (val% «verify_tables» "x@1")) +
          W 4 * σ (.n (val% «verify_tables» "x@2")), W 0 * gen ^ 2 + W 1 * σ (.n (val% «verify_tables» "coord_val@2")) + W 2 + σ (.n (val% «verify_tables» "x@5"))] ∧
      vtFpPull L weights point [σ (.n (val% «verify_tables» "x@1")), σ (.n (val% «verify_tables» "x@2"))] (σ (.n (val% «verify_tables» "x@3"))) (σ (.n (val% «verify_tables» "x@4")))
          (σ (.n (val% «verify_tables» "x@5"))) =
        [W 0 + W 1 * vtWFinalPc + W 2, W 0 * gen + W 1 * σ (.n (val% «verify_tables» "coord_val@1")) + W 2 * σ (.n (val% «verify_tables» "x@3")) +
          W 3 * σ (.n (val% «verify_tables» "x@1")) + W 4 * σ (.n (val% «verify_tables» "x@2")),
          W 0 * gen ^ 2 + W 1 * σ (.n (val% «verify_tables» "coord_val@2")) + W 2 * σ (.n (val% «verify_tables» "x@4")) + σ (.n (val% «verify_tables» "x@5"))] := by
    intro L hL1 hL2
    simp only [vtFpPush, vtFpPull, fingerprints, hL1, hL2, vt_take3 weights (by omega),
      vt_take5 weights (by omega), ← i1, ← i2, vtWFinalPc_eq, dot, List.zipWith_cons_cons,
      List.zipWith_nil_left, List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append,
      sepState, sepMem, sepBytecode, Verifier.gpow, pow_zero, hWd]
    refine ⟨?_, ?_⟩ <;> simp only [List.cons.injEq, and_true] <;> refine ⟨?_, ?_, ?_⟩ <;> ring
  obtain ⟨fP, fQ⟩ := hfp (layoutOf bc lm rows) (vt_layout_logMemory bc lm rows)
    (vt_layout_logBytecode bc lm rows hbc)
  refine ⟨?_, ?_, ?_⟩
  · rw [e0, fP, vt_push_total h, vt_push_fw h hw, hpad, vt_push_sel h, hsum, d810, d815, d819,
      d838, d1293, d1843, c0, c1, c2]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    ring
  · rw [e1, fQ, vt_pull_total h, vt_pull_fw h hw, hpad, vt_pull_sel h, d1294, d1299, d1313,
      d1436, d1305, d1307, d1309, d1319, i1', i2', m0, m1, d1843, c0, c1, c2]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    ring
  · rw [e2, vt_count_total h, vt_count_pad h W, vt_count_sel h, hsumC]
    ring

end

end
end LeanVM.Guest.B1.Tables
