/-
  LeanVM.Guest.B1.Tables.Vt.AsmFinal

  The table sumcheck's final check: the specification's terminal value of the table loop, over
  the guest's evaluations and the bus forms, is the guest's final claim.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.AsmForms
public import LeanVM.Guest.B1.Tables.Vt.Air

/-!
# The final check (V:664-675)

`vt_weight_guest`: a table's weight at the reversed challenges is the guest's `cprod[g^n/τ]` times
`peq[τ]`. `vt_xi_pow`: the batching challenge's powers. `vt_asm_final`: `termsPure`'s terminal
value over the six tables — the weights times the `JUMP` constraints and the three forms, batched
by `ξ⁰, ξ¹` and `ξ², ξ³, ξ⁴` — is `σ 2610`, the sumcheck's final claim the guest checks.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (termsPure length_tableWeights jumpConstraints_eq
  refNConstraints)

@[expose] public section

/-- **A table's weight**, the guest's way. -/
theorem vt_weight_guest {rd : Reader} {σ : Val} {point pts : List E} {n : ℕ}
    (hpl : pts.length = n) (hnp : n ≤ point.length)
    (hcp : ∀ j ≤ n, LoadHolds rd (σ (.n 2608)) j (pts.take j).prod)
    (hpe : EqPrefix rd (σ (.n 2629)) 1 (σ (.n 16)) (σ (.n 703)) n)
    (hchi : ∀ i < n, LoadHolds rd (σ (.n 16)) (n - 1 - i) (pts.getD i 0))
    (hz1 : TbReadsAt rd (σ (.n 703)) (point.map (1 + ·))) (hgn : σ (.n 2516) = gen ^ n)
    {heights : List ℕ} {t : ℕ} (ht : t < heights.length) (hh : heights.getD t 0 ≤ n)
    {x τv cp pe : E} (hx : σ (.n 2516) = x * τv) (hτv : τv = gen ^ heights.getD t 0)
    (hcpL : LoadHolds rd (σ (.n 2608) * x) 0 cp) (hpeL : LoadHolds rd (σ (.n 2629) * τv) 0 pe) :
    (tableWeights heights point pts.reverse).getD t 0 = cp * pe := by
  set hg := heights.getD t 0
  have hxv : x = gen ^ (n - hg) := by
    have e : x * gen ^ hg = gen ^ (n - hg) * gen ^ hg := by
      rw [← pow_add, Nat.sub_add_cancel hh, ← hgn, hx, hτv]
    exact mul_right_cancel₀ (pow_ne_zero _ gen_ne_zero) e
  rw [hxv, tb_loadHolds_mul_gen_pow, Nat.add_zero] at hcpL
  have ecp := tb_loadHolds_unique hcpL (hcp (n - hg) (by omega))
  rw [hτv, tb_loadHolds_mul_gen_pow, Nat.add_zero] at hpeL
  obtain ⟨as, bs, hal, hbl, has, hbs, hpre⟩ := hpe
  have hchiR : TbReadsAt rd (σ (.n 16)) pts.reverse := fun k hk ↦ by
    simp only [List.length_reverse] at hk
    have := hchi (n - 1 - k) (by omega)
    rw [show n - 1 - (n - 1 - k) = k by omega, List.getD_eq_getElem _ _ (by omega)] at this
    rw [List.getElem_reverse]
    convert this using 2
    omega
  have eas : as = pts.reverse := tbReadsAt_unique has hchiR (by simp; omega)
  have ebs : bs = (point.map (1 + ·)).take n :=
    tbReadsAt_unique hbs (tbReadsAt_take hz1 n) (by simp; omega)
  have epe := tb_loadHolds_unique hpeL (hpre hg hh)
  rw [vt_weight heights point pts hpl hnp ht hh, ecp, epe, eas, ebs]

/-- The batching challenge's powers. -/
theorem vt_xi_pow {rd : Reader} {σ : Val} (h : VtH rd σ) :
    σ (.n 2589) = 1 ∧ σ (.n 2590) = σ (.n 2588) ∧ σ (.n 2591) = σ (.n 2588) ^ 2 ∧
      σ (.n 2592) = σ (.n 2588) ^ 3 ∧ σ (.n 2593) = σ (.n 2588) ^ 4 := by
  have a0 := h.atomAt 2636 (.const (.n 2589) (word 1 0)) (by decide +kernel)
  have a1 := h.atomAt 2637 (.mul (.n 2590) (.n 2589) (.n 2588)) (by decide +kernel)
  have a2 := h.atomAt 2638 (.mul (.n 2591) (.n 2590) (.n 2588)) (by decide +kernel)
  have a3 := h.atomAt 2639 (.mul (.n 2592) (.n 2591) (.n 2588)) (by decide +kernel)
  have a4 := h.atomAt 2640 (.mul (.n 2593) (.n 2592) (.n 2588)) (by decide +kernel)
  simp only [Atom.Holds, tb_word_one] at a0 a1 a2 a3 a4
  refine ⟨a0, by rw [a1, a0, one_mul], by rw [a2, a1, a0]; ring, by rw [a3, a2, a1, a0]; ring,
    by rw [a4, a3, a2, a1, a0]; ring⟩

theorem vt_nConstraints_each : (tables.getD 0 default).nConstraints = 0 ∧
    (tables.getD 1 default).nConstraints = 0 ∧ (tables.getD 2 default).nConstraints = 0 ∧
    (tables.getD 3 default).nConstraints = 0 ∧ (tables.getD 4 default).nConstraints = 2 ∧
    (tables.getD 5 default).nConstraints = 0 := by
  have h := refNConstraints
  rw [vt_tables_six] at h
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

theorem vt_constraints (ev : List E) : (tables.getD 0 default).constraints ev = [] ∧
    (tables.getD 1 default).constraints ev = [] ∧ (tables.getD 2 default).constraints ev = [] ∧
    (tables.getD 3 default).constraints ev = [] ∧
    (tables.getD 4 default).constraints ev = jumpConstraints ev ∧
    (tables.getD 5 default).constraints ev = [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

section
variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ)
include hμ

/-- **The final check.** -/
theorem vt_asm_final {σ : Val} (h : VtH Lm.read σ) (bc : List K) (hbc : bc.length = 2 ^ 23)
    {point : List E} (hz : TbReadsAt Lm.read (σ (.n 8)) point)
    (hmu : σ (.n 9) = gen ^ point.length) (hml : point.length < 33)
    (hE : ExpTablesAt Lm.read (σ (.n 12))) {lm : ℕ} (hlm : lm ≤ 32)
    {rows : List ℕ} (hr : rows.length = 6) (hτ : ∀ t < 6, vtHt rows t < 29)
    (hkb : ∀ i < 8, σ (.n (25 + i)) = gen ^ ([0, lm] ++ vtTauList (vtHt rows)).getD i 0)
    {alphas : List E} (hal : alphas.length = 4)
    (hW : TbReadsAt Lm.read (σ (.n 13)) (eqKernel alphas)) {n : ℕ}
    (hgn : σ (.n 2516) = gen ^ n) (hhn : ∀ t < 6, vtHt rows t ≤ n) (hnp : n ≤ point.length)
    {pts : List E} (hpl : pts.length = n)
    (hcp : ∀ j ≤ n, LoadHolds Lm.read (σ (.n 2608)) j (pts.take j).prod)
    (hpe : EqPrefix Lm.read (σ (.n 2629)) 1 (σ (.n 16)) (σ (.n 703)) n)
    (hchi : ∀ i < n, LoadHolds Lm.read (σ (.n 16)) (n - 1 - i) (pts.getD i 0)) :
    (termsPure ((powers (σ (.n 2588)) 5).take 2) ((powers (σ (.n 2588)) 5).drop 2) pts.reverse
      (List.zip (vtRows (tableHeightsOf rows)
        (vtAcc2 (layoutOf bc lm rows) alphas (σ (.n 14)) point
          [σ (.n 830), σ (.n 843), σ (.n 856)] (σ (.n 1843)) (σ (.n 1898)) (σ (.n 581))
          (σ (.n 25)) (σ (.n 26)) (σ (.n 27))).1 point pts) (vtEvsT σ)) 0 0 []).1 =
      σ (.n 2626) := by
  have hz1 := vt_zeta1 h hz hmu (by omega)
  set F := (vtAcc2 (layoutOf bc lm rows) alphas (σ (.n 14)) point
    [σ (.n 830), σ (.n 843), σ (.n 856)] (σ (.n 1843)) (σ (.n 1898)) (σ (.n 581))
    (σ (.n 25)) (σ (.n 26)) (σ (.n 27))).1 with hF
  have hFv : ∀ t < 6, (F.getD t []).map (·.evaluate ((vtEvT σ t).getD · 0)) =
      (vtFV.getD t []).map fun v ↦ σ (.n v) := fun t ht ↦
    vt_forms_val hμ Lm h bc hbc hz hmu hml hE hlm hr hτ hkb hal hW ht
  have hF6 := (vt_forms3_shape bc lm hr alphas (σ (.n 14)) point
    [σ (.n 830), σ (.n 843), σ (.n 856)] (σ (.n 1843)) (σ (.n 1898)) (σ (.n 581))
    (σ (.n 25)) (σ (.n 26)) (σ (.n 27))).1
  have hH6 : (tableHeightsOf rows).length = 6 := vt_tableHeightsOf_length hr
  set Wt := tableWeights (tableHeightsOf rows) point pts.reverse with hWt
  have hW6 : Wt.length = 6 := by rw [hWt, length_tableWeights, hH6]
  -- the weights
  have hkbt : ∀ t < 6, σ (.n (30 + t)) = gen ^ vtHt rows t := fun t ht => by
    have := hkb (2 + t) (by omega)
    rwa [show 28 + (2 + t) = 30 + t by omega, Nat.add_comm 2 t, vt_tau_getD lm _ ht] at this
  have hwt : ∀ t < 6, ∀ {x cp pe : E}, σ (.n 2516) = x * σ (.n (30 + t)) →
      LoadHolds Lm.read (σ (.n 2608) * x) 0 cp →
      LoadHolds Lm.read (σ (.n 2629) * σ (.n (30 + t))) 0 pe → Wt.getD t 0 = cp * pe := by
    intro t ht x cp pe hx hcpL hpeL
    exact vt_weight_guest hpl hnp hcp hpe hchi hz1 hgn (by rw [hH6]; exact ht) (hhn t ht) hx
      (hkbt t ht) hcpL hpeL
  obtain ⟨x0, c0, p0, v0⟩ := vtAir0 h
  obtain ⟨x1, c1, p1, v1⟩ := vtAir1 h
  obtain ⟨x2, c2, p2, v2⟩ := vtAir2 h
  obtain ⟨x3, c3, p3, v3⟩ := vtAir3 h
  have hev4 : ∀ c < 14, σ (.n (vtEvB (53 + c))) = (vtEvT σ 4).getD c 0 :=
    fun c hc ↦ (vt_evT_getD σ 4 c hc).symm
  obtain ⟨x4, c4, p4, v4⟩ := vtAir4 h hev4
  obtain ⟨x5, c5, p5, v5⟩ := vtAir5 h
  have w0 := hwt 0 (by norm_num) x0 c0 p0
  have w1 := hwt 1 (by norm_num) x1 c1 p1
  have w2 := hwt 2 (by norm_num) x2 c2 p2
  have w3 := hwt 3 (by norm_num) x3 c3 p3
  have w4 := hwt 4 (by norm_num) x4 c4 p4
  have w5 := hwt 5 (by norm_num) x5 c5 p5
  have f0 := hFv 0 (by norm_num)
  have f1 := hFv 1 (by norm_num)
  have f2 := hFv 2 (by norm_num)
  have f3 := hFv 3 (by norm_num)
  have f4 := hFv 4 (by norm_num)
  have f5 := hFv 5 (by norm_num)
  simp only [vtFV, List.getD_cons_zero, List.getD_cons_succ, List.map_cons,
    List.map_nil] at f0 f1 f2 f3 f4 f5
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := vt_nConstraints_each
  obtain ⟨xp0, xp1, xp2, xp3, xp4⟩ := vt_xi_pow h
  rw [vtRows, ← hWt, vt_six Wt hW6 0, vt_tables_six, vt_six (tableHeightsOf rows) hH6 0,
    vt_six F hF6 [], vtEvsT]
  simp only [List.zip_cons_cons, List.zip_nil_left, termsPure, f0, f1, f2, f3, f4, f5,
    w0, w1, w2, w3, w4, w5, n0, n1, n2, n3, n4, n5, (vt_constraints _).1, (vt_constraints _).2.1,
    (vt_constraints _).2.2.1, (vt_constraints _).2.2.2.1, (vt_constraints _).2.2.2.2.1,
    (vt_constraints _).2.2.2.2.2, jumpConstraints_eq]
  rw [vt_air_total h, v0, v1, v2, v3, v4, v5, xp0, xp1, xp2, xp3, xp4, tb_word_one]
  simp only [powers, powersFrom, dot, List.take, List.drop, List.zipWith_cons_cons,
    List.zipWith_nil_right, List.foldl_cons, List.foldl_nil]
  ring

end

end
end LeanVM.Guest.B1.Tables
