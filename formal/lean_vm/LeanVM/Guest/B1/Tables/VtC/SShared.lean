/-
  LeanVM.Guest.B1.Tables.VtC.SShared

  `idxc_tab`, `zeta1` and the six tables' shared selector tables hold on the honest valuation.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.SBase
public import LeanVM.Guest.B1.Selectors.SharedTablesComplete
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# The index factors, `1 + ζ` and the shared tables

`vtIdxcW`: `idxc_tab`'s words `1 + g^(2^t)`; `idxc_ok`: its stores hold on a memory holding them.
`zeta1_ok`: `plus_one_run` on `g^μ` holds when `zeta1` holds `1 + ζ_k`. `sh_call`: a table's
`shared_selector_tables` call on a run of `μ - τ` coordinates, its nibble tables in place
(`RunTables`). `vtc_shA`: table `t`'s run and allocations (`vtShAT`) hold, `shared_len[t] = g^(μ - τ)`,
its tables' sizes `g^(8(μ - τ + 1))`, `g^(4(μ - τ + 1))` and pointers the oracle's; `vtc_shC`: its
products and call (`vtShCT`) hold with its tables in place.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- `idxc_tab`'s words. -/
def vtIdxcW : List E := (List.range 34).map fun t ↦ 1 + gen ^ 2 ^ t

theorem vtIdxc_word {t : ℕ} (ht : t < 34) :
    word (tbGSquaresBits.getD t 0 ^^^ 1) 0 = 1 + gen ^ 2 ^ t := by
  rw [word_eOfNat, eOfNat_xor, eOfNat_one, gen_pow_two_pow_eq ht, add_comm]

variable {rd : Reader} {w : ℕ → E} {args : List E}

/-- **`idxc_tab`'s stores.** -/
theorem idxc_ok (hl : args.length = 21) (h : ReadsAt rd (vtσ rd w args (.n (val% «verify_tables» "idxc_tab"))) vtIdxcW) :
    ∀ st ∈ vtIdxcT, VSH (coreProgram.Rel rd) rd (vtσ rd w args) st := by
  intro st hst
  have hst' := hst
  simp only [vtIdxcT, List.mem_flatten, List.mem_map, List.mem_range] at hst'
  obtain ⟨_, ⟨t, ht, rfl⟩, hm⟩ := hst'
  have hc : vtσ rd w args (.n (768 + t)) = 1 + gen ^ 2 ^ t := by
    have := vt_goodS (rd := rd) (w := w) hl (vt_mem_slice (vtPre_drop (pos% «verify_tables» "s21.u0.s0#0") ▸ vtIdxc_check)
      (show Stmt.atom (.const (.n (768 + t)) (word (tbGSquaresBits.getD t 0 ^^^ 1) 0)) ∈
        vtIdxcT by
          simp only [vtIdxcT, List.mem_flatten, List.mem_map, List.mem_range]
          exact ⟨_, ⟨t, ht, rfl⟩, List.mem_cons_self⟩))
    simp only [fixNe, GoodS, Good] at this
    rw [this, vtIdxc_word ht]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · show _ = _
    rw [hc, vtIdxc_word ht]
  · show LoadHolds rd _ _ _
    rw [hc]
    have := h t (by simp [vtIdxcW]; exact ht)
    simpa [vtIdxcW] using this

/-- **`zeta1`'s `plus_one_run`.** -/
theorem zeta1_ok (hl : args.length = 21) {point : List E}
    (h9 : vtσ rd w args (.n (val% «verify_tables» "g_bus_mu")) = gen ^ point.length) (hμ : point.length ≤ 33)
    (hz : ReadsAt rd (vtσ rd w args (.n (val% «verify_tables» "zeta"))) point)
    (hz1 : ReadsAt rd (vtσ rd w args (.n (val% «verify_tables» "zeta1"))) (point.map (1 + ·))) (hw : w 803 = 0) :
    VSH (coreProgram.Rel rd) rd (vtσ rd w args)
      (.dispatch (.n (val% «verify_tables» "g_bus_mu")) plusOneRunNames [.n (val% «verify_tables» "zeta1"), .n (val% «verify_tables» "zeta")] [.n (val% «verify_tables» "zeta1_done")]) := by
  have hg := vt_goodS (rd := rd) (w := w) hl (vt_mem_slice (blk := [_]) (vtPre_drop (pos% «verify_tables» "zeta1_done") ▸ vtZeta1_check)
    List.mem_cons_self)
  simp only [fixNe, GoodS, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hg
  rw [vsh_dispatch]
  have hj : point.length < plusOneRunNames.length := by simp [plusOneRunNames]; omega
  refine ⟨point.length, hj, by rw [h9, gen_pow_eq_ofK], ?_⟩
  rw [← List.getD_eq_getElem _ ""]
  refine (plus_one_run_holds _ hμ rd _ _).mpr ?_
  simp only [List.map_cons, List.map_nil, MeaningPlusOneRun]
  exact ⟨⟨point, rfl, hz, hz1⟩, by rw [hg]; simp [hw]⟩

theorem sh_call {μ τ : ℕ} {point : List E} (hμ : point.length = μ) (hμ33 : μ < 33)
    (hτμ : τ ≤ μ) {eqt gt z z1 gsq : E}
    (hzv : ReadsAt rd z (point.drop τ)) (hz1v : ReadsAt rd z1 ((point.map (1 + ·)).drop τ))
    (hsqv : ReadsAt rd gsq ((gSquaresList.drop τ).take (μ - τ)))
    (hrun : RunTables rd eqt gt (μ - τ) (point.drop τ) ((point.map (1 + ·)).drop τ)
      ((gSquaresList.drop τ).take (μ - τ)))
    (hpad : RunPads rd eqt gt (μ - τ) (point.drop τ)) :
    coreProgram.Rel rd "shared_selector_tables" [eqt, gt, z, z1, gsq, gen ^ (μ - τ)] [] := by
  have hsql : gSquaresList.length = 34 := by simp [gSquaresList]
  exact shared_selector_tables_complete_holds rd eqt gt z z1 gsq (μ - τ) _ _ _ (by omega)
    (by simp; omega) (by simp; omega) (by simp [hsql]; omega) hzv hz1v hsqv hrun hpad

theorem vt_good_mul {σ : Val} {S : List Atom} {d x y : ℕ}
    (h : GoodS rd S w σ (fixNe (.atom (.mul (.n d) (.n x) (.n y))))) (hx : x < d) (hy : y < d) :
    σ (.n d) = σ (.n x) * σ (.n y) := by
  simp only [GoodS, fixNe, Good] at h
  rwa [ite_pos' ⟨hx, hy⟩] at h

theorem vt_good_div {σ : Val} {S : List Atom} {d x y : ℕ}
    (h : GoodS rd S w σ (fixNe (.atom (.mul (.n d) (.n x) (.n y))))) (hx : d < x) :
    σ (.n x) = σ (.n d) * (σ (.n y))⁻¹ := by
  simp only [GoodS, fixNe, Good] at h
  rwa [ite_neg' (show ¬ (x < d ∧ y < d) by omega)] at h

theorem vt_good_rc {σ : Val} {S : List Atom} {x y t1 t2 k : ℕ}
    (h : GoodS rd S w σ (fixNe (.atom (.rangeCheck (.n x) (.n y) (.n t1) (.n t2) (.n k))))) (hk : k < y) :
    σ (.n t1) = rdAt rd (σ (.n x)) 0 ∧ σ (.n t2) = rdAt rd (σ (.n y)) 0 ∧
      σ (.n y) = σ (.n k) * (σ (.n x))⁻¹ := by
  simp only [GoodS, fixNe, Good] at h
  rwa [ite_pos' hk] at h

theorem vtShAT_rest : ∀ t < 6, stmtsEqb (((vtAt (vtShA t)).take 15).filter (fun s ↦ !autoB s))
    [.atom (.mul (.n (val% «verify_tables» "g_bus_mu")) (.n (vtShV t)) (.n (28 + t))),
      .atom (.rangeCheck (.n (vtShV t + 1)) (.n (vtShV t + 3)) (.n (vtShV t + 4)) (.n (vtShV t + 5))
        (.n (vtShV t + 2)))] = true := by
  decide +kernel

theorem vtShCT_rest : ∀ t < 6, stmtsEqb (((vtAt (vtShC t)).take 4).filter (fun s ↦ !autoB s))
    [.call "shared_selector_tables" [.n (vtEqV t), .n (vtGV t), .n (vtShZ t), .n (vtShZ t + 1),
      .n (vtShZ t + 2), .n (vtShLen t)] []] = true := by
  decide +kernel

local notation "σv" => vtσ rd w args

/-- **Table `t`'s run and allocations.** -/
theorem vtc_shA (hl : args.length = 21) (hlow : LowDefB 14 rd) {t μ τ : ℕ} (ht : t < 6)
    (hkb : σv (.n (28 + t)) = gen ^ τ) (h9 : σv (.n (val% «verify_tables» "g_bus_mu")) = gen ^ μ) (hμ33 : μ < 33)
    (hτμ : τ ≤ μ) :
    (∀ s ∈ (vtPre.drop (vtShA t)).take 15, VSH (coreProgram.Rel rd) rd σv s) ∧
      σv (.n (vtShLen t)) = gen ^ (μ - τ) ∧
      σv (.n (vtShV t + 10)) = gen ^ (8 * (μ - τ + 1)) ∧
      σv (.n (vtShV t + 14)) = gen ^ (4 * (μ - τ + 1)) ∧
      σv (.n (vtEqV t)) = w (vtShV t + 11) ∧ σv (.n (vtGV t)) = w (vtShV t + 15) := by
  obtain ⟨eL, eE, eG⟩ := vtSh_vals t ht
  have hv : 579 ≤ vtShV t := by unfold vtShV; omega
  have hG : ∀ s ∈ vtShAT t, GoodS rd vtSL w σv (fixNe s) := fun s hs ↦
    vt_goodS hl (vt_mem_slice (n := vtShA t) (by rw [vtPre_drop]; exact vtShAT_check t ht) hs)
  set v := vtShV t with hvdef
  have g0 := hG (.atom (.mul (.n (val% «verify_tables» "g_bus_mu")) (.n v) (.n (28 + t)))) (by simp [vtShAT, v])
  have g1 := hG (.atom (.copy (.n (v + 1)) (.n v))) (by simp [vtShAT, v])
  have g2 := hG (.atom (.const (.n (v + 2)) vtW33)) (by simp [vtShAT, v])
  have g3 := hG (.atom (.rangeCheck (.n (v + 1)) (.n (v + 3)) (.n (v + 4)) (.n (v + 5)) (.n (v + 2))))
    (by simp [vtShAT, v])
  have g4 := hG (.atom (.const (.n (v + 6)) (word 2 0))) (by simp [vtShAT, v])
  have g5 := hG (.atom (.mul (.n (v + 7)) (.n (v + 1)) (.n (v + 6)))) (by simp [vtShAT, v])
  have g6 := hG (.atom (.mul (.n (v + 8)) (.n (v + 7)) (.n (v + 7)))) (by simp [vtShAT, v])
  have g7 := hG (.atom (.mul (.n (v + 9)) (.n (v + 8)) (.n (v + 8)))) (by simp [vtShAT, v])
  have g8 := hG (.atom (.mul (.n (v + 10)) (.n (v + 9)) (.n (v + 9)))) (by simp [vtShAT, v])
  have g9 := hG (.atom (.hint (.allocDyn (.n (v + 11)) (.n (v + 10))))) (by simp [vtShAT, v])
  have g10 := hG (.atom (.copy (.n (v + 12)) (.n (v + 11)))) (by simp [vtShAT, v])
  have g11 := hG (.atom (.mul (.n (v + 13)) (.n (v + 7)) (.n (v + 7)))) (by simp [vtShAT, v])
  have g12 := hG (.atom (.mul (.n (v + 14)) (.n (v + 13)) (.n (v + 13)))) (by simp [vtShAT, v])
  have g13 := hG (.atom (.hint (.allocDyn (.n (v + 15)) (.n (v + 14))))) (by simp [vtShAT, v])
  have g14 := hG (.atom (.copy (.n (v + 16)) (.n (v + 15)))) (by simp [vtShAT, v])
  replace g0 := vt_good_div g0 (by omega)
  replace g3 := vt_good_rc g3 (by omega)
  replace g5 := vt_good_mul g5 (by omega) (by omega)
  replace g6 := vt_good_mul g6 (by omega) (by omega)
  replace g7 := vt_good_mul g7 (by omega) (by omega)
  replace g8 := vt_good_mul g8 (by omega) (by omega)
  replace g11 := vt_good_mul g11 (by omega) (by omega)
  replace g12 := vt_good_mul g12 (by omega) (by omega)
  simp only [fixNe, GoodS, Good] at g1 g2 g4 g9 g10 g13 g14
  have ev : σv (.n v) = gen ^ (μ - τ) := by rw [g0, h9, hkb, gen_pow_div hτμ]
  have ec : σv (.n (v + 1)) = gen ^ (μ - τ) := by rw [g1, ev]
  have e1 : σv (.n (v + 7)) = gen ^ (μ - τ + 1) := by rw [g5, g4, ec, word_gen, pow_succ]
  obtain ⟨r1, r2, r3⟩ := g3
  obtain ⟨hrc, -⟩ := rc_holds (κ := 14) hlow r1 r2 r3 ec (by rw [g2, vtW33_gen]) (by omega)
    (by norm_num)
  refine ⟨?_, by rw [eL, ec], ?_, ?_, by rw [eE, g10, g9], by rw [eG, g14, g13]⟩
  · refine vt_blockR hl (vtShA t) 15 _ (vtShAT_rest t ht) fun s hs _ ↦ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact mulDiv_holds (rd := rd) g0 (by rw [hkb]; exact gen_pow_ne_zero _)
    · exact hrc
  · rw [g8, g7, g6, e1]; ring
  · rw [g12, g11, e1]; ring

/-- **Table `t`'s products and `shared_selector_tables` call.** -/
theorem vtc_shC (hl : args.length = 21) {t μ τ : ℕ} (ht : t < 6) {point : List E}
    (hμ : point.length = μ) (hμ33 : μ < 33) (hτμ : τ ≤ μ) (hkb : σv (.n (28 + t)) = gen ^ τ)
    (hlen : σv (.n (vtShLen t)) = gen ^ (μ - τ))
    (hz : ReadsAt rd (σv (.n (val% «verify_tables» "zeta"))) point)
    (hz1 : ReadsAt rd (σv (.n (val% «verify_tables» "zeta1"))) (point.map (1 + ·)))
    (hsq : ReadsAt rd (σv (.n (val% «verify_tables» "g_squares"))) gSquaresList)
    (hrun : RunTables rd (σv (.n (vtEqV t))) (σv (.n (vtGV t))) (μ - τ) (point.drop τ)
      ((point.map (1 + ·)).drop τ) ((gSquaresList.drop τ).take (μ - τ)))
    (hpad : RunPads rd (σv (.n (vtEqV t))) (σv (.n (vtGV t))) (μ - τ) (point.drop τ)) :
    ∀ s ∈ (vtPre.drop (vtShC t)).take 4, VSH (coreProgram.Rel rd) rd σv s := by
  have hG : ∀ s ∈ vtShCT t, GoodS rd vtSL w σv (fixNe s) := fun s hs ↦
    vt_goodS hl (vt_mem_slice (n := vtShC t) (by rw [vtPre_drop]; exact vtShCT_check t ht) hs)
  have hz0 : 804 ≤ vtShZ t := by unfold vtShZ; omega
  set z := vtShZ t with hzdef
  have g0 := hG (.atom (.mul (.n z) (.n (val% «verify_tables» "zeta")) (.n (28 + t)))) (by simp [vtShCT, z])
  have g1 := hG (.atom (.mul (.n (z + 1)) (.n (val% «verify_tables» "zeta1")) (.n (28 + t)))) (by simp [vtShCT, z])
  have g2 := hG (.atom (.mul (.n (z + 2)) (.n (val% «verify_tables» "g_squares")) (.n (28 + t)))) (by simp [vtShCT, z])
  replace g0 := vt_good_mul g0 (by omega) (by omega)
  replace g1 := vt_good_mul g1 (by omega) (by omega)
  replace g2 := vt_good_mul g2 (by omega) (by omega)
  refine vt_blockR hl (vtShC t) 4 _ (vtShCT_rest t ht) fun s hs _ ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  show coreProgram.Rel rd _ _ _
  simp only [List.map_cons, List.map_nil]
  rw [g0, g1, g2, hkb, hlen]
  exact sh_call hμ hμ33 hτμ (tbReadsAt_drop hz τ) (tbReadsAt_drop hz1 τ)
    (tbReadsAt_take (tbReadsAt_drop hsq τ) _) hrun hpad

end
end LeanVM.Guest.B1.Tables
