/-
  LeanVM.Guest.B1.Tables.Kids.Shared

  `shared_selector_tables` loads from any region holding the runs it reads and writes.
-/

module

public import LeanVM.Guest.B1.Tables.Kids.Loop9

/-!
# `shared_selector_tables`, loading from a region

`shared_selector_tables_relIn`: a run of `n = 4q + r < 64` coordinates: its loop over the `q`
full nibbles (`loop9_relIn`) and its partial nibble `sel_partial_nibble__L{r}` at `q`
(`sel_partial_nibble_relIn`), the runs `eqt` (`32⌈n/4⌉` words), `gt` (`16⌈n/4⌉`), `z`, `z1`,
`gsq` (`n`) in `R`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- `shared_selector_tables`' dispatch of the partial nibble. -/
def ssDisp : Stmt :=
  .dispatch (.n 20) ["sel_partial_nibble__L0", "sel_partial_nibble__L1",
      "sel_partial_nibble__L2", "sel_partial_nibble__L3"] [.n 49, .n 50, .n 51, .n 52, .n 53]
      [.n 54]

theorem ssPre_eq : ssPre = ssPre.dropLast ++ [ssDisp] := by
  simp [ssPre, ssDisp]

theorem ss_flat : ssPre.all Stmt.flat = true := by decide +kernel

theorem ss_noDisp : ssPre.dropLast.all noDispB = true := by decide +kernel

theorem ss_noLoad : ssPre.filterMap Stmt.loadS = [] := by decide +kernel

theorem ss_calls : ssPre.dropLast.filterMap Main.Stmt.callS =
    [(some (.n 44), "__loop8", [.n 45, .n 39, .n 0, .n 2, .n 3, .n 1, .n 4], [])] := by
  decide +kernel

theorem ceil4 {n q r : ℕ} (hn : n = 4 * q + r) (hr : r < 4) :
    (n + 3) / 4 = if r = 0 then q else q + 1 := by
  split <;> omega

/-- **`shared_selector_tables` loads from `R`.** -/
theorem shared_selector_tables_relIn {rd : Reader} {R : ℕ → Prop} {eqt gt z z1 gsq : E} {n : ℕ}
    (hn : n < 64) {rets : List E} (he : PtrIn R eqt (32 * ((n + 3) / 4)))
    (hgt : PtrIn R gt (16 * ((n + 3) / 4))) (hz : PtrIn R z n) (hz1 : PtrIn R z1 n)
    (hgs : PtrIn R gsq n)
    (h : coreProgram.Rel rd "shared_selector_tables" [eqt, gt, z, z1, gsq, gen ^ n] rets) :
    coreProgram.RelIn rd R "shared_selector_tables" [eqt, gt, z, z1, gsq, gen ^ n] rets := by
  obtain ⟨fn, hf, hp, hb⟩ := ssFound
  refine relIn_of_flatRel hf hb ss_flat h fun σ hpar hh ↦ ?_
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := hpar
  rw [hb, holdsList_append, holdsList_noRet _ ssPre_noRet] at hh
  obtain ⟨hpre, -⟩ := hh
  simp only [ssPre, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, and_true] at hpre
  obtain ⟨p6, p7, p8, p9, p10, p11, c12, c13, m14, a15, c16, c17, m18, a19, m20, c21, c22, m23,
    a24, c25, c26, m27, a28, m29, c30, c31, m32, a33, m34, c35, c36, m37, a38, m39, m40, m41, m42,
    e42, c43, a44, c45, -, hloop, m46, m47, m48, m49, m50, m51, m52, m53, hdisp⟩ := hpre
  let f : ℕ → Bool := fun k ↦ decide (σ (.n (6 + k)) = 1)
  have pin : ∀ k < 6, σ (.n (6 + k)) * σ (.n (6 + k)) = σ (.n (6 + k)) := by
    intro k hk
    interval_cases k
    · exact p6.symm
    · exact p7.symm
    · exact p8.symm
    · exact p9.symm
    · exact p10.symm
    · exact p11.symm
  set r := bitsVal f 2 with hrdef
  set q := bitsVal (fun k ↦ f (k + 2)) 4 with hqdef
  have hr4 : r < 4 := bitsVal_lt f 2
  have hq16 : q < 16 := bitsVal_lt _ 4
  have hrg : σ (.n 20) = gen ^ r := by
    have := ss_prod (b := fun j ↦ σ (.n (6 + j))) (n := 2) (by norm_num)
      (fun j hj => pin j (by omega))
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Nat.reduceAdd] at this
    rw [m20, a15, a19, c12, c16, m14, m18, c13, c17, tb_word_one, this]
  have hqg : σ (.n 39) = gen ^ q := by
    have := ss_prod (b := fun j ↦ σ (.n (6 + (j + 2)))) (n := 4) le_rfl
      (fun j hj => pin (j + 2) (by omega))
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Nat.reduceAdd] at this
    rw [m39, m34, m29, a24, a28, a33, a38, c21, c25, c30, c35, m23, m27, m32, m37, c22, c26, c31,
      c36, tb_word_one, this]
  have hq4 : σ (.n 41) = gen ^ (4 * q) := by rw [m41, m40, hqg]; ring
  have hq16' : σ (.n 47) = gen ^ (16 * q) := by rw [m47, m46, hq4]; ring
  have hnqr : n = 4 * q + r := by
    have h1 : gen ^ n = gen ^ (4 * q + r) := by
      rw [← p5, ← e_add_eq_zero_iff.mp e42, m42, hq4, hrg, ← pow_add]
    exact gen_pow_inj (by omega) (by omega) h1
  have hceil := ceil4 hnqr hr4
  -- the dispatch: `σ 20 = g^r`
  obtain ⟨jd, hjd, hx, hcall⟩ := hdisp
  have hjd4 : jd < 4 := by simpa using hjd
  have hjr : jd = r := by
    rw [hrg, gen_pow_eq_ofK] at hx
    exact gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
      (ofK_injective hx.symm)
  rw [← hjr] at hnqr hceil
  refine ⟨fun s hs ↦ ?_, by rw [ss_noLoad]; simp, fun c hc ht ↦ ?_⟩
  · rw [ssPre_eq, List.mem_append, List.mem_singleton] at hs
    rcases hs with hs | rfl
    · exact dispOk_of_noDisp (List.all_eq_true.mp ss_noDisp s hs)
    · exact ⟨_, hjd, by omega, hx⟩
  · rw [ssPre_eq, List.filterMap_append, filterMap_callSF ss_noDisp, ss_calls] at hc
    simp only [ssDisp, Stmt.callSF, List.filterMap_cons, List.filterMap_nil, List.cons_append,
      List.nil_append, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl
    · -- the loop over the full nibbles
      simp only [Main.mkCall, decide_eq_true_eq] at ht ⊢
      have hq0 : 0 < q := by
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · exfalso; apply ht
          rw [a44, c43, tb_word_one, hqg, h0, pow_zero, e_add_eq_zero_iff]
        · exact h0
      have hrel := hloop ht
      simp only [List.map_cons, List.map_nil, c45, tb_word_one, hqg, p0, p1, p2, p3, p4] at hrel ⊢
      obtain ⟨d, hd⟩ := hrel
      have := loop9_relIn (R := R) (K := q)
        (ptrIn_mono he (by rw [hceil]; split <;> omega))
        (ptrIn_mono hgt (by rw [hceil]; split <;> omega))
        (ptrIn_mono hz (by omega)) (ptrIn_mono hz1 (by omega)) (ptrIn_mono hgs (by omega))
        d 0 hq0 (by rw [pow_zero]; exact hd)
      rwa [pow_zero] at this
    · -- the partial nibble
      simp only [Main.mkCall]
      have hlog : logG (σ (.n 20)) = jd := by rw [hx]; exact logG_spec (by omega)
      rw [hlog, List.getD_eq_getElem _ _ hjd, lName_sel_partial jd hjd4]
      simp only [List.map_cons, List.map_nil, m49, m48, m50, m51, m52, m53, hq16', hq4, p0, p1, p2,
        p3, p4, mul_assoc, ← pow_add]
      rw [lName_sel_partial jd hjd4] at hcall
      simp only [List.map_cons, List.map_nil, m49, m48, m50, m51, m52, m53, hq16', hq4, p0, p1, p2,
        p3, p4, mul_assoc, ← pow_add] at hcall
      refine sel_partial_nibble_relIn hjd4 (ptrIn_mul (ptrIn_mono he ?_))
        (fun hw ↦ ptrIn_mul (ptrIn_mono hgt ?_)) (ptrIn_mul (ptrIn_mono hz (by omega)))
        (ptrIn_mul (ptrIn_mono hz1 (by omega))) (ptrIn_mul (ptrIn_mono hgs (by omega))) hcall
      · rw [hceil]; interval_cases jd <;> simp <;> omega
      · rw [hceil]; interval_cases jd <;> simp at hw ⊢ <;> omega

end
end LeanVM.Guest.B1.Tables
