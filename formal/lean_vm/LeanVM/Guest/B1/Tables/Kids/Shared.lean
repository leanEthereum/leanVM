/-
  LeanVM.Guest.B1.Tables.Kids.Shared

  `shared_selector_tables` loads from any region holding the runs it reads and writes.
-/

module

public import LeanVM.Guest.B1.Tables.Kids.Loop9
public import LeanVM.Guest.Data.NameStrings

/-!
# `shared_selector_tables`, loading from a region

`shared_selector_tables_relIn`: a run of `n = 4q + r < 64` coordinates: its loop over the `q`
full nibbles (`loop9_relIn`) and its partial nibble `sel_partial_nibble__L{r}` at `q`
(`sel_partial_nibble_relIn`), the runs `eqt` (`32⌈n/4⌉` words), `gt` (`16⌈n/4⌉`), `z`, `z1`,
`gsq` (`n`) in `R`, `eqt` and `gt` the two tables it returns.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value LeanVM.Core.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- `shared_selector_tables`' dispatch of the partial nibble. -/
def ssDisp : Stmt :=
  .dispatch (.n 18) ["sel_partial_nibble__L0", "sel_partial_nibble__L1",
      "sel_partial_nibble__L2", "sel_partial_nibble__L3"] [.n 56, .n 57, .n 58, .n 59, .n 60]
      [.n 61]

/-- `shared_selector_tables`' copies of its tables, returned. -/
def ssCopies : List Stmt := [.atom (.copy (.n 62) (.n 48)), .atom (.copy (.n 63) (.n 49))]

/-- `shared_selector_tables`' statements before its dispatch. -/
def ssHead : List Stmt := ssPre.take (ssPre.length - 3)

theorem ssPre_eq : ssPre = ssHead ++ ssDisp :: ssCopies := rfl

theorem ss_flat : ssPre.all Stmt.flat = true := by decide +kernel

theorem ss_noDisp : (ssHead ++ ssCopies).all noDispB = true := by decide +kernel

theorem ss_noLoad : ssPre.filterMap Stmt.loadS = [] := by decide +kernel

theorem ss_calls : (ssHead ++ ssCopies).filterMap Main.Stmt.callS =
    [(some (.n 51), name% «shared_selector_tables_loop0», [.n 52, .n 37, .n 48, .n 0, .n 1, .n 49,
        .n 2], [])] := by
  decide +kernel

theorem ceil4 {n q r : ℕ} (hn : n = 4 * q + r) (hr : r < 4) :
    (n + 3) / 4 = if r = 0 then q else q + 1 := by
  split <;> omega

/-- **`shared_selector_tables` loads from `R`**, its returned tables in `R`. -/
theorem shared_selector_tables_relIn {rd : Reader} {R : ℕ → Prop} {eqt gt z z1 gsq : E} {n : ℕ}
    (hn : n < 64) (he : PtrIn R eqt (32 * ((n + 3) / 4)))
    (hgt : PtrIn R gt (16 * ((n + 3) / 4))) (hz : PtrIn R z n) (hz1 : PtrIn R z1 n)
    (hgs : PtrIn R gsq n)
    (h : coreProgram.Rel rd "shared_selector_tables" [z, z1, gsq, gen ^ n] [eqt, gt]) :
    coreProgram.RelIn rd R "shared_selector_tables" [z, z1, gsq, gen ^ n] [eqt, gt] := by
  obtain ⟨fn, hf, hp, hb⟩ := ssFound
  refine relIn_of_flatRel hf hb ss_flat h fun σ hpar hh ↦ ?_
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨p0, p1, p2, p3⟩ := hpar
  rw [hb, holdsList_append, holdsList_noRet _ ssPre_noRet] at hh
  obtain ⟨hpre, hret⟩ := hh
  simp only [ssRets, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil, List.cons.injEq,
    and_true] at hret
  obtain ⟨r62, r63⟩ := hret
  simp only [ssPre, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, and_true] at hpre
  obtain ⟨p4, p5, p6, p7, p8, p9, c10, c11, m12, a13, c14, c15, m16, a17, m18, c19, c20, m21,
    a22, c23, c24, m25, a26, m27, c28, c29, m30, a31, m32, c33, c34, m35, a36, m37, m38, m39, m40,
    e40, c41, m42, m43, m44, m45, m46, m47, c50, a51, c52, -, hloop, m53, m54, m55, m56, m57, m58,
    m59, m60, hdisp, cp62, cp63⟩ := hpre
  have e48 : σ (.n 48) = eqt := by rw [← cp62, r62]
  have e49 : σ (.n 49) = gt := by rw [← cp63, r63]
  let f : ℕ → Bool := fun k ↦ decide (σ (.n (4 + k)) = 1)
  have pin : ∀ k < 6, σ (.n (4 + k)) * σ (.n (4 + k)) = σ (.n (4 + k)) := by
    intro k hk
    interval_cases k
    · exact p4.symm
    · exact p5.symm
    · exact p6.symm
    · exact p7.symm
    · exact p8.symm
    · exact p9.symm
  set r := bitsVal f 2 with hrdef
  set q := bitsVal (fun k ↦ f (k + 2)) 4 with hqdef
  have hr4 : r < 4 := bitsVal_lt f 2
  have hq16 : q < 16 := bitsVal_lt _ 4
  have hrg : σ (.n 18) = gen ^ r := by
    have := ss_prod (b := fun j ↦ σ (.n (4 + j))) (n := 2) (by norm_num)
      (fun j hj => pin j (by omega))
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Nat.reduceAdd] at this
    rw [m18, a13, a17, c10, c14, m12, m16, c11, c15, tb_word_one, this]
  have hqg : σ (.n 37) = gen ^ q := by
    have := ss_prod (b := fun j ↦ σ (.n (4 + (j + 2)))) (n := 4) le_rfl
      (fun j hj => pin (j + 2) (by omega))
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Nat.reduceAdd] at this
    rw [m37, m32, m27, a22, a26, a31, a36, c19, c23, c28, c33, m21, m25, m30, m35, c20, c24, c29,
      c34, tb_word_one, this]
  have hq4 : σ (.n 39) = gen ^ (4 * q) := by rw [m39, m38, hqg]; ring
  have hq16' : σ (.n 54) = gen ^ (16 * q) := by rw [m54, m53, hq4]; ring
  have hnqr : n = 4 * q + r := by
    have h1 : gen ^ n = gen ^ (4 * q + r) := by
      rw [← p3, ← e_add_eq_zero_iff.mp e40, m40, hq4, hrg, ← pow_add]
    exact gen_pow_inj (by omega) (by omega) h1
  have hceil := ceil4 hnqr hr4
  -- the dispatch: `σ 18 = g^r`
  obtain ⟨jd, hjd, hx, hcall⟩ := hdisp
  have hjd4 : jd < 4 := by simpa using hjd
  have hjr : jd = r := by
    rw [hrg, gen_pow_eq_ofK] at hx
    exact gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
      (ofK_injective hx.symm)
  rw [← hjr] at hnqr hceil
  refine ⟨fun s hs ↦ ?_, by rw [ss_noLoad]; simp, fun c hc ht ↦ ?_⟩
  · rw [ssPre_eq, List.mem_append, List.mem_cons] at hs
    rcases hs with hs | rfl | hs
    · exact dispOk_of_noDisp (List.all_eq_true.mp ss_noDisp s (List.mem_append_left _ hs))
    · exact ⟨_, hjd, by omega, hx⟩
    · exact dispOk_of_noDisp (List.all_eq_true.mp ss_noDisp s (List.mem_append_right _ hs))
  · rw [ssPre_eq, List.filterMap_append, List.filterMap_cons] at hc
    have hcs := ss_calls
    rw [List.filterMap_append] at hcs
    rw [filterMap_callSF (List.all_eq_true.mpr fun s hs ↦
        List.all_eq_true.mp ss_noDisp s (List.mem_append_left _ hs)),
      filterMap_callSF (List.all_eq_true.mpr fun s hs ↦
        List.all_eq_true.mp ss_noDisp s (List.mem_append_right _ hs))] at hc
    have hcopy : ssCopies.filterMap Main.Stmt.callS = [] := by decide +kernel
    rw [hcopy, List.append_nil] at hcs
    rw [hcopy, hcs] at hc
    simp only [ssDisp, Stmt.callSF, List.cons_append, List.nil_append, List.map_cons,
      List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · -- the loop over the full nibbles
      simp only [Main.mkCall, decide_eq_true_eq] at ht ⊢
      have hq0 : 0 < q := by
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · exfalso; apply ht
          rw [a51, c50, tb_word_one, hqg, h0, pow_zero, e_add_eq_zero_iff]
        · exact h0
      have hrel := hloop ht
      simp only [List.map_cons, List.map_nil, c52, tb_word_one, hqg, p0, p1, p2, e48,
        e49] at hrel ⊢
      obtain ⟨d, hd⟩ := hrel
      have := loop9_relIn (R := R) (K := q)
        (ptrIn_mono he (by rw [hceil]; split <;> omega))
        (ptrIn_mono hgt (by rw [hceil]; split <;> omega))
        (ptrIn_mono hz (by omega)) (ptrIn_mono hz1 (by omega)) (ptrIn_mono hgs (by omega))
        d 0 hq0 (by rw [pow_zero]; exact hd)
      rwa [pow_zero] at this
    · -- the partial nibble
      simp only [Main.mkCall]
      have hlog : logG (σ (.n 18)) = jd := by rw [hx]; exact logG_spec (by omega)
      rw [hlog, List.getD_eq_getElem _ _ hjd, lName_sel_partial jd hjd4]
      simp only [List.map_cons, List.map_nil, m56, m55, m57, m58, m59, m60, hq16', hq4, p0, p1,
        p2, e48, e49, mul_assoc, ← pow_add]
      rw [lName_sel_partial jd hjd4] at hcall
      simp only [List.map_cons, List.map_nil, m56, m55, m57, m58, m59, m60, hq16', hq4, p0, p1,
        p2, e48, e49, mul_assoc, ← pow_add] at hcall
      refine sel_partial_nibble_relIn hjd4 (ptrIn_mul (ptrIn_mono he ?_))
        (fun hw ↦ ptrIn_mul (ptrIn_mono hgt ?_)) (ptrIn_mul (ptrIn_mono hz (by omega)))
        (ptrIn_mul (ptrIn_mono hz1 (by omega))) (ptrIn_mul (ptrIn_mono hgs (by omega))) hcall
      · rw [hceil]; interval_cases jd <;> simp <;> omega
      · rw [hceil]; interval_cases jd <;> simp at hw ⊢ <;> omega

end
end LeanVM.Guest.B1.Tables
