/-
  LeanVM.Guest.B1.Tables.Kids.Shared

  `shared_selector_tables` loads from any region holding the runs it reads and writes.
-/

module

public import LeanVM.Guest.B1.Tables.Kids.Loop9
public import LeanVM.Guest.Data.NameStrings

/-!
# `shared_selector_tables`, loading from a region

`shared_selector_tables_relIn`: a run of `n = 4q + r < 64` coordinates split as `g^q`: its loop
over the `q` full nibbles (`loop9_relIn`) and its partial nibble `sel_partial_nibble__L{r}` at `q`
(`sel_partial_nibble_relIn`), the runs `eqt` (`32⌈n/4⌉` words), `gt` (`16⌈n/4⌉`), `z`, `z1`,
`gsq` (`n`) in `R`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value LeanVM.Core.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- `shared_selector_tables`' dispatch of the partial nibble. -/
def ssDisp : Stmt :=
  .dispatch (.n 9) ["sel_partial_nibble__L0", "sel_partial_nibble__L1",
      "sel_partial_nibble__L2", "sel_partial_nibble__L3"] [.n 20, .n 21, .n 22, .n 23, .n 24]
      [.n 25]

theorem ssPre_eq : ssPre = ssPre.dropLast ++ [ssDisp] := by
  simp [ssPre, ssDisp]

theorem ss_flat : ssPre.all Stmt.flat = true := by decide +kernel

theorem ss_noDisp : ssPre.dropLast.all noDispB = true := by decide +kernel

theorem ss_noLoad : ssPre.filterMap Stmt.loadS = [] := by decide +kernel

theorem ss_calls : ssPre.dropLast.filterMap Main.Stmt.callS =
    [(some (.n 11), name% «shared_selector_tables_loop0», [.n 12, .n 6, .n 0, .n 2, .n 3, .n 1,
        .n 4], [])] := by
  decide +kernel

theorem ceil4 {n q r : ℕ} (hn : n = 4 * q + r) (hr : r < 4) :
    (n + 3) / 4 = if r = 0 then q else q + 1 := by
  split <;> omega

/-- **`shared_selector_tables` loads from `R`.** -/
theorem shared_selector_tables_relIn {rd : Reader} {R : ℕ → Prop} {eqt gt z z1 gsq : E} {n : ℕ}
    {rets : List E} (he : PtrIn R eqt (32 * ((n + 3) / 4)))
    (hgt : PtrIn R gt (16 * ((n + 3) / 4))) (hz : PtrIn R z n) (hz1 : PtrIn R z1 n)
    (hgs : PtrIn R gsq n)
    (h : coreProgram.Rel rd "shared_selector_tables" [eqt, gt, z, z1, gsq, gen ^ n, gen ^ (n / 4)]
      rets) :
    coreProgram.RelIn rd R "shared_selector_tables" [eqt, gt, z, z1, gsq, gen ^ n, gen ^ (n / 4)]
      rets := by
  obtain ⟨fn, hf, hp, hb⟩ := ssFound
  refine relIn_of_flatRel hf hb ss_flat h fun σ hpar hh ↦ ?_
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := hpar
  rw [hb, holdsList_append, holdsList_noRet _ ssPre_noRet] at hh
  obtain ⟨hpre, -⟩ := hh
  simp only [ssPre, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hpre
  obtain ⟨m7, m8, m5, c10, a11, c12, -, hloop, m13, m14, -, -, m15, m16, m17, m18, m19, m20,
    hdisp⟩ := hpre
  set q := n / 4 with hqd
  set r := n % 4 with hrd
  have hr4 : r < 4 := Nat.mod_lt _ (by norm_num)
  have hnqr : n = 4 * q + r := by omega
  have hq4 : σ (.n 8) = gen ^ (4 * q) := by rw [m8, m7, p6]; ring
  have hq16' : σ (.n 14) = gen ^ (16 * q) := by rw [m14, m13, hq4]; ring
  have e9 : σ (.n 9) = gen ^ r := by
    refine mul_right_cancel₀ (gen_pow_ne_zero (4 * q)) ?_
    have e := m5
    rw [p5, hq4] at e
    rw [← e, ← pow_add, show r + 4 * q = n by omega]
  have hceil := ceil4 hnqr hr4
  obtain ⟨jd, hjd, hx, hcall⟩ := hdisp
  have hjd4 : jd < 4 := by simpa using hjd
  have hjr : jd = r := by
    rw [e9, gen_pow_eq_ofK] at hx
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
          rw [a11, c10, tb_word_one, p6, h0, pow_zero, e_add_eq_zero_iff]
        · exact h0
      have hrel := hloop ht
      simp only [List.map_cons, List.map_nil, c12, tb_word_one, p6, p0, p1, p2, p3, p4] at hrel ⊢
      obtain ⟨d, hd⟩ := hrel
      have := loop9_relIn (R := R) (K := q)
        (ptrIn_mono he (by rw [hceil]; split <;> omega))
        (ptrIn_mono hgt (by rw [hceil]; split <;> omega))
        (ptrIn_mono hz (by omega)) (ptrIn_mono hz1 (by omega)) (ptrIn_mono hgs (by omega))
        d 0 hq0 (by rw [pow_zero]; exact hd)
      rwa [pow_zero] at this
    · -- the partial nibble
      simp only [Main.mkCall]
      have hlog : logG (σ (.n 9)) = jd := by rw [hx]; exact logG_spec (by omega)
      rw [hlog, List.getD_eq_getElem _ _ hjd, lName_sel_partial jd hjd4]
      simp only [List.map_cons, List.map_nil, m16, m15, m17, m18, m19, m20, hq16', hq4, p0, p1, p2,
        p3, p4, mul_assoc, ← pow_add]
      rw [lName_sel_partial jd hjd4] at hcall
      simp only [List.map_cons, List.map_nil, m16, m15, m17, m18, m19, m20, hq16', hq4, p0, p1, p2,
        p3, p4, mul_assoc, ← pow_add] at hcall
      refine sel_partial_nibble_relIn hjd4 (ptrIn_mul (ptrIn_mono he ?_))
        (fun hw ↦ ptrIn_mul (ptrIn_mono hgt ?_)) (ptrIn_mul (ptrIn_mono hz (by omega)))
        (ptrIn_mul (ptrIn_mono hz1 (by omega))) (ptrIn_mul (ptrIn_mono hgs (by omega))) hcall
      · rw [hceil]; interval_cases jd <;> simp <;> omega
      · rw [hceil]; interval_cases jd <;> simp at hw ⊢ <;> omega

end
end LeanVM.Guest.B1.Tables
