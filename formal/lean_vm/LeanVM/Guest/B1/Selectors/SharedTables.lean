/-
  LeanVM.Guest.B1.Selectors.SharedTables

  B1 for `shared_selector_tables`: a selector run's nibble tables, the full nibbles by its loop
  `shared_selector_tables_loop0` and the last partial one by `sel_partial_nibble`.
-/

module

public import LeanVM.Guest.B1.Selectors.Nibble
public import LeanVM.Guest.B1.Selectors.SelPartial
public import LeanVM.Guest.B1.Selectors.BlockSelectorTab
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.CoreData

/-!
# `shared_selector_tables` (TRIAGE G #48)

`shared_selector_tables(eq_tab, g_tab, zeta_hi, zeta1_hi, gsq_hi, len_g)` (G:2103-2126) hints the
six bits of `len_g`'s exponent, pins them Boolean, rebuilds `r_g = g^r` from the low two and
`q_g = g^q` from the high four, asserts `q_g^4·r_g = len_g` (so `len_g = g^n`, `n = 4q + r < 64`),
runs its loop over `x = g^j`, `j < q` (`shared_selector_tables_loop0`: nibble `j`'s eq levels and
`g` table by the inline `sel_eq_nibble`, `sel_g_nibble`), then dispatches the partial nibble `q` of
width `r` to `sel_partial_nibble__L{r}`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The loop -/

/-- `shared_selector_tables_loop0`'s statements before its conditional call. -/
def lpPre : List Stmt :=
  [.atom (.mul (.n 7) (.n 0) (.n 0)), .atom (.mul (.n 8) (.n 7) (.n 7)),
    .atom (.mul (.n 9) (.n 8) (.n 8)), .atom (.mul (.n 10) (.n 9) (.n 9)),
    .atom (.mul (.n 11) (.n 2) (.n 10)), .atom (.mul (.n 12) (.n 11) (.n 10)),
    .atom (.mul (.n 13) (.n 3) (.n 8)), .atom (.mul (.n 14) (.n 4) (.n 8))] ++
  nbEq 15 (.n 13) (.n 14) (.n 12) 4 ++
  [.atom (.mul (.n 51) (.n 5) (.n 10)), .atom (.mul (.n 52) (.n 6) (.n 8))] ++
  nbG 53 (.n 52) (.n 51) 4 ++
  [.atom (.const (.n 72) (word 2 0)), .atom (.mul (.n 73) (.n 0) (.n 72)),
    .atom (.add (.n 74) (.n 73) (.n 1)), .atom (.const (.n 75) (word 2 0)),
    .atom (.mul (.n 76) (.n 0) (.n 75))]

/-- `shared_selector_tables_loop0`'s body. -/
def lpBody : List Stmt :=
  lpPre ++ [.callIf (.n 74) name% «shared_selector_tables_loop0» [.n 76, .n 1, .n 2, .n 3, .n 4,
      .n 5, .n 6], .ret []]

noncomputable def lpCheck : Bool :=
  match coreProgram.find? name% «shared_selector_tables_loop0» with
  | some fn => decide (fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6]) &&
      tbStmtsEqb fn.body lpBody
  | none => false

theorem lpCheck_eq : lpCheck = true := by decide +kernel

/-! ## The function -/

/-- `shared_selector_tables`'s statements before its dispatch. -/
def ssPre : List Stmt :=
  [.atom (.hint (.bitsExp (.n 5) 6 (.stack [.n 6, .n 7, .n 8, .n 9, .n 10, .n 11]))),
    .atom (.mul (.n 6) (.n 6) (.n 6)), .atom (.mul (.n 7) (.n 7) (.n 7)),
    .atom (.mul (.n 8) (.n 8) (.n 8)), .atom (.mul (.n 9) (.n 9) (.n 9)),
    .atom (.mul (.n 10) (.n 10) (.n 10)), .atom (.mul (.n 11) (.n 11) (.n 11)),
    .atom (.const (.n 12) (word 1 0)), .atom (.const (.n 13) (word (imFactor 0) 0)),
    .atom (.mul (.n 14) (.n 6) (.n 13)), .atom (.add (.n 15) (.n 12) (.n 14)),
    .atom (.const (.n 16) (word 1 0)), .atom (.const (.n 17) (word (imFactor 1) 0)),
    .atom (.mul (.n 18) (.n 7) (.n 17)), .atom (.add (.n 19) (.n 16) (.n 18)),
    .atom (.mul (.n 20) (.n 15) (.n 19)),
    .atom (.const (.n 21) (word 1 0)), .atom (.const (.n 22) (word (imFactor 0) 0)),
    .atom (.mul (.n 23) (.n 8) (.n 22)), .atom (.add (.n 24) (.n 21) (.n 23)),
    .atom (.const (.n 25) (word 1 0)), .atom (.const (.n 26) (word (imFactor 1) 0)),
    .atom (.mul (.n 27) (.n 9) (.n 26)), .atom (.add (.n 28) (.n 25) (.n 27)),
    .atom (.mul (.n 29) (.n 24) (.n 28)),
    .atom (.const (.n 30) (word 1 0)), .atom (.const (.n 31) (word (imFactor 2) 0)),
    .atom (.mul (.n 32) (.n 10) (.n 31)), .atom (.add (.n 33) (.n 30) (.n 32)),
    .atom (.mul (.n 34) (.n 29) (.n 33)),
    .atom (.const (.n 35) (word 1 0)), .atom (.const (.n 36) (word (imFactor 3) 0)),
    .atom (.mul (.n 37) (.n 11) (.n 36)), .atom (.add (.n 38) (.n 35) (.n 37)),
    .atom (.mul (.n 39) (.n 34) (.n 38)),
    .atom (.mul (.n 40) (.n 39) (.n 39)), .atom (.mul (.n 41) (.n 40) (.n 40)),
    .atom (.mul (.n 42) (.n 41) (.n 20)), .atom (.assertEq (.n 42) (.n 5)),
    .atom (.const (.n 43) (word 1 0)), .atom (.add (.n 44) (.n 43) (.n 39)),
    .atom (.const (.n 45) (word 1 0)),
    .callIf (.n 44) name% «shared_selector_tables_loop0» [.n 45, .n 39, .n 0, .n 2, .n 3, .n 1,
        .n 4],
    .atom (.mul (.n 46) (.n 41) (.n 41)), .atom (.mul (.n 47) (.n 46) (.n 46)),
    .atom (.mul (.n 48) (.n 0) (.n 47)), .atom (.mul (.n 49) (.n 48) (.n 47)),
    .atom (.mul (.n 50) (.n 1) (.n 47)), .atom (.mul (.n 51) (.n 2) (.n 41)),
    .atom (.mul (.n 52) (.n 3) (.n 41)), .atom (.mul (.n 53) (.n 4) (.n 41)),
    .dispatch (.n 20) ["sel_partial_nibble__L0", "sel_partial_nibble__L1",
      "sel_partial_nibble__L2", "sel_partial_nibble__L3"] [.n 49, .n 50, .n 51, .n 52, .n 53]
      [.n 54]]

noncomputable def ssCheck : Bool :=
  match coreProgram.find? "shared_selector_tables" with
  | some fn => decide (fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5]) &&
      tbStmtsEqb fn.body (ssPre ++ [.ret []])
  | none => false

theorem ssCheck_eq : ssCheck = true := by decide +kernel

theorem lpFound : ∃ fn : Fn, coreProgram.find? name% «shared_selector_tables_loop0» = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧ fn.body = lpBody := by
  have h := lpCheck_eq
  unfold lpCheck at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

theorem ssFound : ∃ fn : Fn, coreProgram.find? "shared_selector_tables" = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] ∧ fn.body = ssPre ++ [.ret []] := by
  have h := ssCheck_eq
  unfold ssCheck at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

theorem lpPre_noRet : Stmt.noRetList lpPre = true := by
  simp only [lpPre, tb_noRetList_append, nbEq_noRet, nbG_noRet]; rfl

theorem ssPre_noRet : Stmt.noRetList ssPre = true := rfl

/-- What one iteration of `shared_selector_tables_loop0` at `x` writes: for the four coordinates,
complements and shares read at `z·x^4`, `z1·x^4`, `gsq·x^4`, their eq levels at `eqt·x^32` and their
`g` table
at `gt·x^16`. -/
def LpB (rd : Reader) (eqt z z1 gt gsq x : E) : Prop :=
  ∀ zs zs1 gs : List E, zs.length = 4 → zs1.length = 4 → gs.length = 4 →
    TbReadsAt rd (z * x ^ 4) zs → TbReadsAt rd (z1 * x ^ 4) zs1 → TbReadsAt rd (gsq * x ^ 4) gs →
    TbReadsAt rd (eqt * x ^ 32) (eqLevels zs zs1) ∧ TbReadsAt rd (gt * x ^ 16) (gTable gs)

theorem lp_step {rd : Reader} {N eqt z z1 gt gsq : E} (d : ℕ) (x : E)
    (h : coreProgram.relN rd (d + 1) name% «shared_selector_tables_loop0» (x :: [N, eqt, z, z1, gt,
        gsq]) []) :
    LpB rd eqt z z1 gt gsq x ∧
      (x * gen + N ≠ 0 → coreProgram.relN rd d name% «shared_selector_tables_loop0» (x * gen :: [N,
          eqt, z, z1, gt, gsq]) []) := by
  obtain ⟨fn, hf, σ, hpar, hbody⟩ := h
  obtain ⟨fn', hf', hp, hb⟩ := lpFound
  rw [hf] at hf'
  obtain rfl := Option.some.inj hf'
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpar
  rw [hb, lpBody, holdsList_append, holdsList_noRet _ lpPre_noRet] at hbody
  obtain ⟨hpre, hcall⟩ := hbody
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil, and_true] at hcall
  have n0 : ∀ l : List Stmt, (∀ s ∈ l, ∃ a, s = Stmt.atom a) → Stmt.noRetList l = true := by
    intro l hl
    induction l with
    | nil => rfl
    | cons s l ih =>
      obtain ⟨a, rfl⟩ := hl s (by simp)
      simp only [Stmt.noRetList, Stmt.noRet, Bool.true_and]
      exact ih fun s hs => hl s (by simp [hs])
  rw [lpPre, tb_holdsList_append_noRet (by
      simp only [tb_noRetList_append, nbEq_noRet, nbG_noRet]; rfl),
    tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nbEq_noRet]; rfl),
    tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nbEq_noRet]; rfl),
    tb_holdsList_append_noRet (n0 _ (by simp))] at hpre
  obtain ⟨⟨⟨⟨hh, hEq⟩, hm⟩, hG⟩, ht⟩ := hpre
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hh hm ht
  obtain ⟨h7, h8, h9, h10, h11, h12, h13, h14⟩ := hh
  obtain ⟨h51, h52⟩ := hm
  obtain ⟨h72, h73, h74, h75, h76⟩ := ht
  have ex4 : σ (.n 8) = σ (.n 0) ^ 4 := by rw [h8, h7]; ring
  have ex16 : σ (.n 10) = σ (.n 0) ^ 16 := by rw [h10, h9, ex4]; ring
  refine ⟨fun zs zs1 gs hz hz1 hg rz rz1 rg => ?_, fun hne => ?_⟩
  · obtain ⟨zs', zs1', hl', hl1', rz', rz1', reqs⟩ := holds_nbEq (by norm_num) le_rfl hEq
    obtain ⟨gl', hlg', rg', rgs⟩ := holds_nbG (by norm_num) hG
    rw [h13, ex4] at rz'
    rw [h14, ex4] at rz1'
    rw [h52, ex4] at rg'
    rw [h12, h11, ex16, mul_assoc, ← pow_add] at reqs
    rw [h51, ex16] at rgs
    rw [tbReadsAt_unique rz rz' (by rw [hz, hl']), tbReadsAt_unique rz1 rz1' (by rw [hz1, hl1']),
      tbReadsAt_unique rg rg' (by rw [hg, hlg'])]
    exact ⟨reqs, rgs⟩
  · have := hcall.2 (by rw [h74, h73, h72, tb_word_gen]; exact hne)
    rw [h76, h75, tb_word_gen] at this
    exact this

theorem tbReadsAt_nib {rd : Reader} {p : E} {l : List E} (h : TbReadsAt rd p l) (j : ℕ) :
    TbReadsAt rd (p * gen ^ (4 * j)) (nib l j) := by
  intro k hk
  rw [tb_loadHolds_mul_gen_pow]
  have hk' : 4 * j + k < l.length := by simp [nib] at hk; omega
  have := h (4 * j + k) hk'
  simpa [nib, List.getElem_take, List.getElem_drop] using this

theorem lName_sel_partial (j : ℕ) (hj : j < 4) :
    ["sel_partial_nibble__L0", "sel_partial_nibble__L1", "sel_partial_nibble__L2",
      "sel_partial_nibble__L3"][j]'(by simpa using hj) = lName "sel_partial_nibble" j := by
  interval_cases j <;> rfl

/-- `Π (1 + b_j·(1 + g^(2^j)))` over pinned bits, as the data writes the factors. -/
theorem ss_prod {b : ℕ → E} {n : ℕ} (hn : n ≤ 4) (hb : ∀ j < n, b j * b j = b j) :
    ∏ j ∈ Finset.range n, (1 + b j * word (imFactor j) 0) =
      gen ^ bitsVal (fun j ↦ decide (b j = 1)) n := by
  rw [← prod_gen_pow_of_bool hb]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [imFactor_eq (by have := Finset.mem_range.mp hj; omega), add_comm (1 : E) (gen ^ 2 ^ j)]

/-- **`shared_selector_tables` is sound**. -/
theorem shared_selector_tables_holds : shared_selector_tables_Spec := by
  intro rd args rets h
  obtain ⟨fn, hf, hp, hb⟩ := ssFound
  obtain ⟨σ, hpar, hpre, hret⟩ := (tb_rel_pre hf hb ssPre_noRet args rets).mp h
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil] at hpar hret
  subst hpar hret
  simp only [ssPre, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, and_true] at hpre
  obtain ⟨p6, p7, p8, p9, p10, p11, c12, c13, m14, a15, c16, c17, m18, a19, m20, c21, c22, m23,
    a24, c25, c26, m27, a28, m29, c30, c31, m32, a33, m34, c35, c36, m37, a38, m39, m40, m41, m42,
    e42, c43, a44, c45, -, hloop, m46, m47, m48, m49, m50, m51, m52, m53, hdisp⟩ := hpre
  -- the bits
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
  let r := bitsVal f 2
  let q := bitsVal (fun k ↦ f (k + 2)) 4
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
  refine ⟨4 * q + r, by omega, ?_, fun zs zs1 gs hz hz1 hg rz rz1 rg j hj => ?_⟩
  · rw [← e_add_eq_zero_iff.mp e42, m42, hq4, hrg, ← pow_add]
  -- the full nibbles, by the loop
  have hfull : ∀ j < q, LpB rd (σ (.n 0)) (σ (.n 2)) (σ (.n 3)) (σ (.n 1)) (σ (.n 4)) (gen ^ j) := by
    intro j hj'
    have hne : σ (.n 44) ≠ 0 := by
      rw [a44, c43, tb_word_one, hqg]
      intro h0
      have := gen_pow_inj (by omega) (by decide) ((e_add_eq_zero_iff.mp h0).symm.trans
        (pow_zero gen).symm)
      omega
    have hrun := hloop hne
    simp only [List.map_cons, List.map_nil] at hrun
    rw [c45, tb_word_one, ← pow_zero gen] at hrun
    obtain ⟨m, hm0, hN, hall⟩ := tb_loop_sound (fun d x hx => lp_step d x hx) 0 hrun
    have hmq : q ≤ m := by
      by_contra hc
      have := gen_pow_inj (by omega) (by omega) (hqg.symm.trans hN)
      omega
    exact hall j (by omega) (by omega)
  rcases Nat.lt_or_ge j q with hjq | hjq
  · -- a full nibble
    have hlen : ∀ l : List E, l.length = 4 * q + r → (nib l j).length = 4 := fun l hl => by
      simp [nib, hl]; omega
    obtain ⟨h1, h2⟩ := hfull j hjq (nib zs j) (nib zs1 j) (nib gs j) (hlen zs hz) (hlen zs1 hz1)
      (hlen gs hg) (by rw [← pow_mul, mul_comm j 4]; exact tbReadsAt_nib rz j)
      (by rw [← pow_mul, mul_comm j 4]; exact tbReadsAt_nib rz1 j)
      (by rw [← pow_mul, mul_comm j 4]; exact tbReadsAt_nib rg j)
    rw [← pow_mul, mul_comm j 32] at h1
    rw [← pow_mul, mul_comm j 16] at h2
    exact ⟨h1, h2⟩
  · -- the partial nibble
    have hjq' : j = q := by omega
    subst hjq'
    have hr0 : 0 < r := by omega
    obtain ⟨jd, hjd, hx, nd, hcall⟩ := hdisp
    have hjd4 : jd < 4 := by simpa using hjd
    have hjr : jd = r := by
      rw [hrg, gen_pow_eq_ofK] at hx
      exact gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
        (ofK_injective hx.symm)
    have hsp := sel_partial_nibble_holds jd hjd4 rd _ _
      (by rw [← lName_sel_partial jd hjd4]; exact ⟨nd, hcall⟩)
    simp only [List.map_cons, List.map_nil, SelPartialOut] at hsp
    obtain ⟨-, zs', zs1', gl', hl, hl1, hlg, rz', rz1', rg', reqs, rgs⟩ := hsp
    rw [hjr] at hl hl1 hlg rgs
    have hlen : ∀ l : List E, l.length = 4 * q + r → (nib l q).length = r := fun l hl => by
      simp [nib, hl]; omega
    rw [m51, hq4] at rz'
    rw [m52, hq4] at rz1'
    rw [m53, hq4] at rg'
    rw [m49, m48, hq16', mul_assoc, ← pow_add, show 16 * q + 16 * q = 32 * q by ring] at reqs
    rw [m50, hq16', tb_ite_neg'' (show ¬ r = 0 by omega)] at rgs
    rw [tbReadsAt_unique (tbReadsAt_nib rz q) rz' (by rw [hlen zs hz, hl]),
      tbReadsAt_unique (tbReadsAt_nib rz1 q) rz1' (by rw [hlen zs1 hz1, hl1]),
      tbReadsAt_unique (tbReadsAt_nib rg q) rg' (by rw [hlen gs hg, hlg])]
    exact ⟨reqs, rgs⟩

end
end LeanVM.Guest.B1.Tables
