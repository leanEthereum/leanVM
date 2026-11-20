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

`shared_selector_tables(zeta_hi, zeta1_hi, gsq_hi, len_g)` hints the six bits of `len_g`'s
exponent, pins them Boolean, rebuilds `r_g = g^r` from the low two and `q_g = g^q` from the high
four, asserts `q_g^4·r_g = len_g` (so `len_g = g^n`, `n = 4q + r < 64`), allocates its tables
`eq_tab` (`32 (q + 1)` words) and `g_tab` (`16 (q + 1)`), runs its loop over `x = g^j`, `j < q`
(`shared_selector_tables_loop0`: nibble `j`'s eq levels and `g` table by the inline
`sel_eq_nibble`, `sel_g_nibble`), dispatches the partial nibble `q` of width `r` to
`sel_partial_nibble__L{r}` and returns the two tables.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value
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

/-- `shared_selector_tables`'s statements before its `ret`. -/
def ssPre : List Stmt :=
  [.atom (.hint (.bitsExp (.n 3) 6 (.stack [.n 4, .n 5, .n 6, .n 7, .n 8, .n 9]))),
    .atom (.mul (.n 4) (.n 4) (.n 4)), .atom (.mul (.n 5) (.n 5) (.n 5)),
    .atom (.mul (.n 6) (.n 6) (.n 6)), .atom (.mul (.n 7) (.n 7) (.n 7)),
    .atom (.mul (.n 8) (.n 8) (.n 8)), .atom (.mul (.n 9) (.n 9) (.n 9)),
    .atom (.const (.n 10) (word 1 0)), .atom (.const (.n 11) (word (imFactor 0) 0)),
    .atom (.mul (.n 12) (.n 4) (.n 11)), .atom (.add (.n 13) (.n 10) (.n 12)),
    .atom (.const (.n 14) (word 1 0)), .atom (.const (.n 15) (word (imFactor 1) 0)),
    .atom (.mul (.n 16) (.n 5) (.n 15)), .atom (.add (.n 17) (.n 14) (.n 16)),
    .atom (.mul (.n 18) (.n 13) (.n 17)),
    .atom (.const (.n 19) (word 1 0)), .atom (.const (.n 20) (word (imFactor 0) 0)),
    .atom (.mul (.n 21) (.n 6) (.n 20)), .atom (.add (.n 22) (.n 19) (.n 21)),
    .atom (.const (.n 23) (word 1 0)), .atom (.const (.n 24) (word (imFactor 1) 0)),
    .atom (.mul (.n 25) (.n 7) (.n 24)), .atom (.add (.n 26) (.n 23) (.n 25)),
    .atom (.mul (.n 27) (.n 22) (.n 26)),
    .atom (.const (.n 28) (word 1 0)), .atom (.const (.n 29) (word (imFactor 2) 0)),
    .atom (.mul (.n 30) (.n 8) (.n 29)), .atom (.add (.n 31) (.n 28) (.n 30)),
    .atom (.mul (.n 32) (.n 27) (.n 31)),
    .atom (.const (.n 33) (word 1 0)), .atom (.const (.n 34) (word (imFactor 3) 0)),
    .atom (.mul (.n 35) (.n 9) (.n 34)), .atom (.add (.n 36) (.n 33) (.n 35)),
    .atom (.mul (.n 37) (.n 32) (.n 36)),
    .atom (.mul (.n 38) (.n 37) (.n 37)), .atom (.mul (.n 39) (.n 38) (.n 38)),
    .atom (.mul (.n 40) (.n 39) (.n 18)), .atom (.assertEq (.n 40) (.n 3)),
    .atom (.const (.n 41) (word 2 0)), .atom (.mul (.n 42) (.n 37) (.n 41)),
    .atom (.mul (.n 43) (.n 42) (.n 42)), .atom (.mul (.n 44) (.n 43) (.n 43)),
    .atom (.mul (.n 45) (.n 44) (.n 44)), .atom (.mul (.n 46) (.n 45) (.n 45)),
    .atom (.mul (.n 47) (.n 46) (.n 46)),
    .atom (.hint (.allocDyn (.n 48) (.n 47))), .atom (.hint (.allocDyn (.n 49) (.n 46))),
    .atom (.const (.n 50) (word 1 0)), .atom (.add (.n 51) (.n 50) (.n 37)),
    .atom (.const (.n 52) (word 1 0)),
    .callIf (.n 51) name% «shared_selector_tables_loop0» [.n 52, .n 37, .n 48, .n 0, .n 1, .n 49,
        .n 2],
    .atom (.mul (.n 53) (.n 39) (.n 39)), .atom (.mul (.n 54) (.n 53) (.n 53)),
    .atom (.mul (.n 55) (.n 48) (.n 54)), .atom (.mul (.n 56) (.n 55) (.n 54)),
    .atom (.mul (.n 57) (.n 49) (.n 54)), .atom (.mul (.n 58) (.n 0) (.n 39)),
    .atom (.mul (.n 59) (.n 1) (.n 39)), .atom (.mul (.n 60) (.n 2) (.n 39)),
    .dispatch (.n 18) ["sel_partial_nibble__L0", "sel_partial_nibble__L1",
      "sel_partial_nibble__L2", "sel_partial_nibble__L3"] [.n 56, .n 57, .n 58, .n 59, .n 60]
      [.n 61],
    .atom (.copy (.n 62) (.n 48)), .atom (.copy (.n 63) (.n 49))]

/-- `shared_selector_tables`' returns: its two tables. -/
def ssRets : List V := [.n 62, .n 63]

noncomputable def ssCheck : Bool :=
  match coreProgram.find? "shared_selector_tables" with
  | some fn => decide (fn.params = [.n 0, .n 1, .n 2, .n 3]) &&
      tbStmtsEqb fn.body (ssPre ++ [.ret ssRets])
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
    fn.params = [.n 0, .n 1, .n 2, .n 3] ∧ fn.body = ssPre ++ [.ret ssRets] := by
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
  obtain ⟨p4, p5, p6, p7, p8, p9, c10, c11, m12, a13, c14, c15, m16, a17, m18, c19, c20, m21,
    a22, c23, c24, m25, a26, m27, c28, c29, m30, a31, m32, c33, c34, m35, a36, m37, m38, m39, m40,
    e40, c41, m42, m43, m44, m45, m46, m47, c50, a51, c52, -, hloop, m53, m54, m55, m56, m57, m58,
    m59, m60, hdisp, cp62, cp63⟩ := hpre
  simp only [ssRets, List.map_cons, List.map_nil]
  rw [cp62, cp63]
  -- the bits
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
  let r := bitsVal f 2
  let q := bitsVal (fun k ↦ f (k + 2)) 4
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
  refine ⟨4 * q + r, by omega, ?_, fun zs zs1 gs hz hz1 hg rz rz1 rg j hj => ?_⟩
  · rw [← e_add_eq_zero_iff.mp e40, m40, hq4, hrg, ← pow_add]
  -- the full nibbles, by the loop
  have hfull : ∀ j < q, LpB rd (σ (.n 48)) (σ (.n 0)) (σ (.n 1)) (σ (.n 49)) (σ (.n 2)) (gen ^ j) := by
    intro j hj'
    have hne : σ (.n 51) ≠ 0 := by
      rw [a51, c50, tb_word_one, hqg]
      intro h0
      have := gen_pow_inj (by omega) (by decide) ((e_add_eq_zero_iff.mp h0).symm.trans
        (pow_zero gen).symm)
      omega
    have hrun := hloop hne
    simp only [List.map_cons, List.map_nil] at hrun
    rw [c52, tb_word_one, ← pow_zero gen] at hrun
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
    rw [m58, hq4] at rz'
    rw [m59, hq4] at rz1'
    rw [m60, hq4] at rg'
    rw [m56, m55, hq16', mul_assoc, ← pow_add, show 16 * q + 16 * q = 32 * q by ring] at reqs
    rw [m57, hq16', tb_ite_neg'' (show ¬ r = 0 by omega)] at rgs
    rw [tbReadsAt_unique (tbReadsAt_nib rz q) rz' (by rw [hlen zs hz, hl]),
      tbReadsAt_unique (tbReadsAt_nib rz1 q) rz1' (by rw [hlen zs1 hz1, hl1]),
      tbReadsAt_unique (tbReadsAt_nib rg q) rg' (by rw [hlen gs hg, hlg])]
    exact ⟨reqs, rgs⟩

end
end LeanVM.Guest.B1.Tables
