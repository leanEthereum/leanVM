/-
  LeanVM.Guest.B1.Tables.VtCOod

  The size of `opening_ood_point`'s valid trees (`TotalLe`).
-/

module

public import LeanVM.Guest.B1.Tables.VtCLoopsB
public import LeanVM.Guest.B1.OpeningOod
public import LeanVM.Guest.Memory.Size

/-!
# `opening_ood_point`'s trees (TRIAGE #32)

A `mul_range` loop helper's valid tree from `g^j` stops at some `N = g^(j + d)`, `d ≥ 1`
(`vtc_loop_exists`), so `N` is `g` to `vtcItB N`, its exponent (or the order of `g` for `N = 1`),
and `vtc_loop_total` bounds the tree. `opening_ood_point` is its frame, its `HeapBuf` of
`logG ((g^n·g)²)` words and, unless `g^n = 1`, one `__loop9` from `g^0` to `g^n` (`vtc_ood_total`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory

@[expose] public section

variable {fs : String → ℕ}

/-- **A loop helper's valid tree from `g^j` stops**: its bound is a later power of `g`. -/
theorem vtc_loop_exists {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    {pre : List Stmt} {c : V} {nxt : List V} (hb : fn.body = pre ++ [.callIf c f nxt, .ret []])
    (hst : pre.all Main.Stmt.straight = true) (hna : pre.filterMap Main.Stmt.allocSz = [])
    (rd : Reader) (rest : List E)
    (hstep : ∀ σ (x N : E), fn.params.map σ = x :: N :: rest →
      (∀ e ∈ pre.flatMap (Main.slEvs σ), e.Holds rd σ) →
      σ c = x * gen + N ∧ nxt.map σ = x * gen :: N :: rest) :
    ∀ (fuel : ℕ) (t : Tree) (j : ℕ) (N : E) (rets : List E), t.total (fun _ => 1) ≤ fuel → t.name = f →
      t.Valid coreProgram rd (gen ^ j :: N :: rest) rets → t.BufsOk coreProgram →
      ∃ d, 1 ≤ d ∧ N = gen ^ (j + d) := by
  have hb' : fn.body = (pre ++ [Stmt.callIf c f nxt]) ++ [Stmt.ret []] := by rw [hb, List.append_assoc]; rfl
  have hst' : (pre ++ [Stmt.callIf c f nxt]).all Main.Stmt.straight = true := by
    simp [hst, Main.Stmt.straight]
  have hna' : (pre ++ [Stmt.callIf c f nxt]).filterMap Main.Stmt.allocSz = [] := by
    simp [hna, Main.Stmt.allocSz]
  intro fuel
  induction fuel with
  | zero =>
    intro t j N rets hle hn hv hbo
    obtain ⟨σ, kids, ht, -⟩ := vtc_node (fs := fun _ => 1) hf hb' hst' hna' hn hv hbo
    omega
  | succ fuel ih =>
    intro t j N rets hle hn hv hbo
    obtain ⟨σ, kids, ht, hp, hes, hk, hbk⟩ := vtc_node (fs := fun _ => 1) hf hb' hst' hna' hn hv hbo
    have hes' : ∀ e ∈ pre.flatMap (Main.slEvs σ), e.Holds rd σ := fun e he =>
      hes e (by rw [List.flatMap_append]; exact List.mem_append_left _ he)
    obtain ⟨hc, hnx⟩ := hstep σ _ _ hp hes'
    rw [List.filterMap_append, List.map_append] at hk
    obtain ⟨k1, k2, rfl, -, hk2⟩ := vtc_kidsValid_append hk
    obtain ⟨-, hb2⟩ := vtc_bufsOkKids_append hbk
    simp only [Main.Stmt.callS, List.filterMap_cons, List.filterMap_nil, List.map_cons, List.map_nil,
      Main.mkCall] at hk2
    match k2, hk2, hb2 with
    | [kl], ⟨hnl, hvl, _⟩, ⟨hbl, _⟩ =>
      by_cases hz : σ c = 0
      · refine ⟨1, le_rfl, ?_⟩
        rw [hc, gen_pow_mul_gen] at hz
        exact (e_add_eq_zero_iff.mp hz).symm
      · simp only [hz, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, hnx] at hvl
        rw [gen_pow_mul_gen] at hvl
        rw [vtc_totalKids_append] at ht
        simp only [Tree.totalKids, Nat.add_zero] at ht
        obtain ⟨d, hd, hN⟩ := ih kl (j + 1) N _ (by omega) hnl hvl hbl
        exact ⟨d + 1, by omega, by rw [hN]; ring_nf⟩

/-- The exponent of a power of `g`: `logG`, or the order of `g` at `1`. -/
noncomputable def vtcItB (N : E) : ℕ := if logG N = 0 then ordG else logG N

theorem vtc_itB {N : E} {d : ℕ} (hN : N = gen ^ d) : 1 ≤ vtcItB N ∧ N = gen ^ vtcItB N := by
  have hmod : N = gen ^ (d % ordG) := by
    rw [hN]
    conv_lhs => rw [← Nat.div_add_mod d ordG, pow_add, pow_mul, gen_pow_ordG, one_pow, one_mul]
  have hl : logG N = d % ordG := by
    rw [hmod, gen_pow_eq_ofK]; exact logG_spec (Nat.mod_lt _ (by unfold ordG; omega))
  unfold vtcItB
  by_cases h0 : logG N = 0
  · rw [h0] at hl
    simp only [h0, ↓reduceIte]
    refine ⟨by unfold ordG; omega, ?_⟩
    rw [hmod, ← hl, pow_zero, gen_pow_ordG]
  · simp only [h0, ↓reduceIte]
    exact ⟨by omega, by rw [hl]; exact hmod⟩

/-! ## `__loop9` -/

noncomputable def vtcP9 : List Stmt := (Fn.body Data.core39).take 31

theorem vtc_core39 : Fn.body Data.core39 =
    vtcP9 ++ [.callIf (.n 29) "__loop9" [.n 31, .n 1, .n 2, .n 3], .ret []] :=
  stmtsEqb_sound (by decide +kernel)

theorem vtc_p9_ok : vtcP9.all Main.Stmt.straight = true ∧ vtcP9.filterMap Main.Stmt.allocSz = [] ∧
    vtcP9.filterMap Main.Stmt.callS = [] := by decide +kernel

theorem vtc_l9_step (rd : Reader) (rest : List E) (σ : Val) (x N : E)
    (hp : (Fn.params Data.core39).map σ = x :: N :: rest)
    (hes : ∀ e ∈ vtcP9.flatMap (Main.slEvs σ), e.Holds rd σ) :
    σ (.n 29) = x * gen + N ∧ [V.n 31, .n 1, .n 2, .n 3].map σ = x * gen :: N :: rest := by
  simp only [show Fn.params Data.core39 = [.n 0, .n 1, .n 2, .n 3] from rfl, List.map_cons,
    List.map_nil, List.cons.injEq] at hp
  obtain ⟨h0, h1, hr⟩ := hp
  subst hr
  obtain ⟨e1, e2⟩ := vtcl_tail hes 27 26 rfl rfl rfl rfl rfl
  exact ⟨by rw [e1, h0, h1], by simp [e2, h0, h1]⟩

/-- **`__loop9`'s trees from `g^0`.** -/
theorem vtc_l9_total {rd : Reader} {N : E} {rest : List E} {t : Tree} {rets : List E}
    (hn : t.name = "__loop9") (hv : t.Valid coreProgram rd (1 :: N :: rest) rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ vtcItB N * (fs "__loop9" + 0) + fs "__loop9" := by
  have hv0 : t.Valid coreProgram rd (gen ^ 0 :: N :: rest) rets := by rwa [pow_zero]
  obtain ⟨d, hd, hN⟩ := vtc_loop_exists find_loop9 vtc_core39 vtc_p9_ok.1 vtc_p9_ok.2.1 rd rest
    (vtc_l9_step rd rest) _ t 0 N rets le_rfl hn hv0 hbo
  obtain ⟨h1, hN'⟩ := vtc_itB hN
  rw [hN'] at hv0
  refine vtc_loop_total (fs := fs) find_loop9 vtc_core39 vtc_p9_ok.1 vtc_p9_ok.2.1 rd (vtcItB N) rest 0
    ?_ (vtcItB N) 0 t rets (by omega) h1 hn hv0 hbo
  intro σ j _ hp hes
  obtain ⟨e1, e2⟩ := vtc_l9_step rd rest σ _ _ hp hes
  refine ⟨e1, e2, fun kids hk _ => ?_⟩
  rw [vtc_p9_ok.2.2] at hk
  exact vtcl_nokids hk

/-! ## `opening_ood_point` -/

noncomputable def vtcPOod : List Stmt := (Fn.body Data.core9).take 14

theorem vtc_core9 : Fn.body Data.core9 = vtcPOod ++ [.ret [.n 13, .n 14]] := stmtsEqb_sound (by decide +kernel)

theorem vtc_pOod_ok : vtcPOod.all Main.Stmt.straight = true ∧
    vtcPOod.filterMap Main.Stmt.allocSz = [(.n 7, .inr (.n 6))] ∧
    vtcPOod.filterMap Main.Stmt.callS = [(some (.n 9), "__loop9", [.n 10, .n 3, .n 7, .n 2], [])] := by
  decide +kernel

/-- `opening_ood_point`'s bound: its frame, its run of `logG ((g^n·g)²)` words, its loop. -/
noncomputable def vtcOodB (fs : String → ℕ) (a : List E) : ℕ :=
  fs "opening_ood_point" + logG ((a.getD 3 0 * gen) * (a.getD 3 0 * gen)) +
    (vtcItB (a.getD 3 0) * (fs "__loop9" + 0) + fs "__loop9")

set_option maxHeartbeats 1000000 in
/-- **`opening_ood_point`'s valid trees** are at most `vtcOodB fs`. -/
theorem vtc_ood_total : TotalLe coreProgram fs "opening_ood_point" (vtcOodB fs) := by
  intro rd t args rets hn hv hbo
  match t, hn, hv, hbo with
  | .node g σ bufs kids, hn, hv, hbo =>
    simp only [Tree.name] at hn
    subst hn
    obtain ⟨fn', hf', hp, es, vs', hw, -, hes, hk⟩ := hv
    rw [find_opening_ood_point, Option.some.injEq] at hf'
    subst hf'
    have hw' : walk σ (Fn.body Data.core9) = .ret (vtcPOod.flatMap (Main.slEvs σ)) [.n 13, .n 14] := by
      rw [vtc_core9]; exact Main.walk_straight σ _ vtcPOod vtc_pOod_ok.1
    rw [hw'] at hw
    cases hw
    obtain ⟨hbuf, hbk⟩ := hbo
    have hev : (Memory.Tree.node "opening_ood_point" σ bufs kids).events coreProgram =
        vtcPOod.flatMap (Main.slEvs σ) := by
      simp only [Tree.events, Tree.name, Tree.val, find_opening_ood_point, hw']
    obtain ⟨-, i2, -, i4⟩ := Main.straight_parts σ vtcPOod vtc_pOod_ok.1
    rw [hev, i2, vtc_pOod_ok.2.1] at hbuf
    rw [i4, vtc_pOod_ok.2.2] at hk
    simp only [List.map_cons, List.map_nil, Main.mkCall] at hk
    simp only [show Fn.params Data.core9 = [.n 0, .n 1, .n 2, .n 3] from rfl, List.map_cons,
      List.map_nil] at hp
    subst hp
    have a4 := vtc_atom hes (List.mem_of_getElem? (l := vtcPOod) (i := 0) rfl)
    have a5 := vtc_atom hes (List.mem_of_getElem? (l := vtcPOod) (i := 1) rfl)
    have a6 := vtc_atom hes (List.mem_of_getElem? (l := vtcPOod) (i := 2) rfl)
    have a8 := vtc_atom hes (List.mem_of_getElem? (l := vtcPOod) (i := 6) rfl)
    have a9 := vtc_atom hes (List.mem_of_getElem? (l := vtcPOod) (i := 7) rfl)
    have a10 := vtc_atom hes (List.mem_of_getElem? (l := vtcPOod) (i := 8) rfl)
    simp only [Atom.Holds, word_gen, word_one] at a4 a5 a6 a8 a9 a10
    have e6 : σ (.n 6) = (σ (.n 3) * gen) * (σ (.n 3) * gen) := by rw [a6, a5, a4]
    match kids, hk, hbk with
    | [kl], ⟨hnl, hvl, _⟩, ⟨hbl, _⟩ =>
      have hkl : kl.total fs ≤ vtcItB (σ (.n 3)) * (fs "__loop9" + 0) + fs "__loop9" := by
        by_cases hz : σ (.n 9) = 0
        · simp only [hz, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hvl
          obtain ⟨⟨g', σ', rfl⟩, -⟩ := hvl
          simp only [Tree.name] at hnl
          simp only [Tree.total, hnl]
          omega
        · simp only [hz, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, List.map_cons,
            List.map_nil] at hvl
          rw [a10] at hvl
          exact vtc_l9_total hnl hvl hbl
      simp only [Tree.total, Tree.totalKids, hbuf, List.map_cons, List.map_nil, Sum.elim_inr,
        List.sum_cons, List.sum_nil, vtcOodB, List.getD_cons_succ, List.getD_cons_zero]
      rw [e6]
      omega

end
end LeanVM.Guest.B1.VerifySub
