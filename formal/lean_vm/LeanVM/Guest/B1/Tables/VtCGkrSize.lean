/-
  LeanVM.Guest.B1.Tables.VtCGkrSize

  The sizes of the valid trees of `verify_bus_gkr`'s loops: `__loop11`, `__loop101` (with
  `sumcheck_round5`) and `__loop10`.
-/

module

public import LeanVM.Guest.B1.Tables.VtCSize
public import LeanVM.Guest.B1.Tables.GkrAt

/-!
# The GKR loops' sizes

`__loop11` and `__loop101` are `mul_range` loops over straight-line bodies with no `HeapBuf`
(`vtc_loop_total`); `__loop101` calls `sumcheck_round5`, a leaf. `__loop10` runs `__loop101` on
`2j + s` rounds at iteration `j`, `s = ds[μ]` read from the memory, so its bound holds on a memory
holding that word.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Guest.Memory

@[expose] public section

variable {fs : String → ℕ}

theorem vtc_mem {l : List Stmt} {s : Stmt} (i : ℕ) (h : l[i]? = some s) : s ∈ l := List.mem_of_getElem? h

/-! ## `sumcheck_round5` -/

noncomputable def vtcP5 : List Stmt := (Fn.body Data.core7).take 87

theorem vtc_core7 : Fn.body Data.core7 = vtcP5 ++ [.ret [.n 86, .n 87, .n 90, .n 98, .n 99]] :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem vtc_p5 : vtcP5.all Main.Stmt.straight = true ∧ vtcP5.filterMap Main.Stmt.allocSz = [] ∧
    vtcP5.filterMap Main.Stmt.callS = [] := by decide +kernel

theorem vtc_sr5_total {rd : Reader} {t : Tree} {args rets : List E} (hn : t.name = "sumcheck_round5")
    (hv : t.Valid coreProgram rd args rets) (hbo : t.BufsOk coreProgram) :
    t.total fs = fs "sumcheck_round5" :=
  vtc_leaf_total find_sumcheck_round5 vtc_core7 vtc_p5.1 vtc_p5.2.1 vtc_p5.2.2 hn hv hbo

/-! ## `__loop11` -/

noncomputable def vtcP11 : List Stmt := (Fn.body Data.core41).take 9

theorem vtc_core41 : Fn.body Data.core41 =
    vtcP11 ++ [.callIf (.n 9) "__loop11" [.n 11, .n 1, .n 2, .n 3], .ret []] :=
  stmtsEqb_sound (by decide +kernel)

theorem vtc_p11 : vtcP11.all Main.Stmt.straight = true ∧ vtcP11.filterMap Main.Stmt.allocSz = [] ∧
    vtcP11.filterMap Main.Stmt.callS = [] := by decide +kernel

/-- **`__loop11`'s trees** over `m` iterations. -/
theorem vtc_l11_total {rd : Reader} {m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hm : 0 < m)
    (hn : t.name = "__loop11") (hv : t.Valid coreProgram rd (1 :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ m * (fs "__loop11" + 0) + fs "__loop11" := by
  refine vtc_loop_total (fs := fs) find_loop11 vtc_core41 vtc_p11.1 vtc_p11.2.1 rd m rest 0 ?_ m 0 t rets
    (by omega) hm hn (by rwa [pow_zero]) hbo
  intro σ j _ hp hes
  simp only [show Fn.params Data.core41 = [.n 0, .n 1, .n 2, .n 3] from rfl, List.map_cons,
    List.map_nil, List.cons.injEq] at hp
  obtain ⟨h0, h1, hr⟩ := hp
  subst hr
  have a7 := vtc_atom hes (vtc_mem (l := vtcP11) 4 rfl)
  have a8 := vtc_atom hes (vtc_mem (l := vtcP11) 5 rfl)
  have a9 := vtc_atom hes (vtc_mem (l := vtcP11) 6 rfl)
  have a10 := vtc_atom hes (vtc_mem (l := vtcP11) 7 rfl)
  have a11 := vtc_atom hes (vtc_mem (l := vtcP11) 8 rfl)
  simp only [Atom.Holds, word_gen] at a7 a8 a9 a10 a11
  refine ⟨by rw [a9, a8, a7, h0, h1], by simp [a11, a10, h0, h1], fun kids hk _ => ?_⟩
  rw [vtc_p11.2.2] at hk
  match kids, hk with
  | [], _ => simp [Tree.totalKids]

/-! ## `__loop101` -/

noncomputable def vtcP101 : List Stmt := (Fn.body Data.core574).take 22

theorem vtc_core574 : Fn.body Data.core574 =
    vtcP101 ++ [.callIf (.n 24) "__loop101" [.n 26, .n 1, .n 2, .n 3, .n 4, .n 5], .ret []] :=
  stmtsEqb_sound (by decide +kernel)

theorem vtc_p101 : vtcP101.all Main.Stmt.straight = true ∧ vtcP101.filterMap Main.Stmt.allocSz = [] ∧
    vtcP101.filterMap Main.Stmt.callS = [(none, "sumcheck_round5", [.n 10, .n 11, .n 12, .n 13, .n 15],
      [.n 16, .n 17, .n 18, .n 19, .n 20])] := by decide +kernel

/-- **`__loop101`'s trees** over `m` rounds, each with its `sumcheck_round5`. -/
theorem vtc_l101_total {rd : Reader} {m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hm : 0 < m)
    (hn : t.name = "__loop101") (hv : t.Valid coreProgram rd (1 :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) :
    t.total fs ≤ m * (fs "__loop101" + fs "sumcheck_round5") + fs "__loop101" := by
  refine vtc_loop_total (fs := fs) find_loop101 vtc_core574 vtc_p101.1 vtc_p101.2.1 rd m rest _ ?_ m 0 t
    rets (by omega) hm hn (by rwa [pow_zero]) hbo
  intro σ j _ hp hes
  simp only [show Fn.params Data.core574 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨h0, h1, hr⟩ := hp
  subst hr
  have a22 := vtc_atom hes (vtc_mem (l := vtcP101) 17 rfl)
  have a23 := vtc_atom hes (vtc_mem (l := vtcP101) 18 rfl)
  have a24 := vtc_atom hes (vtc_mem (l := vtcP101) 19 rfl)
  have a25 := vtc_atom hes (vtc_mem (l := vtcP101) 20 rfl)
  have a26 := vtc_atom hes (vtc_mem (l := vtcP101) 21 rfl)
  simp only [Atom.Holds, word_gen] at a22 a23 a24 a25 a26
  refine ⟨by rw [a24, a23, a22, h0, h1], by simp [a26, a25, h0, h1], fun kids hk hbk => ?_⟩
  rw [vtc_p101.2.2] at hk
  simp only [List.map_cons, List.map_nil, Main.mkCall] at hk
  match kids, hk, hbk with
  | [k], ⟨hnk, hvk, _⟩, ⟨hbk, _⟩ =>
    simp only [↓reduceIte] at hvk
    simp [Tree.totalKids, vtc_sr5_total hnk hvk hbk]

/-! ## `__loop10` -/

noncomputable def vtcP10 : List Stmt := (Fn.body Data.core40).take 317

theorem vtc_core40 : Fn.body Data.core40 =
    vtcP10 ++ [.callIf (.n 328) "__loop10" [.n 330, .n 1, .n 2, .n 3, .n 4, .n 5], .ret []] :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem vtc_p10 : vtcP10.all Main.Stmt.straight = true ∧ vtcP10.filterMap Main.Stmt.allocSz = [] ∧
    vtcP10.filterMap Main.Stmt.callS =
      [(some (.n 44), "__loop101", [.n 45, .n 9, .n 5, .n 31, .n 30, .n 47], [])] := by decide +kernel

/-- `__loop10`'s callees in one iteration: one `__loop101` of at most 31 rounds. -/
abbrev vtcK10 (fs : String → ℕ) : ℕ := 31 * (fs "__loop101" + fs "sumcheck_round5") + fs "__loop101"

/-- **`__loop10`'s trees** over `m ≤ 16` layers, on a memory holding `ds[μ] = g^s`, `s ≤ 1`, at
`dsb·g^μ`. -/
theorem vtc_l10_total {rd : Reader} {m s : ℕ} {dsb gmu lay rnd : E} {t : Tree} {rets : List E}
    (hm : 0 < m) (hm16 : m ≤ 16) (hs : s ≤ 1) (hds : LoadHolds rd (dsb * gmu) 0 (gen ^ s))
    (hn : t.name = "__loop10") (hv : t.Valid coreProgram rd [1, gen ^ m, dsb, gmu, lay, rnd] rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ m * (fs "__loop10" + vtcK10 fs) + fs "__loop10" := by
  refine vtc_loop_total (fs := fs) find_loop10 vtc_core40 vtc_p10.1 vtc_p10.2.1 rd m [dsb, gmu, lay, rnd]
    _ ?_ m 0 t rets (by omega) hm hn (by rwa [pow_zero]) hbo
  intro σ j hj hp hes
  simp only [show Fn.params Data.core40 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5, -⟩ := hp
  have a6 := vtc_atom hes (vtc_mem (l := vtcP10) 0 rfl)
  have a7 := vtc_atom hes (vtc_mem (l := vtcP10) 1 rfl)
  have l8 := vtc_atom hes (vtc_mem (l := vtcP10) 2 rfl)
  have a9 := vtc_atom hes (vtc_mem (l := vtcP10) 3 rfl)
  have a43 := vtc_atom hes (vtc_mem (l := vtcP10) 41 rfl)
  have a44 := vtc_atom hes (vtc_mem (l := vtcP10) 42 rfl)
  have a45 := vtc_atom hes (vtc_mem (l := vtcP10) 43 rfl)
  have a326 := vtc_atom hes (vtc_mem (l := vtcP10) 312 rfl)
  have a327 := vtc_atom hes (vtc_mem (l := vtcP10) 313 rfl)
  have a328 := vtc_atom hes (vtc_mem (l := vtcP10) 314 rfl)
  have a329 := vtc_atom hes (vtc_mem (l := vtcP10) 315 rfl)
  have a330 := vtc_atom hes (vtc_mem (l := vtcP10) 316 rfl)
  simp only [Atom.Holds, word_gen, word_one] at a6 a7 l8 a9 a43 a44 a45 a326 a327 a328 a329 a330
  refine ⟨by rw [a328, a327, a326, h0, h1], by simp [a330, a329, h0, h1, h2, h3, h4, h5],
    fun kids hk hbk => ?_⟩
  rw [a7, h2, h3] at l8
  have e8 := loadHolds_unique l8 hds
  have e9 : σ (.n 9) = gen ^ (2 * j + s) := by rw [a9, a6, e8, h0, ← pow_add, ← pow_add]; ring_nf
  rw [vtc_p10.2.2] at hk
  simp only [List.map_cons, List.map_nil, Main.mkCall] at hk
  match kids, hk, hbk with
  | [k], ⟨hnk, hvk, _⟩, ⟨hbk, _⟩ =>
    simp only [Tree.totalKids, Nat.add_zero]
    by_cases hz : σ (.n 44) = 0
    · simp only [hz, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hvk
      obtain ⟨⟨g, σ', rfl⟩, -⟩ := hvk
      simp only [Tree.name] at hnk
      simp only [Tree.total, hnk, vtcK10]
      omega
    · simp only [hz, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, List.map_cons,
        List.map_nil] at hvk
      rw [a45, e9] at hvk
      have hpos : 0 < 2 * j + s := by
        rcases Nat.eq_zero_or_pos (2 * j + s) with h | h
        · exfalso; apply hz; rw [a44, a43, e9, h, pow_zero]; exact e_add_self 1
        · exact h
      have := vtc_l101_total (fs := fs) hpos hnk hvk hbk
      have hle : (2 * j + s) * (fs "__loop101" + fs "sumcheck_round5") ≤
          31 * (fs "__loop101" + fs "sumcheck_round5") := Nat.mul_le_mul_right _ (by omega)
      simp only [vtcK10]
      omega

end
end LeanVM.Guest.B1.VerifySub
