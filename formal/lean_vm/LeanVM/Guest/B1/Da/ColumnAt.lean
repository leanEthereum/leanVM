/-
  LeanVM.Guest.B1.Da.ColumnAt

  `da_verify_column__L0` and `__L1` placed by the bump allocator, loading from a region
  (`RelAtIn`): the column's tree right after its frame, then its vector dispatch, row loop, gap
  loop and tree.
-/

module

public import LeanVM.Guest.B1.Da.DispatchAt
public import LeanVM.Guest.B1.Da.LevelsIn
public import LeanVM.Guest.B1.Da.VerifyColumn

/-!
# A column, placed

At `fp`, `da_verify_column(g^b, g^r, g^N, g^(N-r), g^lp, …)` allocates its tree of `4N` words at
`fp + fs col` (`colNode`), then places its callees one after another: `da_vector_dispatch`, whose
weights' run the row loop's cells read, the row loop, the gap loop and the tree's levels. Its own
loads read the vector hash's states and the column tree's root slot (the region `R`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

open LeanVM.Guest.B1.Main (RelAtInW relAtInW_of_walk)

@[expose] public section

/-! ## The honest valuation -/

/-- The column's honest values. -/
def colVals (xb nb np gap glp pb ct rb hs ctr h0 h1 o0 o1 lv node c0 c1 : E) : Val :=
  listVal [xb, nb, np, gap, glp, pb, ct, rb, hs, ctr, xb * xb, hs * (xb * xb), h0, h1, o0, o1,
    lv, gen, xb * gen, xb * gen * (xb * gen), hs * (xb * gen * (xb * gen)), np * np,
    np * np * (np * np), node, 1, 1 + nb, 1, 1, 1 + gap, 1, c0, c1, xb * xb, ct * (xb * xb)]

/-- **The column's body holds** under its honest values. -/
theorem col_holds (store : Bool) {rd : Reader} {xb nb np gap glp pb ct rb hs ctr h0 h1 o0 o1 lv node c0 c1 : E}
    (h12 : CellsAt rd (hs * (xb * xb)) [h0, h1])
    (hdisp : Meaning_da_vector_dispatch rd [xb, h0, h1, ctr] [o0, o1, lv])
    (h14 : CellsAt rd (hs * (xb * gen * (xb * gen))) [o0, o1]) (hk1 : IsInK nb)
    (hrow : nb ≠ 1 → LoopTo nb fun j => RowCell store rd lv rb xb node pb (gen ^ j)) (hk3 : IsInK gap)
    (hgap : gap ≠ 1 → LoopTo gap fun j => GapStep rd node nb (gen ^ j))
    (hdl : ∃ k < 11, glp = gen ^ k ∧ Meaning_da_levels k rd [node] [c0, c1])
    (h30 : CellsAt rd (ct * (xb * xb)) [c0, c1]) :
    Stmt.HoldsList (coreProgram.Rel rd) rd (colVals xb nb np gap glp pb ct rb hs ctr h0 h1 o0 o1 lv node c0 c1)
      (colBody store) False (fun rs => rs = []) := by
  obtain ⟨l12, l13⟩ := cellsAt_two.mp h12
  obtain ⟨l14, l15⟩ := cellsAt_two.mp h14
  obtain ⟨l30, l31⟩ := cellsAt_two.mp h30
  simp only [colBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and,
    word_one, word_gen, colVals, listVal, List.getD_cons_succ, List.getD_cons_zero, and_true]
  exact ⟨l12, l13, (da_vector_dispatch_iff rd _ _).mpr hdisp, l14, l15, isInK_one_add.mpr hk1,
    fun h => (row_loop_meaning store rd _ _ _ _ _ _).mpr (hrow (one_add_ne_zero.mp h)),
    isInK_one_add.mpr hk3, fun h => (gap_loop_meaning store rd _ _ _).mpr (hgap (one_add_ne_zero.mp h)),
    dl_dispatch.mpr hdl, l30, l31⟩

/-! ## The pure callees -/

theorem row_pure (store : Bool) : coreProgram.PureIn [rowName store, "da_verify_cell"] := by
  intro g hg fn hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · rw [find_row, Option.some.injEq] at hf; subst hf; cases store <;> decide +kernel
  · rw [find_da_verify_cell, Option.some.injEq] at hf; subst hf; cases store <;> decide +kernel

theorem gap_pure (store : Bool) : coreProgram.PureIn [gapName store] := by
  intro g hg fn hf
  rw [List.mem_singleton] at hg
  subst hg
  rw [find_gap, Option.some.injEq] at hf; subst hf; cases store <;> decide +kernel

/-- The tree of `2^k` leaves and its level loops. -/
def lvSet (k : ℕ) : List String := dlNames.getD k "" :: lvNames.getD k []

theorem lvNames_length {k : ℕ} (hk : k ≤ 10) : (lvNames.getD k []).length = k := by
  interval_cases k <;> rfl

theorem lv_pure {k : ℕ} (hk : k ≤ 10) : coreProgram.PureIn (lvSet k) := by
  intro g hg fn hf
  rcases List.mem_cons.mp hg with rfl | hg
  · rw [find_dl k hk, Option.some.injEq] at hf; subst hf
    interval_cases k <;> decide +kernel
  · obtain ⟨l, hl0, rfl⟩ := List.getElem_of_mem hg
    have hl : l < k := by rw [lvNames_length hk] at hl0; exact hl0
    have e : (lvNames.getD k [])[l] = lvName k l := by unfold lvName; exact (List.getD_eq_getElem _ _ hl0).symm
    rw [e, find_lv k l hk hl, Option.some.injEq] at hf; subst hf
    interval_cases k <;> interval_cases l <;> decide +kernel

theorem dlNames_getElem! {k : ℕ} (hk : k < 11) : dlNames[k]! = dlNames.getD k "" := by
  interval_cases k <;> rfl

/-! ## The path -/

/-- The column's statements before its tree's dispatch. -/
def colPre (store : Bool) : List Stmt := (colBody store).take 22

/-- The column's statements after its tree's dispatch. -/
def colPost : List Stmt :=
  [.atom (.mul (.n 32) (.n 0) (.n 0)), .atom (.mul (.n 33) (.n 6) (.n 32)),
   .atom (.load (.n 30) (.n 33) 0), .atom (.load (.n 31) (.n 33) 1)]

theorem colBody_split (store : Bool) : colBody store =
    colPre store ++ .dispatch (.n 4) dlNames [.n 23] [.n 30, .n 31] :: (colPost ++ [.ret []]) := by
  cases store <;> rfl

theorem colPre_straight (store : Bool) : (colPre store).all Main.Stmt.straight = true := by
  cases store <;> rfl

theorem colPost_straight : colPost.all Main.Stmt.straight = true := rfl

/-- The words of a column: its frame, its tree, its vector cell, its loops and its tree's levels. -/
def colTot (fs : String → ℕ) (store : Bool) (b r N lp : ℕ) : ℕ :=
  fs (colName store) + 4 * N +
    (fs "da_vector_dispatch" + fs (vxName (decide (b = 127))) +
      (rowTot fs store r 0 + ((if N - r = 0 then fs (gapName store) else gapTot fs store (N - r) 0) +
        (dlTot fs lp + 0))))

theorem loopTo_all' {n : ℕ} {B : ℕ → Prop} (hn : 0 < n) (hn' : n < 2 ^ 33) (h : ∀ j < n, B j) :
    LoopTo (gen ^ n) B :=
  ⟨n, hn, rfl, fun j h1 h2 he => by have := gen_pow_inj' (by omega) hn' he; omega, h⟩

/-- **A column at `fp`.** Its tree at `fp + fs col`, its vector cell's weights at the run the
certificate places in the vector cell's frame; it loads the counters, the vector hash's states,
the column tree's slot and the rows' words from `R`. -/
theorem col_relAtIn (fs : String → ℕ) (cert : String → V → ℕ) (store : Bool) {b r N lp p t q h c a pd : ℕ}
    (hb : b < 128) (hr1 : 1 ≤ r) (hrN : r ≤ N) (hN : N = 2 ^ lp) (hlp : lp ≤ 10)
    {h0 h1 o0 o1 c0 c1 : E} {ws cv : List E} (hcl : cv.length = 4)
    (hch : ChainCells (h0, h1) (vxBlocks (ws.getD · 0)) (vxMd (decide (b = 127)) (cv.getD · 0)) 96 (o0, o1))
    {R : ℕ → Prop} (hRc : ∀ k < 4, R (c + 3 * b + k)) (hRh : ∀ k < 4, R (h + 2 * b + k))
    (hRt : ∀ k < 2, R (t + 2 * b + k))
    (hRrow : ∀ j < r, R (q + j) ∧ R (a + 129 * j + b) ∧ R (a + 129 * j + b + 1) ∧
      (store = true → R (p + j) ∧ R (pd + 128 * j + 2 * b) ∧ R (pd + 128 * j + 2 * b + 1)))
    (fp : ℕ) (rd : Reader)
    (hhs : CellsAt rd (gen ^ h * (gen ^ b * gen ^ b)) [h0, h1])
    (hho : CellsAt rd (gen ^ h * (gen ^ b * gen * (gen ^ b * gen))) [o0, o1])
    (hcv : CellsAt rd (gen ^ c * (gen ^ b * gen ^ b * gen ^ b)) cv)
    (hws : ∀ k < 256, ∀ v, rd (gpow (fp + fs (colName store) + 4 * N + fs "da_vector_dispatch" +
      cert (vxName (decide (b = 127))) (.n 4) + k)) = some v → v = ws.getD k 0)
    (hrows : ∀ j < r, RowCell store rd (gen ^ (fp + fs (colName store) + 4 * N + fs "da_vector_dispatch" +
      cert (vxName (decide (b = 127))) (.n 4))) (gen ^ q) (gen ^ b) (gen ^ (fp + fs (colName store))) (gen ^ p)
      (gen ^ j))
    (hrb : ∀ j < r, rd (gpow (q + j)) = some (gen ^ (a + 129 * j)))
    (hpb : store = true → ∀ j < r, rd (gpow (p + j)) = some (gen ^ (pd + 128 * j)))
    (hgap : ∀ d < N - r, GapStep rd (gen ^ (fp + fs (colName store))) (gen ^ r) (gen ^ d))
    (hlv : Meaning_da_levels lp rd [gen ^ (fp + fs (colName store))] [c0, c1])
    (hct : CellsAt rd (gen ^ t * (gen ^ b * gen ^ b)) [c0, c1]) :
    RelAtInW fs cert wId rd R (fun _ => False) fp (colTot fs store b r N lp) (colName store)
      [gen ^ b, gen ^ r, gen ^ N, gen ^ (N - r), gen ^ lp, gen ^ p, gen ^ t, gen ^ q, gen ^ h, gen ^ c] []
      fun θ => colTot θ store b r N lp := by
  set nodeP := fp + fs (colName store)
  set b0 := nodeP + 4 * N
  set lvP := b0 + fs "da_vector_dispatch" + cert (vxName (decide (b = 127))) (.n 4)
  have hN10 : N ≤ 1024 := by rw [hN]; exact le_trans (Nat.pow_le_pow_right (by norm_num) hlp) (by norm_num)
  have hr33 : r < 2 ^ 33 := by omega
  set σ := colVals (gen ^ b) (gen ^ r) (gen ^ N) (gen ^ (N - r)) (gen ^ lp) (gen ^ p) (gen ^ t) (gen ^ q)
    (gen ^ h) (gen ^ c) h0 h1 o0 o1 (gen ^ lvP) (gen ^ nodeP) c0 c1 with hσ
  -- the body holds
  have hdisp : Meaning_da_vector_dispatch rd [gen ^ b, h0, h1, gen ^ c] [o0, o1, gen ^ lvP] :=
    (da_vector_dispatch_iff rd _ _).mp
      (vd_relAtIn fs cert (D := fun _ => False) hb rfl rfl hch hRc b0 (fun _ h => h.elim) rd hcv hcl hws).toRelAtIn.relAt.rel
  have hrowL : LoopTo (gen ^ r) fun j => RowCell store rd (gen ^ lvP) (gen ^ q) (gen ^ b) (gen ^ nodeP) (gen ^ p)
      (gen ^ j) := loopTo_all' hr1 hr33 hrows
  have hgapL : gen ^ (N - r) ≠ 1 → LoopTo (gen ^ (N - r)) fun j => GapStep rd (gen ^ nodeP) (gen ^ r) (gen ^ j) :=
    fun hne => loopTo_all' (by by_contra h0; exact hne (by rw [show N - r = 0 by omega, pow_zero])) (by omega) hgap
  have hholds := col_holds store hhs hdisp hho (isInK_gen_pow r) (fun _ => hrowL) (isInK_gen_pow _) hgapL
    ⟨lp, by omega, rfl, hlv⟩ hct (xb := gen ^ b) (np := gen ^ N) (glp := gen ^ lp) (rb := gen ^ q)
  -- the path
  have hx : σ (.n 4) = ofK (gpow lp) := by rw [← gen_pow_eq_ofK]; rfl
  have hw := walk_dispatch σ (colPre store) colPost (colPre_straight store) colPost_straight (.n 4) dlNames
    [.n 23] [.n 30, .n 31] [] (i := lp) (by simp [dlNames]; omega) (by simp [dlNames]) hx
  rw [← colBody_split] at hw
  set es := (colPre store).flatMap (Main.slEvs σ) ++
    .call dlNames[lp]! [.n 23] [.n 30, .n 31] :: colPost.flatMap (Main.slEvs σ) with hes
  have hev := holds_of_holdsList (find_col store) hholds hw
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ (colPre_straight store)
  obtain ⟨hqd, hqa, hqad, hqc⟩ := Main.straight_parts σ _ colPost_straight
  have h22 : σ (.n 22) = gen ^ (4 * N) := by
    show gen ^ N * gen ^ N * (gen ^ N * gen ^ N) = _; ring
  have hal : allocs σ es = [4 * N] := by
    rw [hes, allocs_append, show allocs σ (.call dlNames[lp]! [.n 23] [.n 30, .n 31] ::
      colPost.flatMap (Main.slEvs σ)) = allocs σ (colPost.flatMap (Main.slEvs σ)) from rfl, hpa, hqa,
      show (colPre store).filterMap Main.Stmt.allocSz = [(.n 23, .inr (.n 22))] by cases store <;> rfl]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, h22, logG_gen_pow (show 4 * N < 2 ^ 64 - 1 by omega)]
    rfl
  have hown : ∀ i, nodeP ≤ i → i < nodeP + 4 * N → ownData cert fp (fp + fs (colName store)) (colName store)
      [4 * N] es i := fun i h1 h2 => Or.inl ⟨(4 * N, nodeP), List.Mem.head _, h1, h2⟩
  have hcalls : calls es = [⟨"da_vector_dispatch", [.n 0, .n 12, .n 13, .n 9], [.n 14, .n 15, .n 16], true⟩,
      ⟨rowName store, [.n 26, .n 1, .n 16, .n 7, .n 0, .n 23, .n 5], [], true⟩,
      ⟨gapName store, [.n 29, .n 3, .n 23, .n 1], [], decide (N - r ≠ 0)⟩,
      ⟨dlNames[lp]!, [.n 23], [.n 30, .n 31], true⟩] := by
    rw [hes, calls_append, show calls (.call dlNames[lp]! [.n 23] [.n 30, .n 31] ::
      colPost.flatMap (Main.slEvs σ)) = ⟨dlNames[lp]!, [.n 23], [.n 30, .n 31], true⟩ ::
        calls (colPost.flatMap (Main.slEvs σ)) from rfl, hpc, hqc,
      show (colPre store).filterMap Main.Stmt.callS = [(none, "da_vector_dispatch", [.n 0, .n 12, .n 13, .n 9],
        [.n 14, .n 15, .n 16]), (some (.n 25), rowName store, [.n 26, .n 1, .n 16, .n 7, .n 0, .n 23, .n 5], []),
        (some (.n 28), gapName store, [.n 29, .n 3, .n 23, .n 1], [])] by cases store <;> rfl,
      show colPost.filterMap Main.Stmt.callS = [] from rfl]
    have h25 : decide (σ (.n 25) ≠ 0) = true := by
      rw [decide_eq_true_iff]
      exact one_add_ne_zero.mpr fun he => by have := (gen_pow_eq_one_iff (by omega)).mp he; omega
    have h28 : decide (σ (.n 28) ≠ 0) = decide (N - r ≠ 0) := by
      show decide (1 + gen ^ (N - r) ≠ 0) = _
      refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he, pow_zero]; exact e_add_eq_zero_iff.mpr rfl),
        fun h he => h ?_⟩
      have := (gen_pow_eq_one_iff (show N - r < 2 ^ 64 - 1 by omega)).mp (e_add_eq_zero_iff.mp he).symm
      exact this
    simp only [List.map_cons, List.map_nil, Main.mkCall, h25, h28, List.nil_append, List.cons_append]
  -- the callees
  have hrowRel : coreProgram.Rel rd (rowName store) [gen ^ 0, gen ^ r, gen ^ lvP, gen ^ q, gen ^ b, gen ^ nodeP, gen ^ p] [] := by
    rw [pow_zero]; exact (row_loop_meaning store rd _ _ _ _ _ _).mpr hrowL
  have kid2 := relAtInW_of_relInTW_pure fs cert (row_pure store) (by simp)
    (rowLoop_relInT fs store (R := RowR store r lvP q b nodeP p a pd) hr33 hrb hpb (fun _ h => h) hr1 hrowRel)
    (b0 + (fs "da_vector_dispatch" + fs (vxName (decide (b = 127)))))
  rw [pow_zero] at kid2
  have hlvRel : coreProgram.Rel rd (dlNames.getD lp "") [gen ^ nodeP] [c0, c1] := (da_levels_iff lp hlp _ _).mpr hlv
  have kid4 := relAtInW_of_relInTW_pure fs cert (lv_pure hlp) (by simp [lvSet])
    (levels_relInT fs hlp (R := TreeR nodeP lp) (fun _ h => h) hlvRel)
  rw [← dlNames_getElem! (by omega)] at kid4
  have h := relAtInW_of_walk (fs := fs) (cert := cert) (w := wId) (σ := σ) (rd := rd)
    (R := R) (D := fun _ => False) (Dk := fun _ => False) (fp := fp)
    (N := fs "da_vector_dispatch" + fs (vxName (decide (b = 127))) + (rowTot fs store r 0 +
      ((if N - r = 0 then fs (gapName store) else gapTot fs store (N - r) 0) + (dlTot fs lp + 0))))
    (bws := [fun θ => θ "da_vector_dispatch" + θ (vxName (decide (b = 127))), fun θ => rowTot θ store r 0,
      fun θ => gapTot θ store (N - r) 0, fun θ => dlTot θ lp])
    (find_col store) (Or.inl (by cases store <;> decide +kernel)) rfl hw rfl hev
    (by
      rw [hal, hes, allocDsts_append, show allocDsts (.call dlNames[lp]! [.n 23] [.n 30, .n 31] ::
        colPost.flatMap (Main.slEvs σ)) = allocDsts (colPost.flatMap (Main.slEvs σ)) from rfl, hpd, hqd,
        show (colPre store).filterMap Main.Stmt.allocSz = [(.n 23, .inr (.n 22))] by cases store <;> rfl,
        show colPost.filterMap Main.Stmt.allocSz = [] from rfl]
      simp only [List.map_cons, List.map_nil, List.append_nil, bases]
      rw [← gen_pow_eq_ofK]; rfl)
    (fun q hq => by
      rw [hes, addrs_append, show addrs (.call dlNames[lp]! [.n 23] [.n 30, .n 31] ::
        colPost.flatMap (Main.slEvs σ)) = addrs (colPost.flatMap (Main.slEvs σ)) from rfl, hpad, hqad,
        show (colPre store).filterMap Main.Stmt.addrS = [] by cases store <;> rfl,
        show colPost.filterMap Main.Stmt.addrS = [] from rfl] at hq
      simp at hq)
    ?_ ?_ (fun _ h => h.elim)
  · rw [hal, List.sum_cons, List.sum_nil, Nat.add_zero] at h
    refine h.wmono fun θ => ?_
    have hg : (if N - r = 0 then θ (gapName store) else gapTot θ store (N - r) 0) = gapTot θ store (N - r) 0 := by
      split_ifs with h0
      · simp [gapTot, h0]
      · rfl
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, colTot, hg, wId]
    omega
  · rw [hcalls, hal, List.sum_cons, List.sum_nil, Nat.add_zero]
    refine ⟨_, _, R, fun i => lvP ≤ i ∧ i < lvP + 256, rfl, fun i hi => Or.inl (Or.inl hi),
      vd_relAtIn fs cert hb rfl rfl hch hRc b0 (fun _ h => h) rd hcv hcl hws, ?_⟩
    refine ⟨_, _, RowR store r lvP q b nodeP p a pd, fun _ => False, rfl, fun i hi => ?_, kid2, ?_⟩
    · rcases hi with ⟨j, hj, hc⟩ | hl
      · obtain ⟨r1, r2, r3, r4⟩ := hRrow j hj
        rcases hc with rfl | rfl | rfl | rfl | rfl | ⟨hs, rfl | rfl | rfl⟩
        · exact Or.inl (Or.inl r1)
        · exact Or.inl (Or.inl r2)
        · exact Or.inl (Or.inl r3)
        · exact Or.inl (Or.inr (hown (nodeP + 2 * j) (by omega) (by omega)))
        · exact Or.inl (Or.inr (hown (nodeP + 2 * j + 1) (by omega) (by omega)))
        · exact Or.inl (Or.inl (r4 hs).1)
        · exact Or.inl (Or.inl (r4 hs).2.1)
        · exact Or.inl (Or.inl (r4 hs).2.2)
      · exact Or.inr (Or.inr ⟨rfl, hl⟩)
    by_cases hG : N - r = 0
    · refine ⟨_, _, fun _ => False, fun _ => False, rfl, fun i hi => hi.elim, ?_, ?_⟩
      · simp only [hG, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      · simp only [hG, ↓reduceIte]
        refine ⟨_, _, TreeR nodeP lp, fun _ => False, rfl, fun i hi => Or.inl (Or.inr (hown _ hi.1
          (by unfold TreeR at hi; rw [hN]; omega))), kid4 _, ⟨rfl, fun i hi => hi.elim⟩⟩
    · have hGp : 0 < N - r := by omega
      have hgRel : coreProgram.Rel rd (gapName store) [gen ^ 0, gen ^ (N - r), gen ^ nodeP, gen ^ r] [] := by
        rw [pow_zero]
        exact (gap_loop_meaning store rd _ _ _).mpr (hgapL fun he => hG ((gen_pow_eq_one_iff (by omega)).mp he))
      have kid3 := relAtInW_of_relInTW_pure fs cert (gap_pure store) (by simp)
        (gapLoop_relInT fs store (R := GapR r (N - r) nodeP) (by omega) (fun _ h => h) hGp hgRel)
      rw [pow_zero] at kid3
      refine ⟨_, _, GapR r (N - r) nodeP, fun _ => False, rfl, fun i hi => ?_, ?_, ?_⟩
      · obtain ⟨d, hd, hi⟩ := hi
        rcases hi with rfl | rfl
        · exact Or.inl (Or.inr (hown (nodeP + 2 * (r + d)) (by omega) (by omega)))
        · exact Or.inl (Or.inr (hown (nodeP + 2 * (r + d) + 1) (by omega) (by omega)))
      · simp only [ne_eq, hG, not_false_eq_true, decide_true, ↓reduceIte]
        exact kid3 _
      · simp only [hG, ↓reduceIte]
        refine ⟨_, _, TreeR nodeP lp, fun _ => False, rfl, fun i hi => Or.inl (Or.inr (hown _ hi.1
          (by unfold TreeR at hi; rw [hN]; omega))), kid4 _, ⟨rfl, fun i hi => hi.elim⟩⟩
  · intro A hA
    rw [hes, loadAddrs_append, show loadAddrs σ (.call dlNames[lp]! [.n 23] [.n 30, .n 31] ::
      colPost.flatMap (Main.slEvs σ)) = loadAddrs σ (colPost.flatMap (Main.slEvs σ)) from rfl,
      loadAddrs_straight σ _ (colPre_straight store), loadAddrs_straight σ _ colPost_straight,
      show (colPre store).filterMap stmtLoad? = [(.n 11, 0), (.n 11, 1), (.n 20, 0), (.n 20, 1)] by cases store <;> rfl,
      show colPost.filterMap stmtLoad? = [(.n 33, 0), (.n 33, 1)] from rfl] at hA
    have g11 : σ (.n 11) = gen ^ (h + 2 * b) := by show gen ^ h * (gen ^ b * gen ^ b) = _; ring
    have g20 : σ (.n 20) = gen ^ (h + 2 * b + 2) := by show gen ^ h * (gen ^ b * gen * (gen ^ b * gen)) = _; ring
    have g33 : σ (.n 33) = gen ^ (t + 2 * b) := by show gen ^ t * (gen ^ b * gen ^ b) = _; ring
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by rw [g11, addr_gen], Or.inr (Or.inl (hRh 0 (by omega)))⟩
    · exact ⟨_, by rw [g11, addr_gen], Or.inr (Or.inl (hRh 1 (by omega)))⟩
    · exact ⟨_, by rw [g20, addr_gen], Or.inr (Or.inl (by have := hRh 2 (by omega); rwa [Nat.add_zero] at *))⟩
    · exact ⟨_, by rw [g20, addr_gen], Or.inr (Or.inl (by have := hRh 3 (by omega); rwa [show h + 2 * b + 2 + 1 = h + 2 * b + 3 by ring]))⟩
    · exact ⟨_, by rw [g33, addr_gen], Or.inr (Or.inl (hRt 0 (by omega)))⟩
    · exact ⟨_, by rw [g33, addr_gen], Or.inr (Or.inl (hRt 1 (by omega)))⟩

end
end LeanVM.Guest.B1.Digest
