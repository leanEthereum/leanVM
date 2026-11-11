/-
  LeanVM.Guest.WalkOsPre

  What `open_stacked`'s dispatch into `level_positions` writes: at the rate's arm, the squeeze
  loop's decodes, whose window pointers name windows (`QueryWinsOk`), the walk's obligation
  (`OqMainWins`) at the level's queries.
-/

module

public import LeanVM.Guest.WalkOsDefs
public import LeanVM.Guest.B1.Whir.Flat
public import LeanVM.Guest.B1.Whir.HelperT
public import LeanVM.Guest.B1.Whir.DataSpec
public import LeanVM.Guest.B1.Opening.QueriesWalk
public import LeanVM.Guest.B1.Bits.QueryWindowsAll

/-!
# `level_positions`' windows (TRIAGE G #42)

* `holdsList_flatD`: a block of atoms, calls and dispatches that holds holds statement by
  statement (`StmtOkD`, a dispatch's arm at its selector).
* `lpLoop_sound`: `level_positions`' loop (`lpLoopBody`) decodes, at every iteration `g^j` of
  `sq`, a squeeze's positions and windows at `qpos·g^(j·192/d)` and `qbp·g^(j·192/d)`.
* `lp_sound`: from a call of a specialization (`lpBody`) at `[fs0..fs4, qpos, qbp, tabs]`, the
  window pointers at `qbp` name the windows of every query `sq·192/d` decodes (`QueryWinsOk`), and
  so `OqMainWins` at `g^n` for a walk of `oqCount odd base n ≤ sq·192/d` queries.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Flat blocks with dispatches -/

/-- A statement's relation, a dispatch's at its selector's arm. -/
def StmtOkD (C : CallRel) (rd : Reader) (σ : Val) : Stmt → Prop
  | .atom a => a.Holds rd σ
  | .call f args rets => C f (args.map σ) (rets.map σ)
  | .callIf c f args => IsInK (σ c) ∧ (σ c ≠ 0 → C f (args.map σ) [])
  | .dispatch x fs args rets => ∃ (j : ℕ) (h : j < fs.length), σ x = ofK (addressOfIndex j) ∧
      C fs[j] (args.map σ) (rets.map σ)
  | _ => True

/-- **A block of atoms, calls and dispatches holds** statement by statement. -/
theorem holdsList_flatD : ∀ (ss : List Stmt), ss.all flatD = true → ∀ (next : Prop)
    (kret : List E → Prop), Stmt.HoldsList C rd σ ss next kret → (∀ s ∈ ss, StmtOkD C rd σ s) ∧ next
  | [], _, _, _, h => ⟨fun _ hs ↦ absurd hs (by simp), h⟩
  | s :: ss, hf, next, kret, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hf
    obtain ⟨hs, hf⟩ := hf
    have key : StmtOkD C rd σ s ∧ Stmt.HoldsList C rd σ ss next kret := by
      match s, hs with
      | .atom a, _ => exact h
      | .call f args rets, _ => exact h
      | .callIf c f args, _ => exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
      | .dispatch x fs args rets, _ => exact h
    obtain ⟨hk, ht⟩ := key
    obtain ⟨hall, hn⟩ := holdsList_flatD ss hf next kret ht
    refine ⟨fun t ht' ↦ ?_, hn⟩
    rcases List.mem_cons.mp ht' with rfl | ht'
    · exact hk
    · exact hall t ht'

/-- Every statement before `start` holds (one past the body a `ret`, which says nothing). -/
theorem okAt {body : List Stmt} {start i : ℕ} (h : ∀ s ∈ body.take start, StmtOkD C rd σ s)
    (hi : i < start) : StmtOkD C rd σ (stmtAt body i) := by
  unfold stmtAt
  by_cases hl : i < body.length
  · rw [List.getD_eq_getElem _ _ hl]
    exact h _ (List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩)
  · rw [List.getD_eq_default _ _ (by omega)]
    trivial

/-- A flat statement's relation is its `StmtOkD`. -/
theorem stmtOk_of_D {s : Stmt} (hs : Stmt.flat s = true) (h : StmtOkD C rd σ s) :
    Whir.StmtOk C rd σ s := by
  match s, hs with
  | .atom _, _ => exact h
  | .call .., _ => exact h
  | .callIf .., _ => exact h
  | .dispatch .., _ => exact h

/-- **The window table** from a run of the body before the cut. -/
theorem winTabs_of_body {body : List Stmt} {start hw : ℕ}
    (h : ∀ s ∈ body.take start, StmtOkD C rd σ s) (hle : hw + osWinTabs.length ≤ start)
    (heq : stmtsEqb ((body.drop hw).take osWinTabs.length) osWinTabs = true) :
    WinTabs rd (σ (.n osWin)) := by
  have hmem : ∀ s ∈ osWinTabs, s ∈ body.take start := by
    intro s hs
    rw [← stmtsEqb_sound heq] at hs
    have h1 : s ∈ body.take (hw + osWinTabs.length) := by
      rw [List.take_add]; exact List.mem_append_right _ hs
    rw [← Nat.min_eq_left hle, ← List.take_take] at h1
    exact List.mem_of_mem_take h1
  intro n hn
  have hc := h _ (hmem _ (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨n, List.mem_range.mpr hn, rfl⟩,
    List.mem_cons_self ..⟩))
  have hl := h _ (hmem _ (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨n, List.mem_range.mpr hn, rfl⟩,
    List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩))
  simp only [StmtOkD, Atom.Holds] at hc hl
  rw [hc, word_eOfNat] at hl
  exact hl

/-! ## The loop -/

/-- `level_positions`' loop before its tail: the squeeze, the pointers shifted, the decode. -/
def lpLoopA (d cd : ℕ) : List Stmt :=
  let pw := osPowSteps 0 (osPowDigits (192 / d)) 0 40
  let e := 40 + osPowLen (192 / d)
  ([.atom (.mul (.n 6) (.n 0) (.n 0)), .atom (.mul (.n 7) (.n 6) (.n 6)), .atom (.mul (.n 8) (.n 7) (.n 0)),
    .atom (.mul (.n 9) (.n 2) (.n 8))] ++
    ((List.range 5).map fun i ↦ .atom (.load (.n (10 + i)) (.n 9) i)) ++
    [.atom (.const (.n 15) (word 1 0 0)), .atom (.const (.n 16) (word 0 0 0)),
      .atom (.const (.n 17) (word 0 0 0)), .atom (.const (.n 18) (word 0 0 0)),
      .atom (.const (.n 19) (word 0 0 0))] ++
    osSqueeze0 15 [10, 11, 12, 13, 14] 20 ++
    ((List.range 5).map fun i ↦ .atom (.load (.n (28 + i)) (.n 9) (5 + i)))) ++
    pw.1 ++ [.atom (.mul (.n e) (.n 3) (.n pw.2)), .atom (.mul (.n (e + 1)) (.n 4) (.n pw.2)),
      .call ("decode_query_windows__L" ++ natStr d ++ "_L" ++ natStr cd) [.n 39, .n e, .n (e + 1), .n 5] []]

theorem lpLoopBody_split (d cd : ℕ) (name : String) :
    lpLoopBody d cd name = (lpLoopA d cd ++ osLoopTailA (40 + osPowLen (192 / d) + 2)) ++
      [.callIf (.n (40 + osPowLen (192 / d) + 2 + 2)) name
        (.n (40 + osPowLen (192 / d) + 2 + 4) :: (List.range (6 - 1)).map fun i ↦ .n (i + 1)),
        .ret []] := by
  simp only [lpLoopBody, lpLoopA, osLoopTail_split, List.append_assoc, List.cons_append,
    List.nil_append]

theorem lpLoopA_flat (d cd : ℕ) :
    (lpLoopA d cd ++ osLoopTailA (40 + osPowLen (192 / d) + 2)).all Stmt.flat = true := by
  have hpw : ∀ ds acc k, (osPowSteps 0 ds acc k).1.all Stmt.flat = true := by
    intro ds
    induction ds with
    | nil => intro _ _; rfl
    | cons d ds ih =>
      intro acc k
      cases d <;> simp [osPowSteps, ih, Stmt.flat]
  simp [lpLoopA, osSqueeze0, keccakA, challengeT, osLoopTailA, hpw, Stmt.flat]

/-- One iteration of `level_positions`' loop at `x`: a squeeze's positions and windows decoded at
`qpos·x^(192/d)` and `qbp·x^(192/d)`. -/
def LpIter (rd : Reader) (d cd : ℕ) (qpos qbp tabs x : E) : Prop :=
  ∃ w, MeaningDecodeQueryWindows d cd rd [w, qpos * x ^ (192 / d), qbp * x ^ (192 / d), tabs] []

theorem lpLoop_step (d cd : ℕ) (hpw : digitsVal (osPowDigits (192 / d)) 1 = 192 / d)
    (hdec : ∀ args rets, WinTabs rd (args.getD 3 0) →
      coreProgram.Rel rd ("decode_query_windows__L" ++ natStr d ++ "_L" ++ natStr cd) args rets →
        MeaningDecodeQueryWindows d cd rd args rets)
    (σ : Val) (x N sqz qpos qbp tabs : E) (hwt : WinTabs rd tabs)
    (hp : (osParams 6).map σ = [x, N, sqz, qpos, qbp, tabs])
    (hA : AllOk (coreProgram.Rel rd) rd σ (lpLoopA d cd ++ osLoopTailA (40 + osPowLen (192 / d) + 2))) :
    LpIter rd d cd qpos qbp tabs x ∧ σ (.n (40 + osPowLen (192 / d) + 2 + 2)) = x * gen + N ∧
      (.n (40 + osPowLen (192 / d) + 2 + 4) :: (List.range (6 - 1)).map fun i ↦ V.n (i + 1)).map σ =
        x * gen :: [N, sqz, qpos, qbp, tabs] := by
  simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons.injEq, and_true, List.cons_append] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hp
  rw [allOk_append] at hA
  obtain ⟨hA, hT⟩ := hA
  obtain ⟨t2, t4⟩ := osLoopTailA_val hT
  unfold lpLoopA at hA
  simp only [allOk_append] at hA
  obtain ⟨⟨-, hpw1⟩, hL⟩ := hA
  simp only [allOk_cons, allOk_nil, and_true, Whir.StmtOk, Atom.Holds, List.map_cons, List.map_nil] at hL
  obtain ⟨hmul1, hmul2, hdc⟩ := hL
  have hpwv := osPowSteps_val (C := coreProgram.Rel rd) (σ := σ) 0 (osPowDigits (192 / d)) 0 40
    1 (by rw [pow_one]) hpw1
  rw [hpw, h0] at hpwv
  rw [hpwv, h3] at hmul1
  rw [hpwv, h4] at hmul2
  refine ⟨⟨σ (.n 39), ?_⟩, ?_, ?_⟩
  · have := hdec _ _ (by simpa [h5] using hwt) hdc
    rwa [hmul1, hmul2, h5] at this
  · rw [t2, h0, h1]
  · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, Nat.zero_add, t4, h0, h1, h2, h3, h4, h5]

/-- **`level_positions`' loop, soundly**: entered from `1` with the bound `g^n`, `0 < n < ord g`,
every iteration `g^j`, `j < n`, decoded. -/
theorem lpLoop_sound {name : String} {d cd : ℕ}
    (hloop : FnIs name (osParams 6) (lpLoopBody d cd name))
    (hpw : digitsVal (osPowDigits (192 / d)) 1 = 192 / d)
    (hdec : ∀ args rets, WinTabs rd (args.getD 3 0) →
      coreProgram.Rel rd ("decode_query_windows__L" ++ natStr d ++ "_L" ++ natStr cd) args rets →
        MeaningDecodeQueryWindows d cd rd args rets)
    {n : ℕ} (hn0 : 0 < n) (hn : n < ordG) (sqz qpos qbp tabs : E) (hwt : WinTabs rd tabs)
    (hg : 1 + gen ^ n ≠ 0 → coreProgram.Rel rd name [1, gen ^ n, sqz, qpos, qbp, tabs] []) :
    ∀ j < n, LpIter rd d cd qpos qbp tabs (gen ^ j) := by
  obtain ⟨fn, hf, hps, hb⟩ := hloop
  rw [lpLoopBody_split] at hb
  refine loop_guarded (rest := [sqz, qpos, qbp, tabs]) hn0 hn rfl
    (loop_sound_flat hf (lpLoopA_flat d cd) hb ?_) hg
  intro σ x hp hA
  rw [hps] at hp
  exact lpLoop_step d cd hpw hdec σ x (gen ^ n) sqz qpos qbp tabs hwt hp hA

/-! ## The specialization -/

/-- `level_positions` before its returns, and the `ret`. -/
theorem lpBody_split (sq : ℕ) (loop : String) :
    lpBody sq loop = (osHeap ((sq + 1) * 5) 8 ++
      ((List.range 5).map fun i ↦ Stmt.atom (.load (.n i) (.n 9) i)) ++
      osLoopCall loop sq [9, 5, 6, 7] 10 ++
      ([Stmt.atom (.const (.n 15) (gw (sq * 5))), Stmt.atom (.mul (.n 16) (.n 9) (.n 15))] ++
        ((List.range 5).map fun i ↦ Stmt.atom (.load (.n (17 + i)) (.n 16) i)) ++
        ((List.range 5).map fun i ↦ Stmt.atom (.copy (.n (22 + i)) (.n (17 + i)))))) ++
      [Stmt.ret ((List.range 5).map fun i ↦ .n (22 + i))] := by
  simp only [lpBody, List.append_assoc]

theorem lpBodyA_flat (sq : ℕ) (loop : String) :
    (osHeap ((sq + 1) * 5) 8 ++ ((List.range 5).map fun i ↦ Stmt.atom (.load (.n i) (.n 9) i)) ++
      osLoopCall loop sq [9, 5, 6, 7] 10 ++
      ([Stmt.atom (.const (.n 15) (gw (sq * 5))), Stmt.atom (.mul (.n 16) (.n 9) (.n 15))] ++
        ((List.range 5).map fun i ↦ Stmt.atom (.load (.n (17 + i)) (.n 16) i)) ++
        ((List.range 5).map fun i ↦ Stmt.atom (.copy (.n (22 + i)) (.n (17 + i)))))).all
      Stmt.flat = true := by
  simp [osHeap, osLoopCall, Stmt.flat]

/-- **The window pointers name windows**: every decoded query's pointer, at `qbp`, a frame run of
its windows at a position below `2^d`. -/
theorem queryWinsOk_of_iters {d cd q nsq : ℕ} (hd : 1 ≤ 192 / d) (hq : q ≤ nsq * (192 / d))
    {qpos qbp tabs : E} (hit : ∀ jj < nsq, LpIter rd d cd qpos qbp tabs (gen ^ jj)) :
    QueryWinsOk rd qbp q d cd := by
  intro k hk bp hbp
  set per := 192 / d
  have hjj : k / per < nsq := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; exact lt_of_lt_of_le hk hq
  have ht : k % per < per := Nat.mod_lt _ (by omega)
  have hk' : k = k / per * per + k % per := by
    have := Nat.div_add_mod k per; rw [Nat.mul_comm] at this; omega
  obtain ⟨w, hw⟩ := hit (k / per) hjj
  obtain ⟨-, hall⟩ := hw
  obtain ⟨-, p, hptr, hrun⟩ := hall (k % per) ht
  rw [← pow_mul, loadHolds_mul_gen_pow, ← hk'] at hptr
  rw [loadHolds_unique hbp hptr]
  exact ⟨qwPosOf d w (k % per), by unfold qwPosOf; exact Nat.mod_lt _ (by positivity), hrun⟩

/-- What a `level_positions` specialization of the table is: its body and its loop's. -/
def LpOk (e : String × ℕ × ℕ × ℕ × String) : Prop :=
  FnIs e.1 (osParams 8) (lpBody e.2.1 e.2.2.2.2) ∧
    FnIs e.2.2.2.2 (osParams 6) (lpLoopBody e.2.2.1 e.2.2.2.1 e.2.2.2.2)

/-- **A call of `level_positions`** at `[fs0..fs4, qpos, qbp, tabs]`, the table at `tabs`: its
window pointers at `qbp` name windows for the walk of `oqCount odd base n` queries it covers. -/
theorem lp_sound {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {e : String × ℕ × ℕ × ℕ × String}
    (he : LpOk e) {n odd base : ℕ} (hodd : odd = 1 → base = 1)
    (hcov : lpCovers e.2.1 n odd base e.2.2.1 e.2.2.2.1 = true)
    {args rets : List E} (hl : args.length = 8) (hwt : WinTabs L.read (args.getD 7 0))
    (hrel : coreProgram.Rel L.read e.1 args rets) :
    OqMainWins L.read e.2.2.1 e.2.2.2.1 odd base (args.getD 6 0) (gen ^ n) := by
  obtain ⟨name, sq, d, cd, loop⟩ := e
  obtain ⟨⟨fn, hf, hps, hb⟩, hloop⟩ := he
  dsimp only at hf hb hloop hcov hrel hwt ⊢
  simp only [lpCovers, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, beq_iff_eq,
    List.contains_iff_mem] at hcov
  obtain ⟨⟨⟨⟨⟨hq, hper⟩, hpw⟩, hs0⟩, hso⟩, hshape⟩ := hcov
  obtain ⟨fn', hf', σ, hp, hbody⟩ := (rel_iff _ _ _ _).mp hrel
  obtain rfl := Option.some.inj (hf.symm.trans hf')
  rw [hb, lpBody_split, holdsList_flat_ret _ (lpBodyA_flat sq loop)] at hbody
  obtain ⟨hA, -⟩ := hbody
  simp only [allOk_append] at hA
  obtain ⟨⟨-, hL⟩, -⟩ := hA
  simp only [osLoopCall, allOk_cons, allOk_nil, and_true, Whir.StmtOk, Atom.Holds, List.map_cons,
    List.map_nil] at hL
  obtain ⟨c10, c11, a12, c13, c14, -, hcall⟩ := hL
  rw [hps] at hp
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ :
      ∃ a0 a1 a2 a3 a4 a5 a6 a7, args = [a0, a1, a2, a3, a4, a5, a6, a7] := by
    match args, hl with
    | [a0, a1, a2, a3, a4, a5, a6, a7], _ => exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩
  simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq, and_true] at hp
  obtain ⟨-, -, -, -, -, h5, h6, h7⟩ := hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hwt ⊢
  have hgn : gw sq = gen ^ sq := gw_eq (by
    have : ordG < u128Bound := by unfold ordG u128Bound; norm_num
    omega)
  have hdec := fun args rets hw h ↦
    decode_query_windows_all_holds _ hshape (κ := κ) hκ L args rets hw h
  have hit := lpLoop_sound hloop hpw hdec hs0 hso (σ (.n 9)) a5 a6 a7 hwt (by
    rw [a12, c10, c11, c13, c14, hgn, word_one, h5, h6, h7] at hcall
    exact hcall)
  exact oqMainWins_of_queryWinsOk hodd (queryWinsOk_of_iters hper hq hit)

end
end LeanVM.Guest.End
