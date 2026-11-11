/-
  LeanVM.Guest.B1.Whir.LevelResidual

  `level_residual` (with `residual_batch` and its two loops), soundly: the residual chain of a
  level's queries.
-/

module

public import LeanVM.Guest.B1.Whir.ResLoop
public import LeanVM.Guest.B1.Whir.HelperT

/-!
# `level_residual`

`level_residual(positions, row_d, mu)` at `q` queries over `cols` columns returns the chain
`h ← (h + R(p))·μ` from `0` over the `q` positions at `positions`, `R` the residual on the row
`D` at `row_d` (`MeaningLevelResidual`): the batches' loop runs `residual_batch` (eight steps,
`residual_batch_sound`) an iteration (`lrLoop1_sound`, chained by `resChain`), then, when
`8 ∤ q`, the rest's loop one inline step an iteration (`lrLoop2_sound`, `restChain`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- The vanishing table's first entry for `cols` columns. -/
abbrev vanishOff (cols : ℕ) : ℕ := cols * (cols + 1) / 2

/-! ## `residual_batch` -/

/-- **`residual_batch(batch, row_d, mu, h)`** over `cols` columns: on the row `D` at `row_d`, eight
steps from `h` over the positions at `batch`. -/
def MeaningResidualBatch (cols : ℕ) (rd : Reader) : List E → List E → Prop
  | [batch, rowd, mu, h], rets => ∀ D : ℕ → E, (∀ s < cols, LoadHolds rd rowd s (D s)) →
      ∃ ps : List E, ps.length = resBatch ∧ (∀ i < resBatch, LoadHolds rd batch i (ps.getD i 0)) ∧
        rets = [resFold D (vanishOff cols) cols mu h ps]
  | _, _ => False

/-- `residual_batch`'s body before its `ret`. -/
def rbA (cols : ℕ) : List Stmt :=
  (osResSteps 0 1 0 (vanishOff cols) cols 2 (List.range resBatch) 3 4).1 ++
    [.atom (.copy (.n (osResSteps 0 1 0 (vanishOff cols) cols 2 (List.range resBatch) 3 4).2.2)
      (.n (osResSteps 0 1 0 (vanishOff cols) cols 2 (List.range resBatch) 3 4).2.1))]

theorem rbBody_split (cols : ℕ) : rbBody cols = rbA cols ++
    [.ret [.n (osResSteps 0 1 0 (vanishOff cols) cols 2 (List.range resBatch) 3 4).2.2]] := by
  simp only [rbBody, rbA, List.append_assoc, List.cons_append, List.nil_append]

theorem rbA_flat (cols : ℕ) : (rbA cols).all Stmt.flat = true := by
  simp [rbA, osResSteps_flat, Stmt.flat]

/-- **`residual_batch` is sound** at its template. -/
theorem residual_batch_sound {cols : ℕ} (hc : 1 ≤ cols)
    (hfn : FnIs (rbName cols) (osParams 4) (rbBody cols)) (args rets : List E)
    (h : coreProgram.Rel rd (rbName cols) args rets) : MeaningResidualBatch cols rd args rets := by
  obtain ⟨fn, hf, hps, hb⟩ := hfn
  rw [rel_iff_sem hf] at h
  obtain ⟨σ, hp, hh⟩ := h
  rw [hb, rbBody_split, holdsList_flat_ret _ (rbA_flat cols)] at hh
  obtain ⟨hok, hret⟩ := hh
  rw [hps] at hp
  subst hp hret
  rw [show (osParams 4).map σ = [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3)] from rfl]
  intro D hD
  rw [rbA, allOk_append] at hok
  obtain ⟨hs, hcp⟩ := hok
  obtain ⟨ps, hF, hv⟩ := osResSteps_val (bd := 1) (row := 0) hc (D := D)
    (fun s hs ↦ by rw [Nat.zero_add]; exact hD s hs) _ _ _ hs
  obtain ⟨hl, hF⟩ := forall₂_range_to _ _ hF
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hcp
  exact ⟨ps, hl, hF, by simp only [List.map_cons, List.map_nil]; rw [hcp, hv]⟩

/-! ## The batches' loop -/

/-- The batches' loop's body before its tail. -/
def lrLoop1A (cols : ℕ) : List Stmt :=
  [.atom (.mul (.n 6) (.n 0) (.n 0)), .atom (.mul (.n 7) (.n 6) (.n 6)), .atom (.mul (.n 8) (.n 7) (.n 7)),
    .atom (.mul (.n 9) (.n 3) (.n 8)), .atom (.mul (.n 10) (.n 2) (.n 0)), .atom (.load (.n 11) (.n 10) 0),
    .call (rbName cols) [.n 9, .n 4, .n 5, .n 11] [.n 12],
    .atom (.mul (.n 13) (.n 2) (.n 0)), .atom (.load (.n 12) (.n 13) 1)]

theorem lrLoop1Body_split (cols : ℕ) (name : String) :
    lrLoop1Body cols name = (lrLoop1A cols ++ osLoopTailA 14) ++
      [.callIf (.n (14 + 2)) name (.n (14 + 4) :: (List.range (6 - 1)).map fun i ↦ .n (i + 1)),
        .ret []] := by
  simp only [lrLoop1Body, lrLoop1A, osLoopTail_split, List.cons_append, List.nil_append]

theorem lrLoop1A_flat (cols : ℕ) : (lrLoop1A cols ++ osLoopTailA 14).all Stmt.flat = true := by
  simp [lrLoop1A, osLoopTailA, Stmt.flat]

theorem lrLoop1_step {cols : ℕ}
    (hrb : ∀ a r, coreProgram.Rel rd (rbName cols) a r → MeaningResidualBatch cols rd a r)
    (σ : Val) (x N chain qpos rowd mu : E)
    (hp : (osParams 6).map σ = [x, N, chain, qpos, rowd, mu]) {D : ℕ → E}
    (hD : ∀ s < cols, LoadHolds rd rowd s (D s))
    (hA : AllOk (coreProgram.Rel rd) rd σ (lrLoop1A cols ++ osLoopTailA 14)) :
    ResIter rd D (vanishOff cols) cols 0 qpos chain mu x ∧
      σ (.n (14 + 2)) = x * gen + N ∧
      (.n (14 + 4) :: (List.range (6 - 1)).map fun i ↦ V.n (i + 1)).map σ =
        x * gen :: [N, chain, qpos, rowd, mu] := by
  simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons.injEq, and_true, List.cons_append] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hp
  rw [allOk_append] at hA
  obtain ⟨hA, hT⟩ := hA
  obtain ⟨t2, t4⟩ := osLoopTailA_val hT
  refine ⟨?_, by rw [t2, h0, h1], ?_⟩
  · simp only [lrLoop1A, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.map_cons,
      List.map_nil] at hA
    obtain ⟨m6, m7, m8, m9, m10, l11, hcall, m13, s12⟩ := hA
    have hm := hrb _ _ hcall
    rw [h4] at hm
    obtain ⟨ps, hl, hps, hret⟩ := hm D hD
    simp only [List.cons.injEq, and_true] at hret
    have hP : σ (.n 9) = qpos * gen ^ 0 * x ^ resBatch := by
      rw [m9, m8, m7, m6, h0, h3]; ring
    refine ⟨σ (.n 11), ps, hl, by rw [← hP]; exact hps, ?_, ?_⟩
    · rw [← h2, ← h0, ← m10]; exact l11
    · rw [← h2, ← h0, ← m13, ← h5, ← hret]; exact s12
  · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, Nat.zero_add, t4, h0, h1, h2, h3, h4, h5]

/-- **The batches' loop, soundly**: entered from `1` with the bound `g^n`, `0 < n < ord g`, the
iteration's meaning holds at every `g^j`, `j < n`. -/
theorem lrLoop1_sound {name : String} {cols : ℕ}
    (hloop : FnIs name (osParams 6) (lrLoop1Body cols name))
    (hrb : ∀ a r, coreProgram.Rel rd (rbName cols) a r → MeaningResidualBatch cols rd a r)
    {n : ℕ} (hn0 : 0 < n) (hn : n < ordG) (chain qpos rowd mu : E) {D : ℕ → E}
    (hD : ∀ s < cols, LoadHolds rd rowd s (D s))
    (hg : 1 + gen ^ n ≠ 0 → coreProgram.Rel rd name [1, gen ^ n, chain, qpos, rowd, mu] []) :
    ∀ j < n, ResIter rd D (vanishOff cols) cols 0 qpos chain mu (gen ^ j) := by
  obtain ⟨fn, hf, hps, hb⟩ := hloop
  rw [lrLoop1Body_split] at hb
  refine loop_guarded (rest := [chain, qpos, rowd, mu]) hn0 hn rfl
    (loop_sound_flat hf (lrLoop1A_flat cols) hb ?_) hg
  intro σ x hp hA
  rw [hps] at hp
  exact lrLoop1_step hrb σ x (gen ^ n) chain qpos rowd mu hp hD hA

/-! ## The rest's loop -/

/-- One iteration of the rest's loop at `x`: `h = rest[x]`, the position `tail[x]`, one step. -/
def RestIter (rd : Reader) (D : ℕ → E) (vo ml : ℕ) (rest tail mu x : E) : Prop :=
  ∃ h p : E, LoadHolds rd (rest * x) 0 h ∧ LoadHolds rd (tail * x) 0 p ∧
    LoadHolds rd (rest * x) 1 (resFold D vo ml mu h [p])

/-- The rest's loop's body before its tail. -/
def lrLoop2A (cols : ℕ) : List Stmt :=
  let e := osResQuery 9 4 0 (vanishOff cols) cols 10
  [.atom (.mul (.n 6) (.n 2) (.n 0)), .atom (.load (.n 7) (.n 6) 0), .atom (.mul (.n 8) (.n 3) (.n 0)),
    .atom (.load (.n 9) (.n 8) 0)] ++ e.1 ++
    [.atom (.add (.n e.2.2) (.n 7) (.n e.2.1)), .atom (.mul (.n (e.2.2 + 1)) (.n e.2.2) (.n 5)),
      .atom (.mul (.n (e.2.2 + 2)) (.n 2) (.n 0)), .atom (.load (.n (e.2.2 + 1)) (.n (e.2.2 + 2)) 1)]

/-- The rest's loop's tail's first value. -/
abbrev lrLoop2R (cols : ℕ) : ℕ := (osResQuery 9 4 0 (vanishOff cols) cols 10).2.2 + 3

theorem lrLoop2Body_split (cols : ℕ) (name : String) :
    lrLoop2Body cols name = (lrLoop2A cols ++ osLoopTailA (lrLoop2R cols)) ++
      [.callIf (.n (lrLoop2R cols + 2)) name
        (.n (lrLoop2R cols + 4) :: (List.range (6 - 1)).map fun i ↦ .n (i + 1)), .ret []] := by
  simp only [lrLoop2Body, lrLoop2A, lrLoop2R, osLoopTail_split, List.append_assoc,
    List.cons_append, List.nil_append]

theorem lrLoop2A_flat (cols : ℕ) :
    (lrLoop2A cols ++ osLoopTailA (lrLoop2R cols)).all Stmt.flat = true := by
  simp [lrLoop2A, osLoopTailA, osResQuery_flat, Stmt.flat]

theorem lrLoop2_step {cols : ℕ} (hc : 1 ≤ cols) (σ : Val) (x N rest tail rowd mu : E)
    (hp : (osParams 6).map σ = [x, N, rest, tail, rowd, mu]) {D : ℕ → E}
    (hD : ∀ s < cols, LoadHolds rd rowd s (D s)) {C : CallRel}
    (hA : AllOk C rd σ (lrLoop2A cols ++ osLoopTailA (lrLoop2R cols))) :
    RestIter rd D (vanishOff cols) cols rest tail mu x ∧
      σ (.n (lrLoop2R cols + 2)) = x * gen + N ∧
      (.n (lrLoop2R cols + 4) :: (List.range (6 - 1)).map fun i ↦ V.n (i + 1)).map σ =
        x * gen :: [N, rest, tail, rowd, mu] := by
  simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons.injEq, and_true, List.cons_append] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hp
  rw [allOk_append] at hA
  obtain ⟨hA, hT⟩ := hA
  obtain ⟨t2, t4⟩ := osLoopTailA_val hT
  refine ⟨?_, by rw [t2, h0, h1], ?_⟩
  · unfold lrLoop2A at hA
    set e := osResQuery 9 4 0 (vanishOff cols) cols 10
    simp only [allOk_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hA
    obtain ⟨⟨⟨m6, l7, m8, l9⟩, he⟩, a0, m1, m2, s1⟩ := hA
    have hv := osResQuery_val (bd := 4) (row := 0) hc (D := D)
      (fun s hs ↦ by rw [Nat.zero_add, h4]; exact hD s hs) he
    refine ⟨σ (.n 7), σ (.n 9), by rw [← h2, ← h0, ← m6]; exact l7,
      by rw [← h3, ← h0, ← m8]; exact l9, ?_⟩
    rw [← h2, ← h0, ← m2]
    convert s1 using 1
    rw [m1, a0, hv, h5]
    simp [resFold]
  · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, Nat.zero_add, t4, h0, h1, h2, h3, h4, h5]

/-- **The rest's loop, soundly**. -/
theorem lrLoop2_sound {name : String} {cols : ℕ} (hc : 1 ≤ cols)
    (hloop : FnIs name (osParams 6) (lrLoop2Body cols name))
    {n : ℕ} (hn0 : 0 < n) (hn : n < ordG) (rest tail rowd mu : E) {D : ℕ → E}
    (hD : ∀ s < cols, LoadHolds rd rowd s (D s))
    (hg : 1 + gen ^ n ≠ 0 → coreProgram.Rel rd name [1, gen ^ n, rest, tail, rowd, mu] []) :
    ∀ j < n, RestIter rd D (vanishOff cols) cols rest tail mu (gen ^ j) := by
  obtain ⟨fn, hf, hps, hb⟩ := hloop
  rw [lrLoop2Body_split] at hb
  refine loop_guarded (rest := [rest, tail, rowd, mu]) hn0 hn rfl
    (loop_sound_flat hf (lrLoop2A_flat cols) hb ?_) hg
  intro σ x hp hA
  rw [hps] at hp
  exact lrLoop2_step hc σ x (gen ^ n) rest tail rowd mu hp hD hA

/-- **The rest's chain**: from `rest[0] = h`, `rest[j]` is the steps from `h` over the first `j`
positions at `tail`. -/
theorem restChain {D : ℕ → E} {vo ml : ℕ} {rest tail mu h : E} {n : ℕ} {T : ℕ → E}
    (hT : ∀ i < n, LoadHolds rd tail i (T i)) (h0 : LoadHolds rd rest 0 h)
    (hit : ∀ j < n, RestIter rd D vo ml rest tail mu (gen ^ j)) :
    ∀ j ≤ n, LoadHolds rd rest j (resFold D vo ml mu h ((List.range j).map T)) := by
  intro j
  induction j with
  | zero => intro _; simpa [resFold] using h0
  | succ j ih =>
    intro hj
    obtain ⟨h', p, lh, lp, ls⟩ := hit j (by omega)
    rw [loadHolds_mul_gen_pow] at lh lp ls
    have eh := loadHolds_unique lh (by simpa using ih (by omega))
    have ep := loadHolds_unique lp (by simpa using hT j (by omega))
    rw [eh, ep, ← resFold_append] at ls
    rw [List.range_succ, List.map_append]
    simpa using ls

/-! ## `level_residual` -/

/-- **`level_residual(positions, row_d, mu)`** at `q` queries over `cols` columns: on the row `D`
at `row_d` and the positions `P` at `positions`, the chain from `0` over the `q` positions. -/
def MeaningLevelResidual (q cols : ℕ) (rd : Reader) : List E → List E → Prop
  | [pos, rowd, mu], rets => ∀ D P : ℕ → E, (∀ s < cols, LoadHolds rd rowd s (D s)) →
      (∀ i < q, LoadHolds rd pos i (P i)) →
      rets = [resFold D (vanishOff cols) cols mu 0 ((List.range q).map P)]
  | _, _ => False

/-- `level_residual`'s body up to its batches' result. -/
def lrA0 (q : ℕ) (loop1 : String) : List Stmt :=
  osHeap (q / resBatch + 1) 3 ++
    [.atom (.const (.n 5) (word 0 0 0)), .atom (.load (.n 5) (.n 4) 0)] ++
    osLoopCall loop1 (q / resBatch) [4, 0, 1, 2] 6 ++
    [.atom (.load (.n 11) (.n 4) (q / resBatch))]

/-- `level_residual`'s rest, when `8 ∤ q`, before its `ret`. -/
def lrA1 (q : ℕ) (loop2 : String) : List Stmt :=
  osHeap (q % resBatch + 1) 12 ++
    [.atom (.load (.n 11) (.n 13) 0), .atom (.const (.n 14) (gw (resBatch * (q / resBatch)))),
      .atom (.mul (.n 15) (.n 0) (.n 14))] ++
    osLoopCall loop2 (q % resBatch) [13, 15, 1, 2] 16 ++
    [.atom (.load (.n 21) (.n 13) (q % resBatch)), .atom (.copy (.n 22) (.n 21))]

theorem lrBody_split0 {q : ℕ} (loop1 loop2 : String) (hq : q % resBatch = 0) :
    lrBody q loop1 loop2 = (lrA0 q loop1 ++ [.atom (.copy (.n 12) (.n 11))]) ++ [.ret [.n 12]] := by
  simp only [lrBody, lrA0, hq, ↓reduceIte, List.append_assoc, List.cons_append, List.nil_append]

theorem lrBody_split1 {q : ℕ} (loop1 loop2 : String) (hq : q % resBatch ≠ 0) :
    lrBody q loop1 loop2 = (lrA0 q loop1 ++ lrA1 q loop2) ++ [.ret [.n 22]] := by
  simp only [lrBody, lrA0, lrA1, hq, ↓reduceIte, List.append_assoc, List.cons_append,
    List.nil_append]

/-- The batches: `chain[q/8]`, read at `11`, is the chain over the first `8·(q/8)` positions. -/
theorem lrA0_val {q cols : ℕ} {loop1 : String}
    (h1 : FnIs loop1 (osParams 6) (lrLoop1Body cols loop1))
    (hrb : ∀ a r, coreProgram.Rel rd (rbName cols) a r → MeaningResidualBatch cols rd a r)
    (hq1 : q / resBatch < ordG) (hq1' : q / resBatch < u128Bound) {σ : Val} {D P : ℕ → E}
    (hD : ∀ s < cols, LoadHolds rd (σ (.n 1)) s (D s))
    (hP : ∀ i < q, LoadHolds rd (σ (.n 0)) i (P i))
    (hok : AllOk (coreProgram.Rel rd) rd σ (lrA0 q loop1)) :
    σ (.n 11) = resFold D (vanishOff cols) cols (σ (.n 2)) 0
      ((List.range (resBatch * (q / resBatch))).map P) := by
  simp only [lrA0, osHeap, osLoopCall, allOk_append, allOk_cons, allOk_nil, and_true, StmtOk,
    Atom.Holds, List.map_cons, List.map_nil, and_assoc] at hok
  obtain ⟨-, z5, s5, c6, c7, a8, c9, c10, -, hcall, l11⟩ := hok
  rw [z5, word_zero] at s5
  rcases Nat.eq_zero_or_pos (q / resBatch) with hn0 | hn0
  · rw [hn0] at l11 ⊢
    simpa [resFold] using loadHolds_unique l11 s5
  · have hgn : gw (q / resBatch) = gen ^ (q / resBatch) := gw_eq hq1'
    have hit := lrLoop1_sound h1 hrb hn0 hq1 (σ (.n 4)) (σ (.n 0)) (σ (.n 1)) (σ (.n 2)) hD (by
      rw [a8, c6, c7, c9, c10, hgn, word_one] at hcall
      exact hcall)
    have := resChain (po := 0) (P := P) (fun i hi ↦ by
      rw [Nat.zero_add]
      exact hP i (by have := Nat.div_mul_le_self q resBatch; nlinarith))
      s5 hit (q / resBatch) le_rfl
    exact loadHolds_unique l11 this

/-- **`level_residual` is sound** at its specialization's templates. -/
theorem level_residual_sound {name loop1 loop2 : String} {q cols : ℕ}
    (hfn : FnIs name (osParams 3) (lrBody q loop1 loop2))
    (h1 : FnIs loop1 (osParams 6) (lrLoop1Body cols loop1))
    (h2 : q % resBatch ≠ 0 → FnIs loop2 (osParams 6) (lrLoop2Body cols loop2))
    (hrbf : FnIs (rbName cols) (osParams 4) (rbBody cols)) (hc : 1 ≤ cols)
    (hq1 : q / resBatch < ordG) (hq1' : q / resBatch < u128Bound)
    (hq8 : resBatch * (q / resBatch) < u128Bound) (args rets : List E)
    (h : coreProgram.Rel rd name args rets) : MeaningLevelResidual q cols rd args rets := by
  have hrb := residual_batch_sound (rd := rd) hc hrbf
  obtain ⟨fn, hf, hps, hb⟩ := hfn
  rw [rel_iff_sem hf] at h
  obtain ⟨σ, hp, hh⟩ := h
  rw [hps] at hp
  subst hp
  simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append]
  intro D P hD hP
  have hqs : resBatch * (q / resBatch) + q % resBatch = q := Nat.div_add_mod _ _
  by_cases hq : q % resBatch = 0
  · rw [hb, lrBody_split0 loop1 loop2 hq, holdsList_flat_ret _ (by
      simp [lrA0, osHeap, osLoopCall, Stmt.flat])] at hh
    obtain ⟨hok, hret⟩ := hh
    rw [allOk_append] at hok
    have h11 := lrA0_val h1 hrb hq1 hq1' hD hP hok.1
    simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hok
    rw [← hret]
    simp only [List.map_cons, List.map_nil, hok.2, h11]
    rw [show resBatch * (q / resBatch) = q by omega]
  · rw [hb, lrBody_split1 loop1 loop2 hq, holdsList_flat_ret _ (by
      simp [lrA0, lrA1, osHeap, osLoopCall, Stmt.flat])] at hh
    obtain ⟨hok, hret⟩ := hh
    rw [allOk_append] at hok
    obtain ⟨hok0, hok1⟩ := hok
    have h11 := lrA0_val h1 hrb hq1 hq1' hD hP hok0
    have hm0 : 0 < q % resBatch := Nat.pos_of_ne_zero hq
    have hm8 : q % resBatch < resBatch := Nat.mod_lt _ (by decide)
    simp only [lrA1, osHeap, osLoopCall, allOk_append, allOk_cons, allOk_nil, and_true, StmtOk,
      Atom.Holds, List.map_cons, List.map_nil, and_assoc] at hok1
    obtain ⟨-, s11, c14, m15, c16, c17, a18, c19, c20, -, hcall, l21, e22⟩ := hok1
    have h8 : resBatch = 8 := rfl
    have hgm : gw (q % resBatch) = gen ^ (q % resBatch) := gw_eq (by unfold u128Bound; omega)
    have hit := lrLoop2_sound (rd := rd) hc (h2 hq) hm0 (by unfold ordG; omega) (σ (.n 13))
      (σ (.n 15)) (σ (.n 1)) (σ (.n 2)) hD (by
        rw [a18, c16, c17, c19, c20, hgm, word_one] at hcall
        exact hcall)
    have htail : σ (.n 15) = σ (.n 0) * gen ^ (resBatch * (q / resBatch)) := by rw [m15, c14, gw_eq hq8]
    have := restChain (T := fun i ↦ P (resBatch * (q / resBatch) + i)) (fun i hi ↦ by
      rw [htail, loadHolds_mul_gen_pow]; exact hP _ (by omega)) s11 hit _ le_rfl
    have hsplit : (List.range q).map P = (List.range (resBatch * (q / resBatch))).map P ++
        (List.range (q % resBatch)).map fun i ↦ P (resBatch * (q / resBatch) + i) := by
      conv_lhs => rw [← hqs]
      rw [List.range_add, List.map_append, List.map_map]
      rfl
    rw [← hret]
    simp only [List.map_cons, List.map_nil, e22]
    rw [loadHolds_unique l21 this, h11, ← resFold_append, ← hsplit]

end
end LeanVM.Guest.B1.Whir
