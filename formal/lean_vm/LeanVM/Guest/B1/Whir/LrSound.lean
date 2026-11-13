/-
  LeanVM.Guest.B1.Whir.LrSound

  `level_residual` (a level's residual chains at the terminal point: the batches' loop, then the
  rest's), soundly.
-/

module

public import LeanVM.Guest.B1.Whir.ResLoop
public import LeanVM.Guest.B1.Whir.HelperAll

/-!
# `level_residual`, soundly

`MeaningLevelResidual q cols nhs hbits`: on `[positions, row_d, hs, mu]`, for the basis row `D` at
`row_d`, the high part `hsv` at `hs` and the positions `Pos` at `positions`, the returns are the
two chains `h ← (h + P(p))·μ`, `hh ← (hh + H(p))·μ` over the `q` positions from `0, 0`
(`resFold`, `lrP`, `lrH`). `lr_sound`: a call of a specialization whose body and loops are the
templates establishes it.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- The vanishing tables' offset of `cols` message columns. -/
abbrev lrVo (cols : ℕ) : ℕ := cols * (cols + 1) / 2

/-- A query's residual product over `cols` columns, the basis row `D`. -/
def lrP (cols : ℕ) (D : ℕ → E) (x : E) : E := residualProd (osVals (lrVo cols) cols) x D cols

/-- A query's high share over `cols` columns, the high part `hsv` of `nhs` coefficients and
`hbits` index bits. -/
def lrH (cols nhs hbits : ℕ) (hsv : List E) (x : E) : E :=
  residualChain (osVals (lrVo cols) cols) x cols *
    novelSum hsv (residualChain (osVals (lrVo cols) cols) x) nhs hbits

/-- **What `level_residual__L{q}_L{cols}_L{nhs}_L{hbits}` establishes** on
`[positions, row_d, hs, mu]`. -/
def MeaningLevelResidual (q cols nhs hbits : ℕ) (rd : Reader) (args rets : List E) : Prop :=
  ∀ (D : ℕ → E) (hsv : List E) (Pos : ℕ → E), (∀ s < cols, LoadHolds rd (args.getD 1 0) s (D s)) →
    hsv.length = nhs → (∀ c < nhs, LoadHolds rd (args.getD 2 0) c (hsv.getD c 0)) →
    (∀ i < q, LoadHolds rd (args.getD 0 0) i (Pos i)) →
    rets = [(resFold (lrP cols D) (lrH cols nhs hbits hsv) (args.getD 3 0) (0, 0)
        ((List.range q).map Pos)).1,
      (resFold (lrP cols D) (lrH cols nhs hbits hsv) (args.getD 3 0) (0, 0)
        ((List.range q).map Pos)).2]

/-! ## The batches' loop -/

/-- The batches' loop's steps. -/
def lr1St (cols nhs hbits : ℕ) : List Stmt × ℕ × ℕ × ℕ :=
  osResSteps (7 + batchLen) 4 0 5 0 (lrVo cols) cols nhs hbits 6 (List.range resBatch)
    (7 + batchLen + 3) (7 + batchLen + 4) (7 + batchLen + 5)

/-- The batches' loop's body before its tail. -/
def lr1A (cols nhs hbits : ℕ) : List Stmt :=
  (osBatchPow 7).1 ++ [osMul (7 + batchLen) 2 (osBatchPow 7).2, osMul (7 + batchLen + 1) 3 0,
    osMul (7 + batchLen + 2) (7 + batchLen + 1) 0, osLd (7 + batchLen + 3) (7 + batchLen + 2) 0,
    osLd (7 + batchLen + 4) (7 + batchLen + 2) 1] ++ (lr1St cols nhs hbits).1 ++
    [osLd (lr1St cols nhs hbits).2.1 (7 + batchLen + 2) 2,
      osLd (lr1St cols nhs hbits).2.2.1 (7 + batchLen + 2) 3]

theorem lrLoop1Body_split (cols nhs hbits : ℕ) (name : String) :
    lrLoop1Body cols nhs hbits name =
      (lr1A cols nhs hbits ++ osLoopTailA (lr1St cols nhs hbits).2.2.2) ++
        [.callIf (.n ((lr1St cols nhs hbits).2.2.2 + 2)) name
          (.n ((lr1St cols nhs hbits).2.2.2 + 4) :: (List.range (7 - 1)).map fun i ↦ .n (i + 1)),
          .ret []] := by
  simp only [lrLoop1Body, lr1A, lr1St, osLoopTail_split, List.append_assoc]

theorem lr1A_flat (cols nhs hbits : ℕ) :
    (lr1A cols nhs hbits ++ osLoopTailA (lr1St cols nhs hbits).2.2.2).all Stmt.flat = true := by
  simp [lr1A, lr1St, osLoopTailA, osResSteps_flat, osBatchPow, osPowSteps_flat, Stmt.flat]

/-- What a call's reads are: the basis row `D` at `bd`, the high part `hsv` at `hs`. -/
structure LrRead (rd : Reader) (cols nhs hbits : ℕ) (bd hs : E) (D : ℕ → E) (hsv : List E) :
    Prop where
  c1 : 1 ≤ cols
  n1 : 1 ≤ nhs
  b3 : hbits ≤ 3
  bn : hbits ≤ cols + 1
  rowD : ∀ s < cols, LoadHolds rd bd s (D s)
  len : hsv.length = nhs
  high : ∀ c < nhs, LoadHolds rd hs c (hsv.getD c 0)

theorem lrLoop1_step (cols nhs hbits : ℕ) {D : ℕ → E} {hsv : List E} (σ : Val)
    (x N pos chain bd hs mu : E) (hp : (osParams 7).map σ = [x, N, pos, chain, bd, hs, mu])
    (hR : LrRead rd cols nhs hbits bd hs D hsv) {C : CallRel}
    (hA : AllOk C rd σ (lr1A cols nhs hbits ++ osLoopTailA (lr1St cols nhs hbits).2.2.2)) :
    ResIter rd (lrP cols D) (lrH cols nhs hbits hsv) 0 pos chain mu x ∧
      σ (.n ((lr1St cols nhs hbits).2.2.2 + 2)) = x * gen + N ∧
      (.n ((lr1St cols nhs hbits).2.2.2 + 4) :: (List.range (7 - 1)).map fun i ↦ V.n (i + 1)).map σ =
        x * gen :: [N, pos, chain, bd, hs, mu] := by
  simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons.injEq, and_true, List.cons_append] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hp
  rw [allOk_append] at hA
  obtain ⟨hA, hT⟩ := hA
  obtain ⟨t2, t4⟩ := osLoopTailA_val hT
  refine ⟨?_, by rw [t2, h0, h1], ?_⟩
  · unfold lr1A at hA
    simp only [allOk_append, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_mul, holds_load,
      osMul, osLd] at hA
    obtain ⟨⟨⟨hpw, m3, m4, m5, l6, l7⟩, hst⟩, s1, s2⟩ := hA
    have hD' : ∀ s < cols, LoadHolds rd (σ (.n 4)) (0 + s) (D s) := by
      rw [h4]; intro s hs; rw [Nat.zero_add]; exact hR.rowD s hs
    have hH' : ∀ c < nhs, LoadHolds rd (σ (.n 5)) (0 + c) (hsv.getD c 0) := by
      rw [h5]; intro c hc; rw [Nat.zero_add]; exact hR.high c hc
    have hP : σ (.n (7 + batchLen)) = pos * gen ^ 0 * x ^ resBatch := by
      rw [m3, osBatchPow_val _ hpw, h0, h2, pow_zero, mul_one]
    have hC : σ (.n (7 + batchLen + 2)) = chain * x ^ 2 := by rw [m5, m4, h3, h0]; ring
    obtain ⟨ps, hF, hv⟩ := osResSteps_val hR.c1 hR.n1 hR.b3 hR.bn hD' hR.len hH' _ _ _ _ hst
    obtain ⟨hl, hF⟩ := forall₂_range_to _ _ hF
    rw [hP] at hF
    rw [hC] at l6 l7 s1 s2
    rw [h6] at hv
    refine ⟨(σ (.n (7 + batchLen + 3)), σ (.n (7 + batchLen + 4))), ps, hl, hF, l6, l7, ?_, ?_⟩
    · have := congrArg Prod.fst hv; simp only at this
      unfold lrP lrH; rw [← this]; exact s1
    · have := congrArg Prod.snd hv; simp only at this
      unfold lrP lrH; rw [← this]; exact s2
  · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, Nat.zero_add, t4, h0, h1, h2, h3, h4, h5, h6]

/-- **The batches' loop, soundly**: entered from `1` with the bound `g^n`, `0 < n < ord g`. -/
theorem lrLoop1_sound {cols nhs hbits : ℕ} {name : String} (hl : FnIs name (osParams 7) (lrLoop1Body cols nhs hbits name))
    {D : ℕ → E} {hsv : List E} {n : ℕ} (hn0 : 0 < n) (hn : n < ordG) (pos chain bd hs mu : E)
    (hR : LrRead rd cols nhs hbits bd hs D hsv)
    (hg : 1 + gen ^ n ≠ 0 → coreProgram.Rel rd name [1, gen ^ n, pos, chain, bd, hs, mu] []) :
    ∀ j < n, ResIter rd (lrP cols D) (lrH cols nhs hbits hsv) 0 pos chain mu (gen ^ j) := by
  obtain ⟨fn, hf, hps, hb⟩ := hl
  rw [lrLoop1Body_split] at hb
  refine loop_guarded (rest := [pos, chain, bd, hs, mu]) hn0 hn rfl
    (loop_sound_flat hf (lr1A_flat cols nhs hbits) hb ?_) hg
  intro σ x hp hA
  rw [hps] at hp
  exact lrLoop1_step cols nhs hbits σ x (gen ^ n) pos chain bd hs mu hp hR hA

/-! ## The rest's loop -/

/-- The rest's loop's query. -/
def lr2Q (cols nhs hbits : ℕ) : List Stmt × ℕ × ℕ × ℕ :=
  osResQuery 10 4 0 5 0 (lrVo cols) cols nhs hbits 11

/-- The rest's loop's body before its tail. -/
def lr2A (cols nhs hbits : ℕ) : List Stmt :=
  let q := lr2Q cols nhs hbits
  let e := q.2.2.2
  [osMul 7 2 0, osMul 8 7 0, osMul 9 3 0, osLd 10 9 0] ++ q.1 ++
    [osLd e 8 0, osAdd (e + 1) e q.2.1, osMul (e + 2) (e + 1) 6, osLd (e + 2) 8 2,
      osLd (e + 3) 8 1, osAdd (e + 4) (e + 3) q.2.2.1, osMul (e + 5) (e + 4) 6, osLd (e + 5) 8 3]

theorem lrLoop2Body_split (cols nhs hbits : ℕ) (name : String) :
    lrLoop2Body cols nhs hbits name =
      (lr2A cols nhs hbits ++ osLoopTailA ((lr2Q cols nhs hbits).2.2.2 + 6)) ++
        [.callIf (.n ((lr2Q cols nhs hbits).2.2.2 + 6 + 2)) name
          (.n ((lr2Q cols nhs hbits).2.2.2 + 6 + 4) :: (List.range (7 - 1)).map fun i ↦ .n (i + 1)),
          .ret []] := by
  simp only [lrLoop2Body, lr2A, lr2Q, osLoopTail_split, List.append_assoc]

theorem lr2A_flat (cols nhs hbits : ℕ) :
    (lr2A cols nhs hbits ++ osLoopTailA ((lr2Q cols nhs hbits).2.2.2 + 6)).all Stmt.flat = true := by
  simp [lr2A, lr2Q, osLoopTailA, osResQuery_flat, Stmt.flat]

/-- **One iteration of the rest's loop at `x`**: the position at `tail·x`, the chains at
`rest·x^2` (cells `0, 1`) advanced over it into cells `2, 3`. -/
def RestIter (rd : Reader) (P H : E → E) (tail rest mu x : E) : Prop :=
  ∃ (a : E × E) (p : E), LoadHolds rd (tail * x) 0 p ∧
    LoadHolds rd (rest * x ^ 2) 0 a.1 ∧ LoadHolds rd (rest * x ^ 2) 1 a.2 ∧
    LoadHolds rd (rest * x ^ 2) 2 (resFold P H mu a [p]).1 ∧
    LoadHolds rd (rest * x ^ 2) 3 (resFold P H mu a [p]).2

theorem lrLoop2_step (cols nhs hbits : ℕ) {D : ℕ → E} {hsv : List E} (σ : Val)
    (x N rest tail bd hs mu : E) (hp : (osParams 7).map σ = [x, N, rest, tail, bd, hs, mu])
    (hR : LrRead rd cols nhs hbits bd hs D hsv) {C : CallRel}
    (hA : AllOk C rd σ (lr2A cols nhs hbits ++ osLoopTailA ((lr2Q cols nhs hbits).2.2.2 + 6))) :
    RestIter rd (lrP cols D) (lrH cols nhs hbits hsv) tail rest mu x ∧
      σ (.n ((lr2Q cols nhs hbits).2.2.2 + 6 + 2)) = x * gen + N ∧
      (.n ((lr2Q cols nhs hbits).2.2.2 + 6 + 4) :: (List.range (7 - 1)).map fun i ↦ V.n (i + 1)).map σ =
        x * gen :: [N, rest, tail, bd, hs, mu] := by
  simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons.injEq, and_true, List.cons_append] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hp
  rw [allOk_append] at hA
  obtain ⟨hA, hT⟩ := hA
  obtain ⟨t2, t4⟩ := osLoopTailA_val hT
  refine ⟨?_, by rw [t2, h0, h1], ?_⟩
  · unfold lr2A at hA
    simp only [allOk_append, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_mul, holds_load,
      holds_add, osMul, osLd, osAdd] at hA
    obtain ⟨⟨⟨m0, m1, m2, l3⟩, hq⟩, la, a1, u1, sa, lb, a2, u2, sb⟩ := hA
    have hD' : ∀ s < cols, LoadHolds rd (σ (.n 4)) (0 + s) (D s) := by
      rw [h4]; intro s hs; rw [Nat.zero_add]; exact hR.rowD s hs
    have hH' : ∀ c < nhs, LoadHolds rd (σ (.n 5)) (0 + c) (hsv.getD c 0) := by
      rw [h5]; intro c hc; rw [Nat.zero_add]; exact hR.high c hc
    obtain ⟨q1, q2⟩ := osResQuery_val hR.c1 hR.n1 hR.b3 hR.bn hD' hR.len hH' hq
    have hT' : σ (.n 9) = tail * x := by rw [m2, h3, h0]
    have hRx : σ (.n 8) = rest * x ^ 2 := by rw [m1, m0, h2, h0]; ring
    rw [hT'] at l3
    rw [hRx] at la lb sa sb
    refine ⟨(σ (.n (lr2Q cols nhs hbits).2.2.2), σ (.n ((lr2Q cols nhs hbits).2.2.2 + 3))),
      σ (.n 10), l3, la, lb, ?_, ?_⟩
    · simp only [resFold, List.foldl_cons, List.foldl_nil]
      have e : σ (.n ((lr2Q cols nhs hbits).2.2.2 + 2)) =
          (σ (.n (lr2Q cols nhs hbits).2.2.2) + lrP cols D (σ (.n 10))) * mu := by
        rw [u1, a1, h6]; unfold lrP lr2Q; rw [q1]
      rw [← e]; exact sa
    · simp only [resFold, List.foldl_cons, List.foldl_nil]
      have e : σ (.n ((lr2Q cols nhs hbits).2.2.2 + 5)) =
          (σ (.n ((lr2Q cols nhs hbits).2.2.2 + 3)) + lrH cols nhs hbits hsv (σ (.n 10))) * mu := by
        rw [u2, a2, h6]; unfold lrH lr2Q; rw [q2]
      rw [← e]; exact sb
  · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, Nat.zero_add, t4, h0, h1, h2, h3, h4, h5, h6]

/-- **The rest's loop, soundly**: entered from `1` with the bound `g^n`, `0 < n < ord g`. -/
theorem lrLoop2_sound {cols nhs hbits : ℕ} {name : String} (hl : FnIs name (osParams 7) (lrLoop2Body cols nhs hbits name))
    {D : ℕ → E} {hsv : List E} {n : ℕ} (hn0 : 0 < n) (hn : n < ordG) (rest tail bd hs mu : E)
    (hR : LrRead rd cols nhs hbits bd hs D hsv)
    (hg : 1 + gen ^ n ≠ 0 → coreProgram.Rel rd name [1, gen ^ n, rest, tail, bd, hs, mu] []) :
    ∀ j < n, RestIter rd (lrP cols D) (lrH cols nhs hbits hsv) tail rest mu (gen ^ j) := by
  obtain ⟨fn, hf, hps, hb⟩ := hl
  rw [lrLoop2Body_split] at hb
  refine loop_guarded (rest := [rest, tail, bd, hs, mu]) hn0 hn rfl
    (loop_sound_flat hf (lr2A_flat cols nhs hbits) hb ?_) hg
  intro σ x hp hA
  rw [hps] at hp
  exact lrLoop2_step cols nhs hbits σ x (gen ^ n) rest tail bd hs mu hp hR hA

/-- **The rest's chains**: from `rest[0], rest[1] = a`, after `j ≤ n` iterations `rest[2j]`,
`rest[2j + 1]` are the chains from `a` over the positions `Pos 0 .. Pos (j - 1)` at `tail`. -/
theorem restChain {P H : E → E} {tail rest mu : E} {n : ℕ} {Pos : ℕ → E} {a : E × E}
    (hP : ∀ i < n, LoadHolds rd tail i (Pos i))
    (h0 : LoadHolds rd rest 0 a.1) (h1 : LoadHolds rd rest 1 a.2)
    (hit : ∀ j < n, RestIter rd P H tail rest mu (gen ^ j)) :
    ∀ j ≤ n, LoadHolds rd rest (2 * j) (resFold P H mu a ((List.range j).map Pos)).1 ∧
      LoadHolds rd rest (2 * j + 1) (resFold P H mu a ((List.range j).map Pos)).2 := by
  intro j
  induction j with
  | zero => intro _; simpa [resFold] using ⟨h0, h1⟩
  | succ j ih =>
    intro hj
    obtain ⟨b, p, lp, la, lb, lc, ld⟩ := hit j (by omega)
    obtain ⟨i0, i1⟩ := ih (by omega)
    have hx2 : (gen ^ j) ^ 2 = gen ^ (2 * j) := by rw [← pow_mul, Nat.mul_comm]
    rw [hx2, loadHolds_mul_gen_pow] at la lb lc ld
    rw [loadHolds_mul_gen_pow, Nat.add_zero] at lp
    have eb : b = resFold P H mu a ((List.range j).map Pos) := by
      have e1 := loadHolds_unique la (by simpa using i0)
      have e2 := loadHolds_unique lb (by simpa using i1)
      exact Prod.ext e1 e2
    have ep : p = Pos j := loadHolds_unique lp (hP j (by omega))
    rw [eb, ep, ← resFold_append] at lc ld
    rw [List.range_succ, List.map_append]
    refine ⟨?_, ?_⟩
    · rw [show 2 * (j + 1) = 2 * j + 2 by ring]; simpa using lc
    · rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring]; simpa using ld

/-! ## `level_residual` -/

theorem lrBody_eq0 {q : ℕ} (h : q % resBatch = 0) (l1 l2 : String) :
    lrBody q l1 l2 = (osHeap (2 * (q / resBatch + 1)) 4 ++
      [osCst 6 (word 0 0), osLd 6 5 0, osCst 7 (word 0 0), osLd 7 5 1] ++
      osLoopCall l1 0 (q / resBatch) [0, 5, 1, 2, 3] 8 ++
      [osLd 13 5 (2 * (q / resBatch)), osLd 14 5 (2 * (q / resBatch) + 1)] ++ [osCp 15 13, osCp 16 14]) ++
      [.ret [.n 15, .n 16]] := by
  simp [lrBody, h, List.append_assoc]

theorem lrBody_ne0 {q : ℕ} (h : q % resBatch ≠ 0) (l1 l2 : String) :
    lrBody q l1 l2 = (osHeap (2 * (q / resBatch + 1)) 4 ++
      [osCst 6 (word 0 0), osLd 6 5 0, osCst 7 (word 0 0), osLd 7 5 1] ++
      osLoopCall l1 0 (q / resBatch) [0, 5, 1, 2, 3] 8 ++
      [osLd 13 5 (2 * (q / resBatch)), osLd 14 5 (2 * (q / resBatch) + 1)] ++
      osHeap (2 * (q % resBatch + 1)) 15 ++
      [osLd 13 16 0, osLd 14 16 1, osCst 17 (gw (resBatch * (q / resBatch))), osMul 18 0 17] ++
      osLoopCall l2 0 (q % resBatch) [16, 18, 1, 2, 3] 19 ++
      [osLd 24 16 (2 * (q % resBatch)), osLd 25 16 (2 * (q % resBatch) + 1), osCp 26 24, osCp 27 25]) ++
      [.ret [.n 26, .n 27]] := by
  simp [lrBody, h, List.append_assoc]

theorem resFold_zero (P H : E → E) (mu : E) : resFold P H mu (0, 0) [] = (0, 0) := rfl

/-- The loop entry `osLoopCall name 0 n args k` holds: the loop's relation at `[1, g^n] ++ args`,
behind its guard. -/
theorem osLoopCall0_val {C : CallRel} {σ : Val} {name : String} {n : ℕ} {args : List ℕ} {k : ℕ}
    (hn : n < u128Bound) (h : AllOk C rd σ (osLoopCall name 0 n args k)) :
    1 + gen ^ n ≠ 0 → C name (1 :: gen ^ n :: args.map (σ ∘ V.n)) [] := by
  simp only [osLoopCall, allOk_cons, allOk_nil, and_true, osCst, StmtOk, List.map_cons,
    Atom.Holds] at h
  obtain ⟨g0, gn, gsum, g3, g4, -, hcall⟩ := h
  have hg0 : gw 0 = 1 := by rw [gw_eq (by decide), pow_zero]
  have hgn : gw n = gen ^ n := gw_eq hn
  intro hne
  have := hcall (by rw [gsum, g0, gn, hg0, hgn]; exact hne)
  rw [g3, g4, hg0, hgn] at this
  simpa [List.map_map] using this

/-- **`level_residual`, soundly**: a call of a specialization whose body is `lrBody q l1 l2` and
whose loops are the templates establishes `MeaningLevelResidual`. -/
theorem lr_sound {name l1 l2 : String} {q cols nhs hbits : ℕ}
    (hf : FnIs name (osParams 4) (lrBody q l1 l2))
    (hl1 : FnIs l1 (osParams 7) (lrLoop1Body cols nhs hbits l1))
    (hl2 : q % resBatch ≠ 0 → FnIs l2 (osParams 7) (lrLoop2Body cols nhs hbits l2))
    (hq8 : resBatch ≤ q) (hqo : q < ordG) (hcols : 1 ≤ cols) (hnhs : 1 ≤ nhs) (hb3 : hbits ≤ 3)
    (hbn : hbits ≤ cols + 1) {args rets : List E} (hrel : coreProgram.Rel rd name args rets) :
    MeaningLevelResidual q cols nhs hbits rd args rets := by
  intro D hsv Pos hD hlen hH hPos
  obtain ⟨fn, hfind, hps, hb⟩ := hf
  obtain ⟨fn', hf', σ, hp, hh⟩ := (rel_iff coreProgram _ _ _).mp hrel
  rw [hfind] at hf'
  cases hf'
  rw [hps] at hp
  have ha : ∀ i < 4, σ (.n i) = args.getD i 0 := by
    intro i hi
    rw [← hp]
    simp [osParams, List.getD_eq_getElem?_getD, hi]
  have hR : LrRead rd cols nhs hbits (σ (.n 1)) (σ (.n 2)) D hsv :=
    ⟨hcols, hnhs, hb3, hbn, by rw [ha 1 (by decide)]; exact hD, hlen,
      by rw [ha 2 (by decide)]; exact hH⟩
  set nb := q / resBatch with hnb
  have hnb0 : 0 < nb := Nat.div_pos hq8 (by decide)
  have hnbo : nb < ordG := lt_of_le_of_lt (Nat.div_le_self _ _) hqo
  have hnbu : nb < u128Bound := lt_of_lt_of_le hnbo (by unfold ordG u128Bound; norm_num)
  have hPos' : ∀ i < resBatch * nb, LoadHolds rd (σ (.n 0)) (0 + i) (Pos i) := by
    intro i hi; rw [Nat.zero_add, ha 0 (by decide)]
    exact hPos i (lt_of_lt_of_le hi (Nat.mul_div_le q resBatch))
  set Pf := lrP cols D
  set Hf := lrH cols nhs hbits hsv
  have hmu : σ (.n 3) = args.getD 3 0 := ha 3 (by decide)
  -- the batches
  have batches : AllOk (coreProgram.Rel rd) rd σ (osHeap (2 * (nb + 1)) 4 ++
      [osCst 6 (word 0 0), osLd 6 5 0, osCst 7 (word 0 0), osLd 7 5 1] ++
      osLoopCall l1 0 nb [0, 5, 1, 2, 3] 8 ++
      [osLd 13 5 (2 * nb), osLd 14 5 (2 * nb + 1)]) →
      σ (.n 13) = (resFold Pf Hf (σ (.n 3)) (0, 0) ((List.range (resBatch * nb)).map Pos)).1 ∧
      σ (.n 14) = (resFold Pf Hf (σ (.n 3)) (0, 0) ((List.range (resBatch * nb)).map Pos)).2 := by
    intro hA
    simp only [allOk_append, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_const, holds_load,
      osCst, osLd] at hA
    obtain ⟨⟨⟨-, c6, z0, c7, z1⟩, hlp⟩, r0, r1⟩ := hA
    rw [c6, word_zero] at z0
    rw [c7, word_zero] at z1
    have hit := lrLoop1_sound hl1 hnb0 hnbo (σ (.n 0)) (σ (.n 5)) (σ (.n 1)) (σ (.n 2)) (σ (.n 3)) hR
      (fun hne ↦ by simpa using osLoopCall0_val hnbu hlp hne)
    obtain ⟨e0, e1⟩ := resChain hPos' z0 z1 hit nb le_rfl
    exact ⟨loadHolds_unique r0 e0, loadHolds_unique r1 e1⟩
  by_cases h0 : q % resBatch = 0
  · rw [hb, lrBody_eq0 h0, holdsList_flat_ret _ (by simp [osHeap, osLoopCall, Stmt.flat])] at hh
    obtain ⟨hok, hret⟩ := hh
    rw [← hnb] at hok
    simp only [allOk_append] at hok
    obtain ⟨⟨⟨⟨hA, hB⟩, hC⟩, hD4⟩, hcp⟩ := hok
    obtain ⟨e13, e14⟩ := batches (by simp only [allOk_append]; exact ⟨⟨⟨hA, hB⟩, hC⟩, hD4⟩)
    simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_copy, osCp] at hcp
    obtain ⟨c15, c16⟩ := hcp
    have hq : resBatch * nb = q := by rw [hnb]; exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h0)
    rw [← hret, ← hmu]
    simp [c15, c16, e13, e14, hq]
  · rw [hb, lrBody_ne0 h0, holdsList_flat_ret _ (by simp [osHeap, osLoopCall, Stmt.flat])] at hh
    obtain ⟨hok, hret⟩ := hh
    rw [← hnb] at hok
    simp only [allOk_append] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨hA, hB⟩, hC⟩, hD4⟩, -⟩, hF⟩, hG⟩, hH⟩ := hok
    obtain ⟨e13, e14⟩ := batches (by simp only [allOk_append]; exact ⟨⟨⟨hA, hB⟩, hC⟩, hD4⟩)
    set r := q % resBatch with hr
    have hr0 : 0 < r := Nat.pos_of_ne_zero h0
    have hr8 : r < resBatch := Nat.mod_lt _ (by decide)
    have hro : r < ordG := lt_of_lt_of_le hr8 (by unfold ordG; norm_num)
    have hru : r < u128Bound := lt_of_lt_of_le hr8 (by unfold u128Bound; norm_num)
    simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_const, holds_load, holds_mul,
      osCst, osLd, osMul] at hF
    obtain ⟨s0, s1, c17, m18⟩ := hF
    have hq : resBatch * nb + r = q := by rw [hnb, hr]; exact Nat.div_add_mod q resBatch
    have h8u : resBatch * nb < u128Bound := lt_of_le_of_lt (Nat.mul_div_le q resBatch)
      (lt_of_lt_of_le hqo (by unfold ordG u128Bound; norm_num))
    have htail : σ (.n 18) = σ (.n 0) * gen ^ (resBatch * nb) := by rw [m18, c17, gw_eq h8u]
    have hPt : ∀ i < r, LoadHolds rd (σ (.n 18)) i (Pos (resBatch * nb + i)) := by
      intro i hi
      rw [htail, loadHolds_mul_gen_pow, ha 0 (by decide)]
      exact hPos _ (by omega)
    have hit := lrLoop2_sound (hl2 h0) hr0 hro (σ (.n 16)) (σ (.n 18)) (σ (.n 1)) (σ (.n 2)) (σ (.n 3))
      hR (fun hne ↦ by simpa using osLoopCall0_val hru hG hne)
    rw [e13] at s0
    rw [e14] at s1
    obtain ⟨f0, f1⟩ := restChain (Pos := fun i ↦ Pos (resBatch * nb + i)) hPt s0 s1 hit r le_rfl
    simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, holds_copy, osLd,
      osCp] at hH
    obtain ⟨r24, r25, c26, c27⟩ := hH
    have hfold : resFold Pf Hf (σ (.n 3)) (0, 0) ((List.range q).map Pos) =
        resFold Pf Hf (σ (.n 3)) (resFold Pf Hf (σ (.n 3)) (0, 0) ((List.range (resBatch * nb)).map Pos))
          ((List.range r).map fun i ↦ Pos (resBatch * nb + i)) := by
      rw [← resFold_append, ← hq, List.range_add, List.map_append, List.map_map]
      rfl
    rw [← hret, ← hmu, hfold]
    simp [c26, c27, loadHolds_unique r24 f0, loadHolds_unique r25 f1]
    exact ⟨rfl, rfl⟩

end
end LeanVM.Guest.B1.Whir
