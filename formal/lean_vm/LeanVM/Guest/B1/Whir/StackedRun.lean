/-
  LeanVM.Guest.B1.Whir.StackedRun

  Runs of the stacked opening's programs (`whirLevelsOpen`, V:1718) from the runs of their
  pieces: the fold rounds, the next commitment and its out-of-domain sample, the proof of work, the
  query positions, the openings, the tail rounds.
-/

module

public import LeanVM.Guest.B1.VerifySub.Run
public import LeanVM.Guest.B1.OpeningOod

/-!
# Runs of the stacked opening (TRIAGE #36)

The specification's side of `open_stacked`, with no guest value in it: `whirLevelsOpen` split into
a level's head (`levelHead`: the folds, the next commitment or the residual, the queries and the
glue) and the tail (`osTailOpen`), and the run of each piece from the values the guest computes.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-! ## The split -/

/-- A level's claims after its folds: the residual at the last level, otherwise the next
commitment and its out-of-domain claim (V:1724-1736). -/
def osLevelMid (messageLog : ℕ) : List Whir.Level →
    Prog (List E × List (E × List E × (List E → E)))
  | [] => do
    let residual ← Prog.readN (2 ^ messageLog)
    pure (residual, ([] : List (E × List E × (List E → E))))
  | next :: _ => do
    let (height, width) := levelShape messageLog next (3 * 2 ^ next.fold)
    Prog.commitP height width
    let oodPoint ← Prog.sampleN messageLog
    let oodValue ← Prog.readE
    let intro ← sumcheckRoundPoly 3 oodValue none
    pure ([], [(oodValue, intro, fun x ↦ eqEval oodPoint x)])

/-- A level's queries and glue (V:1737-1749), after its folds and its claims. -/
def osLevelQueries (messageLog index : ℕ) (level : Whir.Level) (levelFolds : List E) (s : WhirState)
    (pending : List (E × List E × (List E → E))) : Prog WhirState := do
  Prog.grindP Whir.queryGrindingBits
  let queries ← sampleQueries (messageLog + level.logInvRate) level.queries
  let lam ← Prog.sampleE
  let queryWeights := powers lam queries.length
  let words ← Prog.queryP index queries
  let rows : List (List E) :=
    if index = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow
  let enforced := enforcedSum rows levelFolds queryWeights
  let intro ← sumcheckRoundPoly 3 enforced none
  return glue lam s (pending ++
    [(enforced, intro, fun x ↦ inducedWeight messageLog queries queryWeights x)])

/-- The last level's tail (V:1750-1757): the tail rounds and what the terminal reads. -/
def osTailOpen (messageLog laneFolds : ℕ) (s : WhirState) (residual : List E) : Prog WhirEnd := do
  let (tailFolds, target) ← tailRounds messageLog s.target s.quad
  let point := s.folds ++ tailFolds
  let inner := s.glued.foldl
    (fun weight claim ↦
      weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ tailFolds)) 0
  return ⟨point.drop laneFolds ++ point.take laneFolds, inner,
    multilinearEval residual tailFolds, target⟩

theorem os_whirLevelsOpen_cons (logN laneFolds index : ℕ) (level : Whir.Level)
    (rest : List Whir.Level) (s : WhirState) :
    whirLevelsOpen logN laneFolds index (level :: rest) s = (do
      let (s, levelFolds) ← foldRounds level.fold s []
      let messageLog := logN - s.folds.length
      let (residual, pending) ← osLevelMid messageLog rest
      let s ← osLevelQueries messageLog index level levelFolds s pending
      match rest with
      | [] => osTailOpen messageLog laneFolds s residual
      | _ :: _ => whirLevelsOpen logN laneFolds (index + 1) rest s) := by
  rw [whirLevelsOpen]
  simp only [osLevelQueries, osTailOpen, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind]
  refine bind_congr' fun r ↦ ?_
  cases rest <;> simp only [osLevelMid, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind]


/-! ## Runs of the pieces -/

theorem os_runs_readE (cv : Digest) (x : E) (rest : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) :
    Runs Prog.readE ⟨cv, x :: rest, os, roots⟩ x ⟨obsCv cv x, rest, os, roots⟩ := rfl

theorem os_runs_sampleE (st : St) :
    Runs Prog.sampleE st (challengeOf (sqCv st.cv)) { st with cv := sqCv st.cv } := rfl

theorem os_runs_roundPoly3 (cv : Digest) (claim c0 c2 : E) (rest : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) :
    Runs (sumcheckRoundPoly 3 claim none) ⟨cv, c0 :: c2 :: rest, os, roots⟩ [c0, claim + c2, c2]
      ⟨obsCv (obsCv cv c0) c2, rest, os, roots⟩ := by
  simp only [sumcheckRoundPoly, Prog.readN, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc,
    Prog.ret_bind, sumE, List.foldl, zero_add, Nat.reduceSub]
  rfl

theorem os_runs_commitP {cv : Digest} {x0 x1 : E} {root : Digest}
    (h : digestOfScalars (x0, x1) = some root) (height width : ℕ) (rest : List E)
    (os : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    Runs (Prog.commitP height width) ⟨cv, x0 :: x1 :: rest, os, roots⟩ ()
      ⟨obsCv (obsCv cv x0) x1, rest, os, roots ++ [(root, height, width)]⟩ := by
  simp only [Runs, Prog.commitP, runId, Compile.run, h]
  rfl

theorem os_runs_grindP {cv : Digest} {bits : ℕ} {n : E} (h : powOk bits n (gcDigest cv n) = true)
    (rest : List E) (os : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    Runs (Prog.grindP bits) ⟨cv, n :: rest, os, roots⟩ () ⟨absorbCv cv n 4, rest, os, roots⟩ := by
  have h' : powOk bits n (blake2sBytes (digestBytes (blake2sBytes (digestBytes cv ++ blockOf 0 3)) ++
      blockOf n 4)) = true := h
  simp only [Runs, Prog.grindP, runId, Compile.run, absorbBlock]
  simp only [bind, pure, h', ↓reduceIte]
  rfl

theorem os_runs_queryP {cv : Digest} {i : ℕ} {ps : List ℕ} {xs : List E} {os orest : List Opening}
    {roots : List (Digest × ℕ × ℕ)} {root : Digest} {height width : ℕ} {rows : List (List K)}
    (hr : roots[i]? = some (root, height, width))
    (ho : openAll (m := Id) blake2sBytes root height width ps os = some (rows, orest)) :
    Runs (Prog.queryP i ps) ⟨cv, xs, os, roots⟩ rows ⟨cv, xs, orest, roots⟩ := by
  simp only [Runs, Prog.queryP, runId, Compile.run, hr]
  simp only [bind] at ho ⊢
  rw [ho]
  rfl

/-- `openAll` over openings each of which climbs to the root. -/
theorem os_openAll_of {root : Digest} {height width : ℕ} :
    ∀ (ps : List ℕ) (os orest : List Opening), ps.length = os.length →
      (∀ j (hj : j < os.length), (os[j]).leaf.length = width ∧ (os[j]).path.length = height ∧
        climb (m := Id) blake2sBytes (hashWords (os[j]).leaf) (ps.getD j 0) (os[j]).path = root) →
      openAll (m := Id) blake2sBytes root height width ps (os ++ orest) =
        some (os.map (·.leaf), orest)
  | [], [], orest, _, _ => rfl
  | [], _ :: _, _, h, _ => absurd h (by simp)
  | _ :: _, [], _, h, _ => absurd h (by simp)
  | q :: ps, o :: os, orest, hl, hj => by
    obtain ⟨h1, h2, h3⟩ := hj 0 (by simp)
    have hone : openOne (m := Id) blake2sBytes root height width q o = true := by
      simp only [List.getElem_cons_zero, List.getD_cons_zero] at h1 h2 h3
      simp only [openOne, h1, h2, and_self, ↓reduceIte]
      show decide ((climb (m := Id) blake2sBytes (hashWords o.leaf) q o.path).toList = root.toList) = true
      rw [h3]
      exact decide_eq_true rfl
    have ih := os_openAll_of ps os orest (by simpa using hl) fun j hj' => by
      have := hj (j + 1) (by simpa using hj')
      simp only [List.getElem_cons_succ, List.getD_cons_succ] at this
      exact this
    simp only [List.cons_append, openAll, hone, ↓reduceIte, bind, pure]
    show Option.map _ (openAll (m := Id) blake2sBytes root height width ps (os ++ orest)) = _
    rw [ih]
    rfl

/-! ## Sums over lists -/

private theorem foldl_add_acc : ∀ (l : List E) (c : E), l.foldl (· + ·) c = c + l.foldl (· + ·) 0
  | [], c => by simp
  | x :: l, c => by
    rw [List.foldl_cons, List.foldl_cons, foldl_add_acc l (c + x), foldl_add_acc l (0 + x), zero_add,
      add_assoc]

private theorem foldl_mul_acc : ∀ (l : List E) (c : E), l.foldl (· * ·) c = c * l.foldl (· * ·) 1
  | [], c => by simp
  | x :: l, c => by
    rw [List.foldl_cons, List.foldl_cons, foldl_mul_acc l (c * x), foldl_mul_acc l (1 * x), one_mul,
      mul_assoc]

theorem os_dot_eq_sum' : ∀ (l r : List E), l.length = r.length →
    dot l r = ∑ j ∈ Finset.range l.length, l.getD j 0 * r.getD j 0
  | [], [], _ => by simp [dot]
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)
  | a :: l, b :: r, h => by
    have ih := os_dot_eq_sum' l r (by simpa using h)
    unfold dot at ih ⊢
    rw [List.zipWith_cons_cons, List.foldl_cons, foldl_add_acc, ih, List.length_cons,
      Finset.sum_range_succ', zero_add, add_comm]
    simp only [List.getD_cons_succ, List.getD_cons_zero]

private theorem foldl_pair_eq (g : List E → E) : ∀ (qws : List E) (rows : List (List E)),
    qws.length = rows.length → ∀ c : E,
    (qws.zip rows).foldl (fun t p => t + p.1 * g p.2) c =
      c + ∑ i ∈ Finset.range rows.length, qws.getD i 0 * g (rows.getD i [])
  | [], [], _, c => by simp
  | [], _ :: _, h, _ => absurd h (by simp)
  | _ :: _, [], h, _ => absurd h (by simp)
  | w :: qws, row :: rows, h, c => by
    rw [List.zip_cons_cons, List.foldl_cons, foldl_pair_eq g qws rows (by simpa using h),
      List.length_cons, Finset.sum_range_succ', add_assoc]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [add_comm (w * g row)]

theorem os_enforcedSum_eq (rows : List (List E)) (folds qws : List E) (h : qws.length = rows.length) :
    enforcedSum rows folds qws =
      ∑ i ∈ Finset.range rows.length, qws.getD i 0 * dot (rows.getD i []) (eqKernel folds) := by
  unfold enforcedSum
  rw [foldl_pair_eq (fun row => dot row (eqKernel folds)) qws rows h 0, zero_add]

theorem os_length_powersFrom (acc base : E) : ∀ n, (powersFrom acc base n).length = n
  | 0 => rfl
  | n + 1 => by simp [powersFrom, os_length_powersFrom _ _ n]

private theorem powersFrom_getD (base : E) : ∀ (n : ℕ) (acc : E) (i : ℕ), i < n →
    (powersFrom acc base n).getD i 0 = acc * base ^ i
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, acc, 0, _ => by simp [powersFrom]
  | n + 1, acc, i + 1, h => by
    simp only [powersFrom, List.getD_cons_succ]
    rw [powersFrom_getD base n _ i (by omega), pow_succ', mul_assoc]

theorem os_powers_getD {lam : E} {n i : ℕ} (h : i < n) : (powers lam n).getD i 0 = lam ^ i := by
  rw [powers, powersFrom_getD _ _ _ _ h, one_mul]

theorem os_extRow_length : ∀ (I : ℕ) (leaf : List K), leaf.length = 3 * I → (extRow leaf).length = I
  | 0, [], _ => rfl
  | 0, _ :: _, h => absurd h (by simp)
  | I + 1, c0 :: c1 :: c2 :: rest, h => by
    simp only [extRow, List.length_cons]
    rw [os_extRow_length I rest (by simp at h; omega)]
  | I + 1, [], h => absurd h (by simp)
  | I + 1, [_], h => absurd h (by simp; omega)
  | I + 1, [_, _], h => absurd h (by simp; omega)

theorem os_extRow_getD : ∀ (I : ℕ) (leaf : List K), leaf.length = 3 * I → ∀ j < I,
    (extRow leaf).getD j 0 = E.ofLimbs (leaf.getD (3 * j) 0) (leaf.getD (3 * j + 1) 0)
      (leaf.getD (3 * j + 2) 0)
  | 0, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | I + 1, c0 :: c1 :: c2 :: rest, h, 0, _ => by simp [extRow]
  | I + 1, c0 :: c1 :: c2 :: rest, h, j + 1, hj => by
    simp only [extRow, List.getD_cons_succ]
    rw [os_extRow_getD I rest (by simp at h; omega) j (by omega)]
    simp only [show 3 * (j + 1) = 3 * j + 3 by ring, List.getD_cons_succ]
  | I + 1, [], h, _, _ => absurd h (by simp)
  | I + 1, [_], h, _, _ => absurd h (by simp; omega)
  | I + 1, [_, _], h, _, _ => absurd h (by simp; omega)

/-! ## The query positions -/

/-- Query position `i` from the chain state `cv` (V:1598-1608): chunk `i % (192/depth)` of the
challenge `i / (192/depth)`. -/
def osPosOf (depth : ℕ) (cv : Digest) (i : ℕ) : ℕ :=
  (eToNat (challengeOf (sqCv (sqAll (i / (192 / depth)) cv).2)) >>> (i % (192 / depth) * depth)) %
    2 ^ depth

private theorem sqAll_succ' (j : ℕ) (cv : Digest) : (sqAll (j + 1) cv).2 = (sqAll j (sqCv cv)).2 := rfl

/-- **`sampleQueriesAux`** (V:1598): `k` samples cover `rem` positions, `per = 192/depth` at a
time, ending at the chain state after `k` squeezes. -/
private theorem runsTo_sampleQueriesAux (depth : ℕ) (hd : 0 < 192 / depth) :
    ∀ (k fuel rem : ℕ) (cv : Digest), rem ≤ k * (192 / depth) → (k - 1) * (192 / depth) < rem ∨ k = 0 →
      k ≤ fuel →
      RunsTo (sampleQueriesAux depth fuel rem) cv [] ((List.range rem).map (osPosOf depth cv))
        (sqAll k cv).2 := by
  intro k
  induction k with
  | zero =>
    intro fuel rem cv h1 _ _
    obtain rfl : rem = 0 := by omega
    show RunsTo (sampleQueriesAux depth fuel 0) cv [] [] cv
    cases fuel with
    | zero => exact runsTo_ret _ _
    | succ f =>
      simp only [sampleQueriesAux, ↓reduceIte]
      exact runsTo_ret _ _
  | succ k IH =>
    intro fuel rem cv h1 h2 h3
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hrem : rem ≠ 0 := by rcases h2 with h2 | h2 <;> omega
    have hn : min (192 / depth) rem = if k = 0 then rem else 192 / depth := by
      generalize 192 / depth = per at *
      split
      · subst_vars; simp at h1; omega
      · rcases h2 with h2 | h2
        · have : per ≤ k * per := Nat.le_mul_of_pos_left per (by omega)
          rw [show k + 1 - 1 = k by omega] at h2
          omega
        · omega
    have hr1 : rem - min (192 / depth) rem ≤ k * (192 / depth) := by
      rw [hn]
      generalize 192 / depth = per at *
      split
      · omega
      · rw [Nat.add_mul, Nat.one_mul] at h1; omega
    have hr2 : (k - 1) * (192 / depth) < rem - min (192 / depth) rem ∨ k = 0 := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · exact Or.inr hk
      · left
        rw [hn, ite_neg' (by omega)]
        generalize 192 / depth = per at *
        rcases h2 with h2 | h2
        · rw [show k + 1 - 1 = k by omega] at h2
          have : (k - 1) * per + per = k * per := by
            rw [← Nat.succ_mul, show (k - 1).succ = k by omega]
          omega
        · omega
    have ih := IH f (rem - min (192 / depth) rem) (sqCv cv) hr1 hr2 (by omega)
    unfold sampleQueriesAux
    simp only [hrem, ↓reduceIte]
    refine RunsTo.of_eq (RunsTo.bind (runsTo_sampleE cv) (RunsTo.bind ih (runsTo_ret _ _))) (by simp) ?_ rfl
    have hr : List.range rem = List.range (min (192 / depth) rem) ++
        (List.range (rem - min (192 / depth) rem)).map (min (192 / depth) rem + ·) := by
      rw [← List.range_add]; congr 1; omega
    rw [hr, List.map_append, List.map_map]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · refine List.map_congr_left fun i hi => ?_
      have hi' : i < min (192 / depth) rem := List.mem_range.mp hi
      have e1 : i / (192 / depth) = 0 := Nat.div_eq_of_lt (by omega)
      have e2 : i % (192 / depth) = i := Nat.mod_eq_of_lt (by omega)
      simp only [osPosOf]
      rw [e1, e2]
      rfl
    · refine List.map_congr_left fun i hi => ?_
      simp only [Function.comp, osPosOf]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · have : rem - min (192 / depth) rem = 0 := by rw [hn, ite_pos' hk]; omega
        rw [this] at hi; simp at hi
      · rw [show min (192 / depth) rem = 192 / depth by rw [hn, ite_neg' (by omega)],
          show (192 / depth + i) / (192 / depth) = i / (192 / depth) + 1 by
            rw [Nat.add_comm, Nat.add_div_right _ hd],
          Nat.add_mod_left, sqAll_succ']

/-- `sampleQueries` (V:1610) over `nq` positions in `k = ⌈nq / per⌉` samples. -/
theorem os_runsTo_sampleQueries {depth nq k : ℕ} (hd : 0 < 192 / depth) (h1 : nq ≤ k * (192 / depth))
    (h2 : (k - 1) * (192 / depth) < nq ∨ k = 0) (hk : k ≤ nq) (cv : Digest) :
    RunsTo (sampleQueries depth nq) cv [] ((List.range nq).map (osPosOf depth cv)) (sqAll k cv).2 :=
  runsTo_sampleQueriesAux depth hd k nq nq cv h1 h2 hk

/-! ## The glue -/

theorem os_glue_one (lam : E) (s : WhirState) (v : E) (i : List E) (wf : List E → E) :
    glue lam s [(v, i, wf)] =
      { s with quad := List.zipWith (fun q i ↦ q + 1 * lam * i) s.quad i,
               target := s.target + 1 * lam * v,
               glued := s.glued ++ [⟨1 * lam, s.folds.length, wf⟩] } := rfl

theorem os_glue_two (lam : E) (s : WhirState) (v1 v2 : E) (i1 i2 : List E) (w1 w2 : List E → E) :
    glue lam s [(v1, i1, w1), (v2, i2, w2)] =
      { s with quad := List.zipWith (fun q i ↦ q + 1 * lam * lam * i)
                 (List.zipWith (fun q i ↦ q + 1 * lam * i) s.quad i1) i2,
               target := s.target + 1 * lam * v1 + 1 * lam * lam * v2,
               glued := s.glued ++ [⟨1 * lam, s.folds.length, w1⟩] ++
                 [⟨1 * lam * lam, s.folds.length, w2⟩] } := rfl

/-! ## The induced weight and the out-of-domain weight as products -/

/-- The subspace-vanishing chain of `_induced_weight` (V:1655-1657) from `ch0`, coordinates from
`s` on. -/
def osIwChain (roots : List E) (s : ℕ) (ch0 : E) : ℕ → E
  | 0 => ch0
  | t + 1 => osIwChain roots s ch0 t ^ 2 + roots.getD (s + t) 0 * osIwChain roots s ch0 t

private theorem iwChain_shift (roots : List E) (s : ℕ) (ch0 : E) (t : ℕ) :
    osIwChain roots (s + 1) (ch0 ^ 2 + roots.getD s 0 * ch0) t = osIwChain roots s ch0 (t + 1) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [osIwChain, ih, show s + 1 + t = s + (t + 1) by ring]

/-- One query's product in `_induced_weight` (V:1653-1657). -/
private theorem iw_foldl (roots inverses : List E) :
    ∀ (l : List E) (s : ℕ) (a ch : E),
      (l.zipIdx s).foldl (fun (acc : E × E) (p : E × ℕ) ↦
        (acc.1 * (1 + p.1 * (1 + acc.2 * inverses.getD p.2 0)),
          acc.2 ^ 2 + roots.getD p.2 0 * acc.2)) (a, ch) =
      (a * ∏ t ∈ Finset.range l.length,
          (1 + l.getD t 0 * (1 + osIwChain roots s ch t * inverses.getD (s + t) 0)),
        osIwChain roots s ch l.length)
  | [], s, a, ch => by simp [osIwChain]
  | c :: l, s, a, ch => by
    rw [List.zipIdx_cons, List.foldl_cons, iw_foldl roots inverses l (s + 1)]
    simp only [List.length_cons, Finset.prod_range_succ', List.getD_cons_zero, List.getD_cons_succ,
      osIwChain, Nat.add_zero, iwChain_shift, show ∀ t, s + 1 + t = s + (t + 1) from fun t => by ring]
    refine Prod.ext ?_ rfl
    simp only
    ring

private theorem foldl_zip_sum' {β : Type} (F : E → E × β → E) (G : E → β → E)
    (hF : ∀ t w q, F t (w, q) = t + G w q) (d : β) : ∀ (ws : List E) (bs : List β),
    ws.length = bs.length → ∀ c, (ws.zip bs).foldl F c =
      c + ∑ i ∈ Finset.range bs.length, G (ws.getD i 0) (bs.getD i d)
  | [], [], _, c => by simp
  | [], _ :: _, h, _ => absurd h (by simp)
  | _ :: _, [], h, _ => absurd h (by simp)
  | w :: ws, b :: bs, h, c => by
    rw [List.zip_cons_cons, List.foldl_cons, hF, foldl_zip_sum' F G hF d ws bs (by simpa using h),
      List.length_cons, Finset.sum_range_succ', add_assoc]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [add_comm (G w b)]

/-- **`_induced_weight`** (V:1643) as a sum over the queries of their weights times their
products. -/
theorem os_inducedWeight_eq (ml : ℕ) (qs : List ℕ) (qws point : List E) (h : qws.length = qs.length) :
    inducedWeight ml qs qws point = ∑ x ∈ Finset.range qs.length, qws.getD x 0 *
      ∏ t ∈ Finset.range point.length, (1 + point.getD t 0 *
        (1 + osIwChain (subspaceRoots ml) 0 (eOfNat (qs.getD x 0)) t *
          ((subspaceRoots ml).map fun v ↦ if v = 0 then 0 else v⁻¹).getD t 0)) := by
  unfold inducedWeight
  simp only
  refine (foldl_zip_sum' _ (fun w q ↦ w * ∏ t ∈ Finset.range point.length, (1 + point.getD t 0 *
        (1 + osIwChain (subspaceRoots ml) 0 (eOfNat q) t *
          ((subspaceRoots ml).map fun v ↦ if v = 0 then 0 else v⁻¹).getD t 0))) ?_ 0 qws qs h 0).trans
    (zero_add _)
  intro t w q
  simp only
  rw [iw_foldl]
  simp

/-- **`eq_eval`** (V:703) as a product over the coordinates. -/
theorem os_eqEval_eq : ∀ (z p : List E), z.length = p.length →
    eqEval z p = ∏ t ∈ Finset.range z.length, (1 + z.getD t 0 + p.getD t 0)
  | [], [], _ => by simp [eqEval]
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)
  | a :: z, b :: p, h => by
    have ih := os_eqEval_eq z p (by simpa using h)
    unfold eqEval at ih ⊢
    rw [List.zipWith_cons_cons, List.foldl_cons, List.length_cons, Finset.prod_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, one_mul]
    rw [foldl_mul_acc, ih, mul_comm]

end
end LeanVM.Guest.B1
