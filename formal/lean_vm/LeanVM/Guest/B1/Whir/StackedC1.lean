/-
  LeanVM.Guest.B1.Whir.StackedC1

  The completeness of `open_stacked`'s first blocks: the materialized pointers, `fs_next`, the
  fold rounds.
-/

module

public import LeanVM.Guest.B1.Whir.StackedInv
public import LeanVM.Guest.B1.Whir.StackedBlocks
public import LeanVM.Guest.B1.Whir.QueriesComplete

/-!
# `open_stacked`'s blocks, honestly: pointers, reads, folds (TRIAGE #36)

`OsAt σ st cv cur p`: the guest's state `st` against the chain state `cv` with `p` words of the
stream at `cur` read: the Fiat-Shamir cells are `cv`'s and the cursor points `p` words on. Every
block lemma takes the block's honest values at its value range (`*Vals`, a list from the block's
first value) and gives its relation and the state after it.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The guest's state against the chain state `cv` and `p` words read from `cur`. -/
structure OsAt (σ : Val) (st : OsSt) (cv : Digest) (cur : E) (p : ℕ) : Prop where
  fs : (σ (.n st.f0), σ (.n st.f1)) = digestScalars cv
  cursor : σ (.n st.cb) * gen ^ st.co = cur * gen ^ p

/-! ## Pointers -/

/-- The values of `osMat base off k` from `k`, at the base `bv`. -/
def osMatVals (bv : E) (off : ℕ) : List E := if off = 0 then [] else [osGw off, bv * osGw off]

theorem osMat_next' (base off k : ℕ) : (osMat base off k).2.2 = k + (osMatVals 0 off).length := by
  unfold osMat osMatVals; split <;> simp

theorem os_length_matVals' (bv : E) (off : ℕ) : (osMatVals bv off).length = (osMatVals 0 off).length := by
  unfold osMatVals; split <;> simp

theorem osMat_complete {base off k : ℕ} (hoff : off < 2 ^ 128) {kret : List E → Prop}
    (hv : ∀ j < (osMatVals (σ (.n base)) off).length, σ (.n (k + j)) = (osMatVals (σ (.n base)) off).getD j 0) :
    Stmt.HoldsList C rd σ (osMat base off k).1 True kret ∧
      σ (.n (osMat base off k).2.1) = σ (.n base) * gen ^ off := by
  unfold osMat
  by_cases h0 : off = 0
  · simp [h0, Stmt.HoldsList]
  · have e0 := hv 0 (by simp [osMatVals, h0])
    have e1 := hv 1 (by simp [osMatVals, h0])
    simp only [osMatVals, h0, ↓reduceIte, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1
    simp only [h0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨⟨e0, by rw [e1, e0]⟩, by rw [e1, os_gw_eq hoff]⟩

/-! ## `fs_next` -/

/-- The values of `osFsNext` from its first: the word `x`, then `fs_compress`'s. -/
def osFsNextVals (x : E) (cv : Digest) : List E := x :: (List.range 14).map (fsVals x cv 1)

theorem os_cursor_load {σ : Val} {st : OsSt} {cv : Digest} {cur : E} {p : ℕ} (hat : OsAt σ st cv cur p)
    {j : ℕ} {w : E} (h : LoadHolds rd cur (p + j) w) :
    LoadHolds rd (σ (.n st.cb)) (st.co + j) w := by
  rw [← loadHolds_mul_gen_pow, hat.cursor, loadHolds_mul_gen_pow]
  exact h

/-- **`fs_next`** at its honest values: the word at the cursor read and absorbed. -/
theorem osFsNext_complete {s : OsSt} {cv : Digest} {cur : E} {p : ℕ} (hat : OsAt σ s cv cur p)
    {x : E} (hx : LoadHolds rd cur p x) {kret : List E → Prop}
    (hv : ∀ j < 15, σ (.n (s.k + j)) = (osFsNextVals x cv).getD j 0) :
    Stmt.HoldsList C rd σ (osFsNext s).1 True kret ∧ OsAt σ (osFsNext s).2 (obsCv cv x) cur (p + 1) := by
  have e0 : σ (.n s.k) = x := by simpa [osFsNextVals] using hv 0 (by omega)
  have e : ∀ j < 14, σ (.n (s.k + 1 + j)) = fsVals x cv 1 j := fun j hj => by
    rw [show s.k + 1 + j = s.k + (j + 1) by ring, hv _ (by omega)]
    simp [osFsNextVals, List.getD_eq_getElem?_getD, hj]
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · show Stmt.HoldsList C rd σ (fsNextT (.n s.f0) (.n s.f1) (.n s.cb) s.co s.k) True kret
    rw [holds_fsNextT]
    refine ⟨⟨?_, cv, hat.fs, fun j h1 h2 => ?_⟩, trivial⟩
    · have hl := os_cursor_load (j := 0) hat (by rw [Nat.add_zero]; exact hx)
      rw [Nat.add_zero] at hl
      rw [e0]; exact hl
    · rw [e j h2, e0]
  · show (σ (.n (s.k + 13)), σ (.n (s.k + 14))) = _
    rw [show s.k + 13 = s.k + 1 + 12 by ring, show s.k + 14 = s.k + 1 + 13 by ring, e 12 (by omega),
      e 13 (by omega)]
    simp only [fsVals, absorbCv_one]
  · show σ (.n s.cb) * gen ^ (s.co + 1) = cur * gen ^ (p + 1)
    rw [pow_succ, pow_succ, ← mul_assoc, ← mul_assoc, hat.cursor]

/-! ## The fold rounds -/

/-- The values of one fold round from its first, the cursor at `bv·g^co`, `p` words read: the
pointer, `opening_fold`'s returns, the copies, the next quadratic's middle coefficient. -/
def osFoldVals (xs : List E) (cv : Digest) (p : ℕ) (q : List E) (bv : E) (co : ℕ) : List E :=
  let ch := challengeOf (sqCv cv)
  let t := polyEval q ch
  let d0 := xs.getD p 0
  let d2 := xs.getD (p + 1) 0
  let cv' := obsAll (sqCv cv) [d0, d2]
  osMatVals bv co ++ [(digestScalars cv').1, (digestScalars cv').2, bv * osGw co * gen ^ 2, t, d0, d2, ch,
    (digestScalars cv').1, (digestScalars cv').2, t + d2]

/-- `opening_fold`'s returns at a round. -/
def osFoldRets (xs : List E) (cv : Digest) (p : ℕ) (q : List E) (curv : E) : List E :=
  let ch := challengeOf (sqCv cv)
  let t := polyEval q ch
  let d0 := xs.getD p 0
  let d2 := xs.getD (p + 1) 0
  let cv' := obsAll (sqCv cv) [d0, d2]
  [(digestScalars cv').1, (digestScalars cv').2, curv * gen ^ 2, t, d0, d2, ch]

theorem os_range7 (r : ℕ) : ((List.range 7).map fun j => V.n (r + j)) =
    [.n r, .n (r + 1), .n (r + 2), .n (r + 3), .n (r + 4), .n (r + 5), .n (r + 6)] := by
  simp [List.range_succ]

/-- **One fold round** at its honest values, its call holding. -/
theorem osFold_complete {s : OsSt} {cv : Digest} {cur : E} {p : ℕ} {xs : List E} (hat : OsAt σ s cv cur p)
    (hco : s.co < 2 ^ 128) {fch fo : ℕ} {kret : List E → Prop}
    (hv : ∀ j < (osFoldVals xs cv p [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (σ (.n s.cb)) s.co).length,
      σ (.n (s.k + j)) = (osFoldVals xs cv p [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (σ (.n s.cb)) s.co).getD j 0)
    (hcall : C "opening_fold" [σ (.n s.f0), σ (.n s.f1), σ (.n s.cb) * gen ^ s.co, σ (.n s.c), σ (.n s.b),
      σ (.n s.a)] (osFoldRets xs cv p [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (σ (.n s.cb) * gen ^ s.co)))
    (hst : LoadHolds rd (σ (.n fch)) fo (challengeOf (sqCv cv))) :
    Stmt.HoldsList C rd σ (osFold s fch fo).1 True kret ∧
      OsAt σ (osFold s fch fo).2 (obsAll (sqCv cv) [xs.getD p 0, xs.getD (p + 1) 0]) cur (p + 2) ∧
      (osFold s fch fo).2.co = 0 ∧ σ (.n (osFold s fch fo).2.cb) = σ (.n s.cb) * osGw s.co * gen ^ 2 ∧
      σ (.n (osFold s fch fo).2.t) = polyEval [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (challengeOf (sqCv cv)) ∧
      [σ (.n (osFold s fch fo).2.c), σ (.n (osFold s fch fo).2.b), σ (.n (osFold s fch fo).2.a)] =
        [xs.getD p 0, polyEval [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (challengeOf (sqCv cv)) +
          xs.getD (p + 1) 0, xs.getD (p + 1) 0] ∧
      (osFold s fch fo).2.k = s.k + (osFoldVals xs cv p [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (σ (.n s.cb)) s.co).length := by
  set q := [σ (.n s.c), σ (.n s.b), σ (.n s.a)]
  set M := osMatVals (σ (.n s.cb)) s.co with hM
  set ch := challengeOf (sqCv cv)
  set t := polyEval q ch
  set d0 := xs.getD p 0
  set d2 := xs.getD (p + 1) 0
  set cv' := obsAll (sqCv cv) [d0, d2]
  set T : List E := [(digestScalars cv').1, (digestScalars cv').2, σ (.n s.cb) * osGw s.co * gen ^ 2, t, d0, d2, ch,
    (digestScalars cv').1, (digestScalars cv').2, t + d2] with hT
  have hvals : osFoldVals xs cv p q (σ (.n s.cb)) s.co = M ++ T := rfl
  rw [hvals] at hv
  have hlen : (M ++ T).length = M.length + 10 := by simp [hT]
  have hr : (osMat s.cb s.co s.k).2.2 = s.k + M.length := by
    rw [osMat_next', hM, os_length_matVals' (σ (.n s.cb))]
  have hm := osMat_complete (C := C) (rd := rd) (σ := σ) (base := s.cb) (k := s.k) (kret := kret) hco fun j hj => by
    rw [hv j (by rw [hlen, hM]; omega), oq_getD_app_lt hj]
  have gT : ∀ j < 10, σ (.n ((osMat s.cb s.co s.k).2.2 + j)) = T.getD j 0 := fun j hj => by
    rw [hr, show s.k + M.length + j = s.k + (M.length + j) by ring, hv _ (by rw [hlen]; omega),
      oq_getD_app_ge (by omega), Nat.add_sub_cancel_left]
  have hgw : σ (.n s.cb) * osGw s.co = σ (.n s.cb) * gen ^ s.co := by rw [os_gw_eq hco]
  generalize hR : (osMat s.cb s.co s.k).2.2 = r at gT hr
  have g := fun j (hj : j < 10) => gT j hj
  have g0 := g 0 (by omega); have g1 := g 1 (by omega); have g2 := g 2 (by omega)
  have g3 := g 3 (by omega); have g4 := g 4 (by omega); have g5 := g 5 (by omega)
  have g6 := g 6 (by omega); have g7 := g 7 (by omega); have g8 := g 8 (by omega)
  have g9 := g 9 (by omega)
  simp only [hT, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  unfold osFold
  dsimp only
  rw [hR]
  refine ⟨?_, ⟨?_, ?_⟩, rfl, g2, g3, ?_, by rw [hvals, hlen, hr]; ring⟩
  · rw [holdsList_append]
    refine (holdsList_noRet _ (osMat_noRet _ _ _) _ _).mpr ⟨hm.1, ?_⟩
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, os_range7, List.map_cons, List.map_nil, and_true]
    refine ⟨?_, by rw [g7, g0], by rw [g8, g1], by rw [g6]; exact hst, by rw [g9, g3, g5]⟩
    rw [hm.2, g0, g1, g2, g3, g4, g5, g6, hgw]
    exact hcall
  · show (σ (.n (r + 7)), σ (.n (r + 8))) = _
    rw [g7, g8]
  · show σ (.n (r + 2)) * gen ^ 0 = cur * gen ^ (p + 2)
    rw [g2, pow_zero, mul_one, hgw, hat.cursor, mul_assoc, ← pow_add]
  · show [σ (.n (r + 4)), σ (.n (r + 9)), σ (.n (r + 5))] = _
    rw [g4, g9, g5]

/-- The call relation `open_stacked`'s honest valuation is checked under: its callees are placed
separately, so every call holds. -/
abbrev osTC : CallRel := fun _ _ _ => True

theorem os_drop_cons {xs : List E} {p : ℕ} {a : E} {rest : List E} (h : xs.drop p = a :: rest) :
    xs.getD p 0 = a ∧ rest = xs.drop (p + 1) := by
  have h0 := congrArg (·[0]?) h
  simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at h0
  refine ⟨by simp [List.getD_eq_getElem?_getD, h0], ?_⟩
  rw [← List.drop_drop, h]; rfl

theorem os_drop_cons2 {xs : List E} {p : ℕ} {a b : E} {rest : List E} (h : xs.drop p = a :: b :: rest) :
    xs.getD p 0 = a ∧ xs.getD (p + 1) 0 = b ∧ rest = xs.drop (p + 2) := by
  obtain ⟨h1, h2⟩ := os_drop_cons h
  obtain ⟨h3, h4⟩ := os_drop_cons h2.symm
  exact ⟨h1, h3, by rw [h4]⟩

/-- The values of `n` fold rounds from their first. -/
def osFoldsVals (xs : List E) : ℕ → Digest → ℕ → List E → E → ℕ → List E
  | 0, _, _, _, _, _ => []
  | n + 1, cv, p, q, bv, co =>
    let ch := challengeOf (sqCv cv)
    let t := polyEval q ch
    let d0 := xs.getD p 0
    let d2 := xs.getD (p + 1) 0
    osFoldVals xs cv p q bv co ++
      osFoldsVals xs n (obsAll (sqCv cv) [d0, d2]) (p + 2) [d0, t + d2, d2] (bv * osGw co * gen ^ 2) 0

theorem os_foldRounds_folds : ∀ {n : ℕ} {w : WhirState} {lf : List E} {s : St} {res : WhirState × List E} {s' : St},
    Runs (foldRounds n w lf) s res s' →
      ∃ chs, res.1.folds = w.folds ++ chs ∧ res.2 = lf ++ chs ∧ chs.length = n
  | 0, w, lf, s, res, s', h => by
    obtain ⟨rfl, -⟩ := os_inv_pure h
    exact ⟨[], by simp, by simp, rfl⟩
  | n + 1, w, lf, s, res, s', h => by
    simp only [foldRounds] at h
    obtain ⟨ch, s1, -, h2⟩ := os_inv_bind h
    obtain ⟨q, s2, -, h4⟩ := os_inv_bind h2
    obtain ⟨chs, h5, h6, h7⟩ := os_foldRounds_folds h4
    exact ⟨ch :: chs, by rw [h5]; simp, by rw [h6]; simp, by simp [h7]⟩

theorem os_runs_foldStep {q : List E} {sp sp' : St} {r : E × E × List E}
    (h : Runs (foldStep q) sp r sp') :
    ∃ d0 d2 rest, sp.stream = d0 :: d2 :: rest ∧
      r = (challengeOf (sqCv sp.cv), polyEval q (challengeOf (sqCv sp.cv)),
        [d0, polyEval q (challengeOf (sqCv sp.cv)) + d2, d2]) ∧
      sp' = ⟨obsAll (sqCv sp.cv) [d0, d2], rest, sp.openings, sp.roots⟩ := by
  simp only [foldStep] at h
  obtain ⟨ch, s1, h1, h2⟩ := os_inv_bind h
  obtain ⟨qq, s2, h3, h4⟩ := os_inv_bind h2
  obtain ⟨rfl, rfl⟩ := os_inv_pure h4
  obtain ⟨rfl, rfl⟩ := os_inv_sampleE h1
  obtain ⟨c0, c2, rest, hs, rfl, rfl⟩ := os_inv_roundPoly3 h3
  exact ⟨c0, c2, rest, hs, rfl, rfl⟩

/-- **The fold rounds** at their honest values: `n` rounds of `foldRounds` (V:1678) from the
specification's state at `p` words of `xs` read, each challenge stored at `fch[fo + j]`. -/
theorem osFolds_complete {xs : List E} {cur : E} {fch : ℕ} {kret : List E → Prop} {C : CallRel}
    (hcall : ∀ (cv' : Digest) (p' : ℕ) (q' : List E), q'.length = 3 → p' + 2 ≤ xs.length →
      C "opening_fold" [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ p', q'.getD 0 0, q'.getD 1 0,
        q'.getD 2 0] (osFoldRets xs cv' p' q' (cur * gen ^ p'))) :
    ∀ (n fo : ℕ) (s : OsSt) (cv : Digest) (p : ℕ) (w : WhirState) (lf : List E) (osp : List Opening)
      (roots : List (Digest × ℕ × ℕ)) (res : WhirState × List E) (sp' : St),
      OsAt σ s cv cur p → s.co < 2 ^ 128 → w.quad = [σ (.n s.c), σ (.n s.b), σ (.n s.a)] →
      Runs (foldRounds n w lf) ⟨cv, xs.drop p, osp, roots⟩ res sp' →
      (∀ j < (osFoldsVals xs n cv p w.quad (σ (.n s.cb)) s.co).length,
        σ (.n (s.k + j)) = (osFoldsVals xs n cv p w.quad (σ (.n s.cb)) s.co).getD j 0) →
      (∀ j < n, LoadHolds rd (σ (.n fch)) (fo + j) (res.1.folds.getD (w.folds.length + j) 0)) →
      Stmt.HoldsList C rd σ (osFolds fch fo n s).1 True kret ∧
        OsAt σ (osFolds fch fo n s).2 sp'.cv cur (p + 2 * n) ∧ sp' = ⟨sp'.cv, xs.drop (p + 2 * n), osp, roots⟩ ∧
        res.1.quad = [σ (.n (osFolds fch fo n s).2.c), σ (.n (osFolds fch fo n s).2.b),
          σ (.n (osFolds fch fo n s).2.a)] ∧ res.1.target = (if n = 0 then w.target else σ (.n (osFolds fch fo n s).2.t)) ∧
        res.1.glued = w.glued ∧ res.1.folds.length = w.folds.length + n ∧
        (∃ chs, res.1.folds = w.folds ++ chs ∧ res.2 = lf ++ chs) ∧
        (osFolds fch fo n s).2.co = (if n = 0 then s.co else 0) ∧
        (osFolds fch fo n s).2.k = s.k + (osFoldsVals xs n cv p w.quad (σ (.n s.cb)) s.co).length
  | 0, fo, s, cv, p, w, lf, osp, roots, res, sp', hat, _, _, hrun, _, _ => by
    obtain ⟨rfl, rfl⟩ := os_inv_pure hrun
    exact ⟨trivial, by simpa [osFolds] using hat, by simp, by simpa [osFolds], by simp, rfl, by simp,
      ⟨[], by simp, by simp⟩, by simp [osFolds], by simp [osFolds, osFoldsVals]⟩
  | n + 1, fo, s, cv, p, w, lf, osp, roots, res, sp', hat, hco, hq, hrun, hv, hst => by
    rw [foldRounds_succ] at hrun
    obtain ⟨⟨ch, t, q'⟩, sp1, h1, h2⟩ := os_inv_bind hrun
    obtain ⟨d0, d2, rest, hs, he, hsp1⟩ := os_runs_foldStep h1
    simp only at hs
    have hlen2 : p + 2 ≤ xs.length := by
      have := congrArg List.length hs
      simp only [List.length_drop, List.length_cons] at this
      omega
    obtain ⟨hd0, hd2, hrest⟩ := os_drop_cons2 hs
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    subst hrest
    simp only at hsp1
    subst hsp1
    rw [hq] at hv
    set V1 := osFoldVals xs cv p [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (σ (.n s.cb)) s.co with hV1
    have hvs : osFoldsVals xs (n + 1) cv p [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (σ (.n s.cb)) s.co =
        V1 ++ osFoldsVals xs n (obsAll (sqCv cv) [d0, d2]) (p + 2)
          [d0, polyEval [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (challengeOf (sqCv cv)) + d2, d2]
          (σ (.n s.cb) * osGw s.co * gen ^ 2) 0 := by rw [osFoldsVals, ← hd0, ← hd2]
    rw [hvs] at hv
    obtain ⟨chs', hF1, hF2, hFl⟩ := os_foldRounds_folds h2
    simp only at hF1 hF2
    have hst0 : LoadHolds rd (σ (.n fch)) fo (challengeOf (sqCv cv)) := by
      have := hst 0 (by omega)
      rw [hF1, List.append_assoc, oq_getD_app_ge (by omega), Nat.add_sub_cancel_left] at this
      simpa using this
    have hc1 : C "opening_fold" [σ (.n s.f0), σ (.n s.f1), σ (.n s.cb) * gen ^ s.co, σ (.n s.c), σ (.n s.b),
        σ (.n s.a)] (osFoldRets xs cv p [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (σ (.n s.cb) * gen ^ s.co)) := by
      have := hcall cv p [σ (.n s.c), σ (.n s.b), σ (.n s.a)] rfl hlen2
      have e0 : (digestScalars cv).1 = σ (.n s.f0) := by rw [← hat.fs]
      have e1 : (digestScalars cv).2 = σ (.n s.f1) := by rw [← hat.fs]
      rw [e0, e1, ← hat.cursor] at this
      exact this
    obtain ⟨hH1, hat1, hco1, hcb1, ht1, hq1, hk1⟩ := osFold_complete (C := C) (rd := rd) (xs := xs)
      (fch := fch) (fo := fo) (kret := kret) hat hco (fun j hj => by
        have hj' : j < V1.length := hj
        rw [hv j (by simp only [List.length_append]; omega), oq_getD_app_lt hj]) hc1 hst0
    rw [hd0, hd2] at hat1 hq1
    rw [← hV1] at hk1
    set st1 := (osFold s fch fo).2
    set w1 : WhirState := ⟨polyEval [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (challengeOf (sqCv cv)),
      [d0, polyEval [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (challengeOf (sqCv cv)) + d2, d2],
      w.folds ++ [challengeOf (sqCv cv)], w.glued⟩ with hw1
    have ih := osFolds_complete (xs := xs) (cur := cur) (fch := fch) (kret := kret) hcall n (fo + 1) st1
      (obsAll (sqCv cv) [d0, d2]) (p + 2) w1
      (lf ++ [challengeOf (sqCv cv)]) osp roots res sp' hat1 (by rw [hco1]; exact Nat.two_pow_pos 128) (by rw [hq1])
      (by simp only at h2; rw [hq] at h2; exact h2)
      (fun j hj => by
        rw [show w1.quad = [d0, polyEval [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (challengeOf (sqCv cv)) + d2, d2]
          from rfl, hcb1, hco1] at hj ⊢
        rw [hk1, Nat.add_assoc, hv _ (by simp only [List.length_append]; omega), oq_getD_app_ge (by omega),
          Nat.add_sub_cancel_left])
      (fun j hj => by
        have := hst (j + 1) (by omega)
        rwa [show fo + 1 + j = fo + (j + 1) by ring, show w1.folds.length + j = w.folds.length + (j + 1) by
          rw [show w1.folds = w.folds ++ [challengeOf (sqCv cv)] from rfl]; simp; omega])
    obtain ⟨hH, hat', hsp', hq', ht', hg', hfl', ⟨chs, hc1, hc2⟩, hco', hk'⟩ := ih
    refine ⟨?_, by rwa [show p + 2 * (n + 1) = p + 2 + 2 * n by ring], by rw [hsp']; congr 2; ring, hq', ?_,
      hg', by rw [hfl', show w1.folds = w.folds ++ [challengeOf (sqCv cv)] from rfl]; simp; omega,
      ⟨challengeOf (sqCv cv) :: chs, by rw [hc1, show w1.folds = w.folds ++ [challengeOf (sqCv cv)] from rfl]; simp,
        by rw [hc2]; simp⟩, ?_, ?_⟩
    · show Stmt.HoldsList C rd σ ((osFold s fch fo).1 ++ (osFolds fch (fo + 1) n st1).1) True kret
      rw [holdsList_append]
      exact (holdsList_noRet _ (osFold_noRet _ _ _) _ _).mpr ⟨hH1, hH⟩
    · rw [ht', ite_neg' (show ¬ (n + 1 = 0) by omega)]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [ite_pos' (show (0 : ℕ) = 0 from rfl)]; exact ht1.symm
      · rw [ite_neg' (show ¬ (n = 0) by omega)]; rfl
    · show (osFolds fch (fo + 1) n st1).2.co = _
      rw [hco', hco1]; split <;> simp
    · show (osFolds fch (fo + 1) n st1).2.k = _
      rw [hk', hk1, hq, hvs, List.length_append]
      rw [show w1.quad = [d0, polyEval [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (challengeOf (sqCv cv)) + d2, d2]
        from rfl, hcb1, hco1]
      ring

end
end LeanVM.Guest.B1
