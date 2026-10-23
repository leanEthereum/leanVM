/-
  LeanVM.Guest.B1.Whir.StackedBlocks

  The soundness of `open_stacked`'s blocks: each block's relation gives its facts in the
  specification's terms, against the chain state and the words read so far.
-/

module

public import LeanVM.Guest.B1.Whir.StackedT
public import LeanVM.Guest.B1.Whir.StackedRun
public import LeanVM.Guest.B1.Whir.Queries
public import LeanVM.Guest.B1.Opening
public import LeanVM.Guest.B1.RowWeights
public import LeanVM.Guest.B1.QueryBits
public import LeanVM.Guest.B1.FoldFinal

/-!
# The blocks of `open_stacked` (TRIAGE #36)

`OsCur` is what the guest's running state says against the specification's: the Fiat-Shamir
cells are the chain state `cv`, the words `xs` read so far lie at the cursor, and the guest's
cursor (a base value and a word offset) points past them. Every block lemma takes the block's
relation (with no continuation, by `holdsList_true_of`) and returns its facts.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The running state -/

/-- The guest's state `st` against the chain state `cv` and the words `xs` read from `cur`. -/
structure OsCur (rd : Reader) (σ : Val) (cur : E) (st : OsSt) (cv : Digest) (xs : List E) :
    Prop where
  fs : (σ (.n st.f0), σ (.n st.f1)) = digestScalars cv
  reads : ReadsAt rd cur xs
  cursor : σ (.n st.cb) * gen ^ st.co = cur * gen ^ xs.length

theorem os_gw_eq {e : ℕ} (h : e < 2 ^ 128) : osGw e = gen ^ e := kw_gpowK h

private theorem readsAt_append {cur : E} {xs ys : List E} (hx : ReadsAt rd cur xs)
    (hy : ∀ j (hj : j < ys.length), LoadHolds rd cur (xs.length + j) ys[j]) :
    ReadsAt rd cur (xs ++ ys) := by
  intro k hk
  rw [List.length_append] at hk
  rcases Nat.lt_or_ge k xs.length with h | h
  · rw [List.getElem_append_left h]; exact hx k h
  · rw [List.getElem_append_right h]
    have := hy (k - xs.length) (by omega)
    rwa [show xs.length + (k - xs.length) = k by omega] at this

/-- A read at the cursor's offset `co + j` is the read at `|xs| + j` from `cur`. -/
theorem OsCur.load {cur : E} {st : OsSt} {cv : Digest} {xs : List E} (h : OsCur rd σ cur st cv xs)
    {j : ℕ} {w : E} (hl : LoadHolds rd (σ (.n st.cb)) (st.co + j) w) :
    LoadHolds rd cur (xs.length + j) w := by
  rw [← loadHolds_mul_gen_pow, ← h.cursor, loadHolds_mul_gen_pow]
  exact hl

/-- The cursor's pointer, materialized (`osMat`). -/
theorem osMat_sound {base off k : ℕ} (hoff : off < 2 ^ 128) {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (osMat base off k).1 True kret) :
    σ (.n (osMat base off k).2.1) = σ (.n base) * gen ^ off := by
  unfold osMat at h ⊢
  by_cases h0 : off = 0
  · simp only [h0, ↓reduceIte, pow_zero, mul_one]
  · simp only [h0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h ⊢
    rw [h.2.1, h.1, os_gw_eq hoff]

theorem osMat_next (base off k : ℕ) : k ≤ (osMat base off k).2.2 := by
  unfold osMat; split <;> simp

theorem osMat_noRet (base off k : ℕ) : Stmt.noRetList (osMat base off k).1 = true := by
  unfold osMat; split <;> rfl

/-! ## `fs_next` -/

/-- **`fs_next`** at the running state: the word at the cursor is read and absorbed. -/
theorem osFsNext_sound {cur : E} {s : OsSt} {cv : Digest} {xs : List E} (hat : OsCur rd σ cur s cv xs)
    {kret : List E → Prop} (h : Stmt.HoldsList C rd σ (osFsNext s).1 True kret) :
    OsCur rd σ cur (osFsNext s).2 (obsCv cv (σ (.n s.k))) (xs ++ [σ (.n s.k)]) := by
  rw [osFsNext, holds_fsNextT] at h
  obtain ⟨⟨hl, cv', hcv', e⟩, -⟩ := h
  have hcv : cv' = cv := digestScalars_injective (hcv'.symm.trans hat.fs)
  subst hcv
  refine ⟨?_, readsAt_append hat.reads fun j hj => ?_, ?_⟩
  · show (σ (.n (s.k + 13)), σ (.n (s.k + 14))) = _
    rw [show s.k + 13 = s.k + 1 + 12 by ring, show s.k + 14 = s.k + 1 + 13 by ring,
      e 12 (by omega) (by omega), e 13 (by omega) (by omega)]
    rfl
  · simp only [List.length_cons, List.length_nil] at hj
    obtain rfl : j = 0 := by omega
    exact hat.load (j := 0) (by simpa using hl)
  · show σ (.n s.cb) * gen ^ (s.co + 1) = cur * gen ^ (xs ++ [σ (.n s.k)]).length
    rw [List.length_append, List.length_singleton, pow_succ, pow_succ, ← mul_assoc, ← mul_assoc,
      hat.cursor]


/-! ## The fold rounds -/

private theorem range7_map (r : ℕ) : ((List.range 7).map fun j => V.n (r + j)) =
    [.n r, .n (r + 1), .n (r + 2), .n (r + 3), .n (r + 4), .n (r + 5), .n (r + 6)] := by
  simp [List.range_succ]

/-- **One fold round** (`opening_fold`, G:945): from the chain state `cv`, the challenge
`challengeOf (sqCv cv)` is stored at `fch[fo]`, the next quadratic's `d0, d2` are read, and the
running quadratic and claim are `foldStep`'s (V:1678). -/
theorem osFold_sound {cur : E} {s : OsSt} {cv : Digest} {xs : List E} (hat : OsCur rd σ cur s cv xs)
    (hco : s.co < 2 ^ 128) {fch fo : ℕ} {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ (osFold s fch fo).1 True kret) :
    ∃ d0 d2, OsCur rd σ cur (osFold s fch fo).2 (obsAll (sqCv cv) [d0, d2]) (xs ++ [d0, d2]) ∧
      (osFold s fch fo).2.co = 0 ∧
      RunsTo (foldStep [σ (.n s.c), σ (.n s.b), σ (.n s.a)]) cv [d0, d2]
        (challengeOf (sqCv cv), σ (.n (osFold s fch fo).2.t),
          [σ (.n (osFold s fch fo).2.c), σ (.n (osFold s fch fo).2.b), σ (.n (osFold s fch fo).2.a)])
        (obsAll (sqCv cv) [d0, d2]) ∧
      LoadHolds rd (σ (.n fch)) fo (challengeOf (sqCv cv)) := by
  unfold osFold at h ⊢
  simp only at h ⊢
  rw [holdsList_append] at h
  obtain ⟨hm, h⟩ := holdsList_true_of (osMat_noRet _ _ _) h
  have hp := osMat_sound hco hm
  generalize osMat s.cb s.co s.k = m at h hp ⊢
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, range7_map, List.map_cons, List.map_nil] at h
  obtain ⟨hcall, h7, h8, l6, h9, -⟩ := h
  obtain ⟨cv0, d0, d2, r, t, q, cv', hcv0, hrd, hrun, hret⟩ := (opening_fold_iff rd _ _).mp hcall
  have hcv : cv0 = cv := digestScalars_injective (hcv0.symm.trans hat.fs)
  subst hcv
  obtain ⟨hcl, hcv'⟩ := (runsTo_foldStep cv0 _ _ _ d0 d2).iff.mp hrun
  simp only [Prod.mk.injEq] at hcl
  obtain ⟨rfl, rfl, rfl⟩ := hcl
  subst hcv'
  simp only [List.cons.injEq] at hret
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, -⟩ := hret
  have hl0 : LoadHolds rd (σ (.n m.2.1)) 0 d0 := hrd 0 (by simp)
  have hl1 : LoadHolds rd (σ (.n m.2.1)) 1 d2 := hrd 1 (by simp)
  rw [hp, loadHolds_mul_gen_pow] at hl0 hl1
  refine ⟨d0, d2, ⟨?_, readsAt_append hat.reads fun j hj => ?_, ?_⟩, trivial, ?_, ?_⟩
  · show (σ (.n (m.2.2 + 7)), σ (.n (m.2.2 + 8))) = _
    rw [h7, h8, r0, r1]
  · simp only [List.length_cons, List.length_nil] at hj
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact hat.load (j := 0) (by simpa using hl0)
    · exact hat.load (j := 1) hl1
  · show σ (.n (m.2.2 + 2)) * gen ^ 0 = cur * gen ^ (xs ++ [d0, d2]).length
    rw [r2, hp, pow_zero, mul_one, List.length_append, mul_assoc, ← pow_add, pow_add, ← mul_assoc,
      hat.cursor, mul_assoc, ← pow_add]
    rfl
  · rw [r3, r4, h9, r3, r5]
    exact runsTo_foldStep cv0 _ _ _ d0 d2
  · rw [← r6]; exact l6

theorem osFold_noRet (s : OsSt) (fch fo : ℕ) : Stmt.noRetList (osFold s fch fo).1 = true := by
  unfold osFold
  simp only [noRetList_append, osMat_noRet, Bool.true_and]
  rfl

theorem osFolds_noRet (fch : ℕ) : ∀ fo n s, Stmt.noRetList (osFolds fch fo n s).1 = true
  | _, 0, _ => rfl
  | fo, n + 1, s => by
    simp only [osFolds, noRetList_append, osFold_noRet, osFolds_noRet fch (fo + 1) n, Bool.and_self]

/-- **The fold rounds** (G:1103-1108): `n` rounds of `osFold_sound` are `foldRounds n`
(V:1678), their challenges stored at `fch[fo ..]`. -/
theorem osFolds_sound {cur : E} {fch : ℕ} {kret : List E → Prop} :
    ∀ (n fo : ℕ) (s : OsSt) (cv : Digest) (xs : List E) (w : WhirState) (lf : List E),
      OsCur rd σ cur s cv xs → s.co < 2 ^ 128 → w.quad = [σ (.n s.c), σ (.n s.b), σ (.n s.a)] →
      w.target = σ (.n s.t) →
      Stmt.HoldsList (coreProgram.Rel rd) rd σ (osFolds fch fo n s).1 True kret →
      ∃ ys cv' chs w', OsCur rd σ cur (osFolds fch fo n s).2 cv' (xs ++ ys) ∧
        RunsTo (foldRounds n w lf) cv ys (w', lf ++ chs) cv' ∧ chs.length = n ∧
        w'.quad = [σ (.n (osFolds fch fo n s).2.c), σ (.n (osFolds fch fo n s).2.b),
          σ (.n (osFolds fch fo n s).2.a)] ∧ w'.target = σ (.n (osFolds fch fo n s).2.t) ∧
        w'.folds = w.folds ++ chs ∧ w'.glued = w.glued ∧
        (∀ j < n, LoadHolds rd (σ (.n fch)) (fo + j) (chs.getD j 0)) ∧
        (osFolds fch fo n s).2.co = if n = 0 then s.co else 0
  | 0, fo, s, cv, xs, w, lf, hat, _, hq, ht, _ =>
    ⟨[], cv, [], w, by simpa [osFolds] using hat, by simpa [foldRounds] using runsTo_ret (w, lf) cv,
      rfl, hq, ht, by simp, rfl, fun j hj => absurd hj (Nat.not_lt_zero j), by simp [osFolds]⟩
  | n + 1, fo, s, cv, xs, w, lf, hat, hco, hq, ht, h => by
    simp only [osFolds, holdsList_append] at h ⊢
    obtain ⟨h1, h⟩ := holdsList_true_of (osFold_noRet _ _ _) h
    obtain ⟨d0, d2, hat1, hco1, hrun1, hl1⟩ := osFold_sound hat hco h1
    let w1 : WhirState :=
      { target := σ (.n (osFold s fch fo).2.t)
        quad := [σ (.n (osFold s fch fo).2.c), σ (.n (osFold s fch fo).2.b),
          σ (.n (osFold s fch fo).2.a)]
        folds := w.folds ++ [challengeOf (sqCv cv)]
        glued := w.glued }
    have := osFolds_sound (fch := fch) (kret := kret) n (fo + 1) (osFold s fch fo).2 _ _ w1
      (lf ++ [challengeOf (sqCv cv)]) hat1 (by rw [hco1]; decide) rfl rfl h
    obtain ⟨ys, cv', chs, w', hat', hrun', hlen, hq', ht', hf', hg', hl', hco'⟩ := this
    refine ⟨[d0, d2] ++ ys, cv', challengeOf (sqCv cv) :: chs, w', by simpa using hat', ?_,
      by simp [hlen], hq', ht', by rw [hf']; simp [w1], hg', fun j hj => ?_, ?_⟩
    · rw [foldRounds_succ, hq]
      exact hrun1.bind (hrun'.of_eq rfl (by simp) rfl)
    · rcases j with _ | j
      · simpa using hl1
      · have := hl' j (by omega)
        rwa [show fo + 1 + j = fo + (j + 1) by ring] at this
    · rw [hco']
      split <;> simp_all

/-! ## The final message, the next commitment, the proof of work -/

/-- **The final message** (`opening_final_message`, G:1110-1112): the `n` words `ms` read at the
cursor, absorbed (`readN n`, V:1726), and stored at `final_msg`. -/
theorem osFinal_sound {name : String} {n : ℕ}
    (hfin : ∀ a r, coreProgram.Rel rd name a r → MeaningOpeningFinalMessage n rd a r)
    {cur : E} {s : OsSt} {cv : Digest} {xs : List E} (hat : OsCur rd σ cur s cv xs)
    (hco : s.co < 2 ^ 128) {fmsg : ℕ} {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ (osFinal name fmsg s).1 True kret) :
    ∃ ms : List E, ms.length = n ∧
      OsCur rd σ cur (osFinal name fmsg s).2 (obsAll cv ms) (xs ++ ms) ∧
      ReadsAt rd (σ (.n fmsg)) ms ∧ (osFinal name fmsg s).2.co = 0 := by
  unfold osFinal at h ⊢
  simp only at h ⊢
  rw [holdsList_append] at h
  obtain ⟨hm, h⟩ := holdsList_true_of (osMat_noRet _ _ _) h
  have hp := osMat_sound hco hm
  generalize osMat s.cb s.co s.k = m at h hp ⊢
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨hcall, h3, h4, -⟩ := h
  obtain ⟨cv0, ms, cv', hcv0, hlen, hrd, hout, hrun, hret⟩ := hfin _ _ hcall
  have hcv : cv0 = cv := digestScalars_injective (hcv0.symm.trans hat.fs)
  subst hcv
  have hc' : cv' = obsAll cv0 ms := ((runsTo_readN cv0 ms).unique (hlen ▸ hrun)).2.symm
  subst hc'
  simp only [List.cons.injEq] at hret
  obtain ⟨r0, r1, r2, -⟩ := hret
  refine ⟨ms, hlen, ⟨?_, readsAt_append hat.reads fun j hj => ?_, ?_⟩, hout, trivial⟩
  · show (σ (.n (m.2.2 + 3)), σ (.n (m.2.2 + 4))) = _
    rw [h3, h4, r0, r1]
  · have := hrd j hj
    rw [hp, loadHolds_mul_gen_pow] at this
    exact hat.load this
  · show σ (.n (m.2.2 + 2)) * gen ^ 0 = cur * gen ^ (xs ++ ms).length
    rw [r2, hp, pow_zero, mul_one, List.length_append, hlen, mul_assoc, ← pow_add, pow_add, ← mul_assoc,
      hat.cursor, mul_assoc, ← pow_add]

/-- **An out-of-domain sample** (G:1125-1135): its point, `sampleN logCols` (V:1732), stored at
`oodz·g^oz`; its value and its intro message's `c0, c2` read and stored at `ood[so + 1 ..]`. -/
theorem osOodSample_sound {cur : E} {s : OsSt} {cv : Digest} {xs : List E}
    (hat : OsCur rd σ cur s cv xs) {oz so logCols oodz ood : ℕ} (hoz : oz < 2 ^ 128)
    (hl0 : 0 < logCols) (hl1 : logCols < 2 ^ 63) {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ (osOodSample oz so logCols oodz ood s).1 True kret) :
    ∃ y c0 c2 : E, OsCur rd σ cur (osOodSample oz so logCols oodz ood s).2
        (obsCv (obsCv (obsCv (sqAll logCols cv).2 y) c0) c2) (xs ++ [y, c0, c2]) ∧
      ReadsAt rd (σ (.n oodz) * gen ^ oz) (sqAll logCols cv).1 ∧
      LoadHolds rd (σ (.n ood)) (so + 1) y ∧ LoadHolds rd (σ (.n ood)) (so + 2) c0 ∧
      LoadHolds rd (σ (.n ood)) (so + 3) c2 ∧
      (osOodSample oz so logCols oodz ood s).2.co = s.co + 3 := by
  unfold osOodSample at h ⊢
  simp only at h ⊢
  simp only [holdsList_append] at h
  obtain ⟨hpre, hr⟩ := holdsList_true_of (by rfl) h
  clear h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, and_true] at hpre
  obtain ⟨e0, e1, e2, hcall, e5, e6⟩ := hpre
  obtain ⟨m, hm, hng, p, hcase⟩ := (opening_ood_point_iff rd _ _).mp hcall
  rw [e2, os_gw_eq (by omega)] at hng
  have hmeq : m = logCols := gen_pow_inj hm (by omega) hng.symm
  subst hmeq
  rcases hcase with ⟨h0, -⟩ | ⟨-, cv0, rs, cv', hcv0, hrun, hrs, -, hret⟩
  · omega
  have hcv : cv0 = cv := digestScalars_injective (hcv0.symm.trans hat.fs)
  subst hcv
  obtain ⟨hrs', hcv'⟩ := (runsTo_sampleN m cv0).unique hrun
  subst hrs' hcv'
  simp only [List.cons.injEq] at hret
  obtain ⟨r0, r1, -⟩ := hret
  have hat1 : OsCur rd σ cur { s with k := s.k + 7, f0 := s.k + 5, f1 := s.k + 6 } (sqAll m cv0).2 xs :=
    ⟨by show (σ (.n (s.k + 5)), σ (.n (s.k + 6))) = _; rw [e5, e6, r0, r1], hat.reads, hat.cursor⟩
  obtain ⟨hy, h⟩ := holdsList_true_of (by rfl) hr
  have hat2 := osFsNext_sound hat1 hy
  obtain ⟨hc0, h⟩ := holdsList_true_of (by rfl) h
  have hat3 := osFsNext_sound hat2 hc0
  obtain ⟨hc2, h⟩ := holdsList_true_of (by rfl) h
  have hat4 := osFsNext_sound hat3 hc2
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
  obtain ⟨ly, lc0, lc2⟩ := h
  refine ⟨_, _, _, by simpa using hat4, ?_, ly, lc0, lc2, rfl⟩
  rw [e1, e0, os_gw_eq hoz] at hrs
  exact hrs

/-- **The next commitment** (G:1113-1135), with its one out-of-domain sample: the root's halves
read, absorbed (`commitP`, V:1730), canonical, stored at `level_roots[2lvl + 2 ..]`; then the
sample at `oodz·g^((lvl+1)·22)`, `ood[(lvl+1)·4 + 1 ..]`. -/
theorem osCommit_sound {lvl logCols roots oodz ood : ℕ} (hl0 : 0 < logCols) (hl1 : logCols < 2 ^ 63)
    (hlvl : (lvl + 1) * 22 < 2 ^ 128) {cur : E} {s : OsSt} {cv : Digest} {xs : List E}
    (hat : OsCur rd σ cur s cv xs) {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ (osCommit lvl logCols 1 roots oodz ood s).1 True kret) :
    ∃ x0 x1 y c0 c2 : E, IsCanonical128 x0 ∧ IsCanonical128 x1 ∧
      LoadHolds rd (σ (.n roots)) (2 * lvl + 2) x0 ∧ LoadHolds rd (σ (.n roots)) (2 * lvl + 3) x1 ∧
      OsCur rd σ cur (osCommit lvl logCols 1 roots oodz ood s).2
        (obsCv (obsCv (obsCv (sqAll logCols (obsCv (obsCv cv x0) x1)).2 y) c0) c2)
        (xs ++ [x0, x1, y, c0, c2]) ∧
      ReadsAt rd (σ (.n oodz) * gen ^ ((lvl + 1) * 22)) (sqAll logCols (obsCv (obsCv cv x0) x1)).1 ∧
      LoadHolds rd (σ (.n ood)) ((lvl + 1) * 4 + 1) y ∧ LoadHolds rd (σ (.n ood)) ((lvl + 1) * 4 + 2) c0 ∧
      LoadHolds rd (σ (.n ood)) ((lvl + 1) * 4 + 3) c2 ∧
      (osCommit lvl logCols 1 roots oodz ood s).2.co = s.co + 5 := by
  unfold osCommit at h ⊢
  simp only [osOods, List.append_nil] at h ⊢
  simp only [holdsList_append] at h
  obtain ⟨ha, h⟩ := holdsList_true_of (by rfl) h
  have hat1 := osFsNext_sound hat ha
  obtain ⟨hb, h⟩ := holdsList_true_of (by rfl) h
  have hat2 := osFsNext_sound hat1 hb
  obtain ⟨hc, h⟩ := holdsList_true_of (by rfl) h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, and_true] at hc
  obtain ⟨k0, k1, l0, l1⟩ := hc
  obtain ⟨hk0, -⟩ := (assert_canonical_iff rd _ _).mp k0
  obtain ⟨hk1, -⟩ := (assert_canonical_iff rd _ _).mp k1
  have hat3 : OsCur rd σ cur { (osFsNext (osFsNext s).2).2 with k := (osFsNext (osFsNext s).2).2.k + 2 }
      (obsCv (obsCv cv (σ (.n s.k))) (σ (.n (osFsNext s).2.k)))
      ((xs ++ [σ (.n s.k)]) ++ [σ (.n (osFsNext s).2.k)]) := ⟨hat2.fs, hat2.reads, hat2.cursor⟩
  obtain ⟨y, c0, c2, hat4, hrs, ly, lc0, lc2, hco⟩ :=
    osOodSample_sound hat3 (oz := (lvl + 1 + 0) * 22) (by simpa using hlvl) hl0 hl1 h
  refine ⟨_, _, y, c0, c2, hk0, hk1, l0, l1, by simpa using hat4, by simpa using hrs,
    by simpa using ly, by simpa using lc0, by simpa using lc2, ?_⟩
  rw [hco]; rfl

/-- **The query nonce** (G:1136-1142): the raw word at the cursor passes `grind_check` at
`bits ≠ 0` (`powOk`, V:482) and is absorbed at tag 4 (`grindP`, V:1736). -/
theorem osGrind_sound {bits : ℕ} (hb0 : bits ≠ 0) (hb : bits < 2 ^ 63) {cur : E} {s : OsSt}
    {cv : Digest} {xs : List E} (hat : OsCur rd σ cur s cv xs) {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ (osGrind bits s).1 True kret) :
    ∃ n, OsCur rd σ cur (osGrind bits s).2 (absorbCv cv n 4) (xs ++ [n]) ∧
      powOk bits n (gcDigest cv n) = true ∧ (osGrind bits s).2.co = s.co + 1 := by
  unfold osGrind at h ⊢
  simp only [hb0, ↓reduceIte] at h ⊢
  simp only [holdsList_append] at h
  obtain ⟨hp, h⟩ := holdsList_true_of (by rfl) h
  obtain ⟨hq, h⟩ := holdsList_true_of (by rfl) h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, List.map_cons, List.map_nil] at hp hq
  have ln := hp
  obtain ⟨e1, hcall⟩ := hq
  obtain ⟨-, m, hm, hng, cv0, hcv0, hpow, -⟩ := (grind_check_iff rd _ _).mp hcall
  rw [e1, os_gw_eq (by omega)] at hng
  have hmeq : m = bits := gen_pow_inj hm (by omega) hng.symm
  have hcv : cv0 = cv := digestScalars_injective (hcv0.symm.trans hat.fs)
  rw [hmeq, hcv] at hpow
  obtain ⟨⟨cv1, hcv1, e⟩, -⟩ := (holds_fsCompressT _ _ _ _ (tag := 4) (by decide) _ _).mp h
  have hc1 : cv1 = cv := digestScalars_injective (hcv1.symm.trans hat.fs)
  subst hc1
  refine ⟨σ (.n s.k), ⟨?_, readsAt_append hat.reads fun j hj => ?_, ?_⟩, hpow, trivial⟩
  · show (σ (.n (s.k + 14)), σ (.n (s.k + 15))) = _
    rw [show s.k + 14 = s.k + 2 + 12 by ring, show s.k + 15 = s.k + 2 + 13 by ring,
      e 12 (by omega) (by omega), e 13 (by omega) (by omega)]
    rfl
  · simp only [List.length_cons, List.length_nil] at hj
    obtain rfl : j = 0 := by omega
    exact hat.load (j := 0) (by simpa using ln)
  · show σ (.n s.cb) * gen ^ (s.co + 1) = cur * gen ^ (xs ++ [σ (.n s.k)]).length
    rw [List.length_append, List.length_singleton, pow_succ, pow_succ, ← mul_assoc, ← mul_assoc,
      hat.cursor]

/-! ## The query weights and the glue -/

/-- **The query weights** (G:1167-1170): `qw[base + i] = lam^i`, `i < nq`. -/
theorem osLamPows_sound {lam qw base k : ℕ} {kret : List E → Prop} :
    ∀ nq, Stmt.HoldsList C rd σ (osLamPows lam qw base k nq) True kret →
      ∀ i < nq, LoadHolds rd (σ (.n qw)) (base + i) (σ (.n lam) ^ i)
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | nq + 1, h, i, hi => by
    unfold osLamPows at h
    by_cases h0 : nq = 0
    · subst h0
      obtain rfl : i = 0 := by omega
      simp only [↓reduceIte, List.append_nil, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_one] at h
      rw [Nat.add_zero, pow_zero, ← h.1]
      exact h.2.1
    · simp only [h0, ↓reduceIte] at h
      rw [holdsList_append, holdsList_append] at h
      obtain ⟨h1, h⟩ := holdsList_true_of (by rfl) h
      obtain ⟨h2, h⟩ := holdsList_true_of (by rfl) h
      rw [holdsList_range_flatten _ _ (fun _ => rfl)] at h
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_one, and_true] at h1 h2
      have hpow : ∀ j < nq - 1, σ (.n (k + 1 + j)) = σ (.n lam) ^ (j + 2) ∧
          LoadHolds rd (σ (.n qw)) (base + 2 + j) (σ (.n (k + 1 + j))) := by
        intro j hj
        induction j with
        | zero =>
          have := (h.1 0 (by omega))
          simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
          refine ⟨by rw [Nat.add_zero, h2.2, sq], by simpa using this.1⟩
        | succ j ih =>
          have := (h.1 (j + 1) (by omega))
          have hp := (h.1 j (by omega))
          simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this hp
          refine ⟨?_, by simpa [Nat.add_assoc] using this.1⟩
          rw [show k + 1 + (j + 1) = k + 2 + j by ring, hp.2, (ih (by omega)).1]; ring
      rcases i with _ | _ | i
      · rw [Nat.add_zero, pow_zero, ← h1.1]; exact h1.2
      · rw [pow_one]; exact h2.1
      · have := (hpow i (by omega))
        rw [this.1] at this
        rw [show base + (i + 2) = base + 2 + i by ring]
        exact this.2

/-- **The glue of one claim** (G:1210-1213): the running quadratic and claim plus `sc` times the
claim's intro and value. -/
theorem osGlue_sound {sc v c0 c1 c2 : ℕ} {s : OsSt} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (osGlue sc v c0 c1 c2 s).1 True kret) :
    σ (.n (osGlue sc v c0 c1 c2 s).2.c) = σ (.n s.c) + σ (.n sc) * σ (.n c0) ∧
      σ (.n (osGlue sc v c0 c1 c2 s).2.b) = σ (.n s.b) + σ (.n sc) * σ (.n c1) ∧
      σ (.n (osGlue sc v c0 c1 c2 s).2.a) = σ (.n s.a) + σ (.n sc) * σ (.n c2) ∧
      σ (.n (osGlue sc v c0 c1 c2 s).2.t) = σ (.n s.t) + σ (.n sc) * σ (.n v) := by
  simp only [osGlue, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h ⊢
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := h
  exact ⟨by rw [e1, e0], by rw [e3, e2], by rw [e5, e4], by rw [e7, e6]⟩

/-- **The out-of-domain claim's glue** (G:1199-1207): its value `y` and intro `c0, c2` reread
from `ood[so + 1 ..]`, the scalar `sc` stored at `ood[so]`, the running sums updated; the next
scalar `sc·lam` at the returned `OsSt.k - 1`. -/
theorem osOodGlue_sound {so sc lam : ℕ} {s : OsSt} {y c0 c2 : E}
    (hy : LoadHolds rd (σ (.n osOod)) (so + 1) y) (hc0 : LoadHolds rd (σ (.n osOod)) (so + 2) c0)
    (hc2 : LoadHolds rd (σ (.n osOod)) (so + 3) c2) {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (osOodGlue so sc lam s).1 True kret) :
    LoadHolds rd (σ (.n osOod)) so (σ (.n sc)) ∧
      σ (.n (osOodGlue so sc lam s).2.c) = σ (.n s.c) + σ (.n sc) * c0 ∧
      σ (.n (osOodGlue so sc lam s).2.b) = σ (.n s.b) + σ (.n sc) * (y + c2) ∧
      σ (.n (osOodGlue so sc lam s).2.a) = σ (.n s.a) + σ (.n sc) * c2 ∧
      σ (.n (osOodGlue so sc lam s).2.t) = σ (.n s.t) + σ (.n sc) * y ∧
      σ (.n ((osOodGlue so sc lam s).2.k - 1)) = σ (.n sc) * σ (.n lam) := by
  simp only [osOodGlue, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h ⊢
  obtain ⟨l0, l1, ls, l2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := h
  have v0 := loadHolds_unique l0 hy
  have v1 := loadHolds_unique l1 hc2
  have v2 := loadHolds_unique l2 hc0
  refine ⟨ls, by rw [e4, e3, v2], by rw [e7, e6, e5, v0, v1], by rw [e9, e8, v1], by rw [e11, e10, v0],
    by rw [show s.k + 13 - 1 = s.k + 12 by omega, e12]⟩

end
end LeanVM.Guest.B1
