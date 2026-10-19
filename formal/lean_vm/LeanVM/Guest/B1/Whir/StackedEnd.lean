/-
  LeanVM.Guest.B1.Whir.StackedEnd

  The end of `open_stacked`: the tail rounds, the residual's value, the rotated point.
-/

module

public import LeanVM.Guest.B1.Whir.StackedLevels

/-!
# The tail of the stacked opening (TRIAGE #36)

* the tail rounds (`osTail`, G:1216-1228) against `tailRounds` (V:1689);
* `fold_final_msg` of the final message at the tail challenges (`multilinearEval`, V:687);
* the point (`osPoint`, G:1240-1247): the fold challenges past the lane folds, the tail
  challenges, the lane folds, then zeros, which is `point.drop laneFolds ++ point.take laneFolds`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {rd : Reader} {σ : Val} {C : CallRel}

/-! ## The tail rounds -/

private theorem tailRounds_succ_succ (n : ℕ) (t : E) (q : List E) :
    tailRounds (n + 2) t q = (do
      let (c, target, quad) ← foldStep q
      let (rest, t') ← tailRounds (n + 1) target quad
      return (c :: rest, t')) := by
  simp only [tailRounds, foldStep, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind,
    Nat.add_one_ne_zero, ↓reduceIte]

private theorem tailRounds_one (t : E) (q : List E) :
    tailRounds 1 t q = (do let c ← Prog.sampleE; return ([c], polyEval q c)) := by
  simp only [tailRounds, Prog.bind_eq, Prog.pure_eq, ↓reduceIte]

/-- **The tail's folds** (G:1217-1222): `n` rounds of `osFold_sound`, whose challenges are stored
at `fch[fo ..]`; any run of `tailRounds 1` from where they end extends to `tailRounds (n + 1)`
from where they start. -/
theorem osTailFolds_sound {cur : E} {fch : ℕ} {kret : List E → Prop} :
    ∀ (n fo : ℕ) (s : OsSt) (cv : Digest) (xs : List E),
      OsCur rd σ cur s cv xs → s.co < 2 ^ 128 →
      Stmt.HoldsList (coreProgram.Rel rd) rd σ (osFolds fch fo n s).1 True kret →
      ∃ ys cv' chs, OsCur rd σ cur (osFolds fch fo n s).2 cv' (xs ++ ys) ∧ chs.length = n ∧
        (∀ j < n, LoadHolds rd (σ (.n fch)) (fo + j) (chs.getD j 0)) ∧
        (osFolds fch fo n s).2.co = (if n = 0 then s.co else 0) ∧
        ∀ (L : List E) (T : E) (cv'' : Digest) (t : E),
          RunsTo (tailRounds 1 (σ (.n (osFolds fch fo n s).2.t))
            [σ (.n (osFolds fch fo n s).2.c), σ (.n (osFolds fch fo n s).2.b),
              σ (.n (osFolds fch fo n s).2.a)]) cv' [] (L, T) cv'' →
          RunsTo (tailRounds (n + 1) t [σ (.n s.c), σ (.n s.b), σ (.n s.a)]) cv ys (chs ++ L, T) cv''
  | 0, fo, s, cv, xs, hat, _, _ =>
    ⟨[], cv, [], by simpa [osFolds] using hat, rfl, fun j hj => absurd hj (Nat.not_lt_zero j),
      by simp [osFolds], fun L T cv'' t h => by simpa [osFolds, tailRounds] using h⟩
  | n + 1, fo, s, cv, xs, hat, hco, h => by
    simp only [osFolds, holdsList_append] at h ⊢
    obtain ⟨h1, h⟩ := holdsList_true_of (osFold_noRet _ _ _) h
    obtain ⟨d0, d2, hat1, hco1, hrun1, hl1⟩ := osFold_sound hat hco h1
    obtain ⟨ys, cv', chs, hat', hlen, hl', hco', hrun'⟩ :=
      osTailFolds_sound n (fo + 1) (osFold s fch fo).2 _ _ hat1 (by rw [hco1]; decide) h
    refine ⟨[d0, d2] ++ ys, cv', challengeOf (sqCv cv) :: chs, by simpa using hat', by simp [hlen],
      fun j hj => ?_, by rw [hco']; split <;> simp_all, fun L T cv'' t hT => ?_⟩
    · rcases j with _ | j
      · simpa using hl1
      · have := hl' j (by omega)
        rwa [show fo + 1 + j = fo + (j + 1) by ring] at this
    · have := hrun' L T cv'' (σ (.n (osFold s fch fo).2.t)) hT
      rw [tailRounds_succ_succ]
      exact RunsTo.of_eq (RunsTo.bind hrun1 (RunsTo.bind this (runsTo_ret _ _))) (by simp) rfl rfl

theorem os_readsAt_unique {p : E} {a b : List E} (ha : ReadsAt rd p a) (hb : ReadsAt rd p b)
    (hl : a.length = b.length) : a = b :=
  List.ext_getElem hl fun k h1 h2 => loadHolds_unique (ha k h1) (hb k h2)

theorem os_readsAt_prefix {p : E} {a b : List E} (h : ReadsAt rd p (a ++ b)) : ReadsAt rd p a :=
  fun k hk => by
    have := h k (by simp; omega)
    rwa [List.getElem_append_left hk] at this

private theorem readsAt_of_getD {p : E} {l : List E} (h : ∀ k < l.length, LoadHolds rd p k (l.getD k 0)) :
    ReadsAt rd p l := fun k hk => by
  have := h k hk
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at this

theorem os_getD_append_lt {l l' : List E} {n : ℕ} (h : n < l.length) : (l ++ l').getD n 0 = l.getD n 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem os_getD_append_ge {l l' : List E} {n : ℕ} (h : l.length ≤ n) :
    (l ++ l').getD n 0 = l'.getD (n - l.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

private theorem polyEval_three (c b a x : E) : polyEval [c, b, a] x = c + x * b + x * x * a := by
  simp only [polyEval, List.foldr]; ring

/-- **The tail rounds** (G:1216-1228): `tailRounds yrLog` (V:1689) over the words the guest
reads, its challenges at `tail_challenges` followed by zeros up to `YR_LOG_CAP = 5`, its final
claim at the returned state's `t`. -/
theorem osTail_sound {yrLog : ℕ} (hy : 2 ≤ yrLog) (hy5 : yrLog ≤ 5) {cur : E} {s : OsSt} {cv : Digest}
    {xs : List E} (hat : OsCur rd σ cur s cv xs) (hco : s.co ≤ 8) {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ (osTail yrLog s).1 True kret) :
    ∃ (ys tailFolds : List E) (cv' : Digest), tailFolds.length = yrLog ∧ ReadsAt rd cur (xs ++ ys) ∧
      (∀ t, RunsTo (tailRounds yrLog t [σ (.n s.c), σ (.n s.b), σ (.n s.a)]) cv ys
        (tailFolds, σ (.n (osTail yrLog s).2.1.t)) cv') ∧
      ReadsAt rd (σ (.n (osTail yrLog s).2.2.1)) (tailFolds ++ List.replicate (5 - yrLog) 0) := by
  unfold osTail at h ⊢
  simp only at h ⊢
  simp only [holdsList_append] at h
  obtain ⟨-, h⟩ := holdsList_true_of (by rfl) h
  obtain ⟨hF, h⟩ := holdsList_true_of (osFolds_noRet _ _ _ _) h
  have hat0 : OsCur rd σ cur { s with k := s.k + 2 } cv xs := ⟨hat.fs, hat.reads, hat.cursor⟩
  obtain ⟨ys, cv', chs, hat', hlen, hst, -, hcont⟩ :=
    osTailFolds_sound (yrLog - 1) 0 _ cv xs hat0 (by simp; omega) hF
  generalize osFolds (s.k + 1) 0 (yrLog - 1) { s with k := s.k + 2 } = fr at *
  obtain ⟨hS, h⟩ := holdsList_true_of (by rfl) h
  obtain ⟨hA, h⟩ := holdsList_true_of (by rfl) h
  rw [holdsList_range_flatten _ _ (fun _ => rfl)] at h
  obtain ⟨hZ, -⟩ := h
  obtain ⟨⟨cv0, hcv0, hv⟩, -⟩ := (holds_squeezeT _ _ _ True _).mp (by simpa using hS)
  have hc0 : cv0 = cv' := digestScalars_injective (hcv0.symm.trans hat'.fs)
  subst hc0
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hA
  obtain ⟨llast, a1, a2, a3, a4, a5⟩ := hA
  have hlast : σ (.n (fr.2.k + 13)) = challengeOf (sqCv cv0) := hv 13 (by omega)
  refine ⟨ys, chs ++ [challengeOf (sqCv cv0)], sqCv cv0, by simp [hlen]; omega, hat'.reads,
    fun t => ?_, readsAt_of_getD fun j hj => ?_⟩
  · have h1 : RunsTo (tailRounds 1 (σ (.n fr.2.t)) [σ (.n fr.2.c), σ (.n fr.2.b), σ (.n fr.2.a)]) cv0 []
        ([challengeOf (sqCv cv0)], σ (.n (fr.2.k + 14 + 4))) (sqCv cv0) := by
      rw [tailRounds_one, a5, a4, a3, a2, a1, hlast]
      refine RunsTo.of_eq (RunsTo.bind (runsTo_sampleE cv0) (runsTo_ret _ _)) rfl ?_ rfl
      rw [polyEval_three]
    have := hcont _ _ _ t h1
    rwa [show yrLog - 1 + 1 = yrLog by omega] at this
  · simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate] at hj
    rcases Nat.lt_or_ge j (yrLog - 1) with h1 | h1
    · rw [os_getD_append_lt (by simp; omega), os_getD_append_lt (by omega)]
      simpa using hst j h1
    · rcases Nat.lt_or_ge j yrLog with h2 | h2
      · obtain rfl : j = yrLog - 1 := by omega
        rw [os_getD_append_lt (by simp; omega), os_getD_append_ge (by omega), hlen, Nat.sub_self]
        simp only [List.getD_cons_zero]
        rw [← hlast]; exact llast
      · rw [os_getD_append_ge (by simp; omega)]
        simp only [List.length_append, List.length_cons, List.length_nil, hlen]
        rw [show yrLog - 1 + (0 + 1) = yrLog by omega, List.getD_eq_getElem?_getD,
          List.getElem?_replicate, ite_pos' (by omega)]
        have := hZ (j - yrLog) (by omega)
        simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
        rw [show yrLog + (j - yrLog) = j by omega, this.1, word_zero] at this
        exact this.2

/-! ## The point -/

theorem os_getD_drop' (l : List E) (n i : ℕ) : (l.drop n).getD i 0 = l.getD (n + i) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem os_getD_take' {l : List E} {n i : ℕ} (h : i < n) : (l.take n).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, h]

/-- **The rotated point** (G:1240-1247): with the fold challenges `P` at `fch` and the tail
challenges `T` at `tch`, the point buffer holds `(P ++ T).drop lane ++ (P ++ T).take lane`, then
zeros up to `42`. -/
theorem osPoint_sound {nFolds lane yrLog tch k : ℕ} (hlane : lane ≤ nFolds) (h42 : nFolds + yrLog ≤ 42)
    {P T : List E} (hP : P.length = nFolds) (hT : T.length = yrLog)
    (hfch : ∀ j < nFolds, LoadHolds rd (σ (.n osFch)) j (P.getD j 0))
    (htch : ∀ j < yrLog, LoadHolds rd (σ (.n tch)) j (T.getD j 0)) {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (osPoint nFolds lane yrLog tch k) True kret) :
    ReadsAt rd (σ (.n k)) (((P ++ T).drop lane ++ (P ++ T).take lane) ++
      List.replicate (42 - (nFolds + yrLog)) 0) := by
  unfold osPoint at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and] at h
  rw [holdsList_range_flatten _ _ (fun i => by unfold osPtBlk; split <;> rfl)] at h
  obtain ⟨hb, -⟩ := h
  have hlen : (P ++ T).length = nFolds + yrLog := by simp [hP, hT]
  refine readsAt_of_getD fun i hi => ?_
  simp only [List.length_append, List.length_drop, List.length_take, List.length_replicate, hlen] at hi
  have hbi := hb i (by omega)
  unfold osPtBlk osPtSrc at hbi
  by_cases c1 : i < nFolds - lane
  · simp only [c1, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hbi
    rw [os_getD_append_lt (by simp [hlen]; omega), os_getD_append_lt (by simp [hlen]; omega), os_getD_drop',
      os_getD_append_lt (by omega), ← loadHolds_unique hbi.1 (hfch _ (by omega))]
    exact hbi.2
  · by_cases c2 : i < nFolds - lane + yrLog
    · simp only [c1, c2, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hbi
      rw [os_getD_append_lt (by simp [hlen]; omega), os_getD_append_lt (by simp [hlen]; omega), os_getD_drop',
        os_getD_append_ge (by omega), hP, show lane + i - nFolds = i - (nFolds - lane) by omega,
        ← loadHolds_unique hbi.1 (htch _ (by omega))]
      exact hbi.2
    · by_cases c3 : i < nFolds + yrLog
      · simp only [c1, c2, c3, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hbi
        rw [os_getD_append_lt (by simp [hlen]; omega), os_getD_append_ge (by simp [hlen]; omega),
          List.length_drop, hlen, os_getD_take' (by omega), os_getD_append_lt (by omega),
          show i - (nFolds + yrLog - lane) = i - (nFolds - lane) - yrLog by omega,
          ← loadHolds_unique hbi.1 (hfch _ (by omega))]
        exact hbi.2
      · simp only [c1, c2, c3, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true,
          word_zero] at hbi
        rw [os_getD_append_ge (by simp [hlen]; omega), List.getD_eq_getElem?_getD, List.getElem?_replicate,
          ite_pos' (by simp [hlen]; omega), Option.getD_some, ← hbi.1]
        exact hbi.2

/-! ## The basis rows and the residual chains -/

/-- A basis coordinate `(slot, source, inverse)` (G:1262-1269): the challenge `c` at its source,
`1 + c` at `basis_a[slot]`, `c·inverse` at `basis_b[slot]`. -/
def OsBasisOk (rd : Reader) (σ : Val) (ba bb : ℕ) (it : ℕ × (ℕ × ℕ) × ℕ) : Prop :=
  ∃ c, LoadHolds rd (σ (.n it.2.1.1)) it.2.1.2 c ∧ LoadHolds rd (σ (.n ba)) it.1 (1 + c) ∧
    LoadHolds rd (σ (.n bb)) it.1 (c * eOfNat it.2.2)

theorem osBasisRow_sound {ba bb : ℕ} {kret : List E → Prop} :
    ∀ (items : List (ℕ × (ℕ × ℕ) × ℕ)) (k : ℕ),
      Stmt.HoldsList C rd σ (osBasisRow ba bb items k).1 True kret →
      ∀ it ∈ items, OsBasisOk rd σ ba bb it
  | [], _, _, it, hit => absurd hit (by simp)
  | (slot, src, inv) :: rest, k, h, it, hit => by
    simp only [osBasisRow, holdsList_append] at h
    have hnr : Stmt.noRetList (osBasisBlk ba bb slot src inv k).1 = true := by
      unfold osBasisBlk; split <;> rfl
    obtain ⟨h1, h2⟩ := holdsList_true_of hnr h
    rcases List.mem_cons.mp hit with rfl | hr
    · unfold osBasisBlk at h1
      by_cases hi : inv = 1
      · simp only [hi, ↓reduceIte, List.cons_append, List.nil_append, Stmt.HoldsList,
          Stmt.Holds, Atom.Holds, and_true, word_one] at h1
        obtain ⟨l0, e1, e2, l2, l3⟩ := h1
        refine ⟨σ (.n k), l0, by convert l2 using 1; rw [e2, e1], ?_⟩
        convert l3 using 1; rw [hi, eOfNat_one, mul_one]
      · simp only [hi, ↓reduceIte, List.cons_append, List.nil_append, Stmt.HoldsList,
          Stmt.Holds, Atom.Holds, and_true, word_eOfNat] at h1
        obtain ⟨l0, e1, e2, l2, e3, e4, l4⟩ := h1
        refine ⟨σ (.n k), l0, by convert l2 using 1; rw [e2, e1, eOfNat_one], ?_⟩
        convert l4 using 1; rw [e4, e3]
    · exact osBasisRow_sound rest _ h2 it hr

theorem osBases_sound {yrLog tch ba bb : ℕ} {kret : List E → Prop} :
    ∀ (lvl : ℕ) (lvs : List OsLvl) (k : ℕ),
      Stmt.HoldsList C rd σ (osBases yrLog tch ba bb lvl lvs k).1 True kret →
      ∀ i < lvs.length, ∀ it ∈ osBasisCoords yrLog tch (lvl + i) (lvs.getD i default),
        OsBasisOk rd σ ba bb it
  | _, [], _, _, i, hi => absurd hi (by simp)
  | lvl, lv :: rest, k, h, i, hi => by
    simp only [osBases, holdsList_append] at h
    have hnr : ∀ items k', Stmt.noRetList (osBasisRow ba bb items k').1 = true := by
      intro items
      induction items with
      | nil => intro; rfl
      | cons it rest ih =>
        intro k'
        obtain ⟨slot, src, inv⟩ := it
        simp only [osBasisRow, noRetList_append, ih, Bool.and_true]
        unfold osBasisBlk; split <;> rfl
    obtain ⟨h1, h2⟩ := holdsList_true_of (hnr _ _) h
    rcases i with _ | i
    · simpa using osBasisRow_sound _ _ h1
    · have := osBases_sound (lvl + 1) rest _ h2 i (by simpa using hi)
      simpa [show lvl + 1 + i = lvl + (i + 1) by ring] using this

/-- **A level's residual chain** (G:1276-1296): the loop's queries from `chain[0] = 0`, and
`inner[lvl + 1] = inner[lvl] + beta[lvl]·chain[n]`. -/
theorem osResidual_sound {maxQ ich ba bb lvl k : ℕ} {lv : OsLvl} {fn : Fn}
    (hfind : coreProgram.find? lv.resLoop = some fn)
    (hp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hb : fn.body = resLoopBody lv.posOff (lvl * 22) lv.logCols (lvl * maxQ) lv.vals lv.resLoop)
    (hc : 1 ≤ lv.logCols) (hnq : lv.queries < 2 ^ 62) {kret : List E → Prop}
    (hC : ∀ a, a.length = 7 → C lv.resLoop a [] → coreProgram.Rel rd lv.resLoop a [])
    (h : Stmt.HoldsList C rd σ (osResidual maxQ ich ba bb lvl lv k) True kret) :
    ∃ rc : E, (∀ x < lv.queries, ResBody rd lv.posOff (lvl * 22) lv.logCols (lvl * maxQ) lv.vals
        (σ (.n osQpos)) (σ (.n ba)) (σ (.n bb)) rc (σ (.n osQw)) (gen ^ x)) ∧ LoadHolds rd rc 0 0 ∧
      ∃ i0 b r, LoadHolds rd (σ (.n ich)) lvl i0 ∧ LoadHolds rd (σ (.n osBetas)) lvl b ∧
        LoadHolds rd rc lv.queries r ∧ LoadHolds rd (σ (.n ich)) (lvl + 1) (i0 + b * r) := by
  unfold osResidual osHeap at h
  simp only [List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    List.map_cons, List.map_nil, and_true, word_zero, word_one] at h
  obtain ⟨-, -, e2, l2, e3, e4, e5, e6, e7, hK, hrun, l8, l9, l10, e11, e12, l12⟩ := h
  rw [e5, e3, e4, os_gw_eq (by omega)] at hrun
  rw [e6, e7, os_gw_eq (by omega)] at hrun
  replace hrun := fun hne => hC _ rfl (hrun hne)
  obtain ⟨m, hm, hN, hB⟩ := guarded_loop_sound (P := coreProgram) (f := lv.resLoop)
    (ps := [gen ^ lv.queries, σ (.n osQpos), σ (.n ba), σ (.n bb), σ (.n (k + 1)), σ (.n osQw)])
    (fun d x hx => resLoop_step hfind hp hb hc hx) hrun
  have hmn : m = lv.queries := gen_pow_inj hm (by omega) hN.symm
  subst hmn
  refine ⟨σ (.n (k + 1)), hB, by rw [← e2]; exact l2, _, _, _, l8, l9, l10, ?_⟩
  rw [← e11, ← e12]; exact l12

/-! ## The out-of-domain weights -/

theorem os_zipIdx_map_range {α : Type} (f : ℕ → α) (n : ℕ) :
    ((List.range n).map f).zipIdx = (List.range n).map fun j => (f j, j) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem_zipIdx]

/-- The source of coordinate `t` of an out-of-domain weight: the fold challenges after `ris`,
then the tail challenges. -/
def osOodSrc (tch zf ris t : ℕ) : ℕ × ℕ := if t < zf then (osFch, ris + t) else (tch, t - zf)

/-- **An out-of-domain weight** (G:1302-1310): its scalar at `ood[ol·4]` times
`∏ (1 + z_t + c_t)` over its point at `oodz[ol·22 ..]` and the terminal point's coordinates. -/
theorem osOodWeight_sound {yrLog tch zf ris ol k : ℕ} (hn : 0 < zf + yrLog) {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (osOodWeight yrLog tch zf ris ol 0 k) True kret)
    {sc : E} {z c : ℕ → E} (hsc : LoadHolds rd (σ (.n osOod)) (ol * 4) sc)
    (hz : ∀ t < zf + yrLog, LoadHolds rd (σ (.n osOodz)) (ol * 22 + t) (z t))
    (hc : ∀ t < zf + yrLog, LoadHolds rd (σ (.n (osOodSrc tch zf ris t).1)) (osOodSrc tch zf ris t).2 (c t)) :
    σ (.n (k + 6 * (zf + yrLog))) = sc * ∏ t ∈ Finset.range (zf + yrLog), (1 + z t + c t) := by
  unfold osOodWeight osOodFacs at h
  rw [os_zipIdx_map_range, List.map_map] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, Nat.zero_mul, Nat.add_zero] at h
  obtain ⟨l0, h⟩ := h
  rw [holdsList_range_flatten _ _ (fun _ => rfl)] at h
  obtain ⟨hb, -⟩ := h
  have hs0 := loadHolds_unique l0 hsc
  have key : ∀ j < zf + yrLog, σ (.n (k + 6 * (j + 1))) =
      sc * ∏ t ∈ Finset.range (j + 1), (1 + z t + c t) := by
    intro j hj
    induction j with
    | zero =>
      have := hb 0 (by omega)
      simp only [Function.comp, osOodFac, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true,
        word_one, ↓reduceIte] at this
      obtain ⟨e0, l1, e2, l3, e4, e5⟩ := this
      simp only [Nat.mul_zero, Nat.add_zero] at l1 l3
      rw [show k + 6 * (0 + 1) = k + 1 + 6 * 0 + 5 by ring]
      simp only [Nat.mul_zero, Nat.add_zero] at e0 e2 e4 e5 ⊢
      rw [e5, e4, e2, e0, hs0, loadHolds_unique l1 (hz 0 hj), loadHolds_unique l3 (by
        have := hc 0 hj; simpa [osOodSrc] using this)]
      simp
    | succ j ih =>
      have := hb (j + 1) (by omega)
      simp only [Function.comp, osOodFac, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true,
        word_one, Nat.add_one_ne_zero, ↓reduceIte] at this
      obtain ⟨e0, l1, e2, l3, e4, e5⟩ := this
      rw [show k + 6 * (j + 1 + 1) = k + 1 + 6 * (j + 1) + 5 by ring, e5, e4, e2, e0,
        show k + 1 + 6 * (j + 1) - 1 = k + 6 * (j + 1) by omega, ih (by omega), Finset.prod_range_succ _ (j + 1),
        loadHolds_unique l1 (hz _ hj), loadHolds_unique l3 (hc _ hj)]
      ring
  have := key (zf + yrLog - 1) (by omega)
  rwa [show zf + yrLog - 1 + 1 = zf + yrLog by omega] at this

/-- The running sum's value, `0` before the first weight. -/
def osAccVal (σ : Val) : Option ℕ → E
  | none => 0
  | some a => σ (.n a)

/-- The message log before level `i` of `lvs`, `prev` before the first. -/
def osPrevColsAt (lvs : List OsLvl) (prev i : ℕ) : ℕ := if i = 0 then prev else (lvs.getD (i - 1) default).logCols

private theorem prevColsAt_cons (lv : OsLvl) (rest : List OsLvl) (prev i : ℕ) :
    osPrevColsAt (lv :: rest) prev (i + 1) = osPrevColsAt rest lv.logCols i := by
  cases i <;> simp [osPrevColsAt]

/-- **The out-of-domain weights** (G:1298-1310) of the levels `lvs`, one sample each, summed into
the running sum `acc`, each weight `W i` as `osOodWeight_sound` gives it. -/
theorem osOodWeights_sound {yrLog tch : ℕ} {kret : List E → Prop} :
    ∀ (lvs : List OsLvl) (ol prev : ℕ) (acc : Option ℕ) (k : ℕ) (W : ℕ → E),
      (∀ lv ∈ lvs, lv.oodHere = 1) →
      (∀ i < lvs.length, ∀ k', Stmt.HoldsList C rd σ
          (osOodWeight yrLog tch (osPrevColsAt lvs prev i - yrLog) (lvs.getD i default).foldsOff (ol + i) 0 k')
          True kret →
        σ (.n (k' + 6 * (osPrevColsAt lvs prev i - yrLog + yrLog))) = W i) →
      Stmt.HoldsList C rd σ (osOodWeights yrLog tch prev ol lvs acc k).1 True kret →
      osAccVal σ (osOodWeights yrLog tch prev ol lvs acc k).2.1 =
        osAccVal σ acc + ∑ i ∈ Finset.range lvs.length, W i
  | [], _, _, acc, _, _, _, _, _ => by simp [osOodWeights]
  | lv :: rest, ol, prev, acc, k, W, hood, hW, h => by
    have h1 : lv.oodHere = 1 := hood lv (by simp)
    have hW0 := hW 0 (by simp)
    simp only [osPrevColsAt, ↓reduceIte, List.getD_cons_zero, Nat.add_zero] at hW0
    simp only [osOodWeights, h1, List.range_one, List.foldl_cons, List.foldl_nil] at h ⊢
    have hnr : ∀ k', Stmt.noRetList (osOodWeight yrLog tch (prev - yrLog) lv.foldsOff ol 0 k') = true := by
      intro k'
      unfold osOodWeight osOodFacs
      rw [os_zipIdx_map_range, List.map_map]
      show Stmt.noRetList (List.flatten _) = true
      rw [noRetList_flatten_range _ _ (fun _ => rfl)]
    have hrest := fun acc' k' => osOodWeights_sound (yrLog := yrLog) (tch := tch) (kret := kret) rest
      (ol + 1) lv.logCols acc' k' (fun i => W (i + 1))
      (fun lv' h' => hood lv' (by simp [h'])) (fun i hi k' hk => by
        have := hW (i + 1) (by simp; omega) k'
        rw [prevColsAt_cons, List.getD_cons_succ, show ol + (i + 1) = ol + 1 + i by ring] at this
        exact this hk)
    cases acc with
    | none =>
      simp only [List.nil_append, holdsList_append] at h ⊢
      obtain ⟨hw, h⟩ := holdsList_true_of (hnr k) h
      rw [hrest _ _ h, List.length_cons, Finset.sum_range_succ']
      simp only [osAccVal, zero_add]
      rw [hW0 k hw, add_comm]
    | some a =>
      simp only [List.nil_append, holdsList_append] at h ⊢
      obtain ⟨hw, h⟩ := holdsList_true_of (hnr k) h
      obtain ⟨hadd, h⟩ := holdsList_true_of (by rfl) h
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hadd
      rw [hrest _ _ h, List.length_cons, Finset.sum_range_succ']
      simp only [osAccVal]
      rw [hadd, hW0 k hw]
      ring

end
end LeanVM.Guest.B1
