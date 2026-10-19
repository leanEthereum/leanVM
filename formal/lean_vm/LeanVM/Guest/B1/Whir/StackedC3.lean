/-
  LeanVM.Guest.B1.Whir.StackedC3

  The completeness of `open_stacked`'s level blocks after the proof of work: the squeezes, the
  query weights, the queries, the glue.
-/

module

public import LeanVM.Guest.B1.Whir.StackedC2

/-!
# `open_stacked`'s blocks, honestly: positions, weights, queries, glue (TRIAGE #36)
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The squeezes -/

/-- The values of `osSqueezes` from its first, the state buffer at `sqzv`: its size and pointer,
the loop's bound and arguments, the last state's pointer and cells, the closing squeeze's values. -/
def osSqueezesVals (maxSq nsq : ℕ) (sqzv : E) (cv : Digest) : List E :=
  [osGw (2 * (maxSq + 1)), sqzv, 1, osGw nsq, 1 + osGw nsq, 1, osGw nsq, osGw (2 * nsq), sqzv * osGw (2 * nsq),
    (digestScalars (sqAll nsq cv).2).1, (digestScalars (sqAll nsq cv).2).2] ++
    (List.range 14).map (sqVals (sqAll nsq cv).2)

/-- **The query positions' squeezes** at their honest values: the state stored at `sqz[0 ..]`, the
loop's call, the last state read back at `sqz[2nsq ..]`, the batching challenge squeezed. -/
theorem osSqueezes_complete {maxSq nsq qpos qbp : ℕ} {loop : String} (hnsq : 2 * nsq < 2 ^ 128) {s : OsSt}
    {cv : Digest} {cur : E} {p : ℕ} (hat : OsAt σ s cv cur p) {sqzv : E} {kret : List E → Prop}
    (l0 : LoadHolds rd sqzv 0 (digestScalars cv).1) (l1 : LoadHolds rd sqzv 1 (digestScalars cv).2)
    (l2 : LoadHolds rd sqzv (2 * nsq) (digestScalars (sqAll nsq cv).2).1)
    (l3 : LoadHolds rd sqzv (2 * nsq + 1) (digestScalars (sqAll nsq cv).2).2)
    (hcall : 1 + osGw nsq ≠ 0 → C loop [1, osGw nsq, sqzv, σ (.n qpos), σ (.n qbp)] [])
    (hv : ∀ j < 25, σ (.n (s.k + j)) = (osSqueezesVals maxSq nsq sqzv cv).getD j 0) :
    Stmt.HoldsList C rd σ (osSqueezes maxSq nsq qpos qbp loop s).1 True kret ∧
      OsAt σ (osSqueezes maxSq nsq qpos qbp loop s).2 (sqCv (sqAll nsq cv).2) cur p ∧
      σ (.n ((osSqueezes maxSq nsq qpos qbp loop s).2.k - 1)) = challengeOf (sqCv (sqAll nsq cv).2) ∧
      (osSqueezes maxSq nsq qpos qbp loop s).2.co = s.co ∧ (osSqueezes maxSq nsq qpos qbp loop s).2.cb = s.cb ∧
      (osSqueezes maxSq nsq qpos qbp loop s).2.k = s.k + 25 := by
  set cS := (sqAll nsq cv).2
  set A : List E := [osGw (2 * (maxSq + 1)), sqzv, 1, osGw nsq, 1 + osGw nsq, 1, osGw nsq, osGw (2 * nsq),
    sqzv * osGw (2 * nsq), (digestScalars cS).1, (digestScalars cS).2] with hA
  have hvals : osSqueezesVals maxSq nsq sqzv cv = A ++ (List.range 14).map (sqVals cS) := rfl
  rw [hvals] at hv
  have lA : A.length = 11 := rfl
  have gA : ∀ j < 11, σ (.n (s.k + j)) = A.getD j 0 := fun j hj => by
    rw [hv j (by omega), oq_getD_app_lt (by omega)]
  have gS : ∀ j < 14, σ (.n (s.k + 11 + j)) = sqVals cS j := fun j hj => by
    rw [Nat.add_assoc, show 11 + j = A.length + j by rw [lA], hv _ (by omega), os_skip]
    simp [List.getD_eq_getElem?_getD, hj]
  have e := fun j (hj : j < 11) => gA j hj
  have e0 := e 0 (by omega); have e1 := e 1 (by omega); have e2 := e 2 (by omega)
  have e3 := e 3 (by omega); have e4 := e 4 (by omega); have e5 := e 5 (by omega)
  have e6 := e 6 (by omega); have e7 := e 7 (by omega); have e8 := e 8 (by omega)
  have e9 := e 9 (by omega); have e10 := e 10 (by omega)
  simp only [hA, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
  unfold osSqueezes
  dsimp only
  refine ⟨?_, ⟨?_, hat.cursor⟩, ?_, rfl, rfl, rfl⟩
  · rw [holdsList_append]
    refine (holdsList_noRet _ (by simp [osHeap, Stmt.noRetList, Stmt.noRet]) _ _).mpr ⟨?_, ?_⟩
    · simp only [osHeap, List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
        List.map_cons, List.map_nil, and_true, true_and, word_one]
      refine ⟨e0, ?_, ?_, e2, e3, by rw [e4, e2, e3], e5, e6, ?_, fun h => by rw [e5, e6, e1]; exact hcall (by
        rwa [e4] at h), e7, by rw [e8, e1, e7], ?_, ?_⟩
      · have f0e : σ (.n s.f0) = (digestScalars cv).1 := congrArg Prod.fst hat.fs
        rw [e1, f0e]; exact l0
      · have f1e : σ (.n s.f1) = (digestScalars cv).2 := congrArg Prod.snd hat.fs
        rw [e1, f1e]; exact l1
      · rw [e4]; exact isInK_add (by simpa using gen_pow_isInK 0) (by rw [os_gw_eq (by omega)]; exact gen_pow_isInK _)
      · rw [e8, e9, os_gw_eq hnsq, loadHolds_gen_pow]; exact l2
      · rw [e8, e10, os_gw_eq hnsq, loadHolds_mul_gen_pow]; exact l3
    · exact (holds_squeezeT _ _ _ _ _).mpr ⟨⟨cS, by rw [e9, e10], fun j hj => gS j hj⟩, trivial⟩
  · show (σ (.n (s.k + 16)), σ (.n (s.k + 17))) = _
    rw [show s.k + 16 = s.k + 11 + 5 by ring, show s.k + 17 = s.k + 11 + 6 by ring, gS 5 (by omega),
      gS 6 (by omega)]
    rfl
  · show σ (.n (s.k + 25 - 1)) = _
    rw [show s.k + 25 - 1 = s.k + 11 + 13 by omega, gS 13 (by omega)]
    rfl

/-! ## The query weights -/

/-- The values of `osLamPows` from its first: `1`, then `lam^2 .. lam^nq`. -/
def osLamPowsVals (lv : E) (nq : ℕ) : List E := 1 :: (List.range (nq - 1)).map fun i => lv ^ (i + 2)

/-- **The query weights** at their honest values: `qw[base + i] = lam^i`. -/
theorem osLamPows_complete {lam qw base k : ℕ} {kret : List E → Prop} (nq : ℕ)
    (hst : ∀ i < nq, LoadHolds rd (σ (.n qw)) (base + i) (σ (.n lam) ^ i))
    (hv : ∀ j < nq, σ (.n (k + j)) = (osLamPowsVals (σ (.n lam)) nq).getD j 0) :
    Stmt.HoldsList C rd σ (osLamPows lam qw base k nq) True kret := by
  rcases nq with _ | nq
  · trivial
  rw [osLamPows]
  have e0 : σ (.n k) = 1 := by simpa [osLamPowsVals] using hv 0 (by omega)
  have hs0 := hst 0 (by omega)
  rw [Nat.add_zero, pow_zero] at hs0
  rcases Nat.eq_zero_or_pos nq with rfl | hnq
  · simp only [↓reduceIte, List.append_nil, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_one, and_true]
    exact ⟨e0, by rw [e0]; exact hs0⟩
  have e : ∀ i < nq, σ (.n (k + 1 + i)) = σ (.n lam) ^ (i + 2) := fun i hi => by
    rw [Nat.add_assoc, hv _ (by omega), Nat.add_comm 1 i]
    simp [osLamPowsVals, List.getD_eq_getElem?_getD, List.getElem?_range hi]
  rw [ite_neg' (by omega), holdsList_append, holdsList_append]
  refine (holdsList_noRet _ rfl _ _).mpr ⟨?_, (holdsList_noRet _ rfl _ _).mpr ⟨?_, ?_⟩⟩
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_one, and_true]
    exact ⟨e0, by rw [e0]; exact hs0⟩
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    have hs1 := hst 1 (by omega)
    rw [pow_one] at hs1
    exact ⟨hs1, by rw [show k + 1 = k + 1 + 0 by ring, e 0 hnq]; ring⟩
  · rw [holdsList_range_flatten _ _ (fun _ => rfl)]
    refine ⟨fun i hi => ?_, trivial⟩
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    refine ⟨?_, ?_⟩
    · rw [e i (by omega), show base + 2 + i = base + (i + 2) by ring]
      exact hst (i + 2) (by omega)
    · rw [show k + 2 + i = k + 1 + (i + 1) by ring, e (i + 1) (by omega), e i (by omega)]
      ring

/-! ## Segments of a value list -/

/-- The words of the segments before segment `i`. -/
def osPre (segs : List (List E)) (i : ℕ) : ℕ := ((segs.take i).map List.length).sum

theorem os_flat_seg : ∀ (segs : List (List E)) (i j : ℕ), i < segs.length → j < (segs.getD i []).length →
    segs.flatten.getD (osPre segs i + j) 0 = (segs.getD i []).getD j 0
  | [], _, _, h, _ => absurd h (by simp)
  | s :: segs, 0, j, _, hj => by
    simp only [osPre, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatten_cons,
      List.getD_cons_zero] at hj ⊢
    exact oq_getD_app_lt hj
  | s :: segs, i + 1, j, hi, hj => by
    simp only [osPre, List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons,
      List.getD_cons_succ] at hj ⊢
    rw [Nat.add_assoc, os_skip]
    exact os_flat_seg segs i j (by simpa using hi) hj

theorem os_flat_len (segs : List (List E)) (i : ℕ) (hi : i < segs.length) :
    osPre segs i + (segs.getD i []).length ≤ segs.flatten.length := by
  induction segs generalizing i with
  | nil => simp at hi
  | cons s segs ih =>
    rcases i with _ | i
    · simp [osPre]
    · simp only [osPre, List.take_succ_cons, List.map_cons, List.sum_cons, List.getD_cons_succ,
        List.flatten_cons, List.length_append] at ih ⊢
      have := ih i (by simpa using hi)
      omega

/-- Segment `i`'s lookups from the value list's lookups. -/
theorem os_seg_look {k : ℕ} {segs : List (List E)}
    (hv : ∀ j < segs.flatten.length, σ (.n (k + j)) = segs.flatten.getD j 0) (i : ℕ) (hi : i < segs.length) :
    ∀ j < (segs.getD i []).length, σ (.n (k + osPre segs i + j)) = (segs.getD i []).getD j 0 := fun j hj => by
  rw [Nat.add_assoc, hv _ (by have := os_flat_len segs i hi; omega), os_flat_seg segs i j hi hj]

/-! ## The queries -/

/-- The value segments of `osQueries` from its first: the row weights' buffer, the pointers, the
cap's root, the query count and sum, the intro's reads, its middle coefficient. -/
def osQueriesSegs (cfg : OsCfg) (lv : OsLvl) (lvl : ℕ) (rewv fchv capsv flagsv qwv qbpv : E) (rt : Digest)
    (qsum c0 c2 : E) (cv : Digest) : List (List E) :=
  [[osGw cfg.maxIl, rewv], osMatVals fchv lv.foldsOff, osMatVals capsv (4 * lv.capOff), osMatVals flagsv lv.capOff,
    [(digestScalars rt).1, (digestScalars rt).2], osMatVals capsv (4 * lv.capOff), osMatVals flagsv lv.capOff,
    osMatVals qwv (lvl * cfg.maxQ), osMatVals qbpv lv.posOff, [osGw lv.queries, qsum], osFsNextVals c0 cv,
    osFsNextVals c2 (obsCv cv c0), [qsum + c2]]

/-- **A level's queries** at their honest values: the row weights' buffer, the calls' pointers, the
cap's root checked against the level's root, the queries' sum, the intro's `c0`, `c2` read. -/
theorem osQueries_complete {cfg : OsCfg} {lv : OsLvl} {lvl : ℕ} (hfo : lv.foldsOff < 2 ^ 128)
    (hco4 : 4 * lv.capOff < 2 ^ 128) (hco1 : lv.capOff < 2 ^ 128) (hqo : lvl * cfg.maxQ < 2 ^ 128)
    (hpo : lv.posOff < 2 ^ 128) {s : OsSt} {cv : Digest} {cur : E} {p : ℕ} (hat : OsAt σ s cv cur p)
    {rewv : E} {rt : Digest} {qsum c0 c2 : E} {kret : List E → Prop}
    (lc0 : LoadHolds rd cur p c0) (lc2 : LoadHolds rd cur (p + 1) c2)
    (sr0 : LoadHolds rd (σ (.n osRoots)) (2 * lvl) (digestScalars rt).1)
    (sr1 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) (digestScalars rt).2)
    (hrw : C lv.rowWeights [σ (.n osFch) * gen ^ lv.foldsOff, rewv] [])
    (hcap : C lv.verifyCap [σ (.n osCaps) * gen ^ (4 * lv.capOff), σ (.n osFlags) * gen ^ lv.capOff]
      [(digestScalars rt).1, (digestScalars rt).2])
    (hqf : C lv.queriesFn [σ (.n osCaps) * gen ^ (4 * lv.capOff), σ (.n osFlags) * gen ^ lv.capOff,
      σ (.n osQw) * gen ^ (lvl * cfg.maxQ), σ (.n osQbp) * gen ^ lv.posOff, rewv, osGw lv.queries] [qsum])
    (hv : ∀ j < (osQueriesSegs cfg lv lvl rewv (σ (.n osFch)) (σ (.n osCaps)) (σ (.n osFlags)) (σ (.n osQw))
        (σ (.n osQbp)) rt qsum c0 c2 cv).flatten.length,
      σ (.n (s.k + j)) = (osQueriesSegs cfg lv lvl rewv (σ (.n osFch)) (σ (.n osCaps)) (σ (.n osFlags)) (σ (.n osQw))
        (σ (.n osQbp)) rt qsum c0 c2 cv).flatten.getD j 0) :
    let q := osQueries cfg lv lvl s
    Stmt.HoldsList C rd σ q.1 True kret ∧ OsAt σ q.2.1 (obsCv (obsCv cv c0) c2) cur (p + 2) ∧
      q.2.1.co = s.co + 2 ∧ q.2.1.cb = s.cb ∧ σ (.n q.2.2.1) = qsum ∧ σ (.n q.2.2.2.1) = c0 ∧
      σ (.n q.2.2.2.2.1) = qsum + c2 ∧ σ (.n q.2.2.2.2.2) = c2 ∧ σ (.n (s.k + 1)) = rewv ∧
      q.2.1.k = s.k + (osQueriesSegs cfg lv lvl rewv (σ (.n osFch)) (σ (.n osCaps)) (σ (.n osFlags)) (σ (.n osQw))
        (σ (.n osQbp)) rt qsum c0 c2 cv).flatten.length := by
  intro q
  set segs := osQueriesSegs cfg lv lvl rewv (σ (.n osFch)) (σ (.n osCaps)) (σ (.n osFlags)) (σ (.n osQw))
    (σ (.n osQbp)) rt qsum c0 c2 cv with hsegs
  have look := os_seg_look hv
  have hl : segs.length = 13 := rfl
  have L := fun i (hi : i < 13) j (hj : j < (segs.getD i []).length) => look i (by omega) j hj
  have hlen : ∀ (b : E) off, (osMatVals b off).length = (osMatVals 0 off).length := os_length_matVals'
  set k := s.k
  -- positions
  set P := osMat osFch lv.foldsOff (k + 2)
  set CP := osMat osCaps (4 * lv.capOff) P.2.2
  set FP := osMat osFlags lv.capOff CP.2.2
  set r := FP.2.2
  set CP2 := osMat osCaps (4 * lv.capOff) (r + 2)
  set FP2 := osMat osFlags lv.capOff CP2.2.2
  set QP := osMat osQw (lvl * cfg.maxQ) FP2.2.2
  set BP := osMat osQbp lv.posOff QP.2.2
  set g := BP.2.2
  have hp : ∀ i, osPre segs (i + 1) = osPre segs i + (segs.getD i []).length := fun i => by
    simp only [osPre]
    rcases Nat.lt_or_ge i segs.length with h | h
    · rw [List.take_add_one, List.map_append, List.sum_append, List.getElem?_eq_getElem h]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr h]
  have g0 : (segs.getD 0 []).length = 2 := rfl
  have g1 : (segs.getD 1 []).length = (osMatVals 0 lv.foldsOff).length := hlen _ _
  have g2 : (segs.getD 2 []).length = (osMatVals 0 (4 * lv.capOff)).length := hlen _ _
  have g3 : (segs.getD 3 []).length = (osMatVals 0 lv.capOff).length := hlen _ _
  have g4 : (segs.getD 4 []).length = 2 := rfl
  have g5 : (segs.getD 5 []).length = (osMatVals 0 (4 * lv.capOff)).length := hlen _ _
  have g6 : (segs.getD 6 []).length = (osMatVals 0 lv.capOff).length := hlen _ _
  have g7 : (segs.getD 7 []).length = (osMatVals 0 (lvl * cfg.maxQ)).length := hlen _ _
  have g8 : (segs.getD 8 []).length = (osMatVals 0 lv.posOff).length := hlen _ _
  have g9 : (segs.getD 9 []).length = 2 := rfl
  have g10 : (segs.getD 10 []).length = 15 := os_length_fsNextVals _ _
  have g11 : (segs.getD 11 []).length = 15 := os_length_fsNextVals _ _
  have g12 : (segs.getD 12 []).length = 1 := rfl
  have o0 : osPre segs 0 = 0 := rfl
  have o1 : osPre segs 1 = 2 := by rw [hp, o0, g0]
  have o2 := hp 1; have o3 := hp 2; have o4 := hp 3; have o5 := hp 4; have o6 := hp 5; have o7 := hp 6
  have o8 := hp 7; have o9 := hp 8; have o10 := hp 9; have o11 := hp 10; have o12 := hp 11; have o13 := hp 12
  have q1 : k + 2 = k + osPre segs 1 := by rw [o1]
  have q2 : P.2.2 = k + osPre segs 2 := by rw [osMat_next', o2, o1, g1]; ring
  have q3 : CP.2.2 = k + osPre segs 3 := by rw [osMat_next', q2, o3, g2]; ring
  have q4 : r = k + osPre segs 4 := by rw [show r = FP.2.2 from rfl, osMat_next', q3, o4, g3]; ring
  have q5 : r + 2 = k + osPre segs 5 := by rw [q4, o5, g4]; ring
  have q6 : CP2.2.2 = k + osPre segs 6 := by rw [osMat_next', q5, o6, g5]; ring
  have q7 : FP2.2.2 = k + osPre segs 7 := by rw [osMat_next', q6, o7, g6]; ring
  have q8 : QP.2.2 = k + osPre segs 8 := by rw [osMat_next', q7, o8, g7]; ring
  have q9 : g = k + osPre segs 9 := by rw [show g = BP.2.2 from rfl, osMat_next', q8, o9, g8]; ring
  have q10 : g + 2 = k + osPre segs 10 := by rw [q9, o10, g9]; ring
  have q11 : g + 2 + 15 = k + osPre segs 11 := by rw [q10, o11, g10]; omega
  have q12 : g + 2 + 15 + 15 = k + osPre segs 12 := by rw [q11, o12, g11]; omega
  have qend : osPre segs 13 = segs.flatten.length := by
    simp only [osPre, show 13 = segs.length from rfl, List.take_length, List.length_flatten]
  -- the lookups
  have look0 := L 0 (by omega); have look1 := L 1 (by omega); have look2 := L 2 (by omega)
  have look3 := L 3 (by omega); have look4 := L 4 (by omega); have look5 := L 5 (by omega)
  have look6 := L 6 (by omega); have look7 := L 7 (by omega); have look8 := L 8 (by omega)
  have look9 := L 9 (by omega); have look10 := L 10 (by omega); have look11 := L 11 (by omega)
  have look12 := L 12 (by omega)
  rw [o0, Nat.add_zero] at look0
  have v0 : σ (.n k) = osGw cfg.maxIl := look0 0 (by omega)
  have v1 : σ (.n (k + 1)) = rewv := look0 1 (by omega)
  have mP := osMat_complete (C := C) (rd := rd) (σ := σ) (base := osFch) (k := k + 2) (kret := kret) hfo
    fun j hj => by rw [q1]; exact look1 j (by rwa [g1, ← hlen (σ (.n osFch))])
  have mCP := osMat_complete (C := C) (rd := rd) (σ := σ) (base := osCaps) (k := P.2.2) (kret := kret) hco4
    fun j hj => by rw [q2]; exact look2 j (by rwa [g2, ← hlen (σ (.n osCaps))])
  have mFP := osMat_complete (C := C) (rd := rd) (σ := σ) (base := osFlags) (k := CP.2.2) (kret := kret) hco1
    fun j hj => by rw [q3]; exact look3 j (by rwa [g3, ← hlen (σ (.n osFlags))])
  have vr0 : σ (.n r) = (digestScalars rt).1 := by rw [q4]; exact look4 0 (by omega)
  have vr1 : σ (.n (r + 1)) = (digestScalars rt).2 := by
    have := look4 1 (by omega); rw [← q4] at this; exact this
  have mCP2 := osMat_complete (C := C) (rd := rd) (σ := σ) (base := osCaps) (k := r + 2) (kret := kret) hco4
    fun j hj => by rw [q5]; exact look5 j (by rwa [g5, ← hlen (σ (.n osCaps))])
  have mFP2 := osMat_complete (C := C) (rd := rd) (σ := σ) (base := osFlags) (k := CP2.2.2) (kret := kret) hco1
    fun j hj => by rw [q6]; exact look6 j (by rwa [g6, ← hlen (σ (.n osFlags))])
  have mQP := osMat_complete (C := C) (rd := rd) (σ := σ) (base := osQw) (k := FP2.2.2) (kret := kret) hqo
    fun j hj => by rw [q7]; exact look7 j (by rwa [g7, ← hlen (σ (.n osQw))])
  have mBP := osMat_complete (C := C) (rd := rd) (σ := σ) (base := osQbp) (k := QP.2.2) (kret := kret) hpo
    fun j hj => by rw [q8]; exact look8 j (by rwa [g8, ← hlen (σ (.n osQbp))])
  have vg0 : σ (.n g) = osGw lv.queries := by rw [q9]; exact look9 0 (by omega)
  have vg1 : σ (.n (g + 1)) = qsum := by have := look9 1 (by omega); rw [← q9] at this; exact this
  set s1 : OsSt := { s with k := g + 2 }
  have hat1 : OsAt σ s1 cv cur p := ⟨hat.fs, hat.cursor⟩
  obtain ⟨hi0, hat2⟩ := osFsNext_complete (C := C) (kret := kret) hat1 lc0 fun j hj => by
    show σ (.n (g + 2 + j)) = _
    rw [q10]; exact look10 j (by omega)
  obtain ⟨hi2, hat3⟩ := osFsNext_complete (C := C) (kret := kret) hat2 lc2 fun j hj => by
    show σ (.n (g + 2 + 15 + j)) = _
    rw [q11]; exact look11 j (by omega)
  have vc0 : σ (.n s1.k) = c0 := by show σ (.n (g + 2)) = c0; rw [q10]; exact look10 0 (by omega)
  have vc2 : σ (.n (osFsNext s1).2.k) = c2 := by
    show σ (.n (g + 2 + 15)) = c2; have := look11 0 (by omega); rw [Nat.add_zero, ← q11] at this; exact this
  have vc1 : σ (.n (osFsNext (osFsNext s1).2).2.k) = qsum + c2 := by
    show σ (.n (g + 2 + 15 + 15)) = _; have := look12 0 (by omega); rw [Nat.add_zero, ← q12] at this; exact this
  refine ⟨?_, ⟨hat3.fs, hat3.cursor⟩, by simp [q, osQueries, osFsNext], rfl, vg1, vc0, vc1, vc2, v1, ?_⟩
  · show Stmt.HoldsList C rd σ (osHeap cfg.maxIl k ++ P.1 ++ [.call lv.rowWeights [.n P.2.1, .n (k + 1)] []] ++
      CP.1 ++ FP.1 ++ [.call lv.verifyCap [.n CP.2.1, .n FP.2.1] [.n r, .n (r + 1)],
        .atom (.load (.n r) (.n osRoots) (2 * lvl)), .atom (.load (.n (r + 1)) (.n osRoots) (2 * lvl + 1))] ++
      CP2.1 ++ FP2.1 ++ QP.1 ++ BP.1 ++ [.atom (.const (.n g) (osGw lv.queries)),
        .call lv.queriesFn [.n CP2.2.1, .n FP2.2.1, .n QP.2.1, .n BP.2.1, .n (k + 1), .n g] [.n (g + 1)]] ++
      (osFsNext s1).1 ++ (osFsNext (osFsNext s1).2).1 ++
      [.atom (.add (.n (osFsNext (osFsNext s1).2).2.k) (.n (g + 1)) (.n (osFsNext s1).2.k))]) True kret
    simp only [holdsList_append]
    refine (holdsList_noRet _ rfl _ _).mpr ⟨?_, (holdsList_noRet _ (osMat_noRet _ _ _) _ _).mpr ⟨mP.1,
      (holdsList_noRet _ rfl _ _).mpr ⟨⟨by simp only [List.map_cons, List.map_nil]; rw [mP.2, v1]; exact hrw, trivial⟩,
      (holdsList_noRet _ (osMat_noRet _ _ _) _ _).mpr ⟨mCP.1,
      (holdsList_noRet _ (osMat_noRet _ _ _) _ _).mpr ⟨mFP.1, (holdsList_noRet _ rfl _ _).mpr ⟨?_,
      (holdsList_noRet _ (osMat_noRet _ _ _) _ _).mpr ⟨mCP2.1, (holdsList_noRet _ (osMat_noRet _ _ _) _ _).mpr
      ⟨mFP2.1, (holdsList_noRet _ (osMat_noRet _ _ _) _ _).mpr ⟨mQP.1, (holdsList_noRet _ (osMat_noRet _ _ _) _ _).mpr
      ⟨mBP.1, (holdsList_noRet _ rfl _ _).mpr ⟨?_, (holdsList_noRet _ rfl _ _).mpr ⟨hi0,
      (holdsList_noRet _ rfl _ _).mpr ⟨hi2, ?_⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
    · simp only [osHeap, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      exact v0
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, and_true]
      exact ⟨by rw [mCP.2, mFP.2, vr0, vr1]; exact hcap, by rw [vr0]; exact sr0, by rw [vr1]; exact sr1⟩
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, and_true]
      refine ⟨vg0, ?_⟩
      rw [mCP2.2, mFP2.2, mQP.2, mBP.2, v1, vg0, vg1]
      exact hqf
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      rw [vc1, vg1, vc2]
  · show (osFsNext (osFsNext s1).2).2.k + 1 = _
    rw [← qend, hp 12, show (osFsNext (osFsNext s1).2).2.k = g + 2 + 15 + 15 from rfl, q12, g12]; ring

end
end LeanVM.Guest.B1
