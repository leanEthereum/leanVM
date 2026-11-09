/-
  LeanVM.Guest.B1.Whir.CSqLoop

  The squeeze loop, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CLoop
public import LeanVM.Guest.B1.Whir.CCommit

/-!
# The squeeze loop, honestly

`segVal`: a valuation given by segments. `osPowSteps_complete`: the square-and-multiply chain.
`osSqueeze0_complete`: a squeeze with nothing waiting. `sqIter_complete`: one iteration at `x`,
its memory honest (`SqIterMem`: the capacity in its row, the next in the next, the challenge
decoded), is the loop's body; `sqLoop_complete`: the loop.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The valuation of the segments, at the values `.n i`. -/
def segVal (segs : List (ℕ × (ℕ → E))) : Val := fun v ↦
  if v.path = [] ∧ v.tag = 0 then segLookup segs v.idx else 0

theorem segVal_n (segs : List (ℕ × (ℕ → E))) (i : ℕ) : segVal segs (.n i) = segLookup segs i := by
  simp [segVal]

/-! ## Square and multiply -/

/-- The values of the square-and-multiply chain on `X` from `X^a`. -/
def powVals (X : E) : List Bool → ℕ → List E
  | [], _ => []
  | true :: ds, a => [X ^ (2 * a), X ^ (2 * a + 1)] ++ powVals X ds (2 * a + 1)
  | false :: ds, a => [X ^ (2 * a)] ++ powVals X ds (2 * a)

theorem powVals_length (X : E) : ∀ (ds : List Bool) (a : ℕ),
    (powVals X ds a).length = ds.length + (ds.filter id).length
  | [], _ => rfl
  | true :: ds, a => by simp [powVals, powVals_length X ds]; omega
  | false :: ds, a => by simp [powVals, powVals_length X ds]; omega

/-- **The square-and-multiply chain, honestly.** -/
theorem osPowSteps_complete {σ : Val} (x : ℕ) : ∀ (ds : List Bool) (acc k a : ℕ),
    σ (.n acc) = σ (.n x) ^ a →
    (∀ j < (powVals (σ (.n x)) ds a).length,
      σ (.n (k + j)) = (powVals (σ (.n x)) ds a).getD j 0) →
    AllOk C rd σ (osPowSteps x ds acc k).1 ∧
      σ (.n (osPowSteps x ds acc k).2) = σ (.n x) ^ digitsVal ds a
  | [], _, _, _, ha, _ => ⟨allOk_nil, ha⟩
  | true :: ds, acc, k, a, ha, hv => by
    have v0 := hv 0 (by simp [powVals])
    have v1 := hv 1 (by simp [powVals])
    simp only [powVals, List.cons_append, List.nil_append, List.getD_cons_zero,
      List.getD_cons_succ, Nat.add_zero] at v0 v1
    have := osPowSteps_complete x ds (k + 1) (k + 2) (2 * a + 1) v1 (fun j hj ↦ by
      have := hv (j + 2) (by simp [powVals]; omega)
      simp only [powVals, List.cons_append, List.nil_append, List.getD_cons_succ] at this
      rw [show k + 2 + j = k + (j + 2) by ring, this])
    simp only [osPowSteps, ↓reduceIte, allOk_cons, StmtOk, Atom.Holds]
    refine ⟨⟨by rw [v0, ha, ← pow_add]; ring_nf, by rw [v1, v0]; ring, this.1⟩, ?_⟩
    rw [this.2]; rfl
  | false :: ds, acc, k, a, ha, hv => by
    have v0 := hv 0 (by simp [powVals])
    simp only [powVals, List.cons_append, List.nil_append, List.getD_cons_zero, Nat.add_zero] at v0
    have := osPowSteps_complete x ds k (k + 1) (2 * a) v0 (fun j hj ↦ by
      have := hv (j + 1) (by simp [powVals]; omega)
      simp only [powVals, List.cons_append, List.nil_append, List.getD_cons_succ] at this
      rw [show k + 1 + j = k + (j + 1) by ring, this])
    simp only [osPowSteps, Bool.false_eq_true, ↓reduceIte, allOk_cons, StmtOk, Atom.Holds]
    refine ⟨⟨by rw [v0, ha, ← pow_add]; ring_nf, this.1⟩, ?_⟩
    rw [this.2]; simp [digitsVal]

/-! ## A squeeze with nothing waiting -/

/-- **A squeeze with nothing waiting, honestly**: the zero run, the capacity canonical, the
permutation's cells and the challenge's values. -/
theorem osSqueeze0_complete {σ : Val} {p : ℕ} {cap : List ℕ} (hcl : cap.length = 5) {j : ℕ}
    (hz : σ (.n (p + 1)) = 0 ∧ σ (.n (p + 2)) = 0 ∧ σ (.n (p + 3)) = 0 ∧ σ (.n (p + 4)) = 0)
    (hcan : AllCanonical (cap.map fun i ↦ σ (.n i)))
    (hv : ∀ c < 13, σ (.n (j + c)) = cells13F (⟨cap.map fun i ↦ σ (.n i), []⟩ : Fs).perm c)
    (hc : ∀ i < 7, σ (.n (j + 13 + i)) = challengeVals (σ (.n j)) (σ (.n (j + 1))) i) :
    AllOk C rd σ (osSqueeze0 p cap j) ∧
      σ (.n (j + 19)) = challengeOf (⟨cap.map fun i ↦ σ (.n i), []⟩ : Fs).perm := by
  obtain ⟨z1, z2, z3, z4⟩ := hz
  set S := (⟨cap.map fun i ↦ σ (.n i), []⟩ : Fs).perm with hS
  have h0 : σ (.n j) = cellsOfState S false 0 := by
    have := hv 0 (by omega); simpa [cells13F] using this
  have h1 : σ (.n (j + 1)) = cellsOfState S false 1 := by
    have := hv 1 (by omega); simpa [cells13F] using this
  have hins : (([p + 1, p + 1, p + 1, p + 1, p + 1, p + 2, p + 3, p + 4] ++ cap).map V.n).map σ =
      pendCells [] ++ List.replicate 8 0 ++ cap.map fun i ↦ σ (.n i) := by
    simp [z1, z2, z3, z4, pendCells, List.replicate]
  refine ⟨?_, ?_⟩
  · simp only [osSqueeze0, allOk_cons, allOk_challengeT]
    refine ⟨?_, ?_⟩
    · show (Atom.keccak _ _ false false).Holds rd σ
      apply keccakA_of (by simp [hcl]) (by simp [osRun])
      · rw [hins]
        intro x hx
        simp only [List.mem_append, List.mem_replicate] at hx
        rcases hx with (hx | hx) | hx
        · simp [pendCells] at hx
        · rw [hx.2, zero_eq_ofLimbs]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl
        · exact hcan x hx
      · rw [hins, show permOf (pendCells [] ++ List.replicate 8 0 ++ cap.map fun i ↦ σ (.n i)) = S
          from by rw [hS, perm_eq_cells _ (by simp)]; rfl]
        funext c
        simp only [cells13, osRun, List.map_map, Function.comp_def]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range c.isLt,
          Option.map_some, Option.getD_some]
        have := hv c.val c.isLt
        simp only [cells13F, c.isLt, ↓reduceDIte] at this
        exact this
    · apply challengeOk_of_vals (by rw [h1]; exact cellsOfState_canonical _ _ _)
      intro i hi
      exact hc i hi
  · have := hc 6 (by omega)
    rw [show j + 13 + 6 = j + 19 by ring, h0, h1] at this
    rw [this, challengeVals_six]

/-! ## The squeeze loop's iteration -/

/-- What one iteration at `x` reads and writes of memory: the capacity in its row of the squeeze
run, the next capacity in the next row, the challenge decoded into the positions and windows. -/
structure SqIterMem (rd : Reader) (d cd po : ℕ) (sqz qpos qbp tabs x : E) (cap : List E) : Prop where
  row : ∀ i < 5, LoadHolds rd (sqz * x ^ 5) i (cap.getD i 0)
  next : ∀ i < 5, LoadHolds rd (sqz * x ^ 5) (5 + i) ((capOf (⟨cap, []⟩ : Fs).perm).getD i 0)
  dec : coreProgram.Rel rd ("decode_query_windows__L" ++ natStr d ++ "_L" ++ natStr cd)
    [challengeOf (⟨cap, []⟩ : Fs).perm, qpos * gen ^ po * x ^ (192 / d),
      qbp * gen ^ po * x ^ (192 / d), tabs] []

/-- The iteration's values, by segments. -/
def sqSegs (lv : OsLv) (X N sqz qpos qbp tabs : E) (cap : List E) : List (ℕ × (ℕ → E)) :=
  [(6, fun i ↦ [X, N, sqz, qpos, qbp, tabs].getD i 0),
    (4, fun i ↦ [X * X, X * X * (X * X), X * X * (X * X) * X, sqz * (X * X * (X * X) * X)].getD i 0),
    (5, fun i ↦ cap.getD i 0), (5, fun i ↦ [word 1 0 0, word 0 0 0, word 0 0 0, word 0 0 0,
      word 0 0 0].getD i 0),
    (13, cells13F (⟨cap, []⟩ : Fs).perm),
    (7, challengeVals (cells13F (⟨cap, []⟩ : Fs).perm 0) (cells13F (⟨cap, []⟩ : Fs).perm 1)),
    (osPowLen (192 / lv.depth), fun i ↦ (powVals X (osPowDigits (192 / lv.depth)) 1).getD i 0),
    (if lv.posOff = 0 then 0 else 2, fun i ↦ [gw lv.posOff, qpos * gw lv.posOff].getD i 0),
    (1, fun _ ↦ qpos * gen ^ lv.posOff * X ^ (192 / lv.depth)),
    (if lv.posOff = 0 then 0 else 2, fun i ↦ [gw lv.posOff, qbp * gw lv.posOff].getD i 0),
    (1, fun _ ↦ qbp * gen ^ lv.posOff * X ^ (192 / lv.depth)),
    (5, fun i ↦ [word 2 0 0, X * word 2 0 0, X * word 2 0 0 + N, word 2 0 0, X * word 2 0 0].getD
      i 0)]

theorem osMat_k_eq (b o k : ℕ) : (osMat b o k).2.2 = k + (if o = 0 then 0 else 2) := by
  unfold osMat; split_ifs <;> simp

/-- The loop's tail's first value. -/
def sqTail (lv : OsLv) : ℕ :=
  (osMat 4 lv.posOff ((osMat 3 lv.posOff (40 + osPowLen (192 / lv.depth))).2.2 + 1)).2.2 + 1

theorem sqTail_eq (lv : OsLv) : sqTail lv =
    40 + osPowLen (192 / lv.depth) + 2 * (if lv.posOff = 0 then 0 else 2) + 2 := by
  unfold sqTail osMat
  split_ifs <;> simp

/-- The valuation of one iteration. -/
def sqIterVal (lv : OsLv) (X N sqz qpos qbp tabs : E) (cap : List E) : Val :=
  segVal (sqSegs lv X N sqz qpos qbp tabs cap)

/-- **One iteration, honestly**, at its explicit valuation, for any relation holding of its
decoder call. -/
theorem sqIter_completeC (lv : OsLv)
    (hpw : digitsVal (osPowDigits (192 / lv.depth)) 1 = 192 / lv.depth)
    (hpo : lv.posOff < u128Bound)
    (X N sqz qpos qbp tabs : E) (cap : List E) (hcl : cap.length = 5) (hcan : AllCanonical cap)
    (hrow : ∀ i < 5, LoadHolds rd (sqz * X ^ 5) i (cap.getD i 0))
    (hnext : ∀ i < 5, LoadHolds rd (sqz * X ^ 5) (5 + i) ((capOf (⟨cap, []⟩ : Fs).perm).getD i 0))
    (hdec : C ("decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth)
      [challengeOf (⟨cap, []⟩ : Fs).perm, qpos * gen ^ lv.posOff * X ^ (192 / lv.depth),
        qbp * gen ^ lv.posOff * X ^ (192 / lv.depth), tabs] []) :
    (osParams 6).map (sqIterVal lv X N sqz qpos qbp tabs cap) = [X, N, sqz, qpos, qbp, tabs] ∧
      (AllOk C rd (sqIterVal lv X N sqz qpos qbp tabs cap) (sqLoopA lv ++ osLoopTailA (sqTail lv)) ∧
        sqIterVal lv X N sqz qpos qbp tabs cap (.n 9) = sqz * X ^ 5 ∧
        ([.n 39, .n (osMat 3 lv.posOff (40 + osPowLen (192 / lv.depth))).2.2,
          .n (osMat 4 lv.posOff ((osMat 3 lv.posOff (40 + osPowLen (192 / lv.depth))).2.2 + 1)).2.2,
          .n 5] :
            List V).map (sqIterVal lv X N sqz qpos qbp tabs cap) =
          [challengeOf (⟨cap, []⟩ : Fs).perm, qpos * gen ^ lv.posOff * X ^ (192 / lv.depth),
            qbp * gen ^ lv.posOff * X ^ (192 / lv.depth), tabs]) ∧
      sqIterVal lv X N sqz qpos qbp tabs cap (.n (sqTail lv + 2)) = X * gen + N ∧
      (.n (sqTail lv + 4) :: (List.range (6 - 1)).map fun i ↦ V.n (i + 1)).map
          (sqIterVal lv X N sqz qpos qbp tabs cap) =
        X * gen :: [N, sqz, qpos, qbp, tabs] := by
  rcases cap with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, _ | ⟨c5, rest⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hcl <;> try omega
  unfold sqIterVal
  set segs := sqSegs lv X N sqz qpos qbp tabs [c0, c1, c2, c3, c4] with hsegs
  set σ := segVal segs with hσ
  have hv : ∀ i, σ (.n i) = segLookup segs i := segVal_n segs
  have sv : ∀ (m : ℕ) (hm : m < segs.length) (o : ℕ), segLen (segs.take m) = o → ∀ i,
      i < segs[m].1 → σ (.n (o + i)) = segs[m].2 i := fun m hm o ho i hi ↦ by
    have := seg_val (σ := σ) (k := 0) (segs := segs) (fun j _ ↦ by rw [Nat.zero_add]; exact hv j)
      m hm o ho i hi
    rwa [Nat.zero_add] at this
  set L := osPowLen (192 / lv.depth) with hL
  set m := if lv.posOff = 0 then 0 else 2 with hmm
  have he := sqTail_eq lv
  rw [← hL, ← hmm] at he
  have lowv : ∀ i < 40, σ (.n i) = segLookup segs i := fun i _ ↦ hv i
  have g0 : σ (.n 0) = X := by rw [hv]; simp [hsegs, sqSegs, segLookup]
  have g1 : σ (.n 1) = N := by rw [hv]; simp [hsegs, sqSegs, segLookup]
  have g2 : σ (.n 2) = sqz := by rw [hv]; simp [hsegs, sqSegs, segLookup]
  have g3 : σ (.n 3) = qpos := by rw [hv]; simp [hsegs, sqSegs, segLookup]
  have g4 : σ (.n 4) = qbp := by rw [hv]; simp [hsegs, sqSegs, segLookup]
  have g5 : σ (.n 5) = tabs := by rw [hv]; simp [hsegs, sqSegs, segLookup]
  have tl : ∀ i < 5, σ (.n (sqTail lv + i)) =
      [word 2 0 0, X * word 2 0 0, X * word 2 0 0 + N, word 2 0 0, X * word 2 0 0].getD i 0 :=
    fun i hi ↦ by
      rw [he]
      exact sv 11 (by simp [hsegs, sqSegs]) _ (by simp [hsegs, sqSegs, segLen, ← hL, ← hmm]; ring)
        i (by simp [hsegs, sqSegs]; omega)
  have t0 := tl 0 (by omega); have t1 := tl 1 (by omega); have t2 := tl 2 (by omega)
  have t3 := tl 3 (by omega); have t4 := tl 4 (by omega)
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at t0 t1 t2 t3 t4
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [osParams, List.range_succ, List.range_zero, List.map_cons,
      List.map_nil, List.nil_append, List.cons_append, g0, g1, g2, g3, g4, g5]
  · have v5 : σ (.n 6) = X * X := by rw [hv]; simp [hsegs, sqSegs, segLookup]
    have v6 : σ (.n 7) = X * X * (X * X) := by rw [hv]; simp [hsegs, sqSegs, segLookup]
    have v7 : σ (.n 8) = X * X * (X * X) * X := by rw [hv]; simp [hsegs, sqSegs, segLookup]
    have v8 : σ (.n 9) = sqz * (X * X * (X * X) * X) := by rw [hv]; simp [hsegs, sqSegs, segLookup]
    have vc : ∀ i < 5, σ (.n (10 + i)) = [c0, c1, c2, c3, c4].getD i 0 := fun i hi ↦
      sv 2 (by simp [hsegs, sqSegs]) 10 (by simp [hsegs, sqSegs, segLen]) i
        (by simp [hsegs, sqSegs]; omega)
    have vz : ∀ i < 5, σ (.n (15 + i)) = [word 1 0 0, word 0 0 0, word 0 0 0, word 0 0 0,
        word 0 0 0].getD i 0 := fun i hi ↦
      sv 3 (by simp [hsegs, sqSegs]) 15 (by simp [hsegs, sqSegs, segLen]) i
        (by simp [hsegs, sqSegs]; omega)
    set S := (⟨[c0, c1, c2, c3, c4], []⟩ : Fs).perm with hS
    have vk : ∀ c < 13, σ (.n (20 + c)) = cells13F S c := fun c hc ↦
      sv 4 (by simp [hsegs, sqSegs]) 20 (by simp [hsegs, sqSegs, segLen]) c
        (by simp [hsegs, sqSegs]; omega)
    have vch : ∀ i < 7, σ (.n (33 + i)) = challengeVals (cells13F S 0) (cells13F S 1) i :=
      fun i hi ↦ sv 5 (by simp [hsegs, sqSegs]) 33 (by simp [hsegs, sqSegs, segLen]) i
        (by simp [hsegs, sqSegs]; omega)
    have vpw : ∀ j < (powVals (σ (.n 0)) (osPowDigits (192 / lv.depth)) 1).length,
        σ (.n (40 + j)) = (powVals (σ (.n 0)) (osPowDigits (192 / lv.depth)) 1).getD j 0 :=
      fun j hj ↦ by
        rw [g0] at hj ⊢
        exact sv 6 (by simp [hsegs, sqSegs]) 40 (by simp [hsegs, sqSegs, segLen]) j
          (by simp [hsegs, sqSegs, osPowLen, powVals_length] at hj ⊢; omega)
    have hcm : [c0, c1, c2, c3, c4] = [10, 11, 12, 13, 14].map fun i ↦ σ (.n i) := by
      have e0 := vc 0 (by omega); have e1 := vc 1 (by omega); have e2 := vc 2 (by omega)
      have e3 := vc 3 (by omega); have e4 := vc 4 (by omega)
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1 e2 e3 e4
      simp only [List.map_cons, List.map_nil]
      rw [e0, e1, e2, e3, e4]
    have hp1k : (osMat 3 lv.posOff (40 + L)).2.2 = 40 + L + m := osMat_k_eq _ _ _
    have hp2k : (osMat 4 lv.posOff ((osMat 3 lv.posOff (40 + L)).2.2 + 1)).2.2 = 40 + L + m + 1 + m :=
      by rw [osMat_k_eq, hp1k]
    have hmat : ∀ (b : ℕ) (bv : E) (k : ℕ) (mi : ℕ) (hmi : mi < segs.length), b < k → σ (.n b) = bv →
        segLen (segs.take mi) = k → segs[mi].1 = m →
        segs[mi].2 = (fun i ↦ [gw lv.posOff, bv * gw lv.posOff].getD i 0) →
        AllOk C rd σ (osMat b lv.posOff k).1 ∧
          σ (.n (osMat b lv.posOff k).2.1) = bv * gen ^ lv.posOff := by
      intro b bv k mi hmi hbk hbv hk1 hm1 hm2
      have := osMat_complete (C := C) (rd := rd) (σ := σ) (σ' := σ) hpo hbk
        (fun _ _ ↦ rfl) (fun i h1 h2 ↦ by
          rw [osMat_k_eq] at h2
          have := sv mi hmi k hk1 (i - k) (by rw [hm1, hmm]; split_ifs at h2 ⊢ <;> omega)
          rw [show k + (i - k) = i by omega, hm2] at this
          rw [this, matVal]
          rcases Nat.lt_or_ge i (k + 1) with h | h
          · rw [show i - k = 0 by omega, show i = k by omega]; simp
          · rw [show i - k = 1 by split_ifs at h2 <;> omega]
            simp only [List.getD_cons_succ, List.getD_cons_zero, show i ≠ k by omega, ↓reduceIte,
              hbv])
      rwa [hbv] at this
    have hX5 : X * X * (X * X) * X = X ^ 5 := by ring
    obtain ⟨okp1, vp1⟩ := hmat 3 qpos (40 + L) 7 (by simp [hsegs, sqSegs]) (by omega) g3
      (by simp [hsegs, sqSegs, segLen, hL]; omega) (by simp [hsegs, sqSegs, hmm])
      (by simp [hsegs, sqSegs])
    obtain ⟨okp2, vp2⟩ := hmat 4 qbp ((osMat 3 lv.posOff (40 + L)).2.2 + 1) 9
      (by simp [hsegs, sqSegs]) (by omega) g4
      (by rw [hp1k]; simp [hsegs, sqSegs, segLen, hL, hmm]; split_ifs <;> omega)
      (by simp [hsegs, sqSegs, hmm])
      (by simp [hsegs, sqSegs])
    have hpwr := osPowSteps_complete (C := C) (rd := rd) (σ := σ) 0
      (osPowDigits (192 / lv.depth)) 0 40 1 (by rw [pow_one]) vpw
    rw [hpw, g0] at hpwr
    have vq1 : σ (.n (osMat 3 lv.posOff (40 + L)).2.2) = qpos * gen ^ lv.posOff * X ^ (192 / lv.depth) := by
      rw [hp1k]
      have := sv 8 (by simp [hsegs, sqSegs]) (40 + L + m)
        (by simp [hsegs, sqSegs, segLen, hL, hmm]; split_ifs <;> omega) 0 (by simp [hsegs, sqSegs])
      rw [Nat.add_zero] at this
      rw [this]; simp [hsegs, sqSegs]
    have vq2 : σ (.n (osMat 4 lv.posOff ((osMat 3 lv.posOff (40 + L)).2.2 + 1)).2.2) =
        qbp * gen ^ lv.posOff * X ^ (192 / lv.depth) := by
      rw [hp2k]
      have := sv 10 (by simp [hsegs, sqSegs]) (40 + L + m + 1 + m)
        (by simp [hsegs, sqSegs, segLen, hL, hmm]; split_ifs <;> omega) 0 (by simp [hsegs, sqSegs])
      rw [Nat.add_zero] at this
      rw [this]; simp [hsegs, sqSegs]
    have k0 : σ (.n 20) = cellsOfState S false 0 := by
      have := vk 0 (by omega); simpa [cells13F] using this
    have k1 : σ (.n 21) = cellsOfState S false 1 := by
      have := vk 1 (by omega); simpa [cells13F] using this
    have hS' : (⟨[10, 11, 12, 13, 14].map fun i ↦ σ (.n i), []⟩ : Fs).perm = S := by rw [← hcm]
    have z1 : σ (.n (15 + 1)) = 0 := by have := vz 1 (by omega); simpa [word_zero] using this
    have z2 : σ (.n (15 + 2)) = 0 := by have := vz 2 (by omega); simpa [word_zero] using this
    have z3 : σ (.n (15 + 3)) = 0 := by have := vz 3 (by omega); simpa [word_zero] using this
    have z4 : σ (.n (15 + 4)) = 0 := by have := vz 4 (by omega); simpa [word_zero] using this
    have hsq := osSqueeze0_complete (C := C) (rd := rd) (σ := σ) (p := 15)
      (cap := [10, 11, 12, 13, 14]) (j := 20) rfl ⟨z1, z2, z3, z4⟩
      (by rw [← hcm]; exact hcan) (fun c hc ↦ by rw [hS']; exact vk c hc)
      (fun i hi ↦ by rw [k0, k1, show 20 + 13 + i = 33 + i by ring, vch i hi, cells13F, cells13F]
                     simp)
    rw [hS'] at hsq
    have h38 : σ (.n 39) = challengeOf S := hsq.2
    refine ⟨?_, by rw [v8]; ring, by simp only [List.map_cons, List.map_nil]; rw [h38, vq1, vq2, g5]⟩
    simp only [sqLoopA, allOk_append]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, hsq.1⟩, ?_⟩, hpwr.1⟩, okp1⟩, ?_⟩, okp2⟩, ?_⟩, ?_⟩, ?_⟩
    · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      exact ⟨by rw [v5, g0], by rw [v6, v5], by rw [v7, v6, g0], by rw [v8, v7, g2]⟩
    · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
        List.cons_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, Nat.add_zero]
      rw [v8, hX5]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · have := vc 0 (by omega); simp at this; rw [this]; exact hrow 0 (by omega)
      · have := vc 1 (by omega); simp at this; rw [this]; exact hrow 1 (by omega)
      · have := vc 2 (by omega); simp at this; rw [this]; exact hrow 2 (by omega)
      · have := vc 3 (by omega); simp at this; rw [this]; exact hrow 3 (by omega)
      · have := vc 4 (by omega); simp at this; rw [this]; exact hrow 4 (by omega)
    · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · have := vz 0 (by omega); simpa using this
      · have := vz 1 (by omega); simpa using this
      · have := vz 2 (by omega); simpa using this
      · have := vz 3 (by omega); simpa using this
      · have := vz 4 (by omega); simpa using this
    · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
        List.cons_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, Nat.add_zero]
      rw [v8, hX5]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · have := vk 8 (by omega); simp [cells13F] at this; rw [this]
        simpa [capOf] using hnext 0 (by omega)
      · have := vk 9 (by omega); simp [cells13F] at this; rw [this]
        simpa [capOf] using hnext 1 (by omega)
      · have := vk 10 (by omega); simp [cells13F] at this; rw [this]
        simpa [capOf] using hnext 2 (by omega)
      · have := vk 11 (by omega); simp [cells13F] at this; rw [this]
        simpa [capOf] using hnext 3 (by omega)
      · have := vk 12 (by omega); simp [cells13F] at this; rw [this]
        simpa [capOf] using hnext 4 (by omega)
    · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      rw [vq1, vp1, hpwr.2]
    · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      rw [vq2, vp2, hpwr.2]
    · simp only [allOk_cons, allOk_nil, and_true, StmtOk, List.map_cons, List.map_nil]
      rw [h38, vq1, vq2, g5]
      exact hdec
    · simp only [osLoopTailA, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      exact ⟨t0, by rw [t1, g0, t0], by rw [t2, t1, g1], t3, by rw [t4, g0, t3]⟩
  · rw [t2, word_gen]
  · show [σ (.n (sqTail lv + 4)), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5)] = _
    rw [t4, word_gen, g1, g2, g3, g4, g5]

/-- **One iteration, honestly.** -/
theorem sqIter_complete (lv : OsLv)
    (hpw : digitsVal (osPowDigits (192 / lv.depth)) 1 = 192 / lv.depth)
    (hpo : lv.posOff < u128Bound)
    (X N sqz qpos qbp tabs : E) (cap : List E) (hcl : cap.length = 5) (hcan : AllCanonical cap)
    (hm : SqIterMem rd lv.depth lv.capDepth lv.posOff sqz qpos qbp tabs X cap) :
    ∃ σ : Val, (osParams 6).map σ = [X, N, sqz, qpos, qbp, tabs] ∧
      AllOk (coreProgram.Rel rd) rd σ (sqLoopA lv ++ osLoopTailA (sqTail lv)) ∧
      σ (.n (sqTail lv + 2)) = X * gen + N ∧
      (.n (sqTail lv + 4) :: (List.range (6 - 1)).map fun i ↦ V.n (i + 1)).map σ =
        X * gen :: [N, sqz, qpos, qbp, tabs] :=
  let h := sqIter_completeC (C := coreProgram.Rel rd) lv hpw hpo X N sqz qpos qbp tabs cap hcl hcan
    hm.row hm.next hm.dec
  ⟨_, h.1, h.2.1.1, h.2.2.1, h.2.2.2⟩

end
end LeanVM.Guest.B1.Whir
