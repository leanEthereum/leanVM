/-
  LeanVM.Guest.B1.Whir.SqIter

  One iteration of `open_stacked`'s squeeze loop at its honest valuation: the body holds.
-/

module

public import LeanVM.Guest.B1.Whir.StackedLoops
public import LeanVM.Guest.B1.Whir.QueriesComplete

/-!
# One squeeze, honestly (TRIAGE #36)

`sqIterVal`: the valuation of the squeeze loop's body (`sqLoopBody`) at `x`, from the chain state
`cv` the loop's state buffer holds at `sqz·x²`: `x²`, the row pointer, the state's cells, the
squeeze's values (`sqVals`), the next state's cells, the power `x^(192/depth)` by
square-and-multiply (`osPowVals`), the positions' and bit runs' pointers, the tail's values.
`sqIter_holds`: on a memory holding the state and the next state at `sqz·x²`, with the decode call
and the tail's call holding, the body holds.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Square-and-multiply -/

/-- The values of `osPowSteps x ds acc k` from `k`, at the base `xv` and the accumulator's value
`av`. -/
def osPowVals (xv : E) : List Bool → E → List E
  | [], _ => []
  | d :: ds, av =>
    if d then [av * av, av * av * xv] ++ osPowVals xv ds (av * av * xv)
    else [av * av] ++ osPowVals xv ds (av * av)

theorem os_length_powVals (xv : E) : ∀ (ds : List Bool) (av : E),
    (osPowVals xv ds av).length = ds.length + (ds.filter id).length
  | [], _ => rfl
  | d :: ds, av => by
    cases d
    · simp [osPowVals, os_length_powVals xv ds]; omega
    · simp [osPowVals, os_length_powVals xv ds]; omega

theorem os_powSteps_next (x : ℕ) : ∀ (ds : List Bool) (acc k : ℕ),
    (osPowSteps x ds acc k).2 = acc ∨ k ≤ (osPowSteps x ds acc k).2
  | [], _, _ => Or.inl rfl
  | d :: ds, acc, k => by
    unfold osPowSteps
    cases d
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rcases os_powSteps_next x ds k (k + 1) with h | h <;> omega
    · simp only [↓reduceIte]
      rcases os_powSteps_next x ds (k + 1) (k + 2) with h | h <;> omega

/-- **Square-and-multiply at its honest values**: from the accumulator `acc` holding `av`, the
values from `k` the steps'. -/
theorem osPowSteps_complete (x : ℕ) {kret : List E → Prop} : ∀ (ds : List Bool) (acc k : ℕ) (av : E),
    σ (.n acc) = av →
    (∀ j < (osPowVals (σ (.n x)) ds av).length, σ (.n (k + j)) = (osPowVals (σ (.n x)) ds av).getD j 0) →
    Stmt.HoldsList C rd σ (osPowSteps x ds acc k).1 True kret
  | [], _, _, _, _, _ => trivial
  | d :: ds, acc, k, av, ha, hv => by
    unfold osPowSteps
    cases d
    · simp only [Bool.false_eq_true, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
      have h0 := hv 0 (by simp [osPowVals])
      simp only [osPowVals, Bool.false_eq_true, ↓reduceIte, List.singleton_append, List.getD_cons_zero,
        Nat.add_zero] at h0
      refine ⟨by rw [h0, ha], osPowSteps_complete x ds k (k + 1) (av * av) h0 fun j hj => ?_⟩
      have := hv (j + 1) (by simp [osPowVals]; omega)
      simpa [osPowVals, show k + (j + 1) = k + 1 + j by ring] using this
    · simp only [↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
      have h0 := hv 0 (by simp [osPowVals])
      have h1 := hv 1 (by simp [osPowVals])
      simp only [osPowVals, ↓reduceIte, List.cons_append, List.nil_append, List.getD_cons_zero,
        List.getD_cons_succ, Nat.add_zero] at h0 h1
      refine ⟨by rw [h0, ha], by rw [h1, h0], osPowSteps_complete x ds (k + 1) (k + 2) (av * av * σ (.n x)) h1
        fun j hj => ?_⟩
      have := hv (j + 2) (by simp [osPowVals]; omega)
      simpa [osPowVals, show k + (j + 2) = k + 2 + j by ring] using this

/-! ## The pointers -/

/-- The values of `sqPtr posOff q base k` from `k`, at the base `bv` and `qv`. -/
def sqPtrVals (posOff : ℕ) (bv qv : E) : List E :=
  if posOff = 0 then [bv * qv] else [osGw posOff, bv * osGw posOff, bv * osGw posOff * qv]

theorem sqPtr_complete {posOff q base k : ℕ} {kret : List E → Prop}
    (hv : ∀ j < (sqPtrVals posOff (σ (.n base)) (σ (.n q))).length,
      σ (.n (k + j)) = (sqPtrVals posOff (σ (.n base)) (σ (.n q))).getD j 0) :
    Stmt.HoldsList C rd σ (sqPtr posOff q base k).1 True kret := by
  unfold sqPtr
  by_cases h0 : posOff = 0
  · have e0 := hv 0 (by simp [sqPtrVals, h0])
    simp only [sqPtrVals, h0, ↓reduceIte, List.getD_cons_zero, Nat.add_zero] at e0
    simp only [h0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact e0
  · have e0 := hv 0 (by simp [sqPtrVals, h0])
    have e1 := hv 1 (by simp [sqPtrVals, h0])
    have e2 := hv 2 (by simp [sqPtrVals, h0])
    simp only [sqPtrVals, h0, ↓reduceIte, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1 e2
    simp only [h0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨e0, by rw [e1, e0], by rw [e2, e1]⟩

theorem sqPtr_index (posOff q base k : ℕ) :
    (sqPtr posOff q base k).2.1 = k + (sqPtrVals posOff 0 0).length - 1 ∧
      (sqPtr posOff q base k).2.2 = k + (sqPtrVals posOff 0 0).length := by
  unfold sqPtr sqPtrVals; split <;> simp

/-! ## The valuation -/

/-- The body's power `x^(192/depth)` steps. -/
def sqPw (lv : OsLvl) : List Stmt × ℕ := osPowSteps 0 (osPowDigits (192 / lv.depth)) 0 27

/-- The first value after the power. -/
def sqK (lv : OsLvl) : ℕ :=
  27 + (osPowDigits (192 / lv.depth)).length + ((osPowDigits (192 / lv.depth)).filter id).length

/-- The positions' and bit runs' pointers. -/
def sqP1 (lv : OsLvl) : List Stmt × ℕ × ℕ := sqPtr lv.posOff (sqPw lv).2 3 (sqK lv)
def sqP2 (lv : OsLvl) : List Stmt × ℕ × ℕ := sqPtr lv.posOff (sqPw lv).2 4 (sqP1 lv).2.2

/-- The first value of the tail. -/
def sqE (lv : OsLvl) : ℕ := (sqP2 lv).2.2

/-- **The squeeze loop's body's valuation at `x`**, from the state `cv` at `sqz·x²`. -/
def sqIterVal (lv : OsLvl) (x N sqz qpos qbp : E) (cv : Digest) : Val :=
  let q := x ^ osDigitsVal 1 (osPowDigits (192 / lv.depth))
  setl (Val.ofArgs [x, N, sqz, qpos, qbp]) 5
    ([x * x, sqz * (x * x), (digestScalars cv).1, (digestScalars cv).2, (digestScalars cv).1,
      (digestScalars cv).2] ++ (List.range 14).map (sqVals cv) ++ [sqVals cv 5, sqVals cv 6] ++
      osPowVals x (osPowDigits (192 / lv.depth)) x ++ sqPtrVals lv.posOff qpos q ++
      sqPtrVals lv.posOff qbp q ++ [gen, x * gen, x * gen + N, gen, x * gen])

theorem sqLoopOf_eq (lv : OsLvl) : sqLoopOf lv =
    [.atom (.mul (.n 5) (.n 0) (.n 0)), .atom (.mul (.n 6) (.n 2) (.n 5)),
      .atom (.load (.n 7) (.n 6) 0), .atom (.load (.n 8) (.n 6) 1),
      .atom (.copy (.n 9) (.n 7)), .atom (.copy (.n 10) (.n 8))] ++ squeezeT (.n 9) (.n 10) 11 ++
    [.atom (.copy (.n 25) (.n 16)), .atom (.copy (.n 26) (.n 17)),
      .atom (.load (.n 25) (.n 6) 2), .atom (.load (.n 26) (.n 6) 3)] ++ (sqPw lv).1 ++ (sqP1 lv).1 ++
    (sqP2 lv).1 ++
    [.call lv.decode [.n 24, .n (sqP1 lv).2.1, .n (sqP2 lv).2.1] [],
      .atom (.const (.n (sqE lv)) (word 2 0 0)), .atom (.mul (.n (sqE lv + 1)) (.n 0) (.n (sqE lv))),
      .atom (.add (.n (sqE lv + 2)) (.n (sqE lv + 1)) (.n 1)), .atom (.const (.n (sqE lv + 3)) (word 2 0 0)),
      .atom (.mul (.n (sqE lv + 4)) (.n 0) (.n (sqE lv + 3))),
      .callIf (.n (sqE lv + 2)) lv.sqLoop [.n (sqE lv + 4), .n 1, .n 2, .n 3, .n 4], .ret []] := rfl

theorem sqK_eq (lv : OsLvl) (xv av : E) :
    sqK lv = 27 + (osPowVals xv (osPowDigits (192 / lv.depth)) av).length := by
  rw [sqK, os_length_powVals]; ring

/-- **One squeeze's body holds** at `sqIterVal`, on a memory holding the state `cv` and the next
state at `sqz·x²`, the decode call and the tail's call holding. -/
theorem sqIter_holds {lv : OsLvl} (hpo : lv.posOff < 2 ^ 128)
    (hdig : osDigitsVal 1 (osPowDigits (192 / lv.depth)) = 192 / lv.depth) {x N sqz qpos qbp : E}
    {cv : Digest}
    (l0 : LoadHolds rd (sqz * (x * x)) 0 (digestScalars cv).1)
    (l1 : LoadHolds rd (sqz * (x * x)) 1 (digestScalars cv).2)
    (l2 : LoadHolds rd (sqz * (x * x)) 2 (digestScalars (sqCv cv)).1)
    (l3 : LoadHolds rd (sqz * (x * x)) 3 (digestScalars (sqCv cv)).2)
    (hdec : C lv.decode [challengeOf (sqCv cv), qpos * gen ^ lv.posOff * x ^ (192 / lv.depth),
      qbp * gen ^ lv.posOff * x ^ (192 / lv.depth)] [])
    (hK : IsInK (x * gen + N)) (hcall : x * gen + N ≠ 0 → C lv.sqLoop [x * gen, N, sqz, qpos, qbp] []) :
    Stmt.HoldsList C rd (sqIterVal lv x N sqz qpos qbp cv) (sqLoopOf lv) False (fun rs => rs = []) := by
  set q := x ^ osDigitsVal 1 (osPowDigits (192 / lv.depth)) with hq
  set pv := osPowVals x (osPowDigits (192 / lv.depth)) x
  set P1 := sqPtrVals lv.posOff qpos q
  set P2 := sqPtrVals lv.posOff qbp q
  set A : List E := [x * x, sqz * (x * x), (digestScalars cv).1, (digestScalars cv).2,
      (digestScalars cv).1, (digestScalars cv).2] with hA
  set S : List E := (List.range 14).map (sqVals cv) with hS
  set B : List E := [sqVals cv 5, sqVals cv 6] with hB
  set T : List E := [gen, x * gen, x * gen + N, gen, x * gen] with hT
  set vals : List E := A ++ (S ++ (B ++ (pv ++ (P1 ++ (P2 ++ T))))) with hvals
  set σ := sqIterVal lv x N sqz qpos qbp cv with hσ
  have hσ' : σ = setl (Val.ofArgs [x, N, sqz, qpos, qbp]) 5 vals := by
    rw [hσ, sqIterVal]; simp only [vals, A, S, B, T, P1, P2, pv, q, List.append_assoc]
  have larg : ∀ i < 5, σ (.n i) = [x, N, sqz, qpos, qbp].getD i 0 := fun i hi => by
    rw [hσ']; simp only [setl]; rw [set_n_lt (by omega)]; rfl
  have lv' : ∀ off < vals.length, σ (.n (5 + off)) = vals.getD off 0 := fun off ho => by
    rw [hσ']; simp only [setl]; rw [set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have hlen1 : ∀ v, (sqPtrVals lv.posOff v q).length = (sqPtrVals lv.posOff 0 0).length := by
    intro v; unfold sqPtrVals; split <;> simp
  have lA : A.length = 6 := rfl
  have lS : S.length = 14 := by simp [S]
  have lB : B.length = 2 := rfl
  have lT : T.length = 5 := rfl
  have skip : ∀ (l l' : List E) (n : ℕ), (l ++ l').getD (l.length + n) 0 = l'.getD n 0 := fun l l' n => by
    rw [oq_getD_app_ge (by omega), Nat.add_sub_cancel_left]
  have hvl : vals.length = 22 + pv.length + P1.length + P2.length + 5 := by
    simp only [vals, List.length_append, lA, lS, lB, lT]; omega
  have gA : ∀ t < 6, σ (.n (5 + t)) = A.getD t 0 := fun t ht => by
    rw [lv' t (by omega), hvals, oq_getD_app_lt (by omega)]
  have gS : ∀ t < 14, σ (.n (11 + t)) = sqVals cv t := fun t ht => by
    rw [show 11 + t = 5 + (A.length + t) by rw [lA]; ring, lv' _ (by omega), hvals, skip,
      oq_getD_app_lt (by omega)]
    simp [S, List.getD_eq_getElem?_getD, ht]
  have gB : σ (.n 25) = sqVals cv 5 ∧ σ (.n 26) = sqVals cv 6 := by
    refine ⟨?_, ?_⟩
    · rw [show 25 = 5 + (A.length + (S.length + 0)) by rw [lA, lS], lv' _ (by omega), hvals, skip, skip]; rfl
    · rw [show 26 = 5 + (A.length + (S.length + 1)) by rw [lA, lS], lv' _ (by omega), hvals, skip, skip]; rfl
  have gP : ∀ t < pv.length, σ (.n (27 + t)) = pv.getD t 0 := fun t ht => by
    rw [show 27 + t = 5 + (A.length + (S.length + (B.length + t))) by rw [lA, lS, lB]; ring, lv' _ (by omega),
      hvals, skip, skip, skip, oq_getD_app_lt (by omega)]
  have hk : sqK lv = 27 + pv.length := sqK_eq lv x x
  have gP1 : ∀ t < P1.length, σ (.n (sqK lv + t)) = P1.getD t 0 := fun t ht => by
    rw [hk, show 27 + pv.length + t = 5 + (A.length + (S.length + (B.length + (pv.length + t)))) by
      rw [lA, lS, lB]; ring, lv' _ (by omega), hvals, skip, skip, skip, skip, oq_getD_app_lt (by omega)]
  have hp1 := sqPtr_index lv.posOff (sqPw lv).2 3 (sqK lv)
  have gP2 : ∀ t < P2.length, σ (.n ((sqP1 lv).2.2 + t)) = P2.getD t 0 := fun t ht => by
    rw [show (sqP1 lv).2.2 = sqK lv + P1.length by rw [sqP1, hp1.2, hlen1], hk,
      show 27 + pv.length + P1.length + t = 5 + (A.length + (S.length + (B.length + (pv.length + (P1.length + t)))))
        by rw [lA, lS, lB]; ring, lv' _ (by omega), hvals, skip, skip, skip, skip, skip, oq_getD_app_lt (by omega)]
  have hp2 := sqPtr_index lv.posOff (sqPw lv).2 4 (sqP1 lv).2.2
  have hE : sqE lv = sqK lv + P1.length + P2.length := by
    rw [sqE, sqP2, hp2.2, sqP1, hp1.2, hlen1, hlen1]
  have gT : ∀ t < 5, σ (.n (sqE lv + t)) = T.getD t 0 := fun t ht => by
    rw [hE, hk, show 27 + pv.length + P1.length + P2.length + t =
      5 + (A.length + (S.length + (B.length + (pv.length + (P1.length + (P2.length + t)))))) by
        rw [lA, lS, lB]; ring, lv' _ (by omega), hvals, skip, skip, skip, skip, skip, skip]
  have a0 : σ (.n 0) = x := larg 0 (by omega)
  have a1 : σ (.n 1) = N := larg 1 (by omega)
  have a2 : σ (.n 2) = sqz := larg 2 (by omega)
  have a3 : σ (.n 3) = qpos := larg 3 (by omega)
  have a4 : σ (.n 4) = qbp := larg 4 (by omega)
  -- the power
  have hpw : Stmt.HoldsList C rd σ (sqPw lv).1 True (fun rs => rs = []) := by
    refine osPowSteps_complete 0 _ 0 27 x a0 fun j hj => ?_
    rw [a0]; exact gP j (by rw [a0] at hj; exact hj)
  have hqv : σ (.n (sqPw lv).2) = q := by
    have := osPowSteps_sound (C := C) (rd := rd) (σ := σ) 0 _ 0 27 1 (by rw [pow_one, a0]) hpw
    rw [show (sqPw lv).2 = (osPowSteps 0 (osPowDigits (192 / lv.depth)) 0 27).2 from rfl, this, a0]
  rw [sqLoopOf_eq]
  simp only [holdsList_append]
  refine (holdsList_noRet _ rfl _ _).mpr ⟨?_, ?_⟩
  · have e0 := gA 0 (by omega); have e1 := gA 1 (by omega); have e2 := gA 2 (by omega)
    have e3 := gA 3 (by omega); have e4 := gA 4 (by omega); have e5 := gA 5 (by omega)
    simp only [hA, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd] at e0 e1 e2 e3 e4 e5
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    refine ⟨by rw [e0, a0], by rw [e1, a2, e0], by rw [e1, e2]; exact l0, by rw [e1, e3]; exact l1,
      by rw [e4, e2], by rw [e5, e3]⟩
  refine (holdsList_noRet _ (by simp [squeezeT, squeezeStateT, challengeT, Stmt.noRetList, Stmt.noRet]) _ _).mpr
    ⟨?_, ?_⟩
  · have e4 := gA 4 (by omega); have e5 := gA 5 (by omega)
    simp only [hA, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd] at e4 e5
    refine (holds_squeezeT _ _ _ _ _).mpr ⟨⟨cv, by rw [e4, e5], fun t ht => gS t ht⟩, trivial⟩
  refine (holdsList_noRet _ rfl _ _).mpr ⟨?_, ?_⟩
  · have e1 := gA 1 (by omega)
    simp only [hA, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd] at e1
    have s5 := gS 5 (by omega); have s6 := gS 6 (by omega)
    simp only [Nat.reduceAdd] at s5 s6
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    refine ⟨by rw [gB.1, s5], by rw [gB.2, s6], by rw [e1, gB.1]; exact l2, by rw [e1, gB.2]; exact l3⟩
  refine (holdsList_noRet _ (osPowSteps_noRet _ _ _ _) _ _).mpr ⟨hpw, ?_⟩
  have hpv1 : σ (.n (sqP1 lv).2.1) = qpos * gen ^ lv.posOff * x ^ (192 / lv.depth) := by
    have := sqPtr_sound (C := C) (rd := rd) (σ := σ) hpo (sqPtr_complete (kret := fun rs => rs = [])
      (posOff := lv.posOff) (q := (sqPw lv).2) (base := 3) (k := sqK lv) fun j hj => by rw [a3, hqv]; exact gP1 j (by rw [a3, hqv] at hj; exact hj))
    rw [sqP1, this, a3, hqv, hq, hdig]
  have hpv2 : σ (.n (sqP2 lv).2.1) = qbp * gen ^ lv.posOff * x ^ (192 / lv.depth) := by
    have := sqPtr_sound (C := C) (rd := rd) (σ := σ) hpo (sqPtr_complete (kret := fun rs => rs = [])
      (posOff := lv.posOff) (q := (sqPw lv).2) (base := 4) (k := (sqP1 lv).2.2) fun j hj => by rw [a4, hqv]; exact gP2 j (by rw [a4, hqv] at hj; exact hj))
    rw [sqP2, this, a4, hqv, hq, hdig]
  refine (holdsList_noRet _ (sqPtr_noRet _ _ _ _) _ _).mpr ⟨sqPtr_complete fun j hj => ?_, ?_⟩
  · rw [a3, hqv]; exact gP1 j (by rw [a3, hqv] at hj; exact hj)
  refine (holdsList_noRet _ (sqPtr_noRet _ _ _ _) _ _).mpr ⟨sqPtr_complete fun j hj => ?_, ?_⟩
  · rw [a4, hqv]; exact gP2 j (by rw [a4, hqv] at hj; exact hj)
  have t0 := gT 0 (by omega); have t1 := gT 1 (by omega); have t2 := gT 2 (by omega)
  have t3 := gT 3 (by omega); have t4 := gT 4 (by omega)
  simp only [hT, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at t0 t1 t2 t3 t4
  have s13 := gS 13 (by omega)
  simp only [Nat.reduceAdd] at s13
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen]
  refine ⟨?_, t0, by rw [t1, a0, t0], by rw [t2, t1, a1], t3, by rw [t4, a0, t3], by rw [t2]; exact hK,
    fun h => ?_, trivial⟩
  · rw [s13, hpv1, hpv2]; exact hdec
  · rw [t4, a1, a2, a3, a4]
    exact hcall (by rwa [t2] at h)

/-- **The pointers and arguments of one squeeze** at `sqIterVal`: the row, the challenge, the
positions' and bit runs' pointers, the tail's condition and argument. -/
theorem sqIterVal_ptrs {lv : OsLvl} (hpo : lv.posOff < 2 ^ 128)
    (hdig : osDigitsVal 1 (osPowDigits (192 / lv.depth)) = 192 / lv.depth) (x N sqz qpos qbp : E)
    (cv : Digest) :
    (∀ i < 5, sqIterVal lv x N sqz qpos qbp cv (.n i) = [x, N, sqz, qpos, qbp].getD i 0) ∧
      sqIterVal lv x N sqz qpos qbp cv (.n 6) = sqz * (x * x) ∧
      sqIterVal lv x N sqz qpos qbp cv (.n 24) = challengeOf (sqCv cv) ∧
      sqIterVal lv x N sqz qpos qbp cv (.n (sqP1 lv).2.1) = qpos * gen ^ lv.posOff * x ^ (192 / lv.depth) ∧
      sqIterVal lv x N sqz qpos qbp cv (.n (sqP2 lv).2.1) = qbp * gen ^ lv.posOff * x ^ (192 / lv.depth) ∧
      sqIterVal lv x N sqz qpos qbp cv (.n (sqE lv + 2)) = x * gen + N ∧
      sqIterVal lv x N sqz qpos qbp cv (.n (sqE lv + 4)) = x * gen := by
  set q := x ^ osDigitsVal 1 (osPowDigits (192 / lv.depth)) with hq
  set pv := osPowVals x (osPowDigits (192 / lv.depth)) x
  set P1 := sqPtrVals lv.posOff qpos q
  set P2 := sqPtrVals lv.posOff qbp q
  set A : List E := [x * x, sqz * (x * x), (digestScalars cv).1, (digestScalars cv).2,
      (digestScalars cv).1, (digestScalars cv).2] with hA
  set S : List E := (List.range 14).map (sqVals cv) with hS
  set B : List E := [sqVals cv 5, sqVals cv 6] with hB
  set T : List E := [gen, x * gen, x * gen + N, gen, x * gen] with hT
  set vals : List E := A ++ (S ++ (B ++ (pv ++ (P1 ++ (P2 ++ T))))) with hvals
  set σ := sqIterVal lv x N sqz qpos qbp cv with hσ
  have hσ' : σ = setl (Val.ofArgs [x, N, sqz, qpos, qbp]) 5 vals := by
    rw [hσ, sqIterVal]; simp only [vals, A, S, B, T, P1, P2, pv, q, List.append_assoc]
  have larg : ∀ i < 5, σ (.n i) = [x, N, sqz, qpos, qbp].getD i 0 := fun i hi => by
    rw [hσ']; simp only [setl]; rw [set_n_lt (by omega)]; rfl
  have lv' : ∀ off < vals.length, σ (.n (5 + off)) = vals.getD off 0 := fun off ho => by
    rw [hσ']; simp only [setl]; rw [set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have hlen1 : ∀ v, (sqPtrVals lv.posOff v q).length = (sqPtrVals lv.posOff 0 0).length := by
    intro v; unfold sqPtrVals; split <;> simp
  have lA : A.length = 6 := rfl
  have lS : S.length = 14 := by simp [S]
  have lB : B.length = 2 := rfl
  have lT : T.length = 5 := rfl
  have skip : ∀ (l l' : List E) (n : ℕ), (l ++ l').getD (l.length + n) 0 = l'.getD n 0 := fun l l' n => by
    rw [oq_getD_app_ge (by omega), Nat.add_sub_cancel_left]
  have hvl : vals.length = 22 + pv.length + P1.length + P2.length + 5 := by
    simp only [vals, List.length_append, lA, lS, lB, lT]; omega
  have gA : ∀ t < 6, σ (.n (5 + t)) = A.getD t 0 := fun t ht => by
    rw [lv' t (by omega), hvals, oq_getD_app_lt (by omega)]
  have gS : ∀ t < 14, σ (.n (11 + t)) = sqVals cv t := fun t ht => by
    rw [show 11 + t = 5 + (A.length + t) by rw [lA]; ring, lv' _ (by omega), hvals, skip,
      oq_getD_app_lt (by omega)]
    simp [S, List.getD_eq_getElem?_getD, ht]
  have gB : σ (.n 25) = sqVals cv 5 ∧ σ (.n 26) = sqVals cv 6 := by
    refine ⟨?_, ?_⟩
    · rw [show 25 = 5 + (A.length + (S.length + 0)) by rw [lA, lS], lv' _ (by omega), hvals, skip, skip]; rfl
    · rw [show 26 = 5 + (A.length + (S.length + 1)) by rw [lA, lS], lv' _ (by omega), hvals, skip, skip]; rfl
  have gP : ∀ t < pv.length, σ (.n (27 + t)) = pv.getD t 0 := fun t ht => by
    rw [show 27 + t = 5 + (A.length + (S.length + (B.length + t))) by rw [lA, lS, lB]; ring, lv' _ (by omega),
      hvals, skip, skip, skip, oq_getD_app_lt (by omega)]
  have hk : sqK lv = 27 + pv.length := sqK_eq lv x x
  have gP1 : ∀ t < P1.length, σ (.n (sqK lv + t)) = P1.getD t 0 := fun t ht => by
    rw [hk, show 27 + pv.length + t = 5 + (A.length + (S.length + (B.length + (pv.length + t)))) by
      rw [lA, lS, lB]; ring, lv' _ (by omega), hvals, skip, skip, skip, skip, oq_getD_app_lt (by omega)]
  have hp1 := sqPtr_index lv.posOff (sqPw lv).2 3 (sqK lv)
  have gP2 : ∀ t < P2.length, σ (.n ((sqP1 lv).2.2 + t)) = P2.getD t 0 := fun t ht => by
    rw [show (sqP1 lv).2.2 = sqK lv + P1.length by rw [sqP1, hp1.2, hlen1], hk,
      show 27 + pv.length + P1.length + t = 5 + (A.length + (S.length + (B.length + (pv.length + (P1.length + t)))))
        by rw [lA, lS, lB]; ring, lv' _ (by omega), hvals, skip, skip, skip, skip, skip, oq_getD_app_lt (by omega)]
  have hp2 := sqPtr_index lv.posOff (sqPw lv).2 4 (sqP1 lv).2.2
  have hE : sqE lv = sqK lv + P1.length + P2.length := by
    rw [sqE, sqP2, hp2.2, sqP1, hp1.2, hlen1, hlen1]
  have gT : ∀ t < 5, σ (.n (sqE lv + t)) = T.getD t 0 := fun t ht => by
    rw [hE, hk, show 27 + pv.length + P1.length + P2.length + t =
      5 + (A.length + (S.length + (B.length + (pv.length + (P1.length + (P2.length + t)))))) by
        rw [lA, lS, lB]; ring, lv' _ (by omega), hvals, skip, skip, skip, skip, skip, skip]
  have a0 : σ (.n 0) = x := larg 0 (by omega)
  have a1 : σ (.n 1) = N := larg 1 (by omega)
  have a2 : σ (.n 2) = sqz := larg 2 (by omega)
  have a3 : σ (.n 3) = qpos := larg 3 (by omega)
  have a4 : σ (.n 4) = qbp := larg 4 (by omega)
  have hpw : Stmt.HoldsList (fun _ _ _ => True) (fun _ => none) σ (sqPw lv).1 True (fun rs => rs = []) := by
    refine osPowSteps_complete 0 _ 0 27 x (larg 0 (by omega)) fun j hj => ?_
    rw [larg 0 (by omega)]; exact gP j (by rw [larg 0 (by omega)] at hj; exact hj)
  have hqv : σ (.n (sqPw lv).2) = q := by
    have := osPowSteps_sound (C := fun _ _ _ => True) (rd := fun _ => none) (σ := σ) 0 _ 0 27 1
      (by rw [pow_one, larg 0 (by omega)]) hpw
    rw [show (sqPw lv).2 = (osPowSteps 0 (osPowDigits (192 / lv.depth)) 0 27).2 from rfl, this, a0]
  have a3 : σ (.n 3) = qpos := larg 3 (by omega)
  have a4 : σ (.n 4) = qbp := larg 4 (by omega)
  have e1 := gA 1 (by omega)
  simp only [hA, List.getD_cons_zero, List.getD_cons_succ] at e1
  have s13 := gS 13 (by omega)
  have t2 := gT 2 (by omega); have t4 := gT 4 (by omega)
  simp only [hT, List.getD_cons_zero, List.getD_cons_succ] at t2 t4
  refine ⟨larg, e1, s13, ?_, ?_, t2, t4⟩
  · have := sqPtr_sound (C := fun _ _ _ => True) (rd := fun _ => none) (σ := σ) hpo (sqPtr_complete (kret := fun rs => rs = [])
      (posOff := lv.posOff) (q := (sqPw lv).2) (base := 3) (k := sqK lv) fun j hj => by rw [a3, hqv]; exact gP1 j (by rw [a3, hqv] at hj; exact hj))
    rw [sqP1, this, a3, hqv, hq, hdig]
  · have := sqPtr_sound (C := fun _ _ _ => True) (rd := fun _ => none) (σ := σ) hpo (sqPtr_complete (kret := fun rs => rs = [])
      (posOff := lv.posOff) (q := (sqPw lv).2) (base := 4) (k := (sqP1 lv).2.2) fun j hj => by rw [a4, hqv]; exact gP2 j (by rw [a4, hqv] at hj; exact hj))
    rw [sqP2, this, a4, hqv, hq, hdig]

end
end LeanVM.Guest.B1
