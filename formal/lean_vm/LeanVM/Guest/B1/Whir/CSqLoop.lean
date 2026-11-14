/-
  LeanVM.Guest.B1.Whir.CSqLoop

  One iteration of `open_stacked`'s squeeze loop at its honest values.
-/

module

public import LeanVM.Guest.B1.Whir.SqLoop

/-!
# The squeeze loop's iteration, honestly

`SqIterC' lv`: at `x = X`, on a memory holding the capacity `cap` at the row `sqz·X^5` and its
squeeze's next capacity after it, some valuation of the iteration's parameters
`X, N, sqz, qpos, qbp, tabs` makes the body before its tail's `callIf` hold (every call
unconstrained), the row at `sqz·X^5`, the decoder called on the squeeze's challenge and the
pointers `qpos·g^po·X^(128/d)`, `qbp·g^po·X^(128/d)`, and the tail on `X·g`, its guard `X·g + N`.
`sqIterC'_holds`: it holds at every level row whose power digits read `128/d` and whose position
offset is a word.

* `powVals`, `powRes`, `powSteps_ok`: the square-and-multiply steps at their values.
* `sqTab`: the iteration's values, segment by segment.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## Square and multiply, honestly -/

/-- The values `osPowSteps x ds acc k` writes, from `acc`'s value `a`, `x`'s value `xv`. -/
def powVals (xv : E) : List Bool → E → ℕ → ℕ → E
  | [], _, _, _ => 0
  | true :: ds, a, k, i =>
    if i = k then a * a else if i = k + 1 then a * a * xv else powVals xv ds (a * a * xv) (k + 2) i
  | false :: ds, a, k, i => if i = k then a * a else powVals xv ds (a * a) (k + 1) i

/-- The value they end at. -/
def powRes (xv : E) : List Bool → E → E
  | [], a => a
  | true :: ds, a => powRes xv ds (a * a * xv)
  | false :: ds, a => powRes xv ds (a * a)

/-- The values they take. -/
def powLen (ds : List Bool) : ℕ := ds.length + (ds.filter id).length

theorem powLen_true (ds : List Bool) : powLen (true :: ds) = powLen ds + 2 := by
  simp [powLen]
  omega

theorem powLen_false (ds : List Bool) : powLen (false :: ds) = powLen ds + 1 := by
  simp [powLen]
  omega

theorem powRes_eq (xv : E) : ∀ (ds : List Bool) (n : ℕ), powRes xv ds (xv ^ n) = xv ^ digitsVal ds n
  | [], _ => rfl
  | true :: ds, n => by
    rw [powRes, show xv ^ n * xv ^ n * xv = xv ^ (2 * n + 1) by ring, powRes_eq xv ds]; rfl
  | false :: ds, n => by
    rw [powRes, show xv ^ n * xv ^ n = xv ^ (2 * n + 0) by ring, powRes_eq xv ds]; rfl

/-- **The square-and-multiply steps hold at their values.** -/
theorem powSteps_ok (x : ℕ) : ∀ (ds : List Bool) (acc k : ℕ) (a : E) (σ : Val), acc < k → x < k →
    σ (.n acc) = a →
    (∀ i, k ≤ i → i < k + powLen ds → σ (.n i) = powVals (σ (.n x)) ds a k i) →
    AllOk C rd σ (osPowSteps x ds acc k).1 ∧
      σ (.n (osPowSteps x ds acc k).2) = powRes (σ (.n x)) ds a
  | [], _, _, _, _, _, _, ha, _ => ⟨allOk_nil, ha⟩
  | true :: ds, acc, k, a, σ, hak, hxk, ha, hv => by
    rw [powLen_true] at hv
    have e0 : σ (.n k) = a * a := by rw [hv k le_rfl (by omega)]; simp [powVals]
    have e1 : σ (.n (k + 1)) = a * a * σ (.n x) := by
      rw [hv (k + 1) (by omega) (by omega)]; simp [powVals]
    have ih := powSteps_ok x ds (k + 1) (k + 2) (a * a * σ (.n x)) σ (by omega) (by omega) e1
      fun i h1 h2 ↦ by
        rw [hv i (by omega) (by omega)]
        simp [powVals, show i ≠ k by omega, show i ≠ k + 1 by omega]
    simp only [osPowSteps, ↓reduceIte, osMul]
    refine ⟨allOk_cons.mpr ⟨?_, allOk_cons.mpr ⟨?_, ih.1⟩⟩, ih.2⟩
    · show σ (.n k) = σ (.n acc) * σ (.n acc); rw [e0, ha]
    · show σ (.n (k + 1)) = σ (.n k) * σ (.n x); rw [e1, e0]
  | false :: ds, acc, k, a, σ, hak, hxk, ha, hv => by
    rw [powLen_false] at hv
    have e0 : σ (.n k) = a * a := by rw [hv k le_rfl (by omega)]; simp [powVals]
    have ih := powSteps_ok x ds k (k + 1) (a * a) σ (by omega) (by omega) e0
      fun i h1 h2 ↦ by
        rw [hv i (by omega) (by omega)]
        simp [powVals, show i ≠ k by omega]
    simp only [osPowSteps, Bool.false_eq_true, ↓reduceIte, osMul]
    refine ⟨allOk_cons.mpr ⟨?_, ih.1⟩, ih.2⟩
    show σ (.n k) = σ (.n acc) * σ (.n acc); rw [e0, ha]

/-! ## A materialized pointer, honestly -/

/-- The values `osMat` writes from `k`: `g^off`, then the base's value times it. -/
def matTab (bv : E) (off k i : ℕ) : E := if i = k then gw off else bv * gw off

/-- The values `osMat` takes. -/
def matLen (off : ℕ) : ℕ := if off = 0 then 0 else 2

theorem osMat_end (b off k : ℕ) : (osMat b off k).2.2 = k + matLen off := by
  unfold osMat matLen; split_ifs <;> rfl

theorem osMat_ok {σ : Val} {b off k : ℕ} (hoff : off < u128Bound)
    (hv : ∀ i, k ≤ i → i < k + matLen off → σ (.n i) = matTab (σ (.n b)) off k i) :
    AllOk C rd σ (osMat b off k).1 ∧ σ (.n (osMat b off k).2.1) = σ (.n b) * gen ^ off := by
  by_cases h0 : off = 0
  · subst h0; simp [osMat, allOk_nil]
  · simp only [matLen, h0, ↓reduceIte] at hv
    have e0 : σ (.n k) = gw off := by rw [hv k le_rfl (by omega)]; simp [matTab]
    have e1 : σ (.n (k + 1)) = σ (.n b) * gw off := by
      rw [hv (k + 1) (by omega) (by omega)]; simp [matTab]
    simp only [osMat, h0, ↓reduceIte, osCst, osMul, allOk_cons, allOk_nil, and_true]
    refine ⟨⟨e0, ?_⟩, by rw [e1, gw_eq hoff]⟩
    show σ (.n (k + 1)) = σ (.n b) * σ (.n k)
    rw [e1, e0]

/-! ## The iteration's values -/

/-- The permutation an iteration squeezes. -/
abbrev sqPerm (cap : List E) : KeccakState := (⟨cap, []⟩ : Fs).perm

/-- The iteration's values from `6`: the row's power and pointer, the capacity cells, the
padding, the permutation's cells and the challenge's copy. -/
def sqHead (X sqz : E) (cap : List E) : List E :=
  [X * X, X * X * (X * X), X * X * (X * X) * X, sqz * (X * X * (X * X) * X),
    cap.getD 0 0, cap.getD 1 0, cap.getD 2 0, cap.getD 3 0, cap.getD 4 0,
    word 1 0, word 0 0, word 0 0, word 0 0, word 0 0,
    cellsOfState (sqPerm cap) false 0, cellsOfState (sqPerm cap) false 1,
    cellsOfState (sqPerm cap) false 2, cellsOfState (sqPerm cap) false 3,
    cellsOfState (sqPerm cap) false 4, cellsOfState (sqPerm cap) false 5,
    cellsOfState (sqPerm cap) false 6, cellsOfState (sqPerm cap) false 7,
    cellsOfState (sqPerm cap) false 8, cellsOfState (sqPerm cap) false 9,
    cellsOfState (sqPerm cap) false 10, cellsOfState (sqPerm cap) false 11,
    cellsOfState (sqPerm cap) false 12, cellsOfState (sqPerm cap) false 0]

/-- Where the iteration's segments start: after the powers, after the positions' pointer, after
the window pointers' pointer. -/
def sqK1 (lv : OsLv) : ℕ := 34 + powLen (osPowDigits (128 / lv.depth))
def sqM1 (lv : OsLv) : ℕ := sqK1 lv + matLen lv.posOff
def sqM2 (lv : OsLv) : ℕ := sqM1 lv + 1 + matLen lv.posOff

theorem sqK1_eq (lv : OsLv) : 34 + osPowLen (128 / lv.depth) = sqK1 lv := rfl

theorem sqLoopE_eq (lv : OsLv) : sqLoopE lv = sqM2 lv + 1 := by
  simp only [sqLoopE, osMat_end, sqM2, sqM1, sqK1_eq]

/-- **The iteration's values**, segment by segment. -/
def sqTab (lv : OsLv) (X N sqz qpos qbp tabs : E) (cap : List E) (i : ℕ) : E :=
  if i < 6 then [X, N, sqz, qpos, qbp, tabs].getD i 0
  else if i < 34 then (sqHead X sqz cap).getD (i - 6) 0
  else if i < sqK1 lv then powVals X (osPowDigits (128 / lv.depth)) X 34 i
  else if i < sqM1 lv then matTab qpos lv.posOff (sqK1 lv) i
  else if i = sqM1 lv then qpos * gen ^ lv.posOff * powRes X (osPowDigits (128 / lv.depth)) X
  else if i < sqM2 lv then matTab qbp lv.posOff (sqM1 lv + 1) i
  else if i = sqM2 lv then qbp * gen ^ lv.posOff * powRes X (osPowDigits (128 / lv.depth)) X
  else [gw 1, X * gw 1, X * gw 1 + N, gw 1, X * gw 1].getD (i - (sqM2 lv + 1)) 0

/-- The iteration's valuation. -/
def sqVal (lv : OsLv) (X N sqz qpos qbp tabs : E) (cap : List E) : Val :=
  fun v ↦ sqTab lv X N sqz qpos qbp tabs cap v.idx

/-- **One iteration of the squeeze loop, honestly** (S1a-6's `SqIterC`, `Place/SqAt`, with its
`sqDecArgs`, `sqTailArgs` written out). -/
def SqIterC' (lv : OsLv) : Prop :=
  ∀ (rd : Reader) (X N sqz qpos qbp tabs : E) (cap : List E), cap.length = 5 →
    (∀ i < 5, LoadHolds rd (sqz * X ^ 5) i (cap.getD i 0)) →
    (∀ i < 5, LoadHolds rd (sqz * X ^ 5) (5 + i) ((⟨cap, []⟩ : Fs).squeeze.2.cap.getD i 0)) →
    ∃ σ : Val, (osParams 6).map σ = [X, N, sqz, qpos, qbp, tabs] ∧
      AllOk (fun _ _ _ ↦ True) rd σ (sqLoopA lv ++ osLoopTailA (sqLoopE lv)) ∧
      σ (.n 9) = sqz * X ^ 5 ∧
      ([.n 33, .n (osMat 3 lv.posOff (34 + osPowLen (128 / lv.depth))).2.2,
          .n (osMat 4 lv.posOff ((osMat 3 lv.posOff (34 + osPowLen (128 / lv.depth))).2.2 + 1)).2.2,
          .n 5] : List V).map σ =
        [(⟨cap, []⟩ : Fs).squeeze.1, qpos * gen ^ lv.posOff * X ^ (128 / lv.depth),
          qbp * gen ^ lv.posOff * X ^ (128 / lv.depth), tabs] ∧
      σ (.n (sqLoopE lv + 2)) = X * gen + N ∧
      (.n (sqLoopE lv + 4) :: (List.range (6 - 1)).map fun i ↦ V.n (i + 1)).map σ =
        [X * gen, N, sqz, qpos, qbp, tabs]

theorem sqK1_ge (lv : OsLv) : 34 ≤ sqK1 lv := by unfold sqK1; omega

theorem matLen_le (off : ℕ) : matLen off ≤ 2 := by unfold matLen; split_ifs <;> omega

/-- **The squeeze loop's iteration holds at its values**, at a row whose power digits read
`128/d` and whose position offset is a word. -/
theorem sqIterC'_holds (lv : OsLv) (hpw : digitsVal (osPowDigits (128 / lv.depth)) 1 = 128 / lv.depth)
    (hpo : lv.posOff < u128Bound) : SqIterC' lv := by
  intro rd X N sqz qpos qbp tabs cap hcl hrow hnext
  obtain ⟨c0, c1, c2, c3, c4, rfl⟩ : ∃ c0 c1 c2 c3 c4, cap = [c0, c1, c2, c3, c4] := by
    match cap, hcl with
    | [a, b, c, d, e], _ => exact ⟨a, b, c, d, e, rfl⟩
  set σ := sqVal lv X N sqz qpos qbp tabs [c0, c1, c2, c3, c4] with hσ
  have hK := sqK1_ge lv
  have hm := matLen_le lv.posOff
  have e1 : sqM1 lv = sqK1 lv + matLen lv.posOff := rfl
  have e2 : sqM2 lv = sqM1 lv + 1 + matLen lv.posOff := rfl
  have hK1 : sqK1 lv = 34 + powLen (osPowDigits (128 / lv.depth)) := rfl
  -- reading the segments
  have vp : ∀ i < 6, σ (.n i) = [X, N, sqz, qpos, qbp, tabs].getD i 0 := fun i hi ↦ by
    simp [σ, sqVal, sqTab, hi]
  have h0 : σ (.n 0) = X := by simpa using vp 0 (by omega)
  have h1 : σ (.n 1) = N := by simpa using vp 1 (by omega)
  have h2 : σ (.n 2) = sqz := by simpa using vp 2 (by omega)
  have h3 : σ (.n 3) = qpos := by simpa using vp 3 (by omega)
  have h4 : σ (.n 4) = qbp := by simpa using vp 4 (by omega)
  have h5 : σ (.n 5) = tabs := by simpa using vp 5 (by omega)
  have vh : ∀ i, 6 ≤ i → i < 34 → σ (.n i) =
      (sqHead X sqz [c0, c1, c2, c3, c4]).getD (i - 6) 0 := fun i h1 h2 ↦ by
    simp [σ, sqVal, sqTab, show ¬ i < 6 by omega, h2]
  have vw : ∀ i, 34 ≤ i → i < sqK1 lv → σ (.n i) = powVals X (osPowDigits (128 / lv.depth)) X 34 i :=
    fun i h1 h2 ↦ by
      simp [σ, sqVal, sqTab, show ¬ i < 6 by omega, show ¬ i < 34 by omega, h2]
  have v1 : ∀ i, sqK1 lv ≤ i → i < sqM1 lv → σ (.n i) = matTab qpos lv.posOff (sqK1 lv) i :=
    fun i h1 h2 ↦ by
      simp [σ, sqVal, sqTab, show ¬ i < 6 by omega, show ¬ i < 34 by omega,
        show ¬ i < sqK1 lv by omega, h2]
  have vm1 : σ (.n (sqM1 lv)) = qpos * gen ^ lv.posOff * powRes X (osPowDigits (128 / lv.depth)) X := by
    simp [σ, sqVal, sqTab, show ¬ sqM1 lv < 6 by omega, show ¬ sqM1 lv < 34 by omega,
      show ¬ sqM1 lv < sqK1 lv by omega]
  have v2 : ∀ i, sqM1 lv + 1 ≤ i → i < sqM2 lv →
      σ (.n i) = matTab qbp lv.posOff (sqM1 lv + 1) i := fun i h1 h2 ↦ by
    simp [σ, sqVal, sqTab, show ¬ i < 6 by omega, show ¬ i < 34 by omega,
      show ¬ i < sqK1 lv by omega, show ¬ i < sqM1 lv by omega, show i ≠ sqM1 lv by omega, h2]
  have vm2 : σ (.n (sqM2 lv)) = qbp * gen ^ lv.posOff * powRes X (osPowDigits (128 / lv.depth)) X := by
    simp [σ, sqVal, sqTab, show ¬ sqM2 lv < 6 by omega, show ¬ sqM2 lv < 34 by omega,
      show ¬ sqM2 lv < sqK1 lv by omega, show ¬ sqM2 lv < sqM1 lv by omega,
      show sqM2 lv ≠ sqM1 lv by omega]
  have vt : ∀ j, σ (.n (sqM2 lv + 1 + j)) = [gw 1, X * gw 1, X * gw 1 + N, gw 1, X * gw 1].getD j 0 :=
    fun j ↦ by
      simp [σ, sqVal, sqTab, show ¬ sqM2 lv + 1 + j < 6 by omega,
        show ¬ sqM2 lv + 1 + j < 34 by omega, show ¬ sqM2 lv + 1 + j < sqK1 lv by omega,
        show ¬ sqM2 lv + 1 + j < sqM1 lv by omega, show sqM2 lv + 1 + j ≠ sqM1 lv by omega,
        show ¬ sqM2 lv + 1 + j < sqM2 lv by omega, show sqM2 lv + 1 + j ≠ sqM2 lv by omega]
  have t0 : σ (.n (sqM2 lv + 1)) = gw 1 := by simpa using vt 0
  have t1 : σ (.n (sqM2 lv + 1 + 1)) = X * gw 1 := by simpa using vt 1
  have t2 : σ (.n (sqM2 lv + 1 + 2)) = X * gw 1 + N := by simpa using vt 2
  have t3 : σ (.n (sqM2 lv + 1 + 3)) = gw 1 := by simpa using vt 3
  have t4 : σ (.n (sqM2 lv + 1 + 4)) = X * gw 1 := by simpa using vt 4
  have h9 : σ (.n 9) = sqz * X ^ 5 := by
    rw [vh 9 (by omega) (by omega)]; show sqz * (X * X * (X * X) * X) = sqz * X ^ 5; ring
  have hcell : ∀ c : Fin 13, σ (.n (20 + c.val)) = cellsOfState (sqPerm [c0, c1, c2, c3, c4]) false c :=
    fun c ↦ by
      have := c.isLt
      rw [vh _ (by omega) (by omega)]
      fin_cases c <;> simp [sqHead]
  -- the powers
  have hpow := powSteps_ok (C := fun _ _ _ ↦ True) (rd := rd) 0 (osPowDigits (128 / lv.depth)) 0 34
    X σ (by omega) (by omega) h0 (fun i h1 h2 ↦ by rw [h0]; exact vw i h1 (by omega))
  rw [h0] at hpow
  have hprv : powRes X (osPowDigits (128 / lv.depth)) X = X ^ (128 / lv.depth) := by
    rw [show powRes X (osPowDigits (128 / lv.depth)) X = powRes X (osPowDigits (128 / lv.depth)) (X ^ 1)
      by rw [pow_one], powRes_eq, hpw]
  -- the pointers
  have hq1 := osMat_ok (C := fun _ _ _ ↦ True) (rd := rd) (σ := σ) (b := 3) (off := lv.posOff)
    (k := sqK1 lv) hpo fun i h1' h2' ↦ by
      rw [v1 i h1' (by omega), h3]
  have hq2 := osMat_ok (C := fun _ _ _ ↦ True) (rd := rd) (σ := σ) (b := 4) (off := lv.posOff)
    (k := sqM1 lv + 1) hpo fun i h1' h2' ↦ by
      rw [v2 i h1' (by omega), h4]
  have hp1e : (osMat 3 lv.posOff (34 + osPowLen (128 / lv.depth))).2.2 = sqM1 lv := by
    rw [osMat_end, sqK1_eq, e1]
  have hp2e : (osMat 4 lv.posOff (sqM1 lv + 1)).2.2 = sqM2 lv := by
    rw [osMat_end, e2]
  have hg1 : gw 1 = gen := by rw [gw_eq (by decide), pow_one]
  have hn : ∀ i < 5, LoadHolds rd (sqz * X ^ 5) (5 + i) (σ (.n (28 + i))) := fun i hi ↦ by
    have hx := hnext i hi
    have hc := hcell ⟨8 + i, by omega⟩
    rw [show 20 + (8 + i) = 28 + i by omega] at hc
    rw [hc]
    interval_cases i <;> simpa [Fs.squeeze, capOf] using hx
  refine ⟨σ, ?_, ?_, h9, ?_, ?_, ?_⟩
  · simp [osParams, List.range_succ, h0, h1, h2, h3, h4, h5]
  · rw [allOk_append]
    refine ⟨?_, ?_⟩
    · unfold sqLoopA
      dsimp only
      rw [hp1e, sqK1_eq]
      simp only [allOk_append]
      refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, hpow.1⟩, hq1.1⟩, ?_⟩, hq2.1⟩, ?_⟩, ?_⟩
      · simp only [osMul, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_mul]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [vh 6 (by omega) (by omega), h0]; simp [sqHead]
        · rw [vh 7 (by omega) (by omega), vh 6 (by omega) (by omega)]; simp [sqHead]
        · rw [vh 8 (by omega) (by omega), vh 7 (by omega) (by omega), h0]; simp [sqHead]
        · rw [vh 9 (by omega) (by omega), vh 8 (by omega) (by omega), h2]; simp [sqHead]
      · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
          List.cons_append, osLd, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, h9]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [vh _ (by omega) (by omega)]; simpa [sqHead] using hrow 0 (by omega)
        · rw [vh _ (by omega) (by omega)]; simpa [sqHead] using hrow 1 (by omega)
        · rw [vh _ (by omega) (by omega)]; simpa [sqHead] using hrow 2 (by omega)
        · rw [vh _ (by omega) (by omega)]; simpa [sqHead] using hrow 3 (by omega)
        · rw [vh _ (by omega) (by omega)]; simpa [sqHead] using hrow 4 (by omega)
      · simp only [osCst, osKeccak, osCp, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_const,
          holds_copy]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [vh _ (by omega) (by omega)]; simp [sqHead]
        · rw [vh _ (by omega) (by omega)]; simp [sqHead]
        · rw [vh _ (by omega) (by omega)]; simp [sqHead]
        · rw [vh _ (by omega) (by omega)]; simp [sqHead]
        · rw [vh _ (by omega) (by omega)]; simp [sqHead]
        · refine keccakA_of (by simp) (by simp [osRun]) ?_
          have hins : ([16, 16, 16, 16, 16, 17, 18, 19, 10, 11, 12, 13, 14].map V.n).map σ =
              pendCells (⟨[c0, c1, c2, c3, c4], []⟩ : Fs).pend ++
                List.replicate (8 - 2 * (⟨[c0, c1, c2, c3, c4], []⟩ : Fs).pend.length) 0 ++
                (⟨[c0, c1, c2, c3, c4], []⟩ : Fs).cap := by
            simp [vh 16 (by omega) (by omega), vh 17 (by omega) (by omega),
              vh 18 (by omega) (by omega), vh 19 (by omega) (by omega),
              vh 10 (by omega) (by omega), vh 11 (by omega) (by omega),
              vh 12 (by omega) (by omega), vh 13 (by omega) (by omega),
              vh 14 (by omega) (by omega), sqHead, pendCells, word_zero]
          rw [hins, ← perm_eq_cells _ (by simp)]
          funext c
          have := hcell c
          simp only [cells13, osRun, List.map_map, Function.comp_def]
          rw [List.getD_eq_getElem _ _ (by simp)]
          simpa using this
        · have hc := hcell 0
          rw [vh 33 (by omega) (by omega)]
          simp only [Fin.val_zero, Nat.add_zero] at hc
          rw [hc]; simp [sqHead]
      · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
          List.cons_append, osLd, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, h9]
        exact ⟨hn 0 (by omega), hn 1 (by omega), hn 2 (by omega), hn 3 (by omega), hn 4 (by omega)⟩
      · simp only [osMul, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_mul]
        rw [vm1, hq1.2, h3, hpow.2]
      · rw [hp2e]
        simp only [osMul, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_mul]
        rw [vm2, hq2.2, h4, hpow.2]
      · simp only [allOk_cons, allOk_nil, and_true, stmtOk_call]
    · rw [sqLoopE_eq]
      simp only [osLoopTailA, allOk_cons, allOk_nil, and_true]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show σ (.n (sqM2 lv + 1)) = gw 1; exact t0
      · show σ (.n (sqM2 lv + 1 + 1)) = σ (.n 0) * σ (.n (sqM2 lv + 1)); rw [t1, t0, h0]
      · show σ (.n (sqM2 lv + 1 + 2)) = σ (.n (sqM2 lv + 1 + 1)) + σ (.n 1); rw [t2, t1, h1]
      · show σ (.n (sqM2 lv + 1 + 3)) = gw 1; exact t3
      · show σ (.n (sqM2 lv + 1 + 4)) = σ (.n 0) * σ (.n (sqM2 lv + 1 + 3)); rw [t4, t3, h0]
  · rw [hp1e, hp2e]
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    refine ⟨?_, by rw [vm1, hprv], by rw [vm2, hprv], h5⟩
    have hc := hcell 0
    simp only [Fin.val_zero, Nat.add_zero] at hc
    rw [vh 33 (by omega) (by omega), Fs.squeeze, Keccak.challengeOf_cells, ← hc,
      vh 20 (by omega) (by omega)]
    simp [sqHead]
  · rw [sqLoopE_eq, t2, hg1]
  · rw [sqLoopE_eq]
    simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, List.cons.injEq, and_true]
    exact ⟨by rw [t4, hg1], h1, h2, h3, h4, h5⟩

end
end LeanVM.Guest.B1.Whir
