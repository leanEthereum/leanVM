/-
  LeanVM.Guest.B1.Whir.SqLoop

  The squeeze loop of `open_stacked` (one squeeze and its `decode_query_windows` an iteration),
  soundly.
-/

module

public import LeanVM.Guest.B1.Whir.Loops
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Bits.QueryWindows

/-!
# The squeeze loop

At `x = g^j`, the iteration loads the sponge's capacity from the squeeze run's row `sqz·x^5`,
squeezes with nothing waiting, stores the next capacity in the next row, and decodes the
challenge's positions and their windows into `query_positions`, `query_win_ptrs` at
`g^po·x^(128/depth)` (`decode_query_windows`, reading the window table `tabs`). `SqIter` is that
meaning; `sqLoop_sound`: from the loop's relation, it holds at every iteration; `sqChain`: the
rows hold the sponge's capacities after `j` squeezes, iteration `j` decoding the `j + 1`-th
challenge.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {P : Program} {rd : Reader}

/-- **One iteration of the squeeze loop at `x`**: the capacity at the row `sqz·x^5`, its squeeze's
next capacity stored after it, the challenge's positions and windows decoded at
`qpos·g^po·x^(128/d)` and `qbp·g^po·x^(128/d)`. -/
def SqIter (rd : Reader) (d cd po : ℕ) (sqz qpos qbp tabs x : E) : Prop :=
  ∃ cap : List E, cap.length = 5 ∧
    (∀ i < 5, LoadHolds rd (sqz * x ^ 5) i (cap.getD i 0)) ∧
    (∀ i < 5, LoadHolds rd (sqz * x ^ 5) (5 + i) ((⟨cap, []⟩ : Fs).squeeze.2.cap.getD i 0)) ∧
    MeaningDecodeQueryWindows d cd rd [(⟨cap, []⟩ : Fs).squeeze.1,
      qpos * gen ^ po * x ^ (128 / d), qbp * gen ^ po * x ^ (128 / d), tabs] []

/-- The squeeze loop's body before its tail. -/
def sqLoopA (lv : OsLv) : List Stmt :=
  let pw := osPowSteps 0 (osPowDigits (128 / lv.depth)) 0 34
  let p1 := osMat 3 lv.posOff (34 + osPowLen (128 / lv.depth))
  let p2 := osMat 4 lv.posOff (p1.2.2 + 1)
  [osMul 6 0 0, osMul 7 6 6, osMul 8 7 0, osMul 9 2 8] ++
    ((List.range 5).map fun i ↦ osLd (10 + i) 9 i) ++
    [osCst 15 (word 1 0), osCst 16 (word 0 0), osCst 17 (word 0 0), osCst 18 (word 0 0),
      osCst 19 (word 0 0), osKeccak [16, 16, 16, 16, 16, 17, 18, 19, 10, 11, 12, 13, 14] 20, osCp 33 20] ++
    ((List.range 5).map fun i ↦ osLd (28 + i) 9 (5 + i)) ++
    pw.1 ++ p1.1 ++ [osMul p1.2.2 p1.2.1 pw.2] ++ p2.1 ++ [osMul p2.2.2 p2.2.1 pw.2] ++
    [.call ("decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth)
      [.n 33, .n p1.2.2, .n p2.2.2, .n 5] []]

/-- The value the loop's tail starts at. -/
def sqLoopE (lv : OsLv) : ℕ :=
  (osMat 4 lv.posOff ((osMat 3 lv.posOff (34 + osPowLen (128 / lv.depth))).2.2 + 1)).2.2 + 1

theorem sqLoopBody_split (lv : OsLv) (name : String) :
    sqLoopBody lv name = (sqLoopA lv ++ osLoopTailA (sqLoopE lv)) ++
      [.callIf (.n (sqLoopE lv + 2)) name
        (.n (sqLoopE lv + 4) :: (List.range (6 - 1)).map fun i ↦ .n (i + 1)), .ret []] := by
  simp only [sqLoopBody, sqLoopA, sqLoopE, osLoopTail_split, List.append_assoc]

theorem osMat_flat (b o k : ℕ) : (osMat b o k).1.all Stmt.flat = true := by
  unfold osMat; split_ifs <;> rfl

theorem sqLoopA_flat (lv : OsLv) : (sqLoopA lv ++ osLoopTailA (sqLoopE lv)).all Stmt.flat = true := by
  simp [sqLoopA, osKeccak, osLoopTailA, osPowSteps_flat, osMat_flat, Stmt.flat]

/-- **The squeeze loop's iteration**: from its body's atoms and calls at `x`, the iteration's
meaning, the guard `x·g + N` and the next call's arguments. -/
theorem sqLoop_step (lv : OsLv) (hpw : digitsVal (osPowDigits (128 / lv.depth)) 1 = 128 / lv.depth)
    (hpo : lv.posOff < u128Bound)
    (hdec : ∀ args rets, WinTabs rd (args.getD 3 0) →
      P.Rel rd ("decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth)
        args rets → MeaningDecodeQueryWindows lv.depth lv.capDepth rd args rets)
    (σ : Val) (x N sqz qpos qbp tabs : E) (hwt : WinTabs rd tabs)
    (hp : (osParams 6).map σ = [x, N, sqz, qpos, qbp, tabs])
    (hA : AllOk (P.Rel rd) rd σ (sqLoopA lv ++ osLoopTailA (sqLoopE lv))) :
    SqIter rd lv.depth lv.capDepth lv.posOff sqz qpos qbp tabs x ∧
      σ (.n (sqLoopE lv + 2)) = x * gen + N ∧
      (.n (sqLoopE lv + 4) :: (List.range (6 - 1)).map fun i ↦ V.n (i + 1)).map σ =
        x * gen :: [N, sqz, qpos, qbp, tabs] := by
  simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons.injEq, and_true, List.cons_append] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hp
  rw [allOk_append] at hA
  obtain ⟨hA, hT⟩ := hA
  obtain ⟨t2, t4⟩ := osLoopTailA_val hT
  unfold sqLoopA at hA
  simp only [allOk_append, allOk_cons, allOk_nil, and_true, stmtOk_atom, stmtOk_call, holds_mul,
    holds_load, holds_const, holds_copy, osMul, osLd, osCst, osCp, osKeccak, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, Nat.add_zero, and_assoc] at hA
  obtain ⟨m5, m6, m7, m8, l9, l10, l11, l12, l13, c14, c15, c16, c17, c18, hK, hch, s27, s28, s29,
    s30, s31, hpw1, hp1, hmul1, hp2, hmul2, hdc⟩ := hA
  have hrow : σ (.n 9) = sqz * x ^ 5 := by
    rw [m8, m7, m6, m5, h0, h2]; ring
  set cap := [σ (.n 10), σ (.n 11), σ (.n 12), σ (.n 13), σ (.n 14)]
  have hout := keccakA_fs (s := (⟨cap, []⟩ : Fs)) hK (by simp) (by
    simp [pendCells, c15, c16, c17, c18, word_zero, cap])
  have e : ∀ c : Fin 13, σ (.n (20 + c.val)) = cellsOfState (⟨cap, []⟩ : Fs).perm false c :=
    fun c ↦ by simpa [osRun] using outs_eq hout c (by simp [osRun])
  have hw : σ (.n 33) = (⟨cap, []⟩ : Fs).squeeze.1 := by
    rw [hch, Fs.squeeze, Keccak.challengeOf_cells]; exact e 0
  have hpwv := osPowSteps_val (C := P.Rel rd) (σ := σ) 0 (osPowDigits (128 / lv.depth)) 0 34
    1 (by rw [pow_one]) hpw1
  rw [hpw, h0] at hpwv
  have hq1 := osMat_val hpo hp1
  have hq2 := osMat_val hpo hp2
  rw [hq1, hpwv, h3] at hmul1
  rw [hq2, hpwv, h4] at hmul2
  refine ⟨⟨cap, rfl, fun i hi ↦ ?_, fun i hi ↦ ?_, ?_⟩, ?_, ?_⟩
  · rw [← hrow]
    rcases i with _ | _ | _ | _ | _ | i
    · exact l9
    · exact l10
    · exact l11
    · exact l12
    · exact l13
    · omega
  · rw [← hrow]
    rcases i with _ | _ | _ | _ | _ | i
    · simpa [Fs.squeeze, capOf, ← e 8] using s27
    · simpa [Fs.squeeze, capOf, ← e 9] using s28
    · simpa [Fs.squeeze, capOf, ← e 10] using s29
    · simpa [Fs.squeeze, capOf, ← e 11] using s30
    · simpa [Fs.squeeze, capOf, ← e 12] using s31
    · omega
  · have := hdec _ _ (by simpa [h5] using hwt) hdc
    rwa [hw, hmul1, hmul2, h5] at this
  · rw [t2, h0, h1]
  · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, Nat.zero_add, t4, h0, h1, h2, h3, h4, h5]

/-- **The squeeze loop, soundly**: entered at `g^e` with the bound `g^n`, `e < n < ord g`, the
iteration's meaning holds at every `g^j`, `e ≤ j < n`. -/
theorem sqLoop_sound {name : String} {fn : Fn} (hf : P.find? name = some fn)
    (lv : OsLv) (hps : fn.params = osParams 6) (hb : fn.body = sqLoopBody lv name)
    (hpw : digitsVal (osPowDigits (128 / lv.depth)) 1 = 128 / lv.depth)
    (hpo : lv.posOff < u128Bound)
    (hdec : ∀ args rets, WinTabs rd (args.getD 3 0) →
      P.Rel rd ("decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth)
        args rets → MeaningDecodeQueryWindows lv.depth lv.capDepth rd args rets)
    {e n : ℕ} (hen : e < n) (hn : n < ordG) (sqz qpos qbp tabs : E) (hwt : WinTabs rd tabs)
    (hg : gen ^ e + gen ^ n ≠ 0 → P.Rel rd name [gen ^ e, gen ^ n, sqz, qpos, qbp, tabs] []) :
    ∀ j, e ≤ j → j < n → SqIter rd lv.depth lv.capDepth lv.posOff sqz qpos qbp tabs (gen ^ j) := by
  rw [sqLoopBody_split] at hb
  refine loop_guarded_from (rest := [sqz, qpos, qbp, tabs]) hen hn rfl
    (loop_sound_flat hf (sqLoopA_flat lv) hb ?_) hg
  intro σ x hp hA
  rw [hps] at hp
  exact sqLoop_step lv hpw hpo hdec σ x (gen ^ n) sqz qpos qbp tabs hwt hp hA

/-! ## The chain of squeezes -/

theorem squeezeN_length : ∀ (n : ℕ) (s : Fs), (s.squeezeN n).1.length = n
  | 0, _ => rfl
  | n + 1, s => by simp only [Fs.squeezeN, List.length_cons, squeezeN_length n]

theorem squeezeN_snoc : ∀ (n : ℕ) (s : Fs), s.squeezeN (n + 1) =
    ((s.squeezeN n).1 ++ [(s.squeezeN n).2.squeeze.1], (s.squeezeN n).2.squeeze.2)
  | 0, s => rfl
  | n + 1, s => by
    rw [Fs.squeezeN, squeezeN_snoc n s.squeeze.2]
    rfl

theorem squeezeN_getD : ∀ (n : ℕ) (s : Fs) (j : ℕ), j < n →
    (s.squeezeN n).1.getD j 0 = (s.squeezeN j).2.squeeze.1
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, s, j, h => by
    rw [squeezeN_snoc]
    rcases Nat.lt_or_ge j n with h' | h'
    · rw [List.getD_append _ _ _ _ (by rw [squeezeN_length]; exact h'), squeezeN_getD n s j h']
    · obtain rfl : j = n := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [squeezeN_length]), squeezeN_length, Nat.sub_self]
      rfl

theorem squeezeN_pend {s : Fs} (hs : s.pend = []) : ∀ n, (s.squeezeN n).2.pend = []
  | 0 => hs
  | n + 1 => by rw [squeezeN_snoc]; rfl

/-- Five words at `p` from `o` are determined. -/
theorem five_eq {p : E} {o : ℕ} {a b : List E} (ha : a.length = 5) (hb : b.length = 5)
    (h1 : ∀ i < 5, LoadHolds rd p (o + i) (a.getD i 0))
    (h2 : ∀ i < 5, LoadHolds rd p (o + i) (b.getD i 0)) : a = b := by
  apply List.ext_getElem (by rw [ha, hb])
  intro i hi hi'
  have := loadHolds_unique (h1 i (by omega)) (h2 i (by omega))
  rwa [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at this

theorem sqIter_at {d cd po : ℕ} {sqz qpos qbp tabs : E} {j : ℕ}
    (h : SqIter rd d cd po sqz qpos qbp tabs (gen ^ j)) :
    ∃ cap : List E, cap.length = 5 ∧
      (∀ i < 5, LoadHolds rd sqz (5 * j + i) (cap.getD i 0)) ∧
      (∀ i < 5, LoadHolds rd sqz (5 * (j + 1) + i) ((⟨cap, []⟩ : Fs).squeeze.2.cap.getD i 0)) ∧
      MeaningDecodeQueryWindows d cd rd [(⟨cap, []⟩ : Fs).squeeze.1,
        qpos * gen ^ (po + j * (128 / d)), qbp * gen ^ (po + j * (128 / d)), tabs] [] := by
  obtain ⟨cap, hl, h1, h2, h3⟩ := h
  have hp : (gen ^ j) ^ 5 = gen ^ (5 * j) := by rw [← pow_mul, Nat.mul_comm]
  have hq : ∀ z : E, z * gen ^ po * (gen ^ j) ^ (128 / d) = z * gen ^ (po + j * (128 / d)) := by
    intro z; rw [← pow_mul, mul_assoc, ← pow_add]
  refine ⟨cap, hl, fun i hi ↦ ?_, fun i hi ↦ ?_, ?_⟩
  · have := h1 i hi; rwa [hp, loadHolds_mul_gen_pow] at this
  · have := h2 i hi
    rwa [hp, loadHolds_mul_gen_pow, show 5 * j + (5 + i) = 5 * (j + 1) + i by ring] at this
  · rwa [hq, hq] at h3

/-- **The chain**: from the capacity stored at the squeeze run's row `e`, the capacity stored at
row `e + j` is the sponge's after `j` squeezes; iteration `e + j` decodes the `j + 1`-th
challenge. -/
theorem sqChain {d cd po : ℕ} {sqz qpos qbp tabs : E} {e n : ℕ} (fs : List E) (hfs : fs.length = 5)
    (h0 : ∀ i < 5, LoadHolds rd sqz (5 * e + i) (fs.getD i 0))
    (hit : ∀ j, e ≤ j → j < e + n → SqIter rd d cd po sqz qpos qbp tabs (gen ^ j)) :
    (∀ j ≤ n, ∀ i < 5, LoadHolds rd sqz (5 * (e + j) + i)
      (((⟨fs, []⟩ : Fs).squeezeN j).2.cap.getD i 0)) ∧
    ∀ j < n, MeaningDecodeQueryWindows d cd rd [((⟨fs, []⟩ : Fs).squeezeN j).2.squeeze.1,
        qpos * gen ^ (po + (e + j) * (128 / d)), qbp * gen ^ (po + (e + j) * (128 / d)), tabs] [] := by
  have hcl : ∀ j, (((⟨fs, []⟩ : Fs).squeezeN j).2.cap).length = 5 := by
    intro j; rcases j with _ | j
    · exact hfs
    · rw [squeezeN_snoc]; simp [Fs.squeeze, capOf]
  have hcap : ∀ j, ∀ cap : List E, cap.length = 5 →
      (∀ i < 5, LoadHolds rd sqz (5 * (e + j) + i) (cap.getD i 0)) →
      (∀ i < 5, LoadHolds rd sqz (5 * (e + j) + i) (((⟨fs, []⟩ : Fs).squeezeN j).2.cap.getD i 0)) →
      ((⟨fs, []⟩ : Fs).squeezeN j).2 = ⟨cap, []⟩ := by
    intro j cap hl h1 h2
    have := five_eq hl (hcl j) h1 h2
    have hp := squeezeN_pend (s := (⟨fs, []⟩ : Fs)) rfl j
    cases hq : ((⟨fs, []⟩ : Fs).squeezeN j).2
    rw [hq] at hp this
    simp only at hp this
    rw [hp, this]
  have P : ∀ j ≤ n, ∀ i < 5, LoadHolds rd sqz (5 * (e + j) + i)
      (((⟨fs, []⟩ : Fs).squeezeN j).2.cap.getD i 0) := by
    intro j
    induction j with
    | zero => intro _ i hi; simpa [Fs.squeezeN] using h0 i hi
    | succ j ih =>
      intro hj i hi
      obtain ⟨cap, hl, h1, h2, -⟩ := sqIter_at (hit (e + j) (by omega) (by omega))
      have e' := hcap j cap hl h1 (ih (by omega))
      rw [squeezeN_snoc, e']
      have := h2 i hi
      rwa [show e + j + 1 = e + (j + 1) by ring] at this
  refine ⟨P, fun j hj ↦ ?_⟩
  obtain ⟨cap, hl, h1, -, h3⟩ := sqIter_at (hit (e + j) (by omega) (by omega))
  rw [hcap j cap hl h1 (P j hj.le)]
  exact h3

end
end LeanVM.Guest.B1.Whir
