/-
  LeanVM.Guest.B1.Whir.SqLoop

  The squeeze loop of `open_stacked` (one squeeze and its `decode_query_windows` an iteration),
  soundly.
-/

module

public import LeanVM.Guest.B1.Whir.Loops
public import LeanVM.Guest.B1.Whir.Commit
public import LeanVM.Guest.B1.Bits.QueryWindows

/-!
# The squeeze loop (G:1562-1574)

At `x = g^j`, the iteration loads the sponge's capacity from the squeeze run's row
`sqz·x^5`, squeezes with nothing waiting, stores the next capacity in the next row, and decodes
the challenge's positions and their windows into `query_positions`, `query_win_ptrs` at
`g^po·x^(192/depth)` (`decode_query_windows`, reading the window table `tabs`). `SqIter` is that meaning; `sqLoop_sound`: from the
loop's relation, it holds at every iteration.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- **One iteration of the squeeze loop at `x`**: the capacity at the row `sqz·x^5`, its squeeze's
next capacity stored after it, the challenge's positions and windows decoded at
`qpos·g^po·x^(192/d)` and `qbp·g^po·x^(192/d)`. -/
def SqIter (rd : Reader) (d cd po : ℕ) (sqz qpos qbp tabs x : E) : Prop :=
  ∃ cap : List E, cap.length = 5 ∧
    (∀ i < 5, LoadHolds rd (sqz * x ^ 5) i (cap.getD i 0)) ∧
    (∀ i < 5, LoadHolds rd (sqz * x ^ 5) (5 + i) ((capOf (⟨cap, []⟩ : Fs).perm).getD i 0)) ∧
    MeaningDecodeQueryWindows d cd rd [challengeOf (⟨cap, []⟩ : Fs).perm,
      qpos * gen ^ po * x ^ (192 / d), qbp * gen ^ po * x ^ (192 / d), tabs] []

/-- The squeeze loop's body before its tail. -/
def sqLoopA (lv : OsLv) : List Stmt :=
  let pw := osPowSteps 0 (osPowDigits (192 / lv.depth)) 0 40
  let p1 := osMat 3 lv.posOff (40 + osPowLen (192 / lv.depth))
  let p2 := osMat 4 lv.posOff (p1.2.2 + 1)
  [.atom (.mul (.n 6) (.n 0) (.n 0)), .atom (.mul (.n 7) (.n 6) (.n 6)), .atom (.mul (.n 8) (.n 7) (.n 0)),
    .atom (.mul (.n 9) (.n 2) (.n 8))] ++
    ((List.range 5).map fun i ↦ .atom (.load (.n (10 + i)) (.n 9) i)) ++
    [.atom (.const (.n 15) (word 1 0 0)), .atom (.const (.n 16) (word 0 0 0)),
      .atom (.const (.n 17) (word 0 0 0)), .atom (.const (.n 18) (word 0 0 0)),
      .atom (.const (.n 19) (word 0 0 0))] ++
    osSqueeze0 15 [10, 11, 12, 13, 14] 20 ++
    ((List.range 5).map fun i ↦ .atom (.load (.n (28 + i)) (.n 9) (5 + i))) ++
    pw.1 ++ p1.1 ++ [.atom (.mul (.n p1.2.2) (.n p1.2.1) (.n pw.2))] ++
    p2.1 ++ [.atom (.mul (.n p2.2.2) (.n p2.2.1) (.n pw.2))] ++
    [.call ("decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth)
      [.n 39, .n p1.2.2, .n p2.2.2, .n 5] []]

theorem sqLoopBody_split (lv : OsLv) (name : String) :
    sqLoopBody lv name = (sqLoopA lv ++ osLoopTailA
      ((osMat 4 lv.posOff ((osMat 3 lv.posOff (40 + osPowLen (192 / lv.depth))).2.2 + 1)).2.2 + 1)) ++
      [.callIf (.n ((osMat 4 lv.posOff ((osMat 3 lv.posOff
          (40 + osPowLen (192 / lv.depth))).2.2 + 1)).2.2 + 1 + 2)) name
        (.n ((osMat 4 lv.posOff ((osMat 3 lv.posOff
          (40 + osPowLen (192 / lv.depth))).2.2 + 1)).2.2 + 1 + 4) ::
          (List.range (6 - 1)).map fun i ↦ .n (i + 1)), .ret []] := by
  simp only [sqLoopBody, sqLoopA, osLoopTail_split, List.append_assoc]

theorem sqLoopA_flat (lv : OsLv) : (sqLoopA lv ++ osLoopTailA
    ((osMat 4 lv.posOff ((osMat 3 lv.posOff (40 + osPowLen (192 / lv.depth))).2.2 + 1)).2.2 + 1)).all
      Stmt.flat = true := by
  have hpw : ∀ ds acc k, (osPowSteps 0 ds acc k).1.all Stmt.flat = true := by
    intro ds
    induction ds with
    | nil => intro _ _; rfl
    | cons d ds ih =>
      intro acc k
      cases d <;> simp [osPowSteps, ih, Stmt.flat]
  have hm : ∀ b o k, (osMat b o k).1.all Stmt.flat = true := by
    intro b o k; unfold osMat; split_ifs <;> rfl
  simp [sqLoopA, osSqueeze0, keccakA, challengeT, osLoopTailA, hpw, hm, Stmt.flat]

/-- **The squeeze loop's iteration**: from its body's atoms and calls at `x`, the iteration's
meaning, the guard `x·g + N` and the next call's arguments. -/
theorem sqLoop_step (lv : OsLv) (hpw : digitsVal (osPowDigits (192 / lv.depth)) 1 = 192 / lv.depth)
    (hpo : lv.posOff < u128Bound)
    (hdec : ∀ args rets, WinTabs rd (args.getD 3 0) →
      coreProgram.Rel rd ("decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth)
        args rets → MeaningDecodeQueryWindows lv.depth lv.capDepth rd args rets)
    (σ : Val) (x N sqz qpos qbp tabs : E) (hwt : WinTabs rd tabs)
    (hp : (osParams 6).map σ = [x, N, sqz, qpos, qbp, tabs])
    (hA : AllOk (coreProgram.Rel rd) rd σ (sqLoopA lv ++ osLoopTailA
      ((osMat 4 lv.posOff ((osMat 3 lv.posOff (40 + osPowLen (192 / lv.depth))).2.2 + 1)).2.2 + 1))) :
    SqIter rd lv.depth lv.capDepth lv.posOff sqz qpos qbp tabs x ∧
      σ (.n ((osMat 4 lv.posOff ((osMat 3 lv.posOff
        (40 + osPowLen (192 / lv.depth))).2.2 + 1)).2.2 + 1 + 2)) = x * gen + N ∧
      (.n ((osMat 4 lv.posOff ((osMat 3 lv.posOff
          (40 + osPowLen (192 / lv.depth))).2.2 + 1)).2.2 + 1 + 4) ::
          (List.range (6 - 1)).map fun i ↦ V.n (i + 1)).map σ = x * gen :: [N, sqz, qpos, qbp, tabs] := by
  simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons.injEq, and_true, List.cons_append] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hp
  rw [allOk_append] at hA
  obtain ⟨hA, hT⟩ := hA
  obtain ⟨t2, t4⟩ := osLoopTailA_val hT
  set pw := osPowSteps 0 (osPowDigits (192 / lv.depth)) 0 40
  set p1 := osMat 3 lv.posOff (40 + osPowLen (192 / lv.depth))
  set p2 := osMat 4 lv.posOff (p1.2.2 + 1)
  unfold sqLoopA at hA
  simp only [allOk_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, osSqueeze0,
    allOk_challengeT, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, Nat.add_zero, and_assoc] at hA
  obtain ⟨m5, m6, m7, m8, l9, l10, l11, l12, l13, c14, c15, c16, c17, c18, hK, hch, s27, s28, s29,
    s30, s31, hpw1, hp1, hmul1, hp2, hmul2, hdc⟩ := hA
  have hrow : σ (.n 9) = sqz * x ^ 5 := by
    rw [m8, m7, m6, m5, h0, h2]; ring
  obtain ⟨-, -, -, hout⟩ := keccakA_perm (rd := rd) hK
  set cap := [σ (.n 10), σ (.n 11), σ (.n 12), σ (.n 13), σ (.n 14)]
  have hS : permOf ([V.n (15 + 1), V.n (15 + 1), V.n (15 + 1), V.n (15 + 1), V.n (15 + 1),
      V.n (15 + 2), V.n (15 + 3), V.n (15 + 4), V.n 10, V.n 11, V.n 12, V.n 13, V.n 14].map σ) =
      (⟨cap, []⟩ : Fs).perm := by
    rw [perm_eq_cells _ (by simp)]
    simp [pendCells, c15, c16, c17, c18, word_zero, cap]
  rw [hS] at hout
  have o0 : σ (.n 20) = cellsOfState (⟨cap, []⟩ : Fs).perm false 0 := outs_eq hout 0 (by simp [osRun])
  have o1 : σ (.n 21) = cellsOfState (⟨cap, []⟩ : Fs).perm false 1 := outs_eq hout 1 (by simp [osRun])
  have hw : σ (.n 39) = challengeOf (⟨cap, []⟩ : Fs).perm := challengeT_value hch o0 o1
  have hpwv := osPowSteps_val (C := coreProgram.Rel rd) (σ := σ) 0 (osPowDigits (192 / lv.depth)) 0 40
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
    have e : ∀ c : Fin 13, σ (.n (20 + c.val)) = cellsOfState (⟨cap, []⟩ : Fs).perm false c :=
      fun c ↦ by simpa [osRun] using outs_eq hout c (by simp [osRun])
    rcases i with _ | _ | _ | _ | _ | i
    · simpa [capOf, ← e 8] using s27
    · simpa [capOf, ← e 9] using s28
    · simpa [capOf, ← e 10] using s29
    · simpa [capOf, ← e 11] using s30
    · simpa [capOf, ← e 12] using s31
    · omega
  · have := hdec _ _ (by simpa [h5] using hwt) hdc
    rwa [hw, hmul1, hmul2, h5] at this
  · rw [t2, h0, h1]
  · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, Nat.zero_add, t4, h0, h1, h2, h3, h4, h5]

/-- **The squeeze loop, soundly**: entered from `1` with the bound `g^n`, `0 < n < ord g`, the
iteration's meaning holds at every `g^j`, `j < n`. -/
theorem sqLoop_sound {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (lv : OsLv) (hps : fn.params = osParams 6) (hb : fn.body = sqLoopBody lv name)
    (hpw : digitsVal (osPowDigits (192 / lv.depth)) 1 = 192 / lv.depth)
    (hpo : lv.posOff < u128Bound)
    (hdec : ∀ args rets, WinTabs rd (args.getD 3 0) →
      coreProgram.Rel rd ("decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth)
        args rets → MeaningDecodeQueryWindows lv.depth lv.capDepth rd args rets)
    {n : ℕ} (hn0 : 0 < n) (hn : n < ordG) (sqz qpos qbp tabs : E) (hwt : WinTabs rd tabs)
    (hg : 1 + gen ^ n ≠ 0 → coreProgram.Rel rd name [1, gen ^ n, sqz, qpos, qbp, tabs] []) :
    ∀ j < n, SqIter rd lv.depth lv.capDepth lv.posOff sqz qpos qbp tabs (gen ^ j) := by
  rw [sqLoopBody_split] at hb
  refine loop_guarded (rest := [sqz, qpos, qbp, tabs]) hn0 hn rfl
    (loop_sound_flat hf (sqLoopA_flat lv) hb ?_) hg
  intro σ x hp hA
  rw [hps] at hp
  exact sqLoop_step lv hpw hpo hdec σ x (gen ^ n) sqz qpos qbp tabs hwt hp hA

/-! ## The chain of squeezes -/

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
  | n + 1 => squeezeN_succ_pend n s

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
      (∀ i < 5, LoadHolds rd sqz (5 * (j + 1) + i) ((capOf (⟨cap, []⟩ : Fs).perm).getD i 0)) ∧
      MeaningDecodeQueryWindows d cd rd [challengeOf (⟨cap, []⟩ : Fs).perm,
        qpos * gen ^ (po + j * (192 / d)), qbp * gen ^ (po + j * (192 / d)), tabs] [] := by
  obtain ⟨cap, hl, h1, h2, h3⟩ := h
  have hp : (gen ^ j) ^ 5 = gen ^ (5 * j) := by rw [← pow_mul, Nat.mul_comm]
  have hq : ∀ z : E, z * gen ^ po * (gen ^ j) ^ (192 / d) = z * gen ^ (po + j * (192 / d)) := by
    intro z; rw [← pow_mul, mul_assoc, ← pow_add]
  refine ⟨cap, hl, fun i hi ↦ ?_, fun i hi ↦ ?_, ?_⟩
  · have := h1 i hi; rwa [hp, loadHolds_mul_gen_pow] at this
  · have := h2 i hi
    rwa [hp, loadHolds_mul_gen_pow, show 5 * j + (5 + i) = 5 * (j + 1) + i by ring] at this
  · rwa [hq, hq] at h3

/-- **The chain**: the capacity stored at the squeeze run's row `j` is the sponge's after `j`
squeezes, from the capacity stored at row `0`; iteration `j`'s challenge is the `j+1`-th. -/
theorem sqChain {d cd po : ℕ} {sqz qpos qbp tabs : E} {n : ℕ} (fs : List E) (hfs : fs.length = 5)
    (h0 : ∀ i < 5, LoadHolds rd sqz i (fs.getD i 0))
    (hit : ∀ j < n, SqIter rd d cd po sqz qpos qbp tabs (gen ^ j)) :
    (∀ j ≤ n, ∀ i < 5, LoadHolds rd sqz (5 * j + i)
      (((⟨fs, []⟩ : Fs).squeezeN j).2.cap.getD i 0)) ∧
    ∀ j < n, MeaningDecodeQueryWindows d cd rd [((⟨fs, []⟩ : Fs).squeezeN j).2.squeeze.1,
        qpos * gen ^ (po + j * (192 / d)), qbp * gen ^ (po + j * (192 / d)), tabs] [] := by
  have hcl : ∀ j, (((⟨fs, []⟩ : Fs).squeezeN j).2.cap).length = 5 := by
    intro j; rcases j with _ | j
    · exact hfs
    · rw [squeezeN_snoc]; simp [Fs.squeeze, capOf]
  have hcap : ∀ j < n, ∀ cap : List E, cap.length = 5 →
      (∀ i < 5, LoadHolds rd sqz (5 * j + i) (cap.getD i 0)) →
      (∀ i < 5, LoadHolds rd sqz (5 * j + i) (((⟨fs, []⟩ : Fs).squeezeN j).2.cap.getD i 0)) →
      ((⟨fs, []⟩ : Fs).squeezeN j).2 = ⟨cap, []⟩ := by
    intro j _ cap hl h1 h2
    have := five_eq hl (hcl j) h1 h2
    rw [this]
    have hp := squeezeN_pend (s := (⟨fs, []⟩ : Fs)) rfl j
    cases e : ((⟨fs, []⟩ : Fs).squeezeN j).2
    rw [e] at hp
    simp_all
  have P : ∀ j ≤ n, ∀ i < 5, LoadHolds rd sqz (5 * j + i)
      (((⟨fs, []⟩ : Fs).squeezeN j).2.cap.getD i 0) := by
    intro j
    induction j with
    | zero => intro _ i hi; simpa [Fs.squeezeN] using h0 i hi
    | succ j ih =>
      intro hj i hi
      obtain ⟨cap, hl, h1, h2, -⟩ := sqIter_at (hit j (by omega))
      have e := hcap j (by omega) cap hl h1 (ih (by omega))
      rw [squeezeN_snoc, e]
      exact h2 i hi
  refine ⟨P, fun j hj ↦ ?_⟩
  obtain ⟨cap, hl, h1, -, h3⟩ := sqIter_at (hit j hj)
  rw [hcap j hj cap hl h1 (P j hj.le)]
  exact h3

end
end LeanVM.Guest.B1.Whir
