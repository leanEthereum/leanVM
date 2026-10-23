/-
  LeanVM.Guest.B1.Whir.StackedC2

  The completeness of `open_stacked`'s level blocks after the folds: the final message, the
  next commitment and its out-of-domain sample, the proof of work.
-/

module

public import LeanVM.Guest.B1.Whir.StackedC1

/-!
# `open_stacked`'s blocks, honestly: claims and proof of work (TRIAGE #36)

Each block's honest values from its first (`*Vals`) and its relation from them, the callees'
returns among them; the state after it against the chain state.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

theorem os_skip (l l' : List E) (n : ℕ) : (l ++ l').getD (l.length + n) 0 = l'.getD n 0 := by
  rw [oq_getD_app_ge (by omega), Nat.add_sub_cancel_left]

/-! ## The final message -/

/-- The values of `osFinal` from its first: the pointer, the returns, the copies. -/
def osFinalVals (cv : Digest) (ms : List E) (bv : E) (co n : ℕ) : List E :=
  osMatVals bv co ++ [(digestScalars (obsAll cv ms)).1, (digestScalars (obsAll cv ms)).2, bv * osGw co * gen ^ n,
    (digestScalars (obsAll cv ms)).1, (digestScalars (obsAll cv ms)).2]

/-- **The final message** at its honest values. -/
theorem osFinal_complete {name : String} {n : ℕ} {s : OsSt} {cv : Digest} {cur : E} {p : ℕ}
    (hat : OsAt σ s cv cur p) (hco : s.co < 2 ^ 128) {fmsg : ℕ} {ms : List E}
    (hcall : C name [(digestScalars cv).1, (digestScalars cv).2, cur * gen ^ p, σ (.n fmsg)]
      [(digestScalars (obsAll cv ms)).1, (digestScalars (obsAll cv ms)).2, cur * gen ^ (p + n)])
    {kret : List E → Prop}
    (hv : ∀ j < (osFinalVals cv ms (σ (.n s.cb)) s.co n).length,
      σ (.n (s.k + j)) = (osFinalVals cv ms (σ (.n s.cb)) s.co n).getD j 0) :
    Stmt.HoldsList C rd σ (osFinal name fmsg s).1 True kret ∧
      OsAt σ (osFinal name fmsg s).2 (obsAll cv ms) cur (p + n) ∧ (osFinal name fmsg s).2.co = 0 ∧
      σ (.n (osFinal name fmsg s).2.cb) = σ (.n s.cb) * osGw s.co * gen ^ n ∧
      (osFinal name fmsg s).2.k = s.k + (osFinalVals cv ms (σ (.n s.cb)) s.co n).length := by
  set M := osMatVals (σ (.n s.cb)) s.co with hM
  set c := obsAll cv ms
  set T : List E := [(digestScalars c).1, (digestScalars c).2, σ (.n s.cb) * osGw s.co * gen ^ n,
    (digestScalars c).1, (digestScalars c).2] with hT
  have hvals : osFinalVals cv ms (σ (.n s.cb)) s.co n = M ++ T := rfl
  rw [hvals] at hv ⊢
  have hlen : (M ++ T).length = M.length + 5 := by simp [hT]
  have hr : (osMat s.cb s.co s.k).2.2 = s.k + M.length := by
    rw [osMat_next', hM, os_length_matVals' (σ (.n s.cb))]
  have hm := osMat_complete (C := C) (rd := rd) (σ := σ) (base := s.cb) (k := s.k) (kret := kret) hco
    fun j hj => by rw [hv j (by rw [hlen, hM]; omega), oq_getD_app_lt hj]
  have gT : ∀ j < 5, σ (.n ((osMat s.cb s.co s.k).2.2 + j)) = T.getD j 0 := fun j hj => by
    rw [hr, Nat.add_assoc, hv _ (by rw [hlen]; omega), os_skip]
  have hgw : σ (.n s.cb) * osGw s.co = σ (.n s.cb) * gen ^ s.co := by rw [os_gw_eq hco]
  generalize hR : (osMat s.cb s.co s.k).2.2 = r at gT hr
  have g0 := gT 0 (by omega); have g1 := gT 1 (by omega); have g2 := gT 2 (by omega)
  have g3 := gT 3 (by omega); have g4 := gT 4 (by omega)
  simp only [hT, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at g0 g1 g2 g3 g4
  unfold osFinal
  dsimp only
  rw [hR]
  refine ⟨?_, ⟨?_, ?_⟩, rfl, g2, by rw [hlen, hr]; ring⟩
  · rw [holdsList_append]
    refine (holdsList_noRet _ (osMat_noRet _ _ _) _ _).mpr ⟨hm.1, ?_⟩
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, and_true]
    refine ⟨?_, by rw [g3, g0], by rw [g4, g1]⟩
    have e0 : (digestScalars cv).1 = σ (.n s.f0) := by rw [← hat.fs]
    have e1 : (digestScalars cv).2 = σ (.n s.f1) := by rw [← hat.fs]
    rw [hm.2, g0, g1, g2, hgw, hat.cursor, mul_assoc, ← pow_add]
    rw [e0, e1] at hcall
    exact hcall
  · show (σ (.n (r + 3)), σ (.n (r + 4))) = _
    rw [g3, g4]
  · show σ (.n (r + 2)) * gen ^ 0 = cur * gen ^ (p + n)
    rw [g2, pow_zero, mul_one, hgw, hat.cursor, mul_assoc, ← pow_add]

/-! ## An out-of-domain sample -/

/-- The values of `osOodSample` from its first: the point's pointer and size, `opening_ood_point`'s
returns and their copies, the three reads. -/
def osOodSampleVals (oz logCols : ℕ) (oodzv : E) (cv : Digest) (y c0 c2 : E) : List E :=
  let c' := (sqAll logCols cv).2
  [osGw oz, oodzv * osGw oz, osGw logCols, (digestScalars c').1, (digestScalars c').2, (digestScalars c').1,
    (digestScalars c').2] ++ osFsNextVals y c' ++ osFsNextVals c0 (obsCv c' y) ++
    osFsNextVals c2 (obsCv (obsCv c' y) c0)

theorem os_length_fsNextVals (x : E) (cv : Digest) : (osFsNextVals x cv).length = 15 := by
  simp [osFsNextVals]

theorem os_length_oodSampleVals (oz logCols : ℕ) (oodzv : E) (cv : Digest) (y c0 c2 : E) :
    (osOodSampleVals oz logCols oodzv cv y c0 c2).length = 52 := by
  simp [osOodSampleVals, os_length_fsNextVals]

/-- **An out-of-domain sample** at its honest values: its point squeezed, its value and its
intro's `c0`, `c2` read and stored at `ood[so + 1 ..]`. -/
theorem osOodSample_complete {s : OsSt} {cv : Digest} {cur : E} {p : ℕ} (hat : OsAt σ s cv cur p)
    {oz so logCols oodz ood : ℕ} {y c0 c2 : E} {kret : List E → Prop}
    (ly : LoadHolds rd cur p y) (lc0 : LoadHolds rd cur (p + 1) c0) (lc2 : LoadHolds rd cur (p + 2) c2)
    (sy : LoadHolds rd (σ (.n ood)) (so + 1) y) (sc0 : LoadHolds rd (σ (.n ood)) (so + 2) c0)
    (sc2 : LoadHolds rd (σ (.n ood)) (so + 3) c2)
    (hcall : C "opening_ood_point" [(digestScalars cv).1, (digestScalars cv).2, σ (.n oodz) * osGw oz, osGw logCols]
      [(digestScalars (sqAll logCols cv).2).1, (digestScalars (sqAll logCols cv).2).2])
    (hv : ∀ j < 52, σ (.n (s.k + j)) = (osOodSampleVals oz logCols (σ (.n oodz)) cv y c0 c2).getD j 0) :
    Stmt.HoldsList C rd σ (osOodSample oz so logCols oodz ood s).1 True kret ∧
      OsAt σ (osOodSample oz so logCols oodz ood s).2
        (obsCv (obsCv (obsCv (sqAll logCols cv).2 y) c0) c2) cur (p + 3) ∧
      (osOodSample oz so logCols oodz ood s).2.co = s.co + 3 ∧ (osOodSample oz so logCols oodz ood s).2.cb = s.cb ∧
      (osOodSample oz so logCols oodz ood s).2.k = s.k + 52 := by
  set c' := (sqAll logCols cv).2
  set A : List E := [osGw oz, σ (.n oodz) * osGw oz, osGw logCols, (digestScalars c').1, (digestScalars c').2,
    (digestScalars c').1, (digestScalars c').2] with hA
  set F1 := osFsNextVals y c'
  set F2 := osFsNextVals c0 (obsCv c' y)
  set F3 := osFsNextVals c2 (obsCv (obsCv c' y) c0)
  have hvals : osOodSampleVals oz logCols (σ (.n oodz)) cv y c0 c2 = A ++ (F1 ++ (F2 ++ F3)) := by
    simp only [osOodSampleVals, List.append_assoc]; rfl
  rw [hvals] at hv
  have lA : A.length = 7 := rfl
  have l1 : F1.length = 15 := os_length_fsNextVals _ _
  have l2 : F2.length = 15 := os_length_fsNextVals _ _
  have gA : ∀ j < 7, σ (.n (s.k + j)) = A.getD j 0 := fun j hj => by
    rw [hv j (by omega), oq_getD_app_lt (by omega)]
  have e0 := gA 0 (by omega); have e1 := gA 1 (by omega); have e2 := gA 2 (by omega)
  have e3 := gA 3 (by omega); have e4 := gA 4 (by omega); have e5 := gA 5 (by omega)
  have e6 := gA 6 (by omega)
  simp only [hA, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1 e2 e3 e4 e5 e6
  set s1 : OsSt := { s with k := s.k + 7, f0 := s.k + 5, f1 := s.k + 6 }
  have hat1 : OsAt σ s1 c' cur p := ⟨by show (σ (.n (s.k + 5)), σ (.n (s.k + 6))) = _; rw [e5, e6], hat.cursor⟩
  obtain ⟨h1, hat2⟩ := osFsNext_complete (C := C) (kret := kret) hat1 ly fun j hj => by
    rw [show s1.k + j = s.k + (A.length + j) by simp [s1, lA]; ring, hv _ (by omega), os_skip,
      oq_getD_app_lt (by omega)]
  obtain ⟨h2, hat3⟩ := osFsNext_complete (C := C) (kret := kret) hat2 lc0 fun j hj => by
    rw [show (osFsNext s1).2.k + j = s.k + (A.length + (F1.length + j)) by simp [osFsNext, s1, lA, l1]; ring,
      hv _ (by omega), os_skip, os_skip, oq_getD_app_lt (by omega)]
  obtain ⟨h3, hat4⟩ := osFsNext_complete (C := C) (kret := kret) hat3 lc2 fun j hj => by
    rw [show (osFsNext (osFsNext s1).2).2.k + j = s.k + (A.length + (F1.length + (F2.length + j))) by
      simp [osFsNext, s1, lA, l1, l2]; ring, hv _ (by omega), os_skip, os_skip, os_skip]
  have hk1 : s1.k = s.k + 7 := rfl
  unfold osOodSample
  dsimp only
  refine ⟨?_, hat4, rfl, rfl, by simp [osFsNext]⟩
  simp only [holdsList_append]
  refine (holdsList_noRet _ rfl _ _).mpr ⟨?_, ?_⟩
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, and_true]
    refine ⟨e0, by rw [e1, e0], e2, ?_, by rw [e5, e3], by rw [e6, e4]⟩
    have f0 : (digestScalars cv).1 = σ (.n s.f0) := by rw [← hat.fs]
    have f1 : (digestScalars cv).2 = σ (.n s.f1) := by rw [← hat.fs]
    rw [e1, e2, e3, e4, ← f0, ← f1]
    exact hcall
  refine (holdsList_noRet _ rfl _ _).mpr ⟨h1, ?_⟩
  refine (holdsList_noRet _ rfl _ _).mpr ⟨h2, ?_⟩
  refine (holdsList_noRet _ rfl _ _).mpr ⟨h3, ?_⟩
  have v1 : σ (.n s1.k) = y := by
    have := hv (A.length + 0) (by omega)
    rw [os_skip, oq_getD_app_lt (by omega)] at this
    exact this
  have v2 : σ (.n (osFsNext s1).2.k) = c0 := by
    have := hv (A.length + (F1.length + 0)) (by omega)
    rw [os_skip, os_skip, oq_getD_app_lt (by omega)] at this
    rw [show (osFsNext s1).2.k = s.k + (A.length + (F1.length + 0)) by simp [osFsNext, s1, lA, l1]]
    exact this
  have v3 : σ (.n (osFsNext (osFsNext s1).2).2.k) = c2 := by
    have := hv (A.length + (F1.length + (F2.length + 0))) (by omega)
    rw [os_skip, os_skip, os_skip] at this
    rw [show (osFsNext (osFsNext s1).2).2.k = s.k + (A.length + (F1.length + (F2.length + 0))) by
      simp [osFsNext, s1, lA, l1, l2]]
    exact this
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
  exact ⟨by rw [v1]; exact sy, by rw [v2]; exact sc0, by rw [v3]; exact sc2⟩

/-! ## The next commitment -/

/-- The values of `osCommit` (one out-of-domain sample) from its first: the root's halves read,
`assert_canonical`'s returns, the sample. -/
def osCommitVals (lvl logCols : ℕ) (oodzv : E) (cv : Digest) (x0 x1 y c0 c2 : E) : List E :=
  osFsNextVals x0 cv ++ osFsNextVals x1 (obsCv cv x0) ++ [0, 0] ++
    osOodSampleVals ((lvl + 1 + 0) * 22) logCols oodzv (obsCv (obsCv cv x0) x1) y c0 c2

/-- **The next commitment** at its honest values: the root's halves read and stored, then its
out-of-domain sample. -/
theorem osCommit_complete {lvl logCols roots oodz ood : ℕ} {s : OsSt} {cv : Digest} {cur : E} {p : ℕ}
    (hat : OsAt σ s cv cur p) {x0 x1 y c0 c2 : E} {kret : List E → Prop}
    (lx0 : LoadHolds rd cur p x0) (lx1 : LoadHolds rd cur (p + 1) x1)
    (ly : LoadHolds rd cur (p + 2) y) (lc0 : LoadHolds rd cur (p + 3) c0) (lc2 : LoadHolds rd cur (p + 4) c2)
    (sx0 : LoadHolds rd (σ (.n roots)) (2 * lvl + 2) x0) (sx1 : LoadHolds rd (σ (.n roots)) (2 * lvl + 3) x1)
    (sy : LoadHolds rd (σ (.n ood)) ((lvl + 1) * 4 + 0 * 4 + 1) y)
    (sc0 : LoadHolds rd (σ (.n ood)) ((lvl + 1) * 4 + 0 * 4 + 2) c0)
    (sc2 : LoadHolds rd (σ (.n ood)) ((lvl + 1) * 4 + 0 * 4 + 3) c2)
    (hca0 : C "assert_canonical" [x0] [0]) (hca1 : C "assert_canonical" [x1] [0])
    (hood : C "opening_ood_point" [(digestScalars (obsCv (obsCv cv x0) x1)).1,
      (digestScalars (obsCv (obsCv cv x0) x1)).2, σ (.n oodz) * osGw ((lvl + 1 + 0) * 22), osGw logCols]
      [(digestScalars (sqAll logCols (obsCv (obsCv cv x0) x1)).2).1,
        (digestScalars (sqAll logCols (obsCv (obsCv cv x0) x1)).2).2])
    (hv : ∀ j < 84, σ (.n (s.k + j)) = (osCommitVals lvl logCols (σ (.n oodz)) cv x0 x1 y c0 c2).getD j 0) :
    Stmt.HoldsList C rd σ (osCommit lvl logCols 1 roots oodz ood s).1 True kret ∧
      OsAt σ (osCommit lvl logCols 1 roots oodz ood s).2
        (obsCv (obsCv (obsCv (sqAll logCols (obsCv (obsCv cv x0) x1)).2 y) c0) c2) cur (p + 5) ∧
      (osCommit lvl logCols 1 roots oodz ood s).2.co = s.co + 5 ∧
      (osCommit lvl logCols 1 roots oodz ood s).2.cb = s.cb ∧ (osCommit lvl logCols 1 roots oodz ood s).2.k = s.k + 84 := by
  set F1 := osFsNextVals x0 cv
  set F2 := osFsNextVals x1 (obsCv cv x0)
  set Z : List E := [0, 0] with hZ
  set O := osOodSampleVals ((lvl + 1 + 0) * 22) logCols (σ (.n oodz)) (obsCv (obsCv cv x0) x1) y c0 c2
  have hvals : osCommitVals lvl logCols (σ (.n oodz)) cv x0 x1 y c0 c2 = F1 ++ (F2 ++ (Z ++ O)) := by
    simp only [osCommitVals, List.append_assoc]; rfl
  rw [hvals] at hv
  have l1 : F1.length = 15 := os_length_fsNextVals _ _
  have l2 : F2.length = 15 := os_length_fsNextVals _ _
  have lZ : Z.length = 2 := rfl
  obtain ⟨h1, hat1⟩ := osFsNext_complete (C := C) (kret := kret) hat lx0 fun j hj => by
    rw [hv j (by omega), oq_getD_app_lt (by omega)]
  obtain ⟨h2, hat2⟩ := osFsNext_complete (C := C) (kret := kret) hat1 lx1 fun j hj => by
    rw [show (osFsNext s).2.k + j = s.k + (F1.length + j) by simp [osFsNext, l1]; ring, hv _ (by omega), os_skip,
      oq_getD_app_lt (by omega)]
  set st2 : OsSt := { (osFsNext (osFsNext s).2).2 with k := (osFsNext (osFsNext s).2).2.k + 2 }
  have hk2 : st2.k = s.k + (F1.length + (F2.length + (Z.length + 0))) := by simp [st2, osFsNext, l1, l2, lZ]
  have hat2' : OsAt σ st2 (obsCv (obsCv cv x0) x1) cur (p + 1 + 1) := ⟨hat2.fs, hat2.cursor⟩
  obtain ⟨h3, hat3, hco3, hcb3, hk3⟩ := osOodSample_complete (oz := (lvl + 1 + 0) * 22)
    (so := (lvl + 1) * 4 + 0 * 4) (logCols := logCols) (oodz := oodz) (ood := ood) (kret := kret) hat2'
    (by simpa using ly) (by simpa [Nat.add_assoc] using lc0) (by simpa [Nat.add_assoc] using lc2) sy sc0 sc2 hood
    fun j hj => by rw [hk2, Nat.add_zero, show s.k + (F1.length + (F2.length + Z.length)) + j =
      s.k + (F1.length + (F2.length + (Z.length + j))) by ring, hv _ (by omega), os_skip, os_skip, os_skip]
  have v0 : σ (.n s.k) = x0 := by
    have := hv 0 (by omega); rw [oq_getD_app_lt (by omega)] at this; exact this
  have v1 : σ (.n (osFsNext s).2.k) = x1 := by
    have := hv (F1.length + 0) (by omega); rw [os_skip, oq_getD_app_lt (by omega)] at this
    rw [show (osFsNext s).2.k = s.k + (F1.length + 0) by simp [osFsNext, l1]]; exact this
  have w0 : σ (.n ((osFsNext (osFsNext s).2).2.k)) = 0 := by
    have := hv (F1.length + (F2.length + 0)) (by omega); rw [os_skip, os_skip, oq_getD_app_lt (by omega)] at this
    rw [show (osFsNext (osFsNext s).2).2.k = s.k + (F1.length + (F2.length + 0)) by simp [osFsNext, l1, l2]]
    exact this
  have w1 : σ (.n ((osFsNext (osFsNext s).2).2.k + 1)) = 0 := by
    have := hv (F1.length + (F2.length + 1)) (by omega); rw [os_skip, os_skip, oq_getD_app_lt (by omega)] at this
    rw [show (osFsNext (osFsNext s).2).2.k + 1 = s.k + (F1.length + (F2.length + 1)) by simp [osFsNext, l1, l2]]
    exact this
  unfold osCommit
  dsimp only
  simp only [osOods, List.append_nil]
  refine ⟨?_, by simpa [Nat.add_assoc] using hat3, by rw [hco3]; show s.co + 1 + 1 + 3 = s.co + 5; omega, by rw [hcb3]; rfl,
    by rw [hk3, hk2]; simp [lZ, l1, l2]⟩
  simp only [holdsList_append]
  refine (holdsList_noRet _ rfl _ _).mpr ⟨h1, ?_⟩
  refine (holdsList_noRet _ rfl _ _).mpr ⟨h2, ?_⟩
  refine (holdsList_noRet _ rfl _ _).mpr ⟨?_, h3⟩
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, and_true]
  exact ⟨by rw [v0, w0]; exact hca0, by rw [v1, w1]; exact hca1, by rw [v0]; exact sx0, by rw [v1]; exact sx1⟩

/-! ## The proof of work -/

/-- The values of `osGrind bits` (`bits ≠ 0`) from its first: the nonce, the bits' word, the
absorb's values. -/
def osGrindVals (bits : ℕ) (n : E) (cv : Digest) : List E :=
  [n, osGw bits] ++ (List.range 14).map (fsVals n cv 4)

/-- **The query nonce** at its honest values (`bits ≠ 0`): the word at the cursor, `grind_check`'s
call, its absorb at tag 4. -/
theorem osGrind_complete {bits : ℕ} (hb0 : bits ≠ 0) {s : OsSt} {cv : Digest} {cur : E} {p : ℕ}
    (hat : OsAt σ s cv cur p) {n : E} (ln : LoadHolds rd cur p n) {kret : List E → Prop}
    (hcall : C "grind_check" [(digestScalars cv).1, (digestScalars cv).2, n, osGw bits] [])
    (hv : ∀ j < 16, σ (.n (s.k + j)) = (osGrindVals bits n cv).getD j 0) :
    Stmt.HoldsList C rd σ (osGrind bits s).1 True kret ∧
      OsAt σ (osGrind bits s).2 (absorbCv cv n 4) cur (p + 1) ∧ (osGrind bits s).2.co = s.co + 1 ∧
      (osGrind bits s).2.cb = s.cb ∧ (osGrind bits s).2.k = s.k + 16 := by
  have e0 : σ (.n s.k) = n := by simpa [osGrindVals] using hv 0 (by omega)
  have e1 : σ (.n (s.k + 1)) = osGw bits := by simpa [osGrindVals] using hv 1 (by omega)
  have e : ∀ j < 14, σ (.n (s.k + 2 + j)) = fsVals n cv 4 j := fun j hj => by
    rw [Nat.add_assoc, hv _ (by omega), show 2 + j = j + 1 + 1 by ring]
    simp [osGrindVals, List.getD_eq_getElem?_getD, hj]
  unfold osGrind
  dsimp only
  rw [ite_neg' hb0]
  refine ⟨?_, ⟨?_, ?_⟩, rfl, rfl, rfl⟩
  · simp only [holdsList_append]
    refine (holdsList_noRet _ rfl _ _).mpr ⟨?_, ?_⟩
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      have hl := os_cursor_load (j := 0) hat (by rw [Nat.add_zero]; exact ln)
      rw [Nat.add_zero] at hl
      rw [e0]; exact hl
    refine (holdsList_noRet _ rfl _ _).mpr ⟨?_, ?_⟩
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, and_true]
      refine ⟨e1, ?_⟩
      have f0 : (digestScalars cv).1 = σ (.n s.f0) := by rw [← hat.fs]
      have f1 : (digestScalars cv).2 = σ (.n s.f1) := by rw [← hat.fs]
      rw [e0, e1, ← f0, ← f1]
      exact hcall
    · refine (holds_fsCompressT _ _ _ _ (tag := 4) (by decide) _ _).mpr ⟨⟨cv, hat.fs, fun j h1 h2 => ?_⟩, trivial⟩
      rw [e j h2, e0]
  · show (σ (.n (s.k + 14)), σ (.n (s.k + 15))) = _
    rw [show s.k + 14 = s.k + 2 + 12 by ring, show s.k + 15 = s.k + 2 + 13 by ring, e 12 (by omega),
      e 13 (by omega)]
    simp only [fsVals]
  · show σ (.n s.cb) * gen ^ (s.co + 1) = cur * gen ^ (p + 1)
    rw [pow_succ, pow_succ, ← mul_assoc, ← mul_assoc, hat.cursor]

end
end LeanVM.Guest.B1
