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

variable {rd : Reader} {σ : Val}

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
    {kret : List E → Prop}
    (hv : ∀ j < (osFinalVals cv ms (σ (.n s.cb)) s.co n).length,
      σ (.n (s.k + j)) = (osFinalVals cv ms (σ (.n s.cb)) s.co n).getD j 0) :
    Stmt.HoldsList osTC rd σ (osFinal name fmsg s).1 True kret ∧
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
  have hm := osMat_complete (C := osTC) (rd := rd) (σ := σ) (base := s.cb) (k := s.k) (kret := kret) hco
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
    exact ⟨trivial, by rw [g3, g0], by rw [g4, g1]⟩
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
    (hv : ∀ j < 52, σ (.n (s.k + j)) = (osOodSampleVals oz logCols (σ (.n oodz)) cv y c0 c2).getD j 0) :
    Stmt.HoldsList osTC rd σ (osOodSample oz so logCols oodz ood s).1 True kret ∧
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
  obtain ⟨h1, hat2⟩ := osFsNext_complete (C := osTC) (kret := kret) hat1 ly fun j hj => by
    rw [show s1.k + j = s.k + (A.length + j) by simp [s1, lA]; ring, hv _ (by omega), os_skip,
      oq_getD_app_lt (by omega)]
  obtain ⟨h2, hat3⟩ := osFsNext_complete (C := osTC) (kret := kret) hat2 lc0 fun j hj => by
    rw [show (osFsNext s1).2.k + j = s.k + (A.length + (F1.length + j)) by simp [osFsNext, s1, lA, l1]; ring,
      hv _ (by omega), os_skip, os_skip, oq_getD_app_lt (by omega)]
  obtain ⟨h3, hat4⟩ := osFsNext_complete (C := osTC) (kret := kret) hat3 lc2 fun j hj => by
    rw [show (osFsNext (osFsNext s1).2).2.k + j = s.k + (A.length + (F1.length + (F2.length + j))) by
      simp [osFsNext, s1, lA, l1, l2]; ring, hv _ (by omega), os_skip, os_skip, os_skip]
  have hk1 : s1.k = s.k + 7 := rfl
  unfold osOodSample
  dsimp only
  refine ⟨?_, hat4, rfl, rfl, by simp [osFsNext]⟩
  simp only [holdsList_append]
  refine (holdsList_noRet _ rfl _ _).mpr ⟨?_, ?_⟩
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, and_true]
    exact ⟨e0, by rw [e1, e0], e2, trivial, by rw [e5, e3], by rw [e6, e4]⟩
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

end
end LeanVM.Guest.B1
