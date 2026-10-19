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

variable {rd : Reader} {σ : Val}

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
    (hv : ∀ j < 25, σ (.n (s.k + j)) = (osSqueezesVals maxSq nsq sqzv cv).getD j 0) :
    Stmt.HoldsList osTC rd σ (osSqueezes maxSq nsq qpos qbp loop s).1 True kret ∧
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
      refine ⟨e0, ?_, ?_, e2, e3, by rw [e4, e2, e3], e5, e6, ?_, fun _ => trivial, e7, by rw [e8, e1, e7], ?_, ?_⟩
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
    Stmt.HoldsList osTC rd σ (osLamPows lam qw base k nq) True kret := by
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

end
end LeanVM.Guest.B1
