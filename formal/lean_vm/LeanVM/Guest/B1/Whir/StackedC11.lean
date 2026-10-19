/-
  LeanVM.Guest.B1.Whir.StackedC11

  `open_stacked`'s head at its honest values.
-/

module

public import LeanVM.Guest.B1.Whir.StackedC10

/-!
# The head, honestly (TRIAGE #36)

`osHead_complete`: the parameters, the state copied, the first quadratic read and the fixed
buffers at their honest values `osHeadVals`; the guest is then at level `0`'s start.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The head's values from `.n 0`: the parameters, the state's copies, the two reads, the first
quadratic's middle coefficient, each fixed buffer's size and pointer. -/
def osHeadVals (cfg : OsCfg) (fs0 fs1 target root0 root1 cur : E) (cv : Digest) (x0 x1 : E) (P : OsPtrs) :
    List E :=
  [fs0, fs1, target, root0, root1, cur, fs0, fs1] ++ osFsNextVals x0 cv ++ osFsNextVals x1 (obsCv cv x0) ++
    [target + x1, osGw (4 * cfg.capLen), P.caps, osGw cfg.capLen, P.flags, osGw cfg.yrLen, P.fmsg,
      osGw (2 * cfg.levels.length), P.roots, osGw cfg.nFolds, P.fch, osGw cfg.levels.length, P.betas,
      osGw (cfg.levels.length * cfg.maxQ), P.qw, osGw cfg.posLen, P.qpos, osGw cfg.posLen, P.qbp,
      osGw (cfg.levels.length * 22), P.oodz, osGw (cfg.levels.length * 4), P.ood]

theorem os_length_headVals (cfg : OsCfg) (fs0 fs1 target root0 root1 cur : E) (cv : Digest) (x0 x1 : E)
    (P : OsPtrs) : (osHeadVals cfg fs0 fs1 target root0 root1 cur cv x0 x1 P).length = 61 := by
  simp [osHeadVals, os_length_fsNextVals]

/-- **The head** at its honest values (G:1062-1094). -/
theorem osHead_complete {cfg : OsCfg} {fs0 fs1 target root0 root1 cur : E} {cv : Digest} {x0 x1 : E}
    {P : OsPtrs} (hcv : (fs0, fs1) = digestScalars cv) (lx0 : LoadHolds rd cur 0 x0)
    (lx1 : LoadHolds rd cur 1 x1) (lr0 : LoadHolds rd P.roots 0 root0) (lr1 : LoadHolds rd P.roots 1 root1)
    {kret : List E → Prop}
    (hv : ∀ j < 61, σ (.n j) = (osHeadVals cfg fs0 fs1 target root0 root1 cur cv x0 x1 P).getD j 0) :
    Stmt.HoldsList C rd σ (osHead cfg).1 True kret ∧
      OsAt σ (osHead cfg).2 (obsCv (obsCv cv x0) x1) cur 2 ∧ (osHead cfg).2.co = 2 ∧
      [σ (.n (osHead cfg).2.c), σ (.n (osHead cfg).2.b), σ (.n (osHead cfg).2.a)] = [x0, target + x1, x1] ∧
      σ (.n (osHead cfg).2.t) = target ∧ OsPtrsAt σ P ∧ (osHead cfg).2.k = 61 := by
  set A : List E := [fs0, fs1, target, root0, root1, cur, fs0, fs1]
  set B := osFsNextVals x0 cv
  set Cn := osFsNextVals x1 (obsCv cv x0)
  set D : List E := [target + x1, osGw (4 * cfg.capLen), P.caps, osGw cfg.capLen, P.flags, osGw cfg.yrLen, P.fmsg,
      osGw (2 * cfg.levels.length), P.roots, osGw cfg.nFolds, P.fch, osGw cfg.levels.length, P.betas,
      osGw (cfg.levels.length * cfg.maxQ), P.qw, osGw cfg.posLen, P.qpos, osGw cfg.posLen, P.qbp,
      osGw (cfg.levels.length * 22), P.oodz, osGw (cfg.levels.length * 4), P.ood] with hD
  have hV : osHeadVals cfg fs0 fs1 target root0 root1 cur cv x0 x1 P = A ++ B ++ Cn ++ D := rfl
  have hl : (A ++ B ++ Cn ++ D).length = 61 := by rw [← hV]; exact os_length_headVals _ _ _ _ _ _ _ _ _ _ _
  have hv' : ∀ j < (A ++ B ++ Cn ++ D).length, σ (.n (0 + j)) = (A ++ B ++ Cn ++ D).getD j 0 := fun j hj => by
    rw [Nat.zero_add, ← hV]; exact hv j (by rw [hl] at hj; exact hj)
  obtain ⟨hABC, gD⟩ := os_look_app hv'
  obtain ⟨hAB, gC⟩ := os_look_app hABC
  obtain ⟨gA, gB⟩ := os_look_app hAB
  have lA : A.length = 8 := rfl
  have lB : B.length = 15 := os_length_fsNextVals _ _
  have lC : Cn.length = 15 := os_length_fsNextVals _ _
  simp only [List.length_append, lA, lB, lC, Nat.zero_add] at gB gC gD
  have a0 : σ (.n 0) = fs0 := gA 0 (by simp [A])
  have a1 : σ (.n 1) = fs1 := gA 1 (by simp [A])
  have a2 : σ (.n 2) = target := gA 2 (by simp [A])
  have a3 : σ (.n 3) = root0 := gA 3 (by simp [A])
  have a4 : σ (.n 4) = root1 := gA 4 (by simp [A])
  have a5 : σ (.n 5) = cur := gA 5 (by simp [A])
  have a6 : σ (.n 6) = fs0 := gA 6 (by simp [A])
  have a7 : σ (.n 7) = fs1 := gA 7 (by simp [A])
  have d : ∀ j < 23, σ (.n (38 + j)) = D.getD j 0 := fun j hj => gD j (by simp [hD]; omega)
  have d0 := d 0 (by omega); have d1 := d 1 (by omega); have d2 := d 2 (by omega); have d3 := d 3 (by omega)
  have d4 := d 4 (by omega); have d5 := d 5 (by omega); have d6 := d 6 (by omega); have d7 := d 7 (by omega)
  have d8 := d 8 (by omega); have d9 := d 9 (by omega); have d10 := d 10 (by omega)
  have d11 := d 11 (by omega); have d12 := d 12 (by omega); have d13 := d 13 (by omega)
  have d14 := d 14 (by omega); have d15 := d 15 (by omega); have d16 := d 16 (by omega)
  have d17 := d 17 (by omega); have d18 := d 18 (by omega); have d19 := d 19 (by omega)
  have d20 := d 20 (by omega); have d21 := d 21 (by omega); have d22 := d 22 (by omega)
  simp only [hD, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero, Nat.reduceAdd]
    at d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22
  set s0 : OsSt := ⟨8, 6, 7, 5, 0, 0, 0, 0, 2⟩
  have hat0 : OsAt σ s0 cv cur 0 := ⟨by show (σ (.n 6), σ (.n 7)) = _; rw [a6, a7, hcv],
    by show σ (.n 5) * gen ^ 0 = cur * gen ^ 0; rw [a5]⟩
  obtain ⟨hF1, hat1⟩ := osFsNext_complete (C := C) (kret := kret) hat0 lx0 fun j hj => gB j hj
  obtain ⟨hF2, hat2⟩ := osFsNext_complete (C := C) (kret := kret) hat1 (by simpa using lx1) fun j hj =>
    gC j hj
  have b0 : σ (.n 8) = x0 := by simpa [B, osFsNextVals] using gB 0 (by omega)
  have c0 : σ (.n 23) = x1 := by simpa [Cn, osFsNextVals] using gC 0 (by omega)
  refine ⟨?_, ⟨hat2.fs, hat2.cursor⟩, rfl, ?_, a2, ⟨d2, d4, d6, d8, d10, d12, d14, d16, d18, d20, d22⟩, rfl⟩
  · unfold osHead
    dsimp only
    simp only [holdsList_append]
    refine (holdsList_noRet _ rfl _ _).mpr ⟨?_, (holdsList_noRet _ rfl _ _).mpr ⟨hF1,
      (holdsList_noRet _ rfl _ _).mpr ⟨hF2, ?_⟩⟩⟩
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      exact ⟨by rw [a6, a0], by rw [a7, a1]⟩
    · simp only [osHeap, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, true_and]
      refine ⟨by rw [d0, a2, c0], d1, d3, d5, d7, by rw [a3, show osRoots = 46 from rfl, d8]; exact lr0, by rw [a4, show osRoots = 46 from rfl, d8]; exact lr1, d9, d11,
        d13, d15, d17, d19, d21⟩
  · show [σ (.n 8), σ (.n 38), σ (.n 23)] = _
    rw [b0, d0, c0]

end
end LeanVM.Guest.B1
