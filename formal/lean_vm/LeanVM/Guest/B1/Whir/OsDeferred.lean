/-
  LeanVM.Guest.B1.Whir.OsDeferred

  The deferring verifier's query steps include its stacked opening's.
-/

module

public import LeanVM.Guest.B1.Whir.OsSteps
public import LeanVM.Guest.B1.VerifySub.Run

/-!
# The opening's query steps among the deferring verifier's (TRIAGE #36)

`os_mem_queriesOf_bind_left`: a program's query steps are among its bind's. `os_deferred_queries`:
on the stream `verifyDeferred_true` assembles, every query step of the stacked opening, from the
state the ring switch leaves, is a query step of the deferring verifier's run from the seed.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- **A program's query steps are among its bind's.** -/
theorem os_mem_queriesOf_bind_left {α β : Type} (p : Prog α) (f : α → Prog β) :
    ∀ (s : St) {b : ℕ × List (ℕ × Opening)}, b ∈ queriesOf p s → b ∈ queriesOf (p.bind f) s := by
  induction p with
  | ret a0 => intro s b h; simp [queriesOf] at h
  | fail => intro s b h; simp [queriesOf] at h
  | read k ih =>
    intro s b h
    obtain ⟨cv, xs, os, roots⟩ := s
    cases xs with
    | nil => simp [queriesOf] at h
    | cons x xs => exact ih x _ h
  | sample k ih => intro s b h; exact ih _ _ h
  | grind bits k ih =>
    intro s b h
    obtain ⟨cv, xs, os, roots⟩ := s
    cases xs with
    | nil => simp [queriesOf] at h
    | cons n xs =>
      simp only [queriesOf, Prog.bind] at h ⊢
      split at h
      · rename_i hp
        simp only [hp, ↓reduceIte]
        exact ih _ h
      · simp at h
  | commit hh ww k ih =>
    intro s b h
    obtain ⟨cv, xs, os, roots⟩ := s
    match xs, h with
    | [], h => simp [queriesOf] at h
    | [_], h => simp [queriesOf] at h
    | x0 :: x1 :: xs, h =>
      simp only [queriesOf, Prog.bind] at h ⊢
      split at h
      · rename_i root hr
        try simp only [hr]
        exact ih _ h
      · simp at h
  | query i ps k ih =>
    intro s b h
    simp only [queriesOf, Prog.bind] at h ⊢
    split at h
    · simp at h
    · rename_i root hh ww hr
      try simp only [hr]
      split at h
      · rename_i rows rest hoa
        simp only [List.mem_cons] at h ⊢
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (ih rows _ h)
      · simp at h

/-- A continuation's query steps, from where the first program ends, are among the bind's. -/
theorem os_mem_queriesOf_bind_right {α β : Type} {p : Prog α} {f : α → Prog β} {s s' : St} {a : α}
    (h : Runs p s a s') {b : ℕ × List (ℕ × Opening)} (hb : b ∈ queriesOf (f a) s') :
    b ∈ queriesOf (p.bind f) s := by
  rw [os_queriesOf_bind p f s h]
  exact List.mem_append_right _ hb

/-- **The stacked opening's query steps are the deferring verifier's**, on the stream of the phases'
words from the seed's chain state. -/
theorem os_deferred_queries {bytecode : List K} (hb : bytecode.length = 2 ^ 22)
    (seed pi : Digest) (c : FixedClaims) {logMem rate : ℕ} {rows : List ℕ}
    (hm1 : 16 ≤ logMem) (hm2 : logMem ≤ 32) (hr1 : 1 ≤ rate) (hr2 : rate ≤ 4)
    (hl : rows.length = 6) (hrows : ∀ n ∈ rows, n ≤ 2 ^ 32)
    (hs1 : 22 ≤ (layoutOf bytecode logMem rows).stackLog)
    (hs2 : (layoutOf bytecode logMem rows).stackLog ≤ 28)
    {x0 x1 : E} {root : Digest} (hroot : (x0, x1) = digestScalars root)
    {cv10 cvG cvT cvF : Digest} {xsG xsT xsF xsW : List E} {os : List Opening}
    (h10 : cv10 = obsAll (obsAll (blake2sBytes (digestBytes seed ++ digestBytes pi))
      (announce logMem rows rate)) [x0, x1])
    {gr : E × List E × List E}
    (hG : RunsTo (gkrPhase (pushDepth (layoutOf bytecode logMem rows)))
      (sqCv (sqAll 4 cv10).2) xsG gr cvG)
    {bus : BusResult} {claims : List ColumnClaim}
    (hT : RunsTo (tablesSeg (.claimed c) (layoutOf bytecode logMem rows) pi (sqAll 4 cv10).1
      (challengeOf (sqCv (sqAll 4 cv10).2)) gr.2.1 gr.2.2) cvG xsT (bus, claims) cvT)
    {fp s : List E}
    (hF : RunsTo (verifyFlock (.claimed c) (blake2sR1csLogSize +
      (layoutOf bytecode logMem rows).tableLogHeights.getD opBlake2s 0)) cvT xsF (fp, s) cvF) :
    ∀ b ∈ queriesOf (whirOpen (layoutOf bytecode logMem rows).stackLog rate
        (dot (powers (challengeOf (sqCv (sqAll 6 cvF).2)) (claims.length + 1))
          (ringTarget s (sqAll 6 cvF).1 :: claims.map (·.value))))
        ⟨sqCv (sqAll 6 cvF).2, xsW, os, [(root, stackShape (layoutOf bytecode logMem rows).stackLog rate)]⟩,
      b ∈ queriesOf (deferredProgram c bytecode pi)
        ⟨blake2sBytes (digestBytes seed ++ digestBytes pi),
          announce logMem rows rate ++ x0 :: x1 :: (xsG ++ (xsT ++ (xsF ++ xsW))), os, []⟩ := by
  intro b hbq
  have hcfg : configOk (layoutOf bytecode logMem rows).stackLog rate = true :=
    configOk_window _ (by omega) hs1 _ (by omega) hr1
  unfold deferredProgram
  rw [verifyExecution_split]
  refine os_mem_queriesOf_bind_left _ _ _ ?_
  refine os_mem_queriesOf_bind_right (runs_readSizes hb hm1 hm2 hr1 hr2 hl hrows
    (by unfold minStackedLog Whir.minLogStack; omega) (by exact hs2) _ _ _ _) ?_
  generalize layoutOf bytecode logMem rows = L at hG hT hF hbq hcfg ⊢
  simp only
  refine os_mem_queriesOf_bind_right (runs_commitStack hcfg hroot _ _ _ _) ?_
  rw [← h10]
  refine os_mem_queriesOf_bind_right (RunsTo.runs (runsTo_sampleN 4 cv10) _ _ _) ?_
  refine os_mem_queriesOf_bind_right (RunsTo.runs (runsTo_sampleE _) _ _ _) ?_
  refine os_mem_queriesOf_bind_right (RunsTo.runs hG _ _ _) ?_
  refine os_mem_queriesOf_bind_right (RunsTo.runs hT _ _ _) ?_
  refine os_mem_queriesOf_bind_right (RunsTo.runs hF _ _ _) ?_
  refine os_mem_queriesOf_bind_right (runs_ringSwitch _ _ _ _ _ _) ?_
  unfold verifyStackedOpening
  simp only [verifyWhir_split, Prog.bind_eq]
  rw [show xsW = xsW ++ [] from (List.append_nil _).symm]
  refine os_mem_queriesOf_bind_right (RunsTo.runs (runsTo_sampleE _) _ _ _) ?_
  refine os_mem_queriesOf_bind_left _ _ _ ?_
  simp only [List.append_eq, List.append_nil]
  convert hbq using 4
  all_goals simp [ringSwitchClaim, ColumnClaim.onStack, Function.comp_def]

end
end LeanVM.Guest.B1
