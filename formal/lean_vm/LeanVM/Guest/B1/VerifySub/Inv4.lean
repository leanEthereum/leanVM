/-
  LeanVM.Guest.B1.VerifySub.Inv4

  The announced sizes, the stack's root, the ring switch and the opening's runs, backward.
-/

module

public import LeanVM.Guest.B1.VerifySub.Inv3

/-!
# The sizes, the root, the ring switch and the opening, backward

* `vs_readSizes_inv`: a run of `readSizes` reads the eight announced words of some memory
  log-size, row counts and rate within `buildLayout`'s and `readSizes`' bounds, and returns
  `layoutOf`'s layout;
* `vs_commitStack_inv`: a run of `commitStack` reads the two words of some root and records it;
* `vs_ringSwitch_inv`, `vs_opening_inv`: the ring switch's challenges, and the opening's
  challenge, run and terminal check.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem runs_liftOption_inv {α : Type} {o : Option α} {a : α} {s s' : St}
    (h : Runs (Verifier.liftOption o) s a s') : o = some a ∧ s' = s := by
  match o, h with
  | none, h => cases h
  | some b, h =>
    obtain ⟨rfl, rfl⟩ := runs_ret_inv h
    exact ⟨rfl, rfl⟩

/-- A run of a program known to run from a state returns what it returns there. -/
theorem runs_det {α : Type} {p : Prog α} {cv cv' : Digest} {ys : List E} {a a' : α}
    (h : RunsTo p cv ys a cv') {rest : List E} {os : List Opening} {roots : List (Digest × ℕ × ℕ)}
    {s' : St} (h' : Runs p ⟨cv, ys ++ rest, os, roots⟩ a' s') :
    a' = a ∧ s' = ⟨cv', rest, os, roots⟩ := by
  unfold Runs at h'
  rw [h rest os roots, Option.some.injEq, Prod.mk.injEq] at h'
  exact ⟨h'.1.symm, h'.2.symm⟩

theorem runs_sampleN_det {n : ℕ} {s s' : St} {xs : List E} (h : Runs (Prog.sampleN n) s xs s') :
    xs = (sqAll n s.cv).1 ∧ s' = { s with cv := (sqAll n s.cv).2 } := by
  obtain ⟨cv, ys, os, roots⟩ := s
  exact runs_det (ys := []) (runsTo_sampleN n cv) h

theorem runs_sampleE_det {s s' : St} {x : E} (h : Runs Prog.sampleE s x s') :
    x = challengeOf (sqCv s.cv) ∧ s' = { s with cv := sqCv s.cv } := runs_sampleE_inv h

/-! ## The announced sizes -/

theorem buildLayout_inv {bytecode : List K} (hb : bytecode.length = 2 ^ 22) {logMem : ℕ}
    {rows : List ℕ} {L : Layout} (h : buildLayout bytecode logMem rows = some L) :
    16 ≤ logMem ∧ logMem ≤ 32 ∧ rows.length = 6 ∧ (∀ n ∈ rows, n ≤ 2 ^ 32) ∧
      L = layoutOf bytecode logMem rows := by
  have hc : 16 ≤ logMem ∧ logMem ≤ 32 ∧ rows.length = 6 ∧ ∀ n ∈ rows, n ≤ 2 ^ 32 := by
    unfold buildLayout at h
    rw [hb, log2Strict_two_pow_22] at h
    simp only at h
    split at h
    · rename_i hc
      obtain ⟨-, h1, h2, h3, -, h4⟩ := hc
      exact ⟨h1, h2, h4, fun n hn => by simpa using List.all_eq_true.mp h3 n hn⟩
    · cases h
  obtain ⟨h1, h2, h3, h4⟩ := hc
  rw [buildLayout_eq hb h1 h2 h3 h4, Option.some.injEq] at h
  exact ⟨h1, h2, h3, h4, h.symm⟩

theorem inv_eq_eOfNat {x : E} (h1 : x.limb 1 = 0) (h2 : x.limb 2 = 0) :
    x = eOfNat (kToNat (x.limb 0)) := by
  rw [eOfNat, ofBits_kToNat, ← eq_ofK_limb ⟨h1, h2⟩]

theorem announce_of {a : List E} (hl : a.length = 8)
    (hz : (a.all fun value ↦ decide (value.limb 1 = 0 ∧ value.limb 2 = 0)) = true) :
    a = announce (kToNat ((a.headD 0).limb 0))
      (((a.drop 1).take tables.length).map fun value ↦ kToNat (value.limb 0))
      (kToNat ((a.getLastD 0).limb 0)) := by
  match a, hl with
  | [a0, a1, a2, a3, a4, a5, a6, a7], _ =>
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
      at hz
    obtain ⟨⟨z0, z0'⟩, ⟨z1, z1'⟩, ⟨z2, z2'⟩, ⟨z3, z3'⟩, ⟨z4, z4'⟩, ⟨z5, z5'⟩, ⟨z6, z6'⟩,
      ⟨z7, z7'⟩⟩ := hz
    simp only [announce, tables_length, List.headD_cons, List.drop_succ_cons, List.drop_zero,
      List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.getLastD_eq_getLast?,
      List.getLast?_cons_cons, List.getLast?_singleton, Option.getD_some, List.cons_append,
      List.nil_append]
    rw [← inv_eq_eOfNat z0 z0', ← inv_eq_eOfNat z1 z1', ← inv_eq_eOfNat z2 z2',
      ← inv_eq_eOfNat z3 z3', ← inv_eq_eOfNat z4 z4', ← inv_eq_eOfNat z5 z5',
      ← inv_eq_eOfNat z6 z6', ← inv_eq_eOfNat z7 z7']

/-- **The announced sizes, backward.** -/
theorem vs_readSizes_inv {bytecode : List K} (hb : bytecode.length = 2 ^ 22) {s s' : St}
    {lr : Layout × ℕ} (h : Runs (readSizes bytecode) s lr s') :
    ∃ logMem rows rate, lr = (layoutOf bytecode logMem rows, rate) ∧
      s.stream = announce logMem rows rate ++ s'.stream ∧
      s'.cv = obsAll s.cv (announce logMem rows rate) ∧ s'.openings = s.openings ∧
      s'.roots = s.roots ∧ 16 ≤ logMem ∧ logMem ≤ 32 ∧ 1 ≤ rate ∧ rate ≤ 4 ∧ rows.length = 6 ∧
      (∀ n ∈ rows, n ≤ 2 ^ 32) ∧ (layoutOf bytecode logMem rows).stackLog ≤ 28 := by
  unfold readSizes at h
  obtain ⟨a, s1, hr, h⟩ := runs_bind_inv' h
  obtain ⟨u1, s2, hq1, h⟩ := runs_bind_inv' h
  dsimp only at h
  obtain ⟨u2, s3, hq2, h⟩ := runs_bind_inv' h
  obtain ⟨L, s4, hlo, h⟩ := runs_bind_inv' h
  obtain ⟨u3, s5, hq3, h⟩ := runs_bind_inv' h
  obtain ⟨rfl, rfl⟩ := runs_pure_inv h
  obtain ⟨hz, rfl⟩ := runs_require_inv hq1
  obtain ⟨⟨hr1, hr2⟩, rfl⟩ := runs_require_inv hq2
  obtain ⟨hbl, rfl⟩ := runs_liftOption_inv hlo
  obtain ⟨⟨-, hs2⟩, rfl⟩ := runs_require_inv hq3
  obtain ⟨hal, hs, hc, ho, hro⟩ := runs_readN_inv hr
  obtain ⟨h1, h2, h3, h4, rfl⟩ := buildLayout_inv hb hbl
  have ha := announce_of (by rw [hal]; rfl) hz
  refine ⟨_, _, _, rfl, by rw [hs, ← ha], by rw [hc, ← ha], ho, hro, h1, h2, hr1, hr2, h3, h4, ?_⟩
  exact hs2

/-! ## The stack's root -/

/-- **The stack's root, backward.** -/
theorem vs_commitStack_inv {μ r : ℕ} {s s' : St} {u : Unit} (h : Runs (commitStack μ r) s u s') :
    ∃ (x0 x1 : E) (root : Digest), (x0, x1) = digestScalars root ∧
      s.stream = x0 :: x1 :: s'.stream ∧ s'.cv = obsAll s.cv [x0, x1] ∧
      s'.openings = s.openings ∧ s'.roots = s.roots ++ [(root, stackShape μ r)] := by
  unfold commitStack at h
  obtain ⟨cfg, s1, hc, h⟩ := runs_bind_inv' h
  obtain ⟨hcfg, hs1⟩ := runs_liftOption_inv hc
  rw [hs1] at h
  cases cfg with
  | nil => cases h
  | cons level levels =>
    obtain ⟨cv, xs, os, roots⟩ := s
    match xs, h with
    | [], h => cases h
    | [_], h => cases h
    | x0 :: x1 :: xs, h =>
      unfold Runs at h
      simp only [Prog.commitP, runId, Compile.run] at h
      split at h
      · rename_i root hroot
        cases h
        refine ⟨x0, x1, root, (digestScalars_digestOfScalars hroot).symm, rfl, rfl, rfl, ?_⟩
        simp only [stackShape, hcfg]
      · cases h

end
end LeanVM.Guest.B1.VerifySub
