/-
  LeanVM.Guest.B1.OpeningOod

  B1 for `opening_ood_point` and its loop `__loop9`: `n` squeezes, the challenges stored, the
  states chained through a heap run.
-/

module

public import LeanVM.Guest.B1.Loops

/-!
# `opening_ood_point` (TRIAGE #32)

`opening_ood_point(fs0, fs1, point, g^n)` (G:927-941) squeezes `n` challenges (`sampleN n`,
V:443) into `point`, carrying the state through a `HeapBuf` run `states` (state `j` at
`states·g^(2j)`, `states·g^(2j+1)`), one `squeeze_step` per iteration of `__loop9`. At `n = 0`
nothing is squeezed and the arguments are returned as they are; the state is a digest's only
once a squeeze reads it.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Squeezes, one at a time -/

theorem sqAll_succ_snd (j : ℕ) (cv : Digest) : (sqAll (j + 1) cv).2 = sqCv (sqAll j cv).2 := by
  induction j generalizing cv with
  | zero => rfl
  | succ j ih => exact ih (sqCv cv)

theorem length_sqAll (j : ℕ) (cv : Digest) : (sqAll j cv).1.length = j := by
  induction j generalizing cv with
  | zero => rfl
  | succ j ih => simp [sqAll, ih]

theorem sqAll_getElem (m : ℕ) (cv : Digest) (j : ℕ) (hj : j < (sqAll m cv).1.length) :
    (sqAll m cv).1[j] = challengeOf (sqCv (sqAll j cv).2) := by
  induction m generalizing cv j with
  | zero => simp [sqAll] at hj
  | succ m ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [sqAll, List.getElem_cons_succ]
      rw [ih (sqCv cv) j (by simpa [sqAll] using hj)]

/-! ## `__loop9` -/

/-- The body of `__loop9` at `x`: the state at `states·x²` is a digest's, its squeeze's
challenge goes to `point·x` and the squeezed state after it. -/
def Loop9Body (rd : Reader) (st point x : E) : Prop :=
  ∃ cv, LoadHolds rd (st * x * x) 0 (digestScalars cv).1 ∧
    LoadHolds rd (st * x * x) 1 (digestScalars cv).2 ∧
    LoadHolds rd (point * x) 0 (challengeOf (sqCv cv)) ∧
    LoadHolds rd (st * x * x) 2 (digestScalars (sqCv cv)).1 ∧
    LoadHolds rd (st * x * x) 3 (digestScalars (sqCv cv)).2

theorem find_loop9 : coreProgram.find? "__loop9" = some Data.core39 :=
  Program.find?_of_indexOf? (j := 39) (by decide +kernel) rfl

theorem core39_body : Fn.body Data.core39 =
    [.atom (.mul (.n 4) (.n 2) (.n 0)), .atom (.mul (.n 5) (.n 4) (.n 0)),
      .atom (.load (.n 6) (.n 5) 0), .atom (.load (.n 7) (.n 5) 1), .atom (.copy (.n 8) (.n 6)),
      .atom (.copy (.n 9) (.n 7))] ++
    squeezeT (.n 8) (.n 9) 10 ++
    [.atom (.copy (.n 24) (.n 15)), .atom (.copy (.n 25) (.n 16)), .atom (.mul (.n 26) (.n 3) (.n 0)),
      .atom (.load (.n 23) (.n 26) 0), .atom (.load (.n 24) (.n 5) 2), .atom (.load (.n 25) (.n 5) 3),
      .atom (.const (.n 27) (word 2 0 0)), .atom (.mul (.n 28) (.n 0) (.n 27)),
      .atom (.add (.n 29) (.n 28) (.n 1)), .atom (.const (.n 30) (word 2 0 0)),
      .atom (.mul (.n 31) (.n 0) (.n 30)), .callIf (.n 29) "__loop9" [.n 31, .n 1, .n 2, .n 3],
      .ret []] := rfl

theorem loop9_step (rd : Reader) (N st point : E) (d : ℕ) (x : E) :
    coreProgram.relN rd (d + 1) "__loop9" (x :: [N, st, point]) [] ↔
      Loop9Body rd st point x ∧ IsInK (x * gen + N) ∧
        (x * gen + N ≠ 0 → coreProgram.relN rd d "__loop9" (x * gen :: [N, st, point]) []) := by
  rw [relN_succ_iff find_loop9, show Fn.params Data.core39 = [.n 0, .n 1, .n 2, .n 3] from rfl,
    core39_body]
  simp only [holdsList_append, holds_squeezeT, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    List.map_cons, List.map_nil, and_true, word_gen]
  constructor
  · rintro ⟨σ, hp, h4, h5, l6, l7, h8, h9, ⟨cv, hcv, e⟩, h24, h25, h26, l23, l24, l25, h27, h28,
      h29, h30, h31, hK, hcall⟩
    simp only [List.cons.injEq] at hp
    obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hp
    have f15 : σ (.n 15) = (digestScalars (sqCv cv)).1 := e 5 (by omega)
    have f16 : σ (.n 16) = (digestScalars (sqCv cv)).2 := e 6 (by omega)
    have f23 : σ (.n 23) = challengeOf (sqCv cv) := e 13 (by omega)
    rw [h5, h4] at l6 l7 l24 l25
    rw [h8] at hcv
    rw [h9] at hcv
    refine ⟨⟨cv, ?_, ?_, ?_, ?_, ?_⟩, by rwa [h29, h28, h27] at hK, fun hne => ?_⟩
    · rw [show σ (.n 6) = (digestScalars cv).1 from congrArg Prod.fst hcv] at l6; exact l6
    · rw [show σ (.n 7) = (digestScalars cv).2 from congrArg Prod.snd hcv] at l7; exact l7
    · rw [h26, f23] at l23; exact l23
    · rw [h24, f15] at l24; exact l24
    · rw [h25, f16] at l25; exact l25
    · have := hcall (by rwa [h29, h28, h27])
      rwa [h31, h30] at this
  · rintro ⟨⟨cv, l6, l7, l23, l24, l25⟩, hK, hcall⟩
    refine ⟨setl (setv (setl (Val.ofArgs [x, N, st, point]) 4
      [st * x, st * x * x, (digestScalars cv).1, (digestScalars cv).2, (digestScalars cv).1,
        (digestScalars cv).2]) 10 14 (sqVals cv)) 24
      [sqVals cv 5, sqVals cv 6, point * x, gen, x * gen, x * gen + N, gen, x * gen], ?_, ?_⟩
    · b1_look
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨cv, ?_, fun k hk => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_⟩
      all_goals (try b1_look)
      · exact l6
      · exact l7
      · exact l23
      · exact l24
      · exact l25
      · exact hK
      · exact hcall

/-! ## `opening_ood_point` -/

/-- The states of the run, after each squeeze. -/
def OodScratch (rd : Reader) (p : E) (cv : Digest) (m : ℕ) : Prop :=
  ∀ j ≤ m, LoadHolds rd p (2 * j) (digestScalars (sqAll j cv).2).1 ∧
    LoadHolds rd p (2 * j + 1) (digestScalars (sqAll j cv).2).2

/-- **`opening_ood_point(fs0, fs1, point, g^n)`** (G:927-941; TRIAGE #32): `n` below the order
of `g`, and the run `p` holding the states; at `n = 0` it holds the arguments, which are
returned; otherwise they are the cells of `cv`, the `n` challenges of `sampleN n` (V:443) are
stored at `point`, and the function returns the final state's cells. -/
def MeaningOpeningOodPoint (rd : Reader) : List E → List E → Prop
  | [fs0, fs1, point, ng], rets =>
      ∃ m < ordG, ng = gen ^ m ∧ ∃ p,
        (m = 0 ∧ LoadHolds rd p 0 fs0 ∧ LoadHolds rd p 1 fs1 ∧ rets = [fs0, fs1]) ∨
        (0 < m ∧ ∃ cv rs cv', (fs0, fs1) = digestScalars cv ∧ RunsTo (Prog.sampleN m) cv [] rs cv' ∧
          ReadsAt rd point rs ∧ OodScratch rd p cv m ∧
          rets = [(digestScalars cv').1, (digestScalars cv').2])
  | _, _ => False

theorem find_opening_ood_point : coreProgram.find? "opening_ood_point" = some Data.core9 :=
  Program.find?_of_indexOf? (j := 9) (by decide +kernel) rfl

/-- The loop's bodies below `m > 0`: the states are the squeezes of the first, and the
challenges are stored at `point`. -/
theorem loop9_bodies_iff (rd : Reader) (st point : E) (m : ℕ) (hm : 0 < m) :
    (∀ j < m, Loop9Body rd st point (gen ^ j)) ↔
      ∃ cv, OodScratch rd st cv m ∧ ReadsAt rd point (sqAll m cv).1 := by
  have hx : ∀ j k w, LoadHolds rd (st * gen ^ j * gen ^ j) k w ↔ LoadHolds rd st (2 * j + k) w :=
    fun j k w => by rw [mul_assoc, ← pow_add, loadHolds_mul_gen_pow, ← two_mul]
  have hp : ∀ j w, LoadHolds rd (point * gen ^ j) 0 w ↔ LoadHolds rd point j w :=
    fun j w => by rw [loadHolds_mul_gen_pow, Nat.add_zero]
  simp only [Loop9Body, hx, hp]
  constructor
  · intro h
    obtain ⟨cv, l0, l1, -⟩ := h 0 hm
    have hst : ∀ j ≤ m, LoadHolds rd st (2 * j) (digestScalars (sqAll j cv).2).1 ∧
        LoadHolds rd st (2 * j + 1) (digestScalars (sqAll j cv).2).2 := by
      intro j hj
      induction j with
      | zero => exact ⟨l0, l1⟩
      | succ j ih =>
        obtain ⟨cvj, a0, a1, -, a2, a3⟩ := h j (by omega)
        obtain ⟨b0, b1⟩ := ih (by omega)
        have hc : cvj = (sqAll j cv).2 := digestScalars_injective (Prod.ext
          (loadHolds_unique (by simpa using a0) b0) (loadHolds_unique a1 b1))
        subst hc
        rw [sqAll_succ_snd, show 2 * (j + 1) = 2 * j + 2 by ring,
          show 2 * j + 2 + 1 = 2 * j + 3 by ring]
        exact ⟨a2, a3⟩
    refine ⟨cv, hst, fun j hj => ?_⟩
    rw [length_sqAll] at hj
    obtain ⟨cvj, a0, a1, a2, -⟩ := h j hj
    obtain ⟨b0, b1⟩ := hst j (by omega)
    have hc : cvj = (sqAll j cv).2 := digestScalars_injective (Prod.ext
      (loadHolds_unique (by simpa using a0) b0) (loadHolds_unique a1 b1))
    subst hc
    rw [sqAll_getElem]
    exact a2
  · rintro ⟨cv, hst, hpt⟩ j hj
    obtain ⟨b0, b1⟩ := hst j (by omega)
    obtain ⟨c0, c1⟩ := hst (j + 1) (by omega)
    have r := hpt j (by rw [length_sqAll]; exact hj)
    rw [sqAll_getElem] at r
    rw [sqAll_succ_snd, show 2 * (j + 1) = 2 * j + 2 by ring] at c0 c1
    rw [show 2 * j + 2 + 1 = 2 * j + 3 by ring] at c1
    exact ⟨(sqAll j cv).2, by simpa using b0, b1, r, c0, c1⟩

theorem opening_ood_point_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_ood_point" args rets ↔ MeaningOpeningOodPoint rd args rets := by
  rw [rel_iff_sem find_opening_ood_point,
    show Fn.params Data.core9 = [.n 0, .n 1, .n 2, .n 3] from rfl,
    show Fn.body Data.core9 = Data.core9.body from rfl, Data.core9.body]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_one,
    word_gen, true_and]
  constructor
  · rintro ⟨σ, hp, h4, h5, h6, l0, l1, h8, h9, h10, hK, hcall, h11, h12, l13, l14, hret⟩
    subst hp
    rw [h9, h8] at hK hcall
    rw [h10] at hcall
    obtain ⟨m, hm, hN, hB⟩ := (guarded_loop_iff (loop9_step rd (σ (.n 3)) (σ (.n 7))
      (σ (.n 2)))).mp ⟨hK, hcall⟩
    have hx : ∀ k w, LoadHolds rd (σ (.n 12)) k w ↔ LoadHolds rd (σ (.n 7)) (2 * m + k) w := by
      intro k w
      rw [h12, h11, hN, mul_assoc, ← pow_add, loadHolds_mul_gen_pow, ← two_mul]
    rw [hx] at l13 l14
    refine ⟨m, hm, hN, σ (.n 7), ?_⟩
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      refine Or.inl ⟨rfl, l0, l1, ?_⟩
      rw [← hret, loadHolds_unique l13 l0, loadHolds_unique l14 l1]
    · obtain ⟨cv, hst, hpt⟩ := (loop9_bodies_iff rd _ _ m h0).mp hB
      obtain ⟨s0, s1⟩ := hst 0 (by omega)
      rw [show (sqAll 0 cv).2 = cv from rfl, Nat.mul_zero] at s0 s1
      obtain ⟨t0, t1⟩ := hst m le_rfl
      refine Or.inr ⟨h0, cv, _, _, ?_, runsTo_sampleN m cv, hpt, hst, ?_⟩
      · exact Prod.ext (loadHolds_unique l0 s0) (loadHolds_unique l1 s1)
      · rw [← hret, loadHolds_unique l13 (by simpa using t0), loadHolds_unique l14 t1]
  · intro hm
    obtain ⟨fs0, fs1, point, ng, rfl⟩ : ∃ fs0 fs1 point ng, args = [fs0, fs1, point, ng] := by
      match args, hm with
      | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
    obtain ⟨m, hm, hN, p, h⟩ := hm
    have hcl : (IsInK (1 + ng) ∧ (1 + ng ≠ 0 → coreProgram.Rel rd "__loop9" [1, ng, p, point] [])) ∧
        LoadHolds rd p 0 fs0 ∧ LoadHolds rd p 1 fs1 ∧
        LoadHolds rd p (2 * m) (rets.getD 0 0) ∧ LoadHolds rd p (2 * m + 1) (rets.getD 1 0) ∧
        rets = [rets.getD 0 0, rets.getD 1 0] := by
      rcases h with ⟨rfl, l0, l1, rfl⟩ | ⟨h0, cv, rs, cv', hcv, hrun, hpt, hst, rfl⟩
      · refine ⟨(guarded_loop_iff (loop9_step rd ng p point)).mpr
          ⟨0, by decide, hN, fun j hj => absurd hj (Nat.not_lt_zero j)⟩, l0, l1, l0, l1, rfl⟩
      · obtain ⟨rfl, rfl⟩ := (runsTo_sampleN m cv).iff.mp hrun
        obtain ⟨s0, s1⟩ := hst 0 (by omega)
        rw [show (sqAll 0 cv).2 = cv from rfl, Nat.mul_zero] at s0 s1
        obtain ⟨t0, t1⟩ := hst m le_rfl
        refine ⟨(guarded_loop_iff (loop9_step rd ng p point)).mpr
          ⟨m, hm, hN, (loop9_bodies_iff rd p point m h0).mpr ⟨cv, hst, hpt⟩⟩, ?_, ?_, t0, t1, rfl⟩
        · rw [show fs0 = (digestScalars cv).1 from congrArg Prod.fst hcv]; exact s0
        · rw [show fs1 = (digestScalars cv).2 from congrArg Prod.snd hcv]; exact s1
    obtain ⟨⟨hK, hcall⟩, l0, l1, l13, l14, hret⟩ := hcl
    have hx : ∀ k w, LoadHolds rd (p * ng * ng) k w ↔ LoadHolds rd p (2 * m + k) w := by
      intro k w
      rw [hN, mul_assoc, ← pow_add, loadHolds_mul_gen_pow, ← two_mul]
    refine ⟨setl (Val.ofArgs [fs0, fs1, point, ng]) 4 [gen, ng * gen, ng * gen * (ng * gen), p,
      1, 1 + ng, 1, p * ng, p * ng * ng, rets.getD 0 0, rets.getD 1 0], ?_, ?_⟩
    · b1_look
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals (try b1_look)
      · exact l0
      · exact l1
      · exact hK
      · exact hcall
      · exact (hx 0 _).mpr l13
      · exact (hx 1 _).mpr l14
      · exact hret.symm

/-! ## Completeness at a given buffer -/

/-- `MeaningOpeningOodPoint` at the state buffer `p` (a `HeapBuf` the caller's allocator names). -/
def MeaningOpeningOodPointAt (rd : Reader) (p : E) : List E → List E → Prop
  | [fs0, fs1, point, ng], rets =>
      ∃ m < ordG, ng = gen ^ m ∧
        ((m = 0 ∧ LoadHolds rd p 0 fs0 ∧ LoadHolds rd p 1 fs1 ∧ rets = [fs0, fs1]) ∨
        (0 < m ∧ ∃ cv rs cv', (fs0, fs1) = digestScalars cv ∧ RunsTo (Prog.sampleN m) cv [] rs cv' ∧
          ReadsAt rd point rs ∧ OodScratch rd p cv m ∧
          rets = [(digestScalars cv').1, (digestScalars cv').2]))
  | _, _ => False

theorem opening_ood_point_complete (rd : Reader) (p : E) (args rets : List E)
    (h : MeaningOpeningOodPointAt rd p args rets) : coreProgram.Rel rd "opening_ood_point" args rets :=
  (opening_ood_point_iff rd args rets).mpr (by
    match args, h with
    | [_, _, _, _], ⟨m, hm, hn, hb⟩ => exact ⟨m, hm, hn, p, hb⟩)

end
end LeanVM.Guest.B1
