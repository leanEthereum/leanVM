/-
  LeanVM.Guest.B1.Whir.CLp

  `level_positions`, honestly: its loop's iteration, the loop, and the function.
-/

module

public import LeanVM.Guest.B1.Whir.CPrim
public import LeanVM.Guest.B1.Whir.HelperT

/-!
# `level_positions`, honestly

`lpIter_completeC`: one iteration of `level_positions`' loop (`lpLoopBody d cd`) at `x`, its row
of the squeeze run holding the capacity and the next row the permutation's, its
`decode_query_windows` call holding of the challenge and the shifted pointers, holds at an explicit
valuation. `lp_complete`: on a squeeze run holding the chain of capacities from `cap`
(`sqCaps`), each squeeze's challenge decoded, `level_positions` relates `cap ++ [pos, wp, tabs]`
to the last capacity.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The name of `decode_query_windows`' specialization at a tree depth and a cap depth. -/
def qwDecName (d cd : ℕ) : String := "decode_query_windows__L" ++ natStr d ++ "_L" ++ natStr cd

/-- The loop's iteration before its tail. -/
def lpIterA (d cd : ℕ) : List Stmt :=
  let pw := osPowSteps 0 (osPowDigits (192 / d)) 0 40
  let e := 40 + osPowLen (192 / d)
  [.atom (.mul (.n 6) (.n 0) (.n 0)), .atom (.mul (.n 7) (.n 6) (.n 6)), .atom (.mul (.n 8) (.n 7) (.n 0)),
    .atom (.mul (.n 9) (.n 2) (.n 8))] ++
    ((List.range 5).map fun i ↦ .atom (.load (.n (10 + i)) (.n 9) i)) ++
    [.atom (.const (.n 15) (word 1 0 0)), .atom (.const (.n 16) (word 0 0 0)),
      .atom (.const (.n 17) (word 0 0 0)), .atom (.const (.n 18) (word 0 0 0)),
      .atom (.const (.n 19) (word 0 0 0))] ++
    osSqueeze0 15 [10, 11, 12, 13, 14] 20 ++
    ((List.range 5).map fun i ↦ .atom (.load (.n (28 + i)) (.n 9) (5 + i))) ++
    pw.1 ++ [.atom (.mul (.n e) (.n 3) (.n pw.2)), .atom (.mul (.n (e + 1)) (.n 4) (.n pw.2))] ++
    [.call (qwDecName d cd) [.n 39, .n e, .n (e + 1), .n 5] []]

/-- The loop tail's first value. -/
def lpIterTail (d : ℕ) : ℕ := 40 + osPowLen (192 / d) + 2

theorem lpIterBody_eq (d cd : ℕ) (name : String) :
    lpLoopBody d cd name = lpIterA d cd ++ osLoopTail name 6 (lpIterTail d) := rfl

theorem lpIterA_flat (d cd : ℕ) : (lpIterA d cd ++ osLoopTailA (lpIterTail d)).all Stmt.flat = true := by
  simp [lpIterA, osSqueeze0, keccakA, challengeT, osLoopTailA, osPowSteps_all_flat, Stmt.flat]

/-- The iteration's values, by segments. -/
def lpIterSegs (d : ℕ) (X N sqz pos wp tabs : E) (cap : List E) : List (ℕ × (ℕ → E)) :=
  [(6, fun i ↦ [X, N, sqz, pos, wp, tabs].getD i 0),
    (4, fun i ↦ [X * X, X * X * (X * X), X * X * (X * X) * X, sqz * (X * X * (X * X) * X)].getD i 0),
    (5, fun i ↦ cap.getD i 0), (5, fun i ↦ [word 1 0 0, word 0 0 0, word 0 0 0, word 0 0 0,
      word 0 0 0].getD i 0),
    (13, cells13F (⟨cap, []⟩ : Fs).perm),
    (7, challengeVals (cells13F (⟨cap, []⟩ : Fs).perm 0) (cells13F (⟨cap, []⟩ : Fs).perm 1)),
    (osPowLen (192 / d), fun i ↦ (powVals X (osPowDigits (192 / d)) 1).getD i 0),
    (2, fun i ↦ [pos * X ^ (192 / d), wp * X ^ (192 / d)].getD i 0),
    (5, fun i ↦ [word 2 0 0, X * word 2 0 0, X * word 2 0 0 + N, word 2 0 0, X * word 2 0 0].getD
      i 0)]

/-- **One iteration of `level_positions`' loop, honestly**, for any relation holding of its
decoder call. -/
theorem lpIter_completeC (d cd : ℕ) (hpw : digitsVal (osPowDigits (192 / d)) 1 = 192 / d)
    (X N sqz pos wp tabs : E) (cap : List E) (hcl : cap.length = 5) (hcan : AllCanonical cap)
    (hrow : ∀ i < 5, LoadHolds rd (sqz * X ^ 5) i (cap.getD i 0))
    (hnext : ∀ i < 5, LoadHolds rd (sqz * X ^ 5) (5 + i) ((capOf (⟨cap, []⟩ : Fs).perm).getD i 0))
    (hdec : C (qwDecName d cd)
      [challengeOf (⟨cap, []⟩ : Fs).perm, pos * X ^ (192 / d), wp * X ^ (192 / d), tabs] []) :
    ∃ σ : Val, (osParams 6).map σ = [X, N, sqz, pos, wp, tabs] ∧
      AllOk C rd σ (lpIterA d cd ++ osLoopTailA (lpIterTail d)) ∧
      σ (.n (lpIterTail d + 2)) = X * gen + N ∧
      (.n (lpIterTail d + 4) :: (List.range (6 - 1)).map fun i ↦ V.n (i + 1)).map σ =
        X * gen :: [N, sqz, pos, wp, tabs] := by
  rcases cap with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, _ | ⟨c5, rest⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hcl <;> try omega
  set segs := lpIterSegs d X N sqz pos wp tabs [c0, c1, c2, c3, c4] with hsegs
  set σ := segVal segs with hσ
  have hv : ∀ i, σ (.n i) = segLookup segs i := segVal_n segs
  have sv : ∀ (m : ℕ) (hm : m < segs.length) (o : ℕ), segLen (segs.take m) = o → ∀ i,
      i < segs[m].1 → σ (.n (o + i)) = segs[m].2 i := fun m hm o ho i hi ↦ by
    have := seg_val (σ := σ) (k := 0) (segs := segs) (fun j _ ↦ by rw [Nat.zero_add]; exact hv j)
      m hm o ho i hi
    rwa [Nat.zero_add] at this
  set L := osPowLen (192 / d) with hL
  have he : lpIterTail d = 40 + L + 2 := rfl
  have g0 : σ (.n 0) = X := by rw [hv]; simp [hsegs, lpIterSegs, segLookup]
  have g1 : σ (.n 1) = N := by rw [hv]; simp [hsegs, lpIterSegs, segLookup]
  have g2 : σ (.n 2) = sqz := by rw [hv]; simp [hsegs, lpIterSegs, segLookup]
  have g3 : σ (.n 3) = pos := by rw [hv]; simp [hsegs, lpIterSegs, segLookup]
  have g4 : σ (.n 4) = wp := by rw [hv]; simp [hsegs, lpIterSegs, segLookup]
  have g5 : σ (.n 5) = tabs := by rw [hv]; simp [hsegs, lpIterSegs, segLookup]
  have tl : ∀ i < 5, σ (.n (lpIterTail d + i)) =
      [word 2 0 0, X * word 2 0 0, X * word 2 0 0 + N, word 2 0 0, X * word 2 0 0].getD i 0 :=
    fun i hi ↦ by
      rw [he]
      exact sv 8 (by simp [hsegs, lpIterSegs]) _ (by simp [hsegs, lpIterSegs, segLen, ← hL]; ring)
        i (by simp [hsegs, lpIterSegs]; omega)
  have t0 := tl 0 (by omega); have t1 := tl 1 (by omega); have t2 := tl 2 (by omega)
  have t3 := tl 3 (by omega); have t4 := tl 4 (by omega)
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at t0 t1 t2 t3 t4
  refine ⟨σ, ?_, ?_, ?_, ?_⟩
  · simp only [osParams, List.range_succ, List.range_zero, List.map_cons,
      List.map_nil, List.nil_append, List.cons_append, g0, g1, g2, g3, g4, g5]
  · have v5 : σ (.n 6) = X * X := by rw [hv]; simp [hsegs, lpIterSegs, segLookup]
    have v6 : σ (.n 7) = X * X * (X * X) := by rw [hv]; simp [hsegs, lpIterSegs, segLookup]
    have v7 : σ (.n 8) = X * X * (X * X) * X := by rw [hv]; simp [hsegs, lpIterSegs, segLookup]
    have v8 : σ (.n 9) = sqz * (X * X * (X * X) * X) := by rw [hv]; simp [hsegs, lpIterSegs, segLookup]
    have vc : ∀ i < 5, σ (.n (10 + i)) = [c0, c1, c2, c3, c4].getD i 0 := fun i hi ↦
      sv 2 (by simp [hsegs, lpIterSegs]) 10 (by simp [hsegs, lpIterSegs, segLen]) i
        (by simp [hsegs, lpIterSegs]; omega)
    have vz : ∀ i < 5, σ (.n (15 + i)) = [word 1 0 0, word 0 0 0, word 0 0 0, word 0 0 0,
        word 0 0 0].getD i 0 := fun i hi ↦
      sv 3 (by simp [hsegs, lpIterSegs]) 15 (by simp [hsegs, lpIterSegs, segLen]) i
        (by simp [hsegs, lpIterSegs]; omega)
    set S := (⟨[c0, c1, c2, c3, c4], []⟩ : Fs).perm with hS
    have vk : ∀ c < 13, σ (.n (20 + c)) = cells13F S c := fun c hc ↦
      sv 4 (by simp [hsegs, lpIterSegs]) 20 (by simp [hsegs, lpIterSegs, segLen]) c
        (by simp [hsegs, lpIterSegs]; omega)
    have vch : ∀ i < 7, σ (.n (33 + i)) = challengeVals (cells13F S 0) (cells13F S 1) i :=
      fun i hi ↦ sv 5 (by simp [hsegs, lpIterSegs]) 33 (by simp [hsegs, lpIterSegs, segLen]) i
        (by simp [hsegs, lpIterSegs]; omega)
    have vpw : ∀ j < (powVals (σ (.n 0)) (osPowDigits (192 / d)) 1).length,
        σ (.n (40 + j)) = (powVals (σ (.n 0)) (osPowDigits (192 / d)) 1).getD j 0 :=
      fun j hj ↦ by
        rw [g0] at hj ⊢
        exact sv 6 (by simp [hsegs, lpIterSegs]) 40 (by simp [hsegs, lpIterSegs, segLen]) j
          (by simp [hsegs, lpIterSegs, osPowLen, powVals_length] at hj ⊢; omega)
    have vq : ∀ i < 2, σ (.n (40 + L + i)) = [pos * X ^ (192 / d), wp * X ^ (192 / d)].getD i 0 :=
      fun i hi ↦ sv 7 (by simp [hsegs, lpIterSegs]) (40 + L) (by simp [hsegs, lpIterSegs, segLen, ← hL]; ring)
        i (by simp [hsegs, lpIterSegs]; omega)
    have vq1 := vq 0 (by omega); have vq2 := vq 1 (by omega)
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at vq1 vq2
    have hcm : [c0, c1, c2, c3, c4] = [10, 11, 12, 13, 14].map fun i ↦ σ (.n i) := by
      have e0 := vc 0 (by omega); have e1 := vc 1 (by omega); have e2 := vc 2 (by omega)
      have e3 := vc 3 (by omega); have e4 := vc 4 (by omega)
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1 e2 e3 e4
      simp only [List.map_cons, List.map_nil]
      rw [e0, e1, e2, e3, e4]
    have hX5 : X * X * (X * X) * X = X ^ 5 := by ring
    have hpwr := osPowSteps_complete (C := C) (rd := rd) (σ := σ) 0
      (osPowDigits (192 / d)) 0 40 1 (by rw [pow_one]) vpw
    rw [hpw, g0] at hpwr
    have k0 : σ (.n 20) = cellsOfState S false 0 := by
      have := vk 0 (by omega); simpa [cells13F] using this
    have k1 : σ (.n 21) = cellsOfState S false 1 := by
      have := vk 1 (by omega); simpa [cells13F] using this
    have hS' : (⟨[10, 11, 12, 13, 14].map fun i ↦ σ (.n i), []⟩ : Fs).perm = S := by rw [← hcm]
    have z1 : σ (.n (15 + 1)) = 0 := by have := vz 1 (by omega); simpa [word_zero] using this
    have z2 : σ (.n (15 + 2)) = 0 := by have := vz 2 (by omega); simpa [word_zero] using this
    have z3 : σ (.n (15 + 3)) = 0 := by have := vz 3 (by omega); simpa [word_zero] using this
    have z4 : σ (.n (15 + 4)) = 0 := by have := vz 4 (by omega); simpa [word_zero] using this
    have hsq := osSqueeze0_complete (C := C) (rd := rd) (σ := σ) (p := 15)
      (cap := [10, 11, 12, 13, 14]) (j := 20) rfl ⟨z1, z2, z3, z4⟩
      (by rw [← hcm]; exact hcan) (fun c hc ↦ by rw [hS']; exact vk c hc)
      (fun i hi ↦ by rw [k0, k1, show 20 + 13 + i = 33 + i by ring, vch i hi, cells13F, cells13F]
                     simp)
    rw [hS'] at hsq
    have h38 : σ (.n 39) = challengeOf S := hsq.2
    simp only [lpIterA, allOk_append]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, hsq.1⟩, ?_⟩, hpwr.1⟩, ?_⟩, ?_⟩, ?_⟩
    · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      exact ⟨by rw [v5, g0], by rw [v6, v5], by rw [v7, v6, g0], by rw [v8, v7, g2]⟩
    · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
        List.cons_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, Nat.add_zero]
      rw [v8, hX5]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · have := vc 0 (by omega); simp at this; rw [this]; exact hrow 0 (by omega)
      · have := vc 1 (by omega); simp at this; rw [this]; exact hrow 1 (by omega)
      · have := vc 2 (by omega); simp at this; rw [this]; exact hrow 2 (by omega)
      · have := vc 3 (by omega); simp at this; rw [this]; exact hrow 3 (by omega)
      · have := vc 4 (by omega); simp at this; rw [this]; exact hrow 4 (by omega)
    · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · have := vz 0 (by omega); simpa using this
      · have := vz 1 (by omega); simpa using this
      · have := vz 2 (by omega); simpa using this
      · have := vz 3 (by omega); simpa using this
      · have := vz 4 (by omega); simpa using this
    · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
        List.cons_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, Nat.add_zero]
      rw [v8, hX5]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · have := vk 8 (by omega); simp [cells13F] at this; rw [this]
        simpa [capOf] using hnext 0 (by omega)
      · have := vk 9 (by omega); simp [cells13F] at this; rw [this]
        simpa [capOf] using hnext 1 (by omega)
      · have := vk 10 (by omega); simp [cells13F] at this; rw [this]
        simpa [capOf] using hnext 2 (by omega)
      · have := vk 11 (by omega); simp [cells13F] at this; rw [this]
        simpa [capOf] using hnext 3 (by omega)
      · have := vk 12 (by omega); simp [cells13F] at this; rw [this]
        simpa [capOf] using hnext 4 (by omega)
    · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      exact ⟨by rw [vq1, g3, hpwr.2], by rw [vq2, g4, hpwr.2]⟩
    · simp only [allOk_cons, allOk_nil, and_true, StmtOk, List.map_cons, List.map_nil]
      rw [h38, vq1, vq2, g5]
      exact hdec
    · simp only [osLoopTailA, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      exact ⟨t0, by rw [t1, g0, t0], by rw [t2, t1, g1], t3, by rw [t4, g0, t3]⟩
  · rw [t2, word_gen]
  · show [σ (.n (lpIterTail d + 4)), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5)] = _
    rw [t4, word_gen, g1, g2, g3, g4, g5]

/-- **`level_positions`' loop, honestly**: on a squeeze run at `sqz` holding the chain of
capacities from `cap`, row `j` at `5j`, each squeeze's challenge decoded at the shifted pointers,
the loop's entry holds. -/
theorem lpLoop_complete {loop : String} {d cd sq : ℕ} (hl : FnIs loop (osParams 6) (lpLoopBody d cd loop))
    (hsq : 0 < sq) (hpw : digitsVal (osPowDigits (192 / d)) 1 = 192 / d)
    {cap : List E} (hcl : cap.length = 5) (hcan : AllCanonical cap) {sqz pos wp tabs : E}
    (hrows : ∀ j ≤ sq, ∀ i < 5, LoadHolds rd sqz (5 * j + i) ((sqCaps cap j).getD i 0))
    (hdec : ∀ j < sq, coreProgram.Rel rd (qwDecName d cd)
      [sqChal cap j, pos * gen ^ (j * (192 / d)), wp * gen ^ (j * (192 / d)), tabs] []) :
    IsInK (1 + gen ^ sq) ∧
      (1 + gen ^ sq ≠ 0 → coreProgram.Rel rd loop (1 :: gen ^ sq :: [sqz, pos, wp, tabs]) []) := by
  obtain ⟨fn, hf, hps, hb⟩ := hl
  have hb' : fn.body = (lpIterA d cd ++ osLoopTailA (lpIterTail d)) ++
      [.callIf (.n (lpIterTail d + 2)) loop (.n (lpIterTail d + 4) :: (List.range (6 - 1)).map fun i ↦ .n (i + 1)),
        .ret []] := by
    rw [hb, lpIterBody_eq, osLoopTail_split, List.append_assoc]
  refine loop_complete hf (lpIterA_flat d cd) hb' hsq rfl fun j hj ↦ ?_
  have hrow : ∀ i < 5, LoadHolds rd (sqz * (gen ^ j) ^ 5) i ((sqCaps cap j).getD i 0) := by
    intro i hi
    rw [← pow_mul, loadHolds_mul_gen_pow, show j * 5 + i = 5 * j + i by ring]
    exact hrows j (by omega) i hi
  have hnext : ∀ i < 5, LoadHolds rd (sqz * (gen ^ j) ^ 5) (5 + i)
      ((capOf (⟨sqCaps cap j, []⟩ : Fs).perm).getD i 0) := by
    intro i hi
    rw [← pow_mul, loadHolds_mul_gen_pow, show j * 5 + (5 + i) = 5 * (j + 1) + i by ring]
    exact hrows (j + 1) (by omega) i hi
  obtain ⟨σ, hp, hA, hc, ha⟩ := lpIter_completeC (C := coreProgram.Rel rd) d cd hpw (gen ^ j) (gen ^ sq)
    sqz pos wp tabs (sqCaps cap j) (sqCaps_length cap hcl j) (sqCaps_canonical cap hcan j) hrow hnext
    (by rw [← pow_mul]; exact hdec j hj)
  exact ⟨σ, by rw [hps]; exact hp, hA, hc, ha⟩

/-- The values of `level_positions` past its arguments. -/
def lpHonVals (sq : ℕ) (sqz : E) (last : List E) : List E :=
  [gw ((sq + 1) * 5), sqz, word 1 0 0, gw sq, word 1 0 0 + gw sq, word 1 0 0, gw sq, gw (sq * 5),
    sqz * gw (sq * 5)] ++ last ++ last

/-- **`level_positions`, honestly**: on a squeeze run at `sqz` holding the chain of capacities
from `cap` (row `j` at `5j`, `j ≤ sq`), each squeeze's challenge decoded at the pointers shifted by
`j·(192/d)`, the specialization relates `cap ++ [pos, wp, tabs]` to the last capacity. -/
theorem lp_complete {name loop : String} {sq d cd : ℕ}
    (hlp : FnIs name (osParams 8) (lpBody sq loop)) (hl : FnIs loop (osParams 6) (lpLoopBody d cd loop))
    (hsq : 0 < sq) (hsq5 : (sq + 1) * 5 < u128Bound)
    (hpw : digitsVal (osPowDigits (192 / d)) 1 = 192 / d)
    {cap : List E} (hcl : cap.length = 5) (hcan : AllCanonical cap) {sqz pos wp tabs : E}
    (hrows : ∀ j ≤ sq, ∀ i < 5, LoadHolds rd sqz (5 * j + i) ((sqCaps cap j).getD i 0))
    (hdec : ∀ j < sq, coreProgram.Rel rd (qwDecName d cd)
      [sqChal cap j, pos * gen ^ (j * (192 / d)), wp * gen ^ (j * (192 / d)), tabs] []) :
    coreProgram.Rel rd name (cap ++ [pos, wp, tabs]) (sqCaps cap sq) := by
  obtain ⟨fn, hf, hps, hb⟩ := hlp
  have hloop := lpLoop_complete hl hsq hpw hcl hcan hrows hdec
  have hsq' : sq < u128Bound := by omega
  have hsq5' : sq * 5 < u128Bound := by omega
  set last := sqCaps cap sq with hlast
  have hll : last.length = 5 := sqCaps_length cap hcl sq
  rcases cap with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, _ | ⟨c5, rest⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hcl <;> try omega
  obtain ⟨l0, l1, l2, l3, l4, hl5⟩ : ∃ l0 l1 l2 l3 l4, last = [l0, l1, l2, l3, l4] := by
    match last, hll with
    | [l0, l1, l2, l3, l4], _ => exact ⟨l0, l1, l2, l3, l4, rfl⟩
  set vals := [c0, c1, c2, c3, c4, pos, wp, tabs] ++ lpHonVals sq sqz last with hvals
  set σ : Val := fun v ↦ if v.path = [] ∧ v.tag = 0 then vals.getD v.idx 0 else 0 with hσ
  have hv : ∀ i, σ (.n i) = vals.getD i 0 := fun i ↦ by simp [hσ]
  rw [rel_iff_sem hf]
  refine ⟨σ, ?_, ?_⟩
  · rw [hps]
    simp [osParams, List.range_succ, hv, hvals]
  · rw [hb, lpBody, holdsList_flat_ret _ (by simp [osHeap, osLoopCall, Stmt.flat])]
    refine ⟨?_, ?_⟩
    · simp only [osHeap, osLoopCall, allOk_cons, allOk_nil, and_true, StmtOk,
        Atom.Holds, List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
        List.cons_append, hv]
      simp only [hvals, lpHonVals, hl5, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some, List.cons_append, List.nil_append, true_and,
        and_true]
      have h0 : ∀ i < 5, LoadHolds rd sqz i ([c0, c1, c2, c3, c4].getD i 0) := fun i hi ↦ by
        have := hrows 0 (by omega) i hi
        simpa [sqCaps] using this
      have hs : ∀ i < 5, LoadHolds rd (sqz * gw (sq * 5)) i ([l0, l1, l2, l3, l4].getD i 0) :=
        fun i hi ↦ by
          have := hrows sq le_rfl i hi
          rw [← hlast, hl5] at this
          rw [gw_eq hsq5', loadHolds_mul_gen_pow, show sq * 5 + i = 5 * sq + i by ring]
          exact this
      rw [word_one, gw_eq hsq']
      exact ⟨h0 0 (by omega), h0 1 (by omega), h0 2 (by omega), h0 3 (by omega), h0 4 (by omega),
        hloop, hs 0 (by omega), hs 1 (by omega), hs 2 (by omega), hs 3 (by omega), hs 4 (by omega)⟩
    · simp [hv, hvals, lpHonVals, hl5, List.range_succ]

end
end LeanVM.Guest.B1.Whir
