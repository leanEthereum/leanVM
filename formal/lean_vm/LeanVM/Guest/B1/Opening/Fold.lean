/-
  LeanVM.Guest.B1.Opening.Fold

  B1 for `opening_fold`: one WHIR fold round.
-/

module

public import LeanVM.Guest.B1.Opening.Meaning
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Common.Run

/-!
# `opening_fold` (G:1216-1229 at 40f877dc, TRIAGE #35)

Its body: the capacity copied into `11 .. 15`, the two waiting scalars packed (`fsPackT`, cells
`22, 24` and `31, 33`), the pad run `34 .. 38`, the permutation into `39 .. 51`, the challenge
(`challengeT` from `52`, at `58`), the fold (`59 .. 62`), the two stream words read and packed
(raw loads into `63`, `64`), the returns.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem find_opening_fold : coreProgram.find? "opening_fold" = some Data.core8 :=
  Program.find?_of_indexOf? (j := 8) (by decide +kernel) rfl

theorem core8_params : Fn.params Data.core8 =
    [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10] := rfl

theorem core8_body : Fn.body Data.core8 =
    [.atom (.copy (.n 11) (.n 0)), .atom (.copy (.n 12) (.n 1)), .atom (.copy (.n 13) (.n 2)),
      .atom (.copy (.n 14) (.n 3)), .atom (.copy (.n 15) (.n 4))] ++
    fsPackT (.n 5) 16 dsObserve ++ fsPackT (.n 6) 25 dsObserve ++
    [.atom (.const (.n 34) (word 1 0 0)), .atom (.const (.n 35) (word 0 0 0)),
      .atom (.const (.n 36) (word 0 0 0)), .atom (.const (.n 37) (word 0 0 0)),
      .atom (.const (.n 38) (word 0 0 0)),
      keccakA [.n 22, .n 24, .n 31, .n 33, .n 35, .n 36, .n 37, .n 38, .n 11, .n 12, .n 13, .n 14,
        .n 15]
        [.n 39, .n 40, .n 41, .n 42, .n 43, .n 44, .n 45, .n 46, .n 47, .n 48, .n 49, .n 50, .n 51]] ++
    challengeT (.n 39) (.n 40) 52 ++
    [.atom (.mul (.n 59) (.n 10) (.n 58)), .atom (.add (.n 60) (.n 59) (.n 9)),
      .atom (.mul (.n 61) (.n 60) (.n 58)), .atom (.add (.n 62) (.n 61) (.n 8))] ++
    [.atom (.load (.n 63) (.n 7) 0), .atom (.load (.n 64) (.n 7) 1),
      .atom (.copy (.n 65) (.n 47)), .atom (.copy (.n 66) (.n 48)), .atom (.copy (.n 67) (.n 49)),
      .atom (.copy (.n 68) (.n 50)), .atom (.copy (.n 69) (.n 51)),
      .atom (.const (.n 70) (word 4 0 0)), .atom (.mul (.n 71) (.n 7) (.n 70)),
      .atom (.copy (.n 72) (.n 62)), .atom (.copy (.n 73) (.n 63)), .atom (.copy (.n 74) (.n 64)),
      .atom (.copy (.n 75) (.n 58)),
      .ret [.n 65, .n 66, .n 67, .n 68, .n 69, .n 71, .n 72, .n 73, .n 74, .n 75]] := rfl

theorem word_four : word 4 0 0 = gen ^ 2 := word_two_pow (a := 2) (by decide)

/-- The two waiting scalars of a fold round, on the carried capacity. -/
theorem fold_sponge (cap : List E) (w0 w1 : E) :
    (⟨cap, [(w0, dsObserve), (w1, dsObserve)]⟩ : Fs).perm =
      permOf (pendCells [(w0, dsObserve), (w1, dsObserve)] ++ [0, 0, 0, 0] ++ cap) := by
  rw [perm_eq_cells _ (by simp)]
  rfl

/-- The honest values of `opening_fold`, by index. -/
def foldVals (as : List E) (d0 d2 : E) (S : KeccakState) (k : ℕ) : E :=
  let y := challengeOf S
  if k < 11 then as.getD k 0
  else if k < 16 then as.getD (k - 11) 0
  else if k < 25 then fsPackVals (as.getD 5 0) dsObserve (k - 16)
  else if k < 34 then fsPackVals (as.getD 6 0) dsObserve (k - 25)
  else if k = 34 then 1
  else if k < 39 then 0
  else if k < 52 then cellsOfState S false ⟨(k - 39) % 13, Nat.mod_lt _ (by omega)⟩
  else if k < 59 then challengeVals (cellsOfState S false 0) (cellsOfState S false 1) (k - 52)
  else if k < 63 then [as.getD 10 0 * y, as.getD 10 0 * y + as.getD 9 0,
    (as.getD 10 0 * y + as.getD 9 0) * y, (as.getD 10 0 * y + as.getD 9 0) * y + as.getD 8 0].getD
      (k - 59) 0
  else if k = 63 then d0
  else if k = 64 then d2
  else if k < 70 then cellsOfState S false ⟨(k - 57) % 13, Nat.mod_lt _ (by omega)⟩
  else [word 4 0 0, as.getD 7 0 * word 4 0 0,
    (as.getD 10 0 * y + as.getD 9 0) * y + as.getD 8 0, d0, d2, y].getD (k - 70) 0

/-- **`opening_fold`'s core IR is its meaning.** -/
theorem opening_fold_holds : opening_fold_Spec := by
  intro rd args rets
  rw [rel_iff_sem find_opening_fold, core8_body, core8_params]
  simp only [holdsList_append, holds_fsPackT, holds_challengeT, keccakA,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  constructor
  · rintro ⟨σ, hp, h11, h12, h13, h14, h15, hp0, hp1, h34, h35, h36, h37, h38, hKH, hch,
      h59, h60, h61, h62, hl0, hl1, h83, h84, h85, h86, h87, h88, h89, h91, h92,
      h93, h94, hret⟩
    subst hp
    have hKA : (Atom.keccak [.n 22, .n 24, .n 31, .n 33, .n 35, .n 36, .n 37, .n 38, .n 11, .n 12,
        .n 13, .n 14, .n 15] [.n 39, .n 40, .n 41, .n 42, .n 43, .n 44, .n 45, .n 46, .n 47, .n 48,
        .n 49, .n 50, .n 51] false false).Holds rd σ := hKH
    obtain ⟨-, -, hcan, hout⟩ := keccakA_perm hKA
    have c22 : (σ (.n 22), σ (.n 24)) = Keccak.scalarCells (σ (.n 5)) dsObserve :=
      fsPackT_cells hp0 (hcan (σ (.n 22)) (by simp))
    have c31 : (σ (.n 31), σ (.n 33)) = Keccak.scalarCells (σ (.n 6)) dsObserve :=
      fsPackT_cells hp1 (hcan (σ (.n 31)) (by simp))
    have hS : permOf ([.n 22, .n 24, .n 31, .n 33, .n 35, .n 36, .n 37, .n 38, .n 11, .n 12,
        .n 13, .n 14, .n 15].map σ) = (⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)],
          [(σ (.n 5), dsObserve), (σ (.n 6), dsObserve)]⟩ : Fs).perm := by
      rw [fold_sponge]
      congr 1
      simp only [pendCells, List.flatMap_cons, List.flatMap_nil, ← c22, ← c31, h35, h36, h37, h38,
        h11, h12, h13, h14, h15, word_zero, List.map_cons, List.map_nil]
      rfl
    rw [hS] at hout
    have o0 : σ (.n 39) = cellsOfState _ false 0 := outs_eq hout 0 (by simp)
    have o1 : σ (.n 40) = cellsOfState _ false 1 := outs_eq hout 1 (by simp)
    have o8 : σ (.n 47) = cellsOfState _ false 8 := outs_eq hout 8 (by simp)
    have o9 : σ (.n 48) = cellsOfState _ false 9 := outs_eq hout 9 (by simp)
    have o10 : σ (.n 49) = cellsOfState _ false 10 := outs_eq hout 10 (by simp)
    have o11 : σ (.n 50) = cellsOfState _ false 11 := outs_eq hout 11 (by simp)
    have o12 : σ (.n 51) = cellsOfState _ false 12 := outs_eq hout 12 (by simp)
    have hy := challengeT_value hch o0 o1
    refine ⟨?_, σ (.n 63), σ (.n 64), ?_, ?_⟩
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · rw [← h11]; exact hcan _ (by simp)
      · rw [← h12]; exact hcan _ (by simp)
      · rw [← h13]; exact hcan _ (by simp)
      · rw [← h14]; exact hcan _ (by simp)
      · rw [← h15]; exact hcan _ (by simp)
    · intro k hk
      simp only [List.length_cons, List.length_nil] at hk
      interval_cases k
      · exact hl0
      · exact hl1
    · rw [← hret, h83, h84, h85, h86, h87, h89, h88, word_four, h91, h62, h61, h60, h59, h92,
        h93, h94, hy, o8, o9, o10, o11, o12]
      rfl
  · intro hm
    obtain ⟨f0, f1, f2, f3, f4, w0, w1, cur, c0, c1, c2, rfl⟩ :
        ∃ f0 f1 f2 f3 f4 w0 w1 cur c0 c1 c2,
          args = [f0, f1, f2, f3, f4, w0, w1, cur, c0, c1, c2] := by
      match args, hm with
      | [f0, f1, f2, f3, f4, w0, w1, cur, c0, c1, c2], _ =>
        exact ⟨f0, f1, f2, f3, f4, w0, w1, cur, c0, c1, c2, rfl⟩
    obtain ⟨hcan, d0, d2, hrd, hret⟩ := hm
    obtain ⟨S, hSdef⟩ : ∃ S, S =
        (⟨[f0, f1, f2, f3, f4], [(w0, dsObserve), (w1, dsObserve)]⟩ : Fs).perm := ⟨_, rfl⟩
    simp only [Fs.squeeze] at hret
    simp only [← hSdef] at hret
    let as := [f0, f1, f2, f3, f4, w0, w1, cur, c0, c1, c2]
    let σ : Val := fun v => foldVals as d0 d2 S v.idx
    have ev : ∀ k, σ (.n k) = foldVals as d0 d2 S k := fun _ => rfl
    have hS : permOf ([.n 22, .n 24, .n 31, .n 33, .n 35, .n 36, .n 37, .n 38, .n 11, .n 12,
        .n 13, .n 14, .n 15].map σ) = S := by
      rw [hSdef, fold_sponge]
      have p0 := fsPackVals_cells w0 dsObserve
      have p1 := fsPackVals_cells w1 dsObserve
      simp only [pendCells, List.flatMap_cons, List.flatMap_nil, ← p0, ← p1]
      simp [ev, foldVals, as]
    have hy : challengeVals (cellsOfState S false 0) (cellsOfState S false 1) 6 = challengeOf S :=
      challengeVals_six S
    refine ⟨σ, by simp [ev, foldVals, as], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      keccak13_mk (rd := rd) rfl rfl ?_ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    all_goals try (simp [ev, foldVals, as, word_zero, word_one, hy]; done)
    · exact fsPackOk_of_vals fun i hi => by interval_cases i <;> simp [ev, foldVals, as]
    · exact fsPackOk_of_vals fun i hi => by interval_cases i <;> simp [ev, foldVals, as]
    · intro c
      have p0 := fsPackVals_canonical w0 dsObserve
      have p1 := fsPackVals_canonical w1 dsObserve
      have z : IsCanonical128 (0 : E) := by
        rw [zero_eq_ofLimbs]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl
      fin_cases c <;> simp [cells13, ev, foldVals, as, p0.1, p0.2, p1.1, p1.2, z] <;>
        exact hcan _ (by simp)
    · intro c
      simp only [List.map_cons, List.map_nil]
      have hS' : keccakF1600 (stateOfCells (cells13 [σ (.n 22), σ (.n 24), σ (.n 31), σ (.n 33),
          σ (.n 35), σ (.n 36), σ (.n 37), σ (.n 38), σ (.n 11), σ (.n 12), σ (.n 13), σ (.n 14),
          σ (.n 15)]) false) = S := hS
      rw [hS']
      fin_cases c <;> simp [cells13, ev, foldVals]
    · exact challengeOk_of_vals (by simp [ev, foldVals, cellsOfState_canonical])
        fun i hi => by interval_cases i <;> simp [ev, foldVals]
    · simpa [ev, foldVals, as] using hrd 0 (by simp)
    · simpa [ev, foldVals, as] using hrd 1 (by simp)
    · rw [hret, ← word_four]
      simp [ev, foldVals, as, capOf]

end
end LeanVM.Guest.B1
