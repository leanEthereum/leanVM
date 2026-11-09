/-
  LeanVM.Guest.B1.Sumcheck.Round4

  B1 for `sumcheck_round4`: one plain sumcheck round from a round record.
-/

module

public import LeanVM.Guest.B1.Sumcheck.Meaning
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Common.Run

/-!
# `sumcheck_round4` (G:1102-1118, TRIAGE #30)

Its body: the record's capacity loaded into `3 .. 7`, three `fs_next` (`fsNextT`, cells `15, 17`,
`25, 27`, `35, 37`), the zero run `38, 39`, the permutation into `40 .. 52`, the challenge
(`challengeT` from `53`, the challenge at `59`), the capacity stored into the next record, the
fold.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem find_sumcheck_round4 : coreProgram.find? "sumcheck_round4" = some Data.core7 :=
  Program.find?_of_indexOf? (j := 7) (by decide +kernel) rfl

theorem core7_params : Fn.params Data.core7 = [.n 0, .n 1, .n 2] := rfl

theorem core7_body : Fn.body Data.core7 =
    [.atom (.load (.n 3) (.n 0) 0), .atom (.load (.n 4) (.n 0) 1), .atom (.load (.n 5) (.n 0) 2),
      .atom (.load (.n 6) (.n 0) 3), .atom (.load (.n 7) (.n 0) 4)] ++
    fsNextT (.n 1) 0 8 ++ fsNextT (.n 1) 1 18 ++ fsNextT (.n 1) 2 28 ++
    [.atom (.const (.n 38) (word 0 0 0)), .atom (.const (.n 39) (word 0 0 0)),
      keccakA [.n 15, .n 17, .n 25, .n 27, .n 35, .n 37, .n 38, .n 39, .n 3, .n 4, .n 5, .n 6, .n 7]
        [.n 40, .n 41, .n 42, .n 43, .n 44, .n 45, .n 46, .n 47, .n 48, .n 49, .n 50, .n 51, .n 52]] ++
    challengeT (.n 40) (.n 41) 53 ++
    [.atom (.load (.n 48) (.n 0) 7), .atom (.load (.n 49) (.n 0) 8), .atom (.load (.n 50) (.n 0) 9),
      .atom (.load (.n 51) (.n 0) 10), .atom (.load (.n 52) (.n 0) 11),
      .atom (.const (.n 60) (word 1 0 0)), .atom (.add (.n 61) (.n 60) (.n 59)),
      .atom (.const (.n 62) (word 8 0 0)), .atom (.mul (.n 63) (.n 1) (.n 62)),
      .atom (.copy (.n 64) (.n 63)), .atom (.mul (.n 65) (.n 61) (.n 28)),
      .atom (.add (.n 66) (.n 18) (.n 65)), .atom (.mul (.n 67) (.n 61) (.n 66)),
      .atom (.add (.n 68) (.n 2) (.n 67)), .atom (.mul (.n 69) (.n 59) (.n 68)),
      .atom (.add (.n 70) (.n 8) (.n 69)), .atom (.copy (.n 71) (.n 59)),
      .ret [.n 64, .n 70, .n 71]] := rfl

theorem word_eight : word 8 0 0 = gen ^ 3 := word_two_pow (a := 3) (by decide)

/-- The round's polynomial at `y`, in the guest's Horner form. -/
theorem round4_eval (c0 c2 c3 claim y : E) :
    c0 + y * (claim + (1 + y) * (c2 + (1 + y) * c3)) =
      polyEval [c0, claim + sumE [c2, c3], c2, c3] y := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  simp only [polyEval, List.foldr, sumE, List.foldl, zero_add, zero_mul]
  linear_combination (y ^ 2 * c3) * h2

/-- The sponge of the round: three scalars waiting on the record's capacity. -/
theorem round4_sponge (cap : List E) (c0 c2 c3 : E) :
    (⟨cap, []⟩ : Fs).absorbAll [c0, c2, c3] dsObserve =
      ⟨cap, [(c0, dsObserve), (c2, dsObserve), (c3, dsObserve)]⟩ := by
  rw [absorbAll_short _ _ _ (by simp)]
  rfl

/-- The honest values of `sumcheck_round4`, by index. -/
def r4Vals (rec cur claim : E) (cap : List E) (c0 c2 c3 : E) (S : KeccakState) (k : ℕ) : E :=
  let y := challengeOf S
  if k < 3 then [rec, cur, claim].getD k 0
  else if k < 8 then cap.getD (k - 3) 0
  else if k = 8 then c0 else if k < 18 then fsPackVals c0 dsObserve (k - 9)
  else if k = 18 then c2 else if k < 28 then fsPackVals c2 dsObserve (k - 19)
  else if k = 28 then c3 else if k < 38 then fsPackVals c3 dsObserve (k - 29)
  else if k < 40 then 0
  else if k < 53 then cellsOfState S false ⟨(k - 40) % 13, Nat.mod_lt _ (by omega)⟩
  else if k < 60 then challengeVals (cellsOfState S false 0) (cellsOfState S false 1) (k - 53)
  else [1, 1 + y, word 8 0 0, cur * word 8 0 0, cur * word 8 0 0, (1 + y) * c3,
    c2 + (1 + y) * c3, (1 + y) * (c2 + (1 + y) * c3), claim + (1 + y) * (c2 + (1 + y) * c3),
    y * (claim + (1 + y) * (c2 + (1 + y) * c3)),
    c0 + y * (claim + (1 + y) * (c2 + (1 + y) * c3)), y].getD (k - 60) 0

/-- **`sumcheck_round4`'s core IR is its meaning.** -/
theorem sumcheck_round4_holds : sumcheck_round4_Spec := by
  intro rd args rets
  rw [rel_iff_sem find_sumcheck_round4, core7_body, core7_params]
  simp only [holdsList_append, holds_fsNextT, holds_challengeT, keccakA, Stmt.HoldsList,
    Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  constructor
  · rintro ⟨σ, hp, l3, l4, l5, l6, l7, ⟨hl0, hp0⟩, ⟨hl1, hp1⟩, ⟨hl2, hp2⟩, h38, h39,
      hKH, hch, l48, l49, l50, l51, l52, h60, h61, h62, h63, h64, h65, h66, h67, h68, h69,
      h70, h71, hret⟩
    subst hp
    have hKA : (Atom.keccak [.n 15, .n 17, .n 25, .n 27, .n 35, .n 37, .n 38, .n 39, .n 3, .n 4,
        .n 5, .n 6, .n 7] [.n 40, .n 41, .n 42, .n 43, .n 44, .n 45, .n 46, .n 47, .n 48, .n 49,
        .n 50, .n 51, .n 52] false false).Holds rd σ := hKH
    obtain ⟨-, -, hcan, hout⟩ := keccakA_perm hKA
    have c15 : (σ (.n 15), σ (.n 17)) = Keccak.scalarCells (σ (.n 8)) dsObserve :=
      fsPackT_cells hp0 (hcan (σ (.n 15)) (by simp))
    have c25 : (σ (.n 25), σ (.n 27)) = Keccak.scalarCells (σ (.n 18)) dsObserve :=
      fsPackT_cells hp1 (hcan (σ (.n 25)) (by simp))
    have c35 : (σ (.n 35), σ (.n 37)) = Keccak.scalarCells (σ (.n 28)) dsObserve :=
      fsPackT_cells hp2 (hcan (σ (.n 35)) (by simp))
    have hS : permOf ([.n 15, .n 17, .n 25, .n 27, .n 35, .n 37, .n 38, .n 39, .n 3, .n 4, .n 5,
        .n 6, .n 7].map σ) = (⟨[σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7)],
          [(σ (.n 8), dsObserve), (σ (.n 18), dsObserve), (σ (.n 28), dsObserve)]⟩ : Fs).perm := by
      rw [perm_eq_cells _ (by simp)]
      congr 1
      simp only [pendCells, List.flatMap_cons, List.flatMap_nil, ← c15, ← c25, ← c35, h38, h39,
        word_zero, List.map_cons, List.map_nil]
      rfl
    rw [hS] at hout
    have o0 : σ (.n 40) = cellsOfState _ false 0 := outs_eq hout 0 (by simp)
    have o1 : σ (.n 41) = cellsOfState _ false 1 := outs_eq hout 1 (by simp)
    have o8 : σ (.n 48) = cellsOfState _ false 8 := outs_eq hout 8 (by simp)
    have o9 : σ (.n 49) = cellsOfState _ false 9 := outs_eq hout 9 (by simp)
    have o10 : σ (.n 50) = cellsOfState _ false 10 := outs_eq hout 10 (by simp)
    have o11 : σ (.n 51) = cellsOfState _ false 11 := outs_eq hout 11 (by simp)
    have o12 : σ (.n 52) = cellsOfState _ false 12 := outs_eq hout 12 (by simp)
    have hy := challengeT_value hch o0 o1
    refine ⟨[σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7)], σ (.n 8), σ (.n 18), σ (.n 28),
      ⟨rfl, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro j hj
      simp only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · exact l3
      · exact l4
      · exact l5
      · exact l6
      · exact l7
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> exact hcan _ (by simp)
    · intro k hk
      simp only [List.length_cons, List.length_nil] at hk
      interval_cases k
      · exact hl0
      · exact hl1
      · exact hl2
    · rw [round4_sponge]
      refine ⟨rfl, fun j hj => ?_⟩
      simp only [Fs.squeeze, capOf, List.length_cons, List.length_nil] at hj
      rw [loadHolds_mul_gen_pow]
      interval_cases j
      · show LoadHolds rd (σ (.n 0)) 7 (cellsOfState _ false 8)
        rw [← o8]; exact l48
      · show LoadHolds rd (σ (.n 0)) 8 (cellsOfState _ false 9)
        rw [← o9]; exact l49
      · show LoadHolds rd (σ (.n 0)) 9 (cellsOfState _ false 10)
        rw [← o10]; exact l50
      · show LoadHolds rd (σ (.n 0)) 10 (cellsOfState _ false 11)
        rw [← o11]; exact l51
      · show LoadHolds rd (σ (.n 0)) 11 (cellsOfState _ false 12)
        rw [← o12]; exact l52
    · rw [round4_sponge, ← hret, h64, h63, h62, word_eight, h70, h69, h68, h67, h66, h65, h61, h60,
        h71, word_one, ← round4_eval, hy]
      rfl
  · intro hm
    obtain ⟨rec, cur, claim, rfl⟩ : ∃ rec cur claim, args = [rec, cur, claim] := by
      match args, hm with
      | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
    obtain ⟨cap, c0, c2, c3, ⟨hcl, hcap⟩, hcan, hrd, ⟨-, hst⟩, hret⟩ := hm
    rcases cap with _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, cap⟩⟩⟩⟩⟩⟩ <;>
      simp only [List.length_cons, List.length_nil] at hcl <;> try omega
    rw [round4_sponge] at hst hret
    obtain ⟨S, hSdef⟩ : ∃ S, S =
        (⟨[a3, a4, a5, a6, a7], [(c0, dsObserve), (c2, dsObserve), (c3, dsObserve)]⟩ : Fs).perm :=
      ⟨_, rfl⟩
    simp only [Fs.squeeze] at hst hret
    simp only [← hSdef] at hst hret
    let σ : Val := fun v => r4Vals rec cur claim [a3, a4, a5, a6, a7] c0 c2 c3 S v.idx
    have ev : ∀ k, σ (.n k) = r4Vals rec cur claim [a3, a4, a5, a6, a7] c0 c2 c3 S k :=
      fun _ => rfl
    have hS : permOf ([.n 15, .n 17, .n 25, .n 27, .n 35, .n 37, .n 38, .n 39, .n 3, .n 4, .n 5,
        .n 6, .n 7].map σ) = S := by
      rw [hSdef, perm_eq_cells _ (by simp)]
      have p0 := fsPackVals_cells c0 dsObserve
      have p2 := fsPackVals_cells c2 dsObserve
      have p3 := fsPackVals_cells c3 dsObserve
      simp only [pendCells, List.flatMap_cons, List.flatMap_nil, ← p0, ← p2, ← p3]
      simp [ev, r4Vals]
    have ld : ∀ j (hj : j < 5), LoadHolds rd rec j ([a3, a4, a5, a6, a7] : List E)[j] :=
      fun j hj => by simpa using hcap j hj
    have st : ∀ j (hj : j < 5), LoadHolds rd rec (7 + j) (capOf S)[j] := fun j hj => by
      have := hst j (by simpa [Fs.squeeze, capOf] using hj)
      rwa [loadHolds_mul_gen_pow, Nat.zero_add, Nat.mul_one] at this
    have hy : challengeVals (cellsOfState S false 0) (cellsOfState S false 1) 6 = challengeOf S :=
      challengeVals_six S
    refine ⟨σ, by simp [ev, r4Vals], ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_,
      keccak13_mk (rd := rd) rfl rfl ?_ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ld 0 (by omega)
    · exact ld 1 (by omega)
    · exact ld 2 (by omega)
    · exact ld 3 (by omega)
    · exact ld 4 (by omega)
    · simpa [ev, r4Vals] using hrd 0 (by simp)
    · exact fsPackOk_of_vals fun i hi => by interval_cases i <;> simp [ev, r4Vals]
    · simpa [ev, r4Vals] using hrd 1 (by simp)
    · exact fsPackOk_of_vals fun i hi => by interval_cases i <;> simp [ev, r4Vals]
    · simpa [ev, r4Vals] using hrd 2 (by simp)
    · exact fsPackOk_of_vals fun i hi => by interval_cases i <;> simp [ev, r4Vals]
    · simp [ev, r4Vals, word_zero]
    · simp [ev, r4Vals, word_zero]
    · intro c
      have p0 := fsPackVals_canonical c0 dsObserve
      have p2 := fsPackVals_canonical c2 dsObserve
      have p3 := fsPackVals_canonical c3 dsObserve
      have z : IsCanonical128 (0 : E) := by rw [zero_eq_ofLimbs]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl
      fin_cases c <;> simp [cells13, ev, r4Vals, p0.1, p0.2, p2.1, p2.2, p3.1, p3.2, z] <;>
        exact hcan _ (by simp)
    · intro c
      simp only [List.map_cons, List.map_nil]
      have hS' : keccakF1600 (stateOfCells (cells13 [σ (.n 15), σ (.n 17), σ (.n 25), σ (.n 27),
          σ (.n 35), σ (.n 37), σ (.n 38), σ (.n 39), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6),
          σ (.n 7)]) false) = S := hS
      rw [hS']
      fin_cases c <;> simp [cells13, ev, r4Vals]
    · exact challengeOk_of_vals (by simp [ev, r4Vals, cellsOfState_canonical])
        fun i hi => by interval_cases i <;> simp [ev, r4Vals]
    · simpa [ev, r4Vals, capOf] using st 0 (by omega)
    · simpa [ev, r4Vals, capOf] using st 1 (by omega)
    · simpa [ev, r4Vals, capOf] using st 2 (by omega)
    · simpa [ev, r4Vals, capOf] using st 3 (by omega)
    · simpa [ev, r4Vals, capOf] using st 4 (by omega)
    all_goals try (simp [ev, r4Vals, word_one, hy]; done)
    rw [hret, ← word_eight, ← round4_eval]
    simp [ev, r4Vals]

end
end LeanVM.Guest.B1
