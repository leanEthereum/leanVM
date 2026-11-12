/-
  LeanVM.Guest.B1.Sumcheck.Round4

  B1 for `sumcheck_round4`: one plain sumcheck round from a round record.
-/

module

public import LeanVM.Guest.B1.Sumcheck.Meaning
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Common.Run
public import LeanVM.Guest.B1.Common.Find

/-!
# `sumcheck_round4` (TRIAGE #30)

Its body: the record's capacity loaded into `4 .. 8`, three `fs_next` (`fsNextT`, cells `10, 11`,
`13, 14`, `16, 17`), the zero cells `18, 19` (`zero2T`), the permutation into `20 .. 32`
(`fs_grind_squeeze` at zero bits, `fs_perm(sp, rate, 3)`), the challenge (`challengeT`, at `33`),
the capacity stored into the next record, the fold. The window table `.n 3` is not read.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem find_sumcheck_round4 : coreProgram.find? "sumcheck_round4" = some Data.core6 :=
  coreProgram_find?_at (j := 6) rfl

theorem core6_params : Fn.params Data.core6 = [.n 0, .n 1, .n 2, .n 3] := rfl

theorem core6_body : Fn.body Data.core6 =
    [.atom (.load (.n 4) (.n 0) 0), .atom (.load (.n 5) (.n 0) 1), .atom (.load (.n 6) (.n 0) 2),
      .atom (.load (.n 7) (.n 0) 3), .atom (.load (.n 8) (.n 0) 4)] ++
    fsNextT (.n 1) 0 9 ++ fsNextT (.n 1) 1 12 ++ fsNextT (.n 1) 2 15 ++ zero2T 18 ++
    [keccakA [.n 10, .n 11, .n 13, .n 14, .n 16, .n 17, .n 18, .n 19, .n 4, .n 5, .n 6, .n 7, .n 8]
        [.n 20, .n 21, .n 22, .n 23, .n 24, .n 25, .n 26, .n 27, .n 28, .n 29, .n 30, .n 31, .n 32]] ++
    challengeT (.n 20) 33 ++
    [.atom (.load (.n 28) (.n 0) 7), .atom (.load (.n 29) (.n 0) 8), .atom (.load (.n 30) (.n 0) 9),
      .atom (.load (.n 31) (.n 0) 10), .atom (.load (.n 32) (.n 0) 11),
      .atom (.const (.n 34) (word 1 0)), .atom (.add (.n 35) (.n 34) (.n 33)),
      .atom (.const (.n 36) (word 8 0)), .atom (.mul (.n 37) (.n 1) (.n 36)),
      .atom (.copy (.n 38) (.n 37)), .atom (.mul (.n 39) (.n 35) (.n 15)),
      .atom (.add (.n 40) (.n 12) (.n 39)), .atom (.mul (.n 41) (.n 35) (.n 40)),
      .atom (.add (.n 42) (.n 2) (.n 41)), .atom (.mul (.n 43) (.n 33) (.n 42)),
      .atom (.add (.n 44) (.n 9) (.n 43)), .atom (.copy (.n 45) (.n 33)),
      .ret [.n 38, .n 44, .n 45]] := stmtsEqb_sound (by decide +kernel)

theorem word_eight : word 8 0 = gen ^ 3 := word_two_pow (a := 3) (by decide)

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

/-- The rate cells the permutation reads, as the waiting scalars' cells and zeros. -/
theorem round4_ins (cap : List E) (c0 c2 c3 : E) :
    [c0, word 0 dsObserve, c2, word 0 dsObserve, c3, word 0 dsObserve, 0, 0] ++ cap =
      pendCells [(c0, dsObserve), (c2, dsObserve), (c3, dsObserve)] ++
        List.replicate (8 - 2 * [(c0, dsObserve), (c2, dsObserve), (c3, dsObserve)].length) 0 ++
          cap := by
  simp only [pendCells, List.flatMap_cons, List.flatMap_nil, Keccak.scalarCells, word]
  rfl

/-- The honest values of `sumcheck_round4`, by index. -/
def r4Vals (rec cur claim tabs : E) (cap : List E) (c0 c2 c3 : E) (S : KeccakState) (k : ℕ) : E :=
  let y := challengeOf S
  if k < 4 then [rec, cur, claim, tabs].getD k 0
  else if k < 9 then cap.getD (k - 4) 0
  else if k < 18 then [c0, c0, word 0 dsObserve, c2, c2, word 0 dsObserve, c3, c3,
    word 0 dsObserve].getD (k - 9) 0
  else if k < 20 then 0
  else if k < 33 then cellsOfState S false ⟨(k - 20) % 13, Nat.mod_lt _ (by omega)⟩
  else [y, word 1 0, 1 + y, word 8 0, cur * word 8 0, cur * word 8 0, (1 + y) * c3,
    c2 + (1 + y) * c3, (1 + y) * (c2 + (1 + y) * c3), claim + (1 + y) * (c2 + (1 + y) * c3),
    y * (claim + (1 + y) * (c2 + (1 + y) * c3)),
    c0 + y * (claim + (1 + y) * (c2 + (1 + y) * c3)), y].getD (k - 33) 0

/-- **`sumcheck_round4`'s core IR is its meaning.** -/
theorem sumcheck_round4_holds : sumcheck_round4_Spec := by
  intro rd args rets
  rw [rel_iff_sem find_sumcheck_round4, core6_body, core6_params]
  simp only [holdsList_append, holds_fsNextT, holds_zero2T, holds_challengeT, keccakA,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  constructor
  · rintro ⟨σ, hp, l4, l5, l6, l7, l8, ⟨hl0, hp0⟩, ⟨hl1, hp1⟩, ⟨hl2, hp2⟩, ⟨h18, h19⟩,
      hKH, hch, l28, l29, l30, l31, l32, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43,
      h44, h45, hret⟩
    subst hp
    have hKA : (Atom.keccak [.n 10, .n 11, .n 13, .n 14, .n 16, .n 17, .n 18, .n 19, .n 4, .n 5,
        .n 6, .n 7, .n 8] [.n 20, .n 21, .n 22, .n 23, .n 24, .n 25, .n 26, .n 27, .n 28, .n 29,
        .n 30, .n 31, .n 32] false false).Holds rd σ := hKH
    have hout := keccakA_fs (s := ⟨[σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7), σ (.n 8)],
      [(σ (.n 9), dsObserve), (σ (.n 12), dsObserve), (σ (.n 15), dsObserve)]⟩) hKA
      (by simp) (by
        have e10 : σ (.n 10) = σ (.n 9) := hp0.1
        have e11 : σ (.n 11) = word 0 dsObserve := hp0.2
        have e13 : σ (.n 13) = σ (.n 12) := hp1.1
        have e14 : σ (.n 14) = word 0 dsObserve := hp1.2
        have e16 : σ (.n 16) = σ (.n 15) := hp2.1
        have e17 : σ (.n 17) = word 0 dsObserve := hp2.2
        have e19 : σ (.n 19) = 0 := h19
        dsimp only
        rw [← round4_ins]
        simp only [List.map_cons, List.map_nil, e10, e11, e13, e14, e16, e17, h18, e19]
        rfl)
    have o0 : σ (.n 20) = cellsOfState _ false 0 := outs_eq hout 0 (by simp)
    have o8 : σ (.n 28) = cellsOfState _ false 8 := outs_eq hout 8 (by simp)
    have o9 : σ (.n 29) = cellsOfState _ false 9 := outs_eq hout 9 (by simp)
    have o10 : σ (.n 30) = cellsOfState _ false 10 := outs_eq hout 10 (by simp)
    have o11 : σ (.n 31) = cellsOfState _ false 11 := outs_eq hout 11 (by simp)
    have o12 : σ (.n 32) = cellsOfState _ false 12 := outs_eq hout 12 (by simp)
    have hy := challengeT_value hch o0
    refine ⟨[σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7), σ (.n 8)], σ (.n 9), σ (.n 12), σ (.n 15),
      ⟨rfl, ?_⟩, ?_, ?_, ?_⟩
    · intro j hj
      simp only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · exact l4
      · exact l5
      · exact l6
      · exact l7
      · exact l8
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
        rw [← o8]; exact l28
      · show LoadHolds rd (σ (.n 0)) 8 (cellsOfState _ false 9)
        rw [← o9]; exact l29
      · show LoadHolds rd (σ (.n 0)) 9 (cellsOfState _ false 10)
        rw [← o10]; exact l30
      · show LoadHolds rd (σ (.n 0)) 10 (cellsOfState _ false 11)
        rw [← o11]; exact l31
      · show LoadHolds rd (σ (.n 0)) 11 (cellsOfState _ false 12)
        rw [← o12]; exact l32
    · rw [round4_sponge, ← hret, h38, h37, h36, word_eight, h44, h43, h42, h41, h40, h39, h35,
        h34, h45, word_one, ← round4_eval, hy]
      rfl
  · intro hm
    obtain ⟨rec, cur, claim, tabs, rfl⟩ : ∃ rec cur claim tabs, args = [rec, cur, claim, tabs] := by
      match args, hm with
      | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
    obtain ⟨cap, c0, c2, c3, ⟨hcl, hcap⟩, hrd, ⟨-, hst⟩, hret⟩ := hm
    rcases cap with _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, _ | ⟨a9, cap⟩⟩⟩⟩⟩⟩ <;>
      simp only [List.length_cons, List.length_nil] at hcl <;> try omega
    rw [round4_sponge] at hst hret
    obtain ⟨S, hSdef⟩ : ∃ S, S =
        (⟨[a4, a5, a6, a7, a8], [(c0, dsObserve), (c2, dsObserve), (c3, dsObserve)]⟩ : Fs).perm :=
      ⟨_, rfl⟩
    simp only [Fs.squeeze] at hst hret
    simp only [← hSdef] at hst hret
    let σ : Val := fun v => r4Vals rec cur claim tabs [a4, a5, a6, a7, a8] c0 c2 c3 S v.idx
    have ev : ∀ k, σ (.n k) = r4Vals rec cur claim tabs [a4, a5, a6, a7, a8] c0 c2 c3 S k :=
      fun _ => rfl
    have hS : permOf ([.n 10, .n 11, .n 13, .n 14, .n 16, .n 17, .n 18, .n 19, .n 4, .n 5, .n 6,
        .n 7, .n 8].map σ) = S := by
      rw [hSdef, perm_eq_cells _ (by simp)]
      dsimp only
      rw [← round4_ins]
      simp [ev, r4Vals]
    have ld : ∀ j (hj : j < 5), LoadHolds rd rec j ([a4, a5, a6, a7, a8] : List E)[j] :=
      fun j hj => by simpa using hcap j hj
    have st : ∀ j (hj : j < 5), LoadHolds rd rec (7 + j) (capOf S)[j] := fun j hj => by
      have := hst j (by simpa [Fs.squeeze, capOf] using hj)
      rwa [loadHolds_mul_gen_pow, Nat.zero_add, Nat.mul_one] at this
    refine ⟨σ, by simp [ev, r4Vals], ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
      keccakA_of (rd := rd) rfl rfl ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · exact ld 0 (by omega)
    · exact ld 1 (by omega)
    · exact ld 2 (by omega)
    · exact ld 3 (by omega)
    · exact ld 4 (by omega)
    · simpa [ev, r4Vals] using hrd 0 (by simp)
    · exact ⟨by simp [ev, r4Vals], by simp [ev, r4Vals]⟩
    · simpa [ev, r4Vals] using hrd 1 (by simp)
    · exact ⟨by simp [ev, r4Vals], by simp [ev, r4Vals]⟩
    · simpa [ev, r4Vals] using hrd 2 (by simp)
    · exact ⟨by simp [ev, r4Vals], by simp [ev, r4Vals]⟩
    · simp [ev, r4Vals]
    · simp [ev, r4Vals]
    · rw [hS]
      funext c
      fin_cases c <;> simp [cells13, ev, r4Vals]
    · show r4Vals rec cur claim tabs [a4, a5, a6, a7, a8] c0 c2 c3 S 33 =
        r4Vals rec cur claim tabs [a4, a5, a6, a7, a8] c0 c2 c3 S 20
      simp [r4Vals, Keccak.challengeOf_cells]
    · simpa [ev, r4Vals, capOf] using st 0 (by omega)
    · simpa [ev, r4Vals, capOf] using st 1 (by omega)
    · simpa [ev, r4Vals, capOf] using st 2 (by omega)
    · simpa [ev, r4Vals, capOf] using st 3 (by omega)
    · simpa [ev, r4Vals, capOf] using st 4 (by omega)
    all_goals try (simp [ev, r4Vals, word_one]; done)
    rw [hret, ← word_eight, ← round4_eval]
    simp [ev, r4Vals]

end
end LeanVM.Guest.B1
