/-
  LeanVM.Guest.B1.Fs.TailRound

  B1 for `opening_tail_round`: one round of a degree-two closing sumcheck, its meaning, the Spec
  run it is, and the proof that its core IR computes it.
-/

module

public import LeanVM.Guest.B1.Sumcheck.Run
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Common.Find

/-!
# `opening_tail_round` (TRIAGE G)

`opening_tail_round(fs0..fs4, cursor, claim, tabs)` (`crates/rec_aggregation/guests/
lean_ethereum.py`) reads `c0`, `c2` at the cursor, absorbs them, and squeezes `r` after the round's
grind (`ROUND2_GRIND_BITS`, zero bits as deployed: a plain squeeze); `h(0) + h(1) = claim` fixes
the linear coefficient, so it returns the capacity, the cursor two words on,
`h(r) = c0 + r (claim + (1 + r) c2)` and `r`. That is one plain round of `sumcheck _ 3`
(`tailRound_run`).

Its body: the capacity copied into `8 .. 12`, two `fs_next` (`13`, `16`), the pad run `19 .. 23`,
the permutation into `24 .. 36`, the challenge (`37`), the outputs.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **`opening_tail_round(fs0..fs4, cursor, claim, tabs)`**: the two stream words `c0`, `c2` at
the cursor absorbed on the carried capacity, the challenge `r` squeezed; it returns the capacity
after it, the cursor two words on, `c0 + r (claim + (1 + r) c2)` and `r`. -/
def MeaningOpeningTailRound (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, cur, claim, _], rets =>
      ∃ c0 c2 : E, ReadsAt rd cur [c0, c2] ∧
        let s := (⟨[f0, f1, f2, f3, f4], []⟩ : Fs).absorbAll [c0, c2] dsObserve
        rets = s.squeeze.2.cap ++ [cur * gen ^ 2,
          c0 + s.squeeze.1 * (claim + (1 + s.squeeze.1) * c2), s.squeeze.1]
  | _, _ => False

/-- `opening_tail_round`'s core IR is its meaning. -/
def opening_tail_round_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "opening_tail_round" args rets ↔ MeaningOpeningTailRound rd args rets

/-- The round's polynomial at `r`, in the guest's form. -/
theorem tail_eval (c0 c2 claim r : E) :
    c0 + r * (claim + (1 + r) * c2) = polyEval [c0, claim + sumE [c2], c2] r := by
  simp only [polyEval, List.foldr, sumE, List.foldl, zero_add, zero_mul]
  ring

/-- **`opening_tail_round` is a plain round of `sumcheck _ 3`.** -/
theorem tailRound_run (cap : List E) (c0 c2 claim : E) :
    let s := (⟨cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve
    RunsTo (sumcheck claim 3 [none]) ⟨cap, []⟩ [c0, c2]
      ([s.squeeze.1], c0 + s.squeeze.1 * (claim + (1 + s.squeeze.1) * c2)) s.squeeze.2 := by
  intro s
  have h := runsTo_sumcheck_cons (runsTo_roundPolyNone ⟨cap, []⟩ claim c0 [c2] 3 rfl (by decide))
    (runsTo_sumcheck_nil _ (polyEval [c0, claim + sumE [c2], c2]
      (((⟨cap, []⟩ : Fs).absorb c0 dsObserve).absorbAll [c2] dsObserve).squeeze.1) 3)
  refine h.of_eq rfl rfl ?_ rfl
  rw [tail_eval]
  rfl

theorem find_opening_tail_round : coreProgram.find? "opening_tail_round" = some Data.core8 :=
  coreProgram_find?_at (j := 8) rfl

theorem core8_params : Fn.params Data.core8 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] :=
  rfl

theorem core8_body : Fn.body Data.core8 =
    [.atom (.copy (.n 8) (.n 0)), .atom (.copy (.n 9) (.n 1)), .atom (.copy (.n 10) (.n 2)),
      .atom (.copy (.n 11) (.n 3)), .atom (.copy (.n 12) (.n 4))] ++
    fsNextT (.n 5) 0 13 ++ fsNextT (.n 5) 1 16 ++ padRunT 19 ++
    [keccakA [.n 14, .n 15, .n 17, .n 18, .n 20, .n 21, .n 22, .n 23, .n 8, .n 9, .n 10, .n 11, .n 12]
        [.n 24, .n 25, .n 26, .n 27, .n 28, .n 29, .n 30, .n 31, .n 32, .n 33, .n 34, .n 35, .n 36]] ++
    challengeT (.n 24) 37 ++
    [.atom (.copy (.n 38) (.n 32)), .atom (.copy (.n 39) (.n 33)), .atom (.copy (.n 40) (.n 34)),
      .atom (.copy (.n 41) (.n 35)), .atom (.copy (.n 42) (.n 36)),
      .atom (.const (.n 43) (word 4 0)), .atom (.mul (.n 44) (.n 5) (.n 43)),
      .atom (.copy (.n 45) (.n 44)), .atom (.const (.n 46) (word 1 0)),
      .atom (.add (.n 47) (.n 46) (.n 37)), .atom (.mul (.n 48) (.n 47) (.n 16)),
      .atom (.add (.n 49) (.n 6) (.n 48)), .atom (.mul (.n 50) (.n 37) (.n 49)),
      .atom (.add (.n 51) (.n 13) (.n 50)), .atom (.copy (.n 52) (.n 37)),
      .ret [.n 38, .n 39, .n 40, .n 41, .n 42, .n 45, .n 51, .n 52]] :=
  stmtsEqb_sound (by decide +kernel)

theorem word_four : word 4 0 = gen ^ 2 := word_two_pow (a := 2) (by decide)

/-- The sponge of the round: two scalars waiting on the capacity. -/
theorem tail_sponge (cap : List E) (c0 c2 : E) :
    (⟨cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve = ⟨cap, [(c0, dsObserve), (c2, dsObserve)]⟩ := by
  rw [absorbAll_short _ _ _ (by simp)]
  rfl

/-- The rate cells the permutation reads. -/
theorem tail_ins (cap : List E) (c0 c2 : E) :
    [c0, word 0 dsObserve, c2, word 0 dsObserve, 0, 0, 0, 0] ++ cap =
      pendCells [(c0, dsObserve), (c2, dsObserve)] ++
        List.replicate (8 - 2 * [(c0, dsObserve), (c2, dsObserve)].length) 0 ++ cap := rfl

/-- The honest values of `opening_tail_round`, by index. -/
def tlVals (as : List E) (c0 c2 : E) (S : KeccakState) (k : ℕ) : E :=
  let r := challengeOf S
  let cur := as.getD 5 0
  let claim := as.getD 6 0
  if k < 8 then as.getD k 0
  else if k < 13 then as.getD (k - 8) 0
  else if k < 19 then [c0, c0, word 0 dsObserve, c2, c2, word 0 dsObserve].getD (k - 13) 0
  else if k = 19 then word 1 0
  else if k < 24 then 0
  else if k < 37 then cellsOfState S false ⟨(k - 24) % 13, Nat.mod_lt _ (by omega)⟩
  else if k = 37 then r
  else if k < 43 then cellsOfState S false ⟨(k - 30) % 13, Nat.mod_lt _ (by omega)⟩
  else [word 4 0, cur * word 4 0, cur * word 4 0, word 1 0, word 1 0 + r,
    (word 1 0 + r) * c2, claim + (word 1 0 + r) * c2, r * (claim + (word 1 0 + r) * c2),
    c0 + r * (claim + (word 1 0 + r) * c2), r].getD (k - 43) 0

/-- **`opening_tail_round`'s core IR is its meaning.** -/
theorem opening_tail_round_holds : opening_tail_round_Spec := by
  intro rd args rets
  rw [rel_iff_sem find_opening_tail_round, core8_body, core8_params]
  simp only [holdsList_append, holds_fsNextT, holds_padRunT, holds_challengeT, keccakA,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  constructor
  · rintro ⟨σ, hp, h8, h9, h10, h11, h12, ⟨hl0, hp0⟩, ⟨hl1, hp1⟩, ⟨-, z20, z21, z22, z23⟩,
      hKH, hch, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, hret⟩
    subst hp
    have hKA : (Atom.keccak [.n 14, .n 15, .n 17, .n 18, .n 20, .n 21, .n 22, .n 23, .n 8, .n 9,
        .n 10, .n 11, .n 12] [.n 24, .n 25, .n 26, .n 27, .n 28, .n 29, .n 30, .n 31, .n 32, .n 33,
        .n 34, .n 35, .n 36] false false).Holds rd σ := hKH
    have hout := keccakA_fs (s := ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)],
      [(σ (.n 13), dsObserve), (σ (.n 16), dsObserve)]⟩) hKA (by simp) (by
        have e14 : σ (.n 14) = σ (.n 13) := hp0.1
        have e15 : σ (.n 15) = word 0 dsObserve := hp0.2
        have e17 : σ (.n 17) = σ (.n 16) := hp1.1
        have e18 : σ (.n 18) = word 0 dsObserve := hp1.2
        have e8 : σ (.n 8) = σ (.n 0) := h8
        have e9 : σ (.n 9) = σ (.n 1) := h9
        have e10 : σ (.n 10) = σ (.n 2) := h10
        have e11 : σ (.n 11) = σ (.n 3) := h11
        have e12 : σ (.n 12) = σ (.n 4) := h12
        have e20 : σ (.n 20) = 0 := z20
        have e21 : σ (.n 21) = 0 := z21
        have e22 : σ (.n 22) = 0 := z22
        have e23 : σ (.n 23) = 0 := z23
        dsimp only
        rw [← tail_ins]
        simp only [List.map_cons, List.map_nil, e14, e15, e17, e18, e8, e9, e10, e11, e12, e20,
          e21, e22, e23]
        rfl)
    have o0 : σ (.n 24) = cellsOfState _ false 0 := outs_eq hout 0 (by simp)
    have o8 : σ (.n 32) = cellsOfState _ false 8 := outs_eq hout 8 (by simp)
    have o9 : σ (.n 33) = cellsOfState _ false 9 := outs_eq hout 9 (by simp)
    have o10 : σ (.n 34) = cellsOfState _ false 10 := outs_eq hout 10 (by simp)
    have o11 : σ (.n 35) = cellsOfState _ false 11 := outs_eq hout 11 (by simp)
    have o12 : σ (.n 36) = cellsOfState _ false 12 := outs_eq hout 12 (by simp)
    have hy := challengeT_value hch o0
    refine ⟨σ (.n 13), σ (.n 16), fun k hk => ?_, ?_⟩
    · simp only [List.length_cons, List.length_nil] at hk
      interval_cases k
      · exact hl0
      · exact hl1
    · rw [tail_sponge, ← hret, h38, h39, h40, h41, h42, o8, o9, o10, o11, o12, h45, h44, h43,
        word_four, h51, h50, h49, h48, h47, h46, h52, word_one, hy]
      rfl
  · intro hm
    obtain ⟨f0, f1, f2, f3, f4, cur, claim, tabs, rfl⟩ : ∃ f0 f1 f2 f3 f4 cur claim tabs,
        args = [f0, f1, f2, f3, f4, cur, claim, tabs] := by
      match args, hm with
      | [a, b, c, d, e, f, g, h], _ => exact ⟨a, b, c, d, e, f, g, h, rfl⟩
    obtain ⟨c0, c2, hrd, hret⟩ := hm
    rw [tail_sponge] at hret
    obtain ⟨S, hSdef⟩ : ∃ S, S =
        (⟨[f0, f1, f2, f3, f4], [(c0, dsObserve), (c2, dsObserve)]⟩ : Fs).perm := ⟨_, rfl⟩
    simp only [Fs.squeeze] at hret
    simp only [← hSdef] at hret
    let as := [f0, f1, f2, f3, f4, cur, claim, tabs]
    let σ : Val := fun v => tlVals as c0 c2 S v.idx
    have ev : ∀ k, σ (.n k) = tlVals as c0 c2 S k := fun _ => rfl
    have hS : permOf ([.n 14, .n 15, .n 17, .n 18, .n 20, .n 21, .n 22, .n 23, .n 8, .n 9, .n 10,
        .n 11, .n 12].map σ) = S := by
      rw [hSdef, perm_eq_cells _ (by simp)]
      dsimp only
      rw [← tail_ins]
      simp [ev, tlVals, as]
    refine ⟨σ, by simp [ev, tlVals, as], ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
      ⟨?_, ?_, ?_, ?_, ?_⟩, keccakA_of (rd := rd) rfl rfl ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try (simp [ev, tlVals, as]; done)
    · simpa [ev, tlVals, as] using hrd 0 (by simp)
    · simpa [ev, tlVals, as] using hrd 1 (by simp)
    · rw [hS]
      funext c
      fin_cases c <;> simp [cells13, ev, tlVals]
    · show tlVals as c0 c2 S 37 = tlVals as c0 c2 S 24
      simp [tlVals, Keccak.challengeOf_cells]
    · rw [hret, ← word_four]
      simp [ev, tlVals, as, capOf, word_one]

end
end LeanVM.Guest.B1
