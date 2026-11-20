/-
  LeanVM.Guest.B1.Fs.TailRoundP

  B1 for `opening_tail_round`: one round of a degree-two closing sumcheck, its meaning, the Spec
  run it is, and the proof that it computes it in every program that finds it. No guest data but
  its core module.
-/

module

public import LeanVM.Guest.B1.Sumcheck.Run
public import LeanVM.Guest.CoreFind
import LeanVM.Guest.B1.Common.Vc
public import LeanVM.Guest.Pack.P45.Core

/-!
# `opening_tail_round` (TRIAGE G)

`opening_tail_round(fs0..fs4, cursor, claim, tabs)` (`guests/lean_ethereum.py`) reads
`c0`, `c2` at the cursor, absorbs them, and squeezes `r` after the round's grind
(`ROUND2_GRIND_BITS`, zero bits as deployed: a plain squeeze); `h(0) + h(1) = claim` fixes
the linear coefficient, so it returns the capacity, the cursor two words on,
`h(r) = c0 + r (claim + (1 + r) c2)` and `r`. That is one plain round of `sumcheck _ 3`
(`tailRound_run`).

Its body: the capacity copied, the two stream words read and absorbed, the pad run, the
permutation (the challenge its first cell), the outputs. `vc` computes its condition, which the
meaning is rewritten to.
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

/-- `opening_tail_round`'s function in `P` is its meaning. -/
def opening_tail_round_SpecP (P : Program) : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    P.Rel rd "opening_tail_round" args rets ↔ MeaningOpeningTailRound rd args rets

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

theorem word_four : word 4 0 = gen ^ 2 := word_two_pow (a := 2) (by decide)

/-- The sponge of the round: two scalars waiting on the capacity. -/
theorem tail_sponge (cap : List E) (c0 c2 : E) :
    (⟨cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve = ⟨cap, [(c0, dsObserve), (c2, dsObserve)]⟩ := by
  rw [absorbAll_short _ _ _ (by simp)]
  rfl

/-- **`opening_tail_round` is its meaning**, in every program that finds it. -/
theorem opening_tail_round_holdsP (P : Program)
    [Finds P "opening_tail_round" Fn.«opening_tail_round».core] : opening_tail_round_SpecP P := by
  intro rd args rets
  rw [rel_iff_fnSem (Finds.find (P := P) (fn := Fn.«opening_tail_round».core))]
  rcases args with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | ⟨f4, _ | ⟨cur, _ | ⟨claim, _ |
    ⟨tabs, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    vc [keccakF_cells, word_zero, word_one, word_four] <;>
    simp only [MeaningOpeningTailRound]
  simp only [ReadsAt, tail_sponge, Fs.squeeze, capOf, perm_eq_cells, pendCells, List.flatMap_cons,
    List.flatMap_nil, List.replicate, scalarCells_eq, word_dsObserve, Keccak.challengeOf_cells,
    List.length_cons, List.length_nil, Nat.forall_lt_succ_left', Nat.not_lt_zero,
    IsEmpty.forall_iff, implies_true, List.getElem_cons_zero, List.getElem_cons_succ, and_true,
    List.cons_append, List.nil_append, exists_and_left, and_assoc, @eq_comm _ rets,
    Nat.reduceLeDiff]

end
end LeanVM.Guest.B1
