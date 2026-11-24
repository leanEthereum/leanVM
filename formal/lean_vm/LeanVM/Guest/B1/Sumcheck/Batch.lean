/-
  LeanVM.Guest.B1.Sumcheck.Batch

  B1 for `batch_sumcheck`: the claim-batching sumcheck, its rounds by induction.
-/

module

public import LeanVM.Guest.B1.Sumcheck.Meaning
public import LeanVM.Guest.B1.Common.Run
public import LeanVM.Guest.B1.Common.Find
import LeanVM.Guest.B1.Common.Vc
import LeanVM.Guest.Ref.KernelRfl

/-!
# `batch_sumcheck`

`batch_sumcheck(fs0..fs4, msgs, running, point, tabs, 23)` (`guests/lean_ethereum.py`) copies the
carried capacity, then per round `j` reads `g(1)`, `g(∞)` at `msgs[2j]`, `msgs[2j + 1]`, absorbs
them, squeezes the challenge (`fs_grind_squeeze` at zero bits: one permutation, its cell `0`),
stores it at `point[j]` and folds the degree-two round; it returns the last capacity and claim.

`vc` computes its condition: round by round, the two words read, the challenge stored, the
permutation's cells in place of its outputs. `BsRounds` is that condition for `n` rounds from
round `k`, and `bsRounds_iff` its meaning (`bsRun`), by induction on `n`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- A run read one word at a time. -/
private theorem readsAt_cons {rd : Reader} {p x : E} {xs : List E} :
    ReadsAt rd p (x :: xs) ↔ LoadHolds rd p 0 x ∧ ReadsAt rd (p * gen) xs := by
  have e (k : ℕ) (w : E) : LoadHolds rd (p * gen) k w ↔ LoadHolds rd p (k + 1) w := by
    rw [← pow_one gen, loadHolds_mul_gen_pow, Nat.add_comm]
  refine ⟨fun h => ⟨h 0 (by simp), fun k hk => (e k _).mpr (h (k + 1) (by simpa using hk))⟩,
    fun ⟨h0, h⟩ k hk => ?_⟩
  cases k with
  | zero => exact h0
  | succ k => exact (e k _).mp (h k (by simpa using hk))

/-- `n` rounds of `batch_sumcheck` from round `k` on the claim `claim` and the capacity `cap`,
returning `rets`: each round's words read at `msgs`, its permutation's challenge stored at
`point`, the round folded at it. -/
def BsRounds (rd : Reader) (msgs point : E) (rets : List E) : ℕ → ℕ → E → List E → Prop
  | _, 0, claim, cap => cap ++ [claim] = rets
  | k, n + 1, claim, cap =>
    ∃ a, LoadHolds rd msgs (2 * k) a ∧ ∃ b, LoadHolds rd msgs (2 * k + 1) b ∧
      let F := cellsOfState (permOf ([a, word 0 1, b, word 0 1, 0, 0, 0, 0] ++ cap)) false
      LoadHolds rd point k (F 0) ∧
        BsRounds rd msgs point rets (k + 1) n ((b * F 0 + (claim + a + a + b)) * F 0 + (claim + a))
          [F 8, F 9, F 10, F 11, F 12]

/-- A round's sponge: its two words absorbed on the capacity, its permutation squeezed. -/
private theorem bs_squeeze (cap : List E) (a b : E) :
    (((⟨cap, []⟩ : Fs).absorb a dsObserve).absorb b dsObserve).squeeze =
      let F := cellsOfState (permOf ([a, word 0 1, b, word 0 1, 0, 0, 0, 0] ++ cap)) false
      (F 0, ⟨[F 8, F 9, F 10, F 11, F 12], []⟩) := by
  have h : ((⟨cap, []⟩ : Fs).absorb a dsObserve).absorb b dsObserve =
      ⟨cap, [(a, dsObserve), (b, dsObserve)]⟩ := by
    simp [Fs.absorb, rateScalars]
  rw [h, Fs.squeeze, perm_eq_cells _ (by simp), Keccak.challengeOf_cells]
  rfl

private theorem exists_length_succ {α : Type} {n : ℕ} {P : List α → Prop} :
    (∃ l : List α, l.length = n + 1 ∧ P l) ↔ ∃ x l, l.length = n ∧ P (x :: l) :=
  ⟨fun ⟨l, hl, h⟩ => match l, hl, h with | x :: l, hl, h => ⟨x, l, by simpa using hl, h⟩,
    fun ⟨x, l, hl, h⟩ => ⟨x :: l, by simpa using hl, h⟩⟩

/-- **`BsRounds` is `bsRun`**: `n` rounds from round `k`, their words read from `msgs[2k]`, their
challenges stored from `point[k]`. -/
theorem bsRounds_iff (rd : Reader) (msgs point : E) (rets : List E) :
    ∀ (n k : ℕ) (claim : E) (cap : List E),
      BsRounds rd msgs point rets k n claim cap ↔
        ∃ rounds : List (E × E), rounds.length = n ∧
          ReadsAt rd (msgs * gen ^ (2 * k)) (rounds.flatMap fun g ↦ [g.1, g.2]) ∧
          let res := bsRun rounds claim ⟨cap, []⟩
          ReadsAt rd (point * gen ^ k) res.1.1 ∧ rets = res.2.cap ++ [res.1.2]
  | 0, k, claim, cap => by
    refine ⟨fun h => ⟨[], rfl, readsAt_nil _ _, readsAt_nil _ _, h.symm⟩, ?_⟩
    rintro ⟨l, hl, -, -, h⟩
    obtain rfl := List.length_eq_zero_iff.mp hl
    exact h.symm
  | n + 1, k, claim, cap => by
    have e (p : E) (j : ℕ) (w : E) : LoadHolds rd (p * gen ^ j) 0 w ↔ LoadHolds rd p j w := by
      rw [loadHolds_mul_gen_pow, Nat.add_zero]
    have g1 : msgs * gen ^ (2 * k) * gen = msgs * gen ^ (2 * k + 1) := by ring
    have g2 : msgs * gen ^ (2 * k + 1) * gen = msgs * gen ^ (2 * (k + 1)) := by ring
    have g3 : point * gen ^ k * gen = point * gen ^ (k + 1) := by ring
    rw [exists_length_succ]
    simp only [BsRounds, bsRounds_iff rd msgs point rets n, bsRun, bs_squeeze, Prod.exists,
      List.flatMap_cons, List.cons_append, List.nil_append, readsAt_cons, e, g1, g2, g3]
    constructor
    · rintro ⟨a, ha, b, hb, hp, l, hl, hm, hr, hret⟩
      exact ⟨a, b, l, hl, ⟨ha, hb, hm⟩, ⟨hp, hr⟩, hret⟩
    · rintro ⟨a, b, l, hl, ⟨ha, hb, hm⟩, ⟨hp, hr⟩, hret⟩
      exact ⟨a, ha, b, hb, hp, l, hl, hm, hr, hret⟩

/-- The meaning as the rounds' condition. -/
private theorem meaningBatchSumcheck_iff (n : ℕ) (rd : Reader)
    (f0 f1 f2 f3 f4 msgs running point tabs : E) (rets : List E) :
    MeaningBatchSumcheck n rd [f0, f1, f2, f3, f4, msgs, running, point, tabs] rets ↔
      BsRounds rd msgs point rets 0 n running [f0, f1, f2, f3, f4] := by
  rw [bsRounds_iff, Nat.mul_zero, pow_zero, mul_one, mul_one]
  rfl

/-- **`batch_sumcheck`'s core IR is its meaning.** -/
theorem batch_sumcheck_holds : batch_sumcheck_Spec := by
  intro rd args rets
  rw [rel_iff_fnSem (coreProgram_find?_at (j := idx% «batch_sumcheck__L23») rfl)]
  by_cases h : ∃ f0 f1 f2 f3 f4 msgs running point tabs,
      args = [f0, f1, f2, f3, f4, msgs, running, point, tabs]
  · obtain ⟨f0, f1, f2, f3, f4, msgs, running, point, tabs, rfl⟩ := h
    refine Iff.trans ?_
      (meaningBatchSumcheck_iff 23 rd f0 f1 f2 f3 f4 msgs running point tabs rets).symm
    vc [keccakF_cells, word_zero]
    kernel_rfl
  · refine iff_of_false (fun ⟨σ, hp, _⟩ => h ⟨_, _, _, _, _, _, _, _, _, hp.symm⟩) fun hm => h ?_
    match args, hm with
    | [f0, f1, f2, f3, f4, msgs, running, point, tabs], _ =>
      exact ⟨f0, f1, f2, f3, f4, msgs, running, point, tabs, rfl⟩

end
end LeanVM.Guest.B1
