/-
  LeanVM.Guest.B1.Sumcheck.MeaningP

  The interface of B1's sumcheck functions: what each computes on the carried sponge, and the
  statement that its function in a program computes it (`Meaning.lean`: at `coreProgram`).
-/

module

public import LeanVM.Guest.B1.Common.Sponge
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Consts

/-!
# Sumcheck rounds: meanings (TRIAGE G #30-32)

For each function of the guest (`lean_ethereum.py`, G below) its meaning on its argument and
return words, the Fiat-Shamir sponge as the guest carries it (`Fs`, `B1/Common/Sponge.lean`), and
`…_SpecP P`, the statement that its relation in the program `P` is that meaning (`…_Spec` at
`coreProgram`, `Meaning.lean`, proved as `…_holds`).

| function | meaning |
| --- | --- |
| `sumcheck_round4` | one plain round of `sumcheck _ 4 [none]` (`sumcheckRoundPoly 4 claim none`, a sample), the sponge in a round record |
| `batch_sumcheck__L23` | `Node.batchRounds`, 23 rounds |

Each round's `fs_grind_squeeze` grinds `ROUND3_GRIND_BITS`, `ROUND5_GRIND_BITS`,
`ROUND2_GRIND_BITS` bits, all zero as deployed (`grindingBits` of a degree at most `8`): its
challenge is a plain squeeze (`Fs.grindSqueeze_zero`), and the window table `tabs` each takes is
not read.

A round record (`ROUND_FS = 0`, `ROUND_CURSOR = 5`, `ROUND_CLAIM = 6`, `ROUND_SLOTS = 7`) holds a
sponge's five capacity cells, a stream cursor and a claim, its fields `stride` words apart
(`fs_load`, `fs_store`: `1` for `sumcheck_round4`, `GKR_ROUNDS_CAP = 862` for `gkr_layer`'s).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- A record's five capacity cells, its fields `stride` words apart from offset `off`. -/
def CapAt (rd : Reader) (rec : E) (off stride : ℕ) (cap : List E) : Prop :=
  cap.length = 5 ∧ ∀ j (hj : j < cap.length), LoadHolds rd rec (off + j * stride) cap[j]

/-! ## `sumcheck_round4` (TRIAGE #30) -/

/-- **`sumcheck_round4(rd, msg_cursor, claim, tabs)`**: the record at `rd` carries the sponge's
capacity; the three stream words at the cursor are the round polynomial's
`c0, c2, c3` (`sumcheckRoundPoly 4 claim none`: `c1 = claim + c2 + c3`), absorbed, then the
challenge `y` squeezed; the next record (`rd·g^7`) carries the sponge after it; the function
returns the cursor three words on, the polynomial at `y` (`polyEval`) and `y`. -/
def MeaningSumcheckRound4 (rd : Reader) : List E → List E → Prop
  | [rec, cur, claim, _], rets =>
      ∃ (cap : List E) (c0 c2 c3 : E), CapAt rd rec 0 1 cap ∧ ReadsAt rd cur [c0, c2, c3] ∧
        let s := (⟨cap, []⟩ : Fs).absorbAll [c0, c2, c3] dsObserve
        CapAt rd (rec * gen ^ 7) 0 1 s.squeeze.2.cap ∧
        rets = [cur * gen ^ 3, polyEval [c0, claim + sumE [c2, c3], c2, c3] s.squeeze.1,
          s.squeeze.1]
  | _, _ => False

/-- `sumcheck_round4`'s function in `P` is its meaning. -/
def sumcheck_round4_SpecP (P : Program) : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    P.Rel rd "sumcheck_round4" args rets ↔ MeaningSumcheckRound4 rd args rets

/-! ## GKR rounds (TRIAGE #31)

`gkr_layer`'s equality-mode rounds of `sumcheck _ 5` (`sumcheckRoundPoly 5 claim (some e)`), as
in `gkrStep 2`: each `gkr_round`, inlined, so not a function of its own; runs of them between
round records are `B1/Gkr/Rounds.lean`'s. -/

/-- `GKR_ROUNDS_CAP`: the stride of a GKR round record's fields. -/
abbrev gkrRoundsCap : ℕ := guest_const% GKR_ROUNDS_CAP

/-- `MU_CAP + 2`: where the rounds' challenges go in the point buffer. -/
abbrev gkrChallengeAt : ℕ := 42

/-- The equality-mode rounds from the claim and the sponge, round `q` on its four coefficients
`c1 .. c4` (absorbed) and the previous point's coordinate `es[q]`: `c0 = claim + e·Σ c` (the
coefficient `sumcheckRoundPoly 5 claim (some e)` derives), the challenge squeezed, the claim the
polynomial there. The challenges, the final claim and the final sponge. -/
def gkrRun : List (List E) → List E → E → Fs → List E × E × Fs
  | cs :: rest, e :: es, claim, s =>
    let r := (s.absorbAll cs dsObserve).squeeze
    let res := gkrRun rest es (polyEval ((claim + e * sumE cs) :: cs) r.1) r.2
    (r.1 :: res.1, res.2)
  | _, _, claim, s => ([], claim, s)

/-- **`n` GKR rounds between records**: the record at `rec` (fields `862` words apart)
carries a sponge's capacity and a claim; the `4n` stream words at the cursor `cur` are the rounds'
coefficients `c1 .. c4`, the words `pt[q]`, `q < n`, the previous point's coordinates; the rounds
(`gkrRun`) store their challenges at `pt[42 + q]` (and a zero at `pt[42 + n]` when `n` is odd), and
the next record `rec·g` carries the sponge, the cursor `4n` words on and the claim after them. -/
def GkrRoundsOut (n : ℕ) (rd : Reader) (rec pt cur : E) : Prop :=
  ∃ (cap : List E) (claim : E) (cs : List (List E)) (es : List E),
    CapAt rd rec 0 gkrRoundsCap cap ∧ LoadHolds rd rec (6 * gkrRoundsCap) claim ∧
    cs.length = n ∧ (∀ c ∈ cs, c.length = 4) ∧ ReadsAt rd cur cs.flatten ∧
    es.length = n ∧ ReadsAt rd pt es ∧
    let res := gkrRun cs es claim ⟨cap, []⟩
    ReadsAt rd (pt * gen ^ gkrChallengeAt) res.1 ∧
    (n % 2 = 1 → LoadHolds rd pt (gkrChallengeAt + n) 0) ∧
    CapAt rd rec 1 gkrRoundsCap res.2.2.cap ∧
    LoadHolds rd rec (1 + 5 * gkrRoundsCap) (cur * gen ^ (4 * n)) ∧
    LoadHolds rd rec (1 + 6 * gkrRoundsCap) res.2.1

/-! ## `batch_sumcheck` (TRIAGE #32) -/

/-- `Node.batchRounds` on the carried sponge: per round `g(1)`, `g(∞)` absorbed, the challenge
squeezed, the degree-2 round folded. The challenges, the final claim, the final sponge. -/
def bsRun : List (E × E) → E → Fs → (List E × E) × Fs
  | [], claim, s => (([], claim), s)
  | (g1, gInf) :: rest, claim, s =>
    let r := ((s.absorb g1 dsObserve).absorb gInf dsObserve).squeeze
    let g0 := claim + g1
    let res := bsRun rest ((gInf * r.1 + (g0 + g1 + gInf)) * r.1 + g0) r.2
    ((r.1 :: res.1.1, res.1.2), res.2)

/-- **`batch_sumcheck(fs0..fs4, msgs, running, point, tabs, n)`**: from the carried capacity
(nothing waiting), the `n` rounds' words at `msgs` (`g(1)`, `g(∞)` per round) are
`Node.batchRounds running rounds` (`bsRun`), its challenges stored at `point`; the function
returns the final sponge's capacity and the final claim. -/
def MeaningBatchSumcheck (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, msgs, running, point, _], rets =>
      ∃ rounds : List (E × E), rounds.length = n ∧
        ReadsAt rd msgs (rounds.flatMap fun g ↦ [g.1, g.2]) ∧
        let res := bsRun rounds running ⟨[f0, f1, f2, f3, f4], []⟩
        ReadsAt rd point res.1.1 ∧ rets = res.2.cap ++ [res.1.2]
  | _, _ => False

/-- `batch_sumcheck__L23`'s function in `P` is its meaning. -/
def batch_sumcheck_SpecP (P : Program) : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    P.Rel rd "batch_sumcheck__L23" args rets ↔ MeaningBatchSumcheck 23 rd args rets

end
end LeanVM.Guest.B1
