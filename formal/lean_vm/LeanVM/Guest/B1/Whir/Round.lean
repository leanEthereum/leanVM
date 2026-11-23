/-
  LeanVM.Guest.B1.Whir.Round

  B1 for `opening_round`: one fold round of the stacked WHIR opening.
-/

module

public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Common.Run
public import LeanVM.Guest.B1.Bits.MeaningP
public import LeanVM.Guest.B1.Whir.Flat
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«opening_round»

/-!
# `opening_round` (`lean_ethereum.py`, G below)

One fold round of CWYZ26's affine combiner (`foldRound`, `Statement/LeanVmVerifier.lean`): the
four scalars `u0, w, c0, c1`, a grind and `α`, then `β`; `α` stored for the point and, with
`β`, for the queries' row folds, and the claim folded at `α`.

* `roundBody`: its core IR (`opening_round_body`, `RoundSound.lean`, by kernel evaluation);
* `MeaningOpeningRound`: what a call establishes, over the carried sponge (`rdS2`, `rdG2`,
  `Fs.squeeze`);
* `opening_round_soundP` (`RoundSound.lean`): the core IR gives the meaning in every program
  that finds it, under `grind_check_SpecP P 7`, on a memory image whose `tabs` holds the bit
  windows (`RoundFind.lean` states it at `coreProgram`);
* `opening_round_run`: the meaning runs `foldRound st` for every `st` with that claim.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- `opening_round`'s body: the capacity copied, the four scalars `u0, w, c0, c1`
and their permutation, the grind's nonce and permutation, `α`, the squeeze of `β`, the stores,
the claim. -/
def roundBody : List Stmt :=
  ((List.range 5).map fun i ↦ .atom (.copy (.n ((val% «opening_round» "sp[0]") + i)) (.n i))) ++
  fsNextT (.n (val% «opening_round» "cursor")) 0 (val% «opening_round» "x@1") ++ fsNextT (.n (val% «opening_round» "cursor")) 1 (val% «opening_round» "x@2") ++ fsNextT (.n (val% «opening_round» "cursor")) 2 (val% «opening_round» "x@3") ++ fsNextT (.n (val% «opening_round» "cursor")) 3 (val% «opening_round» "x@4") ++
  [keccakA (permIns 4 [.n (val% «opening_round» "msg[0]"), .n (val% «opening_round» "msg[1]"), .n (val% «opening_round» "msg[2]"), .n (val% «opening_round» "msg[3]"), .n (val% «opening_round» "msg[4]"), .n (val% «opening_round» "msg[5]"), .n (val% «opening_round» "msg[6]"), .n (val% «opening_round» "msg[7]")] 44 (osRun 10 5))
    (osRun 27 13)] ++
  fsNonceT (.n (val% «opening_round» "cursor")) 4 (val% «opening_round» "s6.i0:fs_grind_squeeze.s0.e.s0.t.s2#0") ++ padRunT 43 ++
  [keccakA (permIns 1 [.n (val% «opening_round» "nonce_rate[0]"), .n (val% «opening_round» "nonce_rate[1]")] 44 (osRun 35 5)) (osRun 48 13),
    .call "grind_check__L7" [.n (val% «opening_round» "nxt[1]@2"), .n (val% «opening_round» "tabs")] []] ++
  [keccakA (permIns 0 [] 44 (osRun 56 5)) (osRun 61 13)] ++
  [osLd 48 8 0, osLd 48 9 0, osLd 61 9 1,
    osMul 74 61 21, osAdd 75 15 74, osAdd 76 15 6, osMul 77 48 18, osAdd 78 76 77,
    osAdd 79 21 24, osMul 80 61 79, osAdd 81 78 80, osMul 82 48 81, osAdd 83 75 82] ++
  ((List.range 5).map fun i ↦ osCp (84 + i) (69 + i)) ++
  [osCst 89 (word 32 0), osMul 90 5 89, osCp 91 90, osCp 92 83,
    .ret [.n (val% «opening_round» "s13#0"), .n (val% «opening_round» "s13#0[1]"), .n (val% «opening_round» "s13#0[2]"), .n (val% «opening_round» "s13#0[3]"), .n (val% «opening_round» "s13#0[4]"), .n (val% «opening_round» "s13#0[5]"), .n (val% «opening_round» "s13#0[6]")]]

/-! ## The meaning -/

/-- The sponge before the grind: the four scalars waiting. -/
def rdS2 (fs : List E) (m : List E) : Fs := (⟨fs, []⟩ : Fs).absorbAll m dsObserve

/-- `α` and the sponge after it. -/
def rdG2 (fs : List E) (m : List E) (n2 : E) : E × Fs :=
  (rdS2 fs m).grindSqueeze _root_.LeanVM.Parameters.Whir.foldGrindingBits n2

/-- The fold round's claim: `u0 + β c0 + α (u0 + claim + α w + β (c0 + c1))`. -/
def roundClaim (claim alpha beta u0 w c0 c1 : E) : E :=
  u0 + beta * c0 + alpha * (u0 + claim + alpha * w + beta * (c0 + c1))

/-- **`opening_round(fs0..fs4, cursor, claim, tabs, alphas, coefs)`**: the five
stream words at the cursor `u0, w, c0, c1, n2`; from the carried capacity with nothing waiting,
the four scalars are absorbed, the grind passes and draws `α`, then `β` is squeezed; `α` is stored
at `alphas`, `α, β` at `coefs`; the function returns the capacity after `β`, the cursor five words
on and the folded claim. -/
def MeaningOpeningRound (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, cur, claim, _, gp, cp], rets =>
    ∃ u0 w c0 c1 n2 : E, ReadsAt rd cur [u0, w, c0, c1, n2] ∧
      let fs := [f0, f1, f2, f3, f4]
      let m := [u0, w, c0, c1]
      let ga := rdG2 fs m n2
      let gb := ga.2.squeeze
      (rdS2 fs m).GrindOk _root_.LeanVM.Parameters.Whir.foldGrindingBits n2 ∧
        LoadHolds rd gp 0 ga.1 ∧ LoadHolds rd cp 0 ga.1 ∧ LoadHolds rd cp 1 gb.1 ∧
        rets = gb.2.cap ++ [cur * gen ^ 5, roundClaim claim ga.1 gb.1 u0 w c0 c1]
  | _, _ => False

/-! ## Soundness -/

variable {rd : Reader} {σ : Val}

theorem grindCheckName_seven : grindCheckName 7 = "grind_check__L7" := rfl

/-- Four scalars absorbed from an empty queue: all four waiting. -/
theorem absorbAll_four (cap : List E) (a b c d : E) (t : ℕ) :
    (⟨cap, []⟩ : Fs).absorbAll [a, b, c, d] t = ⟨cap, [(a, t), (b, t), (c, t), (d, t)]⟩ := by
  simp [Fs.absorbAll, Fs.absorb, rateScalars]

/-! ## The run -/

/-- **`opening_round`'s meaning runs the Spec's `foldRound`**: from the carried capacity `fs` with
nothing waiting, the five words read, the grind passing, `foldRound st` returns the state with the
claim folded at `α` and `α` appended, and the round's `α, β`; the sponge left is the one after
`β`. -/
theorem opening_round_run (st : WhirState) (fs : List E) (u0 w c0 c1 n2 : E)
    (h2 : (rdS2 fs [u0, w, c0, c1]).GrindOk _root_.LeanVM.Parameters.Whir.foldGrindingBits n2) :
    RunsTo (foldRound st) ⟨fs, []⟩ [u0, w, c0, c1, n2]
      ({ st with
          claim := roundClaim st.claim (rdG2 fs [u0, w, c0, c1] n2).1
            (rdG2 fs [u0, w, c0, c1] n2).2.squeeze.1 u0 w c0 c1,
          alphas := st.alphas ++ [(rdG2 fs [u0, w, c0, c1] n2).1] },
        ⟨(rdG2 fs [u0, w, c0, c1] n2).1, (rdG2 fs [u0, w, c0, c1] n2).2.squeeze.1⟩)
      (rdG2 fs [u0, w, c0, c1] n2).2.squeeze.2 := by
  have hb : _root_.LeanVM.Parameters.Whir.foldGrindingBits ≠ 0 := by decide
  have g2 := runsToG_grind hb (rdS2 fs [u0, w, c0, c1]) n2 (h2.resolve_left hb)
  have e2 : rdG2 fs [u0, w, c0, c1] n2 =
      (challengeOf ((rdS2 fs [u0, w, c0, c1]).nonceState n2),
        ⟨capOf ((rdS2 fs [u0, w, c0, c1]).nonceState n2), []⟩) := Fs.grindSqueeze_pos _ hb _
  have es : rdS2 fs [u0, w, c0, c1] =
      ((((⟨fs, []⟩ : Fs).absorb u0 dsObserve).absorb w dsObserve).absorb c0 dsObserve).absorb
        c1 dsObserve := rfl
  rw [e2]
  rw [es] at g2 ⊢
  have r := (runsTo_readE _ u0).bind (f := fun u0 => do
      let w ← VerifierProgram.readScalar
      let c0 ← VerifierProgram.readScalar
      let c1 ← VerifierProgram.readScalar
      VerifierProgram.grindProofOfWork _root_.LeanVM.Parameters.Whir.foldGrindingBits
      let alpha ← VerifierProgram.sampleChallenge
      let beta ← VerifierProgram.sampleChallenge
      let claim := u0 + alpha * (u0 + st.claim) + alpha * alpha * w + beta * c0 +
        alpha * beta * (c0 + c1)
      return ({ st with claim := claim, alphas := st.alphas ++ [alpha] },
        (⟨alpha, beta⟩ : FoldRound)))
    ((runsTo_readE _ w).bind ((runsTo_readE _ c0).bind ((runsTo_readE _ c1).bind
      (g2.bindFrom ((runsFromG_sample _ _).bind ((runsTo_sampleE _).bind
        (runsTo_ret _ _)))))))
  refine RunsTo.of_eq r rfl rfl ?_ rfl
  simp only [Fs.squeeze, roundClaim]
  congr 2
  ring

end
end LeanVM.Guest.B1.Whir
