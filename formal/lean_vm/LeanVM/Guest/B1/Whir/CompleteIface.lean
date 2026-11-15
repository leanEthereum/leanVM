/-
  LeanVM.Guest.B1.Whir.CompleteIface

  The completeness interface of `open_stacked` (B1-b): the run it completes on, the two
  hypotheses on that run (no zero challenge, openings that agree in the caps), and the statement.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Guest.B1.Whir.Interface
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.AcceptableChild

/-!
# `open_stacked`'s completeness: the interface

**The run.** An honest child's stacked WHIR opening is an accepting run of `whirOpen μ r target`
(`RunsWith`) from the sponge `⟨capOf S, []⟩` (the state `S` of the caller's sponge, nothing
waiting), the words `xs` and the openings `os`, the stack's root committed with its shape.

**Two hypotheses on the run**, without which the statement is false, as `AcceptableChild` states
them for the whole proof:

* `NoZeroChallenge μ r target S xs os root`: the same run passes `whirOpen` refusing a zero
  challenge (`VerifierProgram.refusingZeroChallenge`). The guest divides by the fold challenges,
  the closing rounds' challenges and each non-final level's `λ` (G =
  `lean_ethereum.py` at leanVM `010cfb18`).
* `CapsAgree μ r target S xs os root`: at every query step of the run (`Limits.queryStepsOf`),
  two openings giving one node of the tree a digest give it the same (`Limits.OpeningsAgree`).
  The guest writes each level's Merkle cap once (write-once memory), so openings meeting in the
  cap must agree there; the Spec checks each opening alone against the root.

**The statement** (`open_stacked_complete_SpecP P`, in the program `P`): for every base `b`, the function's own memory is
one layout `L` of `(exponent, words)` runs within `[b, b + n)` (`LayoutWithin`), its two point
buffers among them; on every memory holding `L` (`HoldsLayout`), the words `xs` at the cursor and
the window tables at `tabs`, the call of the size's arm on `rateSel r :: capOf S ++ [target,
root's two cells, cursor, tabs]` returns the run's claim, the pointers of the point buffers, its
glued weight and its residual's value.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The run's hypotheses -/

/-- **No zero challenge**: the run of `whirOpen μ r target` from the sponge `⟨capOf S, []⟩` on the
words `xs` and the openings `os`, the root committed, passes `whirOpen` refusing a zero
challenge. -/
def NoZeroChallenge (μ r : ℕ) (target : E) (S : KeccakState) (xs : List E)
    (os : List (List Opening)) (root : Digest) : Prop :=
  ∃ (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
    RunsWith (whirOpen μ r target).refusingZeroChallenge ⟨capOf S, []⟩ xs os
      [(root, stackShape μ r)] w s' roots'

/-- **The openings agree in the caps**: at every query step of the run of `whirOpen μ r target`
from the sponge state `S` (nothing waiting) on `xs` and `os`, the root committed, the step's
openings agree wherever they meet. -/
def CapsAgree (μ r : ℕ) (target : E) (S : KeccakState) (xs : List E)
    (os : List (List Opening)) (root : Digest) : Prop :=
  ∀ b ∈ Limits.queryStepsOf (whirOpen μ r target) ⟨⟨S, [], none⟩, xs, os, [(root, stackShape μ r)]⟩,
    Limits.OpeningsAgree b.1 b.2

/-! ## Memory layouts -/

/-- A layout of words: runs `(e, ws)`, word `j` at the address `g^(e + j)`. -/
abbrev OsLayout : Type := List (ℕ × List E)

/-- The memory holds the layout. -/
def HoldsLayout (rd : Reader) (L : OsLayout) : Prop :=
  ∀ q ∈ L, ∀ j (h : j < q.2.length), rd (addressOfIndex (q.1 + j)) = some q.2[j]

/-- The layout lies in the exponents `[b, b + n)`. -/
def LayoutWithin (L : OsLayout) (b n : ℕ) : Prop :=
  ∀ q ∈ L, b ≤ q.1 ∧ q.1 + q.2.length ≤ b + n

/-! ## The statement -/

/-- **`open_stacked` is complete** at every stack log and rate: on an accepting run of `whirOpen μ r target`
from the caller's sponge state `S` (nothing waiting), the words `xs` and the openings `os`, with
no zero challenge and openings that agree in the caps, for every base `b` the function's own
memory is a layout `L` within `[b, b + n)` holding its two point buffers (the run's point,
zero-padded, and one plus each of its coordinates, one-padded); on every memory holding `L`, the
words `xs` at the cursor and the window tables at `tabs`, the call returns the run's claim, the
point buffers' pointers, its glued weight and its residual's value. -/
def open_stacked_complete_SpecP (P : Program) : Prop :=
  ∀ (μ r : ℕ), minOpenLog ≤ μ → μ ≤ 30 → 1 ≤ r → r ≤ 4 →
    ∀ (S : KeccakState) (root : Digest) (target cur tabs : E) (xs : List E)
      (os : List (List Opening)) (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
      RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots' →
      NoZeroChallenge μ r target S xs os root → CapsAgree μ r target S xs os root →
      ∀ b : ℕ, ∃ (n : ℕ) (L : OsLayout) (pt pt1 : ℕ), LayoutWithin L b n ∧
        (pt, w.point ++ List.replicate (pointCap - μ) 0) ∈ L ∧
        (pt1, w.point.map (1 + ·) ++ List.replicate (pointCap - μ) 1) ∈ L ∧
        ∀ rd : Reader, HoldsLayout rd L → ReadsAt rd cur xs → WinTabs rd tabs →
          P.Rel rd (openName μ)
            (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur, tabs])
            [w.target, ofK (addressOfIndex pt), ofK (addressOfIndex pt1), w.inner, w.residual]

end
end LeanVM.Guest.B1.Whir
