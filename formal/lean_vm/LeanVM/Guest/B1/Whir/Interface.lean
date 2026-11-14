/-
  LeanVM.Guest.B1.Whir.Interface

  The interface of `open_stacked` (B1-b): the Spec's stacked WHIR opening split at the terminal
  the guest checks elsewhere, what a call of each of the specializations establishes about it,
  and the statement that every specialization's core IR establishes it.
-/

module

public import LeanVM.Guest.B1.Whir.Split
public import LeanVM.Guest.ExpTables
public import LeanVM.Guest.B1.Common.Sponge
public import LeanVM.Protocol.Compile.Prog

/-!
# `open_stacked` (TRIAGE G #42): the interface

`open_stacked(m_idx, rate_sel, fs0..fs4, target, commit_root_0, commit_root_1, cursor, tabs)`
(`crates/rec_aggregation/guests/lean_ethereum.py`, `open_stacked`) runs
the stacked WHIR opening of one child's proof, `verifyWhir` (`Statement/LeanVmVerifier.lean`;
`crates/verifier/src/whir.rs:215-329`) from `verifyStackedOpening`, up to its terminal: the
fold rounds of CWYZ26's affine combiner (`foldRound`), each non-final level's commitment, high
part, out-of-domain points and values, query grind, batching grind and `λ`, the final level's
lane and its query checks, and the closing sumcheck. The terminal's check
`(inner + evaluateBasis point) · residual = claim` is `check_opening_terminal`'s, which evaluates
the transparent weight `evaluateBasis`. It has `openArms` specializations `open_stacked__L{m}`, one
per stack log `μ = minOpenLog + m ≤ 30`, each reading its size's rows of the `LIG_*` tables at
compile time; the rate `1 ≤ r ≤ 4` is its first argument `rateSel r = g^(r - 1)`, which each
level's `match` on the rate dispatches into helpers specialized on the rate's shapes.

* `WhirEnd`, `whirLevelsOpen`, `whirOpen`: `whirLevels` and `verifyWhir` without the final
  `require`, returning what the terminal reads; `WhirEnd.Accepts` the terminal's check;
  `verifyWhir_split`: `verifyWhir` is `whirOpen` then `require Accepts` (proved here).
* `stackShape μ r`: the shape `commitStack` gives the stack's root (`commitStack_eq`, proved).
* `RunsWith p s xs os roots a s' roots'`: `RunsTo` (`B1/Common/Sponge.lean`) with the openings
  `os` read and the commitments `roots` growing to `roots'`, on any rest of the stream and of the
  openings.
* `OpenOut rd μ r root fs target cur rets`: what a call establishes: from the sponge the guest
  carries as the capacity `fs` with nothing waiting, the stack's root committed with its shape,
  the stream words at the cursor and some openings run `whirOpen μ r target` to `w`; the call
  returns `w`'s claim, two buffers holding `w`'s point (`μ` coordinates, witness order) and its
  coordinates plus one, zero-padded (one-padded) to `pointCap = 40`, `w`'s glued weight and its
  final lane's low part at the tail challenges.
* `open_stacked_sound_SpecP P`: in the program `P` (`InterfaceAt.lean`: at `coreProgram`), every specialization's call relation at `rateSel r` gives `OpenOut`, on a memory
  image of `2^κ` words, `11 ≤ κ ≤ 32` (the query windows' range checks, `decode_query_windows`) whose
  window tables are at `tabs` (`WinTabs`: the grinds' and the query windows' lookups).

The guest's claim differs from the Spec's between a non-final level and the end by the high
part's share of the level's queries times the challenges drawn after it: the guest adds it back in
its residual pass, so the returned claim is the Spec's.

The guest's completeness statement (an honest run with no zero fold, tail or batching challenge,
on a memory holding the hinted caps and rows, gives the call relation; DESIGN §5.2.1) follows the
soundness proof, its memory predicate named by the body's buffers.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Runs with openings and commitments -/

/-- From any Spec sponge the guest carries as `s`, the program `p` reads exactly the stream words
`xs` and the phases of openings `os`, the commitments read so far being `roots`, and returns `a`,
leaving a sponge the guest carries as `s'` and the commitments `roots'`, on any rest of the stream
and of the phases. -/
def RunsWith {α : Type} (p : VerifierProgram α) (s : Fs) (xs : List E) (os : List (List Opening))
    (roots : List (Digest × ℕ × ℕ)) (a : α) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)) : Prop :=
  ∀ sp : Sponge, s.Carries sp → ∀ (rest : List E) (orest : List (List Opening)),
    ∃ sp' : Sponge, s'.Carries sp' ∧ runId p ⟨sp, xs ++ rest, os ++ orest, roots⟩ = some (a, ⟨sp', rest, orest, roots'⟩)

/-! ## What a call establishes -/

/-- **`open_stacked__L{μ - minOpenLog}(rateSel r, fs0..fs4, target, root_0, root_1, cursor, tabs)`**
(TRIAGE #42): from the sponge the guest carries as the capacity `fs` with nothing waiting (the
batching challenge of `verifyStackedOpening` was just squeezed), the stack's
root `root` committed with its shape and nothing else, the words `xs` at the cursor and some
openings `os` run `whirOpen μ r target` to `w`; the function returns `w`'s claim, a buffer
holding its point (`μ` coordinates, zero-padded to `pointCap`), a buffer holding one plus each of
them (one-padded), its glued weight and its final lane's low part at the tail challenges. -/
def OpenOut (rd : Reader) (μ r : ℕ) (root : Digest) (fs : List E) (target cur : E)
    (rets : List E) : Prop :=
  ∃ (xs : List E) (os : List (List Opening)) (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
    ReadsAt rd cur xs ∧
    RunsWith (whirOpen μ r target) ⟨fs, []⟩ xs os [(root, stackShape μ r)] w s' roots' ∧
    w.point.length = μ ∧
    ∃ pt pt1 : E, rets = [w.target, pt, pt1, w.inner, w.residual] ∧
      ReadsAt rd pt (w.point ++ List.replicate (pointCap - μ) 0) ∧
      ReadsAt rd pt1 (w.point.map (1 + ·) ++ List.replicate (pointCap - μ) 1)

/-- **`open_stacked` is sound** in the program `P`, at every stack log and rate: a call of the specialization of `μ`
on the rate's selector, the capacity cells `fs`, the claim `target`, the root's two cells, the
cursor and the exponent
table `tabs` establishes `OpenOut`, on a memory image of `2^κ` words, `11 ≤ κ ≤ 32`,
(`decode_query_windows`' range checks) holding the window tables at `tabs` (`WinTabs`). -/
def open_stacked_sound_SpecP (P : Program) : Prop :=
  ∀ {κ : ℕ}, κ ≤ 32 → winTabBits ≤ κ → ∀ (L : MemoryImage κ) (μ r : ℕ), minOpenLog ≤ μ → μ ≤ 30 →
    1 ≤ r → r ≤ 4 →
    ∀ (root : Digest) (fs : List E) (target root0 root1 cur tabs : E) (rets : List E),
      fs.length = 5 → (root0, root1) = digestHalves root → WinTabs L.read tabs →
      P.Rel L.read (openName μ) (rateSel r :: fs ++ [target, root0, root1, cur, tabs]) rets →
        OpenOut L.read μ r root fs target cur rets

end
end LeanVM.Guest.B1.Whir
