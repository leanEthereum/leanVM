/-
  LeanVM.Guest.B1.Whir.InterfaceW

  `open_stacked`'s soundness with its witness named: the stream words and the openings it reads,
  as functions of its valuation and the frame map.
-/

module

public import LeanVM.Guest.B1.Whir.Interface
public import LeanVM.Guest.B1.Main.Frames

/-!
# `open_stacked`, its witness named

The witness convention (G6, 2026-10-23, `B1/Main/Frames.lean`): a witness is a function of the
function's own valuation `σ` and the frame map `V`, reading words only. `open_stacked`'s witness
`osW rd m σ V` at the candidate `m` is the stream words at the cursor `σ 8` and the openings, one
phase per level, read off the frames of its `opening_queries` calls and the cap's cells; it is
defined with the template of the body (`Whir/Witness.lean`).

`OpenOutW` is `OpenOut` at given words and openings. `open_stacked_sound_w_Spec osW`: under a call
relation `C ≤ Rel` unfolding at `V`, a valuation `σ` holding the candidate's body on the arguments
`fs ++ [target, root0, root1, cur, tabs]`, the window tables at `tabs`, gives `OpenOutW` at
`osW rd (candidate μ r) σ V`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `OpenOut` at given words and openings -/

/-- **`OpenOut` at the words `xs` and the openings `os`.** -/
def OpenOutW (rd : Reader) (μ r : ℕ) (root : Digest) (fs : List E) (target cur : E)
    (rets : List E) (xs : List E) (os : List (List Opening)) : Prop :=
  ∃ (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
    ReadsAt rd cur xs ∧
    RunsWith (whirOpen μ r target) ⟨fs, []⟩ xs os [(root, stackShape μ r)] w s' roots' ∧
    w.point.length = μ ∧
    ∃ pt pt1 : E, rets = [w.target, pt, pt1, w.inner, w.residual] ∧
      ReadsAt rd pt (w.point ++ List.replicate (pointCap - μ) 0) ∧
      ReadsAt rd pt1 (w.point.map (1 + ·) ++ List.replicate (pointCap - μ) 1)

theorem OpenOutW.openOut {rd : Reader} {μ r : ℕ} {root : Digest} {fs : List E} {target cur : E}
    {rets xs : List E} {os : List (List Opening)} (h : OpenOutW rd μ r root fs target cur rets xs os) :
    OpenOut rd μ r root fs target cur rets := by
  obtain ⟨w, s', roots', h1, h2, h3, h4⟩ := h
  exact ⟨xs, os, w, s', roots', h1, h2, h3, h4⟩

/-! ## The statement -/

/-- **`open_stacked` is sound with its witness `osW`**: under a call relation `C ≤ Rel` unfolding
at the frame map `V`, a valuation `σ` holding the body of the candidate of `μ`, `r` on the
capacity cells `fs`, the claim `target`, the root's two cells, the cursor and the window tables
`tabs`, returning `rets`, on a memory image of `2^κ` words, `11 ≤ κ ≤ 32`, (the query windows' range
checks), gives `OpenOutW` at the words and openings `osW L.read (candidate μ r) σ V`. -/
def open_stacked_sound_w_Spec
    (osW : Reader → ℕ → Val → FrameMap → List E × List (List Opening)) :
    Prop :=
  ∀ {κ : ℕ}, κ ≤ 32 → winTabBits ≤ κ → ∀ (L : MemoryImage κ) (C : CallRel) (V : FrameMap),
    UnfoldsV L.read C V →
    CallRel.Le C (coreProgram.Rel L.read) →
    ∀ (μ r : ℕ), 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 →
      ∀ (root : Digest) (fs : List E) (target root0 root1 cur tabs : E) (rets : List E) (fn : Fn)
        (σ : Val), fs.length = 5 → (root0, root1) = digestHalves root →
        WinTabs L.read tabs → coreProgram.find? (openName μ r) = some fn →
        fn.params.map σ = fs ++ [target, root0, root1, cur, tabs] →
        Stmt.HoldsList C L.read σ fn.body False (fun rs ↦ rs = rets) →
        OpenOutW L.read μ r root fs target cur rets (osW L.read (candidate μ r) σ V).1
          (osW L.read (candidate μ r) σ V).2

end
end LeanVM.Guest.B1.Whir
