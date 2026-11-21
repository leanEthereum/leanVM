/-
  LeanVM.Compiler.Complete.AllocSel

  A dispatch's allocation hint reserves the frame of the callee its selector picks, the frame the
  honest memory gives that call, for every program.
-/

module

public import LeanVM.Compiler.Complete.Program
public import LeanVM.Parameters.Generator

/-!
# The frame of a dispatched call

A fused `match` of calls (`PStmt.dispatch`) shares one frame among its callees. Its first
instruction carries `LHint.allocFrameSel nfp x callees` (`emitDispatch_hints`), `x` the cell of
the selector, the one the jump table read `slot x` reads; assembly resolves it to
`RHint.allocSel nfp x sizes` with `sizes` the callees' frames in the layout
(`resolveHint_allocFrameSel`). Both provers' executors (`RHint::AllocSel`, `cpu/execute.rs`) read
the selector's word, find its exponent `j` (a discrete logarithm bounded below the order of `g`)
and reserve `sizes[j]` cells (`RHint.selSize?`).

The honest memory of the completeness theorem (`World.honestB`, `Memory.honest` at `World.fsB`)
gives every call instance its own callee's frame, a dispatch's included: the honest evaluation's
dispatch is the call of the first callee `j` with `σ x = g^j` (`Memory.pick`).
`World.allocSel_fsB`: for every program, at every exponent `k` below the order of `g` of the
selector's word, the hint reserves exactly `World.fsB f` cells, `f` the callee that call enters.
So the executors allocate what the completeness theorem's memory holds of that frame, and no
more. Hints are not constraints, so soundness does not depend on them (`assemble_dropHints`).
-/

namespace LeanVM.Compiler

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Memory

@[expose] public section

/-- **The executors' meaning of a selected allocation** (`RHint::AllocSel`): at the selector word
`g^j`, `allocSel` reserves `sizes[j]` cells, and a `j` past its list is a fault; no other hint
reserves by a selector. -/
def RHint.selSize? (j : ℕ) : RHint → Option ℕ
  | .allocSel _ _ sizes => sizes[j]?
  | _ => none

theorem resolveHint_allocFrameSel (l : Layout) (S ptr sel : Cell) (callees : List String)
    (j : ℕ) :
    (resolveHint l S (.allocFrameSel ptr sel callees)).selSize? j =
      callees[j]?.map (l.frame.getD · 0) := by
  simp [resolveHint, RHint.selSize?]

/-- A dispatch's first instruction carries the hints before it and the selected allocation of
its shared frame, read from the selector's own cell `x`. -/
theorem emitDispatch_hints (pos : Nat) (hints : List LHint) (callees : List String)
    (nfp joinCell x entry one : Cell) (first : Nat) (args rets : List Cell) :
    (emitDispatch pos hints callees nfp joinCell x entry one first args rets).head?.map
        (·.hints) = some (hints ++ [.allocFrameSel nfp x callees]) := by
  simp only [emitDispatch]
  split
  · next h => simp at h
  · simp

/-- The honest dispatch from callee `i`: the call of callee `i + j`, the first whose index's
power is the selector's word. -/
theorem pick_fall {σ : Val} {x : V} {args rets : List V} :
    ∀ {i : ℕ} {fs : List String} {es : List Ev}, pick σ x args rets i fs = .fall es →
      ∃ (j : ℕ) (h : j < fs.length), es = [.call fs[j] args rets] ∧
        σ x = ofK (addressOfIndex (i + j)) ∧ ∀ k < j, σ x ≠ ofK (addressOfIndex (i + k))
  | _, [], _, h => by simp [pick] at h
  | i, f :: fs, es, h => by
      unfold pick at h
      by_cases hx : σ x = ofK (addressOfIndex i)
      · simp only [hx, ↓reduceIte, Out.fall.injEq] at h
        exact ⟨0, by simp, by simpa using h.symm, by simpa using hx,
          fun k hk => absurd hk (by omega)⟩
      · simp only [hx, ↓reduceIte] at h
        obtain ⟨j, hj, he, hxj, hlt⟩ := pick_fall h
        refine ⟨j + 1, by simpa using hj, by simpa using he,
          by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hxj, fun k hk => ?_⟩
        cases k with
        | zero => simpa using hx
        | succ k =>
            have := hlt k (by omega)
            rwa [Nat.add_assoc, Nat.add_comm 1 k] at this

/-- **A dispatch's hint reserves its selected callee's frame**: when the honest evaluation's
dispatch on `x` enters `f`, at every exponent `k` below the order of `g` with `σ x = g^k`, the
resolved hint reserves `f`'s frame in the layout. -/
theorem allocSel_reserves {σ : Val} {x : V} {args rets : List V} {fs : List String} {f : String}
    (hp : pick σ x args rets 0 fs = .fall [.call f args rets]) (l : Layout) (S ptr sel : Cell)
    {k : ℕ} (hk : σ x = ofK (addressOfIndex k)) (hkb : k < 2 ^ 64 - 1) :
    (resolveHint l S (.allocFrameSel ptr sel fs)).selSize? k = some (l.frame.getD f 0) := by
  obtain ⟨j, hj, he, hxj, hlt⟩ := pick_fall hp
  have hf : f = fs[j] := by simpa using he
  have hjk : j ≤ k := by
    by_contra hc
    exact hlt k (by omega) (by simpa using hk)
  have hxj' : σ x = ofK (addressOfIndex j) := by simpa using hxj
  have hkj : k = j :=
    gpow_injOn hkb (show j < 2 ^ 64 - 1 by omega) (ofK_injective (hk.symm.trans hxj'))
  subst hkj hf
  rw [resolveHint_allocFrameSel, List.getElem?_eq_getElem hj]
  rfl

end
end LeanVM.Compiler

namespace LeanVM.Compiler.World

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Memory

@[expose] public section

/-- **For every compiled program, a dispatch's hint reserves the frame the honest memory gives its
call**: at the layout assembly resolves hints with (`World.layout`), when the honest dispatch on
`x` enters `f`, the selected allocation reserves `World.fsB f` cells, the frame size
`World.honestB` places that call instance at. -/
theorem allocSel_fsB {κ₀ : ℕ} (W : World κ₀) {σ : Val} {x : V} {args rets : List V}
    {fs : List String} {f : String} (hp : pick σ x args rets 0 fs = .fall [.call f args rets])
    (S ptr sel : Cell) {k : ℕ} (hk : σ x = ofK (addressOfIndex k)) (hkb : k < 2 ^ 64 - 1) :
    (resolveHint W.layout S (.allocFrameSel ptr sel fs)).selSize? k = some (W.fsB f) :=
  allocSel_reserves hp W.layout S ptr sel hk hkb

end
end LeanVM.Compiler.World

/-- info: 'LeanVM.Compiler.World.allocSel_fsB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.World.allocSel_fsB
