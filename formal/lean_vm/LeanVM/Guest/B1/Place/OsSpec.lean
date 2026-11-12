/-
  LeanVM.Guest.B1.Place.OsSpec

  open_stacked's placed completeness, stated: what it returns, the bound of its callees, and the
  statements at every stack log and rate, unbounded and bounded.
-/

module

public import LeanVM.Guest.B1.Place.OsBos
public import LeanVM.Guest.B1.Whir.CompleteIface
public import LeanVM.Guest.B1.Bits.QueryWindowsAt
public import LeanVM.Guest.Memory.Size

/-!
# `open_stacked`, placed: the statements

`OsOut μ w`: the returns and returned buffers, the run's claim, the point zero-padded, one plus
each coordinate one-padded, the glued weight and the residual's value.

**The callees' bound** (`OsLeafBounds fs Bnd`): every callee of every arm (`osCalleeNames`) has
its trees within `Bnd` of its name (each is statically bounded: the leaves, `level_positions`,
`level_queries`, `level_residual`). `osBosAt fs Bnd μ`: the arm of `μ`'s bound (`osBos`).
`scripts/count/vsos.py` mirrors it.

**The statements**: `open_stacked_completeAtD_Spec`, at every stack log `μ ∈ [20, 30]` and rate
`r ∈ [1, 4]`, for certificates whose frame runs fit (`Lift.RunsFit`, `RunsConsec`), on memories
defined below `2^κ`, `11 ≤ κ` (the grinds' range checks): on an accepting run of
`whirOpen μ r target` from `⟨capOf S, []⟩` with no zero challenge and openings agreeing in the
caps, where every memory holding the caller's words reads `xs` at the cursor and the window tables
at `tabs`, the arm of `μ` called on the rate's selector is complete placed returning `OsOut μ w`.
`open_stacked_completeAtB_Spec`: within `osBosAt` words.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL)

@[expose] public section

/-- What `open_stacked` returns: the claim, the two point buffers' pointers, the glued weight and
the residual's value; the buffers the point zero-padded and one plus it one-padded. -/
def OsOut (μ : ℕ) (w : WhirEnd) : List E → Layout → Prop := fun rets Lout ↦
  ∃ b b1 : ℕ, rets = [w.target, ofK (addressOfIndex b), ofK (addressOfIndex b1), w.inner,
      w.residual] ∧
    Lout = [(b, w.point ++ List.replicate (pointCap - μ) 0),
      (b1, w.point.map (1 + ·) ++ List.replicate (pointCap - μ) 1)]

/-! ## The callees' bound -/

/-- The number of opening arms. -/
abbrev osArms : ℕ := openArms

/-- **The callees' words bounds**: every callee `f` of every arm has its trees within `Bnd f`
words. -/
def OsLeafBounds (fs : String → ℕ) (Bnd : String → ℕ) : Prop :=
  ∀ m < osArms, ∀ f ∈ osCalleeNames (osCfg m), TotalLe coreProgram fs f (fun _ ↦ Bnd f)

/-- `open_stacked`'s frame-size bound at the arm of the stack log `μ`. -/
def osBosAt (fs Bnd : String → ℕ) (μ : ℕ) : ℕ :=
  osBos fs Bnd (openName μ) (osCfg (μ - minOpenLog))

/-! ## The statements -/

/-- **`open_stacked` is complete placed at every stack log and rate.** -/
def open_stacked_completeAtD_Spec : Prop :=
  ∀ (μ r : ℕ), minOpenLog ≤ μ → μ ≤ 30 → 1 ≤ r → r ≤ 4 →
    ∀ (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ), Lift.RunsFit fs cert →
      RunsConsec cert → 11 ≤ κ →
      ∀ (S : KeccakState) (root : Digest) (target cur tabs : E) (xs : List E)
        (os : List (List Opening)) (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
        RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots' →
        NoZeroChallenge μ r target S xs os root →
        CapsAgree μ r target S xs os root →
        ∀ Lin : Layout, (∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs ∧ WinTabs rd tabs) →
          CompleteAtD fs cert κ (openName μ) Lin
            (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur,
              tabs])
            (OsOut μ w)

/-- **`open_stacked` is complete placed at every stack log and rate, within `osBosAt` words**,
given its callees' words bounds. -/
def open_stacked_completeAtB_Spec : Prop :=
  ∀ (μ r : ℕ), minOpenLog ≤ μ → μ ≤ 30 → 1 ≤ r → r ≤ 4 →
    ∀ (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (Bnd : String → ℕ),
      Lift.RunsFit fs cert → RunsConsec cert → 11 ≤ κ → OsLeafBounds fs Bnd →
      ∀ (S : KeccakState) (root : Digest) (target cur tabs : E) (xs : List E)
        (os : List (List Opening)) (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
        RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots' →
        NoZeroChallenge μ r target S xs os root →
        CapsAgree μ r target S xs os root →
        ∀ Lin : Layout, (∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs ∧ WinTabs rd tabs) →
          CompleteAtB fs cert κ (openName μ) Lin
            (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur,
              tabs])
            (OsOut μ w) (osBosAt fs Bnd μ)

end
end LeanVM.Guest.B1
