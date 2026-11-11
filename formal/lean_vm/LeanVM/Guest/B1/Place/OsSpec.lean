/-
  LeanVM.Guest.B1.Place.OsSpec

  open_stacked's placed completeness on f128, stated: what it returns, the bound of its callees,
  and the statements at every candidate, unbounded and bounded.
-/

module

public import LeanVM.Guest.B1.Place.OsMean
public import LeanVM.Guest.B1.Place.OsBos
public import LeanVM.Guest.B1.Whir.CompleteIface
public import LeanVM.Guest.B1.Whir.Witness
public import LeanVM.Guest.B1.Opening.QueriesPlacedD2
public import LeanVM.Guest.B1.Bits.QueryWindowsAt
public import LeanVM.Guest.Memory.SizeTotal
public import LeanVM.Guest.Memory.LoopPre
public import LeanVM.Guest.NZProgram

/-!
# `open_stacked`, placed: the statements

`OsOut μ w`: the returns and returned buffers, the run's claim, the point zero-padded, one plus
each coordinate one-padded, the glued weight and the residual's value.

**The callees' bound** (`osBk fs Bnd Kr c`): a named callee (`osKindOf`) within `Bnd f` words
(`OsLeafBounds`); the others summed over the levels that call them (`osSpB`): a level's squeeze
loop, its `squeezes + 1` frames and `squeezes` `decode_query_windows` frames; its
`opening_queries`, `oqBound` at its `N` queries (pairs at level `0`); a non-final level's residual
loop, `queries / 8` iterations of `Kr` words (`OsLoopBounds`) and its phantom frame.
`scripts/count/vsos.py` mirrors it.

**The statements**: `open_stacked_completeAtD_Spec`, at every candidate `μ ∈ [22, 28]`,
`r ∈ [1, 4]`, for certificates whose frame runs fit (`Lift.RunsFit`, `RunsConsec`), on memories
defined below `2^κ`, `11 ≤ κ` (the grinds' range checks): on an accepting run of
`whirOpen μ r target` from `⟨capOf S, []⟩` with no zero challenge and openings agreeing in the
caps, where every memory holding
the caller's words reads `xs` at the cursor and the window tables at `tabs`, the candidate's specialization is complete placed returning `OsOut μ w`.
`open_stacked_completeAtB_Spec`: within `osBosAt` words.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- What `open_stacked` returns: the claim, the two point buffers' pointers, the glued weight and
the residual's value; the buffers the point zero-padded and one plus it one-padded. -/
def OsOut (μ : ℕ) (w : WhirEnd) : List E → Layout → Prop := fun rets Lout ↦
  ∃ b b1 : ℕ, rets = [w.target, ofK (addressOfIndex b), ofK (addressOfIndex b1), w.inner,
      w.residual] ∧
    Lout = [(b, w.point ++ List.replicate (pointCap - μ) 0),
      (b1, w.point.map (1 + ·) ++ List.replicate (pointCap - μ) 1)]

/-! ## The callees' bound -/

/-- `decode_query_windows__L{depth}_L{capDepth}`, level `lv`'s. -/
def osDecodeName (lv : OsLv) : String :=
  "decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth

/-- The `opening_queries` queries level `l` makes: pairs at level `0`. -/
def osQN (l : ℕ) (lv : OsLv) : ℕ := lv.queries / (1 + if l = 0 then 1 else 0)

/-- **The special callees' bounds, level by level**: the squeeze loop, the `opening_queries`, the
residual loop (non-final levels). -/
def osSpB (fs Kr : String → ℕ) (c : OsCfg) : List (String × ℕ) :=
  (List.range c.levels.length).flatMap fun l ↦
    let lv := c.levels.getD l default
    let qn := osQueriesName c l lv
    [(c.sqLoop l, (lv.squeezes + 1) * fs (c.sqLoop l) + lv.squeezes * fs (osDecodeName lv)),
      (qn, oqBound fs qn (oqLoopOf qn) (osQN l lv))] ++
    (if l < c.yrLevel then
      [(c.resLoop l, lv.queries / resBatch * Kr (c.resLoop l) + fs (c.resLoop l))] else [])

/-- **The callees' bound**: a named callee's `Bnd f`, a special one's summed over its levels. -/
def osBk (fs Bnd Kr : String → ℕ) (c : OsCfg) (f : String) : ℕ :=
  if (osKindOf f).isSome then Bnd f
  else (((osSpB fs Kr c).filter (·.1 == f)).map (·.2)).sum

/-- **The named callees' words bounds**: callee `f`'s trees total at most `Bnd f` words. -/
def OsLeafBounds (fs : String → ℕ) (Bnd : String → ℕ) : Prop :=
  ∀ f K, osKindOf f = some K → TotalLe coreProgram fs f (fun _ ↦ Bnd f)

/-- **The residual loops' words an iteration**: the loop's run at `x`, `N` totals at most
`log_g N · Kr` words and its phantom frame. -/
def OsLoopBounds (fs Kr : String → ℕ) (c : OsCfg) : Prop :=
  ∀ l < c.yrLevel, TotalLeOn coreProgram fs (c.resLoop l) LoopPre
    (fun a ↦ logG (a.getD 1 0) * Kr (c.resLoop l) + fs (c.resLoop l))

/-- `open_stacked`'s frame-size bound at the candidate of `μ`, `r`. -/
def osBosAt (fs Bnd Kr : String → ℕ) (μ r : ℕ) : ℕ :=
  osBos fs (osBk fs Bnd Kr (osCfg (candidate μ r))) (openName μ r) (osCfg (candidate μ r))

/-! ## The statements -/

/-- **`open_stacked` is complete placed at every candidate.** -/
def open_stacked_completeAtD_Spec : Prop :=
  ∀ (μ r : ℕ), 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 →
    ∀ (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ), Lift.RunsFit fs cert →
      RunsConsec cert → 11 ≤ κ →
      ∀ (S : KeccakState) (root : Digest) (target cur tabs : E) (xs : List E)
        (os : List (List Opening)) (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
        RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots' →
        NoZeroChallenge μ r target S xs os root →
        CapsAgree μ r target S xs os root →
        ∀ Lin : Layout, (∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs ∧ WinTabs rd tabs) →
          CompleteAtD fs cert κ (openName μ r) Lin
            (capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur, tabs])
            (OsOut μ w)

/-- **`open_stacked` is complete placed at every candidate, within `osBosAt` words**, given the
named callees' bounds and the residual loops'. -/
def open_stacked_completeAtB_Spec : Prop :=
  ∀ (μ r : ℕ), 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 →
    ∀ (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (Bnd Kr : String → ℕ),
      Lift.RunsFit fs cert → RunsConsec cert → 11 ≤ κ → OsLeafBounds fs Bnd →
      OsLoopBounds fs Kr (osCfg (candidate μ r)) →
      ∀ (S : KeccakState) (root : Digest) (target cur tabs : E) (xs : List E)
        (os : List (List Opening)) (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
        RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots' →
        NoZeroChallenge μ r target S xs os root →
        CapsAgree μ r target S xs os root →
        ∀ Lin : Layout, (∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs ∧ WinTabs rd tabs) →
          CompleteAtB fs cert κ (openName μ r) Lin
            (capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur, tabs])
            (OsOut μ w) (osBosAt fs Bnd Kr μ r)

end
end LeanVM.Guest.B1
