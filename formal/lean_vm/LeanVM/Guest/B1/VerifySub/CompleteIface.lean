/-
  LeanVM.Guest.B1.VerifySub.CompleteIface

  `verify_sub`'s completeness interface: the run it completes on, the honest memory at the
  caller's `HeapBuf` pointers, and what completeness assumes of the callees groups 4 and 5 prove.
-/

module

public import LeanVM.Guest.B1.VerifySub.Body

/-!
# `verify_sub`'s completeness: the run, the memory, the callees

`VsData` is one accepting run of the deferring verifier as `verify_sub` runs it: the announced
sizes, the root, each callee's phase (its words, its value, its final state) and the values the
callees return. `VsData.Ok` says the phases run (the facts `verify_sub_sound` produces, and the
deployed limits: the stack log at least 22, the tables' log-heights below 29).

`VsPtrs` names every `HeapBuf` the run allocates, `verify_sub`'s own and its callees', and
`VsMem` says the memory holds the honest words there; the callees' scratch is each callee's own
predicate (`GMem`, `TMem`, …), group 4's and 5's to define, at its own pointers.

The callees' completeness (`Complete*`): the callee's soundness outcome, with its memory honest,
gives its relation; `HypTCtx` and `HypPCtx` say the honest memory of `verify_tables` and
`certify_placement` is what `check_opening_terminal` reads.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The callees' completeness -/

section Callees

variable (bytecode : List K)
  (TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop)
  (PCtx : Reader → List ℕ → E → E → Prop) (rd : Reader)

/-- The outcome without the terminal's context. -/
abbrev NoCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop :=
  fun _ _ _ _ _ ↦ True

/-- `verify_bus_gkr` is complete over its honest scratch `GMem rd ptrs args rets`. -/
def CompleteGkr (GMem : Reader → List E → List E → List E → Prop) : Prop :=
  ∀ ptrs fs0 fs1 cur gmu zeta rets, GkrOut rd fs0 fs1 cur gmu zeta rets →
    GMem rd ptrs [fs0, fs1, cur, gmu, zeta] rets →
      coreProgram.Rel rd "verify_bus_gkr" [fs0, fs1, cur, gmu, zeta] rets

/-- `verify_tables` is complete over its honest scratch and output buffers `TMem`. -/
def CompleteTables (TMem : Reader → List E → List E → List E → Prop) : Prop :=
  ∀ ptrs lp pi logMem alphas point values args rets,
    TablesPre rd lp pi logMem alphas point values args →
    TablesOut bytecode NoCtx rd pi logMem alphas point values args rets →
    TMem rd ptrs args rets → coreProgram.Rel rd "verify_tables" args rets

/-- Over `verify_tables`' honest memory, the terminal's context holds. -/
def HypTCtx (TMem : Reader → List E → List E → List E → Prop) : Prop :=
  ∀ ptrs lp pi logMem alphas point values args rets,
    TablesPre rd lp pi logMem alphas point values args →
    TablesOut bytecode NoCtx rd pi logMem alphas point values args rets →
    TMem rd ptrs args rets → TablesOut bytecode TCtx rd pi logMem alphas point values args rets

/-- `verify_flock` is complete over its honest scratch `FMem`. -/
def CompleteFlock (FMem : Reader → List E → List E → List E → Prop) : Prop :=
  ∀ ptrs τ fs0 fs1 cur zchis lrs zpart rets, τ < 29 →
    FlockOut rd τ fs0 fs1 cur zchis lrs zpart rets →
    FMem rd ptrs [fs0, fs1, cur, gen ^ τ, zchis, lrs, zpart] rets →
      coreProgram.Rel rd "verify_flock" [fs0, fs1, cur, gen ^ τ, zchis, lrs, zpart] rets

/-- `certify_placement` is complete over its honest memory `PMem` (its output buffers `off`,
`kap` among it). -/
def CompletePlace (PMem : Reader → List E → List E → List E → Prop) : Prop :=
  ∀ ptrs lp sq kb (logMem : ℕ) (hs : List ℕ) off kap, ExpTables rd lp sq → logMem ≤ 32 →
    hs.length = 6 → (∀ h ∈ hs, h < 29) → ReadsAt rd kb (1 :: gen ^ logMem :: hs.map (gen ^ ·)) →
    PMem rd ptrs [kb, sq] [gen ^ stackTotal (columnKappas logMem 18 hs), off, kap] →
      coreProgram.Rel rd "certify_placement" [kb, sq]
        [gen ^ stackTotal (columnKappas logMem 18 hs), off, kap]

/-- Over `certify_placement`'s honest memory, the terminal's context holds. -/
def HypPCtx (PMem : Reader → List E → List E → List E → Prop) : Prop :=
  ∀ ptrs lp sq kb (logMem : ℕ) (hs : List ℕ) off kap, ExpTables rd lp sq → logMem ≤ 32 →
    hs.length = 6 → (∀ h ∈ hs, h < 29) → ReadsAt rd kb (1 :: gen ^ logMem :: hs.map (gen ^ ·)) →
    PMem rd ptrs [kb, sq] [gen ^ stackTotal (columnKappas logMem 18 hs), off, kap] →
      PCtx rd (columnKappas logMem 18 hs) off kap

/-- `open_stacked` is complete at every candidate over its honest scratch `OMem`. -/
def CompleteOpen (OMem : ℕ → ℕ → Reader → List E → List E → List E → Prop) : Prop :=
  ∀ μ r, 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 →
    ∀ (root : Digest) ptrs fs0 fs1 target root0 root1 cur rets,
      (root0, root1) = digestScalars root → OpenOut rd μ r root fs0 fs1 target cur rets →
      OMem μ r rd ptrs [fs0, fs1, target, root0, root1, cur] rets →
        coreProgram.Rel rd (openName μ r) [fs0, fs1, target, root0, root1, cur] rets

/-- `check_opening_terminal` is complete over its honest scratch `EMem`. -/
def CompleteTerm (EMem : Reader → List E → List E → Prop) : Prop :=
  ∀ ptrs layout bus claims lam flockPoint coeffs w args,
    TermPre TCtx PCtx rd layout bus claims lam flockPoint coeffs w args →
    w.Accepts (stackWeight layout claims flockPoint coeffs lam) → EMem rd ptrs args →
      coreProgram.Rel rd "check_opening_terminal" args []

end Callees

end
end LeanVM.Guest.B1.VerifySub
