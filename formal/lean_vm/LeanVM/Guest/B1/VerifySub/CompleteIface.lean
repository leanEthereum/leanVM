/-
  LeanVM.Guest.B1.VerifySub.CompleteIface

  `verify_sub`'s completeness interface: the run it completes on, the honest memory at the
  caller's `HeapBuf` pointers, and what completeness assumes of the callees groups 4 and 5 prove.
-/

module

public import LeanVM.Guest.B1.VerifySub.Body
public import LeanVM.Guest.B1.Uniform

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

/-- Over `verify_tables`' honest memory, the terminal's context holds of the same run: whatever
`Q` holds of the run's layout, bus result and claims, `TCtx` holds of them too. -/
def HypTCtx (TMem : Reader → List E → List E → List E → Prop) : Prop :=
  ∀ (Q : Reader → Layout → BusResult → List ColumnClaim → List E → Prop) ptrs lp pi logMem alphas
    point values args rets,
    TablesPre rd lp pi logMem alphas point values args →
    TablesOut bytecode Q rd pi logMem alphas point values args rets →
    TMem rd ptrs args rets →
      TablesOut bytecode (fun r l b c a ↦ Q r l b c a ∧ TCtx r l b c a) rd pi logMem alphas point
        values args rets

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

/-! ## The callees' completeness, placed

The uniform placed form (`Uniform.lean`): each callee is complete on every layout `Lin` of the
caller's words that makes its precondition true on every memory holding it (defined below `2^k`).
`verify_bus_gkr`, `verify_tables`, `verify_flock` and `check_opening_terminal` return fixed words
(`CompleteRel`); `certify_placement` and `open_stacked` return `HeapBuf`s, their contents in the
layout `Lout` they return (`CompleteAt`). -/

section Placed

open LeanVM.Guest.B1.Main (MemL)

variable (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (bytecode : List K)
  (TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop)
  (PCtx : Reader → List ℕ → E → E → Prop)

/-- `verify_bus_gkr`'s precondition and outcome on a memory (`GkrOut`). -/
def GkrPre (rd : Reader) : List E → List E → Prop
  | [fs0, fs1, cur, gmu, zeta], rets => GkrOut rd fs0 fs1 cur gmu zeta rets
  | _, _ => False

/-- **`verify_bus_gkr`, placed.** -/
def CompleteGkrAt : Prop := CompleteRel fs cert k "verify_bus_gkr" GkrPre

/-- `verify_tables`' precondition and outcome on a memory, the terminal's context included. -/
def TablesPreOut (rd : Reader) (args rets : List E) : Prop :=
  ∃ lp pi logMem alphas point values, TablesPre rd lp pi logMem alphas point values args ∧
    TablesOut bytecode TCtx rd pi logMem alphas point values args rets

/-- **`verify_tables`, placed.** -/
def CompleteTablesAt : Prop := CompleteRel fs cert k "verify_tables" (TablesPreOut bytecode TCtx)

/-- `verify_flock`'s precondition and outcome on a memory (`FlockOut`, `τ < 29`). -/
def FlockPre (rd : Reader) (args rets : List E) : Prop :=
  ∃ τ fs0 fs1 cur zchis lrs zpart, τ < 29 ∧ args = [fs0, fs1, cur, gen ^ τ, zchis, lrs, zpart] ∧
    FlockOut rd τ fs0 fs1 cur zchis lrs zpart rets

/-- **`verify_flock`, placed.** -/
def CompleteFlockAt : Prop := CompleteRel fs cert k "verify_flock" FlockPre

/-- `check_opening_terminal`'s precondition on a memory (`TermPre`) and the terminal's check. -/
def TermPreAcc (rd : Reader) (args rets : List E) : Prop :=
  rets = [] ∧ ∃ layout bus claims lam flockPoint coeffs w,
    TermPre TCtx PCtx rd layout bus claims lam flockPoint coeffs w args ∧
      w.Accepts (stackWeight layout claims flockPoint coeffs lam)

/-- **`check_opening_terminal`, placed.** -/
def CompleteTermAt : Prop := CompleteRel fs cert k "check_opening_terminal" (TermPreAcc TCtx PCtx)

/-- **`certify_placement`, placed**: on a layout holding the exponent tables at `lp`, `sq` and the
base `[1, g^log_mem, g^h_0, …]` at `kb`, it returns `g^(Σ 2^κ)` and two buffers, held by its `Lout`,
of which `PCtx` holds. -/
def CompletePlaceAt : Prop :=
  ∀ (lp sq kb : E) (logMem : ℕ) (hs : List ℕ) (Lin : Main.Layout), logMem ≤ 32 → hs.length = 6 →
    (∀ h ∈ hs, h < 29) →
    (∀ rd, LowDef k rd → MemL rd Lin →
      ExpTables rd lp sq ∧ ReadsAt rd kb (1 :: gen ^ logMem :: hs.map (gen ^ ·))) →
    CompleteAt fs cert k "certify_placement" Lin [kb, sq] fun rets Lout =>
      ∃ off kap, rets = [gen ^ stackTotal (columnKappas logMem 18 hs), off, kap] ∧
        ∀ rd, MemL rd Lout → PCtx rd (columnKappas logMem 18 hs) off kap

/-- **`open_stacked`, placed**, at every candidate, on an explicit run of `whirOpen μ r target`
from the state `cv` reading the words `xs` (held by `Lin` at `g^c`) and the openings `os`
(`CapOk`, group 4's agreement of the queries at the cap along the run): it returns `w`'s claim, the pointer to
its point buffer, its glued weight and its residual's value, the buffer (`w`'s point zero-padded to
`42`) its `Lout`. -/
def CompleteOpenAt (CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop) : Prop :=
  ∀ μ r, 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 →
    ∀ (root cv : Digest) (xs : List E) (os : List Opening) (w : WhirEnd) (cv' : Digest)
      (roots' : List (Digest × ℕ × ℕ)) (target : E) (c : ℕ) (Lin : Main.Layout),
      RunsWith (whirOpen μ r target) cv xs os [(root, stackShape μ r)] w cv' roots' →
      CapOk μ r root cv xs os target → (∀ rd, LowDef k rd → MemL rd Lin → ReadsAt rd (ofK (Parameters.gpow c)) xs) →
      CompleteAt fs cert k (openName μ r) Lin [(digestScalars cv).1, (digestScalars cv).2, target,
        (digestScalars root).1, (digestScalars root).2, ofK (Parameters.gpow c)] fun rets Lout =>
        ∃ b, rets = [w.target, ofK (Parameters.gpow b), w.inner, w.residual] ∧
          Lout = [(b, w.point ++ List.replicate (pointCap - w.point.length) 0)]

end Placed

end
end LeanVM.Guest.B1.VerifySub
