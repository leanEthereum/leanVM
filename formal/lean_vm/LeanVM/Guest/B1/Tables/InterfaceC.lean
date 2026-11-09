/-
  LeanVM.Guest.B1.Tables.InterfaceC

  B1-c's callee statements over a generic call relation `C` (the witness convention's amendment):
  `verify_bus_gkr`, `verify_tables` and `certify_placement` on `C`-calls, for any `C` below
  `coreProgram.Rel rd`.
-/

module

public import LeanVM.Guest.B1.Tables.Interface
public import LeanVM.Guest.B1.Gkr.Interface
public import LeanVM.Guest.CoreLemmas

/-!
# The callee statements over `C`

A caller's hypothesis on a callee quantifies over the calls of the caller's own relation `C`
(`/root/guest-design/WITNESS-CONVENTION.md`, "Amendment"). Each statement here is its `Rel`
statement with the call taken in `C`; none of them has a witness beyond the call's own words and
the memory, so each follows from its `Rel` form for every `C` with `CallRel.Le C (Rel rd)`
(`Tables.HoldsC`). `HypKappa` mentions no call and is unchanged.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `verify_bus_gkr_Spec` on `C`-calls. -/
def verify_bus_gkr_SpecC (rd : Reader) (C : CallRel) : Prop :=
  ∀ args rets, args.getD 6 0 ≠ 1 → C "verify_bus_gkr" args rets → GkrOut rd args rets

/-- `verify_tables_Spec` on `C`-calls. -/
def verify_tables_SpecC (bytecode : List K) (rd : Reader) (C : CallRel) : Prop :=
  ∀ pi logMem alphas point values args rets,
    TablesPre pi logMem alphas point values rd args →
    C "verify_tables" args rets → TablesOut bytecode pi logMem alphas point values rd args rets

/-- `certify_placement_Spec` on `C`-calls. -/
def certify_placement_SpecC (rd : Reader) (C : CallRel) : Prop :=
  ∀ (logMem : ℕ) (hs : List ℕ) (kb sq : E) (rets : List E), logMem ≤ 32 → hs.length = 6 →
    (∀ h ∈ hs, h < 29) → TbReadsAt rd kb (1 :: gen ^ logMem :: hs.map (gen ^ ·)) →
    TbReadsAt rd sq gSquaresList → TbReadsAt rd (sq * gen ^ 178) rankKeysList →
    C "certify_placement" [kb, sq] rets →
      ∃ off, rets = [gen ^ stackTotal (columnKappas logMem guestLogBytecode hs), off] ∧
        PCtx rd (columnKappas logMem guestLogBytecode hs) off

theorem verify_bus_gkr_SpecC_of {rd : Reader} {C : CallRel} (hle : CallRel.Le C (coreProgram.Rel rd))
    (h : verify_bus_gkr_Spec rd) : verify_bus_gkr_SpecC rd C :=
  fun args rets hne hc ↦ h args rets hne (hle _ _ _ hc)

theorem verify_tables_SpecC_of {bytecode : List K} {rd : Reader} {C : CallRel}
    (hle : CallRel.Le C (coreProgram.Rel rd)) (h : verify_tables_Spec bytecode rd) :
    verify_tables_SpecC bytecode rd C :=
  fun pi logMem alphas point values args rets hpre hc ↦
    h pi logMem alphas point values args rets hpre (hle _ _ _ hc)

theorem certify_placement_SpecC_of {rd : Reader} {C : CallRel}
    (hle : CallRel.Le C (coreProgram.Rel rd)) (h : certify_placement_Spec rd) :
    certify_placement_SpecC rd C :=
  fun logMem hs kb sq rets h1 h2 h3 h4 h5 h6 hc ↦ h logMem hs kb sq rets h1 h2 h3 h4 h5 h6 (hle _ _ _ hc)

end
end LeanVM.Guest.B1.Tables
