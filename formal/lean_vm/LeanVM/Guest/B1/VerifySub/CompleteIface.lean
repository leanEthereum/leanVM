/-
  LeanVM.Guest.B1.VerifySub.CompleteIface

  `verify_sub`'s completeness interface: the run it completes on, the honest memory at the
  caller's `HeapBuf` pointers, and what completeness assumes of the callees groups 4 and 5 prove.
-/

module

public import LeanVM.Guest.B1.VerifySub.Body
public import LeanVM.Guest.B1.Uniform
public import LeanVM.Guest.B1.Main.WeightB

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
caller's words whose memories (defined below `2^k`) hold what it reads. A callee that runs a phase
of the verifier takes the run explicitly, before the memory, so that one run (and the callee's
honest buffers, which depend on it) serves every memory: `verify_bus_gkr`, `verify_tables`,
`verify_flock` and `check_opening_terminal` return fixed words, `certify_placement` and
`open_stacked` return `HeapBuf`s, their contents in the layout `Lout` they return. -/

section Placed

open LeanVM.Guest.B1.Main (MemL)

variable (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (bytecode : List K)
  (TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop)
  (PCtx : Reader → List ℕ → E → E → Prop)

/-- **`verify_bus_gkr`, placed**, on an explicit run of `gkrPhase depth` from the state of `cv`
reading the words `xs` (at `g^c`), its point at `g^z`. -/
def CompleteGkrAt : Prop :=
  ∀ (cv : Digest) (depth : ℕ) (xs : List E) (r : E × List E × List E) (cv' : Digest) (c z : ℕ)
    (Lin : Main.Layout), depth < 33 → RunsTo (gkrPhase depth) cv xs r cv' → r.2.1.length = depth →
    r.2.2.length = 3 →
    (∀ rd, LowDef k rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow c)) xs ∧ ReadsAt rd (ofK (Parameters.gpow z)) r.2.1) →
    CompleteAtD fs cert k "verify_bus_gkr" Lin [(digestScalars cv).1, (digestScalars cv).2,
      ofK (Parameters.gpow c), gen ^ depth, ofK (Parameters.gpow z)]
      (Returns ([(digestScalars cv').1, (digestScalars cv').2,
        ofK (Parameters.gpow c) * gen ^ xs.length] ++ r.2.2))

/-- **`verify_tables`, placed**, on an explicit run of `tablesSeg` (for every `ev` taking `bv` for
the bytecode) from the state of `cv` reading the words `xs` (at `g^c`) to the bus result and the
claims, the row counts `rowsN`: on the words its arguments point to (`TablesPre`'s and
`TablesOut`'s reads, the terminal's context `TCtx` among them), it returns the new state, the
cursor past `xs`, `gzcn` (`g` to the tables' largest log-height), `bv` and `rm`. -/
def CompleteTablesAt : Prop :=
  ∀ (pi : Digest) (logMem : ℕ) (alphas point values : List E) (cv : Digest) (xs : List E)
    (cv' : Digest) (rowsN : List ℕ) (bus : BusResult) (claims : List ColumnClaim)
    (beta bv rm gzcn : E) (c z lp sq dims rows bk fpw pool cplen chi : ℕ) (Lin : Main.Layout),
    bytecode.length = 2 ^ 22 →
    point.length = (busLayout [0, logMem, 18] (layoutOf bytecode logMem rowsN).push).depth →
    point.length < 33 → gzcn = gen ^ (layoutOf bytecode logMem rowsN).tableLogHeights.foldl max 0 →
    16 ≤ logMem → logMem ≤ 32 → alphas.length = 4 → values.length = 3 →
    rowsN.length = 6 → (∀ n ∈ rowsN, log2Ceil n < 29) → claims.length = nClaims →
    (∀ ev, BytecodeAt ev bytecode
        (point.take (layoutOf bytecode logMem rowsN).logBytecode ++ alphas) bv →
      RunsTo (tablesSeg ev (layoutOf bytecode logMem rowsN) pi alphas beta point values) cv xs
        (bus, claims) cv') →
    (∀ rd, LowDef k rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow c)) xs ∧ ReadsAt rd (ofK (Parameters.gpow z)) point ∧
      ExpTables rd (ofK (Parameters.gpow lp)) (ofK (Parameters.gpow sq)) ∧
      ReadsAt rd (ofK (Parameters.gpow rows)) (rowsN.map eOfNat) ∧
      ReadsAt rd (ofK (Parameters.gpow dims)) (gen ^ logMem :: rowsN.map fun n ↦ gen ^ log2Ceil n) ∧
      ReadsAt rd (ofK (Parameters.gpow bk))
        (blockKappas (gen ^ logMem) (rowsN.map fun n ↦ gen ^ log2Ceil n)) ∧
      ReadsAt rd (ofK (Parameters.gpow fpw)) (eqKernel alphas) ∧
      ReadsAt rd (ofK (Parameters.gpow pool)) (claims.map (·.value)) ∧
      TCtx rd (layoutOf bytecode logMem rowsN) bus claims [ofK (Parameters.gpow z),
        ofK (Parameters.gpow chi), rm, gen ^ point.length, gzcn, ofK (Parameters.gpow cplen)]) →
    CompleteAtD fs cert k "verify_tables" Lin
      [(digestScalars cv).1, (digestScalars cv).2, ofK (Parameters.gpow c), (digestScalars pi).1,
        (digestScalars pi).2, ofK (Parameters.gpow z), gen ^ point.length,
        ofK (Parameters.gpow dims), ofK (Parameters.gpow rows), ofK (Parameters.gpow bk),
        ofK (Parameters.gpow sq), ofK (Parameters.gpow fpw), beta, ofK (Parameters.gpow pool),
        ofK (Parameters.gpow cplen), ofK (Parameters.gpow chi), values.getD 0 0, values.getD 1 0,
        values.getD 2 0]
      (Returns [(digestScalars cv').1, (digestScalars cv').2,
        ofK (Parameters.gpow c) * gen ^ xs.length, gzcn, bv, rm])

/-- **`verify_flock`, placed**, on an explicit run of `verifyFlock` (for every `ev` with the
matrices' values) from the state of `cv` reading the words `xs` (at `g^c`), its outputs `chi`,
`rcs`, `s` at `g^zc`, `g^lr`, `g^zp`. -/
def CompleteFlockAt : Prop :=
  ∀ (τ : ℕ) (cv : Digest) (xs : List E) (cv' : Digest) (zSkip alpha mv : E) (chi rcs s : List E)
    (c zc lr zp : ℕ) (Lin : Main.Layout), τ < 29 → chi.length = 8 + τ → rcs.length = 8 →
    s.length = 64 →
    (∀ ev, MatricesAt ev alpha zSkip (chi.take 8) rcs.reverse s mv →
      RunsTo (verifyFlock ev (blake2sR1csLogSize + τ)) cv xs (rcs.reverse ++ chi.drop 8, s) cv') →
    (∀ rd, LowDef k rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow c)) xs ∧ ReadsAt rd (ofK (Parameters.gpow zc)) chi ∧
      ReadsAt rd (ofK (Parameters.gpow lr)) rcs ∧ ReadsAt rd (ofK (Parameters.gpow zp)) s) →
    CompleteAtD fs cert k "verify_flock" Lin [(digestScalars cv).1, (digestScalars cv).2,
      ofK (Parameters.gpow c), gen ^ τ, ofK (Parameters.gpow zc), ofK (Parameters.gpow lr),
      ofK (Parameters.gpow zp)]
      (Returns [(digestScalars cv').1, (digestScalars cv').2,
        ofK (Parameters.gpow c) * gen ^ xs.length, zSkip, alpha, mv])

/-- **`check_opening_terminal`, placed**, for an explicit layout, claims and opening's end that
the terminal's check accepts, each claim's point of its column's length, and the tables' sumcheck
point `chis` (its length in `args[4]`), on the words `TermPre` reads and `chis` at `args[1]`. -/
def CompleteTermAt : Prop :=
  ∀ (layout : Layout) (bus : BusResult) (claims : List ColumnClaim) (lam : E)
    (flockPoint coeffs : List E) (w : WhirEnd) (chis : List E) (args : List E) (Lin : Main.Layout),
    w.Accepts (stackWeight layout claims flockPoint coeffs lam) →
    (∀ c ∈ claims, c.point.length = (layout.placements.getD c.column default).vars) →
    args.getD 4 0 = gen ^ chis.length →
    (∀ rd, LowDef k rd → MemL rd Lin →
      TermPre TCtx PCtx rd layout bus claims lam flockPoint coeffs w args ∧
        ReadsAt rd (args.getD 1 0) chis) →
    CompleteAtD fs cert k "check_opening_terminal" Lin args (Returns [])

/-- **`certify_placement`, placed**: on a layout holding the exponent tables at `lp`, `sq` and the
base `[1, g^log_mem, g^h_0, …]` at `kb`, it returns `g^(Σ 2^κ)` and two buffers, held by its `Lout`,
of which `PCtx` holds. -/
def CompletePlaceAt : Prop :=
  ∀ (lp sq kb : E) (logMem : ℕ) (hs : List ℕ) (Lin : Main.Layout), logMem ≤ 32 → hs.length = 6 →
    (∀ h ∈ hs, h < 29) → hs.getD 5 0 + 8 < 34 →
    (∀ rd, LowDef k rd → MemL rd Lin →
      ExpTables rd lp sq ∧ ReadsAt rd kb (1 :: gen ^ logMem :: hs.map (gen ^ ·))) →
    CompleteAtD fs cert k "certify_placement" Lin [kb, sq] fun rets Lout =>
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
      CompleteAtD fs cert k (openName μ r) Lin [(digestScalars cv).1, (digestScalars cv).2, target,
        (digestScalars root).1, (digestScalars root).2, ofK (Parameters.gpow c)] fun rets Lout =>
        ∃ b, rets = [w.target, ofK (Parameters.gpow b), w.inner, w.residual] ∧
          Lout = [(b, w.point ++ List.replicate (pointCap - w.point.length) 0)]

/-! ### Bounded: the same shapes by trees of at most `B` words (`CompleteAtB`) -/

/-- **`verify_bus_gkr`, placed, bounded**, on an explicit run of `gkrPhase depth` from the state of `cv`
reading the words `xs` (at `g^c`), its point at `g^z`. -/
def CompleteGkrAtB (B : ℕ) : Prop :=
  ∀ (cv : Digest) (depth : ℕ) (xs : List E) (r : E × List E × List E) (cv' : Digest) (c z : ℕ)
    (Lin : Main.Layout), depth < 33 → RunsTo (gkrPhase depth) cv xs r cv' → r.2.1.length = depth →
    r.2.2.length = 3 →
    (∀ rd, LowDef k rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow c)) xs ∧ ReadsAt rd (ofK (Parameters.gpow z)) r.2.1) →
    CompleteAtB fs cert k "verify_bus_gkr" Lin [(digestScalars cv).1, (digestScalars cv).2,
      ofK (Parameters.gpow c), gen ^ depth, ofK (Parameters.gpow z)]
      (Returns ([(digestScalars cv').1, (digestScalars cv').2,
        ofK (Parameters.gpow c) * gen ^ xs.length] ++ r.2.2)) B

/-- **`verify_tables`, placed**, on an explicit run of `tablesSeg` (for every `ev` taking `bv` for
the bytecode) from the state of `cv` reading the words `xs` (at `g^c`) to the bus result and the
claims, the row counts `rowsN`: on the words its arguments point to (`TablesPre`'s and
`TablesOut`'s reads, the terminal's context `TCtx` among them), it returns the new state, the
cursor past `xs`, `gzcn` (`g` to the tables' largest log-height), `bv` and `rm`. -/
def CompleteTablesAtB (B : ℕ) : Prop :=
  ∀ (pi : Digest) (logMem : ℕ) (alphas point values : List E) (cv : Digest) (xs : List E)
    (cv' : Digest) (rowsN : List ℕ) (bus : BusResult) (claims : List ColumnClaim)
    (beta bv rm gzcn : E) (c z lp sq dims rows bk fpw pool cplen chi : ℕ) (Lin : Main.Layout),
    bytecode.length = 2 ^ 22 →
    point.length = (busLayout [0, logMem, 18] (layoutOf bytecode logMem rowsN).push).depth →
    point.length < 33 → gzcn = gen ^ (layoutOf bytecode logMem rowsN).tableLogHeights.foldl max 0 →
    16 ≤ logMem → logMem ≤ 32 → alphas.length = 4 → values.length = 3 →
    rowsN.length = 6 → (∀ n ∈ rowsN, log2Ceil n < 29) → claims.length = nClaims →
    (∀ ev, BytecodeAt ev bytecode
        (point.take (layoutOf bytecode logMem rowsN).logBytecode ++ alphas) bv →
      RunsTo (tablesSeg ev (layoutOf bytecode logMem rowsN) pi alphas beta point values) cv xs
        (bus, claims) cv') →
    (∀ rd, LowDef k rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow c)) xs ∧ ReadsAt rd (ofK (Parameters.gpow z)) point ∧
      ExpTables rd (ofK (Parameters.gpow lp)) (ofK (Parameters.gpow sq)) ∧
      ReadsAt rd (ofK (Parameters.gpow rows)) (rowsN.map eOfNat) ∧
      ReadsAt rd (ofK (Parameters.gpow dims)) (gen ^ logMem :: rowsN.map fun n ↦ gen ^ log2Ceil n) ∧
      ReadsAt rd (ofK (Parameters.gpow bk))
        (blockKappas (gen ^ logMem) (rowsN.map fun n ↦ gen ^ log2Ceil n)) ∧
      ReadsAt rd (ofK (Parameters.gpow fpw)) (eqKernel alphas) ∧
      ReadsAt rd (ofK (Parameters.gpow pool)) (claims.map (·.value)) ∧
      TCtx rd (layoutOf bytecode logMem rowsN) bus claims [ofK (Parameters.gpow z),
        ofK (Parameters.gpow chi), rm, gen ^ point.length, gzcn, ofK (Parameters.gpow cplen)]) →
    CompleteAtB fs cert k "verify_tables" Lin
      [(digestScalars cv).1, (digestScalars cv).2, ofK (Parameters.gpow c), (digestScalars pi).1,
        (digestScalars pi).2, ofK (Parameters.gpow z), gen ^ point.length,
        ofK (Parameters.gpow dims), ofK (Parameters.gpow rows), ofK (Parameters.gpow bk),
        ofK (Parameters.gpow sq), ofK (Parameters.gpow fpw), beta, ofK (Parameters.gpow pool),
        ofK (Parameters.gpow cplen), ofK (Parameters.gpow chi), values.getD 0 0, values.getD 1 0,
        values.getD 2 0]
      (Returns [(digestScalars cv').1, (digestScalars cv').2,
        ofK (Parameters.gpow c) * gen ^ xs.length, gzcn, bv, rm]) B

/-- **`verify_flock`, placed**, on an explicit run of `verifyFlock` (for every `ev` with the
matrices' values) from the state of `cv` reading the words `xs` (at `g^c`), its outputs `chi`,
`rcs`, `s` at `g^zc`, `g^lr`, `g^zp`. -/
def CompleteFlockAtB (B : ℕ) : Prop :=
  ∀ (τ : ℕ) (cv : Digest) (xs : List E) (cv' : Digest) (zSkip alpha mv : E) (chi rcs s : List E)
    (c zc lr zp : ℕ) (Lin : Main.Layout), τ < 29 → chi.length = 8 + τ → rcs.length = 8 →
    s.length = 64 →
    (∀ ev, MatricesAt ev alpha zSkip (chi.take 8) rcs.reverse s mv →
      RunsTo (verifyFlock ev (blake2sR1csLogSize + τ)) cv xs (rcs.reverse ++ chi.drop 8, s) cv') →
    (∀ rd, LowDef k rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow c)) xs ∧ ReadsAt rd (ofK (Parameters.gpow zc)) chi ∧
      ReadsAt rd (ofK (Parameters.gpow lr)) rcs ∧ ReadsAt rd (ofK (Parameters.gpow zp)) s) →
    CompleteAtB fs cert k "verify_flock" Lin [(digestScalars cv).1, (digestScalars cv).2,
      ofK (Parameters.gpow c), gen ^ τ, ofK (Parameters.gpow zc), ofK (Parameters.gpow lr),
      ofK (Parameters.gpow zp)]
      (Returns [(digestScalars cv').1, (digestScalars cv').2,
        ofK (Parameters.gpow c) * gen ^ xs.length, zSkip, alpha, mv]) B

/-- **`check_opening_terminal`, placed**, for an explicit layout, claims and opening's end that
the terminal's check accepts, each claim's point of its column's length, and the tables' sumcheck
point `chis` (its length in `args[4]`), on the words `TermPre` reads and `chis` at `args[1]`. -/
def CompleteTermAtB (B : ℕ) : Prop :=
  ∀ (layout : Layout) (bus : BusResult) (claims : List ColumnClaim) (lam : E)
    (flockPoint coeffs : List E) (w : WhirEnd) (chis : List E) (args : List E) (Lin : Main.Layout),
    w.Accepts (stackWeight layout claims flockPoint coeffs lam) →
    (∀ c ∈ claims, c.point.length = (layout.placements.getD c.column default).vars) →
    args.getD 4 0 = gen ^ chis.length →
    (∀ rd, LowDef k rd → MemL rd Lin →
      TermPre TCtx PCtx rd layout bus claims lam flockPoint coeffs w args ∧
        ReadsAt rd (args.getD 1 0) chis) →
    CompleteAtB fs cert k "check_opening_terminal" Lin args (Returns []) B

/-- **`certify_placement`, placed**: on a layout holding the exponent tables at `lp`, `sq` and the
base `[1, g^log_mem, g^h_0, …]` at `kb`, it returns `g^(Σ 2^κ)` and two buffers, held by its `Lout`,
of which `PCtx` holds. -/
def CompletePlaceAtB (B : ℕ) : Prop :=
  ∀ (lp sq kb : E) (logMem : ℕ) (hs : List ℕ) (Lin : Main.Layout), logMem ≤ 32 → hs.length = 6 →
    (∀ h ∈ hs, h < 29) → hs.getD 5 0 + 8 < 34 →
    (∀ rd, LowDef k rd → MemL rd Lin →
      ExpTables rd lp sq ∧ ReadsAt rd kb (1 :: gen ^ logMem :: hs.map (gen ^ ·))) →
    CompleteAtB fs cert k "certify_placement" Lin [kb, sq] (fun rets Lout =>
      ∃ off kap, rets = [gen ^ stackTotal (columnKappas logMem 18 hs), off, kap] ∧
        ∀ rd, MemL rd Lout → PCtx rd (columnKappas logMem 18 hs) off kap) B

/-- **`open_stacked`, placed**, at every candidate, on an explicit run of `whirOpen μ r target`
from the state `cv` reading the words `xs` (held by `Lin` at `g^c`) and the openings `os`
(`CapOk`, group 4's agreement of the queries at the cap along the run): it returns `w`'s claim, the pointer to
its point buffer, its glued weight and its residual's value, the buffer (`w`'s point zero-padded to
`42`) its `Lout`. -/
def CompleteOpenAtB (CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop)
    (B : ℕ) : Prop :=
  ∀ μ r, 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 →
    ∀ (root cv : Digest) (xs : List E) (os : List Opening) (w : WhirEnd) (cv' : Digest)
      (roots' : List (Digest × ℕ × ℕ)) (target : E) (c : ℕ) (Lin : Main.Layout),
      RunsWith (whirOpen μ r target) cv xs os [(root, stackShape μ r)] w cv' roots' →
      CapOk μ r root cv xs os target → (∀ rd, LowDef k rd → MemL rd Lin → ReadsAt rd (ofK (Parameters.gpow c)) xs) →
      CompleteAtB fs cert k (openName μ r) Lin [(digestScalars cv).1, (digestScalars cv).2, target,
        (digestScalars root).1, (digestScalars root).2, ofK (Parameters.gpow c)] (fun rets Lout =>
        ∃ b, rets = [w.target, ofK (Parameters.gpow b), w.inner, w.residual] ∧
          Lout = [(b, w.point ++ List.replicate (pointCap - w.point.length) 0)]) B


/-! ### Within weights: the same shapes by trees weighing at most `Bw θ` at `wt θ` (`CompleteAtW`) -/

section Weights

variable {Θ : Type} (wt : Θ → String → ℕ)

/-- `CompleteGkrAtB` within weights. -/
def CompleteGkrAtW (B : ℕ) (Bw : Θ → ℕ) : Prop :=
  ∀ (cv : Digest) (depth : ℕ) (xs : List E) (r : E × List E × List E) (cv' : Digest) (c z : ℕ)
    (Lin : Main.Layout), depth < 33 → RunsTo (gkrPhase depth) cv xs r cv' → r.2.1.length = depth →
    r.2.2.length = 3 →
    (∀ rd, LowDef k rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow c)) xs ∧ ReadsAt rd (ofK (Parameters.gpow z)) r.2.1) →
    Main.CompleteAtW fs cert wt k "verify_bus_gkr" Lin [(digestScalars cv).1, (digestScalars cv).2,
      ofK (Parameters.gpow c), gen ^ depth, ofK (Parameters.gpow z)]
      (Returns ([(digestScalars cv').1, (digestScalars cv').2,
        ofK (Parameters.gpow c) * gen ^ xs.length] ++ r.2.2)) B Bw

theorem CompleteGkrAtW.toB {B : ℕ} {Bw : Θ → ℕ} (h : CompleteGkrAtW fs cert k wt B Bw) :
    CompleteGkrAtB fs cert k B := by
  unfold CompleteGkrAtW at h
  unfold CompleteGkrAtB
  intros
  exact Main.CompleteAtW.toB (by apply h <;> assumption)

/-- `CompleteTablesAtB` within weights. -/
def CompleteTablesAtW (B : ℕ) (Bw : Θ → ℕ) : Prop :=
  ∀ (pi : Digest) (logMem : ℕ) (alphas point values : List E) (cv : Digest) (xs : List E)
    (cv' : Digest) (rowsN : List ℕ) (bus : BusResult) (claims : List ColumnClaim)
    (beta bv rm gzcn : E) (c z lp sq dims rows bk fpw pool cplen chi : ℕ) (Lin : Main.Layout),
    bytecode.length = 2 ^ 22 →
    point.length = (busLayout [0, logMem, 18] (layoutOf bytecode logMem rowsN).push).depth →
    point.length < 33 → gzcn = gen ^ (layoutOf bytecode logMem rowsN).tableLogHeights.foldl max 0 →
    16 ≤ logMem → logMem ≤ 32 → alphas.length = 4 → values.length = 3 →
    rowsN.length = 6 → (∀ n ∈ rowsN, log2Ceil n < 29) → claims.length = nClaims →
    (∀ ev, BytecodeAt ev bytecode
        (point.take (layoutOf bytecode logMem rowsN).logBytecode ++ alphas) bv →
      RunsTo (tablesSeg ev (layoutOf bytecode logMem rowsN) pi alphas beta point values) cv xs
        (bus, claims) cv') →
    (∀ rd, LowDef k rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow c)) xs ∧ ReadsAt rd (ofK (Parameters.gpow z)) point ∧
      ExpTables rd (ofK (Parameters.gpow lp)) (ofK (Parameters.gpow sq)) ∧
      ReadsAt rd (ofK (Parameters.gpow rows)) (rowsN.map eOfNat) ∧
      ReadsAt rd (ofK (Parameters.gpow dims)) (gen ^ logMem :: rowsN.map fun n ↦ gen ^ log2Ceil n) ∧
      ReadsAt rd (ofK (Parameters.gpow bk))
        (blockKappas (gen ^ logMem) (rowsN.map fun n ↦ gen ^ log2Ceil n)) ∧
      ReadsAt rd (ofK (Parameters.gpow fpw)) (eqKernel alphas) ∧
      ReadsAt rd (ofK (Parameters.gpow pool)) (claims.map (·.value)) ∧
      TCtx rd (layoutOf bytecode logMem rowsN) bus claims [ofK (Parameters.gpow z),
        ofK (Parameters.gpow chi), rm, gen ^ point.length, gzcn, ofK (Parameters.gpow cplen)]) →
    Main.CompleteAtW fs cert wt k "verify_tables" Lin
      [(digestScalars cv).1, (digestScalars cv).2, ofK (Parameters.gpow c), (digestScalars pi).1,
        (digestScalars pi).2, ofK (Parameters.gpow z), gen ^ point.length,
        ofK (Parameters.gpow dims), ofK (Parameters.gpow rows), ofK (Parameters.gpow bk),
        ofK (Parameters.gpow sq), ofK (Parameters.gpow fpw), beta, ofK (Parameters.gpow pool),
        ofK (Parameters.gpow cplen), ofK (Parameters.gpow chi), values.getD 0 0, values.getD 1 0,
        values.getD 2 0]
      (Returns [(digestScalars cv').1, (digestScalars cv').2,
        ofK (Parameters.gpow c) * gen ^ xs.length, gzcn, bv, rm]) B Bw

theorem CompleteTablesAtW.toB {B : ℕ} {Bw : Θ → ℕ} (h : CompleteTablesAtW fs cert k bytecode TCtx wt B Bw) :
    CompleteTablesAtB fs cert k bytecode TCtx B := by
  unfold CompleteTablesAtW at h
  unfold CompleteTablesAtB
  intros
  exact Main.CompleteAtW.toB (by apply h <;> assumption)

/-- `CompleteFlockAtB` within weights. -/
def CompleteFlockAtW (B : ℕ) (Bw : Θ → ℕ) : Prop :=
  ∀ (τ : ℕ) (cv : Digest) (xs : List E) (cv' : Digest) (zSkip alpha mv : E) (chi rcs s : List E)
    (c zc lr zp : ℕ) (Lin : Main.Layout), τ < 29 → chi.length = 8 + τ → rcs.length = 8 →
    s.length = 64 →
    (∀ ev, MatricesAt ev alpha zSkip (chi.take 8) rcs.reverse s mv →
      RunsTo (verifyFlock ev (blake2sR1csLogSize + τ)) cv xs (rcs.reverse ++ chi.drop 8, s) cv') →
    (∀ rd, LowDef k rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow c)) xs ∧ ReadsAt rd (ofK (Parameters.gpow zc)) chi ∧
      ReadsAt rd (ofK (Parameters.gpow lr)) rcs ∧ ReadsAt rd (ofK (Parameters.gpow zp)) s) →
    Main.CompleteAtW fs cert wt k "verify_flock" Lin [(digestScalars cv).1, (digestScalars cv).2,
      ofK (Parameters.gpow c), gen ^ τ, ofK (Parameters.gpow zc), ofK (Parameters.gpow lr),
      ofK (Parameters.gpow zp)]
      (Returns [(digestScalars cv').1, (digestScalars cv').2,
        ofK (Parameters.gpow c) * gen ^ xs.length, zSkip, alpha, mv]) B Bw

theorem CompleteFlockAtW.toB {B : ℕ} {Bw : Θ → ℕ} (h : CompleteFlockAtW fs cert k wt B Bw) :
    CompleteFlockAtB fs cert k B := by
  unfold CompleteFlockAtW at h
  unfold CompleteFlockAtB
  intros
  exact Main.CompleteAtW.toB (by apply h <;> assumption)

/-- `CompleteTermAtB` within weights. -/
def CompleteTermAtW (B : ℕ) (Bw : Θ → ℕ) : Prop :=
  ∀ (layout : Layout) (bus : BusResult) (claims : List ColumnClaim) (lam : E)
    (flockPoint coeffs : List E) (w : WhirEnd) (chis : List E) (args : List E) (Lin : Main.Layout),
    w.Accepts (stackWeight layout claims flockPoint coeffs lam) →
    (∀ c ∈ claims, c.point.length = (layout.placements.getD c.column default).vars) →
    args.getD 4 0 = gen ^ chis.length →
    (∀ rd, LowDef k rd → MemL rd Lin →
      TermPre TCtx PCtx rd layout bus claims lam flockPoint coeffs w args ∧
        ReadsAt rd (args.getD 1 0) chis) →
    Main.CompleteAtW fs cert wt k "check_opening_terminal" Lin args (Returns []) B Bw

theorem CompleteTermAtW.toB {B : ℕ} {Bw : Θ → ℕ} (h : CompleteTermAtW fs cert k TCtx PCtx wt B Bw) :
    CompleteTermAtB fs cert k TCtx PCtx B := by
  unfold CompleteTermAtW at h
  unfold CompleteTermAtB
  intros
  exact Main.CompleteAtW.toB (by apply h <;> assumption)
theorem CompleteGkrAtB.toWE {wt : Empty → String → ℕ} {B : ℕ} {Bw : Empty → ℕ}
    (h : CompleteGkrAtB fs cert k B) : CompleteGkrAtW fs cert k wt B Bw := by
  unfold CompleteGkrAtB at h
  unfold CompleteGkrAtW
  intros
  exact Main.CompleteAtB.toWE (by apply h <;> assumption)

theorem CompleteTablesAtB.toWE {wt : Empty → String → ℕ} {B : ℕ} {Bw : Empty → ℕ}
    (h : CompleteTablesAtB fs cert k bytecode TCtx B) : CompleteTablesAtW fs cert k bytecode TCtx wt B Bw := by
  unfold CompleteTablesAtB at h
  unfold CompleteTablesAtW
  intros
  exact Main.CompleteAtB.toWE (by apply h <;> assumption)

theorem CompleteFlockAtB.toWE {wt : Empty → String → ℕ} {B : ℕ} {Bw : Empty → ℕ}
    (h : CompleteFlockAtB fs cert k B) : CompleteFlockAtW fs cert k wt B Bw := by
  unfold CompleteFlockAtB at h
  unfold CompleteFlockAtW
  intros
  exact Main.CompleteAtB.toWE (by apply h <;> assumption)

theorem CompleteTermAtB.toWE {wt : Empty → String → ℕ} {B : ℕ} {Bw : Empty → ℕ}
    (h : CompleteTermAtB fs cert k TCtx PCtx B) : CompleteTermAtW fs cert k TCtx PCtx wt B Bw := by
  unfold CompleteTermAtB at h
  unfold CompleteTermAtW
  intros
  exact Main.CompleteAtB.toWE (by apply h <;> assumption)

end Weights

end Placed

end
end LeanVM.Guest.B1.VerifySub
