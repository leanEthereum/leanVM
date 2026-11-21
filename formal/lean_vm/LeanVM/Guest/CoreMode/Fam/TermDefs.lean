/-
  LeanVM.Guest.CoreMode.Fam.TermDefs

  `check_opening_terminal`'s residual families: what `verify_sub` hands it (`TermFront`), and the
  checks of its claims' low dimensions.
-/

module

public import LeanVM.Guest.CoreMode.Fam.FamDefs
public import LeanVM.Guest.CoreMode.Fam.ParamRef
public import LeanVM.Guest.CoreMode.Gen.FnData
public import LeanVM.Guest.B1.Terminal.InterfaceP
public import LeanVM.Guest.B1.Selectors.ColumnSelector
import LeanVM.Guest.Data.Consts

/-!
# `check_opening_terminal`'s families

`TermFront rd args`: what `verify_sub`'s front (`B1.VerifySub.vs_front`) gives of
`check_opening_terminal`'s arguments, read by name: `kappa_base` reads `[1, g^log_mem, g^τ_0, …,
g^τ_5]`, `g_log_mem = g^log_mem`, `tau_keccak_g = g^τ_5`, the heights below `31`, `log_mem ≤ 30`;
`col_offsets` holds `certify_placement`'s offsets (`PCtx`, `KappasBelow`), the stack at most `2^30`;
`g_squares·g^34` the
selector's nibble shares; `verify_tables`' context (`TCtx`) on `[zeta, chi, rm, g_bus_mu, g_zc_n]`.

`dimFacts`: function, base parameter, bound parameter, pairs `(k, c)`: the word at `[base]·g^k` is
`g^e`, the bound's `g^m`, `e + c ≤ m` (`FnReg.dimFacts`; at `check_opening_terminal`, the pooled claims' `kappa_base`
sources and adjustments, its own data). `dimB j w`: the point `[T]·B·g^d` inside `[T]·g^i`, `i` below `[M]`'s exponent
plus `t ≥ 1`, `B` the word at `[K]·g^k` (or a product of it and a constant `g^c` the code writes),
`(k, c + d)` a pair of such a fact on `K`, `M`.
-/

namespace LeanVM.Guest.Res

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B2C (cellJ fsN)

@[expose] public section

/-! ## What `verify_sub` hands the terminal -/

/-- **What `verify_sub`'s front gives of `check_opening_terminal`'s arguments.** -/
def TermFront (rd : Reader) : List E → Prop
  | [gsq, zeta, chi, rm, gmu, gzcn, glm, gtau, kb, _lam, off, _zv, _ct, _pt, _pt1, _, _, _, _oz, gm] =>
      ∃ (logMem : ℕ) (hs : List ℕ) (layout : Layout) (bus : BusResult) (claims : List ColumnClaim),
        hs.length = 6 ∧ (∀ h ∈ hs, h < 31) ∧ logMem ≤ 30 ∧
        layout.logMemory = logMem ∧ layout.tableLogHeights = hs ∧ bus.point.length ≤ 40 ∧
        ReadsAt rd kb (1 :: gen ^ logMem :: hs.map (gen ^ ·)) ∧
        glm = gen ^ logMem ∧ gtau = gen ^ hs.getD 5 0 ∧
        Tables.PCtx rd (columnKappas logMem Tables.guestLogBytecode hs) off ∧
        Tables.KappasBelow (columnKappas logMem Tables.guestLogBytecode hs) ∧
        (stackOffsets (Tables.committedKappas (columnKappas logMem Tables.guestLogBytecode hs))).2 ≤ 30 ∧
        Tables.GTabsAt rd (gsq * gen ^ 34) ∧
        Tables.TCtx rd layout bus claims [zeta, chi, rm, gmu, gzcn] ∧ ∃ sl ≤ 30, gm = gen ^ sl
  | _ => False

/-! ## The claims' low dimensions -/

/-- **Dimension facts at listed parameters**: function, base parameter, bound parameter, pairs; each function's own
(`FnReg.dimFacts`: `check_opening_terminal`'s, `CoreMode/Fn/check_opening_terminal/Data.lean`). -/
abbrev dimFacts : List (String × ℕ × ℕ × List (ℕ × ℕ)) := CoreMode.FnReg.dimFacts

/-- The shape `dimB` reads: `[T]·B` and `[T]` up to `[o] + t`, as `(B, o, t)`. -/
def dimShape (a b : Mode.Rng) : Option (Mode.Base × ℕ × ℕ) :=
  match a.q.bs, b.q.bs, b.hi with
  | [(.fr T, 1), (B, 1)], [(.fr T', 1)], .ex (.fr o) t => if T = T' then some (B, o, t) else none
  | _, _, _ => none

/-- **Base `B` is the word at `[pk]·g^k` times `g^c`**, `ok k c`: `B` read there (`c = 0`), or a frame
cell a top-level product writes of a value a top-level load reads there and a constant `g^c`. -/
noncomputable def lowOk (j : ℕ) (w : Wit) (pk : V) (B : Mode.Base) (ok : ℕ → ℕ → Bool) : Bool :=
  match B with
  | .hp q k => inFr j q && cellJ j pk == q && ok k 0
  | .fr P => inFr j P && w.as.any fun
      | .mul P' y z => cellJ j P' == P && w.as.any fun
          | .load y' p k => decide (y' = y) && decide (p = pk) &&
              match (constOf w.as z).bind powOf with
              | some c => ok k c
              | none => false
          | _ => false
      | _ => false

/-- **A claim's low point inside its chain**: `[T]·B·g^d` inside `[T]·g^i`, `i` below `[o] + t`,
`B` the word at `[K]·g^k` times `g^c` (`lowOk`), `(k, c + d)` a pair of a dimension fact on the
parameters `K` and the one of cell `o`. -/
noncomputable def dimB (j : ℕ) (w : Wit) : Mode.Res → Bool
  | .sub a [b] => match dimShape a b with
    | some (B, o, t) =>
      a.lo == .num 0 && a.hi == .num 1 && a.d == 0 && b.lo == .num 0 && b.S == 1 && b.d == 0 &&
        a.q.fp == b.q.fp && decide (b.q.k ≤ a.q.k) && decide (1 ≤ t) && inFr j o &&
        dimFacts.any fun c ↦ c.1 == (coreOf j).name &&
          match (coreOf j).params[c.2.1]?, (coreOf j).params[c.2.2.1]? with
          | some pk, some pb => cellJ j pb == o &&
              lowOk j w pk B fun k c' ↦ c.2.2.2.contains (k, c' + (a.q.k - b.q.k))
          | _, _ => false
    | none => false
  | _ => false

/-! ## The callers -/

/-- **The callees whose facts are carried and their callers** (`Res.callersG`), each callee's own
(`FnReg.stCallers`). -/
abbrev termCallers : List (String × String) := CoreMode.FnReg.stCallers

/-- **The callees whose facts are carried and their callers** (`Res.callersM`), each callee's own
(`FnReg.glCallers`). -/
abbrev glCallers : List (String × List String) := CoreMode.FnReg.glCallers

end

end LeanVM.Guest.Res
