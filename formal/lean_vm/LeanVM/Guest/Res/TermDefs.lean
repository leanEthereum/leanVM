/-
  LeanVM.Guest.Res.TermDefs

  `check_opening_terminal`'s residual families: what `verify_sub` hands it (`TermFront`), the
  exponent facts carried at its parameters, and the checks of its order residuals (F7, F8), its
  claims' low dimensions (F9) and `column_selector`'s lowest digit (F3).
-/

module

public import LeanVM.Guest.Res.FamDefs
public import LeanVM.Guest.Res.ParamRef
public import LeanVM.Guest.B1.Terminal.InterfaceP
public import LeanVM.Guest.B1.Selectors.ColumnSelector
import LeanVM.Guest.Data.Source

/-!
# `check_opening_terminal`'s families

`TermFront rd args`: what `verify_sub`'s front (`B1.VerifySub.vs_front`) gives of
`check_opening_terminal`'s arguments, read by name: `kappa_base` reads `[1, g^log_mem, g^τ_0, …,
g^τ_5]`, `g_log_mem = g^log_mem`, `tau_keccak_g = g^τ_5`, the heights below `31`, `log_mem ≤ 30`;
`col_offsets` holds `certify_placement`'s offsets (`PCtx`, `KappasBelow`), the stack at most `2^30`;
`g_squares·g^34` the
selector's nibble shares; `verify_tables`' context (`TCtx`) on `[zeta, chi, rm, g_bus_mu, g_zc_n]`.

`expFacts`: function, parameter, offset, bound: the parameter's word (`none`), or the word read at
`[parameter]·g^k` (`some k`), is `g^e`, `e` below the bound. `ltExpB j w` (F7, F8): an order
residual `[B] + t < N` whose base `B` has such a fact, with bound `b`: `b + t ≤ N`, or a top-level
dispatch of at most `n` ways on `[B]·g^adj` (a product by a constant, or `B`'s word itself) with
`n + t ≤ N + adj`.

`dimFacts`: function, base parameter, bound parameter, pairs `(k, c)`: the word at `[base]·g^k` is
`g^e`, the bound's `g^m`, `e + c ≤ m`; at `check_opening_terminal`, the pooled claims' `kappa_base`
sources and adjustments, the bus's against `g_bus_mu`, the tables' against `g_zc_n` (`busPairs`,
`tabPairs`). `dimB j` (F9): the point `[T]·[[K]·g^k]·g^c` inside `[T]·g^i`, `i` below `[M]`'s
exponent plus `t ≥ 1`, `(k, c)` a pair of such a fact on `K`, `M`.

`csRes κ s d` (F3): `column_selector__L{κ}`'s read of its lowest digit `[d]`'s eq weight at
`[s]·[d]·g^(64(κ/4) + 16(w - 1))`, inside the strided level-`w` table, `w` the digit's width; `csB j`
names it at function `j`.
-/

namespace LeanVM.Guest.Res

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B2C (cellJ fsN)

@[expose] public section

/-! ## What `verify_sub` hands the terminal -/

/-- **What `verify_sub`'s front gives of `check_opening_terminal`'s arguments.** -/
def TermFront (rd : Reader) : List E → Prop
  | [gsq, zeta, chi, rm, gmu, gzcn, glm, gtau, kb, _lam, off, _zv, _ct, _pt, _pt1, _, _, _, _oz, _gm] =>
      ∃ (logMem : ℕ) (hs : List ℕ) (layout : Layout) (bus : BusResult) (claims : List ColumnClaim),
        hs.length = 6 ∧ (∀ h ∈ hs, h < 31) ∧ logMem ≤ 30 ∧
        layout.logMemory = logMem ∧ layout.tableLogHeights = hs ∧ bus.point.length ≤ 40 ∧
        ReadsAt rd kb (1 :: gen ^ logMem :: hs.map (gen ^ ·)) ∧
        glm = gen ^ logMem ∧ gtau = gen ^ hs.getD 5 0 ∧
        Tables.PCtx rd (columnKappas logMem Tables.guestLogBytecode hs) off ∧
        Tables.KappasBelow (columnKappas logMem Tables.guestLogBytecode hs) ∧
        (stackOffsets (Tables.committedKappas (columnKappas logMem Tables.guestLogBytecode hs))).2 ≤ 30 ∧
        Tables.GTabsAt rd (gsq * gen ^ 34) ∧
        Tables.TCtx rd layout bus claims [zeta, chi, rm, gmu, gzcn]
  | _ => False

/-! ## Exponent facts -/

/-- **Exponent facts at listed parameters**: function, parameter, offset (`none`: its word; `some k`:
the word read at `[parameter]·g^k`), bound. -/
def expFacts : List (String × ℕ × Option ℕ × ℕ) :=
  [(name% «check_opening_terminal», param% check_opening_terminal "tau_keccak_g", none, 31),
    (name% «check_opening_terminal», param% check_opening_terminal "kappa_base", some 0, 1)] ++
  (List.range 7).map fun k ↦
    (name% «check_opening_terminal», param% check_opening_terminal "kappa_base", some (k + 1), 31)

/-- Parameter `p`'s fact at offset `o` names base `B` of function `j`. -/
noncomputable def baseAt (j : ℕ) (p : V) : Option ℕ → Mode.Base → Bool
  | none, .fr c => cellJ j p == c
  | some k, .hp q k' => cellJ j p == q && k == k'
  | _, _ => false

/-- **A base's exponent fact**: the parameter and the bound of a listed fact naming it. -/
noncomputable def expOf (j : ℕ) (B : Mode.Base) : Option (V × ℕ) :=
  expFacts.findSome? fun c ↦
    if c.1 == (coreOf j).name then
      match (coreOf j).params[c.2.1]? with
      | some p => if baseAt j p c.2.2.1 B then some (p, c.2.2.2) else none
      | none => none
    else none

/-- The base's word `y`, read through parameter `p`: `p` itself, or a top-level load from `[p]·g^k`. -/
def readOf (w : Wit) (p : V) : Mode.Base → V → Bool
  | .fr _, y => decide (y = p)
  | .hp _ k, y => w.as.any fun
    | .load y' p' k' => decide (y' = y) && decide (p' = p) && k' == k
    | _ => false

/-- A top-level selector of at most `n` ways on `z`, `n + t ≤ N + adj`. -/
def selLe (w : Wit) (z : V) (t N adj : ℕ) : Bool :=
  w.ss.any fun s ↦ decide (s.1 = z) && decide (s.2 + t ≤ N + adj)

/-- `z` is dispatched on, a constant `c = g^adj` its factor, `adj < 2^33`. -/
noncomputable def constSel (w : Wit) (c z : V) (t N : ℕ) : Bool :=
  match (constOf w.as c).bind powOf with
  | some adj => decide (adj < 2 ^ 33) && selLe w z t N adj
  | none => false

/-- **A dispatch on the base's word times a constant**, or on the word itself. -/
noncomputable def prodSel (w : Wit) (p : V) (B : Mode.Base) (t N : ℕ) : Bool :=
  w.ss.any (fun s ↦ readOf w p B s.1 && decide (s.2 + t ≤ N)) ||
    w.as.any fun
      | .mul z a c => (readOf w p B a && constSel w c z t N) || (readOf w p B c && constSel w a z t N)
      | _ => false

/-- **An order residual bounded by an exponent fact** (F7, F8): `[B] + t < N`, `B` named by a fact of
bound `b`, `b + t ≤ N` or a dispatch bounding it (`prodSel`). -/
noncomputable def ltExpB (j : ℕ) (w : Wit) : Mode.Res → Bool
  | .lt (.ex B t) (.num N) => match expOf j B with
    | some (p, b) => inFr j (cellJ j p) && decide (b ≤ 2 ^ 33) && decide (N ≤ 2 ^ 33) &&
        (decide (b + t ≤ N) || prodSel w p B t N)
    | none => false
  | _ => false

/-! ## The claims' low dimensions -/

/-- The pooled claims' `kappa_base` sources and adjustments, bus claims first. -/
def claimPairs : List (ℕ × ℕ) :=
  (List.range Tables.nPooled).map fun j ↦ (Tables.claimKappaSrc.getD j 0, Tables.claimKappaAdj j)

/-- The bus claims' pairs: their points prefixes of the bus point. -/
def busPairs : List (ℕ × ℕ) := claimPairs.take Tables.nBusClaims

/-- The tables' claims' pairs: their points prefixes of the tables' point. -/
def tabPairs : List (ℕ × ℕ) := claimPairs.drop Tables.nBusClaims

/-- **Dimension facts at listed parameters**: function, base parameter, bound parameter, pairs. -/
def dimFacts : List (String × ℕ × ℕ × List (ℕ × ℕ)) :=
  [(name% «check_opening_terminal», param% check_opening_terminal "kappa_base",
      param% check_opening_terminal "g_bus_mu", busPairs),
    (name% «check_opening_terminal», param% check_opening_terminal "kappa_base",
      param% check_opening_terminal "g_zc_n", tabPairs)]

/-- The shape `dimB` reads: `[T]·[[q]·g^k]` and `[T]` up to `[o] + t`, as `(q, k, o, t)`. -/
def dimShape (a b : Mode.Rng) : Option (ℕ × ℕ × ℕ × ℕ) :=
  match a.q.bs, b.q.bs, b.hi with
  | [(.fr T, 1), (.hp q k, 1)], [(.fr T', 1)], .ex (.fr o) t => if T = T' then some (q, k, o, t) else none
  | _, _, _ => none

/-- **A claim's low point inside its chain** (F9): `[T]·[[q]·g^k]·g^c` inside `[T]·g^i`, `i` below
`[o] + t`, `(k, c)` a pair of a dimension fact on the parameters of cells `q`, `o`. -/
noncomputable def dimB (j : ℕ) : Mode.Res → Bool
  | .sub a [b] => match dimShape a b with
    | some (q, k, o, t) =>
      a.lo == .num 0 && a.hi == .num 1 && a.d == 0 && b.lo == .num 0 && b.S == 1 && b.d == 0 &&
        a.q.fp == b.q.fp && decide (b.q.k ≤ a.q.k) && decide (1 ≤ t) && inFr j q && inFr j o &&
        dimFacts.any fun c ↦ c.1 == (coreOf j).name &&
          match (coreOf j).params[c.2.1]?, (coreOf j).params[c.2.2.1]? with
          | some pk, some pb => cellJ j pk == q && cellJ j pb == o && c.2.2.2.contains (k, a.q.k - b.q.k)
          | _, _ => false
    | none => false
  | _ => false

/-! ## The callers -/

/-- **The terminal's callees and their callers**: `check_opening_terminal` called by `verify_sub`, each
`column_selector__L{κ}` by `check_opening_terminal` (`Res.callersG`). -/
def termCallers : List (String × String) :=
  (name% «check_opening_terminal», name% «verify_sub») ::
    (List.range 31).map fun κ ↦ (Tables.lName "column_selector" κ, name% «check_opening_terminal»)

/-! ## `column_selector`'s lowest digit -/

/-- **`column_selector__L{κ}`'s read of its lowest digit's eq weight**: `[s]·[d]·g^off` inside
`[s]·g^(2^(4 - w)·i + off)`, `i < 2^w`, `w` the digit's width, `off = 64(κ/4) + 16(w - 1)`. -/
def csRes (κ s d : ℕ) : Mode.Res :=
  let w := Tables.csW κ 0
  let off := 64 * (κ / 4) + 16 * (w - 1)
  .sub ⟨⟨0, off, Mode.insertBs (.fr d, 1) [(.fr s, 1)]⟩, .num 0, .num 1, 1, 0⟩
    [⟨⟨0, 0, [(.fr s, 1)]⟩, .num 0, .num (2 ^ w), 2 ^ (4 - w), off⟩]

/-- The `κ` whose `csRes` reads at offset `k`. -/
def csKappa (k : ℕ) : ℕ := 4 * (k / 64) + 3 - k % 64 / 16

/-- **The lowest digit's read at function `j`** (F3): `j` is `column_selector__L{κ}`, its `sel_eq` and
digit cells `s`, `d`, the digit's inside the frame. -/
noncomputable def csB (j : ℕ) : Mode.Res → Bool
  | .sub a [b] =>
    decide (csKappa a.q.k < 31) && (coreOf j).name == Tables.lName "column_selector" (csKappa a.q.k) &&
      inFr j (cellJ j (.n 3)) && decide (Mode.Res.sub a [b] = csRes (csKappa a.q.k) (cellJ j (.n 1)) (cellJ j (.n 3)))
  | _ => false

end

end LeanVM.Guest.Res
