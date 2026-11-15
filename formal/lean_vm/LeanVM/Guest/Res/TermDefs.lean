/-
  LeanVM.Guest.Res.TermDefs

  `check_opening_terminal`'s residual families: what `verify_sub` hands it (`TermFront`), and the
  checks of its claims' low dimensions (F9) and `column_selector`'s lowest digit (F3).
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

`dimFacts`: function, base parameter, bound parameter, pairs `(k, c)`: the word at `[base]·g^k` is
`g^e`, the bound's `g^m`, `e + c ≤ m`; at `check_opening_terminal`, the pooled claims' `kappa_base`
sources and adjustments, the bus's against `g_bus_mu`, the tables' against `g_zc_n` (`busPairs`,
`tabPairs`). `dimB j w` (F9): the point `[T]·B·g^d` inside `[T]·g^i`, `i` below `[M]`'s exponent
plus `t ≥ 1`, `B` the word at `[K]·g^k` (or a product of it and a constant `g^c` the code writes),
`(k, c + d)` a pair of such a fact on `K`, `M`.

`csRes κ s d` (F3): `column_selector__L{κ}`'s read of its lowest digit `[d]`'s eq weight at
`[s]·[d]·g^(64(κ/4) + 16(w - 1))`, inside the strided level-`w` table, `w` the digit's width; `csB j`
names it at function `j`. `termFamB`: either.
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

/-- **A claim's low point inside its chain** (F9): `[T]·B·g^d` inside `[T]·g^i`, `i` below `[o] + t`,
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

/-- **The proof stream's readers and their callers**: `verify_keccak` called by `verify_sub`, the
two `keccak_layer` specializations by `verify_keccak`, each one's two loops by it, `verify_tables` by
`verify_sub` and its table sumcheck's two loops by it; and the roots' tree's arms by `da_verify`. -/
def stCallers : List (String × String) :=
  [(name% «verify_keccak», name% «verify_sub»), (name% «keccak_layer__L0», name% «verify_keccak»),
    (name% «keccak_layer__L1», name% «verify_keccak»),
    (name% «keccak_layer__L0_loop0», name% «keccak_layer__L0»),
    (name% «keccak_layer__L0_loop1», name% «keccak_layer__L0»),
    (name% «keccak_layer__L1_loop0», name% «keccak_layer__L1»),
    (name% «keccak_layer__L1_loop1», name% «keccak_layer__L1»), (name% «verify_tables», name% «verify_sub»),
    (name% «verify_tables_loop0», name% «verify_tables»), (name% «verify_tables_loop1», name% «verify_tables»),
    (name% «da_roots_tree__L0», name% «da_verify»), (name% «da_roots_tree__L1», name% «da_verify»),
    (name% «da_roots_tree__L2», name% «da_verify»), (name% «da_roots_tree__L3», name% «da_verify»),
    (name% «da_roots_tree__L4», name% «da_verify»), (name% «da_roots_tree__L5», name% «da_verify»),
    (name% «da_roots_tree__L6», name% «da_verify»), (name% «da_roots_tree__L7», name% «da_verify»),
    (name% «da_roots_tree__L8», name% «da_verify»), (name% «da_roots_tree__L9», name% «da_verify»),
    (name% «da_roots_tree__L10», name% «da_verify»)]

/-- **The callees whose facts are carried and their callers** (`Res.callersG`): `check_opening_terminal`
called by `verify_sub`, each `column_selector__L{κ}` by `check_opening_terminal`, and `stCallers`. -/
def termCallers : List (String × String) :=
  (name% «check_opening_terminal», name% «verify_sub») ::
    ((List.range 31).map fun κ ↦ (Tables.lName "column_selector" κ, name% «check_opening_terminal»)) ++
    stCallers

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

/-- **`check_opening_terminal`'s `sub` families**: F9 (`dimB`) and F3 (`csB`). -/
noncomputable def termFamB (j : ℕ) (w : Wit) (x : Mode.Res) : Bool := dimB j w x || csB j x

end

end LeanVM.Guest.Res
