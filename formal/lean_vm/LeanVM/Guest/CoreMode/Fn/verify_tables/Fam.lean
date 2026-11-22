/-
  LeanVM.Guest.CoreMode.Fn.verify_tables.Fam

  `verify_tables`'s own residual families (`CoreMode/FnReg.lean`): its reads past its table sumcheck, its buffers through its hinted order, its exponent family.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **`verify_tables`' reads past its table sumcheck's last record's cursor** (`vtSt`, `Res.vtStB` on
core names): the cell `c` words past the cursor, the value `cursor@5`, `c < 153`, one of its stream's, parameter `stream`'s
`[0, 8192)` (`EndExec.vtStC_inst`). -/
def vtStC (fn : Fn) : CRes → Bool
  | .sub c q => fn.name == name% «verify_tables» && decide (c.bases = [(val% «verify_tables» "cursor@5", 1)]) && decide (c.off < 153) &&
      decide (q = ⟨⟨[(val% «verify_tables» "stream", 1)], 0⟩, 1, .num 0, .num 8192⟩)
  | _ => false

/-- `verify_tables`' rank `r`'s group value from the side's first `v0`, by its sort's template (`B1.Tables.vtRv`). -/
def vtRvC (v0 r : ℕ) : ℕ := if r = 0 then v0 else v0 + 13 + 20 * (r - 1)

/-- **`verify_tables`' sides**: each side's ranks' group values (from `gi@1`, `gi@10`) and the side's groups
`[lo, hi)`. -/
def vtSides : List (List ℕ × ℕ × ℕ) :=
  [((List.range 9).map (vtRvC (val% «verify_tables» "gi@1")), 0, 9),
    ((List.range 6).map (vtRvC (val% «verify_tables» "gi@10")), 18, 24)]

/-- **`verify_tables`' buffers indexed by group, through its hinted order** (`vtPerm`, `Res.vtGrpB` on
core names): a cell `[B]·[v]` at a rank's group value `v` is one of `[B]·g^e` over the side's groups (each rank's group
is one of the side's), and a cell `[B]·g^e` at a group of the side is one of `[B]·[v]` over its ranks' values (the
ranks name every group of the side) (`EndExec.vtPerm_inst`). -/
def vtPerm (fn : Fn) : CRes → Bool
  | .subP c cs => fn.name == name% «verify_tables» && vtSides.any fun p ↦ match c.bases with
      | [(B, 1), (v, 1)] => Nat.beq c.off 0 && p.1.contains v &&
          (List.range' p.2.1 (p.2.2 - p.2.1)).all fun e ↦ cs.contains ⟨[(B, 1)], e⟩
      | [(B, 1)] => Nat.ble p.2.1 c.off && Nat.blt c.off p.2.2 && p.1.all fun v ↦ cs.contains ⟨[(B, 1), (v, 1)], 0⟩
      | _ => false
  | _ => false

/-! ## `verify_tables`' exponent family -/

/-- **A linear form** over `verify_tables`' nine slacks (`a = μ - 19`, `b = μ - n`, `c_t = n - τ_t`, `d = μ - lm`): a
constant and the coefficients. -/
abbrev VtL := ℤ × List ℤ

/-- The slacks' upper bounds. -/
def vtUB : List ℤ := [13, 32, 32, 32, 32, 32, 32, 32, 32]

/-- `k·g` entrywise. -/
def lscale (k : ℤ) : List ℤ → List ℤ
  | [] => []
  | y :: ys => k * y :: lscale k ys

/-- `f + k·g` entrywise (a missing entry `0`; structural in `f`, so the kernel reduces it). -/
def ladd (k : ℤ) : List ℤ → List ℤ → List ℤ
  | x :: xs, y :: ys => (x + k * y) :: ladd k xs ys
  | x :: xs, [] => x :: ladd k xs []
  | [], ys => lscale k ys

/-- The least value of `Σ x_i·s_i` over the box `0 ≤ s_i ≤ u_i`. -/
def lmin : List ℤ → List ℤ → ℤ
  | x :: xs, u :: us => min 0 (x * u) + lmin xs us
  | _, _ => 0

/-- The largest. -/
def lmax : List ℤ → List ℤ → ℤ
  | x :: xs, u :: us => max 0 (x * u) + lmax xs us
  | _, _ => 0

def VtL.add (f g : VtL) (k : ℤ) : VtL := (f.1 + k * g.1, ladd k f.2 g.2)
def VtL.minv (f : VtL) : ℤ := f.1 + lmin f.2 vtUB
def VtL.maxv (f : VtL) : ℤ := f.1 + lmax f.2 vtUB

/-- **The slacks' words** (`vtexp.base`): `g_bus_mu` `19 + a`, `g_zc_n` `19 + a - b`, `dims_g[0]` (`kb[1]`)
`19 + a - d`, `dims_g[1 + t]` (`kb[2 + t]`, the values after `kb[1]`) `19 + a - b - c_t`; ghost `GB + j` as
`kb[1 + j]`, `j < 7`. -/
def vtBaseN (x : ℕ) : Option VtL :=
  let y := if GB ≤ x ∧ x < GB + 7 then x - GB + val% «verify_tables» "kb[1]" else x
  if y = val% «verify_tables» "g_bus_mu" then some (19, [1, 0, 0, 0, 0, 0, 0, 0, 0])
  else if y = val% «verify_tables» "g_zc_n" then some (19, [1, -1, 0, 0, 0, 0, 0, 0, 0])
  else if y = val% «verify_tables» "kb[1]" then some (19, [1, 0, 0, 0, 0, 0, 0, 0, -1])
  else if val% «verify_tables» "kb[1]" + 1 ≤ y ∧ y < val% «verify_tables» "kb[1]" + 7 then some (19, (List.range 9).map fun i ↦
    if i = 0 then 1 else if i = 1 then -1 else if i = y - val% «verify_tables» "kb[1]" + 1 then -1 else 0)
  else none

/-- **A word's form** (`vtexp.form`): a slacks' word, or what a top-level atom makes it of others' (fuel `f`): a constant
`g^k`, a copy, a product, or a quotient `d = v·b` whose form is nonnegative on the box. -/
noncomputable def vtF (as : List Atom) : ℕ → V → Option VtL
  | 0, _ => none
  | f + 1, v => match (if v.path = [] ∧ v.tag = 0 then vtBaseN v.idx else none) with
    | some b => some b
    | none => as.findSome? fun
      | .const d w => if d = v then (match Res.powOf1 w with
          | some k => some ((k : ℤ), [])
          | none => none) else none
      | .copy d a => if d = v then vtF as f a else none
      | .mul d a b => if d = v then
            (match vtF as f a, vtF as f b with
            | some p, some q => some (p.add q 1)
            | _, _ => none)
          else if a = v then
            (match vtF as f d, vtF as f b with
            | some p, some q => if 0 ≤ (p.add q (-1)).minv then some (p.add q (-1)) else none
            | _, _ => none)
          else if b = v then
            (match vtF as f d, vtF as f a with
            | some p, some q => if 0 ≤ (p.add q (-1)).minv then some (p.add q (-1)) else none
            | _, _ => none)
          else none
      | _ => none

/-- The fuel `vtexp.FUEL`. -/
def vtFuel : ℕ := 4

/-- **A cell's form**: `off + Σ e·F(b)`. -/
noncomputable def vtM (as : List Atom) : List (ℕ × ℕ) → ℤ → Option VtL
  | [], o => some (o, [])
  | (b, e) :: bs, o => match vtF as vtFuel (V.n b), vtM as bs o with
    | some p, some q => some (q.add p e)
    | _, _ => none

noncomputable def vtI (as : List Atom) (i : CIdx) : Option VtL := vtM as (idxC i).bases (idxC i).off

/-- **The arms' equations**: each arm `x = g^j` (`j`, `F_x` below `2^62`) whose form's first nonzero coefficient is `±1`
removes that slack. -/
noncomputable def vtArms (as : List Atom) : List (ℕ × ℕ) → VtL → VtL
  | [], f => f
  | (x, j) :: arms, f => vtArms as arms (match vtF as vtFuel (V.n x) with
    | some F => if j < capE ∧ F.maxv < capE then (match F.2.findIdx? (· ≠ 0) with
      | some i => if F.2.getD i 0 = 1 ∨ F.2.getD i 0 = -1 then
          f.add (F.add ((j : ℤ), []) (-1)) (-(f.2.getD i 0 * F.2.getD i 0)) else f
      | none => f) else f
    | none => f)

/-- The slacks' words whose forms are nonnegative (`vtexp.NNB`). -/
def vtNNB : List ℕ := [val% «verify_tables» "g_bus_mu", val% «verify_tables» "kb[1]", val% «verify_tables» "kb[2]",
  val% «verify_tables» "kb[3]", val% «verify_tables» "kb[4]", val% «verify_tables» "kb[5]", val% «verify_tables» "kb[6]",
  val% «verify_tables» "kb[7]", val% «verify_tables» "g_zc_n"]

/-- **Nonnegative** once the arms' equations are used: on the box, or less a slacks' word's form on it. -/
noncomputable def vtNN (as : List Atom) (arms : List (ℕ × ℕ)) (f : VtL) : Bool :=
  decide (0 ≤ (vtArms as arms f).minv) || vtNNB.any fun x ↦ match vtBaseN x with
    | some F => decide (0 ≤ ((vtArms as arms f).add F (-1)).minv)
    | none => false

/-- A form below `2^62` on the box. -/
def vtSmall (f : VtL) : Bool := decide (f.maxv < capE)

/-- `e(a) < e(b)`: `F_b - F_a - 1` nonnegative. -/
noncomputable def vtLt (as : List Atom) (arms : List (ℕ × ℕ)) (a b : CIdx) : Bool :=
  match vtI as a, vtI as b with
  | some A, some B => vtSmall A && vtSmall B && vtNN as arms ((B.add A (-1)).add (1, []) (-1))
  | _, _ => false

/-- `[B]·[J]·g^o` one of `cs`, the cells `[B]·g^(o + t)`, `t < |cs|`, by `e(J) < |cs|`. -/
noncomputable def vtSubP (as : List Atom) (arms : List (ℕ × ℕ)) (c : CCell) (cs : List CCell) : Bool :=
  match c.bases with
  | [(B, 1), (J, 1)] => (List.range cs.length).all (fun t ↦ cs.contains ⟨[(B, 1)], c.off + t⟩) &&
      vtLt as arms (.val J) (.num cs.length)
  | _ => false

/-- **`verify_tables`' exponent family** (`vtexp.holds`): `lt a b` (`F_b - F_a - 1 ≥ 0`), `subR q r` (stride `1`, `q`'s
base `r`'s times a product `m`, `r`'s bounds hold `F_m + q.off - r.off` past `q`'s), `subP` (`[B]·[J]·g^o` one of
`[B]·g^(o + t)`, `t < |cs|`, by `e(J) < |cs|`), under branch conditions (the arms used). -/
noncomputable def vtExpR (as : List Atom) (arms : List (ℕ × ℕ)) : CRes → Bool
  | .lt a b => vtLt as arms a b
  | .subP c cs => vtSubP as arms c cs
  | .subR q r => Nat.beq q.stride 1 && Nat.beq r.stride 1 &&
      decide (q.base.bases.take r.base.bases.length = r.base.bases) &&
      (match vtM as (q.base.bases.drop r.base.bases.length) ((q.base.off : ℤ) - r.base.off), vtI as q.lo,
          vtI as q.hi, vtI as r.lo, vtI as r.hi with
      | some m, some ql, some qh, some rl, some rh => vtSmall m && vtSmall ql && vtSmall qh && vtSmall rl &&
          vtSmall rh && vtNN as arms ((m.add ql 1).add rl (-1)) && vtNN as arms (rh.add (m.add qh 1) (-1))
      | _, _, _, _, _ => false)
  | .under cs r => vtExpR as (arms ++ cs.filterMap fun
      | .arm x j => some (x, j)
      | _ => none) r
  | _ => false

/-- `verify_tables`' own parameter words as ghost slots: `dims_g[j]`, `j < 7` (`HSig.gw`). -/
def vtGw : List (CCell × ℕ) := (List.range 7).map fun j ↦ (⟨[(val% «verify_tables» "dims_g", 1)], j⟩, j)

/-- **The top-level atoms of `verify_tables` its exponent family reads** (`vtexp.ATOMS`; `EndExec.vtAtoms_top`). -/
def vtAtoms : List Atom :=
  [.const (.n (val% «verify_tables» "kb[0]")) (word 1 0),
    .mul (.n (val% «verify_tables» "g_bus_mu")) (.n (val% «verify_tables» "s23.u0.s1#0")) (.n (val% «verify_tables» "kb[2]")),
    .mul (.n (val% «verify_tables» "g_bus_mu")) (.n (val% «verify_tables» "s23.u1.s1#0")) (.n (val% «verify_tables» "kb[3]")),
    .mul (.n (val% «verify_tables» "g_bus_mu")) (.n (val% «verify_tables» "s23.u2.s1#0")) (.n (val% «verify_tables» "kb[4]")),
    .mul (.n (val% «verify_tables» "g_bus_mu")) (.n (val% «verify_tables» "s23.u3.s1#0")) (.n (val% «verify_tables» "kb[5]")),
    .mul (.n (val% «verify_tables» "g_bus_mu")) (.n (val% «verify_tables» "s23.u4.s1#0")) (.n (val% «verify_tables» "kb[6]")),
    .mul (.n (val% «verify_tables» "g_bus_mu")) (.n (val% «verify_tables» "s23.u5.s1#0")) (.n (val% «verify_tables» "kb[7]")),
    .mul (.n (val% «verify_tables» "g_bus_mu")) (.n (val% «verify_tables» "sel_len_g@1")) (.n (val% «verify_tables» "kb[0]")),
    .mul (.n (val% «verify_tables» "g_bus_mu")) (.n (val% «verify_tables» "sel_len_g@2")) (.n (val% «verify_tables» "kb[1]")),
    .const (.n (val% «verify_tables» "kappa_g@2~0")) (word 524288 0),
    .mul (.n (val% «verify_tables» "kappa_g@2")) (.n (val% «verify_tables» "kb[0]")) (.n (val% «verify_tables» "kappa_g@2~0")),
    .mul (.n (val% «verify_tables» "g_bus_mu")) (.n (val% «verify_tables» "sel_len_g@3")) (.n (val% «verify_tables» "kappa_g@2")),
    .mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "s56.u0.s1#1")) (.n (val% «verify_tables» "kb[2]")),
    .mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "air_acc@1~0")) (.n (val% «verify_tables» "kb[2]")),
    .mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "air_acc@2~0")) (.n (val% «verify_tables» "kb[3]")),
    .mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "air_acc@3~0")) (.n (val% «verify_tables» "kb[4]")),
    .mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "air_acc@4~0")) (.n (val% «verify_tables» "kb[5]")),
    .mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "air_acc@5~0")) (.n (val% «verify_tables» "kb[6]")),
    .mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "air_acc@6~0")) (.n (val% «verify_tables» "kb[7]"))]

/-- **`verify_tables`' exponent family**, its ghost slots its `dims_g` words. -/
noncomputable def vtExp (fn : Fn) (gw : List (CCell × ℕ)) (r : CRes) : Bool :=
  fn.name == name% «verify_tables» && decide (gw = vtGw) && vtExpR vtAtoms [] r

end

end LeanVM.Guest.CoreMode

namespace LeanVM.Guest.CoreMode.Own.verify_tables

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its families**: its reads past its table sumcheck (`vtStC`), its buffers through its hinted order (`vtPerm`). -/
noncomputable def fams : List (String × (Fn → CRes → Bool)) := [(name% «verify_tables», vtStC), (name% «verify_tables», vtPerm)]

/-- **Its exponent family**, its ghost slots its own `dims_g` words (`vtExp`). -/
noncomputable def gwFams : List (String × (Fn → List (CCell × ℕ) → CRes → Bool)) := [(name% «verify_tables», vtExp)]

end

end LeanVM.Guest.CoreMode.Own.verify_tables
