/-
  LeanVM.Guest.CoreMode.Fn.verify_tables.ExpDefs

  `verify_tables`' exponent family's definitions (`Fam.lean`'s `vtExp`): its words' forms over its slacks and the
  residuals they decide, at a table of the forms (`Gen/Own/verify_tables`) the search `vtF` checks once.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

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

/-- **The slacks' words** (`verify_tables.py`'s `base`): `g_bus_mu` `19 + a`, `g_zc_n` `19 + a - b`, `dims_g[0]` (`kb[1]`)
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

/-- **A word's form** (`verify_tables.py`'s `form`): a slacks' word, or what a top-level atom makes it of others' (fuel `f`): a constant
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

/-- The fuel (`verify_tables.py`'s `FUEL`). -/
def vtFuel : ℕ := 4

/-- **The top-level atoms of `verify_tables` its exponent family reads** (`verify_tables.py`'s `ATOMS`; `EndExec.vtAtoms_top`). -/
def vtAtoms : List Atom :=
  [.const (.n (val% «verify_tables» "kb[0]")) (word 1 0),
    .mul (.n (val% «verify_tables» "g_bus_mu")) (.n (val% «verify_tables» "s17.u0.s0#0")) (.n (val% «verify_tables» "kb[2]")),
    .mul (.n (val% «verify_tables» "g_bus_mu")) (.n (val% «verify_tables» "s17.u1.s0#0")) (.n (val% «verify_tables» "kb[3]")),
    .mul (.n (val% «verify_tables» "g_bus_mu")) (.n (val% «verify_tables» "s17.u2.s0#0")) (.n (val% «verify_tables» "kb[4]")),
    .mul (.n (val% «verify_tables» "g_bus_mu")) (.n (val% «verify_tables» "s17.u3.s0#0")) (.n (val% «verify_tables» "kb[5]")),
    .mul (.n (val% «verify_tables» "g_bus_mu")) (.n (val% «verify_tables» "s17.u4.s0#0")) (.n (val% «verify_tables» "kb[6]")),
    .mul (.n (val% «verify_tables» "g_bus_mu")) (.n (val% «verify_tables» "s17.u5.s0#0")) (.n (val% «verify_tables» "kb[7]")),
    .mul (.n (val% «verify_tables» "g_bus_mu")) (.n (val% «verify_tables» "sel_len_g@1")) (.n (val% «verify_tables» "kb[0]")),
    .mul (.n (val% «verify_tables» "g_bus_mu")) (.n (val% «verify_tables» "sel_len_g@2")) (.n (val% «verify_tables» "kb[1]")),
    .const (.n (val% «verify_tables» "kappa_g@2~0")) (word 524288 0),
    .mul (.n (val% «verify_tables» "kappa_g@2")) (.n (val% «verify_tables» "kb[0]")) (.n (val% «verify_tables» "kappa_g@2~0")),
    .mul (.n (val% «verify_tables» "g_bus_mu")) (.n (val% «verify_tables» "sel_len_g@3")) (.n (val% «verify_tables» "kappa_g@2")),
    .mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "s57.u0.s1#1")) (.n (val% «verify_tables» "kb[2]")),
    .mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "air_acc@1~0")) (.n (val% «verify_tables» "kb[2]")),
    .mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "air_acc@2~0")) (.n (val% «verify_tables» "kb[3]")),
    .mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "air_acc@3~0")) (.n (val% «verify_tables» "kb[4]")),
    .mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "air_acc@4~0")) (.n (val% «verify_tables» "kb[5]")),
    .mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "air_acc@5~0")) (.n (val% «verify_tables» "kb[6]")),
    .mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "air_acc@6~0")) (.n (val% «verify_tables» "kb[7]"))]

/-- **A table of forms** `(x, F)`: value `x`'s form `F`, the first entry for `x`. -/
def vtFormAt : List (ℕ × VtL) → ℕ → Option VtL
  | [], _ => none
  | (y, F) :: T, x => bif Nat.beq x y then some F else vtFormAt T x

/-- **Each entry of the table `T` is its value's form** by the search `vtF` (checked once, `Gen/Own/verify_tables`). -/
noncomputable def vtFormsOk (T : List (ℕ × VtL)) : Bool := T.all fun p ↦ decide (vtF vtAtoms vtFuel (V.n p.1) = some p.2)

/-! ## The residuals, at the words' forms `fs` (by value) -/

/-- **A cell's form**: `off + Σ e·fs(b)`. -/
def vtM (fs : ℕ → Option VtL) : List (ℕ × ℕ) → ℤ → Option VtL
  | [], o => some (o, [])
  | (b, e) :: bs, o => match fs b, vtM fs bs o with
    | some p, some q => some (q.add p e)
    | _, _ => none

def vtI (fs : ℕ → Option VtL) (i : CIdx) : Option VtL := vtM fs (idxC i).bases (idxC i).off

/-- **The arms' equations**: each arm `x = g^j` (`j`, `F_x` below `2^62`) whose form's first nonzero coefficient is `±1`
removes that slack. -/
def vtArms (fs : ℕ → Option VtL) : List (ℕ × ℕ) → VtL → VtL
  | [], f => f
  | (x, j) :: arms, f => vtArms fs arms (match fs x with
    | some Fx => if j < capE ∧ Fx.maxv < capE then (match Fx.2.findIdx? (· ≠ 0) with
      | some i => if Fx.2.getD i 0 = 1 ∨ Fx.2.getD i 0 = -1 then
          f.add (Fx.add ((j : ℤ), []) (-1)) (-(f.2.getD i 0 * Fx.2.getD i 0)) else f
      | none => f) else f
    | none => f)

/-- The slacks' words whose forms are nonnegative (`verify_tables.py`'s `NNB`). -/
def vtNNB : List ℕ := [val% «verify_tables» "g_bus_mu", val% «verify_tables» "kb[1]", val% «verify_tables» "kb[2]",
  val% «verify_tables» "kb[3]", val% «verify_tables» "kb[4]", val% «verify_tables» "kb[5]", val% «verify_tables» "kb[6]",
  val% «verify_tables» "kb[7]", val% «verify_tables» "g_zc_n"]

/-- **Nonnegative** once the arms' equations are used: on the box, or less a slacks' word's form on it. -/
def vtNN (fs : ℕ → Option VtL) (arms : List (ℕ × ℕ)) (f : VtL) : Bool :=
  decide (0 ≤ (vtArms fs arms f).minv) || vtNNB.any fun x ↦ match vtBaseN x with
    | some B => decide (0 ≤ ((vtArms fs arms f).add B (-1)).minv)
    | none => false

/-- A form below `2^62` on the box. -/
def vtSmall (f : VtL) : Bool := decide (f.maxv < capE)

/-- `e(a) < e(b)`: `F_b - F_a - 1` nonnegative. -/
def vtLt (fs : ℕ → Option VtL) (arms : List (ℕ × ℕ)) (a b : CIdx) : Bool :=
  match vtI fs a, vtI fs b with
  | some A, some B => vtSmall A && vtSmall B && vtNN fs arms ((B.add A (-1)).add (1, []) (-1))
  | _, _ => false

/-- **The run `[B]·g^o`, `[B]·g^(o + 1)`, …**: `cs` those cells in order. -/
def vtRun (B : ℕ) : ℕ → List CCell → Bool
  | _, [] => true
  | o, c :: cs => (match c.bases with
      | [(b, e)] => Nat.beq b B && Nat.beq e 1
      | _ => false) && Nat.beq c.off o && vtRun B (o + 1) cs

/-- `[B]·[J]·g^o` one of `cs`, the run `[B]·g^(o + t)`, `t < |cs|` (`vtRun`), by `e(J) < |cs|`. -/
def vtSubP1 (fs : ℕ → Option VtL) (arms : List (ℕ × ℕ)) (o B J : ℕ) (cs : List CCell) : Bool :=
  vtRun B o cs && vtLt fs arms (.val J) (.num cs.length)

/-- `vtSubP1` with either base the index. -/
def vtSubP (fs : ℕ → Option VtL) (arms : List (ℕ × ℕ)) (c : CCell) (cs : List CCell) : Bool :=
  match c.bases with
  | [(B, 1), (J, 1)] => vtSubP1 fs arms c.off B J cs || vtSubP1 fs arms c.off J B cs
  | _ => false

/-- **`verify_tables`' exponent family** (`verify_tables.py`'s `holds`): `lt a b` (`F_b - F_a - 1 ≥ 0`), `subR q r` (stride `1`, `q`'s
base `r`'s times a product `m`, `r`'s bounds hold `F_m + q.off - r.off` past `q`'s), `subP` (`[B]·[J]·g^o` one of `cs`,
the run `[B]·g^(o + t)`, `t < |cs|`, by `e(J) < |cs|`, either base the index), under branch conditions (the arms used). -/
def vtExpR (fs : ℕ → Option VtL) (arms : List (ℕ × ℕ)) : CRes → Bool
  | .lt a b => vtLt fs arms a b
  | .subP c cs => vtSubP fs arms c cs
  | .subR q r => Nat.beq q.stride 1 && Nat.beq r.stride 1 &&
      decide (q.base.bases.take r.base.bases.length = r.base.bases) &&
      (match vtM fs (q.base.bases.drop r.base.bases.length) ((q.base.off : ℤ) - r.base.off), vtI fs q.lo,
          vtI fs q.hi, vtI fs r.lo, vtI fs r.hi with
      | some m, some ql, some qh, some rl, some rh => vtSmall m && vtSmall ql && vtSmall qh && vtSmall rl &&
          vtSmall rh && vtNN fs arms ((m.add ql 1).add rl (-1)) && vtNN fs arms (rh.add (m.add qh 1) (-1))
      | _, _, _, _, _ => false)
  | .under cs r => vtExpR fs (arms ++ cs.filterMap fun
      | .arm x j => some (x, j)
      | _ => none) r
  | _ => false

end

public section

theorem vtRun_mem {B : ℕ} : ∀ {o : ℕ} {cs : List CCell}, vtRun B o cs = true →
    ∀ t < cs.length, (⟨[(B, 1)], o + t⟩ : CCell) ∈ cs
  | _, [], _, _, ht => absurd ht (Nat.not_lt_zero _)
  | o, ⟨bs, off⟩ :: cs, h, t, ht => by
    simp only [vtRun, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨hb, rfl⟩, hr⟩ := h
    cases t with
    | zero =>
      match bs, hb with
      | [(b, e)], hb =>
        simp only [Bool.and_eq_true, Nat.beq_eq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        exact List.mem_cons_self
    | succ t =>
      have := vtRun_mem hr t (by simpa using ht)
      rw [show off + (t + 1) = off + 1 + t by omega]
      exact List.mem_cons_of_mem _ this

theorem vtF_of_formAt {T : List (ℕ × VtL)} (hT : vtFormsOk T = true) {x : ℕ} {F : VtL} (h : vtFormAt T x = some F) :
    vtF vtAtoms vtFuel (V.n x) = some F := by
  induction T with
  | nil => cases h
  | cons p T ih =>
    obtain ⟨y, G⟩ := p
    simp only [vtFormsOk, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hT
    simp only [vtFormAt] at h
    cases hxy : Nat.beq x y
    · rw [hxy, Bool.cond_false] at h
      exact ih hT.2 h
    · rw [hxy, Bool.cond_true, Option.some.injEq] at h
      rw [Nat.beq_eq.mp hxy, ← h]
      exact hT.1

end

end LeanVM.Guest.CoreMode
