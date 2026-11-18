/-
  LeanVM.Guest.CoreMode.CoreRes

  The residuals the core route takes, by family: a heap certificate's statements on core names that
  its honest instances make true (`HonF.res`, discharged in `EndExecCoreRes`).
-/

module

public import LeanVM.Guest.CoreMode.Core
public import LeanVM.Guest.Res.FamDefs
public import LeanVM.Guest.B1.Selectors.ColumnSelector
public import LeanVM.Guest.Res.AnyData
public import LeanVM.Guest.B1.Digest.MonoDefs
public import LeanVM.Guest.CoreMode.CoreGhost
public import LeanVM.Guest.Res.SelDefs
public import LeanVM.Guest.Res.TermDefs

/-!
# Residual families on core names

A heap certificate (`HCert.res`) lists statements on core names (`CRes`) its witnesses use. The core
route takes a function's residuals when each is of a family (`resFam`), a decidable check on the
function's own code whose soundness at its honest instances is proved once, in `EndExecCoreRes`
(`resFam_inst`):

* `rc`: `e(x) < n` (`.lt (.val x) (.num n)`), the value `x` range checked on every returning path
  against a constant `g^(N - 1)`, `N ≤ n` (`Res.rcBound` of the top-level atoms, `Res.topAtoms`), from
  the instance's path;
* `sel`: the same, `x` a top-level selector of `m ≤ n` arms (`Res.topSels`), from its path; and
  `e(x·g^c) < n` (`.lt (.mono ⟨[(x, 1)], c⟩) (.num n)`) for such a selector of `m` arms, `m + c ≤ n`;
* `exp`: the same, `n ≥ 2^28`, `x` a parameter an entry run bounds (so `g^e`, `e < 2^62`, `ExpW`) and
  `q = b·x` with `b` and `q` dereferenced on every returning path: `e` is the difference of two
  addresses, below `2^28` (the emitter's `e(x) < 2^62 - 1` for a run's root, `opening_queries__*`);
* `cs`: `column_selector__L{κ}`'s read of its lowest digit's entry lies in the strided table its
  callers write (`csSub κ`), from the offset its callers hand it (the old route's F3 on names);
* `rcv`: `e(x) < e(p·g)` (`.lt (.val x) (.mono ⟨[(p, 1)], 1⟩)`), the value `x` range checked against the value
  `p` among the top-level atoms;
* `under g r`: a residual of a family, the branch conditions `g` aside.

These name no ghost value (`CRes.vals`, below `GB`), so they hold at an honest valuation whatever its
ghost words (`CRes.holds_congr`). One family names a ghost:
* `ml` (`mlSub`): `child_claim_list_mono_last__L{k}`'s read of claim `jj`'s entry `[ent]·Π[gap_i]^4·g^(4jj+d)`
  lies in its caller's table, the run `[ghost₀]·g^(4j+d)` below the exponent of its parameter `limit` (its ghost
  the caller's cell `2`, `glOk`), from the old route's gap walk (`EndExecCoreMono`).

`resOk Cf`: every residual of `Cf`'s heap certificate of a family (`resFamG`). `CfOk` asks it, so the core
route's honest valuations (`HonF.res`) make the residuals true.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **`column_selector__L{κ}`'s lowest digit in its strided table** (F3 on names): the cell
`[sel_eq]·[digit₀]·g^off` one of the run `⟨[sel_eq]·g^off, 2^(4-w), 0, 2^w⟩`, `w` the digit's width,
`sel_eq` parameter `1` and the digit value `3`. -/
def csSub (κ : ℕ) : CRes :=
  .sub ⟨[(1, 1), (3, 1)], 64 * (κ / 4) + 16 * (B1.Tables.csW κ 0 - 1)⟩
    ⟨⟨[(1, 1)], 64 * (κ / 4) + 16 * (B1.Tables.csW κ 0 - 1)⟩, 2 ^ (4 - B1.Tables.csW κ 0), .num 0,
      .num (2 ^ B1.Tables.csW κ 0)⟩

/-- **`x` the quotient of two addresses**: atoms `q = b·x` (or `x·b`) and `DEREF`s through `b` and
`q` at offset `0`. -/
def expDiff (as : List Atom) (x : V) : Bool :=
  as.any fun
    | .mul q a b => (decide (b = x) && expLd as a && expLd as q) || (decide (a = x) && expLd as b && expLd as q)
    | _ => false
where
  /-- A `DEREF` through `p` at offset `0` among the atoms. -/
  expLd (as : List Atom) (p : V) : Bool := as.any fun
    | .load _ p' 0 => decide (p' = p)
    | _ => false

/-- **A residual of a family**, read off the function's code and the frame cells `xc` known to hold powers of `g` (`CFun.xc`), of `np`
parameters: an exponent bound of a value range checked (`rc`) or a selector (`sel`, also of its word times a
constant power of `g`) on every
returning path, of a parameter an entry run bounds and the quotient of two addresses the path
dereferences (`exp`, a bound `≥ 2^28`), `column_selector`'s lowest digit (`cs`), or such a residual
under branch conditions. -/
noncomputable def resFam (fn : Fn) (xc : List ℕ) : CRes → Bool
  | .lt (.val x) (.num n) => decide (n < capE) &&
      ((match Res.rcBound (Res.topAtoms fn.body) (V.n x) with
        | some N => decide (N ≤ n)
        | none => false) ||
        ((Res.topSels fn.body).any fun p ↦ decide (p.1 = V.n x) && decide (p.2 ≤ n)) ||
        (decide (2 ^ 28 ≤ n) && decide (x < fn.params.length) && xc.contains (2 + x) &&
          expDiff (Res.topAtoms fn.body) (V.n x)))
  | .lt (.val x) (.mono c) => match c.bases, c.off with
    | [(p, 1)], 1 => (Res.topAtoms fn.body).any fun
        | .rangeCheck x' _ _ _ k => decide (x' = V.n x) && decide (k = V.n p)
        | _ => false
    | _, _ => false
  | .lt (.mono c) (.num n) => match c.bases with
    | [(x, 1)] => decide (n < capE) &&
        ((Res.topSels fn.body).any (fun p ↦ decide (p.1 = V.n x) && decide (p.2 + c.off ≤ n)) ||
          match Res.rcBound (Res.topAtoms fn.body) (V.n x) with
          | some N => decide (N + c.off ≤ n)
          | none => false)
    | _ => false
  | .sub c q => (List.range 31).any fun κ ↦ fn.name == B1.Tables.lName "column_selector" κ &&
      decide (CRes.sub c q = csSub κ)
  | .under _ r => resFam fn xc r
  | _ => false

/-! ## The values a residual names -/

def CCell.vals (c : CCell) : List ℕ := c.bases.map (·.1)

def CIdx.vals : CIdx → List ℕ
  | .num _ => []
  | .val v => [v]
  | .mono c => c.vals

def CRun.vals (r : CRun) : List ℕ := r.base.vals ++ r.lo.vals ++ r.hi.vals

def CCond.vals : CCond → List ℕ
  | .arm x _ => [x]
  | .zero c => [c]
  | .nonzero c => [c]

/-- **The value numbers a residual names.** -/
def CRes.vals : CRes → List ℕ
  | .lt a b => a.vals ++ b.vals
  | .nz _ => []
  | .sub c r => c.vals ++ r.vals
  | .subR q r => q.vals ++ r.vals
  | .under g r => g.flatMap CCond.vals ++ r.vals
  | .subP c cs => c.vals ++ cs.flatMap CCell.vals

theorem valW_vals {w w' : ℕ → E} {c : CCell} (h : ∀ k ∈ c.vals, w' k = w k) : c.valW w' = c.valW w :=
  valW_congr fun b hb ↦ h b.1 (List.mem_map.mpr ⟨b, hb, rfl⟩)

theorem idxC_vals (i : CIdx) : (idxC i).vals = i.vals := by
  cases i <;> simp [idxC, CIdx.vals, CCell.vals, baseC]

theorem runSet_vals {w w' : ℕ → E} {r : CRun} (h : ∀ k ∈ r.vals, w' k = w k) (x : K) :
    r.Set w' x ↔ r.Set w x := by
  simp only [CRun.vals, List.mem_append] at h
  exact runSet_congr (valW_vals fun k hk ↦ h k (Or.inl (Or.inl hk)))
    (valW_vals fun k hk ↦ h k (Or.inl (Or.inr (by rwa [idxC_vals] at hk))))
    (valW_vals fun k hk ↦ h k (Or.inr (by rwa [idxC_vals] at hk)))

/-- **A residual's truth depends only on the values it names.** -/
theorem CRes.holds_congr {σ σ' : Val} : ∀ {r : CRes}, (∀ k ∈ r.vals, σ' (V.n k) = σ (V.n k)) →
    (r.Holds σ' ↔ r.Holds σ)
  | .lt a b, h => by
    simp only [CRes.vals, List.mem_append] at h
    show LtF _ _ _ ↔ LtF _ _ _
    unfold LtF
    rw [valW_vals (w := vw σ) (w' := vw σ') (c := idxC a) fun k hk ↦ h k (Or.inl (by rwa [idxC_vals] at hk)),
      valW_vals (w := vw σ) (w' := vw σ') (c := idxC b) fun k hk ↦ h k (Or.inr (by rwa [idxC_vals] at hk))]
  | .nz _, _ => Iff.rfl
  | .sub c r, h => by
    simp only [CRes.vals, List.mem_append] at h
    show r.Set (vw σ') (c.addrW (vw σ')) ↔ r.Set (vw σ) (c.addrW (vw σ))
    unfold CCell.addrW
    rw [valW_vals (w := vw σ) (w' := vw σ') fun k hk ↦ h k (Or.inl hk)]
    exact runSet_vals (fun k hk ↦ h k (Or.inr hk)) _
  | .subR q r, h => by
    simp only [CRes.vals, List.mem_append] at h
    show (∀ x, q.Set (vw σ') x → r.Set (vw σ') x) ↔ (∀ x, q.Set (vw σ) x → r.Set (vw σ) x)
    have h1 := runSet_vals (w := vw σ) (w' := vw σ') (r := q) (fun k hk ↦ h k (Or.inl hk))
    have h2 := runSet_vals (w := vw σ) (w' := vw σ') (r := r) (fun k hk ↦ h k (Or.inr hk))
    exact forall_congr' fun x ↦ imp_congr (h1 x) (h2 x)
  | .under g r, h => by
    simp only [CRes.vals, List.mem_append, List.mem_flatMap] at h
    have hg : ∀ c ∈ g, (c.Holds σ' ↔ c.Holds σ) := fun c hc ↦ by
      cases c <;> simp only [CCond.Holds] <;>
        rw [h _ (Or.inl ⟨_, hc, by simp [CCond.vals]⟩)]
    show ((∀ c ∈ g, c.Holds σ') → r.Holds σ') ↔ ((∀ c ∈ g, c.Holds σ) → r.Holds σ)
    rw [CRes.holds_congr fun k hk ↦ h k (Or.inr hk)]
    constructor
    · exact fun h1 h2 ↦ h1 fun c hc ↦ (hg c hc).mpr (h2 c hc)
    · exact fun h1 h2 ↦ h1 fun c hc ↦ (hg c hc).mp (h2 c hc)
  | .subP c cs, h => by
    simp only [CRes.vals, List.mem_append, List.mem_flatMap] at h
    show (∃ c' ∈ cs, c.addrW (vw σ') = c'.addrW (vw σ')) ↔ (∃ c' ∈ cs, c.addrW (vw σ) = c'.addrW (vw σ))
    unfold CCell.addrW
    rw [valW_vals (w := vw σ) (w' := vw σ') fun k hk ↦ h k (Or.inl hk)]
    constructor
    · rintro ⟨c', hc', he⟩
      exact ⟨c', hc', by rwa [valW_vals (w := vw σ) (w' := vw σ') fun k hk ↦ h k (Or.inr ⟨c', hc', hk⟩)] at he⟩
    · rintro ⟨c', hc', he⟩
      exact ⟨c', hc', by rwa [valW_vals (w := vw σ) (w' := vw σ') fun k hk ↦ h k (Or.inr ⟨c', hc', hk⟩)]⟩

/-! ## The ghost family -/

/-- `k` for `child_claim_list_mono_last__L{k}`, `1 ≤ k < 17`. -/
def mlK (fn : Fn) : Option ℕ :=
  ((List.range 17).find? fun k ↦ B1.Digest.mlNames.getD k "" == fn.name).bind fun k ↦ bif Nat.ble 1 k then some k
    else none

/-- **`child_claim_list_mono_last__L{k}`'s read of claim `jj`'s entry in its caller's table** (`ml`): the cell
`[ent]·Π_{i ≤ jj}[gap_i]^4·g^(4jj+d)` (`ent` the value `5`, gap `i` the value `6 + 10i`) a cell of the run
`[ghost₀]·g^(4j+d)`, `j` below the exponent of the parameter `3` (`limit`). -/
def mlSub (fn : Fn) : CRes → Bool
  | .sub c q => (mlK fn).any fun k ↦ Nat.blt (c.off / 4) k &&
      decide (q = ⟨⟨[(GB, 1)], c.off % 4⟩, 4, .num 0, .val 3⟩) &&
      decide (c.bases = (5, 1) :: (List.range (c.off / 4 + 1)).map fun i ↦ (6 + 10 * i, 4))
  | _ => false

/-! ## The instance's exponent and dimension facts -/

/-- **A top-level `load` of `x` through `p` at offset `k`** among the atoms. -/
def loadAt (as : List Atom) (x p : V) (k : ℕ) : Bool :=
  as.any fun
    | .load d p' k' => decide (d = x) && decide (p' = p) && decide (k' = k)
    | _ => false

/-- **The exponent fact of a value** (`Res.expFacts`): `x` a listed parameter of `fn` (offset `none`), or the word a
top-level `load` reads at a listed parameter's `[p]·g^k` (offset `some k`); the fact's bound. -/
noncomputable def expQ1 (fn : Fn) (x : V) : Option ℕ :=
  Res.expFacts.findSome? fun c ↦ if c.1 == fn.name then
    match fn.params[c.2.1]?, c.2.2.1 with
    | some p, none => if p = x then some c.2.2.2 else none
    | some p, some k => if loadAt (Res.topAtoms fn.body) x p k then some c.2.2.2 else none
    | none, _ => none
  else none

/-- **The exponent fact of a value or of a top-level product** `x = a·w` of a value `a` of one (`expQ1`) and a
constant `g^c`: the bound, plus `c`. -/
noncomputable def expQB (fn : Fn) (x : V) : Option ℕ :=
  match expQ1 fn x with
  | some b => some b
  | none => (Res.topAtoms fn.body).findSome? fun
    | .mul d a w => if d = x then
        match expQ1 fn a, (Res.constOf (Res.topAtoms fn.body) w).bind Res.powOf with
        | some b, some c => some (b + c)
        | _, _ => none
      else none
    | _ => none

/-- **A dimension fact's pair** (`Res.dimFacts`): `x` the word a top-level `load` reads at the base parameter's
`[kb]·g^j`, `p` the bound parameter, `(j, c)` one of the pairs, `t < c + u`, `u < 2^33`. -/
noncomputable def dimLt (fn : Fn) (x : V) (t : ℕ) (p : V) (u : ℕ) : Bool :=
  decide (u < 2 ^ 33) && Res.dimFacts.any fun c ↦ c.1 == fn.name &&
    match fn.params[c.2.1]?, fn.params[c.2.2.1]? with
    | some kb, some gb => decide (gb = p) &&
        c.2.2.2.any fun q ↦ loadAt (Res.topAtoms fn.body) x kb q.1 && decide (t < q.2 + u)
    | _, _ => false

/-- **The residuals of the instance's exponent and dimension facts** (`expQ`, `dim`; `Res.expFacts`,
`Res.dimFacts`, which the old route's F7 to F9 read): a value of an exponent fact (`expQB`), times `g^c`, below
a constant, or a constant `g^k`, `k < c`, below it times `g^c`; a word of a dimension fact times `g^t` below its
bound parameter times `g^u` (`dimLt`). -/
noncomputable def resQ (fn : Fn) : CRes → Bool
  | .lt (.val x) (.num n) => decide (n < capE) && (expQB fn (V.n x)).any (· ≤ n)
  | .lt (.mono c) (.num n) => match c.bases with
    | [(x, 1)] => decide (n < capE) && (expQB fn (V.n x)).any (· + c.off ≤ n)
    | _ => false
  | .lt (.num k) (.mono c) => match c.bases with
    | [(x, 1)] => decide (k < c.off) && (expQB fn (V.n x)).any (· + c.off < capE)
    | _ => false
  | .lt (.val x) (.mono c) => match c.bases with
    | [(p, 1)] => dimLt fn (V.n x) 0 (V.n p) c.off
    | _ => false
  | .lt (.mono a) (.mono c) => match a.bases, c.bases with
    | [(x, 1)], [(p, 1)] => dimLt fn (V.n x) a.off (V.n p) c.off
    | _, _ => false
  | _ => false

/-- **A residual of a family**, ghost-free (`resFam`, `resQ`, its values below `GB`), or the ghost family `ml`. -/
noncomputable def resFamG (fn : Fn) (xc : List ℕ) (r : CRes) : Bool :=
  ((resFam fn xc r || resQ fn r) && r.vals.all (Nat.blt · GB)) || mlSub fn r

/-- **Every residual of the function's heap certificate of a family.** -/
noncomputable def resOk (Cf : CFun) : Bool := Cf.H.res.all (resFamG Cf.fn Cf.xc)

/-- **The ghost family's links** (`ml`): `child_claim_list_mono_last__L{k}`'s caller's cell `2` (its entries
table) its one ghost slot, after its four parameters, and cell `5` its parameter `3` (`limit`); it names no
ghost value. -/
noncomputable def mlGl (Cf : CFun) : Bool :=
  (mlK Cf.fn).isSome && decide (Cf.gl = [(2, 4, 0), (5, 3, 0)]) && Nat.beq Cf.H.sig.ghosts 1 && ngB Cf.fn

/-- **The caller's cells linked** (`CFun.gl`), of a family: none, or those of a callee of `anyLink` (a read of
its caller's entries table, `Res.LinkDefs`): the caller's cell `2` its entries parameter, cell `5` its bound
parameter times `g`, with no ghost slot; for `child_claim_list_mono_last__L{k}` the ghost family's (`mlGl`). -/
noncomputable def glOk (Cf : CFun) : Bool :=
  bif (mlK Cf.fn).isSome then mlGl Cf else
    (Cf.gl.isEmpty || Res.anyLink.fams.any fun F ↦ Cf.fn.name == F.1 && decide (Cf.gl = [(2, F.2.1, 0), (5, F.2.2, 1)]))
      && Nat.beq Cf.H.sig.ghosts 0

theorem resOk_nil {Cf : CFun} (h : Cf.H.res = []) : resOk Cf = true := by
  simp [resOk, h]

end

end LeanVM.Guest.CoreMode
