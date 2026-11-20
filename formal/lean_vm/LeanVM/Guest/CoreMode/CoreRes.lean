/-
  LeanVM.Guest.CoreMode.CoreRes

  The residuals the core route takes, by family: a heap certificate's statements on core names that
  its honest instances make true (`HonF.res`, discharged in `EndExecCoreRes`).
-/

module

public import LeanVM.Guest.CoreMode.Core
public import LeanVM.Guest.CoreMode.Fam.FamDefs
public import LeanVM.Guest.B1.Selectors.ColumnSelector
public import LeanVM.Guest.CoreMode.Gen.AnyLink
public import LeanVM.Guest.B1.Digest.MonoDefs
public import LeanVM.Guest.CoreMode.CoreGhost
public import LeanVM.Guest.CoreMode.LoopLink
public import LeanVM.Guest.CoreMode.Fam.SelDefs
public import LeanVM.Guest.CoreMode.Fam.TermDefs
public import LeanVM.Guest.CoreMode.Fam.ExpDefs
import LeanVM.Guest.Data.Source

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
* `addr`: the same, `x = g^e` with `e` at most a bound `expM` reads off the top-level atoms: products of
  addresses dereferenced, bits' powers and constant powers of `g`;
* `rcv`: `e(x) < e(p·g)` (`.lt (.val x) (.mono ⟨[(p, 1)], 1⟩)`), the value `x` range checked against the value
  `p` among the top-level atoms;
* `rcn`: `e(x) < e(p)` (`.lt (.val x) (.val p)`), the value `x` range checked against `k = p·w`, `w` the constant
  `g⁻¹`, among the top-level atoms;
* `under g r`: a residual of a family, the branch conditions `g` aside.
* `split` (`splitFam`): a function's `g`-power `n = q^S·r` split from hinted bits (`splitsC`: `rs_eq_run`,
  `shared_selector_tables`), from the bits' booleanity on its path (`EndExecCoreSplit`): exponent bounds of `q`, `q^S`
  and `r` times constants, of `q^S·g^c` below `n` under an arm `j > c` of the selector `r`, and the loop's strided
  runs below `e(q)` inside `[0, e(n))`.
* `neg` (`negFam`): under a condition `k ≠ 0`, `e(x·v·g^off) < n`, `v` the constant `g⁻¹` of the arm `k ≠ 0` takes,
  `k = y + g^off`, `y = x·g^off` (so `x ≠ 1`), `x` and `y` range checked, `y` below `g^(n + 1)`; and
  `e(Π xᵢ^aᵢ·g^off) < n` from the arm `k ≠ 0` takes (`nzAtoms`, `armM`): each `xᵢ = g^eᵢ`, `eᵢ ≤ Mᵢ`, `xᵢ` range
  checked there against a constant `g^Mᵢ` (`Res.rcBound`) or `Mᵢ` a bound `expM` reads off that arm's atoms (a `DEREF`
  through `xᵢ`, `assert_gpow`), `Σ aᵢ·Mᵢ + off < n`.

These name no ghost value (`CRes.vals`, below `GB`), so they hold at an honest valuation whatever its
ghost words (`CRes.holds_congr`). One family names a ghost:
* `ml` (`mlSub`): `child_claim_list_mono_last__L{k}`'s read of claim `jj`'s entry `[ent]·Π[gap_i]^4·g^(4jj+d)`
  lies in its caller's table, the run `[ghost₀]·g^(4j+d)` below the exponent of its parameter `limit` (its ghost
  the caller's cell `2`, `glOk`), from the old route's gap walk (`EndExecCoreMono`).
* `st` (`stSub`): a loop's read `[cur]·g^c` past its cursor `cur` lies in its caller's proof stream, the run
  `[ghost₀]·[0, 8192)` (its ghosts the caller's stream and frame, `stGl`), from the old route's cursor invariants
  (`EndExecCoreSt`).

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

/-- **A run of constant bounds inside one of the same bases** (`subRC`): `[b]·g^a·g^(S·j)`, `l ≤ j < h`, among
`[b]·g^a'·g^(S·j')`, `l' ≤ j' < h'`: one stride `S > 0`, `a' ≤ a`, `S ∣ a - a'`, the shifted bounds inside. -/
def subRC (q r : CRun) : Bool :=
  match q.lo, q.hi, r.lo, r.hi with
  | .num l, .num h, .num l', .num h' =>
      basesBeq q.base.bases r.base.bases && Nat.beq q.stride r.stride && Nat.blt 0 q.stride &&
        Nat.ble r.base.off q.base.off && Nat.beq ((q.base.off - r.base.off) % q.stride) 0 &&
        Nat.ble l' (l + (q.base.off - r.base.off) / q.stride) &&
        Nat.ble (h + (q.base.off - r.base.off) / q.stride) h' && Nat.blt l capE && Nat.blt h capE &&
        Nat.blt l' capE && Nat.blt h' capE
  | _, _, _, _ => false

/-- **A run of constant bounds inside one of the same bases, its stride a multiple** (`subRCm`): `[b]·g^a·g^(S·j)`,
`l ≤ j < h`, among `[b]·g^a'·g^(S'·j')`, `l' ≤ j' < h'`: `S' > 0`, `S' ∣ S`, `a' ≤ a`, `S' ∣ a - a'`, its cell `j` the
cell `k + (S / S')·j` of the second (`k = (a - a') / S'`), inside its bounds. -/
def subRCm (q r : CRun) : Bool :=
  match q.lo, q.hi, r.lo, r.hi with
  | .num l, .num h, .num l', .num h' =>
      basesBeq q.base.bases r.base.bases && Nat.blt 0 r.stride && Nat.beq (q.stride % r.stride) 0 &&
        Nat.ble r.base.off q.base.off && Nat.beq ((q.base.off - r.base.off) % r.stride) 0 &&
        Nat.ble l' ((q.base.off - r.base.off) / r.stride + q.stride / r.stride * l) &&
        Nat.blt ((q.base.off - r.base.off) / r.stride + q.stride / r.stride * (h - 1)) h' && Nat.blt l capE &&
        Nat.blt h capE && Nat.blt l' capE && Nat.blt h' capE
  | _, _, _, _ => false

/-- A `DEREF` through `p` at offset `0` among the atoms: a `load` or a `touch`. -/
def derefAt (as : List Atom) (p : V) : Bool := as.any fun
  | .load _ p' 0 => decide (p' = p)
  | .touch _ p' => decide (p' = p)
  | _ => false

/-- The first product `x = a·b` among the atoms: its factors. -/
def mulOf (as : List Atom) (x : V) : Option (V × V) := as.findSome? fun
  | .mul d a b => if d = x then some (a, b) else none
  | _ => none

/-- **A bit's power** `x = 1 + b·w` (the first sum of `x` among the atoms), `b·b = b` and `w = 1 + g^m`
constants among them: `x = g^(m·b)`, at most `m`. -/
noncomputable def bitPow (as : List Atom) (x : V) : Option ℕ :=
  as.findSome? fun
    | .add d o y => if d = x ∧ Res.constOf as o = some 1 then
        match mulOf as y with
        | some (b, w) => if Atom.mul b b b ∈ as then (Res.constOf as w).bind fun c ↦ Res.powOf (c + 1)
          else none
        | none => none
      else none
    | _ => none

/-- **An exponent's bound** (`addr`, at most `M`, fuel `f`): `x = g^e`, `e ≤ M`, from atoms on every returning
path: a `DEREF` through `x` at offset `0` (an address of a memory of at most `2^28` words), a product of two
such values (the bounds' sum), a bit's power (`bitPow`), or a constant power of `g`. -/
noncomputable def expM (as : List Atom) : ℕ → V → Option ℕ
  | 0, _ => none
  | f + 1, x => if derefAt as x then some (2 ^ 28 - 1) else
      match mulOf as x with
      | some (a, b) => (expM as f a).bind fun ma ↦ (expM as f b).map (ma + ·)
      | none => match bitPow as x with
        | some m => some m
        | none => (Res.constOf as x).bind Res.powOf

/-- The fuel of `expM` the families use. -/
def expFuel : ℕ := 6

/-- The top-level atoms of the arm taken when `c` is nonzero (an `ite`'s second) of each top-level branch on `c`
that does not return, before the first statement that may return. -/
noncomputable def nzAtoms (c : V) : List Stmt → List Atom
  | [] => []
  | s :: ss => (match s with
      | .ite c' _ n => if c' = c ∧ Memory.noRetR s = true then Res.topAtoms n else []
      | _ => []) ++ (if Memory.noRetR s = true then nzAtoms c ss else [])

/-- `g⁻¹`: `w·g = 1`. -/
noncomputable def invG (w : E) : Bool := decide (w * ofK (addressOfIndex 1) = 1)

/-- **`x·v·g^off` below `g^n`** (`negFam`), `k` a branch condition: `v` the constant `g⁻¹` of the arm taken when `k`
is nonzero (`nzAtoms`), `x` range checked, `k = y + w` and `y = x·w`, `w` the constant `g^off` (so `x ≠ 1` there), `y`
range checked below `g^(n + 1)`. -/
noncomputable def negPair (fn : Fn) (k x v off n : ℕ) : Bool :=
  decide (off < 2 ^ 33) && (Res.rcBound (Res.topAtoms fn.body) (V.n x)).isSome &&
  (nzAtoms (V.n k) fn.body).any (fun
    | .const d w => decide (d = V.n v) && invG w
    | _ => false) &&
  (Res.topAtoms fn.body).any fun
    | .add d y o => decide (d = V.n k) && (Res.topAtoms fn.body).any (fun
        | .mul y' x' b => decide (y' = y) && decide (x' = V.n x) &&
          (match Res.constOf (Res.topAtoms fn.body) o, Res.constOf (Res.topAtoms fn.body) b with
          | some w, some w' => decide (w = w') && decide (w = ofK (addressOfIndex off))
          | _, _ => false) &&
          (match Res.rcBound (Res.topAtoms fn.body) y with
          | some N => decide (N ≤ n + 1)
          | none => false)
        | _ => false)
    | _ => false

/-- **An exponent bound of `x` in the arm `k ≠ 0` takes** (`nzAtoms`): `x = g^e`, `e ≤ M`, `x` range checked there
against a constant `g^M` (`Res.rcBound`), or `M` the bound `expM` reads off the arm's atoms. -/
noncomputable def armM (fn : Fn) (k x : ℕ) : Option ℕ :=
  match Res.rcBound (nzAtoms (V.n k) fn.body) (V.n x) with
  | some N => some (N - 1)
  | none => expM (nzAtoms (V.n k) fn.body) expFuel (V.n x)

/-- **An exponent bound of a product `Π xᵢ^aᵢ`** in the arm `k ≠ 0` takes: `Σ aᵢ·Mᵢ` (`armM`). -/
noncomputable def armProd (fn : Fn) (k : ℕ) : List (ℕ × ℕ) → Option ℕ
  | [] => some 0
  | (x, a) :: bs => (armM fn k x).bind fun M ↦ (armProd fn k bs).map (a * M + ·)

/-- **The `neg` family**, under a branch condition `k ≠ 0`: `e(x·v·g^off) < n` (`negPair`, either base first), and
`e(x) < n`, `e(Π xᵢ^aᵢ·g^off) < n` from the arm `k ≠ 0` takes (`armM`, `armProd`). -/
noncomputable def negFam (fn : Fn) (cs : List CCond) : CRes → Bool
  | .lt (.mono c) (.num n) => decide (n < capE) && cs.any fun
      | .nonzero k => (match c.bases with
        | [(a, 1), (b, 1)] => negPair fn k a b c.off n || negPair fn k b a c.off n
        | _ => false) || (armProd fn k c.bases).any (· + c.off < n)
      | _ => false
  | .lt (.val x) (.num n) => decide (n < capE) && cs.any fun
      | .nonzero k => (armM fn k x).any (· < n)
      | _ => false
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
          expDiff (Res.topAtoms fn.body) (V.n x)) ||
        (expM (Res.topAtoms fn.body) expFuel (V.n x)).any (· < n))
  | .lt (.val x) (.mono c) => match c.bases, c.off with
    | [(p, 1)], 1 => (Res.topAtoms fn.body).any fun
        | .rangeCheck x' _ _ _ k => decide (x' = V.n x) && decide (k = V.n p)
        | _ => false
    | _, _ => false
  | .lt (.val x) (.val p) => (Res.topAtoms fn.body).any fun
      | .rangeCheck x' _ _ _ k => decide (x' = V.n x) && (Res.topAtoms fn.body).any fun
          | .mul k' p' w => decide (k' = k) && decide (p' = V.n p) &&
              (match Res.constOf (Res.topAtoms fn.body) w with
              | some w' => invG w'
              | none => false)
          | _ => false
      | _ => false
  | .lt (.mono c) (.num n) => match c.bases with
    | [(x, 1)] => decide (n < capE) &&
        ((Res.topSels fn.body).any (fun p ↦ decide (p.1 = V.n x) && decide (p.2 + c.off ≤ n)) ||
          match Res.rcBound (Res.topAtoms fn.body) (V.n x) with
          | some N => decide (N + c.off ≤ n)
          | none => false)
    | _ => false
  | .lt (.num j) (.mono c) => match c.bases with
    | [(x, 1)] => decide (j < c.off) &&
        (Res.topSels fn.body).any fun p ↦ decide (p.1 = V.n x) && decide (p.2 + c.off < capE)
    | _ => false
  | .sub c q => (List.range 31).any fun κ ↦ fn.name == B1.Tables.lName "column_selector" κ &&
      decide (CRes.sub c q = csSub κ)
  | .subR q r => subRC q r || subRCm q r
  | .under cs r => resFam fn xc r || negFam fn cs r
  | _ => false

/-! ## The values a residual names -/

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

/-! ## The proof stream's cursor loops -/

/-- **The loops reading the proof stream past a cursor** (`st`): `(name, D, v, S)`, a loop whose caller's cell `D`
holds the stream, whose body loads the cursor `v`, reading at most `S` words past it an iteration. -/
def stLoops : List (String × ℕ × ℕ × ℕ) :=
  [(name% «keccak_layer__L0_loop0», 17, 20, 16), (name% «keccak_layer__L1_loop0», 17, 20, 16),
    (name% «keccak_layer__L0_loop1», 17, 14, 2), (name% «keccak_layer__L1_loop1», 17, 14, 2),
    (name% «verify_bus_gkr_loop0_loop0», 11, 13, 8), (name% «verify_tables_loop0», 22, 11, 3)]

/-- A stream-cursor loop's `(D, v, S)`. -/
def stK (fn : Fn) : Option (ℕ × ℕ × ℕ) := stLoops.lookup fn.name

/-- **A read past a stream cursor** (`st`): the cell `[v]·g^c`, `c < S`, a cell of the run `[ghost₀]·[0, 8192)` (its
ghost the caller's stream). -/
def stSub (fn : Fn) : CRes → Bool
  | .sub c q => (stK fn).any fun p ↦ decide (c.bases = [(p.2.1, 1)]) && Nat.blt c.off p.2.2 &&
      decide (q = ⟨⟨[(GB, 1)], 0⟩, 1, .num 0, .num 8192⟩)
  | _ => false

/-- **A stream-cursor loop's links**: its caller's cell `D` to its first ghost slot, the caller's frame address to its
second (`loopGl`); it names no ghost value. -/
def stGl (Cf : CFun) : Bool :=
  (stK Cf.fn).any (fun p ↦ decide (Cf.gl = loopGl Cf.fn.params.length [p.1])) && Nat.beq Cf.H.sig.ghosts 2 &&
    ngB Cf.fn

/-! ## The gap walk's frame loops -/

/-- **`child_claim_list_mono`'s frame loops** (`cm`): their claims a frame, `136` and `17`. -/
def cmK (fn : Fn) : Option ℕ :=
  bif fn.name == name% «child_claim_list_mono_loop0» then some 136 else
  bif fn.name == name% «child_claim_list_mono_loop1» then some 17 else none

/-- **A frame loop's read of claim `jj`'s entry in its caller's table** (`cm`): the cell
`[ent]·Π_{i ≤ jj}[gap_i]^4·g^(4jj+d)` (`ent` the value `12`, gap `i` the value `13 + 10i`) a cell of the run
`[ghost₀]·g^(4j+d)`, `j` below the exponent of `ghost₁` (its caller's `limit`); and that exponent's existence. -/
def cmSub (fn : Fn) : CRes → Bool
  | .sub c q => (cmK fn).any fun m ↦ Nat.blt (c.off / 4) m &&
      decide (q = ⟨⟨[(GB, 1)], c.off % 4⟩, 4, .num 0, .val (GB + 1)⟩) &&
      decide (c.bases = (12, 1) :: (List.range (c.off / 4 + 1)).map fun i ↦ (13 + 10 * i, 4))
  | .lt a b => (cmK fn).isSome && decide (a = .num 0) && decide (b = .val (GB + 1))
  | _ => false

/-- **A frame loop's links**: its caller's cells `2` (entries) and `5` (`limit`) to its first two ghost slots, the
caller's frame address to its third (`loopGl`); it names no ghost value. -/
def cmGl (Cf : CFun) : Bool :=
  (cmK Cf.fn).isSome && decide (Cf.gl = loopGl Cf.fn.params.length [2, 5]) && Nat.beq Cf.H.sig.ghosts 3 &&
    ngB Cf.fn

theorem cmSub_none {fn : Fn} (h : cmK fn = none) (x : CRes) : cmSub fn x = false := by
  unfold cmSub
  split <;> simp [h]

/-! ## The instance's exponent and dimension facts -/

/-- The pointer and offset of the first `load` of `x` among the atoms. -/
def ldOf (as : List Atom) (x : V) : Option (V × ℕ) :=
  as.findSome? fun
    | .load d p k => bif decide (d = x) then some (p, k) else none
    | _ => none

/-- **A top-level `load` of `x` through `p` at offset `k`** among the atoms: the first one (one scan per value, which
the kernel shares between a function's residuals). -/
def loadAt (as : List Atom) (x p : V) (k : ℕ) : Bool :=
  decide (ldOf as x = some (p, k))

/-- **The exponent fact of a value** (`Res.expFacts`): `x` a listed parameter of `fn` (offset `none`), or the word a
top-level `load` reads at a listed parameter's `[p]·g^k` (offset `some k`); the fact's bound. -/
noncomputable def expQ1 (fn : Fn) (x : V) : Option ℕ :=
  Res.expFacts.findSome? fun c ↦ if c.1 == fn.name then
    match fn.params[c.2.1]?, c.2.2.1 with
    | some p, none => if p = x then some c.2.2.2 else none
    | some p, some k => if loadAt (Res.topAtoms fn.body) x p k then some c.2.2.2 else none
    | none, _ => none
  else none

/-- **`check_opening_terminal`'s word `gmv = g^sl`, `sl ≤ 30`** (`Res.TermFront`): its parameter `19`. -/
def termGm (fn : Fn) (x : V) : Bool :=
  fn.name == name% «check_opening_terminal» && decide (fn.params[19]? = some x)

/-- **`verify_tables`' word `g_zc_n = g^n`, `n < 34`** (`EndExec.VtQ`): its value `2545`. -/
def vtZc (fn : Fn) (x : V) : Bool :=
  fn.name == name% «verify_tables» && decide (x = V.n 2545)

/-- **The exponent fact of a value**: `expQ1`, `check_opening_terminal`'s `gmv` (`termGm`), `verify_tables`'
`g_zc_n` (`vtZc`). -/
noncomputable def expQ0 (fn : Fn) (x : V) : Option ℕ :=
  match expQ1 fn x with
  | some b => some b
  | none => bif termGm fn x then some 31 else bif vtZc fn x then some 34 else none

/-- **The exponent fact of a value, of a top-level product** `x = a·w` of a value `a` of one (`expQ0`) and a
constant `g^c` (the bound, plus `c`), or of a top-level copy of such a value. -/
noncomputable def expQB (fn : Fn) (x : V) : Option ℕ :=
  match expQ0 fn x with
  | some b => some b
  | none => (Res.topAtoms fn.body).findSome? fun
    | .mul d a w => if d = x then
        match expQ0 fn a, (Res.constOf (Res.topAtoms fn.body) w).bind Res.powOf with
        | some b, some c => some (b + c)
        | _, _ => none
      else none
    | .copy d a => if d = x then expQ0 fn a else none
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

/-! ## Split `g`-powers -/

/-- **A function's `g`-power split from hinted bits** (`split`): `n = q^S·r`, on every returning path the monomial `q`
naming `g^a`, the selector `rv` and the monomial `r` naming `g^b`, `a < A`, `b < S`. -/
structure SplitC where
  q : List (ℕ × ℕ)
  r : List (ℕ × ℕ)
  rv : ℕ
  n : ℕ
  S : ℕ
  A : ℕ

/-- The splits: `rs_eq_run`'s `count = q^8·r` and `shared_selector_tables`' `len = q^4·r` (`EndExecCoreSplit`). -/
def splitsC : List (String × SplitC) :=
  [(name% «rs_eq_run», ⟨[(27, 1), (31, 1), (36, 1)], [(13, 1), (17, 1), (22, 1)], 23, 3, 8, 8⟩),
    (name% «shared_selector_tables», ⟨[(24, 1), (28, 1), (33, 1), (38, 1)], [(15, 1), (19, 1)], 20, 5, 4, 16⟩)]

/-- A monomial's bases to the `k`-th power. -/
def powB (k : ℕ) (bs : List (ℕ × ℕ)) : List (ℕ × ℕ) := bs.map fun p ↦ (p.1, k * p.2)

/-- **The residuals a split gives**, under the branch conditions `cs`: the exponent of `q·g^c`, `q^S·g^c` or `r·g^c`
below a constant past its largest; `q^S·g^c` below `n` under the arm `j > c` of `rv`; the stride-`S` run
`[b]·g^i·g^(S·[0, e(q)))`, `i < S`, inside `[b]·[0, e(n))`. -/
def splitRes (sp : SplitC) (cs : List CCond) : CRes → Bool
  | .lt (.mono c) (.num N) => decide (N < capE) &&
      ((decide (c.bases = sp.q) && decide (sp.A - 1 + c.off < N)) ||
        (decide (c.bases = powB sp.S sp.q) && decide (sp.S * (sp.A - 1) + c.off < N)) ||
        (decide (c.bases = sp.r) && decide (sp.S - 1 + c.off < N)))
  | .lt (.mono c) (.val n) => decide (n = sp.n) && decide (c.bases = powB sp.S sp.q) &&
      cs.any fun
        | .arm x j => decide (x = sp.rv) && decide (c.off < j) && decide (j < capE)
        | _ => false
  | .subR q r => decide (q.stride = sp.S) && decide (q.lo = .num 0) && decide (q.hi = .mono ⟨sp.q, 0⟩) &&
      decide (q.base.off < sp.S) && decide (r = ⟨⟨q.base.bases, 0⟩, 1, .num 0, .val sp.n⟩)
  | .under cs' r => splitRes sp (cs ++ cs') r
  | _ => false

/-- **A residual of a split** of the function (`splitsC`). -/
def splitFam (fn : Fn) (r : CRes) : Bool :=
  splitsC.any fun p ↦ fn.name == p.1 && splitRes p.2 [] r

/-- **`verify_tables`' reads past its table sumcheck's last record's cursor** (`vtSt`, the old route's `Res.vtStB` on
core names): the cell `c` words past the cursor, the value `2652`, `c < 153`, one of its stream's, parameter `20`'s
`[0, 8192)` (`EndExec.vtStC_inst`). -/
def vtStC (fn : Fn) : CRes → Bool
  | .sub c q => fn.name == name% «verify_tables» && decide (c.bases = [(2652, 1)]) && decide (c.off < 153) &&
      decide (q = ⟨⟨[(20, 1)], 0⟩, 1, .num 0, .num 8192⟩)
  | _ => false

/-- `verify_tables`' rank `r`'s group value from the side's first `v0` (`B1.Tables.vtRv`). -/
def vtRvC (v0 r : ℕ) : ℕ := if r = 0 then v0 else v0 + 13 + 20 * (r - 1)

/-- **`verify_tables`' sides**: each side's ranks' group values and the side's groups `[lo, hi)`. -/
def vtSides : List (List ℕ × ℕ × ℕ) :=
  [((List.range 9).map (vtRvC 112), 0, 9), ((List.range 6).map (vtRvC 409), 18, 24)]

/-- **`verify_tables`' buffers indexed by group, through its hinted order** (`vtPerm`, the old route's `vtGrpB` on
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

/-- **The slacks' words** (`vtexp.base`): `g_bus_mu` (`9`) `19 + a`, `g_zc_n` (`2545`) `19 + a - b`, `dims_g[0]` (`27`)
`19 + a - d`, `dims_g[1 + t]` (`28 + t`) `19 + a - b - c_t`; ghost `GB + j` as `27 + j`, `j < 7`. -/
def vtBaseN (x : ℕ) : Option VtL :=
  let y := if GB ≤ x ∧ x < GB + 7 then x - GB + 27 else x
  if y = 9 then some (19, [1, 0, 0, 0, 0, 0, 0, 0, 0])
  else if y = 2545 then some (19, [1, -1, 0, 0, 0, 0, 0, 0, 0])
  else if y = 27 then some (19, [1, 0, 0, 0, 0, 0, 0, 0, -1])
  else if 28 ≤ y ∧ y < 34 then some (19, (List.range 9).map fun i ↦
    if i = 0 then 1 else if i = 1 then -1 else if i = y - 26 then -1 else 0)
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
def vtNNB : List ℕ := [9, 27, 28, 29, 30, 31, 32, 33, 2545]

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
def vtGw : List (CCell × ℕ) := (List.range 7).map fun j ↦ (⟨[(10, 1)], j⟩, j)

/-- **The top-level atoms of `verify_tables` its exponent family reads** (`vtexp.ATOMS`; `EndExec.vtAtoms_top`). -/
def vtAtoms : List Atom :=
  [.const (.n 26) (word 1 0),
    .mul (.n 9) (.n 704) (.n 28),
    .mul (.n 9) (.n 713) (.n 29),
    .mul (.n 9) (.n 726) (.n 30),
    .mul (.n 9) (.n 739) (.n 31),
    .mul (.n 9) (.n 752) (.n 32),
    .mul (.n 9) (.n 765) (.n 33),
    .mul (.n 9) (.n 779) (.n 26),
    .mul (.n 9) (.n 795) (.n 27),
    .const (.n 821) (word 524288 0),
    .mul (.n 822) (.n 26) (.n 821),
    .mul (.n 9) (.n 823) (.n 822),
    .mul (.n 2545) (.n 2547) (.n 28),
    .mul (.n 2545) (.n 2932) (.n 28),
    .mul (.n 2545) (.n 3221) (.n 29),
    .mul (.n 2545) (.n 3394) (.n 30),
    .mul (.n 2545) (.n 3692) (.n 31),
    .mul (.n 2545) (.n 4021) (.n 32),
    .mul (.n 2545) (.n 5945) (.n 33)]

/-- **`verify_tables`' exponent family**, its ghost slots its `dims_g` words. -/
noncomputable def vtExp (fn : Fn) (gw : List (CCell × ℕ)) (r : CRes) : Bool :=
  fn.name == name% «verify_tables» && decide (gw = vtGw) && vtExpR vtAtoms [] r

/-! ## A range-checked index, `certify_placement`'s order, `verify_sub`'s exponents -/

/-- **`[B]·[J]·g^o` one of the points `[B]·g^(o + t)`, `t < N`**, `J` range checked below `g^N` at the top level
(`Res.rcBound`, `N ≤ 64`). -/
noncomputable def rcPtsAt (fn : Fn) (B J o : ℕ) (cs : List CCell) : Bool :=
  match Res.rcBound (Res.topAtoms fn.body) (V.n J) with
  | some N => decide (N ≤ 64) && (List.range N).all fun t ↦ cs.contains ⟨[(B, 1)], o + t⟩
  | none => false

/-- **A cell at a range-checked index among the points it can be** (`rcPtsAt`, either base the index). -/
noncomputable def rcPts (fn : Fn) : CRes → Bool
  | .subP c cs => match c.bases with
    | [(a, 1), (b, 1)] => rcPtsAt fn a b c.off cs || rcPtsAt fn b a c.off cs
    | _ => false
  | _ => false

/-- `certify_placement`'s ranks' group values (`B1.Tables.cpRB`). -/
def cpRanks : List ℕ := [138, 149, 167, 185, 203, 221, 239, 257, 275]

/-- **`certify_placement`'s `group_base[0 .. 9)` through its hinted order** (`cpPerm`, the old route's `Res.cpSub` on core
names): the cell `[137]·g^k`, `k < 9`, one of `[137]·[v]` over its ranks' groups (`EndExec.cpPerm_inst`). -/
def cpPerm (fn : Fn) : CRes → Bool
  | .subP c cs => fn.name == name% «certify_placement» && decide (c.bases = [(137, 1)]) && decide (c.off < 9) &&
      decide (cs = cpRanks.map fun v ↦ ⟨[(137, 1), (v, 1)], 0⟩)
  | _ => false

/-- **`verify_sub`'s values' exponent bounds** `(v, lo, hi)` (`EndExec.VsQ`): the tables' log-heights `dims[1..6]`
(values `86..91`, `583` the keccak table's again), the bus depth `253`, the table sumcheck's depth `579`, the stack's log
`276` and less `20`, `278`. -/
def vsPows : List (ℕ × ℕ × ℕ) :=
  [(86, 0, 30), (87, 0, 30), (88, 0, 30), (89, 0, 30), (90, 0, 30), (91, 9, 24), (583, 9, 24), (253, 20, 33),
    (579, 9, 33), (276, 20, 30), (278, 0, 10)]

/-- `verify_sub`'s products naming one of its values: `278 = 276·277`. -/
def vsMuls : List ((ℕ × ℕ) × ℕ) := [((276, 277), 278)]

/-- `verify_sub`'s orders `e(x) ≤ e(y) + c`. -/
def vsLes : List (ℕ × ℕ × ℕ) := [(91, 579, 0), (583, 579, 0), (276, 278, 20)]

/-- `verify_sub`'s cursors in its stream `[25]·[0, 8192)`, each with room for `207` words. -/
def vsCurs : List ℕ := [567, 578, 595]

/-- **An index as `verify_sub`'s value times `g^c`**: the value (a product of `vsMuls` naming it) and `c`. -/
def vsBase : CIdx → Option (ℕ × ℕ)
  | .num _ => none
  | .val x => some (x, 0)
  | .mono c => match c.bases with
    | [(x, 1)] => some (x, c.off)
    | [(a, 1), (b, 1)] => (vsMuls.lookup (a, b)).map fun x ↦ (x, c.off)
    | _ => none

/-- An index's exponent bounds by `vsPows`. -/
def vsIv (i : CIdx) : Option (ℕ × ℕ) :=
  match i with
  | .num n => some (n, n)
  | _ => (vsBase i).bind fun p ↦ (vsPows.lookup p.1).map fun b ↦ (b.1 + p.2, b.2 + p.2)

/-- **An order of `verify_sub`'s exponents** its bounds or orders decide. -/
def vsLt (a b : CIdx) : Bool :=
  match vsIv a, vsIv b with
  | some (_, ha), some (lb, hb) => decide (ha < capE) && decide (hb < capE) && (decide (ha < lb) ||
      match vsBase a, vsBase b with
      | some (x, ca), some (y, cb) => vsLes.any fun l ↦ decide (l.1 = x ∧ l.2.1 = y ∧ ca + l.2.2 < cb)
      | _, _ => false)
  | _, _ => false

/-- **`verify_sub`'s exponent family** (the old route's `Res.vsB` on core names): an order its bounds decide
(`vsLt`), a read `c < 207` words past a cursor inside its stream, either under branch conditions (`EndExec.vsExp_inst`). -/
def vsExp (fn : Fn) : CRes → Bool
  | .lt a b => fn.name == name% «verify_sub» && vsLt a b
  | .sub c q => fn.name == name% «verify_sub» && decide (q = ⟨⟨[(25, 1)], 0⟩, 1, .num 0, .num 8192⟩) &&
      (match c.bases with
        | [(x, 1)] => vsCurs.contains x
        | _ => false) && decide (c.off < 207)
  | .under _ r => vsExp fn r
  | _ => false

/-- `keccak_layer__L{first}`'s last record's cursor value (`EndExec.layer_cur`, `layOff first + 744`). -/
def layCur (fn : Fn) : Option ℕ :=
  bif fn.name == name% «keccak_layer__L0» then some 745 else bif fn.name == name% «keccak_layer__L1» then some 765 else none

/-- **`keccak_layer`'s family** (`EndExec.LayQ`): a read `c < 36` words past its last record's cursor, one of its
stream's, parameter `15`'s `[0, 8192)`; its pack rounds' words `e(9), e(10) < n`, `32 ≤ n`; either under branch
conditions (`EndExec.layQC_inst`). -/
def layQC (fn : Fn) : CRes → Bool
  | .sub c q => (layCur fn).any (fun v ↦ decide (c.bases = [(v, 1)])) && decide (c.off < 36) &&
      decide (q = ⟨⟨[(15, 1)], 0⟩, 1, .num 0, .num 8192⟩)
  | .lt (.val x) (.num n) => (layCur fn).isSome && (Nat.beq x 9 || Nat.beq x 10) && decide (32 ≤ n) &&
      decide (n < capE)
  | .under _ r => layQC fn r
  | _ => false

/-- **`verify_tables`' copy loop's read** (`EndExec.VtCQ`): `verify_tables_loop1`'s index `x·g^-1/i`, value `7`,
below its bound, parameter `1`, either under branch conditions (`EndExec.vtCp_inst`). -/
def vtCp (fn : Fn) : CRes → Bool
  | .lt a b => fn.name == name% «verify_tables_loop1» && decide (a = .val 7) && decide (b = .val 1)
  | .under _ r => vtCp fn r
  | _ => false

/-- **`da_pad`'s gap and `da_verify`'s blob count and gap** (`EndExec.DaPadQ`, `EndExec.daV_inst`): `da_pad`'s parameter
`2`, the gap `g^(DA_MAX_ROWS - n)` `da_verify` hands it, has an exponent below `m`, `DA_MAX_ROWS ≤ m`; `da_verify`'s value
`1`, the blob count `g^n`, below `m`, `DA_MAX_ROWS < m`, and its value `2`, the gap, below `m`, `DA_MAX_ROWS ≤ m`; either
under branch conditions (`EndExec.daGap_inst`). -/
def daGap (fn : Fn) : CRes → Bool
  | .lt a b => match b with
    | .num m => decide (m < capE) &&
        ((fn.name == name% «da_pad» && decide (a = .val 2) && decide (guest_const% DA_MAX_ROWS ≤ m)) ||
          (fn.name == name% «da_verify» && ((decide (a = .val 1) && decide (guest_const% DA_MAX_ROWS < m)) ||
            (decide (a = .val 2) && decide (guest_const% DA_MAX_ROWS ≤ m)))))
    | _ => false
  | .under _ r => daGap fn r
  | _ => false

/-- The value `p` the first top-level `load x p 0` reads `x` through. -/
def ldAt (as : List Atom) (x : ℕ) : Option ℕ := as.findSome? fun
  | .load v p 0 => match vnum v, vnum p with
    | some x', some p' => bif Nat.beq x' x then some p' else none
    | _, _ => none
  | _ => none

/-- The factors `(a, b)` of the first top-level `mul p a b`. -/
def mulAt (as : List Atom) (p : ℕ) : Option (ℕ × ℕ) := as.findSome? fun
  | .mul d a b => match vnum d, vnum a, vnum b with
    | some p', some a', some b' => bif Nat.beq p' p then some (a', b') else none
    | _, _, _ => none
  | _ => none

/-- The value `c` the first top-level `load c T t` stores at `T·g^t`. -/
def stAt (as : List Atom) (T t : ℕ) : Option ℕ := as.findSome? fun
  | .load v p o => match vnum v, vnum p with
    | some c, some T' => bif Nat.beq T' T && Nat.beq o t then some c else none
    | _, _ => none
  | _ => none

/-- **A table read** (`rcTab`): `x` loaded at offset `0` through a top-level product `T·J`, `J` range checked below
`g^N`: `(T, J, N)`. -/
noncomputable def tabOf (fn : Fn) (x : ℕ) : Option (ℕ × ℕ × ℕ) :=
  let as := Res.topAtoms fn.body
  (ldAt as x).bind fun p ↦ (mulAt as p).bind fun tj ↦ (Res.rcBound as (V.n tj.2)).map fun N ↦ (tj.1, tj.2, N)

/-- **A table's row `t`**: the exponent `k` of the top-level constant `g^k` a top-level `load` stores at `T·g^t`. -/
noncomputable def tabK (fn : Fn) (T t : ℕ) : Option ℕ :=
  let as := Res.topAtoms fn.body
  (stAt as T t).bind fun c ↦ (Res.constOf as (V.n c)).bind Res.powOf1

/-- An index's exponent at a table's row `t`: the read `x` at `k`, the index `J` at `t`, constants as they are. -/
def tabEv (x J t k : ℕ) : CIdx → Option ℕ
  | .num n => some n
  | .val v => bif Nat.beq v x then some k else bif Nat.beq v J then some t else none
  | .mono c => c.bases.foldr (fun b acc ↦ acc.bind fun a ↦
      (bif Nat.beq b.1 x then some (b.2 * k) else bif Nat.beq b.1 J then some (b.2 * t) else none).map (a + ·))
      (some c.off)

/-- **A range-checked table read's order** (`rcTab`): an order over a table read `x` (`tabOf`), its index and
constants, at every row of the table, either under branch conditions (`EndExec.rcTab_inst`). -/
noncomputable def rcTab (fn : Fn) : CRes → Bool
  | .lt a b => (a.vals ++ b.vals).any fun x ↦ match tabOf fn x with
    | some (T, J, N) => (List.range N).all fun t ↦ match tabK fn T t with
      | some k => match tabEv x J t k a, tabEv x J t k b with
        | some u, some v => decide (u < v) && decide (v < capE)
        | _, _ => false
      | none => false
    | none => false
  | .under _ r => rcTab fn r
  | _ => false

/-- `verify_keccak`'s layers' returned cursors, step `s`'s at index `s` (`EndExec.vk_rets`). -/
def vkCurs : List ℕ := [489, 524, 558, 601, 642, 685, 718, 759, 797, 840, 881, 921]

/-- The order of `g`: exponents are taken modulo it. -/
def gOrd : ℕ := 2 ^ 64 - 1

/-- **`verify_keccak`'s values' exponents at `τ`** (`EndExec.vk_exps`), `y = τ - 3`: `tau_g`, `g^-4` (modulo the
order), `pack_g`, `y_g`, the pack rounds' step `g^(y / 8)` and remainder `g^(y % 8)`, and their bits' factors. -/
def vkTab (τ : ℕ) : List (ℕ × ℕ) :=
  [(6, τ), (18, gOrd - 4), (19, τ - 4), (21, τ - 3), (35, (τ - 3) / 8), (49, (τ - 3) % 8), (30, (τ - 3) / 8 % 2),
    (34, 2 * ((τ - 3) / 16 % 2)), (39, (τ - 3) % 2), (43, 2 * ((τ - 3) / 2 % 2)), (48, 4 * ((τ - 3) / 4 % 2))]

/-- A value's exponent at `τ` (`vkTab`). -/
def vkE (τ v : ℕ) : Option ℕ := (vkTab τ).lookup v

/-- **A cell's exponent at `τ`**, its bases all of `vkE`'s, modulo the order. -/
def vkEv (τ : ℕ) (c : CCell) : Option ℕ :=
  (c.bases.foldr (fun b acc ↦ acc.bind fun a ↦ (vkE τ b.1).map fun e ↦ a + b.2 * e) (some c.off)).map (· % gOrd)

/-- A cell's bases `vkE` does not know, in order. -/
def vkU (τ : ℕ) (c : CCell) : List (ℕ × ℕ) := c.bases.filter fun b ↦ (vkE τ b.1).isNone

/-- A cell's part `vkE` knows. -/
def vkK (τ : ℕ) (c : CCell) : CCell := ⟨c.bases.filter fun b ↦ (vkE τ b.1).isSome, c.off⟩

/-- **A run inside a run at `τ`**, the known parts' and bounds' exponents given: the same bases `vkE` does not know,
each cell `kq + S·j` of the first, `lq ≤ j < hq`, a cell `kr + S'·j'` of the second, `lr ≤ j' < hr`. -/
def vkRun (τ : ℕ) (q r : CRun) (kq kr lq hq lr hr : ℕ) : Bool :=
  decide (vkU τ q.base = vkU τ r.base) && Nat.blt 0 r.stride && decide (hq < capE) &&
    decide (kq + q.stride * hq < capE) && decide (hr < capE) &&
    (List.range (hq - lq)).all fun t ↦
      decide (kr ≤ kq + q.stride * (lq + t)) && Nat.beq ((kq + q.stride * (lq + t) - kr) % r.stride) 0 &&
      decide (lr ≤ (kq + q.stride * (lq + t) - kr) / r.stride) &&
      decide ((kq + q.stride * (lq + t) - kr) / r.stride < hr)

/-- **A residual at `τ`**: an order of exponents `vkE` gives; a run inside a run (`vkRun`); either under branch
conditions. -/
def vkAt (τ : ℕ) : CRes → Bool
  | .lt a b => ((vkEv τ (idxC a)).bind fun u ↦ (vkEv τ (idxC b)).map fun v ↦
      decide (u < v) && decide (v < capE)).getD false
  | .subR q r => ((vkEv τ (vkK τ q.base)).bind fun kq ↦ (vkEv τ (vkK τ r.base)).bind fun kr ↦
      (vkEv τ (idxC q.lo)).bind fun lq ↦ (vkEv τ (idxC q.hi)).bind fun hq ↦ (vkEv τ (idxC r.lo)).bind fun lr ↦
      (vkEv τ (idxC r.hi)).map fun hr ↦ vkRun τ q r kq kr lq hq lr hr).getD false
  | .under _ r => vkAt τ r
  | _ => false

/-- **`verify_keccak`'s family** (`EndExec.vkQC_inst`): a read `c < (11 - s)·96 + 97` words past step `s`'s returned
cursor (`vkCurs`), one of its stream's, parameter `12`'s `[0, 8192)`; else a residual that holds at every `τ` of
`[9, 28]` (`vkAt`); either under branch conditions. -/
def vkQC (fn : Fn) : CRes → Bool
  | .sub c q => fn.name == name% «verify_keccak» && decide (q = ⟨⟨[(12, 1)], 0⟩, 1, .num 0, .num 8192⟩) &&
      match c.bases with
      | [(x, 1)] => (List.range 12).any fun s ↦ Nat.beq (vkCurs.getD s 0) x && decide (c.off < (11 - s) * 96 + 97)
      | _ => false
  | .under _ r => vkQC fn r
  | r => fn.name == name% «verify_keccak» && (List.range 20).all fun i ↦ vkAt (9 + i) r

/-- **`verify_bus_gkr`'s layer loop's family** (`EndExec.LyQ`, `EndExec.ly_curs`): a read `c < 8` words past the cursor
its pairs end at (value `65`), or `c < 12` past its last record's (value `80`), one of its stream's, parameter `9`'s
`[0, 8192)`, either under branch conditions (`EndExec.lyQC_inst`). -/
def lyQC (fn : Fn) : CRes → Bool
  | .sub c q => fn.name == name% «verify_bus_gkr_loop0» && decide (q = ⟨⟨[(9, 1)], 0⟩, 1, .num 0, .num 8192⟩) &&
      ((decide (c.bases = [(65, 1)]) && decide (c.off < 8)) || (decide (c.bases = [(80, 1)]) && decide (c.off < 12)))
  | .under _ r => lyQC fn r
  | _ => false

/-- **A residual of a family**, ghost-free (`resFam`, `resQ`, `splitFam`, `vtStC`, `vtPerm`, `rcPts`, `cpPerm`,
`vsExp`, `layQC`, `vtCp`, `daGap`, `rcTab`, `vkQC`, `lyQC`, its values below `GB`), or the ghost families `ml`, `st`
and `verify_tables`' exponent family. -/
noncomputable def resFamG (fn : Fn) (xc : List ℕ) (gw : List (CCell × ℕ)) (r : CRes) : Bool :=
  ((resFam fn xc r || resQ fn r || splitFam fn r || vtStC fn r || vtPerm fn r || rcPts fn r || cpPerm fn r ||
      vsExp fn r || layQC fn r || vtCp fn r || daGap fn r || rcTab fn r || vkQC fn r || lyQC fn r) &&
      r.vals.all (Nat.blt · GB)) ||
    mlSub fn r || stSub fn r || cmSub fn r || vtExp fn gw r

/-- **Every residual of the function's heap certificate of a family.** -/
noncomputable def resOk (Cf : CFun) : Bool := Cf.H.res.all (resFamG Cf.fn Cf.xc Cf.H.sig.gw)

/-- **The ghost family's links** (`ml`): `child_claim_list_mono_last__L{k}`'s caller's cell `2` (its entries
table) its one ghost slot, after its four parameters, and cell `5` its parameter `3` (`limit`); it names no
ghost value. -/
noncomputable def mlGl (Cf : CFun) : Bool :=
  (mlK Cf.fn).isSome && decide (Cf.gl = [(2, 4, 0), (5, 3, 0)]) && Nat.beq Cf.H.sig.ghosts 1 && ngB Cf.fn

/-- **A loop callee of `anyLink`'s links**: its caller's cell `2` its entries parameter, cell `5` its bound parameter
times `g` (`anyLink`'s), its caller's frame address its one ghost slot, after its parameters; it names no ghost
value. -/
noncomputable def alGl (Cf : CFun) : Bool :=
  Res.anyLink.fams.any (fun F ↦ Cf.fn.name == F.1 &&
    decide (Cf.gl = [(2, F.2.1, 0), (5, F.2.2, 1), (0, Cf.fn.params.length, 0)])) &&
    Nat.beq Cf.H.sig.ghosts 1 && ngB Cf.fn && Cf.H.sig.gw.isEmpty

/-- **Own parameter words as the ghost slots** (`HSig.gw`): ghost `j` the word at the `j`-th cell, one per ghost, over
values below `GB`, and the function naming no ghost value (`ngB`). -/
def gwSlots (Cf : CFun) : Bool :=
  Nat.beq Cf.H.sig.ghosts Cf.H.sig.gw.length && decide (Cf.H.sig.gw.map (·.2) = List.range Cf.H.sig.gw.length) &&
    (Cf.H.sig.gw.all fun x ↦ x.1.bases.all fun b ↦ Nat.blt b.1 GB) && ngB Cf.fn

/-- **An instance's ghost words, its own parameter words** (`gwSlots`): ghost `j` the reference's word at the `j`-th
cell's address at `σ` (`setG`), `GwR`. -/
theorem gwR_setG {κ : ℕ} {img : MemoryImage κ} {Cf : CFun} {σ : Val} (h : gwSlots Cf = true) :
    GwR img Cf.H.sig (setG σ (Cf.H.sig.gw.map fun x ↦ (img.read (x.1.addrW (vw σ))).getD 0)) := by
  intro c j hc
  simp only [gwSlots, Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq, List.all_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨hgh, hix⟩, hlt⟩, -⟩ := h
  obtain ⟨i, hi, hci⟩ := List.getElem_of_mem hc
  have hij : j = i := by
    have h1 := congrArg (·[i]?) hix
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi, hci, Option.map_some] at h1
    rw [List.getElem?_range hi] at h1
    exact Option.some.inj h1
  subst hij
  have haddr : c.addrW (vw (setG σ (Cf.H.sig.gw.map fun x ↦ (img.read (x.1.addrW (vw σ))).getD 0))) =
      c.addrW (vw σ) := by
    unfold CCell.addrW
    rw [valW_congr fun b hb ↦ ?_]
    exact setG_eq (show (V.n b.1).idx < GB from hlt (c, j) hc b hb)
  rw [haddr]
  have hO := ownG_setG (G := Cf.H.sig) (σ := σ)
    (gw := Cf.H.sig.gw.map fun x ↦ (img.read (x.1.addrW (vw σ))).getD 0) (by rw [List.length_map, hgh])
  have hj : j < Cf.H.sig.ghosts := by rw [hgh]; exact hi
  have h2 := congrArg (·[j]?) hO
  simp only [ownG, List.getElem?_map, List.getElem?_range hj, Option.map_some, List.getElem?_eq_getElem hi,
    hci] at h2
  exact Option.some.inj h2

/-- **The caller's cells linked** (`CFun.gl`), of a family: none, or those of a callee of `anyLink` (a read of
its caller's entries table, `Res.LinkDefs`): the caller's cell `2` its entries parameter, cell `5` its bound
parameter times `g`, with no ghost slot, or for a loop the same and its caller's frame address its one ghost slot
(`alGl`); for `child_claim_list_mono_last__L{k}` the ghost family's (`mlGl`); for a stream-cursor loop its caller's
stream and frame (`stGl`); for `child_claim_list_mono`'s frame loops its caller's entries, bound and frame (`cmGl`); or
none, the ghost slots own parameter words (`gwSlots`). -/
noncomputable def glOk (Cf : CFun) : Bool :=
  bif (cmK Cf.fn).isSome then cmGl Cf && Cf.H.sig.gw.isEmpty else
  bif (stK Cf.fn).isSome then stGl Cf && Cf.H.sig.gw.isEmpty else
  bif (mlK Cf.fn).isSome then mlGl Cf && Cf.H.sig.gw.isEmpty else
    ((Cf.gl.isEmpty || Res.anyLink.fams.any fun F ↦ Cf.fn.name == F.1 && decide (Cf.gl = [(2, F.2.1, 0), (5, F.2.2, 1)]))
      && Nat.beq Cf.H.sig.ghosts 0 && Cf.H.sig.gw.isEmpty) || (Cf.gl.isEmpty && gwSlots Cf) || alGl Cf

theorem resOk_nil {Cf : CFun} (h : Cf.H.res = []) : resOk Cf = true := by
  simp [resOk, h]

end

end LeanVM.Guest.CoreMode
