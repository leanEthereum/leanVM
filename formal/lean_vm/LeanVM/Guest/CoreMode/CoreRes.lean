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
public import LeanVM.Guest.CoreMode.Gen.FnData
import LeanVM.Guest.Data.Consts

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
* `addr`: the same, `x = g^e` with `e` at most a bound `expM` reads off the top-level atoms: products of
  addresses dereferenced, bits' powers and constant powers of `g`; and `e(Π xᵢ^aᵢ·g^off) < n` from such bounds `Mᵢ`,
  `Σ aᵢ·Mᵢ + off < n` (`topProd`);
* `rcv`: `e(x) < e(p·g)` (`.lt (.val x) (.mono ⟨[(p, 1)], 1⟩)`), the value `x` range checked against the value
  `p` among the top-level atoms;
* `rcn`: `e(x) < e(p)` (`.lt (.val x) (.val p)`), the value `x` range checked against `k = p·w`, `w` the constant
  `g⁻¹`, among the top-level atoms;
* `under g r`: a residual of a family, the branch conditions `g` aside.
* `split` (`splitRes`): a function's `g`-power `n = q^S·r` split from hinted bits (its own family, `Fn/<f>/Fam.lean`),
  from the bits' booleanity on its path (`EndExecCoreSplit`): exponent bounds of `q`, `q^S` and `r` times constants, of
  `q^S·g^c` below `n` under an arm `j > c` of the selector `r`, and the loop's strided runs below `e(q)` inside
  `[0, e(n))`.
* `neg` (`negFam`): under a condition `k ≠ 0`, `e(x·v·g^off) < n`, `v` the constant `g⁻¹` of the arm `k ≠ 0` takes,
  `k = y + g^off`, `y = x·g^off` (so `x ≠ 1`), `x` and `y` range checked, `y` below `g^(n + 1)`; and
  `e(Π xᵢ^aᵢ·g^off) < n` from the arm `k ≠ 0` takes (`nzAtoms`, `armM`): each `xᵢ = g^eᵢ`, `eᵢ ≤ Mᵢ`, `xᵢ` range
  checked there against a constant `g^Mᵢ` (`Res.rcBound`) or `Mᵢ` a bound `expM` reads off that arm's atoms (a `DEREF`
  through `xᵢ`, `assert_gpow`), `Σ aᵢ·Mᵢ + off < n`.

These name no ghost value (`CRes.vals`, below `GB`), so they hold at an honest valuation whatever its
ghost words (`CRes.holds_congr`). One family names a ghost:
* `ml` (`mlSub`): a ghost family specialization's read of claim `jj`'s entry `[ent]·Π[gap_i]^4·g^(4jj+d)` lies in
  its caller's table, the run `[ghost₀]·g^(4j+d)` below the exponent of its parameter `limit` (its ghost the caller's
  cell `2`, `glOk`), its shape and its soundness its function's own (`FnReg.mlLoops`, `EndExec.MlLoopOk`).
* `st` (`stSub`): a loop's read `[cur]·g^c` past its cursor `cur` lies in its caller's proof stream, the run
  `[ghost₀]·[0, 8192)` (its ghosts the caller's stream and frame, `stGl`)
  (`EndExecCoreSt`).

Each function's own families, read off its own data, are in its own modules (`CoreMode/Fn/<f>/Fam.lean`, registered in
`FnReg.fams`, `FnReg.gwFams`, `CoreMode/FnReg.lean`); `resOk Cf` (`CoreResG.lean`): every residual of `Cf`'s heap
certificate of a family (`resFamG`). `CfOk` asks it, so the core route's honest valuations (`HonF.res`) make the
residuals true.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

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

/-- **An exponent bound of a product `Π xᵢ^aᵢ`** from the top-level atoms: `Σ aᵢ·Mᵢ` (`expM`). -/
noncomputable def topProd (fn : Fn) : List (ℕ × ℕ) → Option ℕ
  | [] => some 0
  | (x, a) :: bs => (expM (Res.topAtoms fn.body) expFuel (V.n x)).bind fun M ↦ (topProd fn bs).map (a * M + ·)

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
dereferences (`exp`, a bound `≥ 2^28`), or such a residual under branch conditions. -/
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
  | .lt (.mono c) (.num n) => (match c.bases with
    | [(x, 1)] => decide (n < capE) &&
        ((Res.topSels fn.body).any (fun p ↦ decide (p.1 = V.n x) && decide (p.2 + c.off ≤ n)) ||
          match Res.rcBound (Res.topAtoms fn.body) (V.n x) with
          | some N => decide (N + c.off ≤ n)
          | none => false)
    | _ => false) || (decide (n < capE) && (topProd fn c.bases).any (· + c.off < n))
  | .lt (.num j) (.mono c) => match c.bases with
    | [(x, 1)] => decide (j < c.off) &&
        (Res.topSels fn.body).any fun p ↦ decide (p.1 = V.n x) && decide (p.2 + c.off < capE)
    | _ => false
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

/-- A ghost family specialization's `(k, ent, gap, stride, limit, links)` (`FnReg.mlLoops`). -/
def mlK (fn : Fn) : Option (ℕ × ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ)) := FnReg.mlLoops.lookup fn.name

/-- **A ghost family specialization's read of claim `jj`'s entry in its caller's table** (`ml`): the cell
`[ent]·Π_{i ≤ jj}[gap + stride·i]^4·g^(4jj+d)`, `jj < k`, a cell of the run `[ghost₀]·g^(4j+d)`, `j` below the
exponent of the parameter `limit`. -/
def mlSub (fn : Fn) : CRes → Bool
  | .sub c q => (mlK fn).any fun p ↦ Nat.blt (c.off / 4) p.1 &&
      decide (q = ⟨⟨[(GB, 1)], c.off % 4⟩, 4, .num 0, .val p.2.2.2.2.1⟩) &&
      decide (c.bases = (p.2.1, 1) :: (List.range (c.off / 4 + 1)).map fun i ↦ (p.2.2.1 + p.2.2.2.1 * i, 4))
  | _ => false

/-! ## The proof stream's cursor loops -/

/-- **The loops reading the proof stream past a cursor** (`st`): `(name, D, v, S)`, a loop whose caller's cell `D`
holds the stream, whose body loads the cursor `v`, reading at most `S` words past it an iteration; each its function's
own (`FnReg.stLoops`). -/
def stLoops : List (String × ℕ × ℕ × ℕ) := FnReg.stLoops

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

/-- **The frame loops over a caller's table** (`cm`): their `(m, ent, gap, stride, cells)`, `m` claims a frame, the
caller's cells linked (`FnReg.cmLoops`). -/
def cmK (fn : Fn) : Option (ℕ × ℕ × ℕ × ℕ × List ℕ) := FnReg.cmLoops.lookup fn.name

/-- **A frame loop's read of claim `jj`'s entry in its caller's table** (`cm`): the cell
`[ent]·Π_{i ≤ jj}[gap + stride·i]^4·g^(4jj+d)`, `jj < m`, a cell of the run `[ghost₀]·g^(4j+d)`, `j` below the
exponent of `ghost₁` (its caller's `limit`); and that exponent's existence. -/
def cmSub (fn : Fn) : CRes → Bool
  | .sub c q => (cmK fn).any fun p ↦ Nat.blt (c.off / 4) p.1 &&
      decide (q = ⟨⟨[(GB, 1)], c.off % 4⟩, 4, .num 0, .val (GB + 1)⟩) &&
      decide (c.bases = (p.2.1, 1) :: (List.range (c.off / 4 + 1)).map fun i ↦ (p.2.2.1 + p.2.2.2.1 * i, 4))
  | .lt a b => (cmK fn).isSome && decide (a = .num 0) && decide (b = .val (GB + 1))
  | _ => false

/-- **A frame loop's links**: its caller's cells (`cmK`: the entries, `limit`) to its first two ghost slots, the
caller's frame address to its third (`loopGl`); it names no ghost value. -/
def cmGl (Cf : CFun) : Bool :=
  (cmK Cf.fn).any (fun p ↦ decide (Cf.gl = loopGl Cf.fn.params.length p.2.2.2.2)) && Nat.beq Cf.H.sig.ghosts 3 &&
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

/-- **The exponent fact of a listed value** (`FnReg.expVals`, each its function's own): its bound. -/
def expVal (fn : Fn) (x : V) : Option ℕ :=
  FnReg.expVals.findSome? fun c ↦ bif c.1 == fn.name && decide (x = V.n c.2.1) then some c.2.2 else none

/-- **The exponent fact of a value**: `expQ1`, or a listed value's (`expVal`). -/
noncomputable def expQ0 (fn : Fn) (x : V) : Option ℕ :=
  match expQ1 fn x with
  | some b => some b
  | none => expVal fn x

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
`Res.dimFacts`): a value of an exponent fact (`expQB`), times `g^c`, below
a constant, or a constant `g^k`, `k < c`, below it times `g^c`; a word of a dimension fact times `g^t` below its
bound parameter times `g^u` (`dimLt`); either under branch conditions. -/
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
  | .under _ r => resQ fn r
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

/-- An index's exponent, each value's exponent `ev` gives, constants as they are. -/
def tabEv (ev : ℕ → Option ℕ) : CIdx → Option ℕ
  | .num n => some n
  | .val v => ev v
  | .mono c => c.bases.foldr (fun b acc ↦ acc.bind fun a ↦ (ev b.1).map (b.2 * · + a)) (some c.off)

/-- **The exponents at a table's row `t`** over the index `J`: `J`'s is `t`, a table read over `J` (`tabOf`) the
row's entry of its table (`tabK`). -/
noncomputable def tabRowEv (fn : Fn) (J t v : ℕ) : Option ℕ :=
  bif Nat.beq v J then some t else match tabOf fn v with
    | some (T, J', _) => bif Nat.beq J' J then tabK fn T t else none
    | none => none

/-- **A range-checked table read's order** (`rcTab`): an order over table reads of one index (`tabOf`), the index and
constants, at every row of the first read's table (`tabRowEv`), either under branch conditions
(`EndExec.rcTab_inst`). -/
noncomputable def rcTab (fn : Fn) : CRes → Bool
  | .lt a b => (a.vals ++ b.vals).any fun x ↦ match tabOf fn x with
    | some (_, J, N) => (List.range N).all fun t ↦
      match tabEv (tabRowEv fn J t) a, tabEv (tabRowEv fn J t) b with
      | some u, some v => decide (u < v) && decide (v < capE)
      | _, _ => false
    | none => false
  | .under _ r => rcTab fn r
  | _ => false

end

end LeanVM.Guest.CoreMode
