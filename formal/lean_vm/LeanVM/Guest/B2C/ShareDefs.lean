/-
  LeanVM.Guest.B2C.ShareDefs

  The definitions the sharing check evaluates and its consumers share: bit sets, keys' input
  cells, the certificate's lists of fixed cells, temporaries and frame runs, the cells kept apart.
-/

module

public import LeanVM.Guest.B2C.CplCheck
public import LeanVM.Guest.B2C.KernelList

/-!
# The sharing check's definitions

Bit sets (`bitN`, `setBit`, `bitsOf`); a key's input cells (`keyCells`, `packCells`, `keccakOp`);
the certificate's lists (`listsOk`: the fixed cells, temporaries and frame runs in the frame, one
value per cell; `listed`, `listedT`); the cells kept apart (`apart`, `bitsNodup`, `siteCells`).
Their facts are in `ShareFacts`, so that an edit of a proof rebuilds none of the kernel's checks.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check

@[expose] public section

/-! ## Bit sets -/

/-- Bit `n` of `s`. -/
def bitN (s n : ℕ) : Bool := Nat.beq (Nat.mod (Nat.shiftRight s n) 2) 1

/-- `s` with bit `n` set. -/
def setBit (s n : ℕ) : ℕ := Nat.lor s (Nat.shiftLeft 1 n)

/-- The bit set of a list. -/
def bitsOf (l : List ℕ) : ℕ := l.foldl setBit 0

/-- The cells of a list packed, cell `m` in the `m`-th base-`2^16` digit. -/
def packCells : List ℕ → ℕ
  | [] => 0
  | c :: cs => Nat.add c (Nat.mul (packCells cs) 65536)

/-! ## Atoms -/

/-- The key of written cell `k` of a `KECCAK` in the layouts `inOdd`, `outOdd`: `4` to `55` for
`k < 13`. -/
def keccakOp (k : ℕ) (inOdd outOdd : Bool) : ℕ := 4 + 4 * k + 2 * inOdd.toNat + outOdd.toNat

/-- A key's input cells, a sum's and a product's two in order. -/
def keyCells (op : ℕ) (cs : List ℕ) : List ℕ :=
  match op, cs with
  | 0, [a, b] => bif Nat.ble a b then [a, b] else [b, a]
  | 1, [a, b] => bif Nat.ble a b then [a, b] else [b, a]
  | _, cs => cs

/-! ## What the certificate lists -/

/-- The certificate lists a value with its cell. -/
noncomputable def listed (l : List (ℕ × ℕ)) (v : V) (c : ℕ) : Bool :=
  v == V.n v.idx && l.any fun p ↦ Nat.beq p.1 v.idx && Nat.beq p.2 c

/-- The certificate lists a temporary with its cell: `tt` is its temporaries by cell. -/
noncomputable def listedT (tt : Trie ℕ) (v : V) (c : ℕ) : Bool :=
  v == V.n v.idx && getF tt c == some v.idx

/-- The fixed cells' constants, by cell. -/
noncomputable def statCst (P : Plumb) : Trie (ℕ × ℕ) :=
  P.stat.foldl (fun t q ↦ match q.2 with
    | .k a b => setF (a, b) envDepth t q.1
    | .fpg _ => t) .nil

/-- The temporaries' cells. -/
noncomputable def tmpCells (P : Plumb) : ℕ := bitsOf (P.tmps.map Prod.snd)

/-- The fixed cells holding a frame pointer product. -/
noncomputable def fpgCells (P : Plumb) : ℕ :=
  bitsOf (P.stat.filterMap fun q ↦ match q.2 with
    | .fpg _ => some q.1
    | .k .. => none)

/-- The cells a list of `(value, cell)` pairs gives, by cell. -/
noncomputable def byCell (l : List (ℕ × ℕ)) : Trie ℕ := l.foldl (fun t p ↦ setF p.1 envDepth t p.2) .nil

/-- A list of `(value, cell)` pairs with one value per cell, the cells in `[2, n)`. -/
noncomputable def pairsOk (l : List (ℕ × ℕ)) (n : ℕ) : Bool :=
  (byCell l).seq fun t ↦ l.all fun p ↦ getF t p.2 == some p.1 && Nat.ble 2 p.2 && Nat.blt p.2 n

/-- The certificate's lists: the fixed cells as the walk starts with them, in the frame; the
temporaries' and runs' cells one value each, apart; the call sites' and table targets' cells in
the frame; no table selector a temporary. -/
noncomputable def listsOk (P : Plumb) (n : ℕ) : Bool :=
  (statCst P).seq fun cst ↦ natSeq (tmpCells P) fun tc ↦
  P.stat.all (fun q ↦ Nat.ble 2 q.1 && Nat.blt q.1 n && match q.2 with
    | .k a b => getF cst q.1 == some (a, b)
    | .fpg _ => true) &&
  pairsOk P.tmps n && pairsOk P.runs n && P.runs.all (fun p ↦ !bitN tc p.2) &&
  P.sites.all (fun s ↦ Nat.ble 2 s.q && Nat.blt s.q n) &&
  P.arms.all (fun a ↦ Nat.ble 2 a.2.1 && Nat.blt a.2.1 n && !(P.tmps.any fun p ↦ Nat.beq p.1 a.1))

/-- `s` has none of `t`'s bits. -/
def apart (s t : ℕ) : Bool := Nat.beq (Nat.land s t) 0

/-- No cell twice, `s` the cells seen. -/
def bitsNodup : List ℕ → ℕ → Bool
  | [], _ => true
  | c :: cs, s => !bitN s c && bitsNodup cs (setBit s c)

/-- The cells of the call sites: the callee frame pointers' and the fused dispatches' targets. -/
def siteCells (P : Plumb) : List ℕ := P.sites.flatMap fun s ↦ s.q :: (bif Nat.beq s.tgt 0 then [] else [s.tgt])

end
end LeanVM.Guest.B2C
