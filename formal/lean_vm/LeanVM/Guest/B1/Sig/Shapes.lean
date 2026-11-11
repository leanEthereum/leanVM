/-
  LeanVM.Guest.B1.Sig.Shapes

  The statement shapes the signature verifiers' templates are written in, and the compiler's
  lowering of a Keccak message (`emit_keccak_message`) as a template.
-/

module

public import LeanVM.Guest.B1.Sig.Decide

/-!
# Statement shapes and the Keccak message

A template writes out the statements of a guest construct with its values `V.n k` numbered from a
base `b`, in the order of their first occurrence, as `Fn.renumber` numbers them. The `…Data`
modules prove the guest's core IR equal to the templates by kernel evaluation.

`kMsg pad cells len tailRun out b` is the compiler's `emit_keccak_message`
(`crates/lean_compiler/src/lower/builtins.rs:275-335` at leanVM main `40f877dc`,
`Expand.emitKeccakMessage`) from the zero state with `len=` given: the message cells (`KC`: a
literal zero, a constant, a value) zero-extended
to the last block's read, `0x01` XORed into byte `len` and `0x80` into the last block's last byte
(`xor_byte`: a constant folded, a value by one `XOR` with a constant cell), then one `KECCAK` per
block of `136` bytes, block `k` reading the nine cells from `17k/2`: from the zero state the cells
themselves (`spongeCell`: a zero is the padding run's `0`, the constant `0x01` its `1`, another
constant a fresh cell) and a run for the tail (`spongeRun`: the cells if they are one run
(`tailRun`), a window of the padding run, or a fresh copy); after it the previous output XORed with
them (`spongeXor`). `pad` is the base of the padding run `[0x01, 0, 0, 0, 0]` the function set
before; `out` the last output run if it exists already, else it is fresh after the last block's
inputs.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-! ## Statement shapes -/

def cst (b : Nat) (c : E) : Stmt := .atom (.const (.n b) c)
def hintW (s : String) (vs : List V) : Stmt := .atom (.hint (.witness s (.stack vs)))
def addS (d a b : V) : Stmt := .atom (.add d a b)
def mulS (d a b : V) : Stmt := .atom (.mul d a b)
def copyS (d s : V) : Stmt := .atom (.copy d s)
def loadS (d p : V) (off : Nat) : Stmt := .atom (.load d p off)
def kecS (ins outs : List V) (inOdd outOdd : Bool) : Stmt := .atom (.keccak ins outs inOdd outOdd)

/-- `n` consecutive values from `o`. -/
def runV (o n : Nat) : List V := (List.range n).map fun k => .n (o + k)

/-- The range check `log x < k` against the word `bound = g^(k-1)` at `b`, its witnesses from
`b + 1`. -/
def rangeS (x : V) (bound : E) (b : Nat) : List Stmt :=
  [cst b bound, .atom (.rangeCheck x (.n (b + 1)) (.n (b + 2)) (.n (b + 3)) (.n b))]

/-- Bits pinned Boolean: `x = x · x` for each. -/
def booleans (base n : Nat) : List Stmt :=
  (List.range n).map fun j => mulS (.n (base + j)) (.n (base + j)) (.n (base + j))

/-- `shifts(bits, 0, n, out)` (`lean_ethereum.py:3499-3505`): out `l` at `outBase + 3·(n - 1 - l)`,
over the bits from `bitBase`. -/
def shifts (bitBase n outBase : Nat) : List Stmt :=
  copyS (.n outBase) (.n (bitBase + n - 1)) ::
  (List.range (n - 1)).flatMap fun r' => let r := r' + 1;
    [cst (outBase + 3 * r - 2) (word 2 0),
      mulS (.n (outBase + 3 * r - 1)) (.n (outBase + 3 * r - 2)) (.n (outBase + 3 * r - 3)),
      addS (.n (outBase + 3 * r)) (.n (bitBase + n - 1 - r)) (.n (outBase + 3 * r - 1))]

/-! ## Constants -/

/-- An address's type field, `tag · 2^56`. -/
def tw (tag : Nat) : Nat := tag * 2 ^ 56
def hiMul : Nat := 2 ^ 32
def stepMul : Nat := 2 ^ 61
def lxTop : Nat := 2 ^ 55

/-- A 128-bit literal (`lit_field`). -/
def lit (c : Nat) : E := word (c % 2 ^ 64) (c / 2 ^ 64 % 2 ^ 64)

/-- The digit sum of `k`'s `n` low base-4 digits (`DIGIT_SUMS`). -/
def digitSum (k : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => k / 4 ^ n % 4 + digitSum k n

/-! ## The Keccak message -/

/-- One message cell of a `keccak` block, as the lowering knows it (`SpongeCell`). -/
inductive KC where
  | zero
  | const (c : E)
  | cell (v : V)

/-- Whether a message cell is a literal zero. -/
def KC.isZero : KC → Bool
  | .zero => true
  | _ => false

open scoped Dec in
/-- Whether a constant is `0x01`, the padding run's first cell. -/
def isPadOne (c : E) : Bool := decide (c = word 1 0)

/-- The value holding a message cell (`sponge_cell`): the padding run's `0` or `1`, a fresh
constant at `b`, or the value itself. Its statements, value and next base. -/
def kCell (pad : Nat) (k : KC) (b : Nat) : List Stmt × V × Nat :=
  match k with
  | .zero => ([], .n (pad + 1), b)
  | .const c => if isPadOne c then ([], .n pad, b) else ([cst b c], .n b, b + 1)
  | .cell o => ([], o, b)

/-- `st + k` (`sponge_xor`): the state value itself for a zero, else one `XOR` into a fresh
value. -/
def kXor (pad : Nat) (st : V) (k : KC) (b : Nat) : List Stmt × V × Nat :=
  match k with
  | .zero => ([], st, b)
  | k => ((kCell pad k b).1 ++ [addS (.n (kCell pad k b).2.2) st (kCell pad k b).2.1],
      .n (kCell pad k b).2.2, (kCell pad k b).2.2 + 1)

/-- A fresh run of the four tail cells (`sponge_run`'s copy): constants and copies, from `b`. -/
def kRunFresh : List KC → Nat → List Stmt
  | [], _ => []
  | .zero :: ks, b => cst b (word 0 0) :: kRunFresh ks (b + 1)
  | .const c :: ks, b => cst b c :: kRunFresh ks (b + 1)
  | .cell o :: ks, b => copyS (.n b) o :: kRunFresh ks (b + 1)

/-- The values of a cell list that are values. -/
def kVals : List KC → List V
  | [] => []
  | .cell o :: ks => o :: kVals ks
  | _ :: ks => kVals ks

/-- Four consecutive values holding the tail cells (`sponge_run`): the cells themselves if they
are one run (`tailRun`), a window of the padding run, or a fresh copy from `b`. -/
def kRun (pad : Nat) (ks : List KC) (tailRun : Bool) (b : Nat) : List Stmt × List V × Nat :=
  if tailRun then ([], kVals ks, b)
  else if ks.all KC.isZero then ([], runV (pad + 1) 4, b)
  else match ks with
    | .const c :: rest =>
        if isPadOne c && rest.all KC.isZero then ([], runV pad 4, b)
        else (kRunFresh ks b, runV b 4, b + 4)
    | _ => (kRunFresh ks b, runV b 4, b + 4)

/-- The tail of a later block: the state's own cells for four zeros, else each XORed into a fresh
value (a zero copied). -/
def kTailXor (pad : Nat) : List V → List KC → Nat → List Stmt × List V × Nat
  | st :: sts, k :: ks, b =>
      let x : List Stmt × V × Nat := match k with
        | .zero => ([copyS (.n b) st], .n b, b + 1)
        | k => kXor pad st k b
      let rest := kTailXor pad sts ks x.2.2
      (x.1 ++ rest.1, x.2.1 :: rest.2.1, rest.2.2)
  | _, _, b => ([], [], b)

/-- The `KECCAK` inputs of block `blk`, from the zero state (`st = none`) or XORed into the
previous output `st`: its statements, its thirteen inputs and the next base. -/
def kIns (pad : Nat) (blk : List KC) (tailRun : Bool) (st : Option (List V)) (b : Nat) :
    List Stmt × List V × Nat :=
  let cell := fun i => blk.getD i .zero
  match st with
  | none =>
      let m0 := kCell pad (cell 0) b
      let m1 := kCell pad (cell 1) m0.2.2
      let m2 := kCell pad (cell 2) m1.2.2
      let m3 := kCell pad (cell 3) m2.2.2
      let t := kRun pad [cell 4, cell 5, cell 6, cell 7] tailRun m3.2.2
      let b8 := kCell pad (cell 8) t.2.2
      (m0.1 ++ m1.1 ++ m2.1 ++ m3.1 ++ t.1 ++ b8.1,
        [m0.2.1, m1.2.1, m2.2.1, m3.2.1] ++ t.2.1 ++ [b8.2.1] ++ runV (pad + 1) 4, b8.2.2)
  | some st =>
      let s := fun i => st.getD i default
      let m0 := kXor pad (s 0) (cell 0) b
      let m1 := kXor pad (s 1) (cell 1) m0.2.2
      let m2 := kXor pad (s 2) (cell 2) m1.2.2
      let m3 := kXor pad (s 3) (cell 3) m2.2.2
      let t : List Stmt × List V × Nat :=
        if [cell 4, cell 5, cell 6, cell 7].all KC.isZero then ([], [s 4, s 5, s 6, s 7], m3.2.2)
        else kTailXor pad [s 4, s 5, s 6, s 7] [cell 4, cell 5, cell 6, cell 7] m3.2.2
      let b8 := kXor pad (s 8) (cell 8) t.2.2
      (m0.1 ++ m1.1 ++ m2.1 ++ m3.1 ++ t.1 ++ b8.1,
        [m0.2.1, m1.2.1, m2.2.1, m3.2.1] ++ t.2.1 ++ [b8.2.1, s 9, s 10, s 11, s 12], b8.2.2)

/-- The cells block `k` of `B` writes: the `n` cells of `out` the last (`out_cells`), the whole
thirteen-cell state the next one reads before it. -/
def kOutN (B n k : Nat) : Nat := if k + 1 == B then n else 13

/-- Blocks `k, …, k + m - 1` of `B`, from the state `st`, the last writing `n` cells: the
statements, the next base and the last output run's base. -/
def kBlocks (pad : Nat) (cs : List KC) (B : Nat) (tailRun : Bool) (out : Option Nat) (n : Nat) :
    Nat → Nat → Option (List V) → Nat → List Stmt × Nat × Nat
  | 0, _, _, b => ([], b, b)
  | m + 1, k, st, b =>
      let blk := (cs.drop (17 * k / 2)).take 9
      let ins := kIns pad blk tailRun st b
      let last := k + 1 == B
      let o := if last then out.getD ins.2.2 else ins.2.2
      let b' := if last && out.isSome then ins.2.2 else ins.2.2 + kOutN B n k
      let rest := kBlocks pad cs B tailRun out n m (k + 1) (some (runV o 13)) b'
      (ins.1 ++ [kecS ins.2.1 (runV o (kOutN B n k)) (k % 2 == 1) (!last && k % 2 == 0)] ++ rest.1,
        rest.2.1, if last then o else rest.2.2)

/-- `xor_byte` of byte `v` at `pos`: into a zero or a constant, folded; into a value, one `XOR`
with a constant cell at `b`. -/
def kXorByte (cs : List KC) (pos v b : Nat) : List Stmt × List KC × Nat :=
  let i := pos / 16
  let w := byteWord pos v
  match cs.getD i .zero with
  | .zero => ([], cs.set i (.const w), b)
  | .const c => ([], cs.set i (.const (c + w)), b)
  | .cell o => ([cst b w, addS (.n (b + 1)) o (.n b)], cs.set i (.cell (.n (b + 1))), b + 2)

/-- The blocks of a `len`-byte message. -/
def kBlocksOf (len : Nat) : Nat := len / 136 + 1

/-- **`emit_keccak_message`** from the zero state, `len=` bytes, the last block writing `n` cells
of `out` (`out_cells`: one for a one-cell `out`, every signature digest but `H_msg`'s first, two
for a digest, thirteen for a state): the statements, the next base and the output run's base. -/
def kMsg (pad : Nat) (cells : List KC) (len : Nat) (tailRun : Bool) (out : Option Nat) (b : Nat)
    (n : Nat := 1) : List Stmt × Nat × Nat :=
  let B := kBlocksOf len
  let read := 17 * (B - 1) / 2 + 9
  let cs0 := cells ++ List.replicate (read - cells.length) KC.zero
  let x1 := kXorByte cs0 len 1 b
  let x2 := kXorByte x1.2.1 (136 * B - 1) 0x80 x1.2.2
  let bl := kBlocks pad x2.2.1 B tailRun out n B 0 none x2.2.2
  (x1.1 ++ x2.1 ++ bl.1, bl.2.1, bl.2.2)

/-- `keccak([m0, m1], [m2, m3], out)` into a one-cell `out`: 64 bytes, its last byte's constant at
`c`, the output at `o`. -/
def k64 (pad : Nat) (m0 m1 m2 m3 : V) (c o : Nat) : List Stmt :=
  [cst c (word (2 ^ 63) 0), kecS [m0, m1, m2, m3, .n pad, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n c,
    .n (pad + 1), .n (pad + 2), .n (pad + 3), .n (pad + 4)] (runV o 1) false false]

theorem k64_eq (pad : Nat) (m0 m1 m2 m3 : V) (c o : Nat) :
    k64 pad m0 m1 m2 m3 c o = (kMsg pad [.cell m0, .cell m1, .cell m2, .cell m3] 64 false (some o) c).1 := by
  rfl

end
end LeanVM.Guest.B1.Sig
