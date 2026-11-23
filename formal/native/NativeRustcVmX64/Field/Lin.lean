module

public import NativeRustcX64.Sym

/-!
# Equal bits by xor-linear forms (x86-64)

The values `kmul` and `EW::mul` compute are, bit by bit, xors of bits of the registers, of
variables and of integer products of masked values: `and` with a constant selects bits, `or` and
`add` of values with no common possibly-set bit are their `xor`, shifts (`shl`, `shr`, a product
by a power of two) and `bswap` move bits, `x + x` is `x << 1`. rustc reorders and shares these
freely; `check a b` decides that two symbolic values agree in every bit by computing, for each,
its xor-linear form (`lin`): for each of the 64 bits, the set of key bits it is the xor of, as a
`Nat` with bit `64 * key + j` for bit `j` of key `key` (key `0` the constant all-ones word, keys
`1` to `16` the registers RAX to R15, keys `17` to `31` the variables `0` to `14`, keys from `32`
the products of `tbl`, each a pair of forms, identified up to the order of the factors).
`checkRev a b`: `a` is `b` bit-reversed. `eval_eq_of_check`, `eval_eq_of_checkRev`: a successful
check makes the values equal in every environment.
-/

namespace NativeRustcVmX64.Field.Lin

open NativeRustcX64 NativeRustcX64.Sym

@[expose] public section

/-! ## Parities -/

/-- The parity of `val (k + j)` over the bits `j` of `n`. -/
def par (val : Nat → Bool) (k n : Nat) : Bool :=
  if n = 0 then false else ((n % 2 == 1) && val k) ^^ par val (k + 1) (n / 2)
termination_by n
decreasing_by omega

/-! ## Forms -/

/-- A value's bits as xors of key bits: entry `i` the key bits bit `i` is the xor of. -/
abbrev Form := List Nat

/-- A product of `tbl`: the factors and their forms. -/
structure Entry where
  a : Sym
  b : Sym
  fa : Form
  fb : Form

/-- The constant `n`: its set bits are those of the all-ones key `0`. -/
def litF (n : Nat) : Form := (List.range 64).map fun i ↦ if n.testBit i then 2 ^ i else 0

/-- The key `key` itself. -/
def atomF (key : Nat) : Form := (List.range 64).map fun i ↦ 2 ^ (64 * key + i)

def xorF (f g : Form) : Form := List.zipWith (· ^^^ ·) f g

def andCF (n : Nat) (f : Form) : Form :=
  List.zipWith (fun b x ↦ if b then x else 0) ((List.range 64).map n.testBit) f

/-- In each bit one of `f`, `g` is zero. -/
def orOk (f g : Form) : Bool := (List.zipWith (fun x y ↦ x == 0 || y == 0) f g).all id

def shlF (k : Nat) (f : Form) : Form := (List.replicate k 0 ++ f).take 64

def shrF (k : Nat) (f : Form) : Form := f.drop k ++ List.replicate k 0

/-- The bit `bswap` moves to bit `i`. -/
def bswapIdx (i : Nat) : Nat := 8 * (7 - i / 8) + i % 8

/-- `bswap`'s form. -/
def bswapF (f : Form) : Form := (List.range 64).map fun i ↦ f.getD (bswapIdx i) 0

/-- The index of the product of forms `fa`, `fb` (either order) in `tbl`, from `t`. -/
def find (fa fb : Form) : List Entry → Nat → Option Nat
  | [], _ => none
  | e :: es, t =>
    if (e.fa == fa && e.fb == fb) || (e.fa == fb && e.fb == fa) then some t
    else find fa fb es (t + 1)

/-- The form of a symbolic value, `fuel` bounding its depth; `none` outside the operations above. -/
def lin (tbl : List Entry) : Nat → Sym → Option Form
  | 0, _ => none
  | fuel + 1, s =>
    match s with
    | .lit n => some (litF n)
    | .reg r => some (atomF (r.idx + 1))
    | .var i => if i < 15 then some (atomF (17 + i)) else none
    | .bin .and .W64 a (.lit n) => (lin tbl fuel a).map (andCF n)
    | .bin .and .W64 (.lit n) a => (lin tbl fuel a).map (andCF n)
    | .bin .xor .W64 a b =>
      match lin tbl fuel a, lin tbl fuel b with
      | some fa, some fb => some (xorF fa fb)
      | _, _ => none
    | .bin .or .W64 a b =>
      match lin tbl fuel a, lin tbl fuel b with
      | some fa, some fb => if orOk fa fb then some (xorF fa fb) else none
      | _, _ => none
    | .bin .add .W64 a b =>
      match lin tbl fuel a, lin tbl fuel b with
      | some fa, some fb =>
        if orOk fa fb then some (xorF fa fb) else if fa == fb then some (shlF 1 fa) else none
      | _, _ => none
    | .bin .mul .W64 a (.lit n) =>
      if 2 ^ n.log2 = n ∧ n.log2 < 64 then (lin tbl fuel a).map (shlF n.log2) else none
    | .bin .mul .W64 a b =>
      match lin [] fuel a, lin [] fuel b with
      | some fa, some fb => (find fa fb tbl 0).map fun t ↦ atomF (32 + t)
      | _, _ => none
    | .bin .shl .W64 a (.lit k) => if k < 64 then (lin tbl fuel a).map (shlF k) else none
    | .bin .shr .W64 a (.lit k) => if k < 64 then (lin tbl fuel a).map (shrF k) else none
    | .un .bswap .W64 a => (lin tbl fuel a).map bswapF
    | _ => none

/-- The products of a symbolic value, with repetitions. -/
def prods : Sym → List (Sym × Sym)
  | .bin .mul .W64 a (.lit _) => prods a
  | .bin .mul .W64 a b => [(a, b)]
  | .bin _ _ a b => prods a ++ prods b
  | .un _ _ a => prods a
  | _ => []

/-- `ps`'s products appended to `tbl` where new. Each step inspects the table before the next (the
`match` on `find`), so that the kernel does not build a chain of pending appends. -/
def addAll (fuel : Nat) : List (Sym × Sym) → List Entry → List Entry
  | [], tbl => tbl
  | (a, b) :: ps, tbl =>
    match lin [] fuel a, lin [] fuel b with
    | some fa, some fb =>
      match find fa fb tbl 0 with
      | some _ => addAll fuel ps tbl
      | none => addAll fuel ps (tbl ++ [⟨a, b, fa, fb⟩])
    | _, _ => addAll fuel ps tbl

/-- The products' table of `a` and `b`, each product's forms checked. -/
def table (fuel : Nat) (a b : Sym) : Option (List Entry) :=
  let tbl := addAll fuel (prods a ++ prods b) []
  if tbl.all (fun e ↦ lin [] fuel e.a == some e.fa && lin [] fuel e.b == some e.fb) then some tbl
  else none

/-- **The check**: `a` and `b` have the same form over the products of both. -/
def check (fuel : Nat) (a b : Sym) : Bool :=
  match table fuel a b with
  | some tbl =>
    match lin tbl fuel a, lin tbl fuel b with
    | some f, some g => f == g
    | _, _ => false
  | none => false

/-- **The reversal check**: `a`'s form is `b`'s reversed. -/
def checkRev (fuel : Nat) (a b : Sym) : Bool :=
  match table fuel a b with
  | some tbl =>
    match lin tbl fuel a, lin tbl fuel b with
    | some f, some g => f == g.reverse
    | _, _ => false
  | none => false

/-! ## Meaning -/

section
variable [Labels]

/-- A key's value: all ones, a register, a variable or a product of `tbl`. -/
def keyVal (env : Env) (tbl : List Entry) (key : Nat) : BitVec 64 :=
  if key = 0 then BitVec.allOnes 64
  else if key < 17 then
    match allRegs[key - 1]? with
    | some r => env.regs r
    | none => 0
  else if key < 32 then env.vars (key - 17)
  else
    match tbl[key - 32]? with
    | some e => e.a.eval env * e.b.eval env
    | none => 0

/-- Key bit `n`: bit `n % 64` of key `n / 64`. -/
def val (env : Env) (tbl : List Entry) (n : Nat) : Bool :=
  (keyVal env tbl (n / 64)).getLsbD (n % 64)

/-- `f` is the form of `x`. -/
def Sound (env : Env) (tbl : List Entry) (x : BitVec 64) (f : Form) : Prop :=
  f.length = 64 ∧ ∀ i < 64, x.getLsbD i = par (val env tbl) 0 (f.getD i 0)

end

end

end NativeRustcVmX64.Field.Lin
