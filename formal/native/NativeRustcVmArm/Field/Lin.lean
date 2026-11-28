module

public import NativeRustcVmArm.Field.Norm

/-!
# Equal bits by xor-linear forms

The values `kmul` and `EW::mul` compute are, bit by bit, xors of bits of the registers and of
integer products of masked registers: `and` with a constant selects bits, `orr` of values with no
common possibly-set bit is their `xor`, shifts and `rbit` move bits, `bfxil` inserts one. rustc
reorders and shares these freely; `check a b` decides that two symbolic values agree in every
bit by computing, for each, its xor-linear form (`lin`): for each of the 64 bits, the set of key
bits it is the xor of, as a `Nat` with bit `64 * key + j` for bit `j` of key `key` (key `0` the
constant all-ones word, keys `1` to `31` the registers X0 to X30, keys from `32` the products of
`tbl`, each a pair of forms of registers, identified up to the order of the factors).
`eval_eq_of_check`: a successful check makes the values equal in every environment.
-/

namespace NativeRustcVmArm.Field.Lin

open NativeRustcArm NativeRustcArm.Sym

@[expose] public section

/-! ## Parities -/

/-- The parity of `val (k + j)` over the bits `j` of `n`. -/
def par (val : Nat → Bool) (k n : Nat) : Bool :=
  if n = 0 then false else ((n % 2 == 1) && val k) ^^ par val (k + 1) (n / 2)
termination_by n
decreasing_by omega

theorem par_eq (val : Nat → Bool) (k n : Nat) :
    par val k n = (((n % 2 == 1) && val k) ^^ par val (k + 1) (n / 2)) := by
  rw [par]
  by_cases h : n = 0
  · subst h
    rw [ite_eq_left rfl, par, ite_eq_left (by decide)]
    rfl
  · rw [ite_eq_right h]

theorem par_zero (val : Nat → Bool) (k : Nat) : par val k 0 = false := by
  rw [par, ite_eq_left rfl]

theorem mod_two_xor (a b : Nat) : ((a ^^^ b) % 2 == 1) = ((a % 2 == 1) ^^ (b % 2 == 1)) := by
  have h := @Nat.xor_mod_two_eq_one a b
  have ha := Nat.mod_two_eq_zero_or_one a
  have hb := Nat.mod_two_eq_zero_or_one b
  have hab := Nat.mod_two_eq_zero_or_one (a ^^^ b)
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hab with hab | hab <;>
    simp_all

theorem par_xor_le (val : Nat → Bool) :
    ∀ N a b k, a + b ≤ N → par val k (a ^^^ b) = (par val k a ^^ par val k b) := by
  intro N
  induction N with
  | zero =>
    intro a b k h
    obtain rfl : a = 0 := by omega
    obtain rfl : b = 0 := by omega
    simp [par_zero]
  | succ N ih =>
    intro a b k h
    rw [par_eq val k (a ^^^ b), par_eq val k a, par_eq val k b, Nat.xor_div_two,
      ih (a / 2) (b / 2) (k + 1) (by omega), mod_two_xor]
    generalize (a % 2 == 1) = x
    generalize (b % 2 == 1) = y
    generalize val k = v
    generalize par val (k + 1) (a / 2) = p
    generalize par val (k + 1) (b / 2) = q
    cases x <;> cases y <;> cases v <;> cases p <;> cases q <;> rfl

theorem par_xor (val : Nat → Bool) (k a b : Nat) :
    par val k (a ^^^ b) = (par val k a ^^ par val k b) :=
  par_xor_le val (a + b) a b k (Nat.le_refl _)

theorem par_two_pow (val : Nat → Bool) (j k : Nat) : par val k (2 ^ j) = val (k + j) := by
  induction j generalizing k with
  | zero =>
    rw [par_eq]
    simp [par_zero]
  | succ j ih =>
    rw [par_eq, show 2 ^ (j + 1) % 2 = 0 by rw [Nat.pow_succ]; omega,
      show 2 ^ (j + 1) / 2 = 2 ^ j by rw [Nat.pow_succ]; omega, ih, Nat.add_assoc,
      Nat.add_comm 1 j]
    simp

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

/-- `bfxil d, s, #63, #1`: bit 63 of `s` into bit 0 of `d`. -/
def bfmF (d s : Form) : Form := s.getD 63 0 :: d.tail

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
    | .bin .and .W64 a (.lit n) => (lin tbl fuel a).map (andCF n)
    | .bin .and .W64 (.lit n) a => (lin tbl fuel a).map (andCF n)
    | .bin .eor .W64 a b =>
      match lin tbl fuel a, lin tbl fuel b with
      | some fa, some fb => some (xorF fa fb)
      | _, _ => none
    | .bin .orr .W64 a b =>
      match lin tbl fuel a, lin tbl fuel b with
      | some fa, some fb => if orOk fa fb then some (xorF fa fb) else none
      | _, _ => none
    | .bin .mul .W64 a b =>
      match lin [] fuel a, lin [] fuel b with
      | some fa, some fb => (find fa fb tbl 0).map fun t ↦ atomF (32 + t)
      | _, _ => none
    | .bin (.bfm 63 63) .W64 d a =>
      match lin tbl fuel d, lin tbl fuel a with
      | some fd, some fa => some (bfmF fd fa)
      | _, _ => none
    | .un .rbit .W64 a => (lin tbl fuel a).map List.reverse
    | .un (.shift .LSL k) .W64 a => if k ≤ 64 then (lin tbl fuel a).map (shlF k) else none
    | .un (.shift .LSR k) .W64 a => if k ≤ 64 then (lin tbl fuel a).map (shrF k) else none
    | .un (.ubfm immr imms) .W64 a =>
      if imms = 63 ∧ immr < 64 then (lin tbl fuel a).map (shrF immr)
      else if imms + 1 = immr ∧ immr < 64 then (lin tbl fuel a).map (shlF (64 - immr))
      else none
    | _ => none

/-- The products of a symbolic value, with repetitions. -/
def prods : Sym → List (Sym × Sym)
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

/-- **The check**: `a` and `b` have the same form over the products of both. -/
def check (fuel : Nat) (a b : Sym) : Bool :=
  let tbl := addAll fuel (prods a ++ prods b) []
  tbl.all (fun e ↦ lin [] fuel e.a == some e.fa && lin [] fuel e.b == some e.fb) &&
    match lin tbl fuel a, lin tbl fuel b with
    | some f, some g => f == g
    | _, _ => false

/-! ## Meaning -/

section
variable [Labels]

/-- A key's value: all ones, a register, or a product of `tbl`. -/
def keyVal (env : Env) (tbl : List Entry) (key : Nat) : BitVec 64 :=
  if key = 0 then BitVec.allOnes 64
  else if key < 32 then
    match allXRegs[key - 1]? with
    | some r => env.regs r
    | none => 0
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

end NativeRustcVmArm.Field.Lin
