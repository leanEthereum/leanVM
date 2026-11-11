/-
  LeanVM.Guest.B1.Sig.SphincsForsT

  The FORS trees, their key `T_k`, the hypertree's paths and a layer of `verify_sig_lean_sphincs`
  as templates (`lean_ethereum.py:3790-3925, 4008-4013` at leanVM main 40f877dc), with the values
  numbered as the renumbered expansion numbers them, over the values the body sets before.
-/

module

public import LeanVM.Guest.B1.Sig.Shapes

/-!
# FORS, the paths and a layer as templates

`G` is `lean_ethereum.py`. The templates take what the body sets before them as parameters: the
padding run `pad` (`[0x01, 0, 0, 0, 0]`), `P` (`pp`), the address's first cell `A0` (`a0`, the
layer and the tree), the key pair's cell `key` (`A1` of the key pair alone), and the bits and
right shifts of the fields: `bit j`, `val j`, `j` the bit's index in the digest's FORS fields
(`10 c + z` for tree `c`: `bit` the bit of level `z`, `sp_md_bit(10 c + 9 - z)`, and `val` the
field shifted right by `z`, `vals[10 c + z]`) or in the leaves of the layers (`sp_leaf_bit`,
`lvals`).

FIPS 205's address `A1` (the type and the three words after it, each big endian) is one cell: the
type's low byte at bit `24` of limb `0`, the key pair's two low bytes at bits `48`, `56` of limb
`0`, the height (or chain index) at bit `24` of limb `1`, the index's two low bytes at bits `48`,
`56` of limb `1` (`SP_*_MUL`, `G:486-496`).

* `sBe16` (`sp_be16`, `G:3790-3798`): an `n`-bit value as an `A1` index, its low byte masked by its
  shift by eight;
* `sForsAt` (`sp_fors_at`, `G:3801-3816`): the `A1` of tree `c`'s node at height `z` on the path;
* `sForsLevel(s)`, `sForsTree(s)` (`sp_fors_tree`, `G:3819-3840`): a tree's leaf hashed from its
  hinted secret and climbed up the hinted ordered pairs to its root;
* `sForsBlock` (`G:4008-4013`): `fors_at`, the 24 trees, then `T_k` over the roots (432 bytes);
* `sPath` (`sp_path`, `G:3890-3910`): a path up a tree of the hypertree;
* `sHtLayer` (`sp_layer`, `G:3913-3925`, after its counter): the encoding of `signed`, the key's
  leaf by `sp_wots`, the path.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-! ## Addresses -/

/-- The multiplier of `sp_be16`'s shift by eight, `g^8 · SP_WORD3_MUL_0 + SP_WORD3_MUL_1` folded:
`2^128 + 2^112`, the `y` limb's `g^64` reduced to `27` (`G:3795`). -/
def be16HiW : E := word 0 (2 ^ 48 + 27)

/-- `sp_be16(vals, pos, n)`: the `n`-bit value `val pos` as the index of an `A1` from base `x`,
`val pos · 2^120 + val (pos + 8) · (g^8 · 2^120 + 2^112)`: its low byte at bit `120`, its high bits
at bit `112` (the high bits' part at bit `128` cancels). The statements, the next base and the
value. -/
def sBe16 (val : Nat → V) (pos n x : Nat) : List Stmt × Nat × V :=
  if (n + 7) / 8 = 2 then
    ([cst x (lit (2 ^ 120)), mulS (.n (x + 1)) (val pos) (.n x), cst (x + 2) be16HiW,
      mulS (.n (x + 3)) (val (pos + 8)) (.n (x + 2)), addS (.n (x + 4)) (.n (x + 1)) (.n (x + 3))],
      x + 5, .n (x + 4))
  else ([cst x (lit (2 ^ 120)), mulS (.n (x + 1)) (val pos) (.n x)], x + 2, .n (x + 1))

/-- The carry-less product of `a < 2^8` and `b` (a product of polynomials over `GF(2)`). -/
def clmul8 (a b : Nat) : Nat :=
  (List.range 8).foldl (fun acc i => if a.testBit i then acc ^^^ (b <<< i) else acc) 0

/-- `const(k) · (g^8 · SP_WORD3_MUL_0 + SP_WORD3_MUL_1)` folded, `k < 2^8`: `k · be16HiW`. -/
def forsHiW (k : Nat) : E := word 0 (clmul8 k (2 ^ 48 + 27))

/-- `a + const(w)` from base `x`, `w` the constant's word and `k` a number zero exactly when it is:
none for `k = 0`. -/
def sAddK (a : V) (k : Nat) (w : E) (x : Nat) : List Stmt × Nat × V :=
  if k = 0 then ([], x, a) else ([cst x w, addS (.n (x + 1)) a (.n x)], x + 2, .n (x + 1))

/-- `sp_fors_at(a1, vals, c, z)` from base `x` (`G:3802-3816`): `a1` plus the height `z`
(`z · SP_WORD2_MUL`), then the node's tree index across the trees in the word's last two bytes:
at the root `c` (`c · SP_WORD3_MUL_0`); below `2` the index `val (10 c + z)` (`sBe16`, two bytes);
else its high byte, `c / 2^(z - 2)`, a constant, then its low byte (`sBe16`, one byte). The
statements, the next base and the value. -/
def sForsAt (a1 : V) (val : Nat → V) (c z x : Nat) : List Stmt × Nat × V :=
  let s1 := sAddK a1 z (lit (2 ^ 88 * z)) x
  if z = 10 then
    let s2 := sAddK s1.2.2 c (lit (2 ^ 120 * c)) s1.2.1
    (s1.1 ++ s2.1, s2.2.1, s2.2.2)
  else if z / 2 = 0 then
    let be := sBe16 val (10 * c + z) 16 s1.2.1
    (s1.1 ++ be.1 ++ [addS (.n be.2.1) s1.2.2 be.2.2], be.2.1 + 1, .n be.2.1)
  else
    let s2 := sAddK s1.2.2 (c / 2 ^ (z - 2)) (forsHiW (c / 2 ^ (z - 2))) s1.2.1
    let be := sBe16 val (10 * c + z) 8 s2.2.1
    (s1.1 ++ s2.1 ++ be.1 ++ [addS (.n be.2.1) s2.2.2 be.2.2], be.2.1 + 1, .n be.2.1)

/-- The values `sp_fors_at(a1, vals, c, z)` takes (`sForsAt`): the height's constant (none at `z =
0`), then at the root tree `c`'s constant (none for `c = 0`), below height `2` the index's two
bytes (`sBe16`, five values) and the sum, else the high byte's constant (none when it is `0`), the
low byte (two values) and the sum. -/
def forsAtW (c z : Nat) : Nat :=
  if z = 10 then (if c = 0 then 2 else 4)
  else if z / 2 = 0 then (if z = 0 then 6 else 8)
  else if c / 2 ^ (z - 2) = 0 then 5 else 7

/-- The values level `z` of tree `c` takes: the pair and `is_child`'s two, the parent's address, the
padding's three cells, the last byte's constant and the parent (one cell). -/
def forsLevelW (c z : Nat) : Nat := 9 + forsAtW c (z + 1)

/-- The values tree `c` takes: its secret, its leaf's address and hash (eight), its ten levels. -/
def forsTreeW (c : Nat) : Nat := 9 + ((List.range 10).map (forsLevelW c)).sum

/-- `is_child(node, kids, k, bit)` with the children at `k0`, `k1`, the check's cells at `b`,
`b + 1`. -/
def isChildS (node k0 k1 bit : V) (b : Nat) : List Stmt :=
  [addS (.n b) node k0, addS (.n (b + 1)) k0 k1, mulS (.n b) bit (.n (b + 1))]

/-- **The sibling of a node** whose two children are hinted at `x`, `x + 1`, the node climbed the
one the bit names: the left child when the bit is `1`. -/
def siblingOf (σ : Val) (bit : V) (x : Nat) : E :=
  if σ bit = 1 then σ (.n x) else σ (.n (x + 1))

/-- A node from its two children (`keccak([pp, a0], [adr, kids[0]], out, tail=kids[1:5], len=80,
pad_tail=1)`), from base `y`: the three cells after `kids[1]` set to the padding (`0x01`, `0`,
`0`) and the message read in place, its last byte's constant at `y + 3`. The statements, the next
base and the output run's base. -/
def kNode (pad : Nat) (pp a0 adr k0 k1 : V) (y : Nat) : List Stmt × Nat × Nat :=
  ([cst y (word 1 0), cst (y + 1) (word 0 0), cst (y + 2) (word 0 0),
    cst (y + 3) (word (2 ^ 63) 0),
    kecS [pp, a0, adr, k0, k1, .n y, .n (y + 1), .n (y + 2), .n (y + 3), .n (pad + 1), .n (pad + 2),
      .n (pad + 3), .n (pad + 4)] (runV (y + 4) 1) false false], y + 5, y + 4)

/-! ## FORS -/

section Fors

variable (pad : Nat) (pp a0 a1 : V) (bit val : Nat → V)

/-- Level `z` of FORS tree `c` from base `x`, from the node `cur`: the children hinted and checked,
the parent hashed at height `z + 1`. The statements, the next base and the parent. -/
def sForsLevel (c z : Nat) (cur : V) (x : Nat) : List Stmt × Nat × V :=
  let a := sForsAt a1 val c (z + 1) (x + 4)
  let k := kNode pad pp a0 a.2.2 (.n x) (.n (x + 1)) a.2.1
  ([hintW "sp_fors_nodes" [.n x, .n (x + 1)]] ++ isChildS cur (.n x) (.n (x + 1)) (bit (10 * c + z))
    (x + 2) ++ a.1 ++ k.1, k.2.1, .n k.2.2)

/-- Levels `z ..< z + m` of FORS tree `c` from `cur`, from base `x`. -/
def sForsLevels (c : Nat) : Nat → Nat → V → Nat → List Stmt × Nat × V
  | 0, _, cur, x => ([], x, cur)
  | m + 1, z, cur, x =>
      let a := sForsLevel pad pp a0 a1 bit val c z cur x
      let rest := sForsLevels c m (z + 1) a.2.2 a.2.1
      (a.1 ++ rest.1, rest.2.1, rest.2.2)

/-- FORS tree `c` from base `b` (`sp_fors_tree`): the secret hinted at `b`, the leaf hashed at
height `0` (64 bytes), ten levels. The statements, the next base and the root. -/
def sForsTree (c b : Nat) : List Stmt × Nat × V :=
  let a := sForsAt a1 val c 0 (b + 1)
  let lv := sForsLevels pad pp a0 a1 bit val c 10 0 (.n (a.2.1 + 1)) (a.2.1 + 2)
  ([hintW "sp_fors_secrets" [.n b]] ++ a.1 ++ k64 pad pp a0 a.2.2 (.n b) a.2.1 (a.2.1 + 1) ++ lv.1,
    lv.2.1, lv.2.2)

/-- FORS trees `c ..< c + m` from base `b`: the statements, the next base, the roots. -/
def sForsTrees : Nat → Nat → Nat → List Stmt × Nat × List V
  | 0, _, b => ([], b, [])
  | m + 1, c, b =>
      let t := sForsTree pad pp a0 a1 bit val c b
      let rest := sForsTrees m (c + 1) t.2.1
      (t.1 ++ rest.1, rest.2.1, t.2.2 :: rest.2.2)

end Fors

/-- **The FORS block** from base `b0` (`G:4008-4013`), the key pair's cell `key`: `fors_at = key +
FORS_TREE` at `b0 + 1`, the 24 trees, `roots_at = key + FORS_ROOTS`, then `T_k`: `keccak_cells` of
`P`, `A0`, `roots_at` and the roots (432 bytes). The statements, the next base and the FORS key's
output run's base. -/
def sForsBlock (pad : Nat) (pp a0 key : V) (bit val : Nat → V) (b0 : Nat) : List Stmt × Nat × Nat :=
  let tr := sForsTrees pad pp a0 (.n (b0 + 1)) bit val 24 0 (b0 + 2)
  let B := tr.2.1
  let k := kMsg pad (([pp, a0, .n (B + 1)] ++ tr.2.2).map KC.cell) 432 true none (B + 2)
  ([cst b0 (lit (3 * 2 ^ 24)), addS (.n (b0 + 1)) key (.n b0)] ++ tr.1 ++
    [cst B (lit (4 * 2 ^ 24)), addS (.n (B + 1)) key (.n B)] ++ k.1, k.2.1, k.2.2)

/-! ## The hypertree -/

/-- The constant of a path's node address at height `h`: the type `TREE` and the height. -/
def pathConst (h : Nat) : Nat := 2 * 2 ^ 24 + 2 ^ 88 * h

/-- `sp_path` from `cur`, the levels `z ..< z + m` of the tree whose leaf's bits are `bit (off + ·)`
and its ancestors' indices `val (off + ·)`, from base `x`: the children hinted and checked, the
parent hashed at height `z + 1` with its index below the root. The statements, the next base and the
root. -/
def sPath (pad : Nat) (pp a0 : V) (bit val : Nat → V) (off : Nat) :
    Nat → Nat → V → Nat → List Stmt × Nat × V
  | 0, _, cur, x => ([], x, cur)
  | m + 1, z, cur, x =>
      let pre := [hintW "siblings" [.n x, .n (x + 1)]] ++
        isChildS cur (.n x) (.n (x + 1)) (bit (off + z)) (x + 2)
      let a : List Stmt × Nat × V :=
        if m = 0 then ([cst (x + 4) (lit (pathConst (z + 1)))], x + 5, .n (x + 4))
        else
          let be := sBe16 val (off + z + 1) m (x + 4)
          (be.1 ++ [cst be.2.1 (lit (pathConst (z + 1))),
            addS (.n (be.2.1 + 1)) be.2.2 (.n be.2.1)], be.2.1 + 2, .n (be.2.1 + 1))
      let k := kNode pad pp a0 a.2.2 (.n x) (.n (x + 1)) a.2.1
      let rest := sPath pad pp a0 bit val off m (z + 1) (.n k.2.2) k.2.1
      (pre ++ a.1 ++ k.1 ++ rest.1, rest.2.1, rest.2.2)

/-- **A layer** from base `b` (`sp_layer` after its counter `ctr`): `enc_at = key + WOTS_ENC` at
`b + 1`, the encoding of `signed` (68 bytes), the key's leaf by `sp_wots`, the path of `height`
levels from leaf bit `off`. The statements, the next base and the root. -/
def sHtLayer (pad : Nat) (pp a0 key signed ctr : V) (bit val : Nat → V) (off height b : Nat) :
    List Stmt × Nat × V :=
  let k := kMsg pad [.cell pp, .cell a0, .cell (.n (b + 1)), .cell signed, .cell ctr] 68 false none
    (b + 2)
  let p := sPath pad pp a0 bit val off height 0 (.n k.2.1) (k.2.1 + 1)
  ([cst b (lit (7 * 2 ^ 24)), addS (.n (b + 1)) key (.n b)] ++ k.1 ++
    [.call "sp_wots" [pp, a0, key, .n k.2.2] [.n k.2.1]] ++ p.1, p.2.1, p.2.2)

end
end LeanVM.Guest.B1.Sig
