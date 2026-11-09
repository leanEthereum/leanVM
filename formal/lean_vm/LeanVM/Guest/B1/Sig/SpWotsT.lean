/-
  LeanVM.Guest.B1.Sig.SpWotsT

  The body of `sp_wots` as a template, written from the guest's structure
  (`lean_ethereum.py:3880-3909` at leanVM main 40f877dc) with the values numbered uniformly, every
  chain step taking three fresh values; the guest's numbering is this one with the two values the
  steps without an address constant leave unused removed (`SpWotsLayout`'s `spRen`).
-/

module

public import LeanVM.Guest.B1.Sig.WotsT

/-!
# `sp_wots` as a template

`sp_wots(pp, a0, a1, encoding)` (`G:3880-3909`; `G` is `lean_ethereum.py`) has the parameters
`pp = n0`, the one-time key's FIPS 205 address `a0 = n1` (its layer and tree) and `a1 = n2` (type
`WOTS_HASH`, its key pair), and `encoding = n3`; `at = [a0, a1]` copies them into `n4`, `n5`; the
powers `g^s` are `n(6 + s)`, `s < 10`.

Its codeword is the shared WOTS+C dispatch (`walk_group`, `G:3574-3585`, `lx = 0`): 21 groups of
three digits and the last chain's, each a hinted digit word, its range check, the hoisted constant
and a `match` over its `4^n` arms, written with the shared templates (`WotsT`, `groupD`). No `KECCAK`
precedes the codeword, so the compiler sets the padding run `[0x01, 0, 0, 0, 0]` above the first
group's dispatch, at `n21 ..< n26` (`spPad`), after its range check: the first group's arms are laid
out from `n21` (`spL`), five above its digit word; every chain step and the leaf read that run.

* `spStepC`, `spWp`, `spW`: the chain step (`walk`, `G:3545-3571`): the address `at[1] + (i·2^88 +
  s·2^120)` (the chain in `A1`'s byte 27, the step in its byte 31) and
  `keccak([pp, at[0]], [a, v], walks[o:o + 13])`, 64 bytes (`k64`), its run at `spPad`; the step of
  chain `0` leaving position `0` adds nothing, so the compiler sets no constant and hashes `at[1]`
  itself: its template takes the same three values, using the first only;
* `spDigitPos`, `spDigitsC`: where the encoding digest holds digit `j`, most significant first in
  each byte (`base_2b`, two bits a digit), and the constant arm `k` adds to the encoding (the
  digits' fields `XOR`ed: they are apart);
* `spL`, `spPre`, `spSlot`, `spProd`, `spEnc`, `spGroupT`, `spGroupsT`: a group's layout base, the
  run the first group sets, a chain's slots, the group's outputs, a group, the groups;
* `spLeafCells`, `spBodyT`: the leaf's cells and the body: the copies, the powers, the groups, the
  encoding asserted to be `encoding`, the digit product to be `g^128` (`SP_TARGET_SUM`), the leaf
  hashed as `T_v` of `pp`, `a0`, `a1 + SP_WOTS_PK` and the 64 tips (`keccak_cells` over `sp_word`,
  67 cells, 1072 bytes) and returned.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-! ## The padding run -/

/-- The padding run's base: the first group sets it after its range check. -/
def spPad : Nat := 21

/-- The padding run `[0x01, 0, 0, 0, 0]` at `P`. -/
def padRun (P : Nat) : List Stmt :=
  (List.range 5).map fun k => cst (P + k) (word (if k = 0 then 1 else 0) 0 0)

/-! ## The chains -/

/-- The constant step `s` of chain `i` adds to `A1`: the chain in byte 27 (`SP_WORD2_MUL`), the
step in byte 31 (`SP_WORD3_MUL_0`). -/
def spStepC (i s : Nat) : Nat := i * 2 ^ 88 + s * 2 ^ 120

/-- Where the encoding digest holds digit `j` (two bits): byte `j / 4`, most significant first
(`base_2b`): bit `8 (j / 4) + 2 (3 - j % 4)` of its cell. -/
def spDigitPos (j : Nat) : Nat := 8 * (j / 4) + 2 * (3 - j % 4)

/-- The constant arm `k` of a group of `n` digits from digit `first` adds to the encoding: digit
`r` of `k` (base 4) at `spDigitPos (first + r)`, the fields apart, so their sum is their `XOR`. -/
def spDigitsC (first n k : Nat) : Nat :=
  ((List.range n).map fun r => k / 4 ^ r % 4 * 2 ^ spDigitPos (first + r)).foldr (· ^^^ ·) 0

theorem spDigitsC_zero (first n : Nat) : spDigitsC first n 0 = 0 := by
  unfold spDigitsC
  induction (List.range n) with
  | nil => rfl
  | cons a l ih => simpa using ih

/-- `sp_wots`'s chain step with its padding run at `X`: step `s` of chain `i`, the address
`at[1] + spStepC i s`, then the 64-byte hash of `pp`, `at[0]`, it and the value (`walk`,
`G:3545-3571`). Chain `0`'s step `0` adds nothing: no constant, `at[1]` hashed itself. -/
def spWp (X : Nat) : WotsT where
  step i s v c o := if i = 0 ∧ s = 0 then k64 X (.n 0) (.n 4) (.n 5) v c o
    else cst c (lit (spStepC i s)) :: addS (.n (c + 1)) (.n 5) (.n c) ::
      k64 X (.n 0) (.n 4) (.n (c + 1)) v (c + 2) o
  size := 3
  power s := .n (6 + s)
  enc first n k := spDigitsC first n k
  enc_zero first n := spDigitsC_zero first n

/-- `sp_wots`'s chain step, its padding run at `spPad`. -/
def spW : WotsT := spWp spPad

/-! ## The groups -/

/-- A group's layout base from its digit word's cell `B`: the first group's arms lie above the
padding run, five up. -/
def spL (fold : Bool) (B : Nat) : Nat := if fold then B + 5 else B

/-- What a group sets between its range check and its hoisted constant: the first, the padding run. -/
def spPre (fold : Bool) (B : Nat) : List Stmt := if fold then padRun (B + 5) else []

/-- The slot of chain `r`'s step `s` in a group from base `B`. -/
def spSlot (fold : Bool) (B : Nat) : Nat → Nat → Nat := slotsT spW fold (spL fold B)

/-- The group's running product, after arm `0`'s walks. -/
def spProd (fold : Bool) (n B : Nat) : Nat := groupStart fold (spL fold B) + chainStride spW * n

/-- The group's running encoding. -/
def spEnc (fold : Bool) (n B : Nat) : Nat := spProd fold n B + 1

/-- A group of `n` digits, its digit word at `B`: the shared group, its arms laid out from
`spL fold B`, the first setting the padding run; the statements and the next base. -/
def spGroupT (first n : Nat) (fold : Bool) (prodIn encIn : V) (B : Nat) : List Stmt × Nat :=
  groupD spW first n fold prodIn encIn B (spPre fold B) (spL fold B)

/-- Groups `p ..< p + m` of three digits from base `B`, after the running product and encoding:
the statements, the next base, the chains' tips, the product and the encoding. -/
def spGroupsT : Nat → Nat → V → V → Nat → List Stmt × Nat × List V × V × V
  | 0, _, prod, enc, B => ([], B, [], prod, enc)
  | m + 1, p, prod, enc, B =>
      let fold := p == 0
      let g := spGroupT (3 * p) 3 fold prod enc B
      let rest := spGroupsT m (p + 1) (.n (spProd fold 3 B)) (.n (spEnc fold 3 B)) g.2
      (g.1 ++ rest.1, rest.2.1,
        (List.range 3).map (fun r => V.n (spSlot fold B r 2)) ++ rest.2.2.1, rest.2.2.2)

/-! ## The body -/

/-- `g^128`, the target sum in the exponent (`SP_TARGET_SUM`), as the compiler writes it. -/
def spTarget : E := word 325 0 0

/-- `SP_WOTS_PK`, the type `WOTS_PK` in `A1`'s byte 19. -/
def spPkC : E := word (2 ^ 24) 0 0

/-- The codeword's groups: 21 of three digits from `n16`, then the last chain's. -/
def spGs : List Stmt × Nat × List V × V × V := spGroupsT 21 0 (.n 0) (.n 0) 16

/-- The last chain's group. -/
def spLast : List Stmt × Nat := spGroupT 63 1 false spGs.2.2.2.1 spGs.2.2.2.2 spGs.2.1

/-- The first value after the codeword's checks: `g^128` there, the leaf's `A1` after it. -/
def spC : Nat := spLast.2

/-- The leaf's cells: `pp`, `a0`, `a1 + SP_WOTS_PK` and the 64 chain tips (`sp_word`). -/
def spLeafCells : List V :=
  V.n 0 :: V.n 1 :: V.n (spC + 2) :: spGs.2.2.1 ++ [V.n (spSlot false spGs.2.1 0 2)]

/-- The leaf's `keccak_cells` (1072 bytes), its padding run at `spPad`: the statements, the next
base and the output run's base. -/
def spLeafK : List Stmt × Nat × Nat := kMsg spPad (spLeafCells.map KC.cell) 1072 false none (spC + 3)

/-- The body of `sp_wots`, numbered uniformly. -/
def spBodyT : List Stmt :=
  [copyS (.n 4) (.n 1), copyS (.n 5) (.n 2)] ++
    (List.range 10).map (fun s => cst (6 + s) (word (2 ^ s) 0 0)) ++ spGs.1 ++ spLast.1 ++
    [.atom (.assertEq (.n (spEnc false 1 spGs.2.1)) (.n 3)), cst spC spTarget,
      .atom (.assertEq (.n (spProd false 1 spGs.2.1)) (.n spC)), cst (spC + 1) spPkC,
      addS (.n (spC + 2)) (.n 2) (.n (spC + 1))] ++ spLeafK.1 ++
    [copyS (.n spLeafK.2.1) (.n spLeafK.2.2), .ret [.n spLeafK.2.1]]

end
end LeanVM.Guest.B1.Sig
