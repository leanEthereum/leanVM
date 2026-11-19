/-
  LeanVM.Guest.B1.Sig.SpWotsT

  The body of `sp_wots` as a template, written from the guest's structure
  (`lean_ethereum.py`) with the values numbered uniformly, every
  chain step taking three fresh values; the guest's numbering is this one with the two values the
  steps without an address constant leave unused removed (`SpWotsLayout`'s `spRen`).
-/

module

public import LeanVM.Guest.B1.Sig.WotsT

/-!
# `sp_wots` as a template

`sp_wots(pp, a0, a1, encoding)` (`G` is `lean_ethereum.py`) has the parameters
`pp = n0`, the one-time key's FIPS 205 address `a0 = n1` (its layer and tree) and `a1 = n2` (type
`WOTS_HASH`, its key pair), and `encoding = n3`; `at = [a0, a1]` copies them into `n4`, `n5`; the
powers `g^s` are `n(6 + s)`, `s < 10`.

Its codeword is the shared WOTS+C dispatch (`walk_group`, `lx = 0`) of 21 groups of three digits and
the last chain's, chained as leanXMSS's (`verify_lean_xmss`): the 22 digit words hinted at
`n16 ..< n38` (`spDg`), their range checks (`rangeS`, the last below `g^3`), the padding run
`[0x01, 0, 0, 0, 0]` the compiler sets above the first dispatch at `n126 ..< n131` (`spPad`), the
hoisted `2^63`, then the 22 `match`es back to back, each over `64` arms (`armsM`: the last group's
table as wide as the others, arm `k` walking its one chain at digit `k % 4`). Group `p`'s arms lie
from its base `vb + 6`, the first group's base the padding run's; every chain step and the leaf
read that run.

* `spStepC`, `spWp`, `spW`: the chain step (`walk`): the address `at[1] + (i·2^88 +
  s·2^120)` (the chain in `A1`'s byte 27, the step in its byte 31) and
  `keccak([pp, at[0]], [a, v], walks[o:o + 13])`, 64 bytes (`k64`), its run at `spPad`; the step of
  chain `0` leaving position `0` adds nothing, so the compiler sets no constant and hashes `at[1]`
  itself: its template takes the same three values, using the first only;
* `spDigitPos`, `spDigitsC`: where the encoding digest holds digit `j`, most significant first in
  each byte (`base_2b`, two bits a digit), and the constant arm `k` adds to the encoding (the
  digits' fields `XOR`ed: they are apart);
* `spN`, `spSlot`, `spProd`, `spEnc`, `spGroupArms`, `spGroupsT`: a group's digits, a chain's
  slots, the group's outputs, a group's arms, the dispatches;
* `spHints`, `spBound`, `spRanges`: the digit words' hints and range checks;
* `spLeafCells`, `spBodyT`: the leaf's cells and the body: the copies, the powers, the hints, the
  range checks, the padding run, the hoisted constant, the dispatches, the encoding asserted to be
  `encoding`, the digit product to be `g^128` (`SP_TARGET_SUM`), the leaf hashed as `T_v` of `pp`,
  `a0`, `a1 + SP_WOTS_PK` and the 64 tips (`keccak_cells` over `sp_word`, 67 cells, 1072 bytes) and
  returned.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Core LeanVM.Parameters

@[expose] public section

/-! ## The digit words and the padding run -/

/-- The first digit word's cell: the 22 are `n16 ..< n38`. -/
def spDg : Nat := 16

/-- The padding run's base, after the range checks: the first group's base. -/
def spPad : Nat := 126

/-- The padding run `[0x01, 0, 0, 0, 0]` at `P`. -/
def padRun (P : Nat) : List Stmt :=
  (List.range 5).map fun k => cst (P + k) (word (if k = 0 then 1 else 0) 0)

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
`at[1] + spStepC i s`, then the 64-byte hash of `pp`, `at[0]`, it and the value (`walk`). Chain `0`'s step `0` adds nothing: no constant, `at[1]` hashed itself. -/
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

/-- The digits of group `p`: three, the last chain's one. -/
def spN (p : Nat) : Nat := if p < 21 then 3 else 1

/-- The slot of chain `r`'s step `s` in a group from base `vb`. -/
def spSlot (fold : Bool) (vb : Nat) : Nat → Nat → Nat := slotsT spW fold vb

/-- The group's running product, after arm `0`'s walks. -/
def spProd (fold : Bool) (n vb : Nat) : Nat := groupStart fold vb + chainStride spW * n

/-- The group's running encoding. -/
def spEnc (fold : Bool) (n vb : Nat) : Nat := spProd fold n vb + 1

/-- The `64` arms of group `p`'s dispatch from its base `vb`, after the running product and
encoding (`armsM`): arm `k` walks the group's chains at `k`'s own digits. -/
def spGroupArms (p : Nat) (prodIn encIn : V) (vb : Nat) : List (List Stmt) × Nat :=
  armsM spW (spSlot (p == 0) vb) (3 * p) (spN p) (p == 0) prodIn encIn (.n (spProd (p == 0) (spN p) vb))
    (.n (spEnc (p == 0) (spN p) vb)) 64 0 (vb + 6)

/-- Groups `p ..< p + m`' dispatches, back to back from base `vb`, after the running product and
encoding: the statements, the next base, the chains' tips, the product and the encoding. -/
def spGroupsT : Nat → Nat → V → V → Nat → List Stmt × Nat × List V × V × V
  | 0, _, prod, enc, vb => ([], vb, [], prod, enc)
  | m + 1, p, prod, enc, vb =>
      let a := spGroupArms p prod enc vb
      let rest := spGroupsT m (p + 1) (.n (spProd (p == 0) (spN p) vb))
        (.n (spEnc (p == 0) (spN p) vb)) (a.2 - 6)
      (.match_ (.n (spDg + p)) a.1 :: rest.1, rest.2.1,
        (List.range (spN p)).map (fun r => V.n (spSlot (p == 0) vb r 2)) ++ rest.2.2.1, rest.2.2.2)

/-! ## The digit words -/

/-- The digit words' hints, one `digits` entry each. -/
def spHints : List Stmt := (List.range 22).map fun p => hintW "digits" [.n (spDg + p)]

/-- Group `p`'s range bound `g^(4^n - 1)`: `2^63`, the last chain's `2^3`. -/
def spBound (p : Nat) : E := word (2 ^ (4 ^ spN p - 1)) 0

/-- The digit words' range checks. -/
def spRanges : List Stmt :=
  (List.range 22).flatMap fun p => rangeS (.n (spDg + p)) (spBound p) (spDg + 22 + 4 * p)

/-! ## The body -/

/-- `g^128`, the target sum in the exponent (`SP_TARGET_SUM`), as the compiler writes it. -/
def spTarget : E := word 325 0

/-- `SP_WOTS_PK`, the type `WOTS_PK` in `A1`'s byte 19. -/
def spPkC : E := word (2 ^ 24) 0

/-- The codeword's dispatches, from the padding run's base. -/
def spGs : List Stmt × Nat × List V × V × V := spGroupsT 22 0 (.n 0) (.n 0) spPad

/-- The first value after the codeword's dispatches: `g^128` there, the leaf's `A1` after it. -/
def spC : Nat := spGs.2.1 + 6

/-- The leaf's cells: `pp`, `a0`, `a1 + SP_WOTS_PK` and the 64 chain tips (`sp_word`). -/
def spLeafCells : List V := V.n 0 :: V.n 1 :: V.n (spC + 2) :: spGs.2.2.1

/-- The leaf's `keccak_cells` (1072 bytes), its padding run at `spPad`: the statements, the next
base and the output run's base. -/
def spLeafK : List Stmt × Nat × Nat := kMsg spPad (spLeafCells.map KC.cell) 1072 false none (spC + 3)

/-- The body of `sp_wots`, numbered uniformly. -/
def spBodyT : List Stmt :=
  [copyS (.n 4) (.n 1), copyS (.n 5) (.n 2)] ++
    (List.range 10).map (fun s => cst (6 + s) (word (2 ^ s) 0)) ++ spHints ++ spRanges ++
    padRun spPad ++ [cst (spPad + 5) closeLane] ++ spGs.1 ++
    [.atom (.assertEq spGs.2.2.2.2 (.n 3)), cst spC spTarget,
      .atom (.assertEq spGs.2.2.2.1 (.n spC)), cst (spC + 1) spPkC,
      addS (.n (spC + 2)) (.n 2) (.n (spC + 1))] ++ spLeafK.1 ++
    [copyS (.n spLeafK.2.1) (.n spLeafK.2.2), .ret [.n spLeafK.2.1]]

end
end LeanVM.Guest.B1.Sig
