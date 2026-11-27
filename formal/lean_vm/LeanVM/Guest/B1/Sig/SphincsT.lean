/-
  LeanVM.Guest.B1.Sig.SphincsT

  The body of `verify_sig_lean_sphincs` as a template, written from the guest's structure
  (`lean_ethereum.py`) with the values numbered as the renumbered
  expansion numbers them: the digest block (`SphincsDigestT`), then FORS and the hypertree
  (`SphincsForsT`'s templates, instantiated here).
-/

module

public import LeanVM.Guest.B1.Sig.SphincsDigestT
public import LeanVM.Guest.B1.Sig.SphincsForsT
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sig_lean_sphincs»
import LeanVM.Guest.StmtsAppend

/-!
# `verify_sig_lean_sphincs` as a template

`verify_sig_lean_sphincs(signer, byte_bits)` (`G` is `lean_ethereum.py`). Its first 1358 statements, through the digest's check, are `sDigestBlock`
(`SphincsDigestT`); the next value is `n1372`. After them:

* `sForsAddrs`: `a0_b` at `n1379` (`sA0B`), `key_b` at `n1381` (`sKeyB`);
* `sForsB`: `SphincsForsT.sForsBlock` from `n1382`: `fors_at` at `n1383`, the 24 trees (tree `c`
  from `sForsBase c`), `T_k` over the roots, the FORS key at `n5248` (`sForsPk`); the trees read the digest's bits through `sForsBit`
  and the values `vals[k]` through `sVals`;
* `sLayerAt l` (`sp_layer`), layer `l` from `sLayerBase l`: its counter hinted
  (`sp_counter`) and read (`sFromMarks`, 4 bytes, `sCtrOf l`), then `SphincsForsT.sHtLayer`: the
  encoding digest (`sEncOf l`), the call of `sp_wots` (its leaf `sLeafOf l`) and the
  path of `sHeightOf l` levels from leaf bit `sOffOf l` up to the layer's root;
* `sLayerB`, `sMidAddrs`, `sLayerM`, `sTopAddrs`, `sLayerT`: the three layers with
  their addresses (`sA0Of l`, `sA1Of l`) between them, then `root[0] == pk_root`;
* `sBody = sDigestBlock ++ sAfterDigest`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-! ## FORS -/

/-- `vals[k]`, the index of FORS tree `k / 10`'s leaf's ancestor at height `k % 10`. -/
def sVals (k : Nat) : V := sFVal (k / 10) (k % 10)

/-- The bit FORS tree `k / 10`'s level `k % 10` checks its node against:
`sp_md_bit(bits0, bits1, 10 c + 9 - z)`. -/
def sForsBit (k : Nat) : V := sMdBit (10 * (k / 10) + 9 - k % 10)

/-- `a0_b` (the bottom key's layer `0` and tree: `lvals[8] · 2^120 + tree_mid · 2^112 + lvals[24] ·
2^104`), `key_b` (its leaf, `lvals[0] · 2^56`), and `fors_at = key_b + SP_FORS_TREE`. -/
def sA0B : V := .n (val% «verify_sig_lean_sphincs» "a0_b")
def sKeyB : V := .n (val% «verify_sig_lean_sphincs» "key_b")
/-- `a0_b`, `key_b`, from `n1372`. -/
def sForsAddrs : List Stmt :=
  [cst 1372 (lit (2 ^ 120)), mulS (.n (val% «verify_sig_lean_sphincs» "a0_b~1")) (sLVal 8) (.n (val% «verify_sig_lean_sphincs» "a0_b~0")), cst 1374 (lit (2 ^ 112)),
    mulS (.n (val% «verify_sig_lean_sphincs» "a0_b~3")) sTreeMid (.n (val% «verify_sig_lean_sphincs» "a0_b~2")), addS (.n (val% «verify_sig_lean_sphincs» "a0_b~4")) (.n (val% «verify_sig_lean_sphincs» "a0_b~1")) (.n (val% «verify_sig_lean_sphincs» "a0_b~3")), cst 1377 (lit (2 ^ 104)),
    mulS (.n (val% «verify_sig_lean_sphincs» "a0_b~6")) (sLVal 24) (.n (val% «verify_sig_lean_sphincs» "a0_b~5")), addS sA0B (.n (val% «verify_sig_lean_sphincs» "a0_b~4")) (.n (val% «verify_sig_lean_sphincs» "a0_b~6")),
    cst 1380 (lit (2 ^ 56)), mulS sKeyB (sLVal 0) (.n (val% «verify_sig_lean_sphincs» "key_b~0"))]

/-- FORS from `n1382`: the statements, the next base (`n5249`) and the FORS key's
output run's base. -/
def sForsB : List Stmt × Nat × Nat := sForsBlock sPad sPP sA0B sKeyB sForsBit sVals 1382

/-- Tree `c`'s base, its secret's cell. -/
def sForsBase (c : Nat) : Nat := 1384 + ((List.range c).map forsTreeW).sum

/-- The FORS public key, `fors_pk[0]`. -/
def sForsPk : V := .n (val% «verify_sig_lean_sphincs» "fors_pk[0]")

/-! ## The hypertree -/

/-- Layer `l`'s first leaf bit (`0`, `SP_MID = 8`, `SP_TOP = 16`) and its height (8, 8, 10). -/
def sOffOf (l : Nat) : Nat := sLeafOff l
def sHeightOf (l : Nat) : Nat := sLeafLen l

/-- Layer `l`'s base, its counter's first mark. -/
def sLayerBase (l : Nat) : Nat := if l = 0 then 5249 else if l = 1 then 5407 else 5561

/-- Layer `l`'s `A0` as `sHtLayer` takes it: a value for the bottom and middle layers, the constant
`a0_t = 2 · SP_LAYER_MUL` for the top one, set before each use (`a0Pre`). -/
def sAcOf (l : Nat) : Option E := if l = 2 then some (lit (2 ^ 25)) else none

/-- Layer `l`'s `a0` (the top layer's: the cell its call of `sp_wots` reads), its key pair's `A1`
(`sp_wots`'s `a1`), its counter, its encoding digest's first cell and its leaf (`sp_wots`'s
return). -/
def sA0Of (l : Nat) : V := if l = 0 then sA0B else if l = 1 then .n (val% «verify_sig_lean_sphincs» "a0_m") else .n (val% «verify_sig_lean_sphincs» "leaf@3~1")
def sA1Of (l : Nat) : V := if l = 0 then sKeyB else if l = 1 then .n (val% «verify_sig_lean_sphincs» "key_m") else .n (val% «verify_sig_lean_sphincs» "key_t")
def sCtrOf (l : Nat) : V := .n (sLayerBase l + 36)
def sEncOf (l : Nat) : V := .n (sLayerBase l + 46 + a0W (sAcOf l))
def sLeafOf (l : Nat) : V := .n (sLayerBase l + 47 + 2 * a0W (sAcOf l))

/-- Layer `l` (`sp_layer`) signing `signed`, at `a0` with its key pair `a1`: the
counter's four bytes hinted at `sLayerBase l …` and read, then the layer. The statements, the next
base and the root. -/
def sLayerAt (l : Nat) (a0 a1 signed : V) : List Stmt × Nat × V :=
  let c := sFromMarks (sLayerBase l) 4 (sLayerBase l + 4)
  let L := sHtLayer sPad sPP a0 (sAcOf l) a1 signed c.2.2 sLeafBit sLVal (sOffOf l) (sHeightOf l) c.2.1
  ([hintW "sp_counter" (runV (sLayerBase l) 4)] ++ c.1 ++ L.1, L.2.1, L.2.2)

/-- The bottom layer: `a0_b`, `key_b`, signing the FORS key. -/
def sLayerB : List Stmt × Nat × V := sLayerAt 0 sA0B sKeyB sForsPk

/-- `a0_m = SP_LAYER_MUL + tree_mid · 2^120 + lvals[24] · 2^112`, `key_m = lvals[8] · 2^56`
, from `n5398`. -/
def sMidAddrs : List Stmt :=
  [cst 5398 (lit (2 ^ 24)), cst 5399 (lit (2 ^ 120)), mulS (.n (val% «verify_sig_lean_sphincs» "a0_m~2")) sTreeMid (.n (val% «verify_sig_lean_sphincs» "a0_m~1")),
    addS (.n (val% «verify_sig_lean_sphincs» "a0_m~3")) (.n (val% «verify_sig_lean_sphincs» "a0_m~0")) (.n (val% «verify_sig_lean_sphincs» "a0_m~2")), cst 5402 (lit (2 ^ 112)),
    mulS (.n (val% «verify_sig_lean_sphincs» "a0_m~5")) (sLVal 24) (.n (val% «verify_sig_lean_sphincs» "a0_m~4")), addS (sA0Of 1) (.n (val% «verify_sig_lean_sphincs» "a0_m~3")) (.n (val% «verify_sig_lean_sphincs» "a0_m~5")),
    cst 5405 (lit (2 ^ 56)), mulS (sA1Of 1) (sLVal 8) (.n (val% «verify_sig_lean_sphincs» "key_m~0"))]

/-- The middle layer, signing the bottom root. -/
def sLayerM : List Stmt × Nat × V := sLayerAt 1 (sA0Of 1) (sA1Of 1) sLayerB.2.2

/-- `key_t = tree_mid · 2^56 + lvals[24] · 2^48`, from `n5556` (`a0_t` is a constant, `sAcOf`). -/
def sTopAddrs : List Stmt :=
  [cst 5556 (lit (2 ^ 56)), mulS (.n (val% «verify_sig_lean_sphincs» "key_t~1")) sTreeMid (.n (val% «verify_sig_lean_sphincs» "key_t~0")), cst 5558 (lit (2 ^ 48)),
    mulS (.n (val% «verify_sig_lean_sphincs» "key_t~3")) (sLVal 24) (.n (val% «verify_sig_lean_sphincs» "key_t~2")), addS (sA1Of 2) (.n (val% «verify_sig_lean_sphincs» "key_t~1")) (.n (val% «verify_sig_lean_sphincs» "key_t~3"))]

/-- The top layer, signing the middle root. -/
def sLayerT : List Stmt × Nat × V := sLayerAt 2 (sA0Of 2) (sA1Of 2) sLayerM.2.2

/-! ## The body -/

/-- The statements after the digest block: FORS, the three layers, `root[0] == pk_root`
. -/
def sAfterDigest : List Stmt :=
  sForsAddrs ⧺ sForsB.1 ⧺ sLayerB.1 ⧺ sMidAddrs ⧺ sLayerM.1 ⧺ sTopAddrs ⧺ sLayerT.1 ⧺
    [.atom (.assertEq sLayerT.2.2 sRoot), .ret []]

/-- The body of `verify_sig_lean_sphincs`. -/
def sBody : List Stmt := sDigestBlock ⧺ sAfterDigest

end
end LeanVM.Guest.B1.Sig
