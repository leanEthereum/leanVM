/-
  LeanVM.Guest.B1.Sig.XmssSegT

  `verify_lean_xmss` (`lean_ethereum.py:3645-3717`), inline in `main`'s raw-leanXMSS loop
  `__loop2`, as a template: statements 9 to 321 of `__loop2`'s body, with the values numbered as
  the renumbered expansion numbers them.
-/

module

public import LeanVM.Guest.B1.Sig.XmssT
public import LeanVM.Guest.B1.Sig.XmssWindows
public import LeanVM.Guest.B1.Sig.XmssGroups

/-!
# The leanXMSS check in `__loop2`, as a template

`__loop2`'s parameters are the counter, `n`, `lx_slots`, `cover`, `lx_table` and the `51` carried
chain indices (`lx_tags`, `.n 5` to `.n 55`); its body checks the raw index and its cover word
(statements `0` to `8`, the claim's pointer `.n 65`), then the leanXMSS check (`xSeg`, statements
`9` to `321`), then steps the counter and calls itself (statements `322` to `328`).

* `sPrologue`: `pp`, the index's shifts (`sHis`) and windows (`sWin`) hinted, the powers `g^s`
  (`sPower`, `s < 13`);
* `sWots`: the chain step, its chain index the zero cell, a power or a carried tag (`sTag`);
* `armM`, `armsM`: a codeword arm as `armT`, its encoding the group's own digits `k % 4^n` (the last
  group's table is `4^4` wide over two digits); `sGroupsT`, `sCodewordT`: the `15` hints, their range
  checks, the hoisted `2^63` and the `15` dispatches back to back;
* `lxLevelT`, `lxArmT`, `lxWindowT`: a window of the path, arm `k`'s eight levels (`at`, the hinted
  sibling, the `KECCAK` in the order of `k`'s bit) and its pin `his[w] = his[w + 1] · g^8 + k`
  (`his[3] = k` at the top);
* `sDigest0`, `sDigest1`, `sLayer`, `xSeg`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-! ## Values -/

/-- The padding run of the check, set by the bottom layer's message digest. -/
def sLxPad : Nat := 98
/-- The claim's pointer, `lx_table · idx^4`. -/
def sSigner : V := .n 65
def sLxPP : V := .n 66
/-- `his[w] = leaf_index >> 8w`, hinted. -/
def sHis (w : Nat) : V := .n (67 + w)
/-- Window `w` in the exponent, hinted. -/
def sWin (w : Nat) : V := .n (71 + w)
/-- `powers[s] = g^s`. -/
def sPower (s : Nat) : V := .n (75 + s)
/-- `lx_tags[j]`, a parameter. -/
def sTagParam (j : Nat) : V := .n (5 + j)

/-- Chain `i`'s index cell (`walk`): the zero cell, `powers[log₂ i]` or the carried tag. -/
def sTag (i : Nat) : V :=
  if i = 0 then .n (sLxPad + 1) else if lxTagCarried i then sTagParam (lxTagSlot i - 1)
  else sPower (lxTagLog i)

/-- The range bound `g^255` of an `8`-bit dispatch, a reduced word. -/
def bound255 : E := word 9223372036854810629 0

/-- leanXMSS's chain step: `keccak([P, steps s], [v, tag i], walks[o:o + 1])` (`walk`,
`lean_ethereum.py:3552-3556`), its constant at `c`. -/
def sWots (steps : Nat → V) : WotsT where
  step i s v c o := k64 sLxPad sLxPP (steps s) v (sTag i) c o
  size := 1
  power := sPower

/-- The prologue (`lean_ethereum.py:3649-3669`). -/
def sPrologue : List Stmt :=
  [loadS sLxPP sSigner 1, hintW "lx_index" (runV 67 4), hintW "lx_windows" (runV 71 4)] ++
    (List.range 13).map (fun s => cst (75 + s) (word (2 ^ s) 0))

/-! ## The codeword -/

/-- Arm `k` of a group of `n` digits from base `b` (`walk_group`, `lean_ethereum.py:3563-3577`):
`armT` with the encoding of `k`'s own `n` digits, `k % 4^n` (`W.enc`, leanXMSS's default). -/
def armM (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) (k b : Nat) : List Stmt × Nat :=
  let ws := walksT W slots first k (if k = 0 then W.size + 1 else W.size) n 0
    (if fold then b + 1 else b)
  let enc0 := if fold then V.n b else encIn
  let pre := if fold then [cst b (word 0 0)] else []
  let prod := if fold then copyS prodOut (W.power (digitSum k n))
    else mulS prodOut prodIn (W.power (digitSum k n))
  if k % 4 ^ n = 0 then (pre ++ ws.1 ++ [prod, copyS encOut enc0], ws.2)
  else (pre ++ ws.1 ++ [prod, cst ws.2 (lit (W.enc first n (k % 4 ^ n))), addS encOut enc0 (.n ws.2)],
    ws.2 + 1)

/-- Arms `k ..< k + m` from base `b`; arm `0` allocates the outputs after its walks. -/
def armsM (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) : Nat → Nat → Nat → List (List Stmt) × Nat
  | 0, _, b => ([], b)
  | m + 1, k, b =>
      let a := armM W slots first n fold prodIn encIn prodOut encOut k b
      let rest := armsM W slots first n fold prodIn encIn prodOut encOut m (k + 1)
        (if k = 0 then a.2 + 2 else a.2)
      (a.1 :: rest.1, rest.2)

/-- The `256` arms of group `p`'s dispatch, from `vb + 6` (`vb` its base in `slotsT`'s sense). -/
def sGroupArms (W : WotsT) (p : Nat) (prodIn encIn : V) (vb : Nat) : List (List Stmt) × Nat :=
  armsM W (slotsT W (p == 0) vb) (4 * p) (lxN p) (p == 0) prodIn encIn (prodT W (p == 0) (lxN p) vb)
    (encT W (p == 0) (lxN p) vb) 256 0 (vb + 6)

/-- Groups `p ..< p + m`, back to back, their digit words from `dg`, after the running product
and encoding: the statements, the next base (in `slotsT`'s sense), the chains' tips, the product
and the encoding. -/
def sGroupsT (W : WotsT) (dg : Nat) : Nat → Nat → V → V → Nat → List Stmt × Nat × List V × V × V
  | 0, _, prod, enc, vb => ([], vb, [], prod, enc)
  | m + 1, p, prod, enc, vb =>
      let a := sGroupArms W p prod enc vb
      let rest := sGroupsT W dg m (p + 1) (prodT W (p == 0) (lxN p) vb) (encT W (p == 0) (lxN p) vb)
        (a.2 - 6)
      (.match_ (.n (dg + p)) a.1 :: rest.1, rest.2.1,
        (List.range (lxN p)).map (fun r => V.n (slotsT W (p == 0) vb r 2)) ++ rest.2.2.1,
        rest.2.2.2.1, rest.2.2.2.2)

/-- The range checks of the `15` digit words from `dg`, the last below `4^2`. -/
def sDigitChecks (dg : Nat) : List Stmt :=
  (List.range 15).flatMap fun p =>
    rangeS (.n (dg + p)) (if p < 14 then bound255 else word (2 ^ 15) 0) (dg + 15 + 4 * p)

/-- The codeword of `58` chains, its digit words from `dg` (`lean_ethereum.py:3685-3700`): the
hint, the range checks, the hoisted `2^63`, the `15` dispatches, the digits stored where the
digest's first cell `d0` is and the target sum `g^T` asserted. The statements, the next base and
the chains' tips. -/
def sCodewordT (W : WotsT) (target : E) (d0 : V) (dg : Nat) : List Stmt × Nat × List V :=
  let gs := sGroupsT W dg 15 0 (.n 0) (.n 0) (dg + 70)
  let c := gs.2.1 + 6
  ([hintW "lx_digits" (runV dg 15)] ++ sDigitChecks dg ++ [cst (dg + 75) closeLane] ++ gs.1 ++
    [copyS d0 gs.2.2.2.2, cst c target, .atom (.assertEq gs.2.2.2.1 (.n c))], c + 1, gs.2.2.1)

/-! ## The path, a window at a time -/

/-- Level `r` of window `w` in arm `k` from base `b`, from the node `cur` (`lx_levels`,
`lean_ethereum.py:3602-3626`): the address (`his[w + 1] · g^(7 - r)` plus the constant, `his[w + 1]`
plus it at `r = 7`, the constant alone in the top window), the hinted sibling and the `KECCAK` of
the pair in the order of `k`'s bit `r`. The last level writes `out`, numbered in arm `0`
(`outO = none`). The statements, the next base and the parent. -/
def lxLevelT (w k r : Nat) (cur : V) (outO : Option Nat) (b : Nat) : List Stmt × Nat × V :=
  let c := word (lxNodeConst w r + k / 2 ^ (r + 1)) 0
  let ord := fun (sib : V) => if k / 2 ^ r % 2 = 0 then (cur, sib) else (sib, cur)
  if w + 1 = 4 then
    let o := if r + 1 = 8 then outO.getD (b + 3) else b + 3
    let nb := if r + 1 = 8 ∧ outO.isSome then b + 3 else b + 4
    ([hintW "lx_path" [.n b], cst (b + 1) c] ++
      k64 sLxPad sLxPP (.n (b + 1)) (ord (.n b)).1 (ord (.n b)).2 (b + 2) o, nb, .n o)
  else if r + 1 = 8 then
    let o := outO.getD (b + 4)
    let nb := if outO.isSome then b + 4 else b + 5
    ([cst b c, addS (.n (b + 1)) (sHis (w + 1)) (.n b), hintW "lx_path" [.n (b + 2)]] ++
      k64 sLxPad sLxPP (.n (b + 1)) (ord (.n (b + 2))).1 (ord (.n (b + 2))).2 (b + 3) o, nb, .n o)
  else
    ([mulS (.n b) (sHis (w + 1)) (sPower (7 - r)), cst (b + 1) c, addS (.n (b + 2)) (.n b) (.n (b + 1)),
      hintW "lx_path" [.n (b + 3)]] ++
      k64 sLxPad sLxPP (.n (b + 2)) (ord (.n (b + 3))).1 (ord (.n (b + 3))).2 (b + 4) (b + 5),
      b + 6, .n (b + 5))

/-- Levels `r ..< r + m` of window `w` in arm `k`. -/
def lxLevelsT (w k : Nat) (outO : Option Nat) : Nat → Nat → V → Nat → List Stmt × Nat × V
  | 0, _, cur, b => ([], b, cur)
  | m + 1, r, cur, b =>
      let l := lxLevelT w k r cur outO b
      let rest := lxLevelsT w k outO m (r + 1) l.2.2 l.2.1
      (l.1 ++ rest.1, rest.2.1, rest.2.2)

/-- Arm `k` of window `w` from base `b` (`lx_window`, `lx_top_window`): the eight levels, then the
pin `his[w] = his[w + 1] · g^8 + k` (`k` alone at the top). -/
def lxArmT (w k : Nat) (cur : V) (outO : Option Nat) (b : Nat) : List Stmt × Nat :=
  let lv := lxLevelsT w k outO 8 0 cur b
  if w + 1 = 4 then (lv.1 ++ [cst (67 + w) (word k 0)], lv.2.1)
  else if k = 0 then (lv.1 ++ [mulS (sHis w) (sHis (w + 1)) (sPower 8)], lv.2.1)
  else (lv.1 ++ [mulS (.n lv.2.1) (sHis (w + 1)) (sPower 8), cst (lv.2.1 + 1) (word k 0),
    addS (sHis w) (.n lv.2.1) (.n (lv.2.1 + 1))], lv.2.1 + 2)

/-- Arms `k ..< k + m` of window `w`, `out` at `o` once arm `0` has numbered it. -/
def lxArmsT (w : Nat) (cur : V) (o : Nat) : Nat → Nat → Nat → List (List Stmt) × Nat
  | 0, _, b => ([], b)
  | m + 1, k, b =>
      let a := lxArmT w k cur (if k = 0 then none else some o) b
      let rest := lxArmsT w cur o m (k + 1) a.2
      (a.1 :: rest.1, rest.2)

/-- Where arm `0` of window `w` from base `b` numbers `out`. -/
def lxOut0 (w b : Nat) : Nat := if w + 1 = 4 then b + 31 else b + 46

/-- Window `w` from base `b`, from the node `cur` (`lean_ethereum.py:3705-3714`): the range check,
the hoisted `2^63` and the dispatch over `256` arms. The statements, the next base and `out`. -/
def lxWindowT (w : Nat) (cur : V) (b : Nat) : List Stmt × Nat × Nat :=
  let arms := lxArmsT w cur (lxOut0 w (b + 5)) 256 0 (b + 5)
  (rangeS (sWin w) bound255 b ++ [cst (b + 4) closeLane, .match_ (sWin w) arms.1], arms.2,
    lxOut0 w (b + 5))

/-! ## A layer -/

/-- The bottom layer's message digest from base `b`: `D = Th(P, A_msg, M | ρ)`, 80 bytes, one
block; it sets the padding run at `b + 10`. -/
def sDigest0 (b : Nat) : List Stmt :=
  [hintW "randomizer" [.n b], cst (b + 1) (word (tw 12) 0), addS (.n (b + 2)) (sHis 0) (.n (b + 1)),
    loadS (.n (b + 3)) sSigner 2, loadS (.n (b + 4)) sSigner 3, copyS (.n (b + 5)) (.n b),
    cst (b + 6) (word 1 0), cst (b + 7) (word 0 0), cst (b + 8) (word 0 0),
    cst (b + 9) (word (2 ^ 63) 0)] ++
  (List.range 5).map (fun k => cst (b + 10 + k) (word (if k = 0 then 1 else 0) 0)) ++
  [kecS [sLxPP, .n (b + 2), .n (b + 3), .n (b + 4), .n (b + 5), .n (b + 6), .n (b + 7), .n (b + 8),
    .n (b + 9), .n (b + 11), .n (b + 12), .n (b + 13), .n (b + 14)] (runV (b + 15) 1) false false]

/-- The top layer's index and message digest from base `b`, over the bottom root `root`. -/
def sDigest1 (b : Nat) (root : V) : List Stmt :=
  [cst b (word lxTop 0), addS (.n (b + 1)) (sHis 2) (.n b), hintW "randomizer" [.n (b + 2)],
    cst (b + 3) (word (tw 12) 0), addS (.n (b + 4)) (.n (b + 1)) (.n (b + 3))] ++
  k64 sLxPad sLxPP (.n (b + 4)) root (.n (b + 2)) (b + 5) (b + 6)

def sA (layer b : Nat) : Nat := if layer = 0 then b + 16 else b + 7
def sLxIdx (layer b : Nat) : V := if layer = 0 then sHis 0 else .n (b + 1)
def sD0 (layer b : Nat) : V := if layer = 0 then .n (b + 15) else .n (b + 6)
def sRho (layer b : Nat) : V := if layer = 0 then .n b else .n (b + 2)
def sW (layer b : Nat) : WotsT := sWots fun s => .n (sA layer b + 2 * s + 1)
def sCw (layer b : Nat) : List Stmt × Nat × List V :=
  sCodewordT (sW layer b) xTarget (sD0 layer b) (sA layer b + 6)
def sLeafCells (layer b : Nat) : List V := sLxPP :: V.n ((sCw layer b).2.1 + 1) :: (sCw layer b).2.2
def sLeafK (layer b : Nat) : List Stmt × Nat × Nat :=
  kMsg sLxPad ((sLeafCells layer b).map KC.cell) 960 false none ((sCw layer b).2.1 + 2)
def sWin0 (layer b : Nat) : List Stmt × Nat × Nat :=
  lxWindowT (2 * layer) (.n (sLeafK layer b).2.2) (sLeafK layer b).2.1
def sWin1 (layer b : Nat) : List Stmt × Nat × Nat :=
  lxWindowT (2 * layer + 1) (.n (sWin0 layer b).2.2) (sWin0 layer b).2.1

/-- Layer `layer` from base `b`, over the bottom root `root` at the top: its message digest, its
step addresses, its codeword, its one-time leaf and its two windows; the statements, the next base
and its root. -/
def sLayer (layer b : Nat) (root : V) : List Stmt × Nat × V :=
  ((if layer = 0 then sDigest0 b else sDigest1 b root) ++ xStepAddrs (sLxIdx layer b) (sA layer b) ++
    (sCw layer b).1 ++ [cst (sCw layer b).2.1 (word (tw 2) 0),
      addS (.n ((sCw layer b).2.1 + 1)) (sLxIdx layer b) (.n (sCw layer b).2.1)] ++
    (sLeafK layer b).1 ++ (sWin0 layer b).1 ++ (sWin1 layer b).1, (sWin1 layer b).2.1,
    .n (sWin1 layer b).2.2)

/-- **The leanXMSS check in `__loop2`** (statements `9` to `321` of its body). -/
def xSeg : List Stmt :=
  let l0 := sLayer 0 88 (.n 0)
  let l1 := sLayer 1 l0.2.1 l0.2.2
  sPrologue ++ l0.1 ++ l1.1 ++
    [loadS (.n l1.2.1) sSigner 0, .atom (.assertEq l1.2.2 (.n l1.2.1))]

/-- `__loop2`'s statements before the check (`lean_ethereum.py:4571-4579`): the raw index, its range
check, the cover word, the claim's pointer `lx_table · idx^4`. -/
def l2Pre : List Stmt :=
  [hintW "raw_index" [.n 56], cst 57 (word 9223372036854775821 0), mulS (.n 58) (.n 2) (.n 57),
    .atom (.rangeCheck (.n 56) (.n 59) (.n 60) (.n 61) (.n 58)), mulS (.n 62) (.n 3) (.n 56),
    loadS (.n 0) (.n 62) 0, mulS (.n 63) (.n 56) (.n 56), mulS (.n 64) (.n 63) (.n 63),
    mulS (.n 65) (.n 4) (.n 64)]

/-- `__loop2`'s statements after the check: the next counter and the self-call, the carried tags
passed on unchanged. -/
def l2Post : List Stmt :=
  [cst 120764 (word 2 0), mulS (.n 120765) (.n 0) (.n 120764),
    addS (.n 120766) (.n 120765) (.n 1), cst 120767 (word 2 0),
    mulS (.n 120768) (.n 0) (.n 120767),
    .callIf (.n 120766) "__loop2" (.n 120768 :: (List.range 55).map fun j => V.n (j + 1)), .ret []]

end
end LeanVM.Guest.B1.Sig
