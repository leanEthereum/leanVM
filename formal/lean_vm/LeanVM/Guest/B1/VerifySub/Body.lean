/-
  LeanVM.Guest.B1.VerifySub.Body

  `verify_sub`'s body as a generator: its phases' blocks in order, equal to the compiled core
  body by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.VerifySub.Tail

/-!
# `verify_sub`'s body, generated

`vsBody` writes `verify_sub`'s statements before its `ret` phase by phase, from the block
templates the soundness proof reads (`fsNextT`, `squeezeT`, `eqwEntry`, `ctSlot`, …) and the
irregular statements between them; `vsPre_eq` checks it against the core body by
`decide +kernel`. Completeness builds a valuation for each block of `vsBody`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The blocks -/

/-- The seed (G:2092-2093). -/
def bSeed : List Stmt :=
  [.atom (.hint (.alloc (.n 7) 112)), .atom (.hint (.alloc (.n 8) 112)),
    .atom (.const (.n 9) (word 13503953895743350343 11912009169889063794 0)),
    .atom (.const (.n 10) (word 11170449402626986623 6620516960021240235 0)),
    .atom (.const (.n 11) (word 64 4294967295 0)),
    .atom (.blake2s (.n 2) (.n 3) (.n 0) (.n 1) (.n 9) (.n 10) (.n 12) (.n 13) (.n 11)),
    .atom (.hint (.alloc (.n 14) 8192)), .atom (.hint (.witness "stream" (.heap (.n 14) 0 8192)))]

/-- Read `k` of the eight announced words. -/
def bRead (k : ℕ) : List Stmt := fsNextT (.n (rdS k)) (.n (rdS k + 1)) (.n 14) k (rdB k)

/-- The eight announced words, the row counts stored (G:2103-2107). -/
def bReads : List Stmt :=
  bRead 0 ++ [.atom (.hint (.alloc (.n 30) 6))] ++
    ((List.range 6).map fun t ↦ bRead (t + 1) ++
      [.atom (.load (.n (rdB (t + 1))) (.n 30) t)]).flatten ++ bRead 7

/-- The rate, `dims_g[0]` and the memory's log (G:2108-2115). -/
def bSizes : List Stmt :=
  [.call "g_power_of_word__L6" [.n 121, .n 5] [.n 136],
    .atom (.const (.n 137) (word 2 0 0)), .atom (.mul (.n 136) (.n 138) (.n 137)),
    .atom (.const (.n 139) (word 8 0 0)),
    .atom (.rangeCheck (.n 138) (.n 140) (.n 141) (.n 142) (.n 139)),
    .atom (.hint (.alloc (.n 143) 7)),
    .call "g_power_of_word__L6" [.n 15, .n 5] [.n 144],
    .atom (.const (.n 145) (word 4294967296 0 0)),
    .atom (.rangeCheck (.n 144) (.n 146) (.n 147) (.n 148) (.n 145)),
    .atom (.const (.n 149) (word 4294967296 0 0)), .atom (.const (.n 150) (word 65536 0 0)),
    .atom (.mul (.n 144) (.n 151) (.n 150)),
    .atom (.rangeCheck (.n 151) (.n 152) (.n 153) (.n 154) (.n 149)),
    .atom (.load (.n 144) (.n 143) 0),
    .atom (.hint (.witness "table_logs" (.heap (.n 143) 1 6)))]

/-- `kappa_base` (G:2117-2120). -/
def bKBase : List Stmt :=
  [.atom (.hint (.alloc (.n 155) 8)), .atom (.const (.n 156) (word 1 0 0)),
    .atom (.load (.n 156) (.n 155) 0), .atom (.load (.n 144) (.n 155) 1)] ++
    ((List.range 6).map fun t ↦ [.atom (.load (.n (157 + t)) (.n 143) (1 + t)),
      .atom (.load (.n (157 + t)) (.n 155) (2 + t))]).flatten

/-- Block `b` of `block_kappa`. -/
def bkBlk (b : ℕ) : List Stmt :=
  if b = 2 ∨ b = 39 then
    [.atom (.load (.n (bkV b)) (.n 155) 0), .atom (.const (.n (bkV b + 1)) (word 262144 0 0)),
      .atom (.mul (.n (bkV b + 2)) (.n (bkV b)) (.n (bkV b + 1))),
      .atom (.load (.n (bkV b + 2)) (.n 163) b)]
  else
    [.atom (.load (.n (bkV b)) (.n 155) (blockKappaSrc.getD b 0)),
      .atom (.load (.n (bkV b)) (.n 163) b)]

/-- `block_kappa` (G:2121-2123). -/
def bBlockKappa : List Stmt :=
  .atom (.hint (.alloc (.n 163) 102)) :: ((List.range 102).map bkBlk).flatten

/-- Push block `b + 1`. -/
def pushBlk (b : ℕ) : List Stmt :=
  [.atom (.load (.n (pushK (b + 1))) (.n 163) (b + 1)),
    .atom (.mul (.n (pushK (b + 1) + 1)) (.n 5) (.n (pushK (b + 1)))),
    .atom (.load (.n (pushK (b + 1) + 2)) (.n (pushK (b + 1) + 1)) 0),
    .atom (.mul (.n (pushP (b + 1))) (.n (pushP b)) (.n (pushK (b + 1) + 2)))]

/-- The push side's total and `g_bus_mu` (G:2124-2128). -/
def bPush : List Stmt :=
  [.atom (.load (.n 270) (.n 163) 0), .atom (.mul (.n 271) (.n 5) (.n 270)),
    .atom (.load (.n 272) (.n 271) 0)] ++ ((List.range 36).map pushBlk).flatten ++
    [.call "log2_ceil_in_the_exponent__L0_L34" [.n 416, .n 4, .n 5] [.n 417],
      .atom (.hint (.allocDyn (.n 418) (.n 417)))]

/-- The root (G:2131-2135). -/
def bRoot : List Stmt :=
  fsNextT (.n 134) (.n 135) (.n 14) 8 419 ++ fsNextT (.n 432) (.n 433) (.n 14) 9 434 ++
    [.call "assert_canonical" [.n 419] [.n 449], .call "assert_canonical" [.n 434] [.n 450]]

/-- `m` squeezes from the cells `s0`, stored at `out`. -/
def bSqueezes (m s0 b0 : ℕ) (out : V) : List Stmt :=
  ((List.range m).map fun k ↦
    squeezeT (.n (if k = 0 then s0 else b0 + 14 * (k - 1) + 5))
      (.n ((if k = 0 then s0 else b0 + 14 * (k - 1) + 5) + 1)) (b0 + 14 * k) ++
      [.atom (.load (.n (b0 + 14 * k + 13)) out k)]).flatten

/-- The bus challenges (G:2141-2147): the `alpha`s, `fp_w`, `beta`, the cursor. -/
def bBus : List Stmt :=
  .atom (.hint (.alloc (.n 451) 4)) :: bSqueezes 4 447 452 (.n 451) ++
    .atom (.hint (.alloc (.n 508) 16)) ::
      ((List.range 16).map fun x ↦ (eqwEntry x (eqwStart x)).1).flatten ++
    squeezeT (.n 499) (.n 500) 685 ++
    [.atom (.const (.n 699) (word 1024 0 0)), .atom (.mul (.n 700) (.n 14) (.n 699))]

/-- GKR, the tables and Flock (G:2150-2168). -/
def bCalls : List Stmt :=
  [.call "verify_bus_gkr" [.n 690, .n 691, .n 700, .n 417, .n 418]
      [.n 701, .n 702, .n 703, .n 704, .n 705, .n 706],
    .atom (.copy (.n 707) (.n 701)), .atom (.copy (.n 708) (.n 702)),
    .atom (.hint (.alloc (.n 709) 34)),
    .call "verify_tables" [.n 707, .n 708, .n 703, .n 0, .n 1, .n 418, .n 417, .n 143, .n 30,
      .n 163, .n 5, .n 508, .n 698, .n 7, .n 8, .n 709, .n 704, .n 705, .n 706]
      [.n 710, .n 711, .n 712, .n 713, .n 714, .n 715],
    .atom (.copy (.n 716) (.n 710)), .atom (.copy (.n 717) (.n 711)),
    .atom (.load (.n 718) (.n 143) 6), .atom (.const (.n 719) (word 256 0 0)),
    .atom (.mul (.n 720) (.n 718) (.n 719)), .atom (.hint (.allocDyn (.n 721) (.n 720))),
    .atom (.hint (.alloc (.n 722) 8)), .atom (.hint (.alloc (.n 723) 64)),
    .call "verify_flock" [.n 716, .n 717, .n 712, .n 718, .n 721, .n 722, .n 723]
      [.n 724, .n 725, .n 726, .n 727, .n 728, .n 729],
    .atom (.copy (.n 730) (.n 724)), .atom (.copy (.n 731) (.n 725)),
    .atom (.hint (.alloc (.n 732) 6)), .atom (.hint (.alloc (.n 733) 64)),
    .atom (.hint (.alloc (.n 734) 41))]

/-- Stage `st` of `c_table`. -/
def ctStage (st : ℕ) : List Stmt :=
  .atom (.load (.n (ctV st)) (.n 732) st) :: ((List.range (2 ^ st)).map (ctSlot st)).flatten

/-- The ring map: its challenges, `c_table`, the target, `z_vals` (G:2176-2210). -/
def bRing : List Stmt :=
  bSqueezes 6 730 735 (.n 732) ++
    [.atom (.const (.n 819) (word 1 0 0)), .atom (.load (.n 819) (.n 733) 0)] ++
    ((List.range 6).map ctStage).flatten ++
    [.atom (.hint (.alloc (.n 1144) 130)), .atom (.const (.n 1145) (word 1 0 0)),
      .atom (.load (.n 1145) (.n 1144) 0), .atom (.const (.n 1146) (word 0 0 0)),
      .atom (.load (.n 1146) (.n 1144) 1), .atom (.const (.n 1147) (word 1 0 0)),
      .call "__loop84" [.n 1147, .n 723, .n 732, .n 1144] [],
      .atom (.const (.n 1148) (word 325 0 0)), .atom (.mul (.n 1149) (.n 1144) (.n 1148)),
      .atom (.load (.n 1150) (.n 1149) 1)] ++
    ((List.range 8).map fun t ↦ [.atom (.load (.n (1151 + t)) (.n 722) (7 - t)),
      .atom (.load (.n (1151 + t)) (.n 734) t)]).flatten ++
    [.atom (.const (.n 1159) (word 1 0 0)), .atom (.add (.n 1160) (.n 1159) (.n 718)),
      .atom (.const (.n 1161) (word 1 0 0)), .atom (.const (.n 1162) (word 256 0 0)),
      .atom (.mul (.n 1163) (.n 734) (.n 1162)), .atom (.const (.n 1164) (word 256 0 0)),
      .atom (.mul (.n 1165) (.n 721) (.n 1164)),
      .callIf (.n 1160) "__loop85" [.n 1161, .n 718, .n 1163, .n 1165]]

/-- Claim `j + 1` of the batching. -/
def lpBlk (j : ℕ) : List Stmt :=
  [.atom (.mul (.n (lpP (j + 1))) (.n (lpP j)) (.n 1179)),
    .atom (.load (.n (lpP (j + 1))) (.n 1180) (j + 1)),
    .atom (.load (.n (lpP (j + 1) + 1)) (.n 7) (j + 1)),
    .atom (.mul (.n (lpP (j + 1) + 2)) (.n (lpP (j + 1))) (.n (lpP (j + 1) + 1))),
    .atom (.add (.n (lpT (j + 1))) (.n (lpT j)) (.n (lpP (j + 1) + 2)))]

/-- The batching (G:2219-2229). -/
def bLam : List Stmt :=
  squeezeT (.n 810) (.n 811) 1166 ++
    [.atom (.hint (.alloc (.n 1180) 112)), .atom (.load (.n 1179) (.n 1180) 0),
      .atom (.load (.n 1181) (.n 7) 0), .atom (.mul (.n 1182) (.n 1179) (.n 1181)),
      .atom (.add (.n 1183) (.n 1150) (.n 1182))] ++
    ((List.range 111).map lpBlk).flatten ++ [.atom (.mul (.n 1628) (.n 1624) (.n 1179))]

/-- The stack's size, the opening and the terminal (G:2231-2263). -/
def bOpen : List Stmt :=
  [.call "certify_placement" [.n 155, .n 5] [.n 1629, .n 1630, .n 1631],
    .call "log2_ceil_in_the_exponent__L15_L34" [.n 1629, .n 4, .n 5] [.n 1632],
    .atom (.const (.n 1633) (word 8198552432976855044 0 0)),
    .atom (.mul (.n 1634) (.n 1632) (.n 1633)), .atom (.const (.n 1635) (word 64 0 0)),
    .atom (.rangeCheck (.n 1634) (.n 1636) (.n 1637) (.n 1638) (.n 1635)),
    .atom (.mul (.n 1639) (.n 138) (.n 138)), .atom (.mul (.n 1640) (.n 1639) (.n 138)),
    .atom (.mul (.n 1641) (.n 1640) (.n 1640)), .atom (.mul (.n 1642) (.n 1641) (.n 138)),
    .atom (.mul (.n 1643) (.n 1634) (.n 1642)), .atom (.const (.n 1644) (word 134217728 0 0)),
    .atom (.rangeCheck (.n 1643) (.n 1645) (.n 1646) (.n 1647) (.n 1644)),
    .dispatch (.n 1643) openNames [.n 1171, .n 1172, .n 1627, .n 419, .n 434, .n 726]
      [.n 1648, .n 1649, .n 1650, .n 1651],
    .call "check_opening_terminal" [.n 418, .n 709, .n 715, .n 417, .n 713, .n 144, .n 718, .n 8,
      .n 1180, .n 1630, .n 1631, .n 734, .n 733, .n 1649, .n 1650, .n 1651, .n 1648] []]

/-- A copy from `src[i]` into `defer_out[j]` through the value `v`. -/
def cpBlk (v : ℕ) (src : V) (i j : ℕ) : List Stmt :=
  [.atom (.load (.n v) src i), .atom (.load (.n v) (.n 6) j)]

/-- `defer_out` (G:2265-2279). -/
def bDefer : List Stmt :=
  ((List.range 18).map fun k ↦ cpBlk (1652 + k) (.n 418) k k).flatten ++
    ((List.range 4).map fun k ↦ cpBlk (1670 + k) (.n 451) k (18 + k)).flatten ++
    [.atom (.load (.n 714) (.n 6) 22), .atom (.load (.n 728) (.n 6) 23),
      .atom (.load (.n 727) (.n 6) 24)] ++
    ((List.range 8).map fun k ↦ cpBlk (1674 + 2 * k) (.n 721) k (25 + k) ++
      cpBlk (1675 + 2 * k) (.n 722) k (33 + k)).flatten ++
    ((List.range 64).map fun k ↦ cpBlk (1690 + k) (.n 723) k (41 + k)).flatten ++
    [.atom (.load (.n 729) (.n 6) 105)]

/-- **`verify_sub`'s statements before its `ret`**, generated. -/
def vsBody : List Stmt :=
  bSeed ++ bReads ++ bSizes ++ bKBase ++ bBlockKappa ++ bPush ++ bRoot ++ bBus ++ bCalls ++
    bRing ++ bLam ++ bOpen ++ bDefer

theorem vsPre_eq : vsPre = vsBody := stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1.VerifySub
