/-
  LeanVM.Guest.B1.Gkr.GlT

  The templates of `gkr_layer__L{par}_L{odd}` (a radix-four layer of `verify_bus_gkr`) and of its
  loop, checked against the eight bodies.
-/

module

public import LeanVM.Guest.B1.Gkr.LayerTail
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.CoreData
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«gkr_layer__L»
import LeanVM.Guest.Data.ValNames.«gkr_layer__L_loop0»
import LeanVM.Guest.Data.ValNames.«gkr_layer__L0_L0»

/-!
# A radix-four layer's templates

`gkr_layer__L{p}_L{o}(layers, rounds, gkr_pts, x_m, x_j, start_g, g_bus_mu, tabs, stream)` runs the
radix-four layer `j = 4m + p` (`x_m = g^m`, `x_j = g^j`) at the depth's parity `o`. Its body
(`glBody p o`, in pieces):

* `glPre`: the slot at `layers·(x_j²·start_g)^10` (`15`), its capacity (`16 .. 20`), cursor (`21`),
  the combiner's permutation and combiner (its first cell `27`), the values (`40 .. 42`), the round
  position (`43`), the point row `gkr_pts·(x_j·g)^40` (`52`), the head record `rounds·pos` (`53`),
  the combined claim (`57`);
* `glHeadRounds p`: `2p` rounds (`glRounds`, from value `58`) at the slot's cursor, their
  challenges at `pt[42 + q]`;
* `glHeadStore p`: the head record (capacity, cursor, claim);
* `glLoopCall p nm`: the loop `nm` from `g^0` to `x_m` on the head, the row `qrow = pt·g^(2p)`
  and `nqrow = qrow·g^42`;
* `glTailSetup p`: the last record `head·x_m`, `tpt = qrow·x_m^8`, `ntpt = nqrow·x_m^8`, the
  record's capacity, cursor and claim;
* `glTailRounds p o`: the last `2 - o` rounds, their challenges at `ntpt[q]`; `glPad p o`: at an
  odd depth a zero at `ntpt[1]`;
* the rest, `glTail o` renamed by `glRho p o` (the canonical numbering is `p = 0`, `o = 0`'s):
  `glKids` (the twelve children read, two permutations), `glCheck` (their check), `glY` (the two
  new coordinates, stored at `pt[40]`, `pt[41]`), `glNext` (the next slot) and the return.

Past the prefix, a value of `p ≥ 1` sits `glD p = 78p + 6` on from `p = 0`'s. The loop's body is
`glLoopBody nm` (the same for the eight): eight rounds from the record `head·y` at `qrow·y^8`,
their challenges at `nqrow·y^8`, then the record at `head·y·g`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Five consecutive values. -/
def glCap (b : ℕ) : List V := (List.range 5).map fun k ↦ .n (b + k)

/-! ## Rounds -/

/-- Round `q` of a run from value `B`: at `B + 39q`, on the claim and capacity the previous round
left (`claim0`, `cap0` for the first). -/
def glRound (B : ℕ) (cur pt npt : V) (noff : ℕ) (claim0 : V) (cap0 : List V) (q : ℕ) :
    List Stmt :=
  gkRoundN (B + 39 * q) q cur pt npt noff (if q = 0 then claim0 else .n (B + 39 * q - 1))
    (if q = 0 then cap0 else glCap (B + 39 * q - 19))

/-- `n` rounds from value `B`. -/
def glRounds (B n : ℕ) (cur pt npt : V) (noff : ℕ) (claim0 : V) (cap0 : List V) : List Stmt :=
  ((List.range n).map (glRound B cur pt npt noff claim0 cap0)).flatten

/-! ## The layer -/

/-- Values past the prefix: `p ≥ 1` adds the cursor's, `qrow`'s and `tpt`'s products. -/
def glD (p : ℕ) : ℕ := if p = 0 then 0 else 78 * p + 6

/-- The prefix, common to the eight bodies. -/
def glPre : List Stmt :=
  [.atom (.mul (.n (valf% «gkr_layer» "x_layer~0")) (.n (valf% «gkr_layer» "x_j")) (.n (valf% «gkr_layer» "x_j"))),
    .atom (.mul (.n (valf% «gkr_layer» "x_layer")) (.n (valf% «gkr_layer» "x_layer~0")) (.n (valf% «gkr_layer» "start_g"))),
    .atom (.mul (.n (valf% «gkr_layer» "layer~0")) (.n (valf% «gkr_layer» "x_layer")) (.n (valf% «gkr_layer» "x_layer"))),
    .atom (.mul (.n (valf% «gkr_layer» "layer~1")) (.n (valf% «gkr_layer» "layer~0")) (.n (valf% «gkr_layer» "layer~0"))),
    .atom (.mul (.n (valf% «gkr_layer» "layer~2")) (.n (valf% «gkr_layer» "layer~1")) (.n (valf% «gkr_layer» "x_layer"))),
    .atom (.mul (.n (valf% «gkr_layer» "layer~3")) (.n (valf% «gkr_layer» "layer~2")) (.n (valf% «gkr_layer» "layer~2"))),
    .atom (.mul (.n (valf% «gkr_layer» "layer")) (.n (valf% «gkr_layer» "layers")) (.n (valf% «gkr_layer» "layer~3"))),
    .atom (.load (.n (valf% «gkr_layer» "sp[0]@1")) (.n (valf% «gkr_layer» "layer")) 0),
    .atom (.load (.n (valf% «gkr_layer» "sp[1]@1")) (.n (valf% «gkr_layer» "layer")) 1),
    .atom (.load (.n (valf% «gkr_layer» "sp[2]@1")) (.n (valf% «gkr_layer» "layer")) 2),
    .atom (.load (.n (valf% «gkr_layer» "sp[3]@1")) (.n (valf% «gkr_layer» "layer")) 3),
    .atom (.load (.n (valf% «gkr_layer» "sp[4]@1")) (.n (valf% «gkr_layer» "layer")) 4),
    .atom (.load (.n (valf% «gkr_layer» "s4#0")) (.n (valf% «gkr_layer» "layer")) 5),
    .atom (.const (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0")) (word 1 0)),
    .atom (.const (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]")) (word 0 0)),
    .atom (.const (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[2]")) (word 0 0)),
    .atom (.const (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[3]")) (word 0 0)),
    .atom (.const (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[4]")) (word 0 0)),
    .atom (.keccak [.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[2]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[3]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[4]"), .n (valf% «gkr_layer» "sp[0]@1"), .n (valf% «gkr_layer» "sp[1]@1"), .n (valf% «gkr_layer» "sp[2]@1"), .n (valf% «gkr_layer» "sp[3]@1"), .n (valf% «gkr_layer» "sp[4]@1")] [.n (valf% «gkr_layer» "nxt[0]@1"), .n (valf% «gkr_layer» "nxt[1]@1"), .n (valf% «gkr_layer» "nxt[2]@1"), .n (valf% «gkr_layer» "nxt[3]@1"), .n (valf% «gkr_layer» "nxt[4]@1"), .n (valf% «gkr_layer» "nxt[5]@1"), .n (valf% «gkr_layer» "nxt[6]@1"), .n (valf% «gkr_layer» "nxt[7]@1"), .n (valf% «gkr_layer» "nxt[8]@1"), .n (valf% «gkr_layer» "nxt[9]@1"), .n (valf% «gkr_layer» "nxt[10]@1"), .n (valf% «gkr_layer» "nxt[11]@1"), .n (valf% «gkr_layer» "nxt[12]@1")] false false),
    .atom (.load (.n (valf% «gkr_layer» "layer_vals[0]")) (.n (valf% «gkr_layer» "layer")) 6),
    .atom (.load (.n (valf% «gkr_layer» "layer_vals[1]")) (.n (valf% «gkr_layer» "layer")) 7),
    .atom (.load (.n (valf% «gkr_layer» "layer_vals[2]")) (.n (valf% «gkr_layer» "layer")) 8),
    .atom (.load (.n (valf% «gkr_layer» "round_pos")) (.n (valf% «gkr_layer» "layer")) 9),
    .atom (.const (.n (valf% «gkr_layer» "point_row~0")) (word 2 0)),
    .atom (.mul (.n (valf% «gkr_layer» "point_row~1")) (.n (valf% «gkr_layer» "x_j")) (.n (valf% «gkr_layer» "point_row~0"))),
    .atom (.mul (.n (valf% «gkr_layer» "point_row~2")) (.n (valf% «gkr_layer» "point_row~1")) (.n (valf% «gkr_layer» "point_row~1"))),
    .atom (.mul (.n (valf% «gkr_layer» "point_row~3")) (.n (valf% «gkr_layer» "point_row~2")) (.n (valf% «gkr_layer» "point_row~2"))),
    .atom (.mul (.n (valf% «gkr_layer» "point_row~4")) (.n (valf% «gkr_layer» "point_row~3")) (.n (valf% «gkr_layer» "point_row~1"))),
    .atom (.mul (.n (valf% «gkr_layer» "point_row~5")) (.n (valf% «gkr_layer» "point_row~4")) (.n (valf% «gkr_layer» "point_row~4"))),
    .atom (.mul (.n (valf% «gkr_layer» "point_row~6")) (.n (valf% «gkr_layer» "point_row~5")) (.n (valf% «gkr_layer» "point_row~5"))),
    .atom (.mul (.n (valf% «gkr_layer» "point_row~7")) (.n (valf% «gkr_layer» "point_row~6")) (.n (valf% «gkr_layer» "point_row~6"))),
    .atom (.mul (.n (valf% «gkr_layer» "point_row")) (.n (valf% «gkr_layer» "gkr_pts")) (.n (valf% «gkr_layer» "point_row~7"))),
    .atom (.mul (.n (valf% «gkr_layer» "head")) (.n (valf% «gkr_layer» "rounds")) (.n (valf% «gkr_layer» "round_pos"))),
    .atom (.mul (.n (valf% «gkr_layer» "claim@1~0")) (.n (valf% «gkr_layer» "nxt[0]@1")) (.n (valf% «gkr_layer» "layer_vals[2]"))),
    .atom (.add (.n (valf% «gkr_layer» "claim@1")) (.n (valf% «gkr_layer» "layer_vals[1]")) (.n (valf% «gkr_layer» "claim@1~0"))),
    .atom (.mul (.n (valf% «gkr_layer» "claim@2~0")) (.n (valf% «gkr_layer» "nxt[0]@1")) (.n (valf% «gkr_layer» "claim@1"))),
    .atom (.add (.n (valf% «gkr_layer» "claim@2")) (.n (valf% «gkr_layer» "layer_vals[0]")) (.n (valf% «gkr_layer» "claim@2~0")))]

/-- The head rounds. -/
def glHeadRounds (p : ℕ) : List Stmt :=
  glRounds 58 (2 * p) (.n (valf% «gkr_layer» "s4#0")) (.n (valf% «gkr_layer» "point_row")) (.n (valf% «gkr_layer» "point_row")) 42 (.n (valf% «gkr_layer» "claim@2")) (glCap (valf% «gkr_layer» "nxt[8]@1"))

/-- The head record's stores, at `p = 0`. -/
def glHeadStore0 : List Stmt :=
  (List.range 5).map (fun k ↦ .atom (.load (.n ((valf% «gkr_layer» "nxt[8]@1") + k)) (.n (valf% «gkr_layer» "head")) (862 * k))) ++
    [.atom (.load (.n (valf% «gkr_layer» "s4#0")) (.n (valf% «gkr_layer» "head")) 4310), .atom (.load (.n (valf% «gkr_layer» "claim@2")) (.n (valf% «gkr_layer» "head")) 5172)]

/-- The head record's stores, at `p ≥ 1`: the cursor `8p` words on. -/
def glHeadStoreP (p : ℕ) : List Stmt :=
  (List.range 5).map (fun k ↦ .atom (.load (.n (39 + 78 * p + k)) (.n (valf% «gkr_layer» "head")) (862 * k))) ++
    [.atom (.const (.n (58 + 78 * p)) (word (2 ^ (8 * p)) 0)),
      .atom (.mul (.n (59 + 78 * p)) (.n (valf% «gkr_layer» "s4#0")) (.n (58 + 78 * p))),
      .atom (.load (.n (59 + 78 * p)) (.n (valf% «gkr_layer» "head")) 4310), .atom (.load (.n (57 + 78 * p)) (.n (valf% «gkr_layer» "head")) 5172)]

def glHeadStore (p : ℕ) : List Stmt := if p = 0 then glHeadStore0 else glHeadStoreP p

/-- The loop's call, at `p = 0`. -/
def glLoopCall0 (nm : String) : List Stmt :=
  [.atom (.const (.n (val% «gkr_layer__L0_L0» "s20#0")) (word 1 0)), .atom (.add (.n (val% «gkr_layer__L0_L0» "s20#1")) (.n (val% «gkr_layer__L0_L0» "s20#0")) (.n (valf% «gkr_layer» "x_m"))),
    .atom (.const (.n (val% «gkr_layer__L0_L0» "s20#2")) (word 1 0)), .atom (.const (.n (val% «gkr_layer__L0_L0» "s20#3")) (word (2 ^ 42) 0)),
    .atom (.mul (.n (val% «gkr_layer__L0_L0» "s20#4")) (.n (valf% «gkr_layer» "point_row")) (.n (val% «gkr_layer__L0_L0» "s20#3"))),
    .callIf (.n (val% «gkr_layer__L0_L0» "s20#1")) nm [.n (val% «gkr_layer__L0_L0» "s20#2"), .n (valf% «gkr_layer» "x_m"), .n (valf% «gkr_layer» "head"), .n (valf% «gkr_layer» "point_row"), .n (val% «gkr_layer__L0_L0» "s20#4"), .n (valf% «gkr_layer» "tabs")]]

/-- The loop's call, at `p ≥ 1`. -/
def glLoopCallP (p : ℕ) (nm : String) : List Stmt :=
  [.atom (.const (.n (60 + 78 * p)) (word 1 0)),
    .atom (.add (.n (61 + 78 * p)) (.n (60 + 78 * p)) (.n (valf% «gkr_layer» "x_m"))),
    .atom (.const (.n (62 + 78 * p)) (word 1 0)),
    .atom (.const (.n (63 + 78 * p)) (word (2 ^ (2 * p)) 0)),
    .atom (.mul (.n (64 + 78 * p)) (.n (valf% «gkr_layer» "point_row")) (.n (63 + 78 * p))),
    .atom (.const (.n (65 + 78 * p)) (word (2 ^ (42 + 2 * p)) 0)),
    .atom (.mul (.n (66 + 78 * p)) (.n (valf% «gkr_layer» "point_row")) (.n (65 + 78 * p))),
    .callIf (.n (61 + 78 * p)) nm
      [.n (62 + 78 * p), .n (valf% «gkr_layer» "x_m"), .n (valf% «gkr_layer» "head"), .n (64 + 78 * p), .n (66 + 78 * p), .n (valf% «gkr_layer» "tabs")]]

def glLoopCall (p : ℕ) (nm : String) : List Stmt :=
  if p = 0 then glLoopCall0 nm else glLoopCallP p nm

/-- The last record's loads, from `head·x_m` (at `w`) into `71 + glD p ..`. -/
def glTailLoads (p w : ℕ) : List Stmt :=
  (List.range 5).map (fun k ↦ .atom (.load (.n (71 + glD p + k)) (.n w) (862 * k))) ++
    [.atom (.load (.n (76 + glD p)) (.n w) 4310), .atom (.load (.n (77 + glD p)) (.n w) 5172)]

/-- The tail's pointers, at `p = 0`. -/
def glTailSetup0 : List Stmt :=
  [.atom (.mul (.n (val% «gkr_layer__L0_L0» "rd_last")) (.n (valf% «gkr_layer» "head")) (.n (valf% «gkr_layer» "x_m"))), .atom (.mul (.n (val% «gkr_layer__L0_L0» "m2")) (.n (valf% «gkr_layer» "x_m")) (.n (valf% «gkr_layer» "x_m"))),
    .atom (.mul (.n (val% «gkr_layer__L0_L0» "m4")) (.n (val% «gkr_layer__L0_L0» "m2")) (.n (val% «gkr_layer__L0_L0» "m2"))), .atom (.mul (.n (val% «gkr_layer__L0_L0» "m8")) (.n (val% «gkr_layer__L0_L0» "m4")) (.n (val% «gkr_layer__L0_L0» "m4"))),
    .atom (.mul (.n (val% «gkr_layer__L0_L0» "tpt")) (.n (valf% «gkr_layer» "point_row")) (.n (val% «gkr_layer__L0_L0» "m8"))), .atom (.const (.n (val% «gkr_layer__L0_L0» "ntpt~0")) (word (2 ^ 42) 0)),
    .atom (.mul (.n (val% «gkr_layer__L0_L0» "ntpt~1")) (.n (valf% «gkr_layer» "point_row")) (.n (val% «gkr_layer__L0_L0» "ntpt~0"))), .atom (.mul (.n (val% «gkr_layer__L0_L0» "ntpt")) (.n (val% «gkr_layer__L0_L0» "ntpt~1")) (.n (val% «gkr_layer__L0_L0» "m8")))] ++
  glTailLoads 0 63

/-- The tail's pointers, at `p ≥ 1`. -/
def glTailSetupP (p : ℕ) : List Stmt :=
  [.atom (.mul (.n (67 + 78 * p)) (.n (valf% «gkr_layer» "head")) (.n (valf% «gkr_layer» "x_m"))),
    .atom (.mul (.n (68 + 78 * p)) (.n (valf% «gkr_layer» "x_m")) (.n (valf% «gkr_layer» "x_m"))),
    .atom (.mul (.n (69 + 78 * p)) (.n (68 + 78 * p)) (.n (68 + 78 * p))),
    .atom (.mul (.n (70 + 78 * p)) (.n (69 + 78 * p)) (.n (69 + 78 * p))),
    .atom (.const (.n (71 + 78 * p)) (word (2 ^ (2 * p)) 0)),
    .atom (.mul (.n (72 + 78 * p)) (.n (valf% «gkr_layer» "point_row")) (.n (71 + 78 * p))),
    .atom (.mul (.n (73 + 78 * p)) (.n (72 + 78 * p)) (.n (70 + 78 * p))),
    .atom (.const (.n (74 + 78 * p)) (word (2 ^ (42 + 2 * p)) 0)),
    .atom (.mul (.n (75 + 78 * p)) (.n (valf% «gkr_layer» "point_row")) (.n (74 + 78 * p))),
    .atom (.mul (.n (76 + 78 * p)) (.n (75 + 78 * p)) (.n (70 + 78 * p)))] ++
  glTailLoads p (67 + 78 * p)

def glTailSetup (p : ℕ) : List Stmt := if p = 0 then glTailSetup0 else glTailSetupP p

/-- The last `2 - o` rounds, from the last record's state at `72 + glD p ..`. -/
def glTailRounds (p o : ℕ) : List Stmt :=
  glRounds (78 + glD p) (2 - o) (.n (76 + glD p)) (.n (67 + glD p)) (.n (70 + glD p)) 0
    (.n (77 + glD p)) (glCap (71 + glD p))

/-- At an odd depth, the row's zero cell. -/
def glPad (p o : ℕ) : List Stmt :=
  if o = 1 then
    [.atom (.const (.n (117 + glD p)) (word 0 0)),
      .atom (.load (.n (117 + glD p)) (.n (70 + glD p)) 1)]
  else []

/-- The canonical numbering's values at `p`, `o`: the last record's from `63` on by `glD p`,
the last round's from `117` less a round at an odd depth, the rest past the pad's zero. -/
def glRho (p o : ℕ) (v : V) : V :=
  if v.idx < 58 then v
  else if v.idx < 117 then .n (v.idx + glD p)
  else if v.idx < 156 then .n (v.idx + glD p - 39 * o)
  else .n (v.idx + glD p - 38 * o)

/-- The children, read `off` words past the tail cursor `77`: four, a permutation, four, a
permutation, four. -/
def glKids (off : ℕ) : List Stmt :=
  ((List.range 4).map (chT (.n (val% «gkr_layer__L0_L0» "tcur")) off (val% «gkr_layer__L0_L0» "x@9"))).flatten ++
    [.atom (.keccak (chRate (val% «gkr_layer__L0_L0» "x@9") 0 ++ glCap (val% «gkr_layer__L0_L0» "nxt[8]@3")) (lyOuts (val% «gkr_layer__L0_L0» "nxt[0]@4")) false false)] ++
    ((List.range 4).map fun i ↦ chT (.n (val% «gkr_layer__L0_L0» "tcur")) off (val% «gkr_layer__L0_L0» "x@9") (4 + i)).flatten ++
    [.atom (.keccak (chRate (val% «gkr_layer__L0_L0» "x@9") 1 ++ lyCap (val% «gkr_layer__L0_L0» "nxt[0]@4")) (lyOuts (val% «gkr_layer__L0_L0» "nxt[0]@5")) false false)] ++
    ((List.range 4).map fun i ↦ chT (.n (val% «gkr_layer__L0_L0» "tcur")) off (val% «gkr_layer__L0_L0» "x@9") (8 + i)).flatten

/-- The children's check against the last claim `158` (`gkr_product_check`). -/
def glCheck : List Stmt :=
  [.atom (.mul (.n (val% «gkr_layer__L0_L0» "product@1")) (.n (val% «gkr_layer__L0_L0» "evals[8]")) (.n (val% «gkr_layer__L0_L0» "evals[9]"))),
    .atom (.mul (.n (val% «gkr_layer__L0_L0» "product@2")) (.n (val% «gkr_layer__L0_L0» "product@1")) (.n (val% «gkr_layer__L0_L0» "evals[10]"))),
    .atom (.mul (.n (val% «gkr_layer__L0_L0» "product@3")) (.n (val% «gkr_layer__L0_L0» "product@2")) (.n (val% «gkr_layer__L0_L0» "evals[11]"))),
    .atom (.const (.n (val% «gkr_layer__L0_L0» "combined@1~0")) (word 0 0)),
    .atom (.mul (.n (val% «gkr_layer__L0_L0» "combined@1~1")) (.n (val% «gkr_layer__L0_L0» "nxt[0]@1")) (.n (val% «gkr_layer__L0_L0» "combined@1~0"))),
    .atom (.add (.n (val% «gkr_layer__L0_L0» "combined@1")) (.n (val% «gkr_layer__L0_L0» "product@3")) (.n (val% «gkr_layer__L0_L0» "combined@1~1"))),
    .atom (.mul (.n (val% «gkr_layer__L0_L0» "product@4")) (.n (val% «gkr_layer__L0_L0» "evals[4]")) (.n (val% «gkr_layer__L0_L0» "evals[5]"))),
    .atom (.mul (.n (val% «gkr_layer__L0_L0» "product@5")) (.n (val% «gkr_layer__L0_L0» "product@4")) (.n (val% «gkr_layer__L0_L0» "evals[6]"))),
    .atom (.mul (.n (val% «gkr_layer__L0_L0» "product@6")) (.n (val% «gkr_layer__L0_L0» "product@5")) (.n (val% «gkr_layer__L0_L0» "evals[7]"))),
    .atom (.mul (.n (val% «gkr_layer__L0_L0» "combined@2~0")) (.n (val% «gkr_layer__L0_L0» "nxt[0]@1")) (.n (val% «gkr_layer__L0_L0» "combined@1"))),
    .atom (.add (.n (val% «gkr_layer__L0_L0» "combined@2")) (.n (val% «gkr_layer__L0_L0» "product@6")) (.n (val% «gkr_layer__L0_L0» "combined@2~0"))),
    .atom (.mul (.n (val% «gkr_layer__L0_L0» "product@7")) (.n (val% «gkr_layer__L0_L0» "evals[0]")) (.n (val% «gkr_layer__L0_L0» "evals[1]"))),
    .atom (.mul (.n (val% «gkr_layer__L0_L0» "product@8")) (.n (val% «gkr_layer__L0_L0» "product@7")) (.n (val% «gkr_layer__L0_L0» "evals[2]"))),
    .atom (.mul (.n (val% «gkr_layer__L0_L0» "product@9")) (.n (val% «gkr_layer__L0_L0» "product@8")) (.n (val% «gkr_layer__L0_L0» "evals[3]"))),
    .atom (.mul (.n (val% «gkr_layer__L0_L0» "combined@3~0")) (.n (val% «gkr_layer__L0_L0» "nxt[0]@1")) (.n (val% «gkr_layer__L0_L0» "combined@2"))),
    .atom (.add (.n (val% «gkr_layer__L0_L0» "combined@3")) (.n (val% «gkr_layer__L0_L0» "product@9")) (.n (val% «gkr_layer__L0_L0» "combined@3~0"))),
    .atom (.assertEq (.n (val% «gkr_layer__L0_L0» "nclaim@2")) (.n (val% «gkr_layer__L0_L0» "combined@3")))]

/-- The two new coordinates (`y`'s grind of `0` bits, then a squeeze), stored at `pt[40]`,
`pt[41]`. -/
def glY : List Stmt :=
  [.atom (.keccak (chRate (val% «gkr_layer__L0_L0» "x@9") 2 ++ lyCap (val% «gkr_layer__L0_L0» "nxt[0]@5")) (lyOuts (val% «gkr_layer__L0_L0» "nxt[0]@6")) false false),
    .atom (.keccak ([.n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[2]"), .n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[3]"), .n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[4]")] ++ lyCap (val% «gkr_layer__L0_L0» "nxt[0]@6"))
      (lyOuts (val% «gkr_layer__L0_L0» "nxt[0]@7")) false false),
    .atom (.load (.n (val% «gkr_layer__L0_L0» "nxt[0]@6")) (.n (val% «gkr_layer__L0_L0» "point_row")) 40),
    .atom (.load (.n (val% «gkr_layer__L0_L0» "nxt[0]@7")) (.n (val% «gkr_layer__L0_L0» "point_row")) 41)]

/-- The next slot, `20` words on: the capacity, the cursor `cw` words on, the three values and
the position `pos·x_m·g`. -/
def glNext (cw : ℕ) : List Stmt :=
  (List.range 5).map (fun k ↦ .atom (.load (.n ((val% «gkr_layer__L0_L0» "nxt[8]@7") + k)) (.n (val% «gkr_layer__L0_L0» "layer")) (20 + k))) ++
    [.atom (.const (.n (val% «gkr_layer__L0_L0» "s42#0")) (word (2 ^ cw) 0)), .atom (.mul (.n (val% «gkr_layer__L0_L0» "s42#1")) (.n (val% «gkr_layer__L0_L0» "tcur")) (.n (val% «gkr_layer__L0_L0» "s42#0"))),
      .atom (.load (.n (val% «gkr_layer__L0_L0» "s42#1")) (.n (val% «gkr_layer__L0_L0» "layer")) 25)] ++
    chValT (val% «gkr_layer__L0_L0» "x@9") (val% «gkr_layer__L0_L0» "nxt[0]@6") (val% «gkr_layer__L0_L0» "nxt[0]@7") (val% «gkr_layer__L0_L0» "layer") 0 (val% «gkr_layer__L0_L0» "lo@1~0") 26 ++ chValT (val% «gkr_layer__L0_L0» "x@9") (val% «gkr_layer__L0_L0» "nxt[0]@6") (val% «gkr_layer__L0_L0» "nxt[0]@7") (val% «gkr_layer__L0_L0» "layer") 1 (val% «gkr_layer__L0_L0» "lo@2~0") 27 ++
    chValT (val% «gkr_layer__L0_L0» "x@9") (val% «gkr_layer__L0_L0» "nxt[0]@6") (val% «gkr_layer__L0_L0» "nxt[0]@7") (val% «gkr_layer__L0_L0» "layer") 2 (val% «gkr_layer__L0_L0» "lo@3~0") 28 ++
    [.atom (.mul (.n (val% «gkr_layer__L0_L0» "s44#0")) (.n (val% «gkr_layer__L0_L0» "round_pos")) (.n (val% «gkr_layer__L0_L0» "x_m"))), .atom (.const (.n (val% «gkr_layer__L0_L0» "s44#1")) (word 2 0)),
      .atom (.mul (.n (val% «gkr_layer__L0_L0» "s44#2")) (.n (val% «gkr_layer__L0_L0» "s44#0")) (.n (val% «gkr_layer__L0_L0» "s44#1"))), .atom (.load (.n (val% «gkr_layer__L0_L0» "s44#2")) (.n (val% «gkr_layer__L0_L0» "layer")) 29)]

/-- The rest of the body, canonically numbered. -/
def glTail (o : ℕ) : List Stmt :=
  glKids (4 * (2 - o)) ++ glCheck ++ glY ++ glNext (4 * (2 - o) + 12) ++ [.ret []]

/-- **`gkr_layer__L{p}_L{o}`'s body**, its loop `nm`. -/
def glBody (p o : ℕ) (nm : String) : List Stmt :=
  glPre ++ glHeadRounds p ++ glHeadStore p ++ glLoopCall p nm ++ glTailSetup p ++
    glTailRounds p o ++ glPad p o ++ Stmt.renameList (glRho p o) (glTail o)

/-! ## The loop -/

/-- The iteration's pointers (`head·y`, `y^8`, `qrow·y^8`, `nqrow·y^8`) and its record. -/
def glLoopPre : List Stmt :=
  [.atom (.mul (.n (valf% «gkr_layer» «_loop0» "rd")) (.n (valf% «gkr_layer» «_loop0» "head")) (.n (valf% «gkr_layer» «_loop0» "y"))), .atom (.mul (.n (valf% «gkr_layer» «_loop0» "y2")) (.n (valf% «gkr_layer» «_loop0» "y")) (.n (valf% «gkr_layer» «_loop0» "y"))),
    .atom (.mul (.n (valf% «gkr_layer» «_loop0» "y4")) (.n (valf% «gkr_layer» «_loop0» "y2")) (.n (valf% «gkr_layer» «_loop0» "y2"))), .atom (.mul (.n (valf% «gkr_layer» «_loop0» "y8")) (.n (valf% «gkr_layer» «_loop0» "y4")) (.n (valf% «gkr_layer» «_loop0» "y4"))),
    .atom (.mul (.n (valf% «gkr_layer» «_loop0» "pt")) (.n (valf% «gkr_layer» «_loop0» "qrow")) (.n (valf% «gkr_layer» «_loop0» "y8"))), .atom (.mul (.n (valf% «gkr_layer» «_loop0» "npt")) (.n (valf% «gkr_layer» «_loop0» "nqrow")) (.n (valf% «gkr_layer» «_loop0» "y8")))] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n ((valf% «gkr_layer» «_loop0» "sp[0]") + k)) (.n (valf% «gkr_layer» «_loop0» "rd")) (862 * k))) ++
  [.atom (.load (.n (valf% «gkr_layer» «_loop0» "cur")) (.n (valf% «gkr_layer» «_loop0» "rd")) 4310), .atom (.load (.n (valf% «gkr_layer» «_loop0» "claim")) (.n (valf% «gkr_layer» «_loop0» "rd")) 5172)]

/-- The iteration's eight rounds. -/
def glLoopRounds : List Stmt := glRounds 19 8 (.n (valf% «gkr_layer» «_loop0» "cur")) (.n (valf% «gkr_layer» «_loop0» "pt")) (.n (valf% «gkr_layer» «_loop0» "npt")) 0 (.n (valf% «gkr_layer» «_loop0» "claim")) (glCap (valf% «gkr_layer» «_loop0» "sp[0]"))

/-- The next record, the guard and the next call. -/
def glLoopPost (nm : String) : List Stmt :=
  (List.range 5).map (fun k ↦ .atom (.load (.n ((valf% «gkr_layer» «_loop0» "nxt[8]@8") + k)) (.n (valf% «gkr_layer» «_loop0» "rd")) (1 + 862 * k))) ++
  [.atom (.const (.n (valf% «gkr_layer» «_loop0» "s12#0")) (word (2 ^ 32) 0)), .atom (.mul (.n (valf% «gkr_layer» «_loop0» "s12#1")) (.n (valf% «gkr_layer» «_loop0» "cur")) (.n (valf% «gkr_layer» «_loop0» "s12#0"))),
    .atom (.load (.n (valf% «gkr_layer» «_loop0» "s12#1")) (.n (valf% «gkr_layer» «_loop0» "rd")) 4311), .atom (.load (.n (valf% «gkr_layer» «_loop0» "nclaim@8")) (.n (valf% «gkr_layer» «_loop0» "rd")) 5173),
    .atom (.const (.n (valf% «gkr_layer» «_loop0» "s15#0")) (word 2 0)), .atom (.mul (.n (valf% «gkr_layer» «_loop0» "s15#1")) (.n (valf% «gkr_layer» «_loop0» "y")) (.n (valf% «gkr_layer» «_loop0» "s15#0"))),
    .atom (.add (.n (valf% «gkr_layer» «_loop0» "s15#2")) (.n (valf% «gkr_layer» «_loop0» "s15#1")) (.n (valf% «gkr_layer» «_loop0» "bound"))), .atom (.const (.n (valf% «gkr_layer» «_loop0» "s15#3")) (word 2 0)),
    .atom (.mul (.n (valf% «gkr_layer» «_loop0» "s15#4")) (.n (valf% «gkr_layer» «_loop0» "y")) (.n (valf% «gkr_layer» «_loop0» "s15#3"))),
    .callIf (.n (valf% «gkr_layer» «_loop0» "s15#2")) nm [.n (valf% «gkr_layer» «_loop0» "s15#4"), .n (valf% «gkr_layer» «_loop0» "bound"), .n (valf% «gkr_layer» «_loop0» "head"), .n (valf% «gkr_layer» «_loop0» "qrow"), .n (valf% «gkr_layer» «_loop0» "nqrow"), .n (valf% «gkr_layer» «_loop0» "tabs")], .ret []]

/-- **The loop's body**, its own name `nm`. -/
def glLoopBody (nm : String) : List Stmt := glLoopPre ++ glLoopRounds ++ glLoopPost nm

/-! ## The eight functions -/

/-- `gkr_layer__L{p}_L{o}`. -/
def glName : ℕ → ℕ → String
  | 0, 0 => name% «gkr_layer__L0_L0»
  | 1, 0 => name% «gkr_layer__L1_L0»
  | 2, 0 => name% «gkr_layer__L2_L0»
  | 3, 0 => name% «gkr_layer__L3_L0»
  | 0, _ => name% «gkr_layer__L0_L1»
  | 1, _ => name% «gkr_layer__L1_L1»
  | 2, _ => name% «gkr_layer__L2_L1»
  | _, _ => name% «gkr_layer__L3_L1»

/-- Its loop. -/
def glLoopName : ℕ → ℕ → String
  | 0, 0 => name% «gkr_layer__L0_L0_loop0»
  | 1, 0 => name% «gkr_layer__L1_L0_loop0»
  | 2, 0 => name% «gkr_layer__L2_L0_loop0»
  | 3, 0 => name% «gkr_layer__L3_L0_loop0»
  | 0, _ => name% «gkr_layer__L0_L1_loop0»
  | 1, _ => name% «gkr_layer__L1_L1_loop0»
  | 2, _ => name% «gkr_layer__L2_L1_loop0»
  | _, _ => name% «gkr_layer__L3_L1_loop0»

/-- A function of `coreProgram` with these parameters and body. -/
noncomputable def glIs (f : String) (ps : List V) (b : List Stmt) : Bool :=
  match coreProgram.find? f with
  | some fn => decide (fn.params = ps) && tbStmtsEqb fn.body b
  | none => false

theorem glIs_sound {f : String} {ps : List V} {b : List Stmt} (h : glIs f ps b = true) :
    ∃ fn : Fn, coreProgram.find? f = some fn ∧ fn.params = ps ∧ fn.body = b := by
  unfold glIs at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

/-- The layer's parameters. -/
def glParams : List V := (List.range 9).map V.n

/-- The loop's parameters `[y, x_m, head, qrow, nqrow, tabs]`. -/
def glLoopParams : List V := (List.range 6).map V.n


theorem glIs_layers : ∀ p < 4, ∀ o < 2,
    glIs (glName p o) glParams (glBody p o (glLoopName p o)) = true := by
  decide +kernel

theorem glIs_loops : ∀ p < 4, ∀ o < 2,
    glIs (glLoopName p o) glLoopParams (glLoopBody (glLoopName p o)) = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Tables
