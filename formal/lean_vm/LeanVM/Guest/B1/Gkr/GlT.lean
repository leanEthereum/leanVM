/-
  LeanVM.Guest.B1.Gkr.GlT

  The templates of `gkr_layer__L{par}_L{odd}` (a radix-four layer of `verify_bus_gkr`) and of its
  loop, checked against the eight bodies.
-/

module

public import LeanVM.Guest.B1.Gkr.LayerTail
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.CoreData

/-!
# A radix-four layer's templates

`gkr_layer__L{p}_L{o}(layers, rounds, gkr_pts, x_m, x_j, start_g, g_bus_mu, tabs, stream)` runs the
radix-four layer `j = 4m + p` (`x_m = g^m`, `x_j = g^j`) at the depth's parity `o`. Its body
(`glBody p o`, in pieces):

* `glPre`: the slot at `layers·(x_j²·start_g)^10` (`15`), its capacity (`16 .. 20`), cursor (`21`),
  the combiner's permutation and combiner (`40`), the values (`41 .. 43`), the round position
  (`44`), the point row `gkr_pts·(x_j·g)^40` (`53`), the head record `rounds·pos` (`54`), the
  combined claim (`58`);
* `glHeadRounds p`: `2p` rounds (`glRounds`, from value `59`) at the slot's cursor, their
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

Past the prefix, a value of `p ≥ 1` sits `glD p = 80p + 6` on from `p = 0`'s. The loop's body is
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

/-- Round `q` of a run from value `B`: at `B + 40q`, on the claim and capacity the previous round
left (`claim0`, `cap0` for the first). -/
def glRound (B : ℕ) (cur pt npt : V) (noff : ℕ) (claim0 : V) (cap0 : List V) (q : ℕ) :
    List Stmt :=
  gkRoundN (B + 40 * q) q cur pt npt noff (if q = 0 then claim0 else .n (B + 40 * q - 1))
    (if q = 0 then cap0 else glCap (B + 40 * q - 20))

/-- `n` rounds from value `B`. -/
def glRounds (B n : ℕ) (cur pt npt : V) (noff : ℕ) (claim0 : V) (cap0 : List V) : List Stmt :=
  ((List.range n).map (glRound B cur pt npt noff claim0 cap0)).flatten

/-! ## The layer -/

/-- Values past the prefix: `p ≥ 1` adds the cursor's, `qrow`'s and `tpt`'s products. -/
def glD (p : ℕ) : ℕ := if p = 0 then 0 else 80 * p + 6

/-- The prefix, common to the eight bodies. -/
def glPre : List Stmt :=
  [.atom (.mul (.n 9) (.n 4) (.n 4)),
    .atom (.mul (.n 10) (.n 9) (.n 5)),
    .atom (.mul (.n 11) (.n 10) (.n 10)),
    .atom (.mul (.n 12) (.n 11) (.n 11)),
    .atom (.mul (.n 13) (.n 12) (.n 10)),
    .atom (.mul (.n 14) (.n 13) (.n 13)),
    .atom (.mul (.n 15) (.n 0) (.n 14)),
    .atom (.load (.n 16) (.n 15) 0),
    .atom (.load (.n 17) (.n 15) 1),
    .atom (.load (.n 18) (.n 15) 2),
    .atom (.load (.n 19) (.n 15) 3),
    .atom (.load (.n 20) (.n 15) 4),
    .atom (.load (.n 21) (.n 15) 5),
    .atom (.const (.n 22) (word 1 0)),
    .atom (.const (.n 23) (word 0 0)),
    .atom (.const (.n 24) (word 0 0)),
    .atom (.const (.n 25) (word 0 0)),
    .atom (.const (.n 26) (word 0 0)),
    .atom (.keccak [.n 23, .n 23, .n 23, .n 23, .n 23, .n 24, .n 25, .n 26, .n 16, .n 17, .n 18, .n 19, .n 20] [.n 27, .n 28, .n 29, .n 30, .n 31, .n 32, .n 33, .n 34, .n 35, .n 36, .n 37, .n 38, .n 39] false false),
    .atom (.copy (.n 40) (.n 27)),
    .atom (.load (.n 41) (.n 15) 6),
    .atom (.load (.n 42) (.n 15) 7),
    .atom (.load (.n 43) (.n 15) 8),
    .atom (.load (.n 44) (.n 15) 9),
    .atom (.const (.n 45) (word 2 0)),
    .atom (.mul (.n 46) (.n 4) (.n 45)),
    .atom (.mul (.n 47) (.n 46) (.n 46)),
    .atom (.mul (.n 48) (.n 47) (.n 47)),
    .atom (.mul (.n 49) (.n 48) (.n 46)),
    .atom (.mul (.n 50) (.n 49) (.n 49)),
    .atom (.mul (.n 51) (.n 50) (.n 50)),
    .atom (.mul (.n 52) (.n 51) (.n 51)),
    .atom (.mul (.n 53) (.n 2) (.n 52)),
    .atom (.mul (.n 54) (.n 1) (.n 44)),
    .atom (.mul (.n 55) (.n 40) (.n 43)),
    .atom (.add (.n 56) (.n 42) (.n 55)),
    .atom (.mul (.n 57) (.n 40) (.n 56)),
    .atom (.add (.n 58) (.n 41) (.n 57))]

/-- The head rounds. -/
def glHeadRounds (p : ℕ) : List Stmt :=
  glRounds 59 (2 * p) (.n 21) (.n 53) (.n 53) 42 (.n 58) (glCap 35)

/-- The head record's stores, at `p = 0`. -/
def glHeadStore0 : List Stmt :=
  (List.range 5).map (fun k ↦ .atom (.load (.n (35 + k)) (.n 54) (862 * k))) ++
    [.atom (.load (.n 21) (.n 54) 4310), .atom (.load (.n 58) (.n 54) 5172)]

/-- The head record's stores, at `p ≥ 1`: the cursor `8p` words on. -/
def glHeadStoreP (p : ℕ) : List Stmt :=
  (List.range 5).map (fun k ↦ .atom (.load (.n (39 + 80 * p + k)) (.n 54) (862 * k))) ++
    [.atom (.const (.n (59 + 80 * p)) (word (2 ^ (8 * p)) 0)),
      .atom (.mul (.n (60 + 80 * p)) (.n 21) (.n (59 + 80 * p))),
      .atom (.load (.n (60 + 80 * p)) (.n 54) 4310), .atom (.load (.n (58 + 80 * p)) (.n 54) 5172)]

def glHeadStore (p : ℕ) : List Stmt := if p = 0 then glHeadStore0 else glHeadStoreP p

/-- The loop's call, at `p = 0`. -/
def glLoopCall0 (nm : String) : List Stmt :=
  [.atom (.const (.n 59) (word 1 0)), .atom (.add (.n 60) (.n 59) (.n 3)),
    .atom (.const (.n 61) (word 1 0)), .atom (.const (.n 62) (word (2 ^ 42) 0)),
    .atom (.mul (.n 63) (.n 53) (.n 62)),
    .callIf (.n 60) nm [.n 61, .n 3, .n 54, .n 53, .n 63, .n 7]]

/-- The loop's call, at `p ≥ 1`. -/
def glLoopCallP (p : ℕ) (nm : String) : List Stmt :=
  [.atom (.const (.n (61 + 80 * p)) (word 1 0)),
    .atom (.add (.n (62 + 80 * p)) (.n (61 + 80 * p)) (.n 3)),
    .atom (.const (.n (63 + 80 * p)) (word 1 0)),
    .atom (.const (.n (64 + 80 * p)) (word (2 ^ (2 * p)) 0)),
    .atom (.mul (.n (65 + 80 * p)) (.n 53) (.n (64 + 80 * p))),
    .atom (.const (.n (66 + 80 * p)) (word (2 ^ (42 + 2 * p)) 0)),
    .atom (.mul (.n (67 + 80 * p)) (.n 53) (.n (66 + 80 * p))),
    .callIf (.n (62 + 80 * p)) nm
      [.n (63 + 80 * p), .n 3, .n 54, .n (65 + 80 * p), .n (67 + 80 * p), .n 7]]

def glLoopCall (p : ℕ) (nm : String) : List Stmt :=
  if p = 0 then glLoopCall0 nm else glLoopCallP p nm

/-- The last record's loads, from `head·x_m` (at `w`) into `72 + glD p ..`. -/
def glTailLoads (p w : ℕ) : List Stmt :=
  (List.range 5).map (fun k ↦ .atom (.load (.n (72 + glD p + k)) (.n w) (862 * k))) ++
    [.atom (.load (.n (77 + glD p)) (.n w) 4310), .atom (.load (.n (78 + glD p)) (.n w) 5172)]

/-- The tail's pointers, at `p = 0`. -/
def glTailSetup0 : List Stmt :=
  [.atom (.mul (.n 64) (.n 54) (.n 3)), .atom (.mul (.n 65) (.n 3) (.n 3)),
    .atom (.mul (.n 66) (.n 65) (.n 65)), .atom (.mul (.n 67) (.n 66) (.n 66)),
    .atom (.mul (.n 68) (.n 53) (.n 67)), .atom (.const (.n 69) (word (2 ^ 42) 0)),
    .atom (.mul (.n 70) (.n 53) (.n 69)), .atom (.mul (.n 71) (.n 70) (.n 67))] ++
  glTailLoads 0 64

/-- The tail's pointers, at `p ≥ 1`. -/
def glTailSetupP (p : ℕ) : List Stmt :=
  [.atom (.mul (.n (68 + 80 * p)) (.n 54) (.n 3)),
    .atom (.mul (.n (69 + 80 * p)) (.n 3) (.n 3)),
    .atom (.mul (.n (70 + 80 * p)) (.n (69 + 80 * p)) (.n (69 + 80 * p))),
    .atom (.mul (.n (71 + 80 * p)) (.n (70 + 80 * p)) (.n (70 + 80 * p))),
    .atom (.const (.n (72 + 80 * p)) (word (2 ^ (2 * p)) 0)),
    .atom (.mul (.n (73 + 80 * p)) (.n 53) (.n (72 + 80 * p))),
    .atom (.mul (.n (74 + 80 * p)) (.n (73 + 80 * p)) (.n (71 + 80 * p))),
    .atom (.const (.n (75 + 80 * p)) (word (2 ^ (42 + 2 * p)) 0)),
    .atom (.mul (.n (76 + 80 * p)) (.n 53) (.n (75 + 80 * p))),
    .atom (.mul (.n (77 + 80 * p)) (.n (76 + 80 * p)) (.n (71 + 80 * p)))] ++
  glTailLoads p (68 + 80 * p)

def glTailSetup (p : ℕ) : List Stmt := if p = 0 then glTailSetup0 else glTailSetupP p

/-- The last `2 - o` rounds, from the last record's state at `72 + glD p ..`. -/
def glTailRounds (p o : ℕ) : List Stmt :=
  glRounds (79 + glD p) (2 - o) (.n (77 + glD p)) (.n (68 + glD p)) (.n (71 + glD p)) 0
    (.n (78 + glD p)) (glCap (72 + glD p))

/-- At an odd depth, the row's zero cell. -/
def glPad (p o : ℕ) : List Stmt :=
  if o = 1 then
    [.atom (.const (.n (119 + glD p)) (word 0 0)),
      .atom (.load (.n (119 + glD p)) (.n (71 + glD p)) 1)]
  else []

/-- The canonical numbering's values at `p`, `o`: the last record's from `64` on by `glD p`,
the last round's from `119` less a round at an odd depth, the rest past the pad's zero. -/
def glRho (p o : ℕ) (v : V) : V :=
  if v.idx < 59 then v
  else if v.idx < 119 then .n (v.idx + glD p)
  else if v.idx < 159 then .n (v.idx + glD p - 40 * o)
  else .n (v.idx + glD p - 39 * o)

/-- The children, read `off` words past the tail cursor `77`: four, a permutation, four, a
permutation, four. -/
def glKids (off : ℕ) : List Stmt :=
  ((List.range 4).map (chT (.n 77) off 159)).flatten ++
    [.atom (.keccak (chRate 159 0 ++ glCap 139) (lyOuts 175) false false)] ++
    ((List.range 4).map fun i ↦ chT (.n 77) off 159 (4 + i)).flatten ++
    [.atom (.keccak (chRate 159 1 ++ lyCap 175) (lyOuts 204) false false)] ++
    ((List.range 4).map fun i ↦ chT (.n 77) off 159 (8 + i)).flatten

/-- The children's check against the last claim `158` (`gkr_product_check`). -/
def glCheck : List Stmt :=
  [.atom (.mul (.n 233) (.n 220) (.n 224)),
    .atom (.mul (.n 234) (.n 233) (.n 228)),
    .atom (.mul (.n 235) (.n 234) (.n 232)),
    .atom (.const (.n 236) (word 0 0)),
    .atom (.mul (.n 237) (.n 40) (.n 236)),
    .atom (.add (.n 238) (.n 235) (.n 237)),
    .atom (.mul (.n 239) (.n 191) (.n 195)),
    .atom (.mul (.n 240) (.n 239) (.n 199)),
    .atom (.mul (.n 241) (.n 240) (.n 203)),
    .atom (.mul (.n 242) (.n 40) (.n 238)),
    .atom (.add (.n 243) (.n 241) (.n 242)),
    .atom (.mul (.n 244) (.n 162) (.n 166)),
    .atom (.mul (.n 245) (.n 244) (.n 170)),
    .atom (.mul (.n 246) (.n 245) (.n 174)),
    .atom (.mul (.n 247) (.n 40) (.n 243)),
    .atom (.add (.n 248) (.n 246) (.n 247)),
    .atom (.assertEq (.n 158) (.n 248))]

/-- The two new coordinates (`y`'s grind of `0` bits, then a squeeze), stored at `pt[40]`,
`pt[41]`. -/
def glY : List Stmt :=
  [.atom (.keccak (chRate 159 2 ++ lyCap 204) (lyOuts 249) false false),
    .atom (.copy (.n 262) (.n 249)),
    .atom (.keccak ([.n 23, .n 23, .n 23, .n 23, .n 23, .n 24, .n 25, .n 26] ++ lyCap 249)
      (lyOuts 263) false false),
    .atom (.copy (.n 276) (.n 263)), .atom (.load (.n 262) (.n 53) 40),
    .atom (.load (.n 276) (.n 53) 41)]

/-- The next slot, `20` words on: the capacity, the cursor `cw` words on, the three values and
the position `pos·x_m·g`. -/
def glNext (cw : ℕ) : List Stmt :=
  (List.range 5).map (fun k ↦ .atom (.load (.n (271 + k)) (.n 15) (20 + k))) ++
    [.atom (.const (.n 277) (word (2 ^ cw) 0)), .atom (.mul (.n 278) (.n 77) (.n 277)),
      .atom (.load (.n 278) (.n 15) 25)] ++
    chValT 159 262 276 15 0 279 26 ++ chValT 159 262 276 15 1 288 27 ++
    chValT 159 262 276 15 2 297 28 ++
    [.atom (.mul (.n 306) (.n 44) (.n 3)), .atom (.const (.n 307) (word 2 0)),
      .atom (.mul (.n 308) (.n 306) (.n 307)), .atom (.load (.n 308) (.n 15) 29)]

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
  [.atom (.mul (.n 6) (.n 2) (.n 0)), .atom (.mul (.n 7) (.n 0) (.n 0)),
    .atom (.mul (.n 8) (.n 7) (.n 7)), .atom (.mul (.n 9) (.n 8) (.n 8)),
    .atom (.mul (.n 10) (.n 3) (.n 9)), .atom (.mul (.n 11) (.n 4) (.n 9))] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (12 + k)) (.n 6) (862 * k))) ++
  [.atom (.load (.n 17) (.n 6) 4310), .atom (.load (.n 18) (.n 6) 5172)]

/-- The iteration's eight rounds. -/
def glLoopRounds : List Stmt := glRounds 19 8 (.n 17) (.n 10) (.n 11) 0 (.n 18) (glCap 12)

/-- The next record, the guard and the next call. -/
def glLoopPost (nm : String) : List Stmt :=
  (List.range 5).map (fun k ↦ .atom (.load (.n (319 + k)) (.n 6) (1 + 862 * k))) ++
  [.atom (.const (.n 339) (word (2 ^ 32) 0)), .atom (.mul (.n 340) (.n 17) (.n 339)),
    .atom (.load (.n 340) (.n 6) 4311), .atom (.load (.n 338) (.n 6) 5173),
    .atom (.const (.n 341) (word 2 0)), .atom (.mul (.n 342) (.n 0) (.n 341)),
    .atom (.add (.n 343) (.n 342) (.n 1)), .atom (.const (.n 344) (word 2 0)),
    .atom (.mul (.n 345) (.n 0) (.n 344)),
    .callIf (.n 343) nm [.n 345, .n 1, .n 2, .n 3, .n 4, .n 5], .ret []]

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
