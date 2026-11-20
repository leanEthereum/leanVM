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
    .atom (.load (.n 40) (.n 15) 6),
    .atom (.load (.n 41) (.n 15) 7),
    .atom (.load (.n 42) (.n 15) 8),
    .atom (.load (.n 43) (.n 15) 9),
    .atom (.const (.n 44) (word 2 0)),
    .atom (.mul (.n 45) (.n 4) (.n 44)),
    .atom (.mul (.n 46) (.n 45) (.n 45)),
    .atom (.mul (.n 47) (.n 46) (.n 46)),
    .atom (.mul (.n 48) (.n 47) (.n 45)),
    .atom (.mul (.n 49) (.n 48) (.n 48)),
    .atom (.mul (.n 50) (.n 49) (.n 49)),
    .atom (.mul (.n 51) (.n 50) (.n 50)),
    .atom (.mul (.n 52) (.n 2) (.n 51)),
    .atom (.mul (.n 53) (.n 1) (.n 43)),
    .atom (.mul (.n 54) (.n 27) (.n 42)),
    .atom (.add (.n 55) (.n 41) (.n 54)),
    .atom (.mul (.n 56) (.n 27) (.n 55)),
    .atom (.add (.n 57) (.n 40) (.n 56))]

/-- The head rounds. -/
def glHeadRounds (p : ℕ) : List Stmt :=
  glRounds 58 (2 * p) (.n 21) (.n 52) (.n 52) 42 (.n 57) (glCap 35)

/-- The head record's stores, at `p = 0`. -/
def glHeadStore0 : List Stmt :=
  (List.range 5).map (fun k ↦ .atom (.load (.n (35 + k)) (.n 53) (862 * k))) ++
    [.atom (.load (.n 21) (.n 53) 4310), .atom (.load (.n 57) (.n 53) 5172)]

/-- The head record's stores, at `p ≥ 1`: the cursor `8p` words on. -/
def glHeadStoreP (p : ℕ) : List Stmt :=
  (List.range 5).map (fun k ↦ .atom (.load (.n (39 + 78 * p + k)) (.n 53) (862 * k))) ++
    [.atom (.const (.n (58 + 78 * p)) (word (2 ^ (8 * p)) 0)),
      .atom (.mul (.n (59 + 78 * p)) (.n 21) (.n (58 + 78 * p))),
      .atom (.load (.n (59 + 78 * p)) (.n 53) 4310), .atom (.load (.n (57 + 78 * p)) (.n 53) 5172)]

def glHeadStore (p : ℕ) : List Stmt := if p = 0 then glHeadStore0 else glHeadStoreP p

/-- The loop's call, at `p = 0`. -/
def glLoopCall0 (nm : String) : List Stmt :=
  [.atom (.const (.n 58) (word 1 0)), .atom (.add (.n 59) (.n 58) (.n 3)),
    .atom (.const (.n 60) (word 1 0)), .atom (.const (.n 61) (word (2 ^ 42) 0)),
    .atom (.mul (.n 62) (.n 52) (.n 61)),
    .callIf (.n 59) nm [.n 60, .n 3, .n 53, .n 52, .n 62, .n 7]]

/-- The loop's call, at `p ≥ 1`. -/
def glLoopCallP (p : ℕ) (nm : String) : List Stmt :=
  [.atom (.const (.n (60 + 78 * p)) (word 1 0)),
    .atom (.add (.n (61 + 78 * p)) (.n (60 + 78 * p)) (.n 3)),
    .atom (.const (.n (62 + 78 * p)) (word 1 0)),
    .atom (.const (.n (63 + 78 * p)) (word (2 ^ (2 * p)) 0)),
    .atom (.mul (.n (64 + 78 * p)) (.n 52) (.n (63 + 78 * p))),
    .atom (.const (.n (65 + 78 * p)) (word (2 ^ (42 + 2 * p)) 0)),
    .atom (.mul (.n (66 + 78 * p)) (.n 52) (.n (65 + 78 * p))),
    .callIf (.n (61 + 78 * p)) nm
      [.n (62 + 78 * p), .n 3, .n 53, .n (64 + 78 * p), .n (66 + 78 * p), .n 7]]

def glLoopCall (p : ℕ) (nm : String) : List Stmt :=
  if p = 0 then glLoopCall0 nm else glLoopCallP p nm

/-- The last record's loads, from `head·x_m` (at `w`) into `71 + glD p ..`. -/
def glTailLoads (p w : ℕ) : List Stmt :=
  (List.range 5).map (fun k ↦ .atom (.load (.n (71 + glD p + k)) (.n w) (862 * k))) ++
    [.atom (.load (.n (76 + glD p)) (.n w) 4310), .atom (.load (.n (77 + glD p)) (.n w) 5172)]

/-- The tail's pointers, at `p = 0`. -/
def glTailSetup0 : List Stmt :=
  [.atom (.mul (.n 63) (.n 53) (.n 3)), .atom (.mul (.n 64) (.n 3) (.n 3)),
    .atom (.mul (.n 65) (.n 64) (.n 64)), .atom (.mul (.n 66) (.n 65) (.n 65)),
    .atom (.mul (.n 67) (.n 52) (.n 66)), .atom (.const (.n 68) (word (2 ^ 42) 0)),
    .atom (.mul (.n 69) (.n 52) (.n 68)), .atom (.mul (.n 70) (.n 69) (.n 66))] ++
  glTailLoads 0 63

/-- The tail's pointers, at `p ≥ 1`. -/
def glTailSetupP (p : ℕ) : List Stmt :=
  [.atom (.mul (.n (67 + 78 * p)) (.n 53) (.n 3)),
    .atom (.mul (.n (68 + 78 * p)) (.n 3) (.n 3)),
    .atom (.mul (.n (69 + 78 * p)) (.n (68 + 78 * p)) (.n (68 + 78 * p))),
    .atom (.mul (.n (70 + 78 * p)) (.n (69 + 78 * p)) (.n (69 + 78 * p))),
    .atom (.const (.n (71 + 78 * p)) (word (2 ^ (2 * p)) 0)),
    .atom (.mul (.n (72 + 78 * p)) (.n 52) (.n (71 + 78 * p))),
    .atom (.mul (.n (73 + 78 * p)) (.n (72 + 78 * p)) (.n (70 + 78 * p))),
    .atom (.const (.n (74 + 78 * p)) (word (2 ^ (42 + 2 * p)) 0)),
    .atom (.mul (.n (75 + 78 * p)) (.n 52) (.n (74 + 78 * p))),
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
  ((List.range 4).map (chT (.n 76) off 156)).flatten ++
    [.atom (.keccak (chRate 156 0 ++ glCap 137) (lyOuts 172) false false)] ++
    ((List.range 4).map fun i ↦ chT (.n 76) off 156 (4 + i)).flatten ++
    [.atom (.keccak (chRate 156 1 ++ lyCap 172) (lyOuts 201) false false)] ++
    ((List.range 4).map fun i ↦ chT (.n 76) off 156 (8 + i)).flatten

/-- The children's check against the last claim `158` (`gkr_product_check`). -/
def glCheck : List Stmt :=
  [.atom (.mul (.n 230) (.n 217) (.n 221)),
    .atom (.mul (.n 231) (.n 230) (.n 225)),
    .atom (.mul (.n 232) (.n 231) (.n 229)),
    .atom (.const (.n 233) (word 0 0)),
    .atom (.mul (.n 234) (.n 27) (.n 233)),
    .atom (.add (.n 235) (.n 232) (.n 234)),
    .atom (.mul (.n 236) (.n 188) (.n 192)),
    .atom (.mul (.n 237) (.n 236) (.n 196)),
    .atom (.mul (.n 238) (.n 237) (.n 200)),
    .atom (.mul (.n 239) (.n 27) (.n 235)),
    .atom (.add (.n 240) (.n 238) (.n 239)),
    .atom (.mul (.n 241) (.n 159) (.n 163)),
    .atom (.mul (.n 242) (.n 241) (.n 167)),
    .atom (.mul (.n 243) (.n 242) (.n 171)),
    .atom (.mul (.n 244) (.n 27) (.n 240)),
    .atom (.add (.n 245) (.n 243) (.n 244)),
    .atom (.assertEq (.n 155) (.n 245))]

/-- The two new coordinates (`y`'s grind of `0` bits, then a squeeze), stored at `pt[40]`,
`pt[41]`. -/
def glY : List Stmt :=
  [.atom (.keccak (chRate 156 2 ++ lyCap 201) (lyOuts 246) false false),
    .atom (.keccak ([.n 23, .n 23, .n 23, .n 23, .n 23, .n 24, .n 25, .n 26] ++ lyCap 246)
      (lyOuts 259) false false),
    .atom (.load (.n 246) (.n 52) 40),
    .atom (.load (.n 259) (.n 52) 41)]

/-- The next slot, `20` words on: the capacity, the cursor `cw` words on, the three values and
the position `pos·x_m·g`. -/
def glNext (cw : ℕ) : List Stmt :=
  (List.range 5).map (fun k ↦ .atom (.load (.n (267 + k)) (.n 15) (20 + k))) ++
    [.atom (.const (.n 272) (word (2 ^ cw) 0)), .atom (.mul (.n 273) (.n 76) (.n 272)),
      .atom (.load (.n 273) (.n 15) 25)] ++
    chValT 156 246 259 15 0 274 26 ++ chValT 156 246 259 15 1 283 27 ++
    chValT 156 246 259 15 2 292 28 ++
    [.atom (.mul (.n 301) (.n 43) (.n 3)), .atom (.const (.n 302) (word 2 0)),
      .atom (.mul (.n 303) (.n 301) (.n 302)), .atom (.load (.n 303) (.n 15) 29)]

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
  (List.range 5).map (fun k ↦ .atom (.load (.n (312 + k)) (.n 6) (1 + 862 * k))) ++
  [.atom (.const (.n 331) (word (2 ^ 32) 0)), .atom (.mul (.n 332) (.n 17) (.n 331)),
    .atom (.load (.n 332) (.n 6) 4311), .atom (.load (.n 330) (.n 6) 5173),
    .atom (.const (.n 333) (word 2 0)), .atom (.mul (.n 334) (.n 0) (.n 333)),
    .atom (.add (.n 335) (.n 334) (.n 1)), .atom (.const (.n 336) (word 2 0)),
    .atom (.mul (.n 337) (.n 0) (.n 336)),
    .callIf (.n 335) nm [.n 337, .n 1, .n 2, .n 3, .n 4, .n 5], .ret []]

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
