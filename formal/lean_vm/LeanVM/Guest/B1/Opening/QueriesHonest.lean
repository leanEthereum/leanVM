/-
  LeanVM.Guest.B1.Opening.QueriesHonest

  The honest values of one query of `opening_queries`, by index: what the completeness direction
  builds its valuation from.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesMain
public import LeanVM.Guest.AcceptableChild

/-!
# One query's honest values

`QD` is what an honest query is made of: the shape, its first value, whether it emits the padding
run, the row's `K` words, the position `q`, the siblings below the cap, the cap's and the flags'
pointers, the fold rounds and (final level) the final coefficients. Its values from `b` are the
list `vals`, piece by piece as `oqQueryT` numbers them:

* the row's cells (`cell`: `ofK` of the words at level 0, `E.ofLimbs` of two words deeper);
* at level 0 the packs `y`, `y·cell`, the leaf cell `pk` (`packVals`);
* the padding run `1, 0, 0, 0, 0` when emitted;
* the leaf hash: per block the XORed inputs and the permutation's output (`leafV`);
* the walk, inline (`WD.vals`, the query's honest walk `QD.wd`): the siblings' cells (`pc`), each
  window's word, `0x80` and the arm taken (`winV`), the cap leaf (`capV`);
* the fold (`foldVals`): round `j`'s `α, β, β·x, t`, its outputs `t·lo`, `hi + t·lo`
  (`roundVals`); the value the last lane (`foldVal`);
* at the final level (`finVals`): the point, the chain `W_i` by threes, `novel_eval`'s level `0`
  by fours (`nv0Vals`), its later levels (`nvVals`), the result `0`.

`val i` is `vals`' entry `i - b`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Lists by blocks -/

/-- The offsets of the blocks `f 0, f 1, …` laid end to end. -/
def offOf {α : Type} (f : ℕ → List α) : ℕ → ℕ
  | 0 => 0
  | j + 1 => offOf f j + (f j).length

theorem length_flatMap_range_of {α : Type} (f : ℕ → List α) :
    ∀ n, ((List.range n).flatMap f).length = offOf f n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, length_flatMap_range_of f n]
    simp [offOf]

theorem offOf_mono {α : Type} (f : ℕ → List α) {i : ℕ} : ∀ {n : ℕ}, i ≤ n → offOf f i ≤ offOf f n
  | 0, h => by rw [Nat.le_zero.mp h]
  | n + 1, h => by
    rcases Nat.lt_or_ge i (n + 1) with h' | h'
    · have := offOf_mono f (i := i) (n := n) (by omega); simp only [offOf]; omega
    · rw [show i = n + 1 by omega]

theorem getD_flatMap_range_of {α : Type} (f : ℕ → List α) (d : α) :
    ∀ (n j r : ℕ), j < n → r < (f j).length →
      ((List.range n).flatMap f).getD (offOf f j + r) d = (f j).getD r d
  | 0, _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | n + 1, j, r, hj, hr => by
    rw [List.range_succ, List.flatMap_append]
    have hl := length_flatMap_range_of f n
    rcases Nat.lt_or_ge j n with h | h
    · have h1 : offOf f (j + 1) ≤ offOf f n := offOf_mono f h
      simp only [offOf] at h1
      rw [List.getD_append _ _ _ _ (by rw [hl]; omega)]
      exact getD_flatMap_range_of f d n j r h hr
    · obtain rfl : j = n := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl, Nat.add_sub_cancel_left]
      simp

theorem offOf_const {α : Type} (f : ℕ → List α) {c : ℕ} (hf : ∀ j, (f j).length = c) :
    ∀ j, offOf f j = c * j
  | 0 => rfl
  | j + 1 => by rw [offOf, offOf_const f hf j, hf, Nat.mul_succ]

theorem length_flatMap_const {α : Type} (f : ℕ → List α) {c : ℕ} (hf : ∀ j, (f j).length = c)
    (n : ℕ) : ((List.range n).flatMap f).length = c * n := by
  rw [length_flatMap_range_of, offOf_const f hf]

theorem getD_flatMap_const {α : Type} (f : ℕ → List α) {c : ℕ} (hf : ∀ j, (f j).length = c)
    (d : α) {n j r : ℕ} (hj : j < n) (hr : r < c) :
    ((List.range n).flatMap f).getD (c * j + r) d = (f j).getD r d := by
  rw [← offOf_const f hf j]
  exact getD_flatMap_range_of f d n j r hj (by rw [hf]; exact hr)


/-! ## An honest walk -/

/-- **An honest walk** (`walk_path`, inline in a query of shape `s`, of path depth `s.pd`) below
a cap of depth `cd`: the leaf's digest it climbs from, the position, the siblings, the window
pointer, the cap's and the flags' pointers (offset by the caller to the cap's leaves). -/
structure WD where
  s : Oq
  cd : ℕ
  leaf : Digest
  q : ℕ
  sibs : List Digest
  bpv : E
  capv : E
  flagsv : E

/-- A window's values: its word, `0x80`, `2^w` arms of `3w` values and the two targets. -/
def winSz (s : Oq) (i : ℕ) : ℕ := 4 + 3 * oqWw s i * 2 ^ oqWw s i

/-- The values of the windows before window `i`. -/
def winOff (s : Oq) : ℕ → ℕ
  | 0 => 0
  | i + 1 => winOff s i + winSz s i

namespace WD

variable (w : WD)

/-- The path's depth below the cap. -/
abbrev pd : ℕ := w.s.pd

/-- Path cell `k`: level `k / 2`'s sibling's halves. -/
def pc (k : ℕ) : E := pathCell w.sibs k

/-- The node after `l` levels. -/
def node (l : ℕ) : Digest := climbNode w.leaf w.q w.sibs l

/-- The cells level `l`'s permutation reads: the node and the sibling on the sides the position's
bit names, the padding. -/
def levelIns (l : ℕ) : List E :=
  (if w.q.testBit l then [w.pc (2 * l), w.pc (2 * l + 1), (digestHalves (w.node l)).1,
      (digestHalves (w.node l)).2]
    else [(digestHalves (w.node l)).1, (digestHalves (w.node l)).2, w.pc (2 * l), w.pc (2 * l + 1)]) ++
    [word 1 0, word 0 0, word 0 0, word 0 0, word (2 ^ 63) 0, word 0 0, word 0 0, word 0 0, word 0 0]

/-- Level `l`'s step at offset `c < 3`: the `0x80` constant, the permutation's first two cells. -/
def stepV (l c : ℕ) : E :=
  if c = 0 then word (2 ^ 63) 0 else cellsOfState (permOf (w.levelIns l)) false (Fin.ofNat 13 (c - 1))

/-- Window `i`'s value: the position's bits there. -/
def wv (i : ℕ) : ℕ := qwVal (w.s.pd + w.cd) w.cd w.q i

/-- The offset of arm `a` in a window of `ww` levels. -/
def armOff (ww a : ℕ) : ℕ := if a = 0 then 2 else 4 + 3 * ww * a

/-- Window `i`'s value at offset `o`: its word `g^v`, `0x80`, the targets (the node after it), arm
`v`'s steps, `0` elsewhere (the arms not taken). -/
def winV (i o : ℕ) : E :=
  if o = 0 then gen ^ w.wv i
  else if o = 1 then word (2 ^ 63) 0
  else if o = 2 + 3 * oqWw w.s i then (digestHalves (w.node (6 * i + oqWw w.s i))).1
  else if o = 3 + 3 * oqWw w.s i then (digestHalves (w.node (6 * i + oqWw w.s i))).2
  else if armOff (oqWw w.s i) (w.wv i) ≤ o ∧ o < armOff (oqWw w.s i) (w.wv i) + 3 * oqWw w.s i then
    w.stepV (6 * i + (o - armOff (oqWw w.s i) (w.wv i)) / 3) ((o - armOff (oqWw w.s i) (w.wv i)) % 3)
  else 0

/-- The cap child bit's window `g^b`. -/
def wbV : E := gen ^ (if w.q.testBit w.s.pd then 1 else 0)

/-- The cap parent index's window `g^Q`. -/
def qV : E := gen ^ (w.q / 2 ^ (w.s.pd + 1))

/-- The cap leaf at offset `o < 9`. -/
def capV (o : ℕ) : E :=
  [w.wbV, w.qV, w.flagsv * w.qV, word 1 0, w.qV * w.qV, w.capv * (w.qV * w.qV),
    w.capv * (w.qV * w.qV) * (w.qV * w.qV), w.wbV * w.wbV,
    w.capv * (w.qV * w.qV) * (w.qV * w.qV) * (w.wbV * w.wbV)].getD o 0

/-- The siblings' cells. -/
def sibVals : List E := (List.range (2 * w.s.pd)).map w.pc

/-- Window `i`'s values. -/
def winBlock (i : ℕ) : List E := (List.range (winSz w.s i)).map (w.winV i)

/-- The windows' values. -/
def winVals : List E := (List.range (oqNpw w.s)).flatMap w.winBlock

/-- The cap leaf's values. -/
def capVals : List E := (List.range 9).map w.capV

/-- **The walk's values**, from its siblings' first cell. -/
def vals : List E := w.sibVals ++ w.winVals ++ w.capVals

/-- What the memory holds of an honest walk: its windows at `bpv`, its cap leaf and its flag. -/
structure MemOk (w : WD) (rd : Reader) : Prop where
  wins : ∀ i < qwN (w.s.pd + w.cd) w.cd, LoadHolds rd w.bpv i (gen ^ w.wv i)
  cap0 : LoadHolds rd w.capv (2 * (w.q / 2 ^ w.s.pd)) (digestHalves (climbD w.leaf w.q w.sibs)).1
  cap1 : LoadHolds rd w.capv (2 * (w.q / 2 ^ w.s.pd) + 1) (digestHalves (climbD w.leaf w.q w.sibs)).2
  flag : LoadHolds rd w.flagsv (w.q / 2 ^ (w.s.pd + 1)) 1

end WD

/-! ## An honest query -/

/-- An honest query at a level of cap depth `cd`: its shape, first value, padding run, row,
position, siblings, window pointer, cap's and flags' pointers, rounds and final coefficients. -/
structure QD where
  s : Oq
  cd : ℕ
  b : ℕ
  emit : Bool
  pr : ℕ
  row : List K
  q : ℕ
  sibs : List Digest
  bpv : E
  capv : E
  flagsv : E
  rounds : List FoldRound
  hsv : List E

namespace QD

variable (d : QD)

/-- The padding run's first value. -/
def prV : ℕ := oqPr d.s d.b d.emit d.pr
/-- The first value after the row and its packs. -/
def k1 : ℕ := oqK1 d.s d.b
/-- The first value of the leaf hash. -/
def kL : ℕ := oqKL d.s d.b d.emit
/-- The first value after the leaf hash: the walk's siblings. -/
def ch : ℕ := oqCh d.s d.b d.emit
/-- The fold's start. -/
def fo : ℕ := oqFo d.s d.b d.emit
/-- The fold's value. -/
def v : ℕ := oqVal d.s d.fo
/-- The first value after the query. -/
def e : ℕ := oqEnd d.s d.b d.emit

/-- The point: the position's word. -/
def x : E := eOfNat d.q

/-- The row's hinted cell `j`: a word of `K` at level 0, two deeper. -/
def cell (j : ℕ) : E :=
  if d.s.base = 1 then ofK (d.row.getD j 0) else E.ofLimbs (d.row.getD (2 * j) 0) (d.row.getD (2 * j + 1) 0)

/-- The leaf's cell `j`: two words of the row. -/
def pk (j : ℕ) : E := E.ofLimbs (d.row.getD (2 * j) 0) (d.row.getD (2 * j + 1) 0)

/-- The row's values. -/
def rowVals : List E := (List.range d.s.I).map d.cell

/-- A pack's values: `y`, `y·cell(2j + 1)`, the leaf cell. -/
def packV (j : ℕ) : List E := [word 0 1, word 0 1 * d.cell (2 * j + 1), d.pk j]

/-- The packs' values (level 0). -/
def packVals : List E := if d.s.base = 1 then (List.range (d.s.I / 2)).flatMap d.packV else []

/-- The padding run's values, when emitted. -/
def padVals : List E := if d.emit then [word 1 0, word 0 0, word 0 0, word 0 0, word 0 0] else []

/-! ### The leaf hash -/

/-- The padded message cell `m` of the leaf hash. -/
def P (m : ℕ) : E :=
  if m < d.s.ncells then d.pk m
  else if m = d.s.ncells then (if m = d.s.lc then oqW81 d.s else word 1 0) else oqW80 d.s

/-- The leaf hash's state before block `k`, as the cells block `k - 1` writes. -/
def leafO : ℕ → Fin 13 → E
  | 0, _ => 0
  | k + 1, c => cellsOfState (keccakF1600 (stateOfCells (fun c' ↦
      if k = 0 then (if c'.val < 9 then d.P c'.val else 0)
      else if c'.val < 9 then leafO k c' + d.P (17 * k / 2 + c'.val) else leafO k c')
      (inLayout k))) (outLayout d.s.B k) c

/-- The cells the leaf's block `k` reads. -/
def leafI (k : ℕ) (c : Fin 13) : E :=
  if k = 0 then (if c.val < 9 then d.P c.val else 0)
  else if c.val < 9 then d.leafO k c + d.P (17 * k / 2 + c.val) else d.leafO k c

/-- The leaf hash's value at offset `i`: block `0`'s outputs, then per block the XORed inputs (the
last's padding constant before its cell `8`) and the outputs. -/
def leafV (i : ℕ) : E :=
  if i < 13 then d.leafO 1 (Fin.ofNat 13 i)
  else
    let k := min ((i - 13) / 22 + 1) (d.s.B - 1)
    let r := i - (13 + (k - 1) * 22)
    if k + 1 = d.s.B then
      (if r < 8 then d.leafI k (Fin.ofNat 13 r)
        else if r = 8 then d.P d.s.lc
        else if r = 9 then d.leafI k 8
        else d.leafO (k + 1) (Fin.ofNat 13 (r - 10)))
    else
      (if r < 9 then d.leafI k (Fin.ofNat 13 r) else d.leafO (k + 1) (Fin.ofNat 13 (r - 9)))

/-- The leaf hash's values. -/
def leafVals : List E := (List.range d.s.chainLen).map d.leafV

/-- The leaf's digest. -/
def leaf : Digest := merkleLeafDigest d.row

/-- **The query's honest walk.** -/
def wd : WD := ⟨d.s, d.cd, d.leaf, d.q, d.sibs, d.bpv, d.capv, d.flagsv⟩

/-! ### The fold -/

/-- Round `j`'s challenges. -/
def rd (j : ℕ) : FoldRound := d.rounds.getD j ⟨0, 0⟩

/-- Round `j`'s combiner `t = α + β·x`. -/
def t (j : ℕ) : E := (d.rd j).alpha + (d.rd j).beta * d.x

/-- Round `0`'s lanes `(lo, hi)` for its output `m`: the cells, reversed at level 0. -/
def lane0 (m : ℕ) : E × E :=
  if d.s.base = 1 then (d.cell (d.s.I - 1 - 2 * m), d.cell (d.s.I - 2 - 2 * m))
  else (d.cell (2 * m), d.cell (2 * m + 1))

/-- Lane `m` after round `j`. -/
def acc : ℕ → ℕ → E
  | 0, m => (d.lane0 m).2 + d.t 0 * (d.lane0 m).1
  | j + 1, m => acc j (2 * m + 1) + d.t (j + 1) * acc j (2 * m)

/-- The `lo` lane round `j` reads for its output `m`. -/
def loV (j m : ℕ) : E := if j = 0 then (d.lane0 m).1 else d.acc (j - 1) (2 * m)

/-- Round `j`'s values. -/
def roundVals (j : ℕ) : List E :=
  [(d.rd j).alpha, (d.rd j).beta, (d.rd j).beta * d.x, d.t j] ++
  (List.range (2 ^ (d.s.folds - 1 - j))).flatMap fun m ↦ [d.t j * d.loV j m, d.acc j m]

/-- The fold's value: the last lane. -/
def foldVal : E := d.acc (d.s.folds - 1) 0

/-- The fold's values. -/
def foldVals : List E := (List.range d.s.folds).flatMap d.roundVals

/-! ### The final check -/

/-- The chain `W_i` at the point. -/
def W (i : ℕ) : E := wsChain (d.s.vs.map K.ofBits) d.x i

/-- The chain's values: per step the constant, `W_i + vs_i`, `W_(i+1)`. -/
def chainVals : List E :=
  (List.range d.s.mu).flatMap fun i ↦
    [word (d.s.vs.getD i 0) 0, d.W i + word (d.s.vs.getD i 0) 0, d.W (i + 1)]

/-- `novel_eval`'s level `0`: per pair the two coefficients, `W_0·hi`, the sum. -/
def nv0Vals : List E :=
  (List.range (d.s.nHs / 2)).flatMap fun m ↦
    [d.hsv.getD (2 * m) 0, d.hsv.getD (2 * m + 1) 0, d.W 0 * d.hsv.getD (2 * m + 1) 0,
      d.hsv.getD (2 * m) 0 + d.W 0 * d.hsv.getD (2 * m + 1) 0]

/-- A later level's values on the inputs `l`: per pair `w·hi`, `lo + w·hi`; an odd last copied. -/
def nvLevelVals (w : E) : List E → List E
  | lo :: hi :: rest => [w * hi, lo + w * hi] ++ nvLevelVals w rest
  | [lo] => [lo]
  | [] => []

/-- Levels `i .. i + c` of `novel_eval`'s values on the inputs `l`. -/
def nvVals (W : ℕ → E) : ℕ → ℕ → List E → List E
  | 0, _, _ => []
  | c + 1, i, l => nvLevelVals (W i) l ++ nvVals W c (i + 1) (nvPair (W i) l)

/-- The final check's values after the fold's: the point, the chain, `novel_eval`'s levels. -/
def finVals : List E :=
  if d.s.final = 1 then
    [d.x] ++ d.chainVals ++ d.nv0Vals ++
      nvVals d.W (d.s.hsBits - 1) 1 (nvPair (d.W 0) (d.hsv.take d.s.nHs))
  else []

/-! ### The query -/

/-- **The query's values from `b`.** -/
def vals : List E :=
  d.rowVals ++ d.packVals ++ d.padVals ++ d.leafVals ++ d.wd.vals ++ d.foldVals ++ d.finVals

/-- **The honest value of index `i` of the query.** -/
def val (i : ℕ) : E := if d.b ≤ i then d.vals.getD (i - d.b) 0 else 0

/-- The honest valuation on a query's values. -/
abbrev Hv (σ : Val) : Prop := ∀ i, d.b ≤ i → i < d.e → σ (.n i) = d.val i

end QD

/-! ## The walk's places -/

theorem oqWk_eq (s : Oq) (ch : ℕ) : ∀ i, oqWk s ch i = ch + 2 * s.pd + winOff s i
  | 0 => rfl
  | i + 1 => by rw [oqWk, oqWk_eq s ch i, winOff, winSz]; omega

theorem winOff_mono (s : Oq) {i : ℕ} : ∀ {j : ℕ}, i ≤ j → winOff s i ≤ winOff s j
  | 0, h => by rw [Nat.le_zero.mp h]
  | j + 1, h => by
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · have := winOff_mono s (i := i) (j := j) (by omega); simp only [winOff]; omega
    · rw [show i = j + 1 by omega]

theorem winOff_succ_le {s : Oq} {i : ℕ} (hi : i < oqNpw s) : winOff s i + winSz s i ≤ winOff s (oqNpw s) :=
  winOff_mono s (i := i + 1) hi

namespace WD

variable (w : WD)

theorem winBlock_length (i : ℕ) : (w.winBlock i).length = winSz w.s i := by simp [winBlock]

theorem offOf_winBlock : ∀ i, offOf w.winBlock i = winOff w.s i
  | 0 => rfl
  | i + 1 => by rw [offOf, offOf_winBlock i, winBlock_length, winOff]

theorem winVals_length : w.winVals.length = winOff w.s (oqNpw w.s) := by
  rw [winVals, length_flatMap_range_of, offOf_winBlock]

theorem vals_length : w.vals.length = 2 * w.s.pd + winOff w.s (oqNpw w.s) + 9 := by
  simp only [vals, List.length_append, sibVals, capVals, List.length_map, List.length_range,
    winVals_length]

theorem vals_sib {o : ℕ} (ho : o < 2 * w.s.pd) : w.vals.getD o 0 = w.pc o := by
  rw [vals, List.append_assoc, List.getD_append _ _ _ _ (by simpa [sibVals] using ho)]
  simp [sibVals, List.getD_eq_getElem?_getD, ho]

theorem vals_win {i o : ℕ} (hi : i < oqNpw w.s) (ho : o < winSz w.s i) :
    w.vals.getD (2 * w.s.pd + (winOff w.s i + o)) 0 = w.winV i o := by
  have h1 := winOff_succ_le (s := w.s) hi
  have hw := w.winVals_length
  have hs : w.sibVals.length = 2 * w.s.pd := by simp [sibVals]
  rw [vals, List.append_assoc, List.getD_append_right _ _ _ _ (by omega), hs, Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ (by omega), winVals, ← offOf_winBlock,
    getD_flatMap_range_of _ 0 _ _ _ hi (by rw [winBlock_length]; exact ho)]
  simp [winBlock, List.getD_eq_getElem?_getD, ho]

theorem vals_cap {o : ℕ} (ho : o < 9) :
    w.vals.getD (2 * w.s.pd + (winOff w.s (oqNpw w.s) + o)) 0 = w.capV o := by
  have hw := w.winVals_length
  have hs : w.sibVals.length = 2 * w.s.pd := by simp [sibVals]
  rw [vals, List.getD_append_right _ _ _ _ (by simp only [List.length_append]; omega),
    List.length_append, hs, hw, show 2 * w.s.pd + (winOff w.s (oqNpw w.s) + o) -
      (2 * w.s.pd + winOff w.s (oqNpw w.s)) = o by omega]
  simp [capVals, List.getD_eq_getElem?_getD, ho]

end WD

namespace QD

variable (d : QD)

/-! ## The pieces' places -/

theorem wd_pd : d.wd.s.pd = d.s.pd := rfl

theorem wd_npw : oqNpw d.wd.s = oqNpw d.s := rfl

theorem wd_winOff (i : ℕ) : winOff d.wd.s i = winOff d.s i := rfl


theorem vals_eq : d.vals =
    d.rowVals ++ (d.packVals ++ (d.padVals ++ (d.leafVals ++ (d.wd.vals ++ (d.foldVals ++ d.finVals))))) := by
  simp only [vals, List.append_assoc]

theorem rowVals_length : d.rowVals.length = d.s.I := by simp [rowVals]

theorem packVals_length : d.packVals.length = if d.s.base = 1 then 3 * (d.s.I / 2) else 0 := by
  unfold packVals
  split
  · rw [length_flatMap_const _ (c := 3) (fun _ ↦ rfl)]
  · rfl

theorem padVals_length : d.padVals.length = if d.emit then 5 else 0 := by
  unfold padVals; split <;> rfl

theorem leafVals_length : d.leafVals.length = d.s.chainLen := by simp [leafVals]

theorem roundVals_length (j : ℕ) :
    (d.roundVals j).length = 4 + 2 * 2 ^ (d.s.folds - 1 - j) := by
  unfold roundVals
  rw [List.length_append, length_flatMap_const _ (c := 2) (fun _ ↦ rfl)]
  simp

theorem oqRK_eq (F : ℕ) : ∀ j, oqRK d.s F j = F + offOf d.roundVals j
  | 0 => rfl
  | j + 1 => by
    rw [oqRK, oqRK_eq F j, offOf, roundVals_length]
    omega

theorem foldVals_length : d.foldVals.length = offOf d.roundVals d.s.folds := by
  simp only [foldVals, length_flatMap_range_of]

/-- The last round takes six values. -/
theorem offOf_last (hf : 1 ≤ d.s.folds) :
    offOf d.roundVals d.s.folds = offOf d.roundVals (d.s.folds - 1) + 6 := by
  conv_lhs => rw [show d.s.folds = d.s.folds - 1 + 1 by omega]
  rw [offOf, roundVals_length]
  simp

theorem k1_eq : d.k1 = d.b + d.rowVals.length + d.packVals.length := by
  rw [rowVals_length, packVals_length]; rfl

theorem kL_eq : d.kL = d.k1 + d.padVals.length := by
  rw [padVals_length]; rfl

theorem ch_eq : d.ch = d.kL + d.leafVals.length := by
  rw [leafVals_length]; rfl

theorem v_eq (hf : 1 ≤ d.s.folds) : d.v + 1 = d.fo + offOf d.roundVals d.s.folds := by
  rw [d.offOf_last hf]
  simp only [v, oqVal, oqAcc, oqRO, oqRK_eq]
  omega

theorem fo_eq : d.fo = d.ch + d.wd.vals.length := by
  rw [d.wd.vals_length, wd_winOff, wd_npw, wd_pd]
  show oqCq d.s d.ch + 9 = _
  rw [oqCq, oqWk_eq]
  omega

theorem val_add (o : ℕ) : d.val (d.b + o) = d.vals.getD o 0 := by
  simp [val]

/-- The walk's start, from `b`. -/
theorem ch_off : d.ch = d.b + (d.rowVals.length + (d.packVals.length + (d.padVals.length +
    d.leafVals.length))) := by
  rw [ch_eq, kL_eq, k1_eq]; omega

theorem val_row {j : ℕ} (hj : j < d.s.I) : d.val (d.b + j) = d.cell j := by
  rw [val_add, vals_eq, List.getD_append _ _ _ _ (by rw [rowVals_length]; exact hj)]
  simp [rowVals, List.getD_eq_getElem?_getD, hj]

theorem val_pack (hb : d.s.base = 1) {j t : ℕ} (hj : j < d.s.I / 2) (ht : t < 3) :
    d.val (d.b + d.s.I + 3 * j + t) = (d.packV j).getD t 0 := by
  have hl : d.packVals.length = 3 * (d.s.I / 2) := by rw [packVals_length]; simp [hb]
  rw [show d.b + d.s.I + 3 * j + t = d.b + (d.rowVals.length + (3 * j + t)) by
      rw [rowVals_length]; omega, val_add, vals_eq,
    List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ (by rw [hl]; omega)]
  unfold packVals
  simp only [hb, ↓reduceIte]
  exact getD_flatMap_const _ (c := 3) (fun _ ↦ rfl) 0 hj ht

theorem val_pad (he : d.emit = true) {i : ℕ} (hi : i < 5) :
    d.val (d.k1 + i) = [word 1 0, word 0 0, word 0 0, word 0 0, word 0 0].getD i 0 := by
  have hl : d.padVals.length = 5 := by rw [padVals_length, he]; rfl
  rw [k1_eq, show d.b + d.rowVals.length + d.packVals.length + i =
      d.b + (d.rowVals.length + (d.packVals.length + i)) by omega, val_add, vals_eq,
    List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ (by omega)]
  simp [padVals, he]

theorem val_leaf {i : ℕ} (hi : i < d.s.chainLen) : d.val (d.kL + i) = d.leafV i := by
  have hl := d.leafVals_length
  rw [kL_eq, k1_eq, show d.b + d.rowVals.length + d.packVals.length + d.padVals.length + i =
      d.b + (d.rowVals.length + (d.packVals.length + (d.padVals.length + i))) by omega, val_add,
    vals_eq]
  repeat rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
  rw [List.getD_append _ _ _ _ (by omega)]
  simp [leafVals, List.getD_eq_getElem?_getD, hi]

/-- The walk's values, from its start. -/
theorem val_walk {o : ℕ} (ho : o < d.wd.vals.length) : d.val (d.ch + o) = d.wd.vals.getD o 0 := by
  rw [ch_off, show d.b + (d.rowVals.length + (d.packVals.length + (d.padVals.length +
      d.leafVals.length))) + o = d.b + (d.rowVals.length + (d.packVals.length + (d.padVals.length +
      (d.leafVals.length + o)))) by omega, val_add, vals_eq]
  repeat rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
  rw [List.getD_append _ _ _ _ ho]

/-- The walk's sibling cells. -/
theorem val_sib {o : ℕ} (ho : o < 2 * d.s.pd) : d.val (d.ch + o) = d.wd.pc o := by
  have hl := d.wd.vals_length
  rw [val_walk _ (by rw [hl]; exact lt_of_lt_of_le ho (by rw [wd_pd]; omega))]
  exact d.wd.vals_sib ho

/-- Window `i`'s values. -/
theorem val_win {i o : ℕ} (hi : i < oqNpw d.s) (ho : o < winSz d.s i) :
    d.val (oqWk d.s d.ch i + o) = d.wd.winV i o := by
  have h1 := winOff_succ_le (s := d.s) hi
  have hl := d.wd.vals_length
  rw [wd_winOff, wd_npw, wd_pd] at hl
  rw [oqWk_eq, Nat.add_assoc, Nat.add_assoc, val_walk _ (by omega), ← wd_winOff, ← wd_pd]
  exact d.wd.vals_win hi ho

/-- The cap leaf's values. -/
theorem val_cap {o : ℕ} (ho : o < 9) : d.val (oqCq d.s d.ch + o) = d.wd.capV o := by
  have hl := d.wd.vals_length
  rw [wd_winOff, wd_npw, wd_pd] at hl
  rw [oqCq, oqWk_eq, Nat.add_assoc, Nat.add_assoc, val_walk _ (by omega), ← wd_npw, ← wd_winOff,
    ← wd_pd]
  exact d.wd.vals_cap ho

/-- The fold's values, from its start. -/
theorem val_foldVals {o : ℕ} (ho : o < d.foldVals.length) :
    d.val (d.fo + o) = d.foldVals.getD o 0 := by
  rw [fo_eq, ch_off, show d.b + (d.rowVals.length + (d.packVals.length + (d.padVals.length +
      d.leafVals.length))) + d.wd.vals.length + o = d.b + (d.rowVals.length + (d.packVals.length +
      (d.padVals.length + (d.leafVals.length + (d.wd.vals.length + o))))) by omega, val_add, vals_eq]
  repeat rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
  rw [List.getD_append _ _ _ _ ho]

theorem val_round {j o : ℕ} (hj : j < d.s.folds) (ho : o < (d.roundVals j).length) :
    d.val (oqRK d.s d.fo j + o) = (d.roundVals j).getD o 0 := by
  have h1 : offOf d.roundVals (j + 1) ≤ offOf d.roundVals d.s.folds := offOf_mono _ hj
  simp only [offOf] at h1
  rw [oqRK_eq, Nat.add_assoc, val_foldVals _ (by rw [foldVals_length]; omega), foldVals]
  exact getD_flatMap_range_of _ 0 _ _ _ hj ho

theorem val_v (hf1 : 1 ≤ d.s.folds) : d.val d.v = d.foldVal := by
  have e : d.v = oqRK d.s d.fo (d.s.folds - 1) + 5 := by simp only [v, oqVal, oqAcc, oqRO]
  rw [e, val_round d (by omega) (by rw [roundVals_length, Nat.sub_self, pow_zero]; omega)]
  simp [roundVals, foldVal]

theorem val_fin (hf1 : 1 ≤ d.s.folds) (o : ℕ) : d.val (d.v + 1 + o) = d.finVals.getD o 0 := by
  have hf := d.foldVals_length
  have hv := d.v_eq hf1
  have e : d.v + 1 + o = d.b + (d.rowVals.length + (d.packVals.length + (d.padVals.length +
      (d.leafVals.length + (d.wd.vals.length + (d.foldVals.length + o)))))) := by
    rw [hv, fo_eq, ch_off]; omega
  rw [e, val_add, vals_eq]
  repeat rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

/-! ## The final check's places -/

theorem length_nvLevelVals (w : E) : ∀ l : List E, (nvLevelVals w l).length = l.length
  | _ :: _ :: rest => by simp [nvLevelVals, length_nvLevelVals w rest]
  | [_] => rfl
  | [] => rfl

theorem length_nvLevelT_out {w : V} : ∀ (ins : List ℕ) (k : ℕ),
    (nvLevelT w ins k).2.1.length = (ins.length + 1) / 2 ∧ (nvLevelT w ins k).2.2 = k + ins.length
  | _ :: _ :: rest, k => by
    have := length_nvLevelT_out (w := w) rest (k + 2)
    simp only [nvLevelT, List.length_cons]
    omega
  | [_], _ => by simp [nvLevelT]
  | [], _ => by simp [nvLevelT]

theorem length_nvPair' (w : E) : ∀ l : List E, (nvPair w l).length = (l.length + 1) / 2
  | _ :: _ :: rest => by
    simp only [nvPair, List.length_cons, length_nvPair' w rest]
    omega
  | [_] => by simp [nvPair]
  | [] => by simp [nvPair]

theorem nvLevelsT_next {ws : ℕ → ℕ} (W : ℕ → E) : ∀ (c i : ℕ) (ins : List ℕ) (L : List E) (k : ℕ),
    ins.length = L.length → (nvLevelsT ws c i ins k).2.2 = k + (nvVals W c i L).length
  | 0, _, _, _, _, _ => by simp [nvLevelsT, nvVals]
  | c + 1, i, ins, L, k, h => by
    simp only [nvLevelsT, nvVals, List.length_append, length_nvLevelVals]
    have := length_nvLevelT_out (w := .n (ws i)) ins k
    rw [nvLevelsT_next W c (i + 1) _ (nvPair (W i) L) _ (by rw [this.1, length_nvPair', h]), this.2, h]
    omega

theorem chainVals_length : d.chainVals.length = 3 * d.s.mu := by
  rw [chainVals, length_flatMap_const _ (c := 3) (fun _ ↦ rfl)]

theorem nv0Vals_length : d.nv0Vals.length = 4 * (d.s.nHs / 2) := by
  rw [nv0Vals, length_flatMap_const _ (c := 4) (fun _ ↦ rfl)]

/-- The final check's novel sum's next free value (its result's index). -/
theorem oqNovel_next (hn : d.s.nHs % 2 = 0) (hlen : d.s.nHs ≤ d.hsv.length) :
    (oqNovel d.s (.n 0) d.v).2.2 = d.v + 2 + 3 * d.s.mu + 4 * (d.s.nHs / 2) +
      (nvVals d.W (d.s.hsBits - 1) 1 (nvPair (d.W 0) (d.hsv.take d.s.nHs))).length := by
  simp only [oqNovel]
  rw [nvLevelsT_next d.W _ _ _ (nvPair (d.W 0) (d.hsv.take d.s.nHs)) _
    (by rw [length_nvPair']; simp; omega)]

theorem e_eq (hf1 : 1 ≤ d.s.folds)
    (hn : d.s.final = 1 → d.s.nHs % 2 = 0 ∧ d.s.nHs ≤ d.hsv.length) :
    d.e = d.b + d.vals.length := by
  have hv := d.v_eq hf1
  have hc := d.ch_off
  have ho := d.fo_eq
  have hf := d.foldVals_length
  rw [e, oqEnd, oqRes]
  change (if d.s.final = 1 then (if d.s.final = 1 then (oqNovel d.s (.n 0) d.v).2.2 else d.v) else
    (if d.s.final = 1 then (oqNovel d.s (.n 0) d.v).2.2 else d.v) + 1) = _
  by_cases h1 : d.s.final = 1
  · simp only [h1, ↓reduceIte]
    rw [d.oqNovel_next (hn h1).1 (hn h1).2]
    simp only [vals, finVals, h1, ↓reduceIte, List.length_append, chainVals_length, nv0Vals_length,
      List.length_cons, List.length_nil]
    omega
  · simp only [h1, ↓reduceIte, vals, finVals, List.length_append, List.length_nil]
    omega

end QD

end
end LeanVM.Guest.B1
