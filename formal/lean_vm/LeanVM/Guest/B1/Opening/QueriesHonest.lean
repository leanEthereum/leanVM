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
run, the row's words, the weights, the position `q`, the siblings below the cap, the cap's and the
flags' pointers.
`qVal d i` is the value of index `i` of the query's expansion (`oqQueryT`), piece by piece:

* the row's words `ofK`, the packs `y`, `y·r`, `r + y·r` (`qPackV`);
* the dot product: per term the assembled word (deeper), the weight, the product, the running sum
  (`qPartV`), per group the weight, the product, the running dot product (`qDotAfterV`);
* the padding run `1, 0, 0, 0, 0`;
* the leaf hash: per block the XORed inputs and the permutation's output (`qLeafO`, `qLeafI`);
  then the query calls `walk_path` (lean_ethereum.py:1308-1343 at 40f877dc), whose frame is `WD`'s.

`WD` is an honest `walk_path` frame: the shape, the leaf's digest, the position, the siblings, the
window pointer, the cap's and the flags' pointers. `WD.val i` is the value of index `i` of its body
(`wpBodyT`): the parameters (the leaf's halves, the pointers); the children `pathCell` (the node on
the walk's side, the sibling off it); per window its word `g^v`, (window `0`) the padding run
`1, 0, 0, 0, 0`, `0x80`, arm `v`'s steps (`0x80` and the pair's permutation, `levelIns`), the node
after it at the match's targets, `0` in the arms not taken (`winV`); the cap leaf: the last two
windows `g^b`, `g^Q`, the flag's address, the cap leaf's (`capV`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- An honest query (its walk's siblings, cap and flags kept for its `walk_path` frame, `QD.wd`). -/
structure QD where
  s : Oq
  b : ℕ
  emit : Bool
  pr : ℕ
  row : List K
  w : ℕ → E
  q : ℕ
  sibs : List Digest
  capv : E
  flagsv : E

namespace QD

variable (d : QD)

/-- The padding run's first value. -/
def prV : ℕ := oqPr d.s d.b d.emit d.pr
/-- The first value of the dot product. -/
def k1 : ℕ := oqK1 d.b d.s.R
/-- The first value of the leaf hash. -/
def kL : ℕ := oqKL d.s d.b d.emit
/-- The first value after the leaf hash: the call of `walk_path`. -/
def ch : ℕ := oqCh d.s d.b d.emit
/-- The first value after the query. -/
def e : ℕ := d.ch

/-- Row word `j`. -/
def rw (j : ℕ) : E := ofK (d.row.getD j 0)

/-- The packed cell `j`. -/
def pk (j : ℕ) : E := d.rw (2 * j) + word 0 1 0 * d.rw (2 * j + 1)

/-- The row's `E` word `jw`. -/
def W (jw : ℕ) : E := rowWord d.s.base d.row jw

/-- The running sum of group `h` after its term `l`. -/
def partV (h l : ℕ) : E :=
  ((List.range (l + 1)).map fun l' ↦ d.W (d.s.lo * h + l') * d.w l').foldl (· + ·) 0

/-- The dot product after group `h`. -/
def dotAfterV (h : ℕ) : E :=
  ((List.range (h + 1)).map fun h' ↦ d.w (d.s.lo + h') * d.partV h' (d.s.lo - 1)).foldl (· + ·) 0

/-- A deeper level's word statements' values, offset `o < 3`. -/
def wordStmtV (jw o : ℕ) : E :=
  if jw % 2 = 0 then
    [word 0 0 1, word 0 0 1 * d.rw (3 * jw + 2), d.W jw].getD o 0
  else
    [word 0 1 0, word 0 1 0 * d.pk ((3 * jw + 1) / 2), d.W jw].getD o 0

/-- Term `l` of group `h`, offset `o`. -/
def termV (h l o : ℕ) : E :=
  if o < d.s.tsz then d.wordStmtV (d.s.lo * h + l) o
  else if o = d.s.tsz then d.w l
  else if o = d.s.tsz + 1 then d.W (d.s.lo * h + l) * d.w l
  else d.partV h l

/-- The group of the dot product's offset `i`. -/
def dotH (G i : ℕ) : ℕ := if i < G then 0 else (i - G) / (G + 1) + 1

/-- The offset within its group. -/
def dotR (G i : ℕ) : ℕ := if dotH G i = 0 then i else i + 1 - dotH G i * (G + 1)

/-- The term of a group's offset `r`. -/
def termL (t r : ℕ) : ℕ := if r < 2 + t then 0 else (r - (2 + t)) / (3 + t) + 1

/-- The offset within its term. -/
def termO (t r : ℕ) : ℕ := if r < 2 + t then r else (r - (2 + t)) % (3 + t)

/-- The dot product's value at offset `i`. -/
def dotV (i : ℕ) : E :=
  if dotR d.s.G i < d.s.G - 2 then
    d.termV (dotH d.s.G i) (termL d.s.tsz (dotR d.s.G i)) (termO d.s.tsz (dotR d.s.G i))
  else if dotR d.s.G i = d.s.G - 2 then d.w (d.s.lo + dotH d.s.G i)
  else if dotR d.s.G i = d.s.G - 1 then
    d.w (d.s.lo + dotH d.s.G i) * d.partV (dotH d.s.G i) (d.s.lo - 1)
  else d.dotAfterV (dotH d.s.G i)

/-- The padded message cell `m` of the leaf hash. -/
def P (m : ℕ) : E := if m < d.s.ncells then d.pk m else if m = d.s.ncells then word 1 0 0 else oqW80 d.s

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
last's `0x80` constant before its cell `8`) and the outputs. -/
def leafV (i : ℕ) : E :=
  if i < 13 then d.leafO 1 (Fin.ofNat 13 i)
  else
    let k := min ((i - 13) / 22 + 1) (d.s.B - 1)
    let r := i - (13 + (k - 1) * 22)
    if k + 1 = d.s.B then
      (if r < 8 then d.leafI k (Fin.ofNat 13 r)
        else if r = 8 then oqW80 d.s
        else if r = 9 then d.leafI k 8
        else d.leafO (k + 1) (Fin.ofNat 13 (r - 10)))
    else
      (if r < 9 then d.leafI k (Fin.ofNat 13 r) else d.leafO (k + 1) (Fin.ofNat 13 (r - 9)))

/-- The leaf's digest. -/
def leaf : Digest := merkleLeafDigest d.row

/-- **The honest value of index `i` of the query.** -/
def val (i : ℕ) : E :=
  if i < d.b + d.s.R then d.rw (i - d.b)
  else if i < d.k1 then
    [word 0 1 0, word 0 1 0 * d.rw (2 * ((i - d.b - d.s.R) / 3) + 1),
      d.pk ((i - d.b - d.s.R) / 3)].getD ((i - d.b - d.s.R) % 3) 0
  else if i < d.k1 + d.s.D then d.dotV (i - d.k1)
  else if i < d.kL then [word 1 0 0, word 0 0 0, word 0 0 0, word 0 0 0, word 0 0 0].getD
    (i - (d.k1 + d.s.D)) 0
  else if i < d.ch then d.leafV (i - d.kL)
  else 0

end QD

namespace QD

variable (d : QD)

/-! ## The pieces' places -/

theorem k1_eq : d.k1 = d.b + d.s.R + 3 * (d.s.R / 2) := rfl
theorem kL_eq : d.kL = d.k1 + d.s.D + (if d.emit then 5 else 0) := rfl
theorem ch_eq : d.ch = d.kL + d.s.chainLen := rfl
theorem e_eq : d.e = d.ch := rfl

theorem end_eq : oqEnd d.s d.b d.emit = d.e := rfl

/-- The honest valuation on a query's values. -/
abbrev Hv (d : QD) (σ : Val) : Prop := ∀ i, d.b ≤ i → i < d.e → σ (.n i) = d.val i

theorem val_row {j : ℕ} (hj : j < d.s.R) : d.val (d.b + j) = d.rw j := by
  unfold val; simp [hj]

theorem val_pack {j t : ℕ} (hj : j < d.s.R / 2) (ht : t < 3) :
    d.val (d.b + d.s.R + 3 * j + t) =
      [word 0 1 0, word 0 1 0 * d.rw (2 * j + 1), d.pk j].getD t 0 := by
  unfold val
  have := k1_eq d
  simp only [show ¬ d.b + d.s.R + 3 * j + t < d.b + d.s.R by omega,
    show d.b + d.s.R + 3 * j + t < d.k1 by omega, ↓reduceIte,
    show (d.b + d.s.R + 3 * j + t - d.b - d.s.R) / 3 = j by omega,
    show (d.b + d.s.R + 3 * j + t - d.b - d.s.R) % 3 = t by omega]

theorem val_dot {i : ℕ} (hi : i < d.s.D) : d.val (d.k1 + i) = d.dotV i := by
  unfold val
  have := k1_eq d
  simp only [show ¬ d.k1 + i < d.b + d.s.R by omega, show ¬ d.k1 + i < d.k1 by omega,
    show d.k1 + i < d.k1 + d.s.D by omega, ↓reduceIte, Nat.add_sub_cancel_left]

theorem val_pad (he : d.emit = true) {i : ℕ} (hi : i < 5) :
    d.val (d.k1 + d.s.D + i) =
      [word 1 0 0, word 0 0 0, word 0 0 0, word 0 0 0, word 0 0 0].getD i 0 := by
  unfold val
  have := k1_eq d
  have hkL : d.kL = d.k1 + d.s.D + 5 := by rw [kL_eq, he]; rfl
  simp only [show ¬ d.k1 + d.s.D + i < d.b + d.s.R by omega,
    show ¬ d.k1 + d.s.D + i < d.k1 by omega, show ¬ d.k1 + d.s.D + i < d.k1 + d.s.D by omega,
    show d.k1 + d.s.D + i < d.kL by omega, ↓reduceIte, Nat.add_sub_cancel_left]

theorem val_leaf {i : ℕ} (hi : i < d.s.chainLen) : d.val (d.kL + i) = d.leafV i := by
  unfold val
  have := k1_eq d
  have h1 := kL_eq d
  have h2 : d.k1 + d.s.D ≤ d.kL := by rw [h1]; split <;> omega
  simp only [show ¬ d.kL + i < d.b + d.s.R by omega, show ¬ d.kL + i < d.k1 by omega,
    show ¬ d.kL + i < d.k1 + d.s.D by omega, show ¬ d.kL + i < d.kL by omega,
    show d.kL + i < d.ch by rw [ch_eq]; omega, ↓reduceIte, Nat.add_sub_cancel_left]

theorem le_kL : d.k1 + d.s.D ≤ d.kL := by rw [kL_eq]; split <;> omega

end QD

namespace QD

/-! ## Decoding the dot product -/

/-- The offset of group `h`. -/
def gsOff (G h : ℕ) : ℕ := if h = 0 then 0 else h * (G + 1) - 1

/-- The offset of term `l` in its group. -/
def tsOff (t l : ℕ) : ℕ := if l = 0 then 0 else (2 + t) + (l - 1) * (3 + t)

theorem dotH_eq {G h r : ℕ} (hG : 2 ≤ G) (hr : r < (if h = 0 then G else G + 1)) :
    dotH G (gsOff G h + r) = h ∧ dotR G (gsOff G h + r) = r := by
  unfold dotR dotH gsOff
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · simp only [↓reduceIte] at hr ⊢
    simp [hr]
  · simp only [show h ≠ 0 by omega, ↓reduceIte] at hr ⊢
    obtain ⟨a, rfl⟩ : ∃ a, h = a + 1 := ⟨h - 1, by omega⟩
    have hm : (a + 1) * (G + 1) = (G + 1) * a + (G + 1) := by ring
    rw [hm]
    have hdiv : ((G + 1) * a + (G + 1) - 1 + r - G) / (G + 1) = a := by
      rw [show (G + 1) * a + (G + 1) - 1 + r - G = (G + 1) * a + r by omega,
        Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, Nat.add_zero]
    have hlt : ¬ (G + 1) * a + (G + 1) - 1 + r < G := by omega
    simp only [hlt, ↓reduceIte, hdiv, true_and]
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    omega

theorem termL_eq {t l o : ℕ} (ho : o < (if l = 0 then 2 + t else 3 + t)) :
    termL t (tsOff t l + o) = l ∧ termO t (tsOff t l + o) = o := by
  unfold termL termO tsOff
  rcases Nat.eq_zero_or_pos l with rfl | hpos
  · simp only [↓reduceIte] at ho ⊢
    simp [ho]
  · simp only [show l ≠ 0 by omega, ↓reduceIte] at ho ⊢
    obtain ⟨a, rfl⟩ : ∃ a, l = a + 1 := ⟨l - 1, by omega⟩
    have e : 2 + t + (a + 1 - 1) * (3 + t) + o - (2 + t) = (3 + t) * a + o := by
      rw [Nat.add_sub_cancel]; ring_nf; omega
    simp only [show ¬ 2 + t + (a + 1 - 1) * (3 + t) + o < 2 + t by omega, ↓reduceIte, e,
      Nat.mul_add_div (show 0 < 3 + t by omega), Nat.div_eq_of_lt ho, Nat.add_zero,
      Nat.mul_add_mod, Nat.mod_eq_of_lt ho, and_true]

/-- The dot product's offset of term `l`'s value `o` in group `h`. -/
theorem oqTs_eq (s : Oq) (b h l : ℕ) :
    oqTs s b h l = oqK1 b s.R + gsOff s.G h + tsOff s.tsz l := by
  simp [oqTs, oqGs, gsOff, tsOff]


/-- The shape's numbers. -/
theorem shape_nums {s : Oq} (hs : s.RowShape) :
    (s.base = 1 ∧ s.I = 64 ∧ s.tsz = 0 ∧ s.lo = 8 ∧ s.G = 25 ∧ s.R = 64 ∧ s.D = 207 ∧
      s.ncells = 32 ∧ s.B = 4 ∧ s.chainLen = 69) ∨
    (s.base = 0 ∧ s.I = 16 ∧ s.tsz = 3 ∧ s.lo = 8 ∧ s.G = 49 ∧ s.R = 48 ∧ s.D = 99 ∧
      s.ncells = 24 ∧ s.B = 3 ∧ s.chainLen = 47) := by
  rcases hs with ⟨hb, hI⟩ | ⟨hb, hI⟩
  · left; simp [Oq.tsz, Oq.lo, Oq.G, Oq.R, Oq.D, Oq.ncells, Oq.B, Oq.chainLen, rowLo, rate, hb, hI]
  · right; simp [Oq.tsz, Oq.lo, Oq.G, Oq.R, Oq.D, Oq.ncells, Oq.B, Oq.chainLen, rowLo, rate, hb, hI]

variable (d : QD)

theorem dotV_term (hs : d.s.RowShape) {h l o : ℕ} (hl : l < d.s.lo)
    (ho : o < (if l = 0 then 2 + d.s.tsz else 3 + d.s.tsz)) :
    d.dotV (gsOff d.s.G h + tsOff d.s.tsz l + o) = d.termV h l o := by
  have hr : tsOff d.s.tsz l + o < d.s.G - 2 := by
    unfold tsOff
    rcases shape_nums hs with ⟨-, -, ht, hlo, hG, -⟩ | ⟨-, -, ht, hlo, hG, -⟩ <;>
      simp only [ht, hlo, hG] at ho hl ⊢ <;> split <;> split at ho <;> omega
  have hG2 : 2 ≤ d.s.G := by omega
  obtain ⟨e1, e2⟩ := dotH_eq (G := d.s.G) (h := h) (r := tsOff d.s.tsz l + o) hG2
    (by split <;> omega)
  rw [Nat.add_assoc]
  unfold dotV
  rw [e1, e2]
  simp only [hr, ↓reduceIte]
  obtain ⟨f1, f2⟩ := termL_eq (t := d.s.tsz) (l := l) (o := o) ho
  rw [f1, f2]

theorem dotV_tail (hs : d.s.RowShape) {h o : ℕ} (ho : o < (if h = 0 then 2 else 3)) :
    d.dotV (gsOff d.s.G h + (d.s.G - 2 + o)) =
      [d.w (d.s.lo + h), d.w (d.s.lo + h) * d.partV h (d.s.lo - 1), d.dotAfterV h].getD o 0 := by
  have hG : 2 ≤ d.s.G := by
    rcases shape_nums hs with ⟨-, -, -, -, hG, -⟩ | ⟨-, -, -, -, hG, -⟩ <;> omega
  obtain ⟨e1, e2⟩ := dotH_eq (G := d.s.G) (h := h) (r := d.s.G - 2 + o) hG (by split at ho <;> split <;> omega)
  unfold dotV
  rw [e1, e2]
  rcases (show o = 0 ∨ o = 1 ∨ o = 2 by split at ho <;> omega) with rfl | rfl | rfl
  · simp
  · rw [show d.s.G - 2 + 1 = d.s.G - 1 by omega]
    simp only [show ¬ d.s.G - 1 < d.s.G - 2 by omega, show ¬ d.s.G - 1 = d.s.G - 2 by omega,
      ↓reduceIte]; rfl
  · rw [show d.s.G - 2 + 2 = d.s.G by omega]
    simp only [show ¬ d.s.G < d.s.G - 2 by omega, show ¬ d.s.G = d.s.G - 2 by omega,
      show ¬ d.s.G = d.s.G - 1 by omega, ↓reduceIte]; rfl

end QD


/-! ## An honest `walk_path` frame -/

/-- **An honest frame of `walk_path__L{pd}_L{cd}`** (`s`'s `pd` and `cd`): the leaf's digest it
climbs from, the position, the siblings, the window pointer, the cap's and the flags' pointers. -/
structure WD where
  pd : ℕ
  cd : ℕ
  leaf : Digest
  q : ℕ
  sibs : List Digest
  bpv : E
  capv : E
  flagsv : E

/-- The walk frame of a query whose windows are at `bpv`. -/
def QD.wd (d : QD) (bpv : E) : WD := ⟨d.s.pd, d.s.cd, d.leaf, d.q, d.sibs, bpv, d.capv, d.flagsv⟩

/-- A window's values: its word, (window `0`) the padding run, `0x80`, `2^w` arms of `14w` values
and the two targets. -/
def winSz (s : Oq) (i : ℕ) : ℕ := 4 + oqWo i + 3 * oqWw s i * 2 ^ oqWw s i

namespace WD

variable (w : WD)

/-- The walk's shape: only its `pd` and `cd` are read. -/
def s : Oq := ⟨0, 0, w.pd, w.cd⟩

/-- The windows' first value. -/
def W0 : ℕ := oqWk w.s wpCh 0
/-- The cap section. -/
def Cq : ℕ := oqCq w.s wpCh
/-- The frame's values. -/
def e : ℕ := w.Cq + 9

/-- Path cell `k`: the node on the walk's side, the sibling off it. -/
def pc (k : ℕ) : E := pathCell w.leaf w.q w.sibs k

/-- The node after `l` levels. -/
def node (l : ℕ) : Digest := climbNode w.leaf w.q w.sibs l

/-- The cells level `l`'s permutation reads. -/
def levelIns (l : ℕ) : List E :=
  [w.pc (4 * l), w.pc (4 * l + 1), w.pc (4 * l + 2), w.pc (4 * l + 3), word 1 0 0, word 0 0 0,
    word 0 0 0, word 0 0 0, word (2 ^ 63) 0 0, word 0 0 0, word 0 0 0, word 0 0 0, word 0 0 0]

/-- Level `l`'s step at offset `c < 3`: the `0x80` constant, the permutation's first two cells. -/
def stepV (l c : ℕ) : E :=
  if c = 0 then word (2 ^ 63) 0 0 else cellsOfState (permOf (w.levelIns l)) false (Fin.ofNat 13 (c - 1))

/-- Window `i`'s value: the position's bits there. -/
def wv (i : ℕ) : ℕ := qwVal (w.s.pd + w.s.cd) w.s.cd w.q i

/-- The offset of arm `a` in a window of `ww` levels, after the padding run. -/
def armOff (ww a : ℕ) : ℕ := if a = 0 then 2 else 4 + 3 * ww * a

/-- Window `i`'s value at offset `o ≥ 1` after its padding run: `0x80`, the targets (the node after
it), arm `v`'s steps, `0` elsewhere (the arms not taken). -/
def winA (i o : ℕ) : E :=
  if o = 1 then word (2 ^ 63) 0 0
  else if o = 2 + 3 * oqWw w.s i then (digestHalves (w.node (6 * i + oqWw w.s i))).1
  else if o = 3 + 3 * oqWw w.s i then (digestHalves (w.node (6 * i + oqWw w.s i))).2
  else if armOff (oqWw w.s i) (w.wv i) ≤ o ∧ o < armOff (oqWw w.s i) (w.wv i) + 3 * oqWw w.s i then
    w.stepV (6 * i + (o - armOff (oqWw w.s i) (w.wv i)) / 3) ((o - armOff (oqWw w.s i) (w.wv i)) % 3)
  else 0

/-- The padding run's cell `k`: `1, 0, 0, 0, 0`. -/
def padV (k : ℕ) : E := [word 1 0 0, word 0 0 0, word 0 0 0, word 0 0 0, word 0 0 0].getD k 0

/-- Window `i`'s value at offset `o`: its word `g^v`, (window `0`) the padding run, then `winA`. -/
def winV (i o : ℕ) : E :=
  if o = 0 then gen ^ w.wv i else if o ≤ oqWo i then padV (o - 1) else w.winA i (o - oqWo i)

/-- The cap child bit's window `g^b`. -/
def wbV : E := gen ^ (if w.q.testBit w.s.pd then 1 else 0)

/-- The cap parent index's window `g^Q`. -/
def qV : E := gen ^ (w.q / 2 ^ (w.s.pd + 1))

/-- The cap leaf at offset `o < 9`. -/
def capV (o : ℕ) : E :=
  [w.wbV, w.qV, w.flagsv * w.qV, word 1 0 0, w.qV * w.qV, w.capv * (w.qV * w.qV),
    w.capv * (w.qV * w.qV) * (w.qV * w.qV), w.wbV * w.wbV,
    w.capv * (w.qV * w.qV) * (w.qV * w.qV) * (w.wbV * w.wbV)].getD o 0

/-- **The honest value of index `i` of the walk's frame.** -/
def val (i : ℕ) : E :=
  if i = 0 then (digestHalves w.leaf).1
  else if i = 1 then (digestHalves w.leaf).2
  else if i = 2 then w.bpv
  else if i = 3 then w.capv
  else if i = 4 then w.flagsv
  else if i < w.W0 then w.pc (i - wpCh)
  else if i < w.Cq then
    (if i - w.W0 < winSz w.s 0 then w.winV 0 (i - w.W0)
      else w.winV ((i - w.W0 - winSz w.s 0) / 1156 + 1) ((i - w.W0 - winSz w.s 0) % 1156))
  else w.capV (i - w.Cq)

/-- What the memory holds of an honest walk: its windows at `bpv`, its cap leaf and its flag. -/
structure MemOk (w : WD) (rd : Reader) : Prop where
  wins : ∀ i < qwN (w.s.pd + w.s.cd) w.s.cd, LoadHolds rd w.bpv i (gen ^ w.wv i)
  cap0 : LoadHolds rd w.capv (2 * (2 ^ w.s.cd + w.q / 2 ^ w.s.pd))
    (digestHalves (climbD w.leaf w.q w.sibs)).1
  cap1 : LoadHolds rd w.capv (2 * (2 ^ w.s.cd + w.q / 2 ^ w.s.pd) + 1)
    (digestHalves (climbD w.leaf w.q w.sibs)).2
  flag : LoadHolds rd w.flagsv (2 ^ (w.s.cd - 1) + w.q / 2 ^ (w.s.pd + 1)) 1

end WD

/-! ## The walk frame's places -/

theorem winSz_le (s : Oq) (i : ℕ) : winSz s i ≤ 1156 + oqWo i := by
  have h := oqWw_le s i
  unfold winSz
  interval_cases (oqWw s i) <;> norm_num <;> omega

theorem winSz_le' (s : Oq) {i : ℕ} (hi : 1 ≤ i) : winSz s i ≤ 1156 := by
  have := winSz_le s i
  simp only [oqWo, show i ≠ 0 by omega, ↓reduceIte] at this; omega

theorem winSz_full {s : Oq} {i : ℕ} (hi : i + 1 < oqNpw s) : winSz s i = 1156 + oqWo i := by
  unfold winSz oqWw; simp only [show ¬ i + 1 = oqNpw s by omega, ↓reduceIte]; norm_num; ring

theorem oqWk_succ (s : Oq) (ch i : ℕ) : oqWk s ch (i + 1) = oqWk s ch i + winSz s i := by
  simp [oqWk, winSz]; ring

/-- Window `i ≥ 1` starts after window `0` and `i - 1` full windows of `1156` values. -/
theorem oqWk_eq {s : Oq} {ch : ℕ} : ∀ {i : ℕ}, 1 ≤ i → i < oqNpw s →
    oqWk s ch i = ch + 4 * s.pd + winSz s 0 + 1156 * (i - 1)
  | 0, h, _ => absurd h (by omega)
  | 1, _, _ => by rw [oqWk_succ]; simp [oqWk]
  | i + 2, _, h => by
    rw [oqWk_succ, oqWk_eq (by omega) (by omega), winSz_full h]
    simp only [oqWo, show i + 1 ≠ 0 by omega, ↓reduceIte]; omega

theorem oqWk_mono {s : Oq} {ch : ℕ} : ∀ {i j : ℕ}, i ≤ j → oqWk s ch i ≤ oqWk s ch j
  | _, 0, h => by rw [Nat.le_zero.mp h]
  | i, j + 1, h => by
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · rw [oqWk_succ]; have := oqWk_mono (s := s) (ch := ch) (show i ≤ j by omega); omega
    · rw [show i = j + 1 by omega]

namespace WD

variable (w : WD)

theorem W0_eq : w.W0 = wpCh + 4 * w.s.pd := rfl
theorem e_eq : w.e = w.Cq + 9 := rfl

theorem W0_le_Cq : w.W0 ≤ w.Cq := oqWk_mono (Nat.zero_le _)

theorem win_le_Cq {i : ℕ} (hi : i < oqNpw w.s) : oqWk w.s wpCh i + winSz w.s i ≤ w.Cq := by
  rw [← oqWk_succ]; exact oqWk_mono hi

theorem val_0 : w.val 0 = (digestHalves w.leaf).1 := rfl
theorem val_1 : w.val 1 = (digestHalves w.leaf).2 := rfl
theorem val_2 : w.val 2 = w.bpv := rfl
theorem val_3 : w.val 3 = w.capv := rfl
theorem val_4 : w.val 4 = w.flagsv := rfl

theorem val_pc {o : ℕ} (ho : o < 4 * w.s.pd) : w.val (wpCh + o) = w.pc o := by
  unfold val
  have := W0_eq w
  simp only [wpCh] at this ⊢
  simp only [show 5 + o ≠ 0 by omega, show 5 + o ≠ 1 by omega, show 5 + o ≠ 2 by omega,
    show 5 + o ≠ 3 by omega, show 5 + o ≠ 4 by omega, show 5 + o < w.W0 by omega, ↓reduceIte,
    Nat.add_sub_cancel_left]

theorem val_win {i o : ℕ} (hi : i < oqNpw w.s) (ho : o < winSz w.s i) :
    w.val (oqWk w.s wpCh i + o) = w.winV i o := by
  have h4 := W0_eq w
  have h5 := w.win_le_Cq hi
  have hW := oqWk_mono (s := w.s) (ch := wpCh) (Nat.zero_le i)
  have hW0 : oqWk w.s wpCh 0 = w.W0 := rfl
  unfold val
  simp only [wpCh] at h4
  simp only [show oqWk w.s wpCh i + o ≠ 0 by omega, show oqWk w.s wpCh i + o ≠ 1 by omega,
    show oqWk w.s wpCh i + o ≠ 2 by omega, show oqWk w.s wpCh i + o ≠ 3 by omega,
    show oqWk w.s wpCh i + o ≠ 4 by omega, show ¬ oqWk w.s wpCh i + o < w.W0 by omega,
    show oqWk w.s wpCh i + o < w.Cq by omega, ↓reduceIte]
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp only [hW0, Nat.add_sub_cancel_left, ho, ↓reduceIte]
  · have h6 := oqWk_eq (s := w.s) (ch := wpCh) hpos hi
    have h7 := winSz_le' w.s hpos
    simp only [wpCh] at h6 h7 ⊢
    simp only [show ¬ oqWk w.s 5 i + o - w.W0 < winSz w.s 0 by omega, ↓reduceIte]
    rw [show (oqWk w.s 5 i + o - w.W0 - winSz w.s 0) / 1156 + 1 = i by omega,
      show (oqWk w.s 5 i + o - w.W0 - winSz w.s 0) % 1156 = o by omega]

theorem val_cap {o : ℕ} : w.val (w.Cq + o) = w.capV o := by
  have h4 := W0_eq w
  have h5 := w.W0_le_Cq
  unfold val
  simp only [wpCh] at h4
  simp only [show w.Cq + o ≠ 0 by omega, show w.Cq + o ≠ 1 by omega, show w.Cq + o ≠ 2 by omega,
    show w.Cq + o ≠ 3 by omega, show w.Cq + o ≠ 4 by omega, show ¬ w.Cq + o < w.W0 by omega,
    show ¬ w.Cq + o < w.Cq by omega, ↓reduceIte, Nat.add_sub_cancel_left]

end WD

end
end LeanVM.Guest.B1
