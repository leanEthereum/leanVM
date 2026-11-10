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
* the fold (`foldVals`): round `j`'s `α, β, β·x, t, θ, 1, t⁻¹, r = θ + t⁻¹`, the scale
  `Π_(i ≤ j) t_i` (`j ≥ 1`), its outputs `r·hi`, `lo + r·hi` (`roundVals`); the value
  `scale · acc` (`foldVal`);
* at the final level (`finVals`): the point, the chain `W_i` by threes, `novel_eval`'s level `0`
  by fours (`nv0Vals`), its later levels (`nvVals`), the result `0`.

`val i` is `vals`' entry `i - b`; `WD` is an honest `walk_path` frame, `WD.val` its values.
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

theorem length_flatMap_range {α : Type} (f : ℕ → List α) :
    ∀ n, ((List.range n).flatMap f).length = offOf f n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, length_flatMap_range f n]
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
    have hl := length_flatMap_range f n
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
  rw [length_flatMap_range, offOf_const f hf]

theorem getD_flatMap_const {α : Type} (f : ℕ → List α) {c : ℕ} (hf : ∀ j, (f j).length = c)
    (d : α) {n j r : ℕ} (hj : j < n) (hr : r < c) :
    ((List.range n).flatMap f).getD (c * j + r) d = (f j).getD r d := by
  rw [← offOf_const f hf j]
  exact getD_flatMap_range_of f d n j r hj (by rw [hf]; exact hr)

/-! ## An honest query -/

/-- An honest query (its walk's siblings, cap and flags kept for its `walk_path` frame, `QD.wd`). -/
structure QD where
  s : Oq
  b : ℕ
  emit : Bool
  pr : ℕ
  row : List K
  q : ℕ
  sibs : List Digest
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
/-- The first value after the leaf hash: the fold's start. -/
def ch : ℕ := oqCh d.s d.b d.emit
/-- The fold's value. -/
def v : ℕ := oqVal d.s d.ch
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

/-! ### The fold -/

/-- Round `j`'s challenges. -/
def rd (j : ℕ) : FoldRound := d.rounds.getD j ⟨0, 0, 0⟩

/-- Round `j`'s combiner `t = α + β·x`. -/
def t (j : ℕ) : E := (d.rd j).alpha + (d.rd j).beta * d.x

/-- Round `j`'s fold factor `r = θ + t⁻¹`. -/
def r (j : ℕ) : E := (d.rd j).theta + (d.t j)⁻¹

/-- The scale after round `j`, `Π_(i ≤ j) t_i`. -/
def scale : ℕ → E
  | 0 => d.t 0
  | j + 1 => scale j * d.t (j + 1)

/-- Round `0`'s lanes `(lo, hi)` for its output `m`: the cells, reversed at level 0. -/
def lane0 (m : ℕ) : E × E :=
  if d.s.base = 1 then (d.cell (d.s.I - 1 - 2 * m), d.cell (d.s.I - 2 - 2 * m))
  else (d.cell (2 * m), d.cell (2 * m + 1))

/-- Lane `m` after round `j`. -/
def acc : ℕ → ℕ → E
  | 0, m => (d.lane0 m).1 + d.r 0 * (d.lane0 m).2
  | j + 1, m => acc j (2 * m) + d.r (j + 1) * acc j (2 * m + 1)

/-- The `hi` lane round `j` reads for its output `m`. -/
def hiV (j m : ℕ) : E := if j = 0 then (d.lane0 m).2 else d.acc (j - 1) (2 * m + 1)

/-- Round `j`'s values. -/
def roundVals (j : ℕ) : List E :=
  [(d.rd j).alpha, (d.rd j).beta, (d.rd j).beta * d.x, d.t j, (d.rd j).theta, word 1 0, (d.t j)⁻¹,
    d.r j] ++ (if j = 0 then [] else [d.scale j]) ++
  (List.range (2 ^ (d.s.folds - 1 - j))).flatMap fun m ↦ [d.r j * d.hiV j m, d.acc j m]

/-- The fold's value: the scale times the last lane. -/
def foldVal : E := d.scale (d.s.folds - 1) * d.acc (d.s.folds - 1) 0

/-- The fold's values. -/
def foldVals : List E := (List.range d.s.folds).flatMap d.roundVals ++ [d.foldVal]

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

/-- The final check's values after the fold's: the point, the chain, `novel_eval`'s levels, the
result `0`. -/
def finVals : List E :=
  if d.s.final = 1 then
    [d.x] ++ d.chainVals ++ d.nv0Vals ++
      nvVals d.W (d.s.hsBits - 1) 1 (nvPair (d.W 0) (d.hsv.take d.s.nHs)) ++ [word 0 0]
  else []

/-! ### The query -/

/-- **The query's values from `b`.** -/
def vals : List E :=
  d.rowVals ++ d.packVals ++ d.padVals ++ d.leafVals ++ d.foldVals ++ d.finVals

/-- **The honest value of index `i` of the query.** -/
def val (i : ℕ) : E := if d.b ≤ i then d.vals.getD (i - d.b) 0 else 0

/-- The honest valuation on a query's values. -/
abbrev Hv (σ : Val) : Prop := ∀ i, d.b ≤ i → i < d.e → σ (.n i) = d.val i

end QD

namespace QD

variable (d : QD)

/-! ## The pieces' places -/

theorem vals_eq : d.vals =
    d.rowVals ++ (d.packVals ++ (d.padVals ++ (d.leafVals ++ (d.foldVals ++ d.finVals)))) := by
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
    (d.roundVals j).length = 8 + (if j = 0 then 0 else 1) + 2 * 2 ^ (d.s.folds - 1 - j) := by
  unfold roundVals
  rw [List.length_append, List.length_append, length_flatMap_const _ (c := 2) (fun _ ↦ rfl)]
  split <;> simp

theorem oqRK_eq (F : ℕ) : ∀ j, oqRK d.s F j = F + offOf d.roundVals j
  | 0 => rfl
  | j + 1 => by
    rw [oqRK, oqRK_eq F j, offOf, roundVals_length]
    omega

theorem foldVals_length : d.foldVals.length = offOf d.roundVals d.s.folds + 1 := by
  simp only [foldVals, List.length_append, length_flatMap_range, List.length_singleton]

theorem k1_eq : d.k1 = d.b + d.rowVals.length + d.packVals.length := by
  rw [rowVals_length, packVals_length]; rfl

theorem kL_eq : d.kL = d.k1 + d.padVals.length := by
  rw [padVals_length]; rfl

theorem ch_eq : d.ch = d.kL + d.leafVals.length := by
  rw [leafVals_length]; rfl

theorem v_eq : d.v = d.ch + offOf d.roundVals d.s.folds := by
  rw [v, oqVal, oqRK_eq]

theorem val_add (o : ℕ) : d.val (d.b + o) = d.vals.getD o 0 := by
  simp [val]

/-- The fold's start, from `b`. -/
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

/-- The fold's values, from its start. -/
theorem val_foldVals {o : ℕ} (ho : o < d.foldVals.length) :
    d.val (d.ch + o) = d.foldVals.getD o 0 := by
  rw [ch_off, show d.b + (d.rowVals.length + (d.packVals.length + (d.padVals.length +
      d.leafVals.length))) + o = d.b + (d.rowVals.length + (d.packVals.length + (d.padVals.length +
      (d.leafVals.length + o)))) by omega, val_add, vals_eq]
  repeat rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
  rw [List.getD_append _ _ _ _ ho]

theorem val_round {j o : ℕ} (hj : j < d.s.folds) (ho : o < (d.roundVals j).length) :
    d.val (oqRK d.s d.ch j + o) = (d.roundVals j).getD o 0 := by
  have h1 : offOf d.roundVals (j + 1) ≤ offOf d.roundVals d.s.folds := offOf_mono _ hj
  simp only [offOf] at h1
  rw [oqRK_eq, Nat.add_assoc, val_foldVals _ (by rw [foldVals_length]; omega), foldVals,
    List.getD_append _ _ _ _ (by rw [length_flatMap_range]; omega)]
  exact getD_flatMap_range_of _ 0 _ _ _ hj ho

theorem val_v : d.val d.v = d.foldVal := by
  rw [v_eq, val_foldVals _ (by rw [foldVals_length]; omega), foldVals,
    List.getD_append_right _ _ _ _ (by rw [length_flatMap_range]), length_flatMap_range,
    Nat.sub_self]
  rfl

theorem val_fin (o : ℕ) : d.val (d.v + 1 + o) = d.finVals.getD o 0 := by
  have hf := d.foldVals_length
  have e : d.v + 1 + o = d.b + (d.rowVals.length + (d.packVals.length + (d.padVals.length +
      (d.leafVals.length + (d.foldVals.length + o))))) := by
    rw [v_eq, ch_off]; omega
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

theorem e_eq (hn : d.s.final = 1 → d.s.nHs % 2 = 0 ∧ d.s.nHs ≤ d.hsv.length) :
    d.e = d.b + d.vals.length := by
  have hv := d.v_eq
  have hc := d.ch_off
  have hf := d.foldVals_length
  rw [e, oqEnd, oqRes]
  change (if d.s.final = 1 then (oqNovel d.s (.n 0) d.v).2.2 else d.v) + 1 = _
  by_cases h1 : d.s.final = 1
  · simp only [h1, ↓reduceIte]
    rw [d.oqNovel_next (hn h1).1 (hn h1).2]
    simp only [vals, finVals, h1, ↓reduceIte, List.length_append, chainVals_length, nv0Vals_length,
      List.length_cons, List.length_nil]
    omega
  · simp only [h1, ↓reduceIte, vals, finVals, List.length_append, List.length_nil]
    omega

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
def s : Oq := ⟨0, 0, w.pd, w.cd, 0, [], 0, 0⟩

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
  [w.pc (4 * l), w.pc (4 * l + 1), w.pc (4 * l + 2), w.pc (4 * l + 3), word 1 0, word 0 0,
    word 0 0, word 0 0, word (2 ^ 63) 0, word 0 0, word 0 0, word 0 0, word 0 0]

/-- Level `l`'s step at offset `c < 3`: the `0x80` constant, the permutation's first two cells. -/
def stepV (l c : ℕ) : E :=
  if c = 0 then word (2 ^ 63) 0 else cellsOfState (permOf (w.levelIns l)) false (Fin.ofNat 13 (c - 1))

/-- Window `i`'s value: the position's bits there. -/
def wv (i : ℕ) : ℕ := qwVal (w.s.pd + w.s.cd) w.s.cd w.q i

/-- The offset of arm `a` in a window of `ww` levels, after the padding run. -/
def armOff (ww a : ℕ) : ℕ := if a = 0 then 2 else 4 + 3 * ww * a

/-- Window `i`'s value at offset `o ≥ 1` after its padding run: `0x80`, the targets (the node after
it), arm `v`'s steps, `0` elsewhere (the arms not taken). -/
def winA (i o : ℕ) : E :=
  if o = 1 then word (2 ^ 63) 0
  else if o = 2 + 3 * oqWw w.s i then (digestHalves (w.node (6 * i + oqWw w.s i))).1
  else if o = 3 + 3 * oqWw w.s i then (digestHalves (w.node (6 * i + oqWw w.s i))).2
  else if armOff (oqWw w.s i) (w.wv i) ≤ o ∧ o < armOff (oqWw w.s i) (w.wv i) + 3 * oqWw w.s i then
    w.stepV (6 * i + (o - armOff (oqWw w.s i) (w.wv i)) / 3) ((o - armOff (oqWw w.s i) (w.wv i)) % 3)
  else 0

/-- The padding run's cell `k`: `1, 0, 0, 0, 0`. -/
def padV (k : ℕ) : E := [word 1 0, word 0 0, word 0 0, word 0 0, word 0 0].getD k 0

/-- Window `i`'s value at offset `o`: its word `g^v`, (window `0`) the padding run, then `winA`. -/
def winV (i o : ℕ) : E :=
  if o = 0 then gen ^ w.wv i else if o ≤ oqWo i then padV (o - 1) else w.winA i (o - oqWo i)

/-- The cap child bit's window `g^b`. -/
def wbV : E := gen ^ (if w.q.testBit w.s.pd then 1 else 0)

/-- The cap parent index's window `g^Q`. -/
def qV : E := gen ^ (w.q / 2 ^ (w.s.pd + 1))

/-- The cap leaf at offset `o < 9`. -/
def capV (o : ℕ) : E :=
  [w.wbV, w.qV, w.flagsv * w.qV, word 1 0, w.qV * w.qV, w.capv * (w.qV * w.qV),
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
