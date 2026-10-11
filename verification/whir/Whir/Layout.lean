import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-!
Executable indexing model for `pcs/whir/commit.rs`, `whir/verify.rs`,
`whir.rs`, and `stack_open.rs` at edafd396120f453de6f75013f231bfda2049f217.
Lane blocks occupy the TOP witness coordinates. Stored L0 rows reverse only
live lanes; restoration prefixes zeros before reversing the full leaf.
No field law or cryptographic assumption is used here.
-/
namespace Whir.Layout

/-- The mathematical commit shape. `logRows > 0` is Rust's `log_n > k`.
There is deliberately no assumption that more than half the lanes are live:
the minimum stack-size floor and the public commit interface allow fewer. -/
structure Shape where
  logRows : Nat
  logLanes : Nat
  liveLanes : Nat
  logInvRate : Nat
  rowsPositive : 0 < logRows
  livePositive : 0 < liveLanes
  liveBound : liveLanes ≤ 2 ^ logLanes
  ratePositive : 0 < logInvRate
  deriving DecidableEq

def Shape.rows (s : Shape) : Nat := 2 ^ s.logRows
def Shape.lanes (s : Shape) : Nat := 2 ^ s.logLanes
def Shape.positions (s : Shape) : Nat := 2 ^ (s.logRows + s.logInvRate)
def Shape.messageLength (s : Shape) : Nat := s.liveLanes * s.rows
def Shape.cubeLength (s : Shape) : Nat := s.lanes * s.rows

/-- Additional bounds for Rust's 64-bit shifts and its 4096-word transpose tile.
These are not silently imposed on the algebraic model. -/
def Shape.machineBounded (s : Shape) : Prop :=
  s.logRows + s.logLanes < 64 ∧ s.logRows + s.logInvRate < 64 ∧
  s.liveLanes ≤ 4096 ∧ s.positions * s.liveLanes < 2 ^ 64

 theorem Shape.message_le_cube (s : Shape) : s.messageLength ≤ s.cubeLength :=
  Nat.mul_le_mul_right s.rows s.liveBound

/-- Stack index: low row bits, then the high lane bits. -/
def stackIndex (rows lane row : Nat) : Nat := lane * rows + row

 theorem stackIndex_partition {rows lane row : Nat} (h : row < rows) :
    stackIndex rows lane row / rows = lane ∧
    stackIndex rows lane row % rows = row := by
  constructor
  · rw [stackIndex, Nat.mul_comm, Nat.mul_add_div (by omega)]
    simp [Nat.div_eq_of_lt h]
  · simp [stackIndex, Nat.add_mod, Nat.mod_eq_of_lt h]

 theorem stackIndex_bound {rows lanes lane row : Nat}
    (hl : lane < lanes) (hr : row < rows) : stackIndex rows lane row < lanes * rows := by
  unfold stackIndex
  nlinarith

 theorem stackIndex_reconstruct (rows index : Nat) :
    stackIndex rows (index / rows) (index % rows) = index := by
  simpa [stackIndex, Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div index rows

/-- The actual descending-lane transpose, not a plain matrix transpose. -/
def transposeIndex (lanes rows : Nat) : (Fin lanes × Fin rows) ≃ (Fin rows × Fin lanes) where
  toFun p := (p.2, p.1.rev)
  invFun p := (p.2.rev, p.1)
  left_inv p := by simp
  right_inv p := by simp

 theorem transposeIndex_lane (lanes rows : Nat) (p : Fin lanes × Fin rows) :
    ((transposeIndex lanes rows p).2 : Nat) = lanes - 1 - p.1.val := by
  change lanes - (p.1.val + 1) = lanes - 1 - p.1.val
  omega

 theorem transposeIndex_inverse (lanes rows : Nat) (p : Fin lanes × Fin rows) :
    (transposeIndex lanes rows).symm (transposeIndex lanes rows p) = p :=
  (transposeIndex lanes rows).symm_apply_apply p

 theorem transposeIndex_permutation (lanes rows : Nat) :
    Function.Bijective (transposeIndex lanes rows) :=
  (transposeIndex lanes rows).bijective

/-- Flat destination address used by `transpose_lane_major`. -/
def codeIndex (lanes row lane : Nat) : Nat := row * lanes + (lanes - 1 - lane)

 theorem codeIndex_bound {lanes rows lane row : Nat}
    (hl : lane < lanes) (hr : row < rows) : codeIndex lanes row lane < rows * lanes := by
  have : lanes - 1 - lane < lanes := by omega
  exact stackIndex_bound hr this

 theorem codeIndex_partition {lanes lane row : Nat} (hl : lane < lanes) :
    codeIndex lanes row lane / lanes = row ∧
      lanes - 1 - (codeIndex lanes row lane % lanes) = lane := by
  have hrev : lanes - 1 - lane < lanes := by omega
  obtain ⟨hq, hr⟩ := stackIndex_partition (lane := row) hrev
  constructor
  · exact hq
  · change lanes - 1 - (stackIndex lanes row (lanes - 1 - lane) % lanes) = lane
    rw [hr]
    omega

 theorem codeIndex_injective {lanes row row' lane lane' : Nat}
    (h : lane < lanes) (h' : lane' < lanes)
    (eq : codeIndex lanes row lane = codeIndex lanes row' lane') :
    row = row' ∧ lane = lane' := by
  obtain ⟨hq, hl⟩ := codeIndex_partition (row := row) h
  obtain ⟨hq', hl'⟩ := codeIndex_partition (row := row') h'
  rw [eq] at hq hl
  exact ⟨hq.symm.trans hq', hl.symm.trans hl'⟩

/-- Executable transpose of bounded data, including the physical row reversal. -/
def transposeData {α : Type*} {lanes rows : Nat}
    (stack : Fin lanes × Fin rows → α) : Fin rows × Fin lanes → α :=
  fun p => stack ((transposeIndex lanes rows).symm p)

 theorem transposeData_recovers {α : Type*} {lanes rows : Nat}
    (stack : Fin lanes × Fin rows → α) (p : Fin lanes × Fin rows) :
    transposeData stack (transposeIndex lanes rows p) = stack p := by
  simp [transposeData]

/-- Padding in witness order is trailing; the full Merkle image reverses it. -/
def padTail {α : Type*} (zero : α) (width : Nat) (live : List α) : List α :=
  live ++ List.replicate (width - live.length) zero

def prunedLeaf {α : Type*} (live : List α) : List α := live.reverse

def restoreLeaf {α : Type*} (zero : α) (width : Nat) (stored : List α) : List α :=
  List.replicate (width - stored.length) zero ++ stored

 theorem restoreLeaf_eq_full {α : Type*} (zero : α) (width : Nat) (live : List α) :
    restoreLeaf zero width (prunedLeaf live) = (padTail zero width live).reverse := by
  simp [restoreLeaf, prunedLeaf, padTail, List.reverse_append]

 theorem restored_reverse_eq_padding {α : Type*} (zero : α) (width : Nat) (live : List α) :
    (restoreLeaf zero width (prunedLeaf live)).reverse = padTail zero width live := by
  rw [restoreLeaf_eq_full, List.reverse_reverse]

 theorem restoreLeaf_length {α : Type*} (zero : α) (width : Nat) (stored : List α)
    (h : stored.length ≤ width) : (restoreLeaf zero width stored).length = width := by
  simp [restoreLeaf]
  omega

 theorem restoreLeaf_drop_prefix {α : Type*} (zero : α) (width : Nat) (stored : List α) :
    (restoreLeaf zero width stored).drop (width - stored.length) = stored := by
  simp [restoreLeaf]

 theorem prunedLeaf_inverse {α : Type*} (live : List α) : (prunedLeaf live).reverse = live := by
  simp [prunedLeaf]

/-- A finitely supported weight sees no choice of witness outside its live prefix. -/
theorem padding_noninterference {α : Type*} [MulZeroClass α]
    (live width : Nat) (weight witness other : Nat → α)
    (same : ∀ i, i < live → witness i = other i)
    (support : ∀ i, live ≤ i → weight i = 0) :
    (List.range width).map (fun i => witness i * weight i) =
      (List.range width).map (fun i => other i * weight i) := by
  apply List.map_congr_left
  intro i _
  by_cases h : i < live
  · rw [same i h]
  · simp [support i (by omega)]

/-- Only the caller's transparent weight consumes witness-coordinate order. -/
def terminalPoint {α : Type*} (initialK : Nat) (roundPoint : List α) : List α :=
  roundPoint.rotate initialK

/-- Induced and OOD weights keep their suffix of ROUND order. -/
def levelPoint {α : Type*} (start : Nat) (folds tail : List α) : List α :=
  folds.drop start ++ tail

 theorem terminalPoint_order {α : Type*} (lanes low : List α) :
    terminalPoint lanes.length (lanes ++ low) = low ++ lanes := by
  simp [terminalPoint]

 theorem terminalPoint_length {α : Type*} (k : Nat) (point : List α) :
    (terminalPoint k point).length = point.length := by simp [terminalPoint]

 theorem terminalPoint_permutation {α : Type*} (k : Nat) (point : List α) :
    (terminalPoint k point).Perm point := List.rotate_perm point k

 theorem terminalPoint_inverse {α : Type*} (k : Nat) (point : List α) (h : k ≤ point.length) :
    terminalPoint (point.length - k) (terminalPoint k point) = point := by
  simp [terminalPoint, Nat.add_sub_of_le h]

 theorem terminalPoint_slices {α : Type*} (k : Nat) (point : List α) (h : k ≤ point.length) :
    terminalPoint k point = point.drop k ++ point.take k :=
  List.rotate_eq_drop_append_take h

 theorem levelPoint_order {α : Type*} (before after tail : List α) :
    levelPoint before.length (before ++ after) tail = after ++ tail := by
  simp [levelPoint]

/-- Bound-carrying counterpart of Rust's `Stratum`. -/
structure Stratum (depth : Nat) where
  bits : Nat
  index : Nat
  bits_le : bits ≤ depth
  index_lt : index < 2 ^ bits
  deriving DecidableEq

/-- The group's `j`th coset, including modulo wrap beyond the domain size. -/
def stratumAt (depth g j : Nat) : Stratum depth :=
  ⟨min g depth, j % 2 ^ min g depth, Nat.min_le_right _ _, Nat.mod_lt _ (by positivity)⟩

/-- One set binary digit, enumerated in increasing `j`, not sorted by query. -/
def stratumGroup (depth g : Nat) : List (Stratum depth) :=
  (List.range (2 ^ g)).map (stratumAt depth g)

/-- Scan the `width` binary digits from highest to lowest, just as Rust does.
Correct count requires `count < 2^width`; Rust uses `width = usize::BITS`. -/
def strataBits (width count depth : Nat) : List (Stratum depth) :=
  match width with
  | 0 => []
  | width + 1 =>
    if 2 ^ width ≤ count then
      stratumGroup depth width ++ strataBits width (count - 2 ^ width) depth
    else strataBits width count depth

 theorem stratumGroup_length (depth g : Nat) : (stratumGroup depth g).length = 2 ^ g := by
  simp [stratumGroup]

 theorem strataBits_length (width count depth : Nat) (h : count < 2 ^ width) :
    (strataBits width count depth).length = count := by
  induction width generalizing count with
  | zero => simp_all [strataBits]
  | succ width ih =>
    have hp : 2 ^ (width + 1) = 2 ^ width * 2 := by rw [pow_succ]
    simp only [strataBits]
    split_ifs with hc
    · rw [List.length_append, stratumGroup_length, ih (count - 2 ^ width) (by omega)]
      omega
    · exact ih count (by omega)

/-- Low bits are sampled; top bits are replaced, never added with carry. -/
def placeQuery {depth : Nat} (s : Stratum depth) (raw : Nat) : Nat :=
  raw % 2 ^ (depth - s.bits) + s.index * 2 ^ (depth - s.bits)

 theorem placeQuery_bound {depth : Nat} (s : Stratum depth) (raw : Nat) :
    placeQuery s raw < 2 ^ depth := by
  have hlo := Nat.mod_lt raw (show 0 < 2 ^ (depth - s.bits) by positivity)
  have hpow : 2 ^ depth = 2 ^ s.bits * 2 ^ (depth - s.bits) := by
    rw [← pow_add, Nat.add_sub_of_le s.bits_le]
  unfold placeQuery
  rw [hpow]
  have hm := Nat.mul_le_mul_right (2 ^ (depth - s.bits)) (Nat.succ_le_iff.mpr s.index_lt)
  nlinarith [s.index_lt]

 theorem placeQuery_top {depth : Nat} (s : Stratum depth) (raw : Nat) :
    placeQuery s raw / 2 ^ (depth - s.bits) = s.index := by
  have hp : 0 < 2 ^ (depth - s.bits) := by positivity
  rw [placeQuery, Nat.add_mul_div_right _ _ hp]
  simp [Nat.div_eq_of_lt (Nat.mod_lt raw hp)]

 theorem stratumAt_periodic (depth g j : Nat) :
    stratumAt depth g (j + 2 ^ min g depth) = stratumAt depth g j := by
  simp [stratumAt]

/-- Once a group covers the whole domain, its queries are deterministic and
repeat every domain length. This permits counts larger than the domain. -/
theorem fullDomain_query (depth g j raw : Nat) (h : depth ≤ g) :
    placeQuery (stratumAt depth g j) raw = j % 2 ^ depth := by
  simp [placeQuery, stratumAt, Nat.min_eq_right h, Nat.mod_one]

theorem fullDomain_repeated (depth g j raw raw' : Nat) (h : depth ≤ g) :
    placeQuery (stratumAt depth g (j + 2 ^ depth)) raw' =
      placeQuery (stratumAt depth g j) raw := by
  simp [fullDomain_query _ _ _ _ h]

theorem partialDomain_distinct (depth g i j raw raw' : Nat) (h : g ≤ depth)
    (hi : i < 2 ^ g) (hj : j < 2 ^ g) (hne : i ≠ j) :
    placeQuery (stratumAt depth g i) raw ≠ placeQuery (stratumAt depth g j) raw' := by
  intro heq
  have ht := congrArg (fun q => q / 2 ^ (depth - g)) heq
  have hti := placeQuery_top (stratumAt depth g i) raw
  have htj := placeQuery_top (stratumAt depth g j) raw'
  simp only [stratumAt, Nat.min_eq_left h, Nat.mod_eq_of_lt hi,
    Nat.mod_eq_of_lt hj] at hti htj ht
  rw [hti, htj] at ht
  exact hne ht

/-- The `i`th raw query consumes chunk `i % (192/depth)` of squeeze `i/(192/depth)`.
For the transcript sampler require `0 < depth ≤ 192`; Rust's domains satisfy this. -/
def rawQuery (depth : Nat) (squeeze : Nat → Nat) (i : Nat) : Nat :=
  (squeeze (i / (192 / depth)) / 2 ^ ((i % (192 / depth)) * depth)) % 2 ^ depth

 theorem rawQuery_bound (depth : Nat) (squeeze : Nat → Nat) (i : Nat) :
    rawQuery depth squeeze i < 2 ^ depth := Nat.mod_lt _ (by positivity)

 theorem query_chunks_positive {depth : Nat} (hpos : 0 < depth) (hmax : depth ≤ 192) :
    0 < 192 / depth := Nat.div_pos hmax hpos

 theorem query_chunk_fits {depth : Nat} (hpos : 0 < depth) (hmax : depth ≤ 192) (i : Nat) :
    (i % (192 / depth)) * depth + depth ≤ 192 := by
  have hm := Nat.mod_lt i (query_chunks_positive hpos hmax)
  have hmul := Nat.mul_le_mul_right depth (Nat.succ_le_iff.mpr hm)
  have hd := Nat.div_mul_le_self 192 depth
  nlinarith

/-- Query-indexed map, not a set: no deduplication and no sorting. -/
def sampleQueries (width count depth : Nat) (squeeze : Nat → Nat) : List Nat :=
  ((strataBits width count depth).zipIdx).map fun p => placeQuery p.1 (rawQuery depth squeeze p.2)

 theorem sampleQueries_length (width count depth : Nat) (squeeze : Nat → Nat)
    (h : count < 2 ^ width) : (sampleQueries width count depth squeeze).length = count := by
  simp [sampleQueries, strataBits_length width count depth h]

 theorem sampleQueries_bound (width count depth : Nat) (squeeze : Nat → Nat)
    (q : Nat) (h : q ∈ sampleQueries width count depth squeeze) : q < 2 ^ depth := by
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp h
  exact placeQuery_bound _ _

 theorem sampleQueries_order (width count depth : Nat) (squeeze : Nat → Nat)
    (i : Nat) (hi : i < (strataBits width count depth).length) :
    (sampleQueries width count depth squeeze)[i]'(by simp [sampleQueries]; exact hi) =
      placeQuery ((strataBits width count depth)[i]) (rawQuery depth squeeze i) := by
  simp [sampleQueries]

/-- Repeated positions re-open the same row and remain repeated list entries. -/
def openRows {α : Type*} (oracle : Nat → α) (queries : List Nat) : List α := queries.map oracle

 theorem openRows_append {α : Type*} (oracle : Nat → α) (before after : List Nat) (q : Nat) :
    openRows oracle (before ++ q :: q :: after) =
      openRows oracle before ++ oracle q :: oracle q :: openRows oracle after := by
  simp [openRows]

 theorem repeatedQuery_row {α : Type*} (oracle : Nat → α) (queries : List Nat)
    (i j : Fin queries.length) (h : queries[i] = queries[j]) :
    (openRows oracle queries)[i.val]'(by simp [openRows]) =
      (openRows oracle queries)[j.val]'(by simp [openRows]) := by
  simpa [openRows] using congrArg oracle h

end Whir.Layout
