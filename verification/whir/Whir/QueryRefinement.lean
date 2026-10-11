import Whir.ArrayAlgebra
import Whir.TerminalRefinement
import Whir.FieldExtension

/-! Authenticated query rows refine the shared executable column kernel.

`enforced_eq_foldLow` and `enforced_eq_foldLane` prove bilinear interchange
against the actual repeated folds, including the pruned L0 zero-padded layout.
The concrete encoder row formulas and every column dimension are proved here.

`enforced_encodeExt` and `enforced_encodeBase` are unconditional identities
between the actual encoded/authenticated rows, actual folds,
`Protocol.enforced`, and `Concrete.induced`, under only shape/query bounds.
The ring laws come from the checked operation-compatible `FieldExtension`
instance. The reusable `Representation` transport also describes precisely
which arithmetic properties these identities use. Honest-query identities
alone do not establish PCS soundness. -/
namespace Whir.QueryRefinement
open Concrete Protocol ArrayLayout ArrayAlgebra
open scoped BigOperators

variable {R : Type*} [CommRing R] [Inhabited R]

omit [Inhabited R] in
 theorem tab_sum (n : Nat) (f : Nat → R) :
    (tab n f).foldl (· + ·) 0 = ∑ i ∈ Finset.range n, f i := by
  rw [← Array.foldl_toList, toList_tab, ← List.sum_eq_foldl,
    ← List.sum_toFinset _ List.nodup_range]
  congr 1
  ext i
  simp

@[simp] theorem size_inducedColumns (width : Nat) (cols : Array (Array R))
    (weights : Array R) : (inducedColumns width cols weights).size = width := by
  simp [inducedColumns]

 theorem inducedColumns_get (width : Nat) (cols : Array (Array R))
    (weights : Array R) (j : Nat) (hj : j < width) :
    (inducedColumns width cols weights)[j]! =
      ∑ i ∈ Finset.range cols.size, weights[i]! * (cols[i]!)[j]! := by
  simp only [inducedColumns, getElem!_tab _ _ _ hj, tab_sum]

/-- Bilinear interchange for the actual weighted-column kernel. -/
 theorem dot_inducedColumns (f : Array R) (cols : Array (Array R)) (weights : Array R)
    (shape : ∀ i < cols.size, cols[i]!.size = f.size) :
    dot f (inducedColumns f.size cols weights) =
      ∑ i ∈ Finset.range cols.size, weights[i]! * dot f cols[i]! := by
  simp only [dot_eq_sum, size_inducedColumns, min_self]
  have hget : ∀ j ∈ Finset.range f.size,
      (inducedColumns f.size cols weights)[j]! =
        ∑ i ∈ Finset.range cols.size, weights[i]! * (cols[i]!)[j]! :=
    fun j hj => inducedColumns_get _ _ _ _ (Finset.mem_range.mp hj)
  simp only [Finset.sum_congr rfl (fun j hj => congrArg (f[j]! * ·) (hget j hj))]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [shape i (Finset.mem_range.mp hi), min_self]
  apply Finset.sum_congr rfl
  intro j hj
  ring

 theorem dot_tab_left (n : Nat) (f : Nat → R) (b : Array R) (h : n ≤ b.size) :
    dot (tab n f) b = ∑ i ∈ Finset.range n, f i * b[i]! := by
  simp only [dot_eq_sum, size_tab, Nat.min_eq_left h]
  apply Finset.sum_congr rfl
  intro i hi
  rw [getElem!_tab _ _ _ (Finset.mem_range.mp hi)]

/-- Swapping the lane and column sums, with all accesses in bounds. -/
 theorem dot_row_interchange (width lanes : Nat) (coeff : Nat → Nat → R)
    (col eq : Array R) (hc : col.size = width) (he : lanes ≤ eq.size) :
    dot (tab lanes fun lane => dot (tab width (coeff lane)) col) eq =
      dot (tab width fun j => dot (tab lanes fun lane => coeff lane j) eq) col := by
  simp only [dot_tab_left lanes _ eq he,
    dot_tab_left width _ col (Nat.le_of_eq hc.symm)]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro lane hl
  ring

/-- The actual verifier's enforced scalar is the dot against its induced
query weights. `rows` are authenticated encoded rows, not a supplied scalar
correctness identity. L0 reversal and later low-lane order share this theorem. -/
 theorem enforced_eq_dot_inducedColumns
    (width lanes : Nat) (coeff : Nat → Nat → R)
    (cols rows : Array (Array R)) (rs weights : Array R) (base : Bool)
    (count : rows.size = cols.size)
    (columnShape : ∀ i < cols.size, cols[i]!.size = width)
    (laneShape : lanes ≤ (eqTable rs).size)
    (honest : ∀ i < rows.size,
      (if base then rows[i]!.reverse else rows[i]!) =
        tab lanes fun lane => dot (tab width (coeff lane)) cols[i]!) :
    enforced rows rs weights base =
      dot (tab width fun j => dot (tab lanes fun lane => coeff lane j) (eqTable rs))
        (inducedColumns width cols weights) := by
  rw [enforced, tab_sum]
  have hf : (tab width fun j => dot (tab lanes fun lane => coeff lane j)
      (eqTable rs)).size = width := size_tab _ _
  have hd := dot_inducedColumns
    (tab width fun j => dot (tab lanes fun lane => coeff lane j) (eqTable rs))
    cols weights (by simpa only [hf] using columnShape)
  simp only [hf] at hd
  rw [hd]
  rw [count]
  apply Finset.sum_congr rfl
  intro i hi
  rw [honest i (by simpa [count] using Finset.mem_range.mp hi)]
  rw [dot_row_interchange width lanes coeff _ _
    (columnShape i (Finset.mem_range.mp hi)) laneShape]

/-- Exact later-level encoder row: low coordinates select the lane. -/
theorem encodeExt_row (message : Array E) (logN foldK rate q : Nat)
    (hq : q < 2 ^ (logN - foldK + rate)) :
    (encodeExt message logN foldK rate)[q]! =
      tab (2 ^ foldK) fun lane =>
        dot (tab (2 ^ (logN - foldK)) fun j => message[j * 2 ^ foldK + lane]!)
          (column (logN - foldK) q) := by
  unfold encodeExt
  rw [getElem!_tab _ _ _ hq]
  apply Array.ext
  · simp
  · intro lane hl hr
    simp only [size_tab] at hl
    simp [tab, encode, getElem!_pos, hl, hq]

/-- Exact L0 encoder row after undoing the transmitted descending lane order. -/
theorem encodeBase_row (message : Array K) (logN initialK rate q : Nat)
    (hq : q < 2 ^ (logN - initialK + rate)) :
    ((encodeBase message logN initialK rate)[q]!).reverse =
      tab (message.size / 2 ^ (logN - initialK)) fun lane =>
        dot (tab (2 ^ (logN - initialK)) fun j =>
          E.ofK message[lane * 2 ^ (logN - initialK) + j]!)
          (column (logN - initialK) q) := by
  unfold encodeBase
  rw [getElem!_tab _ _ _ hq]
  apply Array.ext
  · simp
  · intro i hi hj
    simp only [Array.size_reverse, size_tab] at hi
    have hi' : message.size / 2 ^ (logN - initialK) - 1 -
        (message.size / 2 ^ (logN - initialK) - 1 - i) = i := by omega
    simp [Array.getElem_reverse, tab, encode, getElem!_pos, hi', hi, hq]

/-- A contiguous low-lane slice commutes with one actual adjacent fold. -/
theorem foldLow_slice (a : Array R) (width lanes row : Nat) (r : R)
    (ha : a.size = width * (lanes * 2)) (hr : row < width) :
    (tab lanes fun lane => (foldLow a r)[row * lanes + lane]!) =
      foldLow (tab (lanes * 2) fun lane => a[row * (lanes * 2) + lane]!) r := by
  have half : a.size / 2 = width * lanes := by
    rw [ha, ← Nat.mul_assoc, Nat.mul_div_left _ (by decide : 0 < 2)]
  unfold foldLow
  simp only [size_tab, Nat.mul_div_left _ (by decide : 0 < 2)]
  apply Array.ext
  · simp
  · intro lane hl hr'
    have hl' : lane < lanes := by simpa using hl
    have hidx : row * lanes + lane < a.size / 2 := by
      rw [half]
      exact Layout.stackIndex_bound hr hl'
    have h0 : 2 * lane < lanes * 2 := by omega
    have h1 : 2 * lane + 1 < lanes * 2 := by omega
    simp only [tab, Array.getElem_map, List.getElem_toArray, List.getElem_range]
    change (tab (a.size / 2) fun i => foldPair a[2*i]! a[2*i+1]! r)[row * lanes + lane]! =
      foldPair
        ((tab (lanes * 2) fun i => a[row * (lanes * 2) + i]!)[2*lane]!)
        ((tab (lanes * 2) fun i => a[row * (lanes * 2) + i]!)[2*lane+1]!) r
    rw [getElem!_tab _ _ _ hidx, getElem!_tab _ _ _ h0, getElem!_tab _ _ _ h1]
    rw [show 2 * (row * lanes + lane) = row * (lanes * 2) + 2 * lane by ring]
    rw [show row * (lanes * 2) + 2 * lane + 1 =
      row * (lanes * 2) + (2 * lane + 1) by omega]

private theorem foldLow_blocks_list (point : List R) (a : Array R) (width : Nat)
    (ha : a.size = width * 2 ^ point.length) :
    point.foldl foldLow a =
      tab width fun row =>
        Concrete.mle (tab (2 ^ point.length) fun lane => a[row * 2 ^ point.length + lane]!)
          point.toArray := by
  induction point generalizing a with
  | nil =>
    apply Array.ext
    · simpa using ha
    · intro i hi hi'
      have hia : i < a.size := hi
      simp [tab, Concrete.mle, dot_eq_sum,
        TerminalRefinement.eqTable_empty, getElem!_pos, hia]
  | cons r point ih =>
    have hs : a.size = width * (2 ^ point.length * 2) := by
      simpa only [List.length_cons, pow_succ] using ha
    rw [List.foldl_cons, ih (foldLow a r) (by
      simp only [size_foldLow, hs, ← Nat.mul_assoc,
        Nat.mul_div_left _ (by decide : 0 < 2)])]
    apply Array.ext
    · simp
    · intro row hr hr'
      have hrw : row < width := by simpa using hr
      simp only [tab, Array.getElem_map, List.getElem_toArray, List.getElem_range]
      change Concrete.mle
          (tab (2 ^ point.length) fun lane => (foldLow a r)[row * 2 ^ point.length + lane]!)
          point.toArray =
        Concrete.mle
          (tab (2 ^ (r :: point).length) fun lane => a[row * 2 ^ (r :: point).length + lane]!)
          (r :: point).toArray
      rw [foldLow_slice a width (2 ^ point.length) row r hs hrw]
      have hc := TerminalRefinement.mle_cons
        (tab (2 ^ (r :: point).length) fun lane => a[row * 2 ^ (r :: point).length + lane]!)
        point.toArray r (by simp)
      have harr : (r :: point).toArray = #[r] ++ point.toArray := by simp
      rw [harr]
      simpa only [List.length_cons, pow_succ] using hc.symm

/-- Actual repeated low-lane folds, not a replacement mathematical evaluator. -/
theorem foldLow_blocks (a point : Array R) (width : Nat)
    (ha : a.size = width * 2 ^ point.size) :
    point.foldl foldLow a =
      tab width fun row =>
        dot (tab (2 ^ point.size) fun lane => a[row * 2 ^ point.size + lane]!)
          (eqTable point) := by
  rw [← Array.foldl_toList]
  simpa only [Array.length_toList, Array.toArray_toList, Concrete.mle] using
    foldLow_blocks_list point.toList a width (by simpa using ha)

/-- Gathering one column commutes with the actual top-lane fold. -/
theorem foldLane_slice (a : Array R) (width lanes row : Nat) (r : R)
    (ha : a.size = (lanes * 2) * width) (hr : row < width) :
    (tab lanes fun lane => (foldLane a width r)[lane * width + row]!) =
      foldLow (tab (lanes * 2) fun lane => a[lane * width + row]!) r := by
  have half : a.size / 2 = lanes * width := by
    rw [ha, Nat.mul_right_comm, Nat.mul_div_left _ (by decide : 0 < 2)]
  unfold foldLane foldLow
  simp only [size_tab, Nat.mul_div_left _ (by decide : 0 < 2)]
  apply Array.ext
  · simp
  · intro lane hl hr'
    have hl' : lane < lanes := by simpa using hl
    have hidx : lane * width + row < a.size / 2 := by
      rw [half]
      exact Layout.stackIndex_bound hl' hr
    have h0 : 2 * lane < lanes * 2 := by omega
    have h1 : 2 * lane + 1 < lanes * 2 := by omega
    simp only [tab, Array.getElem_map, List.getElem_toArray, List.getElem_range]
    change (tab (a.size / 2) fun i =>
      foldPair a[(i / width) * (2 * width) + i % width]!
        a[(i / width) * (2 * width) + i % width + width]! r)[lane * width + row]! =
      foldPair ((tab (lanes * 2) fun i => a[i * width + row]!)[2*lane]!)
        ((tab (lanes * 2) fun i => a[i * width + row]!)[2*lane+1]!) r
    rw [getElem!_tab _ _ _ hidx, getElem!_tab _ _ _ h0, getElem!_tab _ _ _ h1]
    rw [foldLane_offset hr]
    simp only [Layout.stackIndex]
    rw [show 2 * lane * width + row + width = (2 * lane + 1) * width + row by ring]

private theorem foldLane_blocks_list (point : List R) (a : Array R) (width : Nat)
    (ha : a.size = 2 ^ point.length * width) :
    point.foldl (fun a r => foldLane a width r) a =
      tab width fun row =>
        Concrete.mle (tab (2 ^ point.length) fun lane => a[lane * width + row]!)
          point.toArray := by
  induction point generalizing a with
  | nil =>
    apply Array.ext
    · simpa using ha
    · intro i hi hi'
      have hia : i < a.size := hi
      simp [tab, Concrete.mle, dot_eq_sum,
        TerminalRefinement.eqTable_empty, getElem!_pos, hia]
  | cons r point ih =>
    have hs : a.size = (2 ^ point.length * 2) * width := by
      simpa only [List.length_cons, pow_succ] using ha
    rw [List.foldl_cons, ih (foldLane a width r) (by
      simp only [size_foldLane, hs]
      rw [Nat.mul_right_comm, Nat.mul_div_left _ (by decide : 0 < 2)])]
    apply Array.ext
    · simp
    · intro row hr hr'
      have hrw : row < width := by simpa using hr
      simp only [tab, Array.getElem_map, List.getElem_toArray, List.getElem_range]
      change Concrete.mle
          (tab (2 ^ point.length) fun lane => (foldLane a width r)[lane * width + row]!)
          point.toArray =
        Concrete.mle
          (tab (2 ^ (r :: point).length) fun lane => a[lane * width + row]!)
          (r :: point).toArray
      rw [foldLane_slice a width (2 ^ point.length) row r hs hrw]
      have hc := TerminalRefinement.mle_cons
        (tab (2 ^ (r :: point).length) fun lane => a[lane * width + row]!)
        point.toArray r (by simp)
      have harr : (r :: point).toArray = #[r] ++ point.toArray := by simp
      rw [harr]
      simpa only [List.length_cons, pow_succ] using hc.symm

/-- Actual repeated L0 top-lane folds in the unchanged executable layout. -/
theorem foldLane_blocks (a point : Array R) (width : Nat)
    (ha : a.size = 2 ^ point.size * width) :
    point.foldl (fun a r => foldLane a width r) a =
      tab width fun row =>
        dot (tab (2 ^ point.size) fun lane => a[lane * width + row]!)
          (eqTable point) := by
  rw [← Array.foldl_toList]
  simpa only [Array.length_toList, Array.toArray_toList, Concrete.mle] using
    foldLane_blocks_list point.toList a width (by simpa using ha)

/-- Later authenticated rows imply the exact executable query update on the
folded witness; there is no scalar-correctness premise. -/
theorem enforced_eq_foldLow
    (a : Array R) (width : Nat) (cols rows : Array (Array R)) (rs weights : Array R)
    (shape : a.size = width * 2 ^ rs.size)
    (count : rows.size = cols.size)
    (columnShape : ∀ i < cols.size, cols[i]!.size = width)
    (honest : ∀ i < rows.size, rows[i]! =
      tab (2 ^ rs.size) fun lane =>
        dot (tab width fun j => a[j * 2 ^ rs.size + lane]!) cols[i]!) :
    enforced rows rs weights false =
      dot (rs.foldl foldLow a) (inducedColumns width cols weights) := by
  rw [foldLow_blocks a rs width shape]
  exact enforced_eq_dot_inducedColumns width (2 ^ rs.size)
    (fun lane j => a[j * 2 ^ rs.size + lane]!) cols rows rs weights false
    count columnShape (by simp [TerminalRefinement.size_eqTable]) (by simpa using honest)

theorem dot_tab_zero_tail (full live : Nat) (f : Nat → R) (b : Array R)
    (hl : live ≤ full) (hb : full ≤ b.size)
    (hz : ∀ i, live ≤ i → i < full → f i = 0) :
    dot (tab full f) b = dot (tab live f) b := by
  rw [dot_tab_left full f b hb, dot_tab_left live f b (hl.trans hb)]
  symm
  apply Finset.sum_subset (Finset.range_mono hl)
  intro i hi hn
  rw [hz i (by simpa using hn) (Finset.mem_range.mp hi), zero_mul]

/-- L0 permits a pruned occupied prefix. The actual witness is zero padded;
authenticated descending rows are reversed by `enforced`, not by an oracle
correctness assumption. -/
theorem enforced_eq_foldLane
    (a : Array R) (width live : Nat) (cols rows : Array (Array R)) (rs weights : Array R)
    (shape : a.size = 2 ^ rs.size * width)
    (count : rows.size = cols.size)
    (columnShape : ∀ i < cols.size, cols[i]!.size = width)
    (liveBound : live ≤ 2 ^ rs.size)
    (zeroTail : ∀ lane, live ≤ lane → lane < 2 ^ rs.size →
      ∀ j < width, a[lane * width + j]! = 0)
    (honest : ∀ i < rows.size, (rows[i]!).reverse =
      tab live fun lane => dot (tab width fun j => a[lane * width + j]!) cols[i]!) :
    enforced rows rs weights true =
      dot (rs.foldl (fun a r => foldLane a width r) a) (inducedColumns width cols weights) := by
  rw [foldLane_blocks a rs width shape]
  have htab :
      (tab width fun j => dot (tab (2 ^ rs.size) fun lane => a[lane * width + j]!)
        (eqTable rs)) =
      (tab width fun j => dot (tab live fun lane => a[lane * width + j]!)
        (eqTable rs)) := by
    apply Array.ext
    · simp
    · intro j hj hj'
      have hjw : j < width := by simpa using hj
      simp only [tab, Array.getElem_map, List.getElem_toArray, List.getElem_range]
      exact dot_tab_zero_tail _ _ _ _ liveBound
        (by simp [TerminalRefinement.size_eqTable])
        (fun lane hl hf => zeroTail lane hl hf j hjw)
  rw [htab]
  exact enforced_eq_dot_inducedColumns width live
    (fun lane j => a[lane * width + j]!) cols rows rs weights true
    count columnShape (by simpa [TerminalRefinement.size_eqTable] using liveBound)
    (by simpa using honest)

private theorem normalized_loop_size (xs : List Nat) (roots : Array K)
    (state : Array K × K) :
    (xs.foldl (fun state i =>
      (state.1.push (kmul state.2 (kinv roots[i]!)),
        kmul state.2 (state.2 ^^^ roots[i]!))) state).1.size =
      state.1.size + xs.length := by
  induction xs generalizing state with
  | nil => simp
  | cons i xs ih =>
    simp only [List.foldl_cons, ih, Array.size_push, List.length_cons]
    omega

/-- Dimensions of the actual normalized-subspace loop need no field laws. -/
@[simp] theorem size_normalizedSubspaces (n : Nat) (x : K) :
    (normalizedSubspaces n x).size = n := by
  unfold normalizedSubspaces
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    List.forIn_pure_yield_eq_foldl, pure_bind]
  change ((List.range n).foldl (fun state i =>
    (state.1.push (kmul state.2 (kinv (subspaceRoots n)[i]!)),
      kmul state.2 (state.2 ^^^ (subspaceRoots n)[i]!))) (#[], x)).1.size = n
  rw [normalized_loop_size]
  simp

private theorem column_loop_size (xs : List K) (a : Array E) :
    (xs.foldl (fun out s => out ++ out.map (fun x => x.scale s)) a).size =
      a.size * 2 ^ xs.length := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, Array.size_append, Array.size_map, List.length_cons,
      pow_succ]
    ring

/-- Exact column dimension, independent of the unproved machine field laws. -/
@[simp] theorem size_column (n q : Nat) : (column n q).size = 2 ^ n := by
  unfold column
  simp only [Array.forIn_pure_yield_eq_foldl, pure_bind]
  change ((normalizedSubspaces n (UInt64.ofNat q)).foldl
    (fun out s => out ++ out.map (fun x => x.scale s)) #[E.one]).size = _
  rw [← Array.foldl_toList, column_loop_size]
  simp

@[simp] theorem size_induced (n : Nat) (queries : Array Nat) (weights : Array E) :
    (induced n queries weights).size = 2 ^ n := by
  simp [induced, inducedColumns]

@[simp] theorem size_encodeBase (message : Array K) (logN initialK rate : Nat) :
    (encodeBase message logN initialK rate).size = 2 ^ (logN - initialK + rate) := by
  simp [encodeBase]

@[simp] theorem size_encodeExt (message : Array E) (logN foldK rate : Nat) :
    (encodeExt message logN foldK rate).size = 2 ^ (logN - foldK + rate) := by
  simp [encodeExt]

/-- An algebraic interpretation of the *actual* machine operations. Providing
this structure is the separate machine-field obligation, not a query identity.
Default preservation also makes transport valid for malformed array accesses. -/
structure Representation (R : Type*) [CommRing R] [Inhabited R] where
  map : E → R
  injective : Function.Injective map
  zero : map (0 : E) = 0
  one : map (1 : E) = 1
  add : ∀ a b, map (a + b) = map a + map b
  mul : ∀ a b, map (a * b) = map a * map b
  default : map (default : E) = (default : R)

namespace Representation
variable (ρ : Representation R)

private theorem map_tab {A B : Type*} (f : A → B) (n : Nat) (g : Nat → A) :
    (tab n g).map f = tab n (fun i => f (g i)) := by
  simp [tab, Array.map_map, Function.comp_def]

private theorem map_get {A B : Type*} [Inhabited A] [Inhabited B]
    (f : A → B) (hd : f Inhabited.default = Inhabited.default) (a : Array A) (i : Nat) :
    (a.map f)[i]! = f a[i]! := by
  by_cases hi : i < a.size
  · simp [getElem!_pos, hi]
  · simp [getElem!_neg, hi, hd]

private theorem map_add_fold (a : Array E) (init : E) :
    ρ.map (a.foldl (· + ·) init) = (a.map ρ.map).foldl (· + ·) (ρ.map init) := by
  rw [← Array.foldl_toList, ← Array.foldl_toList, Array.toList_map, List.foldl_map]
  generalize a.toList = xs
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, ih]
    congr 1
    exact ρ.add init x

/-- Transport of the shared dot kernel, including truncation. -/
theorem map_dot (a b : Array E) :
    ρ.map (dot a b) = dot (a.map ρ.map) (b.map ρ.map) := by
  unfold dot
  rw [map_add_fold, ρ.zero, map_tab]
  simp only [Array.size_map]
  apply congrArg (fun g : Nat → R => (tab (min a.size b.size) g).foldl (· + ·) 0)
  funext i
  rw [map_get ρ.map ρ.default, map_get ρ.map ρ.default]
  exact ρ.mul _ _

private theorem map_table_loop (xs : List E) (a : Array E) :
    (xs.foldl (fun out r => out.map (fun x => x * (1 + r)) ++ out.map (fun x => x * r)) a).map ρ.map =
      (xs.map ρ.map).foldl
        (fun out r => out.map (fun x => x * (1 + r)) ++ out.map (fun x => x * r))
        (a.map ρ.map) := by
  induction xs generalizing a with
  | nil => rfl
  | cons r xs ih =>
    simp only [List.foldl_cons, List.map_cons, ih]
    congr 1
    simp only [Array.map_append, Array.map_map, Function.comp_def]
    congr 1 <;> congr 1 <;> funext x
    · exact (ρ.mul x (1 + r)).trans
        (congrArg (ρ.map x * ·) ((ρ.add 1 r).trans (by rw [ρ.one])))
    · exact ρ.mul x r

theorem map_eqTable (point : Array E) :
    (eqTable point).map ρ.map = eqTable (point.map ρ.map) := by
  unfold eqTable
  simp only [Array.forIn_pure_yield_eq_foldl, pure_bind]
  rw [← Array.foldl_toList, ← Array.foldl_toList, Array.toList_map]
  change (point.toList.foldl
    (fun out r => out.map (fun x => x * (1 + r)) ++ out.map (fun x => x * r)) #[1]).map ρ.map =
    (point.toList.map ρ.map).foldl
    (fun out r => out.map (fun x => x * (1 + r)) ++ out.map (fun x => x * r)) #[1]
  rw [map_table_loop]
  simp only [Array.map_singleton, ρ.one]

theorem map_foldPair (a b r : E) :
    ρ.map (foldPair a b r) = foldPair (ρ.map a) (ρ.map b) (ρ.map r) := by
  unfold foldPair
  exact (ρ.add a (r * (a + b))).trans (by
    rw [ρ.mul, ρ.add])

theorem map_foldLow (a : Array E) (r : E) :
    (foldLow a r).map ρ.map = foldLow (a.map ρ.map) (ρ.map r) := by
  unfold foldLow
  rw [map_tab]
  simp only [Array.size_map]
  congr 1
  funext i
  rw [map_foldPair, map_get ρ.map ρ.default, map_get ρ.map ρ.default]

theorem map_foldLane (a : Array E) (width : Nat) (r : E) :
    (foldLane a width r).map ρ.map = foldLane (a.map ρ.map) width (ρ.map r) := by
  unfold foldLane
  rw [map_tab]
  simp only [Array.size_map]
  congr 1
  funext i
  rw [map_foldPair, map_get ρ.map ρ.default, map_get ρ.map ρ.default]

theorem map_inducedColumns (width : Nat) (cols : Array (Array E)) (weights : Array E) :
    (inducedColumns width cols weights).map ρ.map =
      inducedColumns width (cols.map (Array.map ρ.map)) (weights.map ρ.map) := by
  unfold inducedColumns
  rw [map_tab]
  simp only [Array.size_map]
  congr 1
  funext j
  rw [map_add_fold, ρ.zero, map_tab]
  apply congrArg (fun g : Nat → R => (tab cols.size g).foldl (· + ·) 0)
  funext i
  rw [map_get ρ.map ρ.default, map_get (Array.map ρ.map)
    (by change (#[] : Array E).map ρ.map = #[]; simp),
    map_get ρ.map ρ.default]
  exact ρ.mul _ _

theorem map_enforced (rows : Array (Array E)) (rs weights : Array E) (base : Bool) :
    ρ.map (enforced rows rs weights base) =
      enforced (rows.map (Array.map ρ.map)) (rs.map ρ.map) (weights.map ρ.map) base := by
  unfold enforced
  rw [map_add_fold, ρ.zero, map_tab]
  simp only [Array.size_map]
  apply congrArg (fun g : Nat → R => (tab rows.size g).foldl (· + ·) 0)
  funext i
  rw [map_get ρ.map ρ.default]
  rw [ρ.mul, map_dot, map_eqTable, map_get (Array.map ρ.map)
    (by change (#[] : Array E).map ρ.map = #[]; simp)]
  congr 2
  cases base <;> simp [Array.map_reverse]

private theorem map_get_row (rows : Array (Array E)) (i : Nat) :
    (rows.map (Array.map ρ.map))[i]! = (rows[i]!).map ρ.map :=
  map_get _ (by change (#[] : Array E).map ρ.map = #[]; simp) _ _

private theorem map_steps (xs : List E) (a : Array E)
    (step : Array E → E → Array E) (stepR : Array R → R → Array R)
    (hstep : ∀ a r, (step a r).map ρ.map = stepR (a.map ρ.map) (ρ.map r)) :
    (xs.foldl step a).map ρ.map =
      (xs.map ρ.map).foldl stepR (a.map ρ.map) := by
  induction xs generalizing a with
  | nil => rfl
  | cons r xs ih => simp only [List.foldl_cons, List.map_cons, ih, hstep]

theorem map_foldLow_many (a rs : Array E) :
    (rs.foldl foldLow a).map ρ.map =
      (rs.map ρ.map).foldl foldLow (a.map ρ.map) := by
  rw [← Array.foldl_toList, ← Array.foldl_toList, Array.toList_map]
  exact map_steps ρ _ _ _ _ (map_foldLow ρ)

theorem map_foldLane_many (a rs : Array E) (width : Nat) :
    (rs.foldl (fun a r => foldLane a width r) a).map ρ.map =
      (rs.map ρ.map).foldl (fun a r => foldLane a width r) (a.map ρ.map) := by
  rw [← Array.foldl_toList, ← Array.foldl_toList, Array.toList_map]
  exact map_steps ρ _ _ _ _ (fun a r => map_foldLane ρ a width r)

include ρ in
/-- The concrete low-lane query identity, conditional only on an algebraic
interpretation of the real machine operations and honest encoded rows. -/
theorem enforced_eq_foldLow
    (a : Array E) (width : Nat) (cols rows : Array (Array E)) (rs weights : Array E)
    (shape : a.size = width * 2 ^ rs.size)
    (count : rows.size = cols.size)
    (columnShape : ∀ i < cols.size, cols[i]!.size = width)
    (honest : ∀ i < rows.size, rows[i]! =
      tab (2 ^ rs.size) fun lane =>
        dot (tab width fun j => a[j * 2 ^ rs.size + lane]!) cols[i]!) :
    enforced rows rs weights false =
      dot (rs.foldl foldLow a) (inducedColumns width cols weights) := by
  apply ρ.injective
  rw [map_enforced, map_dot, map_foldLow_many, map_inducedColumns]
  apply Whir.QueryRefinement.enforced_eq_foldLow
  · simpa using shape
  · simpa using count
  · intro i hi
    rw [map_get_row, Array.size_map]
    exact columnShape i (by simpa using hi)
  · intro i hi
    have hi' : i < rows.size := by simpa using hi
    rw [map_get_row, honest i hi', map_tab, map_get_row]
    simp only [Array.size_map]
    congr 1
    funext lane
    rw [map_dot, map_tab]
    congr 2
    funext j
    exact (map_get ρ.map ρ.default a _).symm

include ρ in
/-- The concrete L0 identity, with the actual reverse and actual top-lane
folds. Only zero padding, encoded-row formulas and representation laws enter. -/
theorem enforced_eq_foldLane
    (a : Array E) (width live : Nat) (cols rows : Array (Array E)) (rs weights : Array E)
    (shape : a.size = 2 ^ rs.size * width)
    (count : rows.size = cols.size)
    (columnShape : ∀ i < cols.size, cols[i]!.size = width)
    (liveBound : live ≤ 2 ^ rs.size)
    (zeroTail : ∀ lane, live ≤ lane → lane < 2 ^ rs.size →
      ∀ j < width, a[lane * width + j]! = 0)
    (honest : ∀ i < rows.size, (rows[i]!).reverse =
      tab live fun lane => dot (tab width fun j => a[lane * width + j]!) cols[i]!) :
    enforced rows rs weights true =
      dot (rs.foldl (fun a r => foldLane a width r) a) (inducedColumns width cols weights) := by
  apply ρ.injective
  rw [map_enforced, map_dot, map_foldLane_many, map_inducedColumns]
  apply Whir.QueryRefinement.enforced_eq_foldLane _ _ live
  · simpa using shape
  · simpa using count
  · intro i hi
    rw [map_get_row, Array.size_map]
    exact columnShape i (by simpa using hi)
  · simpa using liveBound
  · intro lane hl hf j hj
    rw [map_get ρ.map ρ.default, zeroTail lane hl (by simpa using hf) j hj, ρ.zero]
  · intro i hi
    have hi' : i < rows.size := by simpa using hi
    rw [map_get_row, ← Array.map_reverse, honest i hi', map_tab, map_get_row]
    congr 1
    funext lane
    rw [map_dot, map_tab]
    congr 2
    funext j
    exact (map_get ρ.map ρ.default a _).symm

private theorem get_map_valid {A B : Type*} [Inhabited A] [Inhabited B]
    (f : A → B) (a : Array A) (i : Nat) (hi : i < a.size) :
    (a.map f)[i]! = f a[i]! := by
  simp [getElem!_pos, hi]

include ρ in
/-- Direct actual later-level encoder/query/fold correspondence. The only
algebraic dependency is `ρ`; rows and columns are the executable definitions,
not supplied evaluations or oracle-correctness identities. -/
theorem enforced_encodeExt (a : Array E) (logN foldK rate : Nat)
    (queries : Array Nat) (rs weights : Array E)
    (folds : rs.size = foldK)
    (shape : a.size = 2 ^ (logN - foldK) * 2 ^ foldK)
    (queryBound : ∀ i < queries.size, queries[i]! < 2 ^ (logN - foldK + rate)) :
    enforced (queries.map fun q => (encodeExt a logN foldK rate)[q]!) rs weights false =
      dot (rs.foldl foldLow a) (induced (logN - foldK) queries weights) := by
  apply enforced_eq_foldLow ρ a (2 ^ (logN - foldK)) (queries.map (column (logN - foldK)))
  · simpa only [folds] using shape
  · simp
  · intro i hi
    rw [get_map_valid _ _ _ (by simpa using hi)]
    exact size_column _ _
  · intro i hi
    have hiq : i < queries.size := by simpa using hi
    rw [get_map_valid _ _ _ hiq, encodeExt_row _ _ _ _ _ (queryBound i hiq)]
    simp only [folds]
    rw [get_map_valid _ _ _ hiq]

include ρ in
/-- Direct actual L0 encoder/query/fold correspondence, including a pruned
occupied prefix and the prover's exact `getD 0` padding construction. -/
theorem enforced_encodeBase (message : Array K) (logN initialK rate : Nat)
    (queries : Array Nat) (rs weights : Array E)
    (folds : rs.size = initialK) (foldBound : initialK ≤ logN)
    (shape : message.size =
      (message.size / 2 ^ (logN - initialK)) * 2 ^ (logN - initialK))
    (liveBound : message.size / 2 ^ (logN - initialK) ≤ 2 ^ initialK)
    (queryBound : ∀ i < queries.size,
      queries[i]! < 2 ^ (logN - initialK + rate)) :
    let padded := tab (2 ^ logN) fun i => E.ofK (message[i]?.getD 0)
    enforced (queries.map fun q => (encodeBase message logN initialK rate)[q]!) rs weights true =
      dot (rs.foldl (fun a r => foldLane a (2 ^ (logN - initialK)) r) padded)
        (induced (logN - initialK) queries weights) := by
  dsimp only
  let padded := tab (2 ^ logN) fun i => E.ofK (message[i]?.getD 0)
  have hp : 2 ^ logN = 2 ^ initialK * 2 ^ (logN - initialK) := by
    rw [← pow_add]
    congr 1
    omega
  have hg (i : Nat) (hi : i < 2 ^ logN) :
      padded[i]! = E.ofK message[i]! := by
    rw [getElem!_tab _ _ _ hi]
    by_cases him : i < message.size
    · simp [getElem?_pos, getElem!_pos, him]
    · simp only [getElem?_neg message i him, Option.getD_none, getElem!_neg message i him]
      rfl
  apply enforced_eq_foldLane ρ padded (2 ^ (logN - initialK))
    (message.size / 2 ^ (logN - initialK)) (queries.map (column (logN - initialK)))
  · simpa only [padded, size_tab, folds] using hp
  · simp
  · intro i hi
    rw [get_map_valid _ _ _ (by simpa using hi)]
    exact size_column _ _
  · simpa only [folds] using liveBound
  · intro lane hl hf j hj
    have hidx : lane * 2 ^ (logN - initialK) + j < 2 ^ logN := by
      rw [hp]
      exact Layout.stackIndex_bound (by simpa only [folds] using hf) hj
    rw [getElem!_tab _ _ _ hidx]
    have hn : ¬lane * 2 ^ (logN - initialK) + j < message.size := by
      have hm := Nat.mul_le_mul_right (2 ^ (logN - initialK)) hl
      omega
    simp only [getElem?_neg message (lane * 2 ^ (logN - initialK) + j) hn, Option.getD_none]
    rfl
  · intro i hi
    have hiq : i < queries.size := by simpa using hi
    rw [get_map_valid _ _ _ hiq, encodeBase_row _ _ _ _ _ (queryBound i hiq),
      get_map_valid _ _ _ hiq]
    apply Array.ext
    · simp
    · intro lane hl hr
      have hll : lane < message.size / 2 ^ (logN - initialK) := by simpa using hl
      simp only [tab, Array.getElem_map, List.getElem_toArray, List.getElem_range]
      apply congrArg (fun coeff => dot coeff (column (logN - initialK) queries[i]!))
      apply Array.ext
      · simp
      · intro j hj hj'
        have hjw : j < 2 ^ (logN - initialK) := by simpa using hj
        simp only [Array.getElem_map, List.getElem_toArray, List.getElem_range]
        exact (hg _ (by rw [hp]; exact Layout.stackIndex_bound (hll.trans_le liveBound) hjw)).symm

end Representation

/-- The operation-compatible ring laws proved in `FieldExtension` discharge
the algebraic interpretation boundary without assuming a query identity. -/
def concreteRepresentation : Representation E where
  map := id
  injective := Function.injective_id
  zero := rfl
  one := rfl
  add _ _ := rfl
  mul _ _ := rfl
  default := rfl

/-- Actual later-level query correspondence with no remaining algebraic
premise: the columns and encoded rows are the executable definitions. -/
theorem enforced_encodeExt (a : Array E) (logN foldK rate : Nat)
    (queries : Array Nat) (rs weights : Array E)
    (folds : rs.size = foldK)
    (shape : a.size = 2 ^ (logN - foldK) * 2 ^ foldK)
    (queryBound : ∀ i < queries.size, queries[i]! < 2 ^ (logN - foldK + rate)) :
    enforced (queries.map fun q => (encodeExt a logN foldK rate)[q]!) rs weights false =
      dot (rs.foldl foldLow a) (induced (logN - foldK) queries weights) :=
  Representation.enforced_encodeExt concreteRepresentation a logN foldK rate
    queries rs weights folds shape queryBound

/-- Actual initial query correspondence, including pruned reversed rows and
the exact padded witness construction, with all ring laws discharged. -/
theorem enforced_encodeBase (message : Array K) (logN initialK rate : Nat)
    (queries : Array Nat) (rs weights : Array E)
    (folds : rs.size = initialK) (foldBound : initialK ≤ logN)
    (shape : message.size =
      (message.size / 2 ^ (logN - initialK)) * 2 ^ (logN - initialK))
    (liveBound : message.size / 2 ^ (logN - initialK) ≤ 2 ^ initialK)
    (queryBound : ∀ i < queries.size,
      queries[i]! < 2 ^ (logN - initialK + rate)) :
    let padded := tab (2 ^ logN) fun i => E.ofK (message[i]?.getD 0)
    enforced (queries.map fun q => (encodeBase message logN initialK rate)[q]!) rs weights true =
      dot (rs.foldl (fun a r => foldLane a (2 ^ (logN - initialK)) r) padded)
        (induced (logN - initialK) queries weights) :=
  Representation.enforced_encodeBase concreteRepresentation message logN initialK rate
    queries rs weights folds foldBound shape liveBound queryBound

end Whir.QueryRefinement
