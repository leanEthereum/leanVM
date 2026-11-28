module

public import LeanVM.Guest.Complete.DaPad
public import LeanVM.Guest.Complete.DaLoop
public import LeanVM.Guest.B1.Da.VectorMath

/-!
# The dual codeword's honest words, and its builders' completeness as statements

The words an honest run of `da_vector` and `da_weights` leaves in the buffers and frame runs they
return, as functions of the challenge `z` (restored from the archive's `Da/HonestDefs`, without its
layouts): `zsCells z` (`z^(2^j)`, then `0`), `facCells Z top D` (a `da_factors` buffer),
`expRunVals root F Z S top D` (a `da_expand` frame run: node `n` at word `n`), `offCells Z`
(`da_column_offsets`' buffer), `topRun z` (the tree over the cell index) and `colRun z h` (column
`h`'s tree, its leaves the dual codeword on cell `h`, `colRun_leaf`).

A buffer a callee returns is its caller's words: `DaVectorComplete k` and `DaWeightsComplete k`
state `da_vector`'s and `da_weights`' completeness on memories holding the words they return
(`vecWords`, `wsWords`: the weights table and each column's run), popping nothing.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Da LeanVM.Guest.B1.Digest
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.Value

@[expose] public section

/-! ## The honest words -/

/-- `da_vector`'s `zs`: `z^(2^j)` for `j < 13`, then `0` (`14` words). -/
def zsCells (z : E) : List E := (List.range 14).map (zsVal z)

/-- A `da_factors` buffer: node `n`'s factor for `1 ≤ n < 2^D`, `0` elsewhere (`128` words). -/
def facCells (Z : ℕ → E) (top D : ℕ) : List E :=
  (List.range 128).map fun n => if 1 ≤ n ∧ n < 2 ^ D then factorAt Z top n else 0

/-- A `da_expand` frame run (`256` words): node `n` of its tree at word `n`, `1 ≤ n < 2^(D + 1)`,
zeros elsewhere. -/
def expRunVals (root : E) (F Z S : ℕ → E) (top D : ℕ) : List E :=
  (List.range 256).map fun i =>
    if 1 ≤ i ∧ i < 2 ^ (D + 1) then expandLeaf root F Z S top (Nat.log 2 i) (i - 2 ^ Nat.log 2 i)
    else 0

/-- `da_column_offsets`' buffer: `offsets[7h + j] = Z_j · Ŵ_j(128 h)` (`896` words). -/
def offCells (Z : ℕ → E) : List E :=
  (List.range 896).map fun i => Z (i % 7) * ofK (wK (i % 7) (128 * (i / 7)))

/-- The tree over the cell index: `da_expand__L13_L7` from `1`, no shifts. -/
def topRun (z : E) : List E := expRunVals 1 (factorAt (zsVal z) 13) (zsVal z) (fun _ => 0) 13 7

/-- Column `h`'s shifts: `z_j Ŵ_j(128 h)`. -/
def colShift (z : E) (h : ℕ) : ℕ → E := fun j => zsVal z j * ofK (wK j (128 * h))

/-- Column `h`'s tree: `da_expand__L6_L7` from the top tree's leaf `h`. -/
def colRun (z : E) (h : ℕ) : List E :=
  expRunVals (topLeaf z h) (factorAt (zsVal z) 6) (zsVal z) (colShift z h) 6 7

@[simp] theorem length_zsCells (z : E) : (zsCells z).length = 14 := by simp [zsCells]
@[simp] theorem length_facCells (Z : ℕ → E) (top D : ℕ) : (facCells Z top D).length = 128 := by simp [facCells]
@[simp] theorem length_expRunVals (root : E) (F Z S : ℕ → E) (top D : ℕ) :
    (expRunVals root F Z S top D).length = 256 := by simp [expRunVals]
@[simp] theorem length_offCells (Z : ℕ → E) : (offCells Z).length = 896 := by simp [offCells]
@[simp] theorem length_topRun (z : E) : (topRun z).length = 256 := by simp [topRun]
@[simp] theorem length_colRun (z : E) (h : ℕ) : (colRun z h).length = 256 := by simp [colRun]

theorem expRunVals_leaf (root : E) (F Z S : ℕ → E) (top : ℕ) {e : ℕ} (he : e < 128) :
    (expRunVals root F Z S top 7).getD (128 + e) 0 = expandLeaf root F Z S top 7 e := by
  rw [expRunVals, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range,
    ite_pos' ⟨by omega, by norm_num; omega⟩,
    show 128 + e = 2 ^ 7 + e by rfl, log_two_pow_add (by norm_num; omega), Nat.add_sub_cancel_left]

/-- **Column `h`'s leaves are the dual codeword on cell `h`.** -/
theorem colRun_leaf (z : E) (h : ℕ) {e : ℕ} (he : e < 128) :
    (colRun z h).getD (128 + e) 0 = dualAt z (128 * h + e) := by
  rw [colRun, expRunVals_leaf _ _ _ _ _ he]
  exact cellLeaf_eq z he

/-- **The top tree's leaves are the cells' first points' factors.** -/
theorem topRun_leaf (z : E) {h : ℕ} (hh : h < 128) : (topRun z).getD (128 + h) 0 = topLeaf z h := by
  rw [topRun, expRunVals_leaf _ _ _ _ _ hh, topLeaf_eq z hh]

/-! ## Reading runs -/

/-- A part of a run in memory. -/
theorem readsAt_sub {rd : Reader} {p : E} {xs ys : List E} {o : ℕ} (h : ReadsAt rd p xs)
    (hl : o + ys.length ≤ xs.length) (hv : ∀ i < ys.length, xs.getD (o + i) 0 = ys.getD i 0) :
    ReadsAt rd (p * gen ^ o) ys := by
  intro i hi
  have := h (o + i) (by omega)
  rw [← List.getD_eq_getElem _ 0, hv i hi, List.getD_eq_getElem _ _ hi] at this
  exact (loadHolds_mul_gen_pow rd p o i _).mpr this

theorem holdsWords_cons {rd : Reader} {b : ℕ} {xs : List E} {W : Words} :
    HoldsWords rd ((b, xs) :: W) ↔ ReadsAt rd (gen ^ b) xs ∧ HoldsWords rd W := by
  simp only [HoldsWords, List.mem_cons, forall_eq_or_imp, gen_pow_eq_ofK]

/-! ## The words `da_vector` and `da_weights` return -/

/-- `da_vector`'s returned words: the powers at `g^bz`, the top tree's run at `g^bt`, the cell
tree's factors at `g^bc`, the column offsets at `g^bo`. -/
def vecWords (z : E) (bz bt bc bo : ℕ) : Words :=
  [(bz, zsCells z), (bt, topRun z), (bc, facCells (zsVal z) 6 7), (bo, offCells (zsVal z))]

/-- `da_vector`'s returns: pointers to its words, the top tree's at its leaves. -/
def vecRets (bz bt bc bo : ℕ) : List E := [gen ^ bz, gen ^ (bt + 128), gen ^ bc, gen ^ bo]

/-- The weights table: column `h`'s pointer, its run's leaves. -/
def wsTable (bcol : ℕ → ℕ) : List E := (List.range 128).map fun h => gen ^ (bcol h + 128)

/-- `da_weights`' returned words: the table at `g^bw` and column `h`'s run at `g^(bcol h)`. -/
def wsWords (z : E) (bw : ℕ) (bcol : ℕ → ℕ) : Words :=
  (bw, wsTable bcol) :: (List.range 128).map fun h => (bcol h, colRun z h)

/-- **`da_vector` completes** on memories holding the words it returns, popping nothing. -/
def DaVectorComplete (k : ℕ) : Prop :=
  ∀ (z : E) (bz bt bc bo : ℕ), CallCompletes k "da_vector" [z] (vecRets bz bt bc bo)
    (fun rd => HoldsWords rd (vecWords z bz bt bc bo)) FreePost

/-- **`da_weights` completes** on memories holding `da_vector`'s words and the ones it returns,
popping nothing. -/
def DaWeightsComplete (k : ℕ) : Prop :=
  ∀ (z : E) (bz bt bc bo bw : ℕ) (bcol : ℕ → ℕ),
    CallCompletes k "da_weights" [gen ^ (bt + 128), gen ^ bc, gen ^ bz, gen ^ bo] [gen ^ bw]
      (fun rd => HoldsWords rd (vecWords z bz bt bc bo) ∧ HoldsWords rd (wsWords z bw bcol)) FreePost

/-- **The weights table's words are the weights.** -/
theorem weightsHold_of {rd : Reader} {z : E} {bw : ℕ} {bcol : ℕ → ℕ} (h : HoldsWords rd (wsWords z bw bcol)) :
    WeightsHold rd z (gen ^ bw) := by
  rw [wsWords, holdsWords_cons] at h
  intro c hc
  refine ⟨gen ^ (bcol c + 128), ?_, ?_⟩
  · have := h.1 c (by simp [wsTable]; omega)
    rw [loadHolds_mul_gen_pow, Nat.add_zero]
    simpa [wsTable] using this
  · have hr : ReadsAt rd (gen ^ bcol c) (colRun z c) := by
      have := h.2 (bcol c, colRun z c) (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)
      rwa [← gen_pow_eq_ofK] at this
    rw [pow_add]
    refine readsAt_sub hr (by simp [colWs]) fun i hi => ?_
    simp only [colWs, List.length_map, List.length_range] at hi
    rw [colRun_leaf z c hi, colWs, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map,
      List.getElem_range]

end
end LeanVM.Guest.Complete
