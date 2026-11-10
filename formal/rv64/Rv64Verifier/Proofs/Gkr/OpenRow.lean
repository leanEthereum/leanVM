import Rv64Verifier.Model.KeccakGkr

/-!
# `open`'s row, loop by loop

`openRow` (`Model/KeccakGkr.lean`) is three nested folds: segments, the weights' chunks of 64 (a
lane each), the positions of a chunk. The compiled loops run them one step at a time; `outRow g`,
`midRow g l` and `inRow g l z` are the row after `g` segments, `l` more chunks and `z` more
positions, with the step equations the loop invariants need.
-/

namespace Rv64Verifier.Gkr.Open
open LeanVM.Parameters Rv64Verifier.Model.Gkr

variable (SG SL W : List E) (first : Nat)

/-- The `l`-th chunk of 64 weights. -/
def chunk (l : Nat) : List E := (W.drop (64 * l)).take 64

/-- One position: `row[z] += SG[g] * SL[25 (first + g) + l] * cl[z]`. -/
def zf (g : Nat) (cl : List E × Nat) (row : List E) (z : Nat) : List E :=
  row.set z (row.getD z 0 + SG.getD g 0 * SL.getD (25 * (first + g) + cl.2) 0 * cl.1.getD z 0)

/-- One chunk. -/
def cf (g : Nat) (row : List E) (cl : List E × Nat) : List E :=
  (List.range (min 64 cl.1.length)).foldl (zf SG SL first g cl) row

/-- One segment. -/
def sf (row : List E) (g : Nat) : List E := (chunks 64 W).zipIdx.foldl (cf SG SL first g) row

theorem openRow_eq (count : Nat) :
    openRow SG SL W first count = (List.range count).foldl (sf SG SL W first) (List.replicate 64 0) :=
  rfl

def outRow (g : Nat) : List E := (List.range g).foldl (sf SG SL W first) (List.replicate 64 0)

def midRow (g l : Nat) : List E :=
  ((chunks 64 W).zipIdx.take l).foldl (cf SG SL first g) (outRow SG SL W first g)

def inRow (g l z : Nat) : List E :=
  (List.range z).foldl (zf SG SL first g (chunk W l, l)) (midRow SG SL W first g l)

theorem outRow_succ (g : Nat) :
    outRow SG SL W first (g + 1) = sf SG SL W first (outRow SG SL W first g) g := by
  simp only [outRow, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem midRow_zero (g : Nat) : midRow SG SL W first g 0 = outRow SG SL W first g := by
  simp [midRow]

theorem chunks_length : (chunks 64 W).length = (W.length + 63) / 64 := by
  simp [chunks]

theorem midRow_full (g : Nat) :
    midRow SG SL W first g ((W.length + 63) / 64) = outRow SG SL W first (g + 1) := by
  rw [outRow_succ, midRow, ← chunks_length, List.take_of_length_le (by simp)]
  rfl

theorem chunks_getElem {l : Nat} (h : l < (chunks 64 W).length) :
    (chunks 64 W)[l] = chunk W l := by
  simp [chunks, chunk]

theorem midRow_succ (g : Nat) {l : Nat} (hl : 64 * l < W.length) :
    midRow SG SL W first g (l + 1) = cf SG SL first g (midRow SG SL W first g l) (chunk W l, l) := by
  have hl' : l < (chunks 64 W).zipIdx.length := by
    simp only [List.length_zipIdx, chunks_length]; omega
  rw [midRow, List.take_succ_eq_append_getElem hl', List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, List.getElem_zipIdx, Nat.zero_add]
  rw [chunks_getElem _ (by simpa using hl')]
  rfl

theorem inRow_zero (g l : Nat) : inRow SG SL W first g l 0 = midRow SG SL W first g l := by
  simp [inRow]

theorem inRow_succ (g l z : Nat) :
    inRow SG SL W first g l (z + 1) =
      zf SG SL first g (chunk W l, l) (inRow SG SL W first g l z) z := by
  simp only [inRow, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem chunk_length (l : Nat) : (chunk W l).length = min 64 (W.length - 64 * l) := by
  simp [chunk]

theorem inRow_full (g : Nat) {l : Nat} (hl : 64 * l < W.length) :
    inRow SG SL W first g l (min 64 (W.length - 64 * l)) = midRow SG SL W first g (l + 1) := by
  rw [midRow_succ _ _ _ _ _ hl, inRow, cf, chunk_length, Nat.min_eq_right (Nat.min_le_left _ _)]

theorem chunk_getD (l : Nat) {z : Nat} (hz : z < min 64 (W.length - 64 * l)) :
    (chunk W l).getD z 0 = W.getD (64 * l + z) 0 := by
  simp only [chunk, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  rw [ite_eq_left (by omega)]

theorem zf_length (g : Nat) (cl : List E × Nat) (row : List E) (z : Nat) :
    (zf SG SL first g cl row z).length = row.length := by
  simp [zf]

theorem foldl_zf_length (g : Nat) (cl : List E × Nat) :
    ∀ (zs : List Nat) (row : List E), (zs.foldl (zf SG SL first g cl) row).length = row.length
  | [], _ => rfl
  | z :: zs, row => by
    rw [List.foldl_cons, foldl_zf_length g cl zs, zf_length]

theorem cf_length (g : Nat) (row : List E) (cl : List E × Nat) :
    (cf SG SL first g row cl).length = row.length :=
  foldl_zf_length SG SL first g cl _ row

theorem foldl_cf_length (g : Nat) :
    ∀ (cls : List (List E × Nat)) (row : List E), (cls.foldl (cf SG SL first g) row).length = row.length
  | [], _ => rfl
  | cl :: cls, row => by
    rw [List.foldl_cons, foldl_cf_length g cls, cf_length]

theorem foldl_sf_length :
    ∀ (gs : List Nat) (row : List E), (gs.foldl (sf SG SL W first) row).length = row.length
  | [], _ => rfl
  | g :: gs, row => by
    rw [List.foldl_cons, foldl_sf_length gs, sf, foldl_cf_length]

theorem outRow_length (g : Nat) : (outRow SG SL W first g).length = 64 := by
  rw [outRow, foldl_sf_length]; simp

theorem midRow_length (g l : Nat) : (midRow SG SL W first g l).length = 64 := by
  rw [midRow, foldl_cf_length, outRow_length]

theorem inRow_length (g l z : Nat) : (inRow SG SL W first g l z).length = 64 := by
  rw [inRow, foldl_zf_length, midRow_length]

/-- With no weights, every segment leaves the row as it is. -/
theorem openRow_nil (count : Nat) : openRow SG SL [] first count = List.replicate 64 0 := by
  rw [openRow_eq]
  induction count with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    rfl

theorem openRow_zero : openRow SG SL W first 0 = List.replicate 64 0 := rfl

theorem openRow_outRow (count : Nat) :
    openRow SG SL W first count = outRow SG SL W first count := rfl

end Rv64Verifier.Gkr.Open
