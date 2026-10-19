/-
  LeanVM.Guest.B1.Tables.GkrOwn

  `verify_bus_gkr`'s five `HeapBuf`s holding an honest trace's words, and the words a memory
  holding them loads.
-/

module

public import LeanVM.Guest.B1.Tables.GkrTrace
public import LeanVM.Guest.B1.Tables.GkrCompleteBody
public import LeanVM.Guest.B1.Tables.GkrIteAt

/-!
# The honest buffers

`layers` holds each visited layer's eight slots (`gLay`; layer `0` apart, `gLay0`, when the odd
layer runs), `rounds` each pair's round states (`gRnd`), `gkr_pts` each step's point in a row of
`40` (`gRow`), and the two exponent tables `vbgPb`, `vbgDs`. `gkrMem_of`: a memory reading them
loads what `GkrMem` says.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory

@[expose] public section

/-- Pair `i`'s layer slots. -/
noncomputable def gLay (T : GkrTrace) (sh : ℕ) (cur pts : E) (i : ℕ) : List E :=
  [(digestScalars (T.C i)).1, (digestScalars (T.C i)).2, cur * gen ^ gCur sh i,
    (T.P i).values.getD 0 0, (T.P i).values.getD 1 0, (T.P i).values.getD 2 0,
    pts * gen ^ (40 * (sh + i)), gen ^ gPos sh i]

/-- Layer `0`'s slots. -/
noncomputable def gLay0 (T : GkrTrace) (cv : Digest) (cur pts : E) : List E :=
  [(digestScalars (obsCv (obsCv cv T.x0) T.cnt)).1, (digestScalars (obsCv (obsCv cv T.x0) T.cnt)).2,
    cur * gen ^ 2, T.x0, T.x0, T.cnt, pts, gen ^ 0]

/-- `layers`. -/
noncomputable def gLayW (T : GkrTrace) (μ : ℕ) (cv : Digest) (cur pts : E) : List E :=
  (if μ % 2 = 1 then gLay0 T cv cur pts else []) ++
    (List.range (μ / 2 + 1)).flatMap fun i => gLay T (μ % 2) cur pts i ++ List.replicate 8 0

/-- Pair `i`'s round `r` state. -/
noncomputable def gRnd (T : GkrTrace) (sh : ℕ) (cur : E) (i r : ℕ) : List E :=
  [(digestScalars (T.CVR i r)).1, (digestScalars (T.CVR i r)).2, cur * gen ^ gCur sh i * gen ^ (4 * r),
    T.CL i r]

/-- `rounds`. -/
noncomputable def gRndW (T : GkrTrace) (μ : ℕ) (cur : E) : List E :=
  List.replicate (4 * (μ % 2)) 0 ++
    (List.range (μ / 2)).flatMap fun i => (List.range (gL (μ % 2) i + 1)).flatMap (gRnd T (μ % 2) cur i)

/-- A point's row. -/
def gRow (s : GkrState) : List E := (List.range 40).map (s.point.getD · 0)

/-- `gkr_pts`. -/
def gPtsW (T : GkrTrace) (μ : ℕ) : List E :=
  List.replicate (40 * (μ % 2)) 0 ++ (List.range (μ / 2 + 1)).flatMap fun i => gRow (T.P i)

/-- The buffers' sizes. -/
def gkrSizes (μ : ℕ) : List ℕ := [8 * (μ + 2), 3448, 1640, 33, 33]

/-- The buffers' words. -/
noncomputable def gkrOwn (T : GkrTrace) (μ : ℕ) (cv : Digest) (cur pts : E) : List (List E) :=
  [gLayW T μ cv cur pts, gRndW T μ cur, gPtsW T μ, vbgPb, vbgDs]

theorem gkrBases (μ b : ℕ) : bases b (gkrSizes μ) =
    [b, b + 8 * (μ + 2), b + 8 * (μ + 2) + 3448, b + 8 * (μ + 2) + 3448 + 1640,
      b + 8 * (μ + 2) + 3448 + 1640 + 33] := rfl

/-! ## Lengths -/

theorem length_flatMap_range_succ (F : ℕ → List E) (i : ℕ) :
    ((List.range (i + 1)).flatMap F).length = ((List.range i).flatMap F).length + (F i).length := by
  rw [List.range_succ, List.flatMap_append]; simp

theorem length_flatMap_range_const {F : ℕ → List E} {w : ℕ} (hF : ∀ j, (F j).length = w) :
    ∀ i, ((List.range i).flatMap F).length = w * i
  | 0 => by simp
  | i + 1 => by rw [length_flatMap_range_succ, length_flatMap_range_const hF i, hF]; ring

theorem gPos_eq (sh : ℕ) : ∀ i, gPos sh i = sh + i * i + i * sh
  | 0 => by simp [gPos]
  | i + 1 => by rw [gPos, gPos_eq sh i, gL]; ring

theorem gRnd_length (T : GkrTrace) (sh : ℕ) (cur : E) (i r : ℕ) : (gRnd T sh cur i r).length = 4 := rfl

theorem gRnds_length (T : GkrTrace) (sh : ℕ) (cur : E) :
    ∀ i, ((List.range i).flatMap fun i => (List.range (gL sh i + 1)).flatMap (gRnd T sh cur i)).length =
      4 * (gPos sh i - sh)
  | 0 => by simp [gPos]
  | i + 1 => by
    rw [length_flatMap_range_succ, gRnds_length T sh cur i,
      length_flatMap_range_const (gRnd_length T sh cur i), gPos_eq, gPos_eq, gL]
    have : sh + (i + 1) * (i + 1) + (i + 1) * sh - sh = (sh + i * i + i * sh - sh) + (2 * i + sh + 1) := by
      have e1 : (i + 1) * (i + 1) = i * i + 2 * i + 1 := by ring
      have e2 : (i + 1) * sh = i * sh + sh := by ring
      rw [e1, e2]; omega
    rw [this]; ring

theorem gkrOwn_fit (T : GkrTrace) {μ : ℕ} (hμ : μ < 33) (cv : Digest) (cur pts : E) :
    List.Forall₂ (fun c s => c.length ≤ s) (gkrOwn T μ cv cur pts) (gkrSizes μ) := by
  have hl : ∀ i, (gLay T (μ % 2) cur pts i ++ List.replicate 8 0).length = 16 := fun i => rfl
  have hr : ∀ i, (gRow (T.P i)).length = 40 := fun i => by simp [gRow]
  simp only [gkrOwn, gkrSizes, List.forall₂_cons, List.Forall₂.nil, and_true]
  refine ⟨?_, ?_, ?_, by decide, by decide⟩
  · rw [gLayW, List.length_append, length_flatMap_range_const hl]
    rcases Nat.mod_two_eq_zero_or_one μ with h | h <;> simp [h, gLay0] <;> omega
  · rw [gRndW, List.length_append, gRnds_length, List.length_replicate, gPos_eq]
    have : μ / 2 * (μ / 2) ≤ 16 * 16 := Nat.mul_le_mul (by omega) (by omega)
    have : μ / 2 * (μ % 2) ≤ 16 := by
      rcases Nat.mod_two_eq_zero_or_one μ with h | h <;> rw [h] <;> omega
    omega
  · rw [gPtsW, List.length_append, length_flatMap_range_const hr, List.length_replicate]
    omega

/-! ## Loads -/

theorem readsAt_flatMap_block {rd : Reader} {p : E} {F : ℕ → List E} {n i : ℕ}
    (h : ReadsAt rd p ((List.range n).flatMap F)) (hi : i < n) :
    ReadsAt rd (p * gen ^ ((List.range i).flatMap F).length) (F i) := by
  have e : (List.range n).flatMap F = (List.range i).flatMap F ++
      (F i ++ ((List.range (n - (i + 1))).map (i + 1 + ·)).flatMap F) := by
    rw [show n = i + 1 + (n - (i + 1)) by omega, List.range_add, List.range_succ, List.flatMap_append,
      List.flatMap_append]
    simp [List.append_assoc]
  rw [e] at h
  exact (readsAt_split (readsAt_split h).2).1

theorem readsAt_getD {rd : Reader} {p : E} {l : List E} (h : ReadsAt rd p l) {k : ℕ} (hk : k < l.length) :
    LoadHolds rd p k (l.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

theorem loadHolds_shift {rd : Reader} {p v : E} {a k n : ℕ} (h : LoadHolds rd (p * gen ^ a) k v)
    (hn : a + k = n) : LoadHolds rd p n v := by
  rw [← hn]; exact loadHolds_gen_pow_mul.mp h

theorem gk_getD_map_range (f : ℕ → E) {n k : ℕ} (hk : k < n) : ((List.range n).map f).getD k 0 = f k := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]; simp

/-- **What the buffers' memory loads.** -/
structure GkrMem (rd : Reader) (T : GkrTrace) (μ : ℕ) (cv : Digest) (cur layers rounds pts pb dsb : E) :
    Prop where
  pb : ∀ k < 33, LoadHolds rd pb k (vbgPb.getD k 0)
  ds : ∀ k < 33, LoadHolds rd dsb k (vbgDs.getD k 0)
  lay0 : μ % 2 = 1 → ∀ k < 8, LoadHolds rd layers k ((gLay0 T cv cur pts).getD k 0)
  lay : ∀ i ≤ μ / 2, ∀ k < 8, LoadHolds rd layers (8 * gL (μ % 2) i + k) ((gLay T (μ % 2) cur pts i).getD k 0)
  rnd : ∀ i < μ / 2, ∀ r ≤ gL (μ % 2) i, ∀ k < 4,
    LoadHolds rd rounds (4 * (gPos (μ % 2) i + r) + k) ((gRnd T (μ % 2) cur i r).getD k 0)
  row : ∀ i ≤ μ / 2, ∀ j < 40, LoadHolds rd pts (40 * (μ % 2 + i) + j) ((T.P i).point.getD j 0)

theorem gkrMem_of {rd : Reader} {T : GkrTrace} {μ : ℕ} {cv : Digest} {cur layers rounds pts pb dsb : E}
    (hL : ReadsAt rd layers (gLayW T μ cv cur pts)) (hR : ReadsAt rd rounds (gRndW T μ cur))
    (hP : ReadsAt rd pts (gPtsW T μ)) (hB : ReadsAt rd pb vbgPb) (hD : ReadsAt rd dsb vbgDs) :
    GkrMem rd T μ cv cur layers rounds pts pb dsb := by
  have hl : ∀ i, (gLay T (μ % 2) cur pts i ++ List.replicate 8 0).length = 16 := fun i => rfl
  have hr : ∀ i, (gRow (T.P i)).length = 40 := fun i => by simp [gRow]
  have hsh : μ % 2 = 0 ∨ μ % 2 = 1 := Nat.mod_two_eq_zero_or_one μ
  refine ⟨fun k hk => readsAt_getD hB (by simpa [vbgPb] using hk),
    fun k hk => readsAt_getD hD (by simpa [vbgDs] using hk), fun h k hk => ?_, fun i hi k hk => ?_,
    fun i hi r hr' k hk => ?_, fun i hi j hj => ?_⟩
  · rw [gLayW, ite_pos' h] at hL
    exact readsAt_getD (readsAt_split hL).1 (by simpa [gLay0] using hk)
  · rw [gLayW] at hL
    have hb := readsAt_flatMap_block (readsAt_split hL).2 (Nat.lt_succ_of_le hi)
    have := readsAt_getD (readsAt_split hb).1 (k := k) (by simpa [gLay] using hk)
    rw [length_flatMap_range_const hl, mul_assoc, ← pow_add] at this
    refine loadHolds_shift this ?_
    rcases hsh with h | h <;> simp [h, gL, gLay0] <;> omega
  · rw [gRndW] at hR
    have hb := readsAt_flatMap_block (readsAt_split hR).2 hi
    have hb2 := readsAt_flatMap_block hb (Nat.lt_succ_of_le hr')
    have := readsAt_getD hb2 (k := k) (by rw [gRnd_length]; exact hk)
    rw [length_flatMap_range_const (gRnd_length T _ cur i), gRnds_length, mul_assoc, ← pow_add,
      mul_assoc, ← pow_add] at this
    refine loadHolds_shift this ?_
    have := gPos_eq (μ % 2) i
    simp only [List.length_replicate]
    rcases hsh with h | h <;> rw [h] at this ⊢ <;> omega
  · rw [gPtsW] at hP
    have hb := readsAt_flatMap_block (readsAt_split hP).2 (Nat.lt_succ_of_le hi)
    have := readsAt_getD hb (k := j) (by rw [hr]; exact hj)
    rw [length_flatMap_range_const hr, mul_assoc, ← pow_add, gRow, gk_getD_map_range _ hj] at this
    refine loadHolds_shift this ?_
    simp only [List.length_replicate]; ring

end
end LeanVM.Guest.B1.VerifySub
