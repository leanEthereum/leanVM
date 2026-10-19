/-
  LeanVM.Guest.B1.Main.HonestOk

  The pieces of `MainWordsOk` for `main`'s honest words: the bounds within the deployed limits,
  the buffers' sizes, the words the tables, the coverage marks and the exponent tables hold.
-/

module

public import LeanVM.Guest.B1.Main.HonestCounts
public import LeanVM.Guest.B1.Sig.XmssIff
public import LeanVM.Guest.B1.Digest.ClaimBytes

/-!
# `main`'s honest words, checked

The bounds (`honest_bounds`) and sizes (`honest_lens`) from `Limits` and `NodeRel`'s shapes; the
words a memory holding `mainIn` holds (`hon_reads`, `hon_cell`): a table's entry at a slot
(`reads_table`), a region's marks (`cellL_covX`, …), the squares table (`squaresAt_of_mainIn`);
claims' cells and their bytes (`xCellsOf_bytes`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Hints (direct)
open LeanVM.Guest.End (Limits coverage)
open LeanVM.Guest.B1 (LowDef)
open LeanVM.Guest.B1.Digest (SquaresAt CellsAt)

@[expose] public section

/-! ## Lists of fixed-size blocks -/

theorem length_flatMap_const {β γ : Type} (f : γ → List β) (k : ℕ) :
    ∀ (L : List γ), (∀ x ∈ L, (f x).length = k) → (L.flatMap f).length = k * L.length
  | [], _ => by simp
  | x :: L, h => by
    rw [List.flatMap_cons, List.length_append, h x List.mem_cons_self,
      length_flatMap_const f k L fun y hy => h y (List.mem_cons_of_mem _ hy)]
    simp; ring

theorem cellL_of_mem {L : Layout} {b : ℕ} {xs : List E} (hq : (b, xs) ∈ L) (k : ℕ)
    (hk : k < xs.length) {v : E} (hv : xs[k] = v) : CellL L (b + k) v :=
  ⟨b, xs, hq, by omega, by simp only [Nat.add_sub_cancel_left]; exact hk, by simpa using hv⟩

theorem cellL_of_getD {L : Layout} {b : ℕ} {xs : List E} (hq : (b, xs) ∈ L) (k : ℕ)
    (hk : k < xs.length) {v : E} (hv : xs.getD k 0 = v) : CellL L (b + k) v :=
  cellL_of_mem hq k hk (by rw [List.getD_eq_getElem _ _ hk] at hv; exact hv)

/-! ## Claims' cells -/

theorem xCellsOf_length (c : XmssClaim) : (xCellsOf c).length = 4 := by simp [xCellsOf]

theorem sCellsOf_length (c : SphincsClaim) : (sCellsOf c).length = 4 := by simp [sCellsOf]

theorem cellBytes_cellOf' (v : BitVec 128) : cellBytes (Sig.cellOf v) = bytes16 v := by
  rw [← Sig.bytesLE_cellVal, Sig.cellVal_cellOf]; rfl

theorem claimCells_bytes (r p : BitVec 128) (m : BitVec 256) :
    (List.ofFn (LeanVM.Guest.B1.claimCells r p m)).flatMap cellBytes = claimBytes r p m := by
  simp only [List.ofFn_succ, List.ofFn_zero, LeanVM.Guest.B1.claimCells, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, claimBytes]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, cellBytes_cellOf', List.append_assoc, LeanVM.Guest.B1.Digest.bytesLE_32]

theorem xCellsOf_bytes (cs : List XmssClaim) :
    (cs.flatMap xCellsOf).flatMap cellBytes = cs.flatMap fun c => claimBytes c.1.root c.1.parameter c.2 := by
  rw [List.flatMap_assoc]
  exact List.flatMap_congr fun c _ => claimCells_bytes _ _ _

theorem sCellsOf_bytes (cs : List SphincsClaim) :
    (cs.flatMap sCellsOf).flatMap cellBytes = cs.flatMap fun c => claimBytes c.1.root c.1.parameter c.2 := by
  rw [List.flatMap_assoc]
  exact List.flatMap_congr fun c _ => claimCells_bytes _ _ _

theorem claimCells_canonical (r p : BitVec 128) (m : BitVec 256) :
    ∀ c ∈ List.ofFn (LeanVM.Guest.B1.claimCells r p m), IsCanonical128 c := by
  intro c hc
  simp only [List.ofFn_succ, List.ofFn_zero, List.mem_cons, List.not_mem_nil, or_false,
    LeanVM.Guest.B1.claimCells] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact Sig.isCanonical128_cellOf _

theorem xCellsOf_canonical (cs : List XmssClaim) : ∀ c ∈ cs.flatMap xCellsOf, IsCanonical128 c := by
  intro c hc
  obtain ⟨a, -, ha⟩ := List.mem_flatMap.mp hc
  exact claimCells_canonical _ _ _ c ha

theorem sCellsOf_canonical (cs : List SphincsClaim) : ∀ c ∈ cs.flatMap sCellsOf, IsCanonical128 c := by
  intro c hc
  obtain ⟨a, -, ha⟩ := List.mem_flatMap.mp hc
  exact claimCells_canonical _ _ _ c ha

/-! ## Shapes -/

theorem fixedCells_length {c : FixedClaims} (h : FreshShaped c) : (fixedCells c).length = 106 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp [fixedCells, h1, h2, h3, h4]

theorem defer_cells_length {bytecode : List K} (hb : bytecode.length = 2 ^ 22) {d : DeferredClaim}
    (h : d.Shaped bytecode) : d.cells.length = 53 := by
  obtain ⟨h1, h2⟩ := h
  rw [hb, Nat.log2_two_pow] at h1
  simp [DeferredClaim.cells, h1, h2, blake2sR1csLogSize]

/-! ## The bounds -/

section Bounds

variable {seed : Digest} {s : NodeStatement} {w : NodeWitness}

theorem honest_total (hlim : Limits s w) : (honestWords seed s w).total < 2 ^ 16 := by
  have := hlim.coverage
  rw [coverage_eq] at this
  simpa [MainWords.total, honestWords] using this

theorem honest_rx_le (hlim : Limits s w) : hrx s w ≤ s.claims.xmss.length + (planX s w).2.length := by
  have h1 := writersX_length hlim
  rw [writersX_len] at h1
  omega

theorem honest_rs_le (hlim : Limits s w) :
    hrs s w ≤ s.claims.sphincs.length + (planS s w).2.length := by
  have h1 := writersS_length hlim
  rw [writersS_len] at h1
  omega

theorem honest_rd_le (hlim : Limits s w) : hrd s w ≤ s.claims.da.length + (planD s w).2.length := by
  have h1 := writersD_length hlim
  rw [writersD_len] at h1
  omega

theorem honest_dau (hlim : Limits s w) : s.claims.da.length + (planD s w).2.length ≤ 257 := by
  have := writersD_le hlim
  rw [writersD_length hlim] at this
  exact this

end Bounds

end
end LeanVM.Guest.B1.Main
