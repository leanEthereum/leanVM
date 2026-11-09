/-
  LeanVM.Guest.B1.Da.Witness

  A LeanDA witness as `da_verify`'s honest data: its rows' cells, their orthogonality to the dual
  codeword cell by cell, and the root it opens as the tree `da_verify` builds.

  The witness and `Da.MatrixWitness.Opens` are Benedikt Wagner's LeanDA formalization, as ported here.
-/

module

public import LeanVM.Guest.B1.Da.VerifyMath
public import LeanVM.Guest.B1.Da.RowShapeComplete
public import LeanVM.Protocol.KeccakHash

/-!
# A witness, cell by cell

`wSyms w i j`: cell `j` of codeword `i` (`LeanDa.listCell`), padded outside the matrix; `wLog w`:
the padded count's log. `witness_eq`: the witness is `⟨daRows r (wSyms w)⟩`; `wDot`: each row is
orthogonal to the dual codeword of `z`, cell by cell; `opens_eq`: the root it opens is
`daRoot r (wLog w) (wSyms w)`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

/-- A witness's cells: cell `j` of codeword `i`, padded outside the matrix. -/
def wSyms (w : LeanVM.Da.MatrixWitness) (i j : ℕ) : List K :=
  if i < w.rows.length ∧ j < 128 then LeanDa.listCell (w.rows.getD i []) j else List.replicate 256 0

/-- The padded count's log. -/
def wLog (w : LeanVM.Da.MatrixWitness) : ℕ := LeanDa.logPaddedRowCount w.rows.length

/-- A list of `128` blocks of `256` is the flattening of its blocks. -/
theorem flatMap_blocks {α : Type} (l : List α) (d : α) (hl : l.length = 128 * 256) (f : ℕ → List α)
    (hf : ∀ j, (f j).length = 256) (hfj : ∀ j < 128, f j = (l.drop (256 * j)).take 256) :
    (List.range 128).flatMap f = l := by
  have hlen := length_flatMap_range f 256 128 hf
  refine List.ext_getElem (by rw [hlen, hl]) fun k h1 h2 => ?_
  have hk : k = 256 * (k / 256) + k % 256 := by omega
  rw [← List.getD_eq_getElem _ d h1, ← List.getD_eq_getElem _ d h2]
  conv_lhs => rw [hk]
  rw [flatMap_getD f 256 hf d 128 (k / 256) (k % 256) (by omega) (by omega), hfj _ (by omega)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  rw [ite_pos' (by omega)]
  congr 2
  omega

theorem wSyms_length (w : LeanVM.Da.MatrixWitness)
    (hrow : ∀ row ∈ w.rows, row.length = 2 ^ LeanDa.logM) (i j : ℕ) : (wSyms w i j).length = 256 := by
  unfold wSyms
  split
  · rename_i h
    have hl := hrow (w.rows.getD i []) (by rw [List.getD_eq_getElem _ _ h.1]; exact List.getElem_mem _)
    rw [LeanDa.listCell, LeanDa.cellSymbols, List.length_take, List.length_drop, hl]
    simp only [LeanDa.logM]
    omega
  · rw [List.length_replicate]

/-- **A witness is its cells.** -/
theorem witness_eq {w : LeanVM.Da.MatrixWitness} {root : Digest} {z : E} (hw : w.Opens root z) :
    w = ⟨daRows w.rows.length (wSyms w)⟩ := by
  obtain ⟨-, -, hrow, -, -⟩ := hw
  obtain ⟨rows⟩ := w
  simp only at hrow ⊢
  congr 1
  refine List.ext_getElem (by simp [daRows]) fun i h1 h2 => ?_
  simp only [daRows, List.getElem_map, List.getElem_range]
  have hl := hrow _ (List.getElem_mem h1)
  simp only [LeanDa.logM] at hl
  refine (flatMap_blocks rows[i] 0 (by rw [hl]; norm_num) _ (wSyms_length ⟨rows⟩ hrow i)
    fun j hj => ?_).symm
  simp only [wSyms, h1, hj, and_self, ite_true, LeanDa.listCell, LeanDa.cellSymbols,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some, mul_comm j 256]

theorem toBytes_inj {d d' : Digest}
    (h : LeanVM.Protocol.Digest.toBytes d = LeanVM.Protocol.Digest.toBytes d') : d = d' := by
  apply LeanVM.Protocol.KeccakHash.digestBytes_injective
  have := congrArg (fun x : Common.DigestBytes => x.toList) h
  simpa [LeanVM.Protocol.Digest.toBytes] using this

theorem wSyms_len {w : LeanVM.Da.MatrixWitness} {root : Digest} {z : E} (hw : w.Opens root z)
    (i j : ℕ) : (wSyms w i j).length = 256 := wSyms_length w hw.2.2.1 i j

set_option maxRecDepth 20000 in
/-- **A witness's rows are orthogonal to the dual codeword**, cell by cell. -/
theorem wDot {w : LeanVM.Da.MatrixWitness} {root : Digest} {z : E} (hw : w.Opens root z) :
    ∀ i < w.rows.length, ∑ h ∈ Finset.range 128, ∑ e ∈ Finset.range 256,
      dualAt z (256 * h + e) * ofK ((wSyms w i h).getD e 0) = 0 := by
  intro i hi
  have hw' := hw
  rw [witness_eq hw] at hw'
  have hlen : (daRows w.rows.length (wSyms w)).length = w.rows.length := by simp [daRows]
  have hrow := hw'.2.2.2.2 ((daRows w.rows.length (wSyms w))[i]'(by rw [hlen]; exact hi))
    (List.getElem_mem _)
  have he : (daRows w.rows.length (wSyms w))[i]'(by rw [hlen]; exact hi) =
      (List.range 128).flatMap (wSyms w i) := by simp [daRows]
  have hfun : ∀ b : Fin (2 ^ 15), LeanDa.dualCodewordAt z b *
      LeanDa.ι (((List.range 128).flatMap (wSyms w i)).getD b 0) =
      dualAt z b * ofK (((List.range 128).flatMap (wSyms w i)).getD b 0) := fun b => by
    rw [dualAt_eq]; rfl
  rw [he, LeanDa.innerProduct, Finset.sum_congr rfl fun b _ => hfun b,
    Fin.sum_univ_eq_sum_range (fun b => dualAt z b *
      ofK (((List.range 128).flatMap (wSyms w i)).getD b 0)) (2 ^ 15),
    show 2 ^ 15 = 128 * 256 by norm_num, sum_range_mul _ 256 128] at hrow
  refine (Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun e he => ?_).trans hrow
  have hj' := Finset.mem_range.mp hj
  have he' := Finset.mem_range.mp he
  rw [flatMap_getD (wSyms w i) 256 (wSyms_len hw i) 0 128 j e hj' he']

/-- **The root a witness opens** is the tree `da_verify` builds over its cells. -/
theorem opens_eq {w : LeanVM.Da.MatrixWitness} {root : Digest} {z : E} (hw : w.Opens root z) :
    root = daRoot w.rows.length (wLog w) (wSyms w) := by
  obtain ⟨hlo, -⟩ := nPad_bounds hw.1
  have ho := opens_of (z := z) hw.1 hw.2.1 rfl hlo (wSyms_len hw) (wDot hw)
  rw [← witness_eq hw] at ho
  exact toBytes_inj (hw.2.2.2.1.symm.trans ho.2.2.2.1)

end
end LeanVM.Guest.B1.Da
