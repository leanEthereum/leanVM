/-
  LeanVM.Guest.B1.Da.Verify

  B1 for `da_verify` (G:2888-2956), soundly: its relation implies that a LeanDA witness opens the
  returned root and vector digest (`Da.Witness.Opens`).
-/

module

public import LeanVM.Guest.B1.Da.Witness
public import LeanVM.Guest.B1.Da.ListDigest

/-!
# `da_verify`, soundly

From `DaFacts`: each column's and each cell's facts (`Da.Columns`), each row's digest, then the
witness, the rows' symbols and the vector's weights, and its four properties: the vector digest
is the chain of the `128` columns' hashes (`vector_chain`), the rows' inner products telescope to
the row sums' ends, `0` (`dot_eq`), and the commitment is the hash of the row tree's root and the
column tree's (`commitCodewords_eq`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Node

@[expose] public section

/-- **`da_verify`, soundly**: the facts of its relation give a witness that opens the returned
root and vector digest. -/
theorem daFacts_opens {rd : Reader} {r0 r1 v0 v1 : E} (h : DaFacts rd r0 r1 v0 v1) :
    ∃ (root vd : Digest) (w : Da.Witness), (r0, r1) = digestScalars root ∧ (v0, v1) = digestScalars vd ∧
      w.Opens root vd := by
  obtain ⟨r, pb, pd, hs, ctr, acc, rb, ct, rt, rc0, rc1, rr0, rr1, hr1, hr2, h88, hiv0, hiv1, -, hctr, h89,
    hcol, h92, hlv7, h93, h94, hlvr, hfin, hv0, hv1⟩ := h
  have hr33 : r < 2 ^ 33 := by unfold LeanDa.maxRows at hr2; omega
  obtain ⟨hrN, hNr⟩ := (logPad_iff (lp := LeanDa.logPad r) hr1).mp rfl
  have hNdef : LeanDa.nPad r = 2 ^ LeanDa.logPad r := rfl
  obtain ⟨F, hF⟩ := choose_lt (fun b hb => col_facts hr1 hr2 hctr hb (hcol b hb))
  obtain ⟨G, hG⟩ := choose_lt₂ (n := 128) (m := r) (P := fun b i c =>
      CellOk rd (decide (b < 64)) (F b).lv rb (gen ^ b) (F b).node pb (gen ^ i) c)
    (fun b hb i hi => cell_facts ((hF b hb).2.2.2.2.2.1 i hi))
  obtain ⟨Rw, hRw⟩ := choose_lt (α := E × List E) (n := r) (P := fun i x =>
      LoadHolds rd (pb * gen ^ i) 0 x.1 ∧ x.2.length = 128 ∧ CellsAt rd x.1 x.2 ∧
        (∀ c ∈ x.2, IsCanonical128 c) ∧
        CellsAt rd (rt * (gen ^ i * gen ^ i)) [(digestScalars (blake2sBytes (x.2.flatMap cellBytes))).1,
          (digestScalars (blake2sBytes (x.2.flatMap cellBytes))).2])
    (fun i hi => by obtain ⟨P, cs, h⟩ := h93 i hi; exact ⟨(P, cs), h⟩)
  -- the witness
  let sy : ℕ → ℕ → List K := fun b i => (G b i).syms
  let rowL : ℕ → List K := fun i => (List.range 128).flatMap fun b => sy b i
  let rows : List (List K) := (List.range r).map rowL
  let vector : List E := (List.range 128).flatMap fun b => (F b).ws
  have hsyl : ∀ b < 128, ∀ i < r, (sy b i).length = 256 := fun b hb i hi => (hG b hb i hi).1
  have hrowL : ∀ i < r, (rowL i).length = 2 ^ LeanDa.logM := fun i hi => by
    rw [length_flatMap_range _ 128 (fun b hb => hsyl b hb i hi)]; rfl
  -- the column roots
  have hcolroot : ∀ b < 128, ((F b).c0, (F b).c1) = digestScalars (nodeD (colLeafOf r sy b) (LeanDa.logPad r) 0) := by
    intro b hb
    obtain ⟨-, -, -, -, -, -, hgap, hlv, -⟩ := hF b hb
    refine levels_root hlv fun i hi => ?_
    rw [← hNdef] at hi
    by_cases hir : i < r
    · obtain ⟨-, -, -, hd, -, -, -, -, hn, -⟩ := hG b hb i hir
      simp only [colLeafOf, cellDOf, hir, ↓reduceIte]
      rw [gen_sq] at hn
      rw [← hd]; exact hn
    · have := hgap (i - r) (by omega)
      simp only [colLeafOf, hir, ↓reduceIte, padCell_cells]
      unfold GapStep at this
      rwa [pad_ptr, show r + (i - r) = i by omega] at this
  have hRC : (rc0, rc1) = digestScalars (colRootOf r sy) := by
    refine levels_root hlv7 fun b hb => ?_
    rw [← hcolroot b (by simpa using hb)]
    exact (hF b (by simpa using hb)).2.2.2.2.2.2.2.2
  -- the row digests
  have hcs : ∀ i < r, (Rw i).2.flatMap cellBytes = (List.range 64).flatMap fun b => digestBytes (cellDOf sy b i) := by
    intro i hi
    obtain ⟨hP, hlen, hcells, -, -⟩ := hRw i hi
    have hc2 : ∀ b < 64, (Rw i).2.getD (2 * b) 0 = (G b i).d0 ∧ (Rw i).2.getD (2 * b + 1) 0 = (G b i).d1 := by
      intro b hb
      obtain ⟨-, -, -, -, -, -, -, -, -, hst⟩ := hG b (by omega) i hi
      obtain ⟨P', hP', hc⟩ := hst (decide_eq_true hb)
      rw [loadHolds_unique hP' hP, gen_sq] at hc
      obtain ⟨x0, x1⟩ := cellsAt_two.mp hc
      rw [loadHolds_mul_gen_pow] at x0 x1
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
      exact ⟨loadHolds_unique (hcells _ (by omega)) x0, loadHolds_unique (hcells _ (by omega)) x1⟩
    rw [← flatMap_range_getD (Rw i).2 0 cellBytes, hlen, show 128 = 2 * 64 by rfl, flatMap_range_mul 2]
    refine List.flatMap_congr fun b hb => ?_
    have hb' := List.mem_range.mp hb
    rw [show List.range 2 = [0, 1] from rfl]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.add_zero]
    rw [(hc2 b hb').1, (hc2 b hb').2, digestBytes_eq, cellDOf, ← (hG b (by omega) i hi).2.2.2.1]
  have hRR : (rr0, rr1) = digestScalars (rowRootOf r sy) := by
    refine levels_root hlvr fun i hi => ?_
    rw [← hNdef] at hi
    by_cases hir : i < r
    · obtain ⟨-, -, -, -, hout⟩ := hRw i hir
      simp only [rowLeafOf, hir, ↓reduceIte, rowDOf]
      rw [gen_sq, hcs i hir] at hout
      exact hout
    · have := h94 (i - r) (by omega)
      simp only [rowLeafOf, hir, ↓reduceIte, padRow_cells]
      unfold L94Step at this
      rwa [pad_ptr, show r + (i - r) = i by omega] at this
  refine ⟨commitOf r sy, blake2sBytes (vector.flatMap eBytes), ⟨rows, vector⟩, ?_,
    vector_chain hF hiv0 hiv1 hv0 hv1, ?_⟩
  · obtain ⟨e1, e2⟩ := Prod.mk.inj hRR
    obtain ⟨e3, e4⟩ := Prod.mk.inj hRC
    rw [e1, e2, e3, e4] at hfin
    exact compress_pair.mp hfin
  have hlen : rows.length = r := by simp [rows]
  refine ⟨by simp only [hlen]; exact hr1, by simp only [hlen]; exact hr2, fun row hrow => ?_, ?_, ?_,
    vectorDigest_eq vector, fun row hrow => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hrow
    exact hrowL i (List.mem_range.mp hi)
  · rw [commitCodewords_eq (by rw [hlen]; exact hr1) fun i hi b hb => ?_, hlen]
    simp only [rows, List.getElem_map, List.getElem_range]
    exact listCell_flatMap (fun b => sy b i) (fun b hb => hsyl b hb i (by rw [← hlen]; exact hi)) hb
  · show vector.length = _
    rw [length_flatMap_range _ 128 (fun b hb => (hF b hb).1)]; rfl
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hrow
    have hi' := List.mem_range.mp hi
    have hws : ∀ b < 128, ∀ k < 256, (G b i).wsc.getD k 0 = (F b).ws.getD k 0 := by
      intro b hb k hk
      obtain ⟨-, hwl, hcells, -⟩ := hG b hb i hi'
      obtain ⟨-, -, -, -, hfr, -⟩ := hF b hb
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hfr.2 k (by rw [(hF b hb).1]; exact hk) _ (hcells k (by omega)).2
    let Ri : E := acc * (gen ^ i) ^ 129
    have hR : ∀ b < 128, (G b i).R = Ri := fun b hb =>
      loadHolds_unique (hG b hb i hi').2.2.2.2.2.1 (h89 i hi').1
    have hA : ∀ b < 128, (G b i).s = cellAt rd Ri (b + 1) - cellAt rd Ri b := by
      intro b hb
      obtain ⟨-, -, -, -, -, -, ha, has, -⟩ := hG b hb i hi'
      rw [hR b hb, loadHolds_mul_gen_pow] at ha has
      have e0 : cellAt rd Ri b = (G b i).a := cellAt_of_load ha
      have e1 : cellAt rd Ri (b + 1) = (G b i).a + (G b i).s := cellAt_of_load has
      rw [e0, e1]
      ring
    have h0 : cellAt rd Ri 0 = 0 := cellAt_of_load (h89 i hi').2
    have h128 : cellAt rd Ri 128 = 0 := by
      obtain ⟨R', hR', h1⟩ := h92 i hi'
      rw [loadHolds_unique hR' (h89 i hi').1] at h1
      exact cellAt_of_load h1
    rw [dot_eq rfl rfl (fun b hb => (hF b hb).1) (fun b hb => hsyl b hb i hi')]
    rw [Finset.sum_congr rfl (g := fun b => (G b i).s) fun b hb => by
        have hb' := Finset.mem_range.mp hb
        rw [(hG b hb' i hi').2.2.2.2.1]
        exact Finset.sum_congr rfl fun k hk => by rw [hws b hb' k (Finset.mem_range.mp hk)],
      Finset.sum_congr rfl (fun b hb => hA b (Finset.mem_range.mp hb)), Finset.sum_range_sub, h128, h0, sub_zero]

/-- **`da_verify`, soundly**: on a valid execution's memory and the squares table, the returned
cells are a root and a vector digest that some LeanDA witness opens. -/
theorem da_verify_sound {rd : Reader} (hm : MemOk rd) {gsq : E} (hT : SquaresAt rd gsq) {r0 r1 v0 v1 : E}
    (h : coreProgram.Rel rd "da_verify" [gsq] [r0, r1, v0, v1]) :
    ∃ (root vd : Digest) (w : Da.Witness), (r0, r1) = digestScalars root ∧ (v0, v1) = digestScalars vd ∧
      w.Opens root vd :=
  daFacts_opens (da_verify_facts hm hT h)

/-! ## The dispatch bounds group K's checker assumes -/

/-- `da_row_shape`'s argument `1` is `g^k`, `k < 11` (its post `(3, 11)`): `da_verify`'s dispatch
on it, and the columns' (`da_verify_column`'s argument `4`), stay in their tables. -/
theorem da_row_shape_glp_lt {rd : Reader} (hm : MemOk rd) {gsq : E} (hT : SquaresAt rd gsq)
    {n_blob glp : E} {rets : List E} (h : coreProgram.Rel rd "da_row_shape" [n_blob, glp, gsq] rets) :
    ∃ k < 11, glp = gen ^ k := by
  obtain ⟨_, _, _, _, _, ha, -, r, -, hr2, -, hglp, -⟩ := (da_row_shape_iff hm hT _ _ _).mp h
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨-, rfl, -⟩ := ha
  exact ⟨_, by have := logPad_le hr2; omega, hglp⟩

/-- `da_list_digest`'s argument `1` is `g^k`, `k < 17`. -/
theorem da_list_digest_ng_lt {rd : Reader} {roots n_g : E} {rets : List E}
    (h : coreProgram.Rel rd "da_list_digest" [roots, n_g] rets) : ∃ k < 17, n_g = gen ^ k := by
  obtain ⟨_, _, _, _, ha, -, claims, hlen, hng, -⟩ := (da_list_digest_iff rd _ _).mp h
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨-, rfl⟩ := ha
  exact ⟨_, by omega, hng⟩

end
end LeanVM.Guest.B1.Digest

namespace LeanVM.Guest.B1
export Digest (DaFacts da_verify_facts daFacts_opens da_verify_sound da_row_shape_glp_lt
  da_list_digest_ng_lt)
end LeanVM.Guest.B1
