module

public import NativeVm.Code.Phase3.FormsStore
public import NativeVm.Code.Phase3.FormsAcc
public import NativeVm.Code.Phase3.FormsFold
public import NativeVm.Code.Phase3.FormsBlocks

/-!
# The bus forms of a side: the blocks' loop, its invariant

`FLInv … i s`: after `i` blocks, the state holds the fold over them (`accI`): the side's forms in
`busR` (`FZ`, their monomials `ownerShape`), the padding rows' sum in `sumR side`; the padding row,
the data, the selectors, padding weights, slot weights and `β` kept; the loop's state at block `i`;
only the words `W side` written since `mem0`.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript

/-- The words the forms' code writes: the side's forms, the sum, `formTmpR`. -/
def W (side : Nat) (k : Nat) : Prop :=
  (∃ t < nTables, busR.off + formOff t side ≤ k ∧ k < busR.off + formOff t side + 1 + 5 * formCap) ∨
    k = (sumR side).off ∨ k = (sumR side).off + 1 ∨ (ftOff ≤ k ∧ k < ftOff + 24576)

/-- **The loop's invariant** after `i` blocks. -/
structure FLInv (w ctx : UInt64) (side : Nat) (D : List DBlk) (blocks : Array BusBlockW)
    (sels pws ws : Array EW) (β : EW) (forms : Array (Array FormW))
    (mem0 : UInt64 → Option UInt64) (i : Nat) (s : QState) : Prop where
  le : i ≤ D.length
  rdi : s.reg .rdi = ctx
  wp : s.mem (wd ctx ctxWork) = some w
  pad : PadAt s.mem w
  data : DataAt s.mem w side dOff D
  cur : s.mem (wd w vCur) = some (wd w (dOff + (encode side (D.take i)).length))
  sel : s.mem (wd w vSel) = some (wd w ((tselR side).off + 2 * i))
  rem : s.mem (wd w vRem) = some (D.length - i).toUInt64
  hsel : ∀ j (h : j < sels.size), EAtI s.mem w ((tselR side).off + 2 * j) sels[j]
  hpw : ∀ j (h : j < pws.size), EAtI s.mem w ((tselR side).off + 102 + 2 * j) pws[j]
  hws : ∀ j < slotN side, EAtI s.mem w (wSrc side + 2 * j) (ws.getD j 0)
  hbeta : EAtI s.mem w (bSrc side) β
  sum : EAtI s.mem w (sumR side).off (accI forms side blocks sels pws ws β i).2
  fz : ∀ t < nTables, FZ s.mem w (busR.off + formOff t side) formCap
    (((accI forms side blocks sels pws ws β i).1.getD t #[]).getD side #[])
  shp : ∀ t < nTables, shape (((accI forms side blocks sels pws ws β i).1.getD t #[]).getD side #[]) =
    ownerShape (D.take i) t
  ok : FormsOk (accI forms side blocks sels pws ws β i).1
  other : ∀ t s', s' ≠ side → ((accI forms side blocks sels pws ws β i).1.getD t #[]).getD s' #[] =
    (forms.getD t #[]).getD s' #[]
  keep : KeepS w (W side) mem0 s.mem
  dom : ∀ k < dataEnd, (s.mem (wd w k)).isSome

/-! ## Facts the step uses -/

theorem dOk_spec {side : Nat} {D : List DBlk} (h : dOk side D = true) :
    (∀ b ∈ D, blkOk side b = true) ∧ D.length ≤ 51 ∧
      (∀ o < 6, (ownerShape D o).length ≤ formCap) ∧ (encode side D).length ≤ 4096 := by
  simp only [dOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2⟩

theorem dataAt_get {mem : UInt64 → Option UInt64} {w : UInt64} {side : Nat} :
    ∀ (D : List DBlk) (q i : Nat) (h : i < D.length), DataAt mem w side q D →
      BlkAt mem w (q + (encode side (D.take i)).length) side D[i]
  | b :: D, q, 0, _, h => by simpa [encode] using h.1
  | b :: D, q, i + 1, hi, h => by
    have := dataAt_get D _ i (by simp at hi; omega) h.2
    simp only [List.take_succ_cons, List.getElem_cons_succ]
    rw [show (encode side (b :: D.take i)).length = (encBlk side b).length +
      (encode side (D.take i)).length by simp [encode]]
    rwa [← Nat.add_assoc]

theorem EntAt.congr' {mem mem' : UInt64 → Option UInt64} {w : UInt64} {q : Nat} {e : DEnt}
    (h : ∀ k < 5, mem' (wd w (q + k)) = mem (wd w (q + k))) (he : EntAt mem w q e) :
    EntAt mem' w q e :=
  ⟨by rw [← Nat.add_zero q, h 0 (by omega)]; exact he.1, by rw [h 1 (by omega)]; exact he.2.1,
    by rw [h 2 (by omega)]; exact he.2.2.1, by rw [h 3 (by omega)]; exact he.2.2.2.1,
    by rw [h 4 (by omega)]; exact he.2.2.2.2⟩

theorem dataAt_congr {mem mem' : UInt64 → Option UInt64} {w : UInt64} {side : Nat} :
    ∀ (D : List DBlk) (q : Nat), (∀ k, q ≤ k → k < q + (encode side D).length →
      mem' (wd w k) = mem (wd w k)) → DataAt mem w side q D → DataAt mem' w side q D
  | [], _, _, _ => trivial
  | b :: D, q, h, ⟨⟨h0, h1, he⟩, hD⟩ => by
    have hl : (encode side (b :: D)).length = (encBlk side b).length + (encode side D).length := by
      simp [encode]
    have hb := encBlk_length side b
    refine ⟨⟨by rw [h q le_rfl (by omega)]; exact h0, by rw [h (q + 1) (by omega) (by omega)]; exact h1,
      fun j hj ↦ (he j hj).congr' fun k hk ↦ h _ (by omega) (by omega)⟩, dataAt_congr D _
      (fun k h1 h2 ↦ h k (by omega) (by omega)) hD⟩

theorem encode_take_le (side : Nat) (D : List DBlk) (i : Nat) :
    (encode side (D.take i)).length ≤ (encode side D).length := by
  conv_rhs => rw [← List.take_append_drop i D]
  rw [encode, encode, List.flatMap_append, List.length_append]
  omega

theorem buildF_cols {es : List DEnt} {ws : Array EW} {β : EW} {t : TermW} (ht : t ∈ buildF es ws β) :
    ∀ a ∈ t.cols, ∃ e ∈ es, a ∈ e.2.1 := by
  intro a ha
  have hm : t.cols.toList ∈ shape (buildF es ws β) :=
    List.mem_map.mpr ⟨t, Array.mem_toList_iff.mpr ht, rfl⟩
  rw [shape_buildF] at hm
  rcases mem_foldl_addMono hm with h | h
  · simp only [List.mem_singleton] at h
    have : a ∈ t.cols.toList := Array.mem_toList_iff.mpr ha
    rw [h] at this
    simp at this
  · obtain ⟨e, he, hc⟩ := List.mem_map.mp h
    exact ⟨e, he, by rw [hc]; exact Array.mem_toList_iff.mpr ha⟩

end NativeVm.Code.P3
