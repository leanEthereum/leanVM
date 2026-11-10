import Rv64Verifier.Proofs.Bus.VbbTail61

/-!
# `verify_bus_balance`'s side loop: the matrix under writes that miss it

A step that writes only what misses the matrix's rows and pieces (`O`), and what it allocates, keeps
the matrix, its rows' headers, its forms' headers and its forms (`Mat.keepO`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript

theorem Mat.keepO {b t t' : MachineState} {P : Word} {n : Nat} {O : Word → Prop} (M : Mat b t P n)
    (hheap : HeapOk t) (hm : heapNext t ≤ heapNext t')
    (fr : DFrame t t' fun a ↦ O a ∨ Fresh t t' a)
    (hO : ∀ x, O x → ¬ Within x P (24 * n) ∧ ∀ i < n, ∀ j ≤ 3, ¬ piece t P i j x) :
    Mat b t' P n ∧ (∀ i < n, ∀ k < 3, t'.getMem (rowAt P i + BitVec.ofNat 64 (8 * k)) =
      t.getMem (rowAt P i + BitVec.ofNat 64 (8 * k))) ∧
      (∀ i < n, ∀ j < 3, ∀ k < 3,
        t'.getMem (cellAt t (rowAt P i) j + BitVec.ofNat 64 (8 * k)) =
          t.getMem (cellAt t (rowAt P i) j + BitVec.ofNat 64 (8 * k))) ∧
      ∀ i < n, ∀ j < 3,
        Layout.formOf t' (cellAt t (rowAt P i) j) = Layout.formOf t (cellAt t (rowAt P i) j) := by
  have hnt := hheap.hi
  have hbt := M.mono
  simp only [heapNext, heapEnd] at hnt hbt hm
  have hP (hn : 0 < n) : heapStart ≤ P.toNat ∧ P.toNat + 24 * n ≤ heapNext t := by
    rcases M.hdr.2 with h0 | h0
    · omega
    · exact h0
  simp only [heapNext] at hP
  have rb (i : Nat) (hi : i < n) : 3 ≤ (vecCap t (rowAt P i)).toNat ∧
      heapStart ≤ (vecPtr t (rowAt P i)).toNat ∧
      (vecPtr t (rowAt P i)).toNat + 24 * (vecCap t (rowAt P i)).toNat ≤ heapNext t := by
    obtain ⟨hv, hl⟩ := M.rows i hi
    have hc := hv.len
    rw [hl] at hc
    have e3 : (3 : Word).toNat = 3 := rfl
    have hraw := hv.raw
    simp only [RawVecOk, Buf] at hraw
    refine ⟨by omega, ?_⟩
    rcases hraw.2 with h0 | h0
    · omega
    · exact ⟨h0.1, by omega⟩
  have nf (x : Word) (hx : x.toNat < heapNext t) : ¬ Fresh t t' x := by
    simp only [Fresh]; omega
  have hrow (i : Nat) (hi : i < n) (k : Nat) (hk : k < 3) :
      t'.getMem (rowAt P i + BitVec.ofNat 64 (8 * k)) =
        t.getMem (rowAt P i + BitVec.ofNat 64 (8 * k)) := by
    obtain ⟨p1, p2⟩ := hP (by omega)
    refine fr _ fun q hq hw ↦ ?_
    have hin : Within (rowAt P i + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 q) P (24 * n) := by
      simp only [rowAt, heapStart] at p1 p2 ⊢; addr_omega [p1, p2, hi, hk, hq, hnt]
    rcases hw with hw | hw
    · exact (hO _ hw).1 hin
    · refine nf _ ?_ hw
      simp only [Within] at hin; simp only [heapNext] at p2 ⊢; omega
  have hptr (i : Nat) (hi : i < n) : vecPtr t' (rowAt P i) = vecPtr t (rowAt P i) := by
    have h := hrow i hi 1 (by omega)
    simp only [Nat.mul_one] at h
    exact h
  have hcap (i : Nat) (hi : i < n) : vecCap t' (rowAt P i) = vecCap t (rowAt P i) := by
    have h := hrow i hi 0 (by omega)
    simp only [Nat.mul_zero, add_ofNat_zero] at h
    exact h
  have hlen (i : Nat) (hi : i < n) : vecLen t' (rowAt P i) = vecLen t (rowAt P i) := by
    have h := hrow i hi 2 (by omega)
    simp only [show 8 * 2 = 16 from rfl] at h
    exact h
  have hcellAt (i : Nat) (hi : i < n) (j : Nat) :
      cellAt t' (rowAt P i) j = cellAt t (rowAt P i) j := by
    simp only [cellAt, hptr i hi]
  have inRow (i : Nat) (hi : i < n) (j : Nat) (hj : j < 3) (x : Word)
      (h : Within x (cellAt t (rowAt P i) j) 24) : piece t P i 3 x := by
    rw [piece_row]
    obtain ⟨c3, l, u⟩ := rb i hi
    simp only [Layout.formVecBuf, cellAt, Within] at h ⊢
    addr_omega [h, c3, l, u, hj, hnt]
  have miss (i : Nat) (hi : i < n) (j : Nat) (hj : j ≤ 3) (x : Word) (hx : piece t P i j x) :
      ¬ (O x ∨ Fresh t t' x) := by
    rintro (hw | hw)
    · exact (hO x hw).2 i hi j hj hx
    · exact nf x (M.below hi hj hx).2 hw
  have hcellw (i : Nat) (hi : i < n) (j : Nat) (hj : j < 3) (k : Nat) (hk : k < 3) :
      t'.getMem (cellAt t (rowAt P i) j + BitVec.ofNat 64 (8 * k)) =
        t.getMem (cellAt t (rowAt P i) j + BitVec.ofNat 64 (8 * k)) := by
    obtain ⟨c3, l, u⟩ := rb i hi
    simp only [heapStart, heapNext] at l u
    have hcw : (cellAt t (rowAt P i) j).toNat + 24 ≤ (vecPtr t (rowAt P i)).toNat +
        24 * (vecCap t (rowAt P i)).toNat := by simp only [cellAt]; addr_omega [c3, l, u, hj, hnt]
    exact fr _ fun q hq ↦ miss i hi 3 (le_refl _) _ (inRow i hi j hj _ (by
      simp only [Within, cellAt] at hcw ⊢; addr_omega [hcw, c3, l, u, hj, hk, hq, hnt]))
  have pe (i : Nat) (hi : i < n) (j : Nat) (hj : j ≤ 3) (x : Word) :
      piece t' P i j x ↔ piece t P i j x := by
    rcases Nat.lt_or_ge j 3 with h3 | h3
    · rw [piece_form h3, piece_form h3, hcellAt i hi j]
      have e0 := hcellw i hi j h3 0 (by omega)
      have e8 := hcellw i hi j h3 1 (by omega)
      simp only [Nat.mul_zero, Nat.mul_one, add_ofNat_zero] at e0 e8
      simp only [Layout.formBuf, vecPtr, vecCap]
      rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, e0, e8]
    · obtain rfl : j = 3 := by omega
      rw [piece_row, piece_row]
      simp only [Layout.formVecBuf, hptr i hi, hcap i hi]
  have fo (i : Nat) (hi : i < n) (j : Nat) (hj : j < 3) :
      Layout.formOf t' (cellAt t (rowAt P i) j) = Layout.formOf t (cellAt t (rowAt P i) j) ∧
        Layout.FormOk t' (cellAt t (rowAt P i) j) := by
    have hok := M.forms i hi j hj
    have hcw : (cellAt t (rowAt P i) j).toNat + 24 ≤ 2 ^ 64 := by
      obtain ⟨c3, l, u⟩ := rb i hi
      simp only [heapNext] at u
      simp only [cellAt]; addr_omega [c3, l, u, hj, hnt]
    exact Layout.formOf_frame (toLayoutFrame fr) hok
      (fun x hx ↦ miss i hi 3 (le_refl _) x (inRow i hi j hj x hx))
      (fun x hx ↦ miss i hi j hj.le x ((piece_form hj).mpr hx)) hcw hheap
      (by simp only [heapNext]; omega)
  refine ⟨⟨by simp only [heapNext]; omega, ⟨M.hdr.1, M.hdr.2.imp id fun h ↦ ⟨h.1, by
      simp only [heapNext] at h ⊢; omega⟩⟩,
    fun i hi ↦ ⟨(M.rows i hi).1.keep (hcap i hi) (hptr i hi) (hlen i hi)
      (by simp only [heapNext]; omega), (hlen i hi).trans (M.rows i hi).2⟩,
    fun i hi j hj ↦ by rw [hcellAt i hi j]; exact (fo i hi j hj).2,
    fun i hi j hj x hx ↦ M.fresh i hi j hj x ((pe i hi j hj x).mp hx),
    fun i hi j hj i' hi' j' hj' hne x hx hx' ↦
      M.apart i hi j hj i' hi' j' hj' hne x ((pe i hi j hj x).mp hx) ((pe i' hi' j' hj' x).mp hx'),
    fun i hi j hj x hx ↦ M.outer i hi j hj x ((pe i hi j hj x).mp hx)⟩, hrow, hcellw,
    fun i hi j hj ↦ (fo i hi j hj).1⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
