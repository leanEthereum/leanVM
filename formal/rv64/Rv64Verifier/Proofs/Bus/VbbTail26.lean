import Rv64Verifier.Proofs.Bus.VbbTail25

/-!
# `verify_bus_balance` past the GKR loop: the forms' matrix

`forms[table][side]` at `P`: `n` rows of three forms. Its pieces, each row's buffer and each form's
buffer, were allocated from `b` on, are pairwise apart and apart from the rows' headers (`Mat`).
`Rows1` is such a matrix of empty forms (`Rows1.mat`, `Rows1.value`). A write to one form that only
changes the form's header and buffer, and allocates, keeps the matrix and every other form
(`Mat.update`), which is `Form::add_scaled`'s frame.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript

/-- Piece `j` of row `i`: form `j`'s buffer (`j < 3`) or the row's own buffer (`j = 3`). -/
def piece (t : MachineState) (P : Word) (i j : Nat) (x : Word) : Prop :=
  if j < 3 then Layout.formBuf t (cellAt t (rowAt P i) j) x
  else Layout.formVecBuf t (rowAt P i) x

theorem piece_form {t : MachineState} {P x : Word} {i j : Nat} (hj : j < 3) :
    piece t P i j x ↔ Layout.formBuf t (cellAt t (rowAt P i) j) x := by
  simp only [piece, hj, ↓reduceIte]

theorem piece_row {t : MachineState} {P x : Word} {i : Nat} :
    piece t P i 3 x ↔ Layout.formVecBuf t (rowAt P i) x := by
  simp only [piece, Nat.lt_irrefl, ↓reduceIte]

/-- The matrix at `P`, its pieces allocated from `b` on. -/
structure Mat (b t : MachineState) (P : Word) (n : Nat) : Prop where
  mono : heapNext b ≤ heapNext t
  hdr : P.toNat % 8 = 0 ∧ (n = 0 ∨ heapStart ≤ P.toNat ∧ P.toNat + 24 * n ≤ heapNext t)
  rows : ∀ i < n, VecOk t (rowAt P i) 24 8 ∧ vecLen t (rowAt P i) = 3
  forms : ∀ i < n, ∀ j < 3, Layout.FormOk t (cellAt t (rowAt P i) j)
  fresh : ∀ i < n, ∀ j ≤ 3, ∀ x, piece t P i j x → heapNext b ≤ x.toNat
  apart : ∀ i < n, ∀ j ≤ 3, ∀ i' < n, ∀ j' ≤ 3, (i ≠ i' ∨ j ≠ j') → ∀ x,
    piece t P i j x → ¬ piece t P i' j' x
  outer : ∀ i < n, ∀ j ≤ 3, ∀ x, piece t P i j x → ¬ Within x P (24 * n)

/-- Every piece lies in the heap below `NEXT`. -/
theorem Mat.below {b t : MachineState} {P : Word} {n : Nat} (M : Mat b t P n) {i j : Nat}
    (hi : i < n) (hj : j ≤ 3) {x : Word} (hx : piece t P i j x) :
    heapStart ≤ x.toNat ∧ x.toNat < heapNext t := by
  rcases Nat.lt_or_ge j 3 with h3 | h3
  · rw [piece_form h3] at hx
    exact Layout.formBuf_below (M.forms i hi j h3) hx
  · obtain rfl : j = 3 := by omega
    rw [piece_row] at hx
    have hraw := (M.rows i hi).1.raw
    simp only [RawVecOk, Buf] at hraw
    simp only [Layout.formVecBuf, Within] at hx
    rcases hraw.2 with h0 | h0 <;> omega

/-- The forms' rows of `Rows1` are a matrix of empty forms. -/
theorem Rows1.mat {s z w v : MachineState} (R : Rows1 s z w v) (hz : heapStart ≤ heapNext z) :
    Mat z v (w.getReg .x23) (w.getReg .x25).toNat := by
  have cell0 (i : Nat) (hi : i < (w.getReg .x25).toNat) (j : Nat) (hj : j < 3) (x : Word)
      (hx : piece v (w.getReg .x23) i j x) : False := by
    rw [piece_form hj] at hx
    have hc := ((R.rows i hi).cells j hj).1
    simp only [Layout.formBuf, hc, Within] at hx
    have : (0 : Word).toNat = 0 := rfl
    omega
  refine ⟨R.step.mono, ?_, fun i hi ↦ ⟨(R.rows i hi).vec, (R.rows i hi).len⟩,
    fun i hi j hj ↦ ?_,
    fun i hi j hj x hx ↦ ?_, fun i hi j hj i' hi' j' hj' _ x hx hx' ↦ ?_,
    fun i hi j hj x hx ↦ ?_⟩
  · have ho := R.obuf
    simp only [NewBuf] at ho
    refine ⟨ho.1, ?_⟩
    rcases ho.2 with h0 | h0
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, by omega⟩
  · obtain ⟨c0, c1, c2⟩ := (R.rows i hi).cells j hj
    refine ⟨⟨?_, ?_⟩, fun k hk ↦ absurd hk (by rw [c1]; exact Nat.not_lt_zero _)⟩
    · simp only [RawVecOk, Buf, c0]; exact ⟨by rw [c2]; rfl, Or.inl rfl⟩
    · rw [c0, c1]
  · rcases Nat.lt_or_ge j 3 with h3 | h3
    · exact (cell0 i hi j h3 x hx).elim
    · obtain rfl : j = 3 := by omega
      rw [piece_row] at hx
      obtain ⟨-, q1, -⟩ := (R.rows i hi).bufIn
      simp only [Layout.formVecBuf, Within] at hx
      omega
  · rcases Nat.lt_or_ge j 3 with h3 | h3
    · exact cell0 i hi j h3 x hx
    rcases Nat.lt_or_ge j' 3 with h3' | h3'
    · exact cell0 i' hi' j' h3' x hx'
    obtain rfl : j = 3 := by omega
    obtain rfl : j' = 3 := by omega
    rw [piece_row] at hx hx'
    rename_i hne
    exact R.apart i hi i' hi' (by omega) x hx hx'
  · rcases Nat.lt_or_ge j 3 with h3 | h3
    · exact (cell0 i hi j h3 x hx).elim
    obtain rfl : j = 3 := by omega
    rw [piece_row] at hx
    exact R.outer i hi x hx

/-- The forms of `Rows1`: all empty. -/
theorem Rows1.value {s z w v : MachineState} (R : Rows1 s z w v) :
    formRowsAt v (w.getReg .x23) (w.getReg .x25).toNat =
      List.replicate (w.getReg .x25).toNat (List.replicate 3 {}) := by
  have e : ∀ i ∈ List.range (w.getReg .x25).toNat,
      formVecAt v (w.getReg .x23 + BitVec.ofNat 64 (24 * i)) = List.replicate 3 {} :=
    fun i hi ↦ (R.rows i (List.mem_range.mp hi)).value
  simp only [formRowsAt]
  rw [List.map_congr_left e, List.map_const', List.length_range]

theorem toLayoutFrame {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) :
    Layout.DFrame s t w :=
  fun a ha hw ↦ h a fun i hi hw' ↦ ha _ (by addr_omega [hi, hw]) hw'

/-- A write to form `sd` of row `o` that changes only that form's header and buffer, what `Other`
holds, which misses the matrix, and the heap it allocates keeps the matrix, the rows' headers and
every other form. -/
theorem Mat.update {b t t' : MachineState} {P : Word} {n o sd : Nat} {Other : Word → Prop}
    (M : Mat b t P n) (ho : o < n) (hsd : sd < 3) (hheap : HeapOk t)
    (hmono : heapNext t ≤ heapNext t')
    (fr : DFrame t t' fun a ↦ Within a (cellAt t (rowAt P o) sd) 24 ∨
      Layout.formBuf t (cellAt t (rowAt P o) sd) a ∨ Other a ∨ Fresh t t' a)
    (hO : ∀ x, Other x → ¬ Within x P (24 * n) ∧ ∀ i < n, ∀ j ≤ 3, ¬ piece t P i j x)
    (ok : Layout.FormOk t' (cellAt t (rowAt P o) sd))
    (buf : ∀ x, Layout.formBuf t' (cellAt t (rowAt P o) sd) x →
      Layout.formBuf t (cellAt t (rowAt P o) sd) x ∨ Fresh t t' x) :
    Mat b t' P n ∧ (∀ i < n, ∀ k < 3, t'.getMem (rowAt P i + BitVec.ofNat 64 (8 * k)) =
      t.getMem (rowAt P i + BitVec.ofNat 64 (8 * k))) ∧
      (∀ i < n, ∀ j < 3, (i ≠ o ∨ j ≠ sd) →
        Layout.formOf t' (cellAt t (rowAt P i) j) = Layout.formOf t (cellAt t (rowAt P i) j)) ∧
      (∀ i < n, ∀ j ≤ 3, (i ≠ o ∨ j ≠ sd) → ∀ x, piece t' P i j x ↔ piece t P i j x) ∧
      (∀ x, piece t' P o sd x → piece t P o sd x ∨ Fresh t t' x) ∧
      ∀ i < n, ∀ j < 3, (i ≠ o ∨ j ≠ sd) → ∀ k < 3,
        t'.getMem (cellAt t (rowAt P i) j + BitVec.ofNat 64 (8 * k)) =
          t.getMem (cellAt t (rowAt P i) j + BitVec.ofNat 64 (8 * k)) := by
  have hnt := hheap.hi
  have hbt := M.mono
  simp only [heapNext, heapEnd] at hnt hbt hmono
  have hP : heapStart ≤ P.toNat ∧ P.toNat + 24 * n ≤ heapNext t := by
    rcases M.hdr.2 with h0 | h0
    · omega
    · exact h0
  simp only [heapNext, heapStart] at hP
  -- a row's buffer
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
  -- the frame's set misses what is not `C`'s
  have miss (x : Word) (hx : heapStart ≤ x.toNat ∧ x.toNat < heapNext t)
      (h1 : ¬ Within x (cellAt t (rowAt P o) sd) 24) (h2 : ¬ piece t P o sd x)
      (h3 : Within x P (24 * n) ∨ ∃ i < n, ∃ j ≤ 3, piece t P i j x) :
      ¬ (Within x (cellAt t (rowAt P o) sd) 24 ∨
        Layout.formBuf t (cellAt t (rowAt P o) sd) x ∨ Other x ∨ Fresh t t' x) := by
    rintro (h | h | h | h)
    · exact h1 h
    · exact h2 ((piece_form hsd).mpr h)
    · rcases h3 with h3 | ⟨i, hi, j, hj, h3⟩
      · exact (hO x h).1 h3
      · exact (hO x h).2 i hi j hj h3
    · simp only [Fresh, heapNext] at h hx; omega
  have inRow (i : Nat) (hi : i < n) (j : Nat) (hj : j < 3) (x : Word)
      (h : Within x (cellAt t (rowAt P i) j) 24) : piece t P i 3 x := by
    rw [piece_row]
    obtain ⟨c3, l, u⟩ := rb i hi
    simp only [Layout.formVecBuf, cellAt, Within] at h ⊢
    addr_omega [h, c3, l, u, hj, hnt]
  have rowMiss (i : Nat) (hi : i < n) (x : Word) (hx : Within x (rowAt P i) 24) :
      ¬ (Within x (cellAt t (rowAt P o) sd) 24 ∨
        Layout.formBuf t (cellAt t (rowAt P o) sd) x ∨ Other x ∨ Fresh t t' x) := by
    have hxP : Within x P (24 * n) := by
      simp only [rowAt, Within] at hx ⊢; addr_omega [hx, hP, hi]
    refine miss x ⟨by simp only [Within, heapStart] at hxP ⊢; omega,
      by simp only [Within, heapNext] at hxP ⊢; omega⟩
      (fun h ↦ M.outer o ho 3 (le_refl _) x (inRow o ho sd hsd x h) hxP)
      (fun h ↦ M.outer o ho sd hsd.le x h hxP) (Or.inl hxP)
  have cellMiss (i : Nat) (hi : i < n) (j : Nat) (hj : j < 3) (hne : i ≠ o ∨ j ≠ sd)
    (x : Word)
      (hx : Within x (cellAt t (rowAt P i) j) 24) :
      ¬ (Within x (cellAt t (rowAt P o) sd) 24 ∨
        Layout.formBuf t (cellAt t (rowAt P o) sd) x ∨ Other x ∨ Fresh t t' x) := by
    have hr := inRow i hi j hj x hx
    refine miss x (M.below hi (le_refl _) hr) (fun h ↦ ?_)
      (fun h ↦ M.apart i hi 3 (le_refl _) o ho sd hsd.le (Or.inr (by omega)) x hr h)
      (Or.inr ⟨i, hi, 3, le_refl _, hr⟩)
    rcases hne with hne | hne
    · exact M.apart i hi 3 (le_refl _) o ho 3 (le_refl _) (Or.inl hne) x hr (inRow o ho sd hsd x h)
    · by_cases hio : i = o
      · subst hio
        obtain ⟨c3, l, u⟩ := rb i hi
        simp only [cellAt, Within] at hx h
        addr_omega [hx, h, c3, l, u, hj, hsd, hne, hnt]
      · exact M.apart i hi 3 (le_refl _) o ho 3 (le_refl _) (Or.inl hio) x hr
          (inRow o ho sd hsd x h)
  have bufMiss (i : Nat) (hi : i < n) (j : Nat) (hj : j < 3) (hne : i ≠ o ∨ j ≠ sd) (x : Word)
      (hx : Layout.formBuf t (cellAt t (rowAt P i) j) x) :
      ¬ (Within x (cellAt t (rowAt P o) sd) 24 ∨
        Layout.formBuf t (cellAt t (rowAt P o) sd) x ∨ Other x ∨ Fresh t t' x) := by
    have hp : piece t P i j x := (piece_form hj).mpr hx
    exact miss x (M.below hi hj.le hp)
      (fun h ↦ M.apart i hi j hj.le o ho 3 (le_refl _) (Or.inr (by omega)) x hp
        (inRow o ho sd hsd x h))
      (fun h ↦ M.apart i hi j hj.le o ho sd hsd.le hne x hp h) (Or.inr ⟨i, hi, j, hj.le, hp⟩)
  have word {a : Word} {m : Nat} (hm : 8 ≤ m) (ha : a.toNat + m < 2 ^ 64)
      (hW : ∀ x, Within x a m → ¬ (Within x (cellAt t (rowAt P o) sd) 24 ∨
        Layout.formBuf t (cellAt t (rowAt P o) sd) x ∨ Other x ∨ Fresh t t' x)) :
      t'.getMem a = t.getMem a :=
    fr a fun k hk hw ↦ hW _ (by addr_omega [hk, hm, ha]) hw
  have hrow (i : Nat) (hi : i < n) (k : Nat) (hk : k < 3) :
      t'.getMem (rowAt P i + BitVec.ofNat 64 (8 * k)) =
        t.getMem (rowAt P i + BitVec.ofNat 64 (8 * k)) :=
    word (m := 8) (le_refl _) (by simp only [rowAt]; addr_omega [hP, hi, hk, hnt])
      fun x hx ↦ rowMiss i hi x (by
        simp only [rowAt, Within] at hx ⊢; addr_omega [hx, hP, hi, hk, hnt])
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
  have hcw (i : Nat) (hi : i < n) (j : Nat) (hj : j < 3) :
      (cellAt t (rowAt P i) j).toNat + 24 < 2 ^ 64 := by
    obtain ⟨c3, l, u⟩ := rb i hi
    simp only [cellAt]; addr_omega [c3, l, u, hj, hnt]
  have other (i : Nat) (hi : i < n) (j : Nat) (hj : j < 3) (hne : i ≠ o ∨ j ≠ sd) :
      Layout.formOf t' (cellAt t (rowAt P i) j) = Layout.formOf t (cellAt t (rowAt P i) j) ∧
        Layout.FormOk t' (cellAt t (rowAt P i) j) :=
    Layout.formOf_frame (toLayoutFrame fr) (M.forms i hi j hj) (cellMiss i hi j hj hne)
      (bufMiss i hi j hj hne) (by have := hcw i hi j hj; omega) hheap
      (by simpa [heapNext] using hmono)
  have hcellw (i : Nat) (hi : i < n) (j : Nat) (hj : j < 3) (hne : i ≠ o ∨ j ≠ sd) (k : Nat)
      (hk : k < 3) : t'.getMem (cellAt t (rowAt P i) j + BitVec.ofNat 64 (8 * k)) =
        t.getMem (cellAt t (rowAt P i) j + BitVec.ofNat 64 (8 * k)) :=
    word (m := 8) (le_refl _) (by have := hcw i hi j hj; addr_omega [this, hk])
      fun x hx ↦ cellMiss i hi j hj hne x (by
        have := hcw i hi j hj; simp only [Within] at hx ⊢; addr_omega [hx, this, hk])
  -- the pieces at `t'`
  have pe (i : Nat) (hi : i < n) (j : Nat) (hj : j ≤ 3) (hne : i ≠ o ∨ j ≠ sd) (x : Word) :
      piece t' P i j x ↔ piece t P i j x := by
    rcases Nat.lt_or_ge j 3 with h3 | h3
    · rw [piece_form h3, piece_form h3, hcellAt i hi j]
      have e0 := hcellw i hi j h3 hne 0 (by omega)
      have e8 := hcellw i hi j h3 hne 1 (by omega)
      simp only [Nat.mul_zero, Nat.mul_one, add_ofNat_zero] at e0 e8
      simp only [Layout.formBuf, vecPtr, vecCap]
      rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, e0, e8]
    · obtain rfl : j = 3 := by omega
      rw [piece_row, piece_row]
      simp only [Layout.formVecBuf, hptr i hi, hcap i hi]
  have pn (x : Word) (hx : piece t' P o sd x) : piece t P o sd x ∨ Fresh t t' x := by
    rw [piece_form hsd, hcellAt o ho sd] at hx
    rw [piece_form hsd]
    exact buf x hx
  have hfr (x : Word) (hx : Fresh t t' x) : heapNext t ≤ x.toNat := by
    simp only [Fresh] at hx; exact hx.1
  have hm' : heapNext t ≤ heapNext t' := by simp only [heapNext]; omega
  refine ⟨⟨by have := M.mono; omega,
    ⟨M.hdr.1, M.hdr.2.imp id fun h ↦ ⟨h.1, by omega⟩⟩,
    fun i hi ↦ ⟨(M.rows i hi).1.keep (hcap i hi) (hptr i hi) (hlen i hi) hm',
      (hlen i hi).trans (M.rows i hi).2⟩, fun i hi j hj ↦ ?_, fun i hi j hj x hx ↦ ?_,
    fun i hi j hj i' hi' j' hj' hne x hx hx' ↦ ?_, fun i hi j hj x hx hxP ↦ ?_⟩,
    fun i hi k hk ↦ hrow i hi k hk, fun i hi j hj hne ↦ (other i hi j hj hne).1, pe, pn, hcellw⟩
  · rw [hcellAt i hi j]
    by_cases hc : i = o ∧ j = sd
    · obtain ⟨rfl, rfl⟩ := hc; exact ok
    · exact (other i hi j hj (not_and_or.mp hc)).2
  · by_cases hc : i = o ∧ j = sd
    · obtain ⟨rfl, rfl⟩ := hc
      rcases pn x hx with h | h
      · exact M.fresh i hi j hj x h
      · have := hfr x h; have := M.mono; omega
    · exact M.fresh i hi j hj x ((pe i hi j hj (not_and_or.mp hc) x).mp hx)
  · by_cases hc : i = o ∧ j = sd <;> by_cases hc' : i' = o ∧ j' = sd
    · obtain ⟨rfl, rfl⟩ := hc; obtain ⟨rfl, rfl⟩ := hc'; omega
    · obtain ⟨rfl, rfl⟩ := hc
      have hx'' := (pe i' hi' j' hj' (not_and_or.mp hc') x).mp hx'
      rcases pn x hx with h | h
      · exact M.apart i hi j hj i' hi' j' hj' hne x h hx''
      · have := hfr x h; have := (M.below hi' hj' hx'').2; omega
    · obtain ⟨rfl, rfl⟩ := hc'
      have hx'' := (pe i hi j hj (not_and_or.mp hc) x).mp hx
      rcases pn x hx' with h | h
      · exact M.apart i hi j hj i' hi' j' hj' hne x hx'' h
      · have := hfr x h; have := (M.below hi hj hx'').2; omega
    · exact M.apart i hi j hj i' hi' j' hj' hne x ((pe i hi j hj (not_and_or.mp hc) x).mp hx)
        ((pe i' hi' j' hj' (not_and_or.mp hc') x).mp hx')
  · by_cases hc : i = o ∧ j = sd
    · obtain ⟨rfl, rfl⟩ := hc
      rcases pn x hx with h | h
      · exact M.outer i hi j hj x h hxP
      · have := hfr x h; simp only [Within] at hxP; simp only [heapNext] at this; omega
    · exact M.outer i hi j hj x ((pe i hi j hj (not_and_or.mp hc) x).mp hx) hxP

/-- The matrix's value after a write to form `sd` of row `o` that keeps the rows' headers and every
other form: that form replaced. -/
theorem formRowsAt_update {t t' : MachineState} {P : Word} {n o sd : Nat}
    (hrows : ∀ i < n, vecLen t (rowAt P i) = 3)
    (hrow : ∀ i < n, ∀ k < 3, t'.getMem (rowAt P i + BitVec.ofNat 64 (8 * k)) =
      t.getMem (rowAt P i + BitVec.ofNat 64 (8 * k)))
    (hother : ∀ i < n, ∀ j < 3, (i ≠ o ∨ j ≠ sd) →
      Layout.formOf t' (cellAt t (rowAt P i) j) = Layout.formOf t (cellAt t (rowAt P i) j)) :
    formRowsAt t' P n = (formRowsAt t P n).modify o fun row ↦
      row.modify sd fun _ ↦ (Layout.formOf t' (cellAt t (rowAt P o) sd)).toSpec := by
  have hp (i : Nat) (hi : i < n) : vecPtr t' (rowAt P i) = vecPtr t (rowAt P i) := by
    have h := hrow i hi 1 (by omega)
    simp only [Nat.mul_one] at h
    exact h
  have hl (i : Nat) (hi : i < n) : vecLen t' (rowAt P i) = 3 := by
    have h := hrow i hi 2 (by omega)
    simp only [show 8 * 2 = 16 from rfl] at h
    exact h.trans (hrows i hi)
  apply List.ext_getElem
  · simp [formRowsAt]
  intro i h1 h2
  have hi : i < n := by simpa [formRowsAt] using h1
  simp only [formRowsAt, List.getElem_map, List.getElem_range, List.getElem_modify]
  have hr : rowAt P i = P + BitVec.ofNat 64 (24 * i) := rfl
  rw [← hr]
  apply List.ext_getElem
  · split <;> simp [formVecAt, hl i hi, hrows i hi]
  intro j g1 g2
  have hj : j < 3 := by simpa [formVecAt, hl i hi] using g1
  by_cases hc : o = i ∧ sd = j
  · obtain ⟨rfl, rfl⟩ := hc
    simp only [↓reduceIte, List.getElem_modify, formVecAt, List.getElem_map, List.getElem_range,
      Layout.formAt_eq, cellAt, hp o hi]
  · have hne : i ≠ o ∨ j ≠ sd := by omega
    have e := hother i hi j hj hne
    simp only [cellAt] at e
    by_cases ho : o = i
    · subst ho
      have hsd : ¬ sd = j := by omega
      simp only [↓reduceIte, List.getElem_modify, hsd, formVecAt, List.getElem_map,
        List.getElem_range, Layout.formAt_eq, hp o hi, e]
    · simp only [ho, ↓reduceIte, formVecAt, List.getElem_map, List.getElem_range,
        Layout.formAt_eq, hp i hi, e]

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
