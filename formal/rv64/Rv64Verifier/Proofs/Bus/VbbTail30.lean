import Rv64Verifier.Proofs.Bus.VbbTail29

/-!
# `verify_bus_balance` past the side loop: `FinalStage`

The result `finalRun` stores holds the mirror's value (`BusResultAt`): the claims, the bytecode's
point and the point allocated before `z` and kept since, the forms' matrix and the totals as the
side loop left them, every buffer below `NEXT` (`Ptrs` for the empty ones), the forms' pieces apart.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript

theorem NewBuf.bufAt {s z t : MachineState} {p : Word} {m : Nat} (h : NewBuf s z p m 8)
    (hs : HeapOk s) (hm : heapNext z ≤ heapNext t) : Buf t p m 8 := by
  have := hs.lo
  simp only [NewBuf, Buf] at h ⊢
  exact ⟨h.1, h.2.imp id fun h' ↦ ⟨by omega, by omega⟩⟩

/-- A byte of a piece, at its length, is a byte of the piece. -/
theorem formPiece_piece {b t : MachineState} {P : Word} {n : Nat} (M : Mat b t P n) {i j : Nat}
    (hi : i < n) (hj : j ≤ 3) {x : Word}
    (hx : Within x (formPiece t P i j).1 (formPiece t P i j).2) : piece t P i j x := by
  rcases Nat.lt_or_ge j 3 with h3 | h3
  · rw [piece_form h3]
    simp only [formPiece, h3, ↓reduceIte] at hx
    have hl := (M.forms i hi j h3).vec.len
    simp only [Layout.formBuf, cellAt, rowAt, Within] at hx hl ⊢
    omega
  · obtain rfl : j = 3 := by omega
    rw [piece_row]
    simp only [formPiece, Nat.lt_irrefl, ↓reduceIte] at hx
    have hl := (M.rows i hi).1.len
    simp only [Layout.formVecBuf, rowAt, Within] at hx hl ⊢
    omega

theorem finalStage (bev : MachineState → Word → List E → Option E) : FinalStage bev := by
  intro s z w v h₀ h k state mem mf bf bv hpre C hpc Sd
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have F := C.fps
  have stVH := C.setup.step.trans Sd.step
  have stZH := (C.rows1.step.trans C.setup.step).trans Sd.step
  have vw (j : Nat) (hj : 8 ≤ j) (hj2 : j ≤ 1344)
      (hm : ∀ i, j - 8 < i → i ≤ j → (320 ≤ i ∧ i ≤ 608 → False) ∧ (1224 < i ∧ i ≤ 1240 → False) ∧
        (1280 < i ∧ i ≤ 1304 → False) ∧ (1256 < i ∧ i ≤ 1272 → False) ∧
        (1240 < i ∧ i ≤ 1248 → False) ∧ (1144 < i ∧ i ≤ 1216 → False) ∧
        (1104 < i ∧ i ≤ 1136 → False) ∧ (608 < i ∧ i ≤ 632 → False) ∧ (104 < i ∧ i ≤ 320 → False)) :
      h.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = v.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    stVH.slot' hpre hj hj2 fun y hy hy' ↦ by
      have hyn : (s.getReg .x2).toNat - j ≤ y.toNat ∧ y.toNat < (s.getReg .x2).toNat - j + 8 := by
        addr_omega [hy, hb1, hj, hj2]
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hm ((s.getReg .x2).toNat - y.toNat) (by omega)
        (by omega)
      simp only [SetupW, LoopW, heapEnd] at hy'
      rcases hy' with (hy' | hy') | (hy' | hy' | hy' | hy' | hy' | hy' | hy' | hy')
      · exact c1 (by addr_omega [hy', hb1, hyn])
      · exact c2 (by addr_omega [hy', hb1, hyn])
      · exact c3 (by addr_omega [hy', hb1, hyn])
      · exact c4 (by addr_omega [hy', hb1, hyn])
      · exact c5 (by addr_omega [hy', hb1, hyn])
      · exact c6 (by addr_omega [hy', hb1, hyn])
      · exact c7 (by addr_omega [hy', hb1, hyn])
      · exact c8 (by addr_omega [hy', hb1, hyn])
      · exact c9 (by addr_omega [hy', hb1, hyn])
      · addr_omega [hy', hb1, hyn, hj2]
  have rw' (j : Nat) (hj : 8 ≤ j) (hj2 : j ≤ 1344)
      (hm : ∀ i, j - 8 < i → i ≤ j → (584 < i ∧ i ≤ 608 → False) ∧ (1320 < i ∧ i ≤ 1328 → False) ∧
        (1216 < i ∧ i ≤ 1224 → False)) :
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = z.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    C.rows1.step.slot' hpre hj hj2 fun y hy hy' ↦ by
      have hyn : (s.getReg .x2).toNat - j ≤ y.toNat ∧ y.toNat < (s.getReg .x2).toNat - j + 8 := by
        addr_omega [hy, hb1, hj, hj2]
      obtain ⟨c1, c2, c3⟩ := hm ((s.getReg .x2).toNat - y.toNat) (by omega) (by omega)
      simp only [RowsW] at hy'
      rcases hy' with hy' | hy' | hy'
      · exact c1 (by addr_omega [hy', hb1, hyn])
      · exact c2 (by addr_omega [hy', hb1, hyn])
      · exact c3 (by addr_omega [hy', hb1, hyn])
  have zw (j : Nat) (hj : 8 ≤ j) (hj2 : j ≤ 1344)
      (hm : ∀ i, j - 8 < i → i ≤ j → (320 ≤ i ∧ i ≤ 608 → False) ∧ (1224 < i ∧ i ≤ 1240 → False) ∧
        (1280 < i ∧ i ≤ 1304 → False) ∧ (1256 < i ∧ i ≤ 1272 → False) ∧
        (1240 < i ∧ i ≤ 1248 → False) ∧ (1144 < i ∧ i ≤ 1216 → False) ∧
        (1104 < i ∧ i ≤ 1136 → False) ∧ (608 < i ∧ i ≤ 632 → False) ∧ (104 < i ∧ i ≤ 320 → False))
      (hm' : ∀ i, j - 8 < i → i ≤ j → (584 < i ∧ i ≤ 608 → False) ∧ (1320 < i ∧ i ≤ 1328 → False) ∧
        (1216 < i ∧ i ≤ 1224 → False)) :
      h.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = z.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    (vw j hj hj2 hm).trans (rw' j hj hj2 hm')
  have hout' : h.getMem (s.getReg .x2 - 1312) = s.getReg .x10 :=
    (vw 1312 (by omega) (by omega) (by intro i h1 h2; omega)).trans C.kept.out
  obtain ⟨t, hr, ex, FO, frHT, hnt⟩ := finalRun hpre Sd.inv hout' hpc
  have hzh := stZH.mono
  have hsz := F.inv.mono
  have hzt : heapNext z ≤ heapNext t := by rw [hnt]; exact hzh
  have hht := Sd.inv.heap.hi
  have hof := hpre.outFree
  -- the heap from the entry's `NEXT` on, up to `h`'s, is kept from `h` to `t`
  have hkH : HeapKept s h t (heapNext h) := fun x h1 h2 ↦ frHT x fun i hi hw ↦ by
    simp only [Outside, heapNext, heapEnd] at hof h1 h2 hht
    rcases hw with hw | hw
    · rcases hof.1 with ho | ho <;> addr_omega [hw, hi, h1, h2, ho, hht]
    · addr_omega [hw, hi, h1, h2, hht, hzh, hb1]
  -- and up to `z`'s, from `z` to `t`
  have hkZ : HeapKept s z t (heapNext z) := fun x h1 h2 ↦ (hkH x h1 (by omega)).trans
    (stZH.frame x fun i hi hw ↦ by
      simp only [heapNext, heapEnd] at h1 h2 hht hzh
      rcases hw with hw | hw | hw | hw
      · simp only [RowsW, SetupW, LoopW] at hw
        rcases hw with ((hw | hw | hw) | (hw | hw)) | (hw | hw | hw | hw | hw | hw | hw | hw) <;>
          addr_omega [hw, hi, h1, h2, hht, hzh, hb1]
      · addr_omega [hw, hi, h1, h2, hht, hzh, hb1]
      · addr_omega [hw, hi, h1, h2, hht, hzh, hb1]
      · simp only [Fresh, heapNext] at hw
        addr_omega [hw, hi, h1, h2, hht, hzh, hb1])
  -- the program's run
  refine ⟨t, hr, ex.pc, ex.preserves, ex.heap, ex.mono, fun T hT ↦ ?_, ex.frame⟩
  obtain ⟨T', hT', e⟩ := F.tracks.done T hT
  have e' : (verifyBusBalanceM (bev s (bytecodeOf s (s.getReg .x11)))
      (busLayoutAt s (s.getReg .x11))).run T = some (restValue s k state mem mf bf bv, T') := e
  rw [e']
  dsimp only
  -- the frame's words at `h`
  have nm (j : Nat) : ∀ i, j - 8 < i → i ≤ j → True := fun _ _ _ ↦ trivial
  have c0 := zw 840 (by omega) (by omega) (by intro i h1 h2; omega) (by intro i h1 h2; omega)
  have c8 := zw 832 (by omega) (by omega) (by intro i h1 h2; omega) (by intro i h1 h2; omega)
  have c16 := zw 824 (by omega) (by omega) (by intro i h1 h2; omega) (by intro i h1 h2; omega)
  have b0 := zw 768 (by omega) (by omega) (by intro i h1 h2; omega) (by intro i h1 h2; omega)
  have b8 := zw 760 (by omega) (by omega) (by intro i h1 h2; omega) (by intro i h1 h2; omega)
  have b16 := zw 752 (by omega) (by omega) (by intro i h1 h2; omega) (by intro i h1 h2; omega)
  have p0 := zw 1320 (by omega) (by omega) (by intro i h1 h2; omega) (by intro i h1 h2; omega)
  have p16 := zw 1144 (by omega) (by omega) (by intro i h1 h2; omega) (by intro i h1 h2; omega)
  have f0 := vw 1328 (by omega) (by omega) (by intro i h1 h2; omega)
  have f8 := vw 1224 (by omega) (by omega) (by intro i h1 h2; omega)
  clear nm
  have hx27 : h.getReg .x27 = z.getMem (s.getReg .x2 - 1256) :=
    Sd.x27.trans ((C.setup.regs .x27 (by decide)).trans ((C.rows1.regs .x27 (by decide)).trans
      ((C.rows0.regs .x27 (by decide)).trans F.x27)))
  have hx25 : h.getReg .x25 = w.getReg .x25 :=
    Sd.x25.trans ((C.setup.regs .x25 (by decide)).trans (C.rows1.regs .x25 (by decide)))
  -- the claims
  have CO := F.claims.heapKept hkZ F.inv.heap.hi (le_refl _) F.inv.heap.hi hzt
    (by rw [F.len]; decide)
  have ecap : vecCap t (s.getReg .x10) = z.getMem (s.getReg .x2 - 840) := FO.w0.trans c0
  have eptr : vecPtr t (s.getReg .x10) = z.getMem (s.getReg .x2 - 832) := FO.w8.trans c8
  have elen : vecLen t (s.getReg .x10) = z.getMem (s.getReg .x2 - 824) := FO.w16.trans c16
  have hl5 : (z.getMem (s.getReg .x2 - 824)).toNat = 5 := by rw [F.len]; rfl
  have hcl5 := CO.claims.le
  have hbuf := CO.claims.buf
  have hcapB : 56 * (z.getMem (s.getReg .x2 - 840)).toNat ≤ heapEnd := by
    have := F.inv.heap.hi
    simp only [NewBuf] at hbuf
    rcases hbuf.2 with h0 | h0 <;> omega
  have hcl : (restValue s k state mem mf bf bv).claims = allClaims s state mem mf bf := by
    simp [restValue, tailValue, allClaims, claims4, memClaims, busLayoutAt, logMem, logBc]
  have hlenC := CO.claims.len
  have hcapNe : vecCap t (s.getReg .x10) ≠ errNiche := by
    rw [ecap]; intro he
    have h1 : (z.getMem (s.getReg .x2 - 840)).toNat = 2 ^ 64 - 1 := by rw [he]; rfl
    simp only [heapEnd] at hcapB
    omega
  have hclaims : (List.range (vecLen t (s.getReg .x10)).toNat).map
      (fun i ↦ claimAt t (vecPtr t (s.getReg .x10) + BitVec.ofNat 64 (56 * i))) =
        (restValue s k state mem mf bf bv).claims := by
    rw [elen, eptr, hcl]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range]; exact hlenC
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      exact (CO.claims.claims i h2).eq
  have hcvec : ∀ i < (vecLen t (s.getReg .x10)).toNat,
      ∃ xs, NewVecE s t (vecPtr t (s.getReg .x10) + BitVec.ofNat 64 (56 * i)) xs := by
    rw [elen, eptr]
    intro i hi
    exact ⟨_, (CO.claims.claims i (by rw [← hlenC]; exact hi)).vec⟩
  have hcok : VecOk t (s.getReg .x10) 56 8 := by
    refine ⟨?_, ?_⟩
    · show Buf t (vecPtr t _) _ 8
      rw [eptr, ecap, Nat.mul_comm]
      exact NewBuf.bufAt hbuf hpre.heap (le_refl _)
    · rw [elen, ecap]; exact hcl5
  have hcbuf : NewBuf s t (vecPtr t (s.getReg .x10)) (56 * (vecCap t (s.getReg .x10)).toNat) 8 := by
    rw [eptr, ecap]; exact hbuf
  have hcIn : BufIn s t (vecPtr t (s.getReg .x10)) (56 * (vecCap t (s.getReg .x10)).toNat) := by
    rw [eptr, ecap]; exact BufIn.of_newBuf hbuf (by omega)
  -- the claims' points
  have hptrB : heapNext s ≤ (z.getMem (s.getReg .x2 - 832)).toNat ∧
      (z.getMem (s.getReg .x2 - 832)).toNat + 56 * (z.getMem (s.getReg .x2 - 840)).toNat ≤
        heapNext z := by
    have hb := F.claims.claims.buf
    simp only [NewBuf] at hb
    rcases hb.2 with h0 | h0
    · omega
    · exact h0
  have hcp : ∀ i < (vecLen t (s.getReg .x10)).toNat,
      BufIn s t (vecPtr t (vecPtr t (s.getReg .x10) + BitVec.ofNat 64 (56 * i)))
        (24 * (vecLen t (vecPtr t (s.getReg .x10) + BitVec.ofNat 64 (56 * i))).toNat) ∧
      Apart (vecPtr t (vecPtr t (s.getReg .x10) + BitVec.ofNat 64 (56 * i)))
        (24 * (vecLen t (vecPtr t (s.getReg .x10) + BitVec.ofNat 64 (56 * i))).toNat)
        (vecPtr t (s.getReg .x10)) (56 * (vecCap t (s.getReg .x10)).toNat) := by
    rw [elen, eptr, ecap]
    intro i hi
    have hi' : i < (allClaims s state mem mf bf).length := by rw [← hlenC]; exact hi
    have CA := CO.claims.claims i hi'
    have hheB : heapNext z ≤ heapEnd := F.inv.heap.hi
    have w8 := hkZ.at hheB (a := z.getMem (s.getReg .x2 - 832) + BitVec.ofNat 64 (56 * i))
      (m := 56) (j := 8) (by simp only [heapNext, heapEnd] at hheB hptrB ⊢; addr_omega [hptrB, hi, hcl5, hheB])
      (by simp only [heapNext, heapEnd] at hheB hptrB ⊢; addr_omega [hptrB, hi, hcl5, hheB]) (by omega)
    have w16 := hkZ.at hheB (a := z.getMem (s.getReg .x2 - 832) + BitVec.ofNat 64 (56 * i))
      (m := 56) (j := 16) (by simp only [heapNext, heapEnd] at hheB hptrB ⊢; addr_omega [hptrB, hi, hcl5, hheB])
      (by simp only [heapNext, heapEnd] at hheB hptrB ⊢; addr_omega [hptrB, hi, hcl5, hheB]) (by omega)
    have eP : vecPtr t (z.getMem (s.getReg .x2 - 832) + BitVec.ofNat 64 (56 * i)) =
        vecPtr z (z.getMem (s.getReg .x2 - 832) + BitVec.ofNat 64 (56 * i)) := w8
    have eL : vecLen t (z.getMem (s.getReg .x2 - 832) + BitVec.ofNat 64 (56 * i)) =
        vecLen z (z.getMem (s.getReg .x2 - 832) + BitVec.ofNat 64 (56 * i)) := w16
    have pz := C.ptrs.claims i (by omega)
    have vb : Buf t _ _ 8 := CA.vec.vec.raw
    have vl := CA.vec.vec.len
    have nb := CA.vec.buf
    have ap := CO.apart i hi
    simp only [Buf, NewBuf] at vb nb
    refine ⟨⟨vb.1, by rw [eP, eL]; omega, ?_⟩, Apart.shrink ap (by omega) (le_refl _)⟩
    rcases nb.2 with h0 | h0
    · exact Or.inl (by rw [Nat.mul_eq_zero] at h0; omega)
    · exact Or.inr h0.1
  -- the bytecode's point
  have hheZ : heapNext z ≤ heapEnd := F.inv.heap.hi
  have hbp : NewVecE s t (s.getReg .x10 + 24)
      (restValue s k state mem mf bf bv).bytecodePoint := by
    refine F.bcPoint.heapKept hkZ hheZ (le_refl _) hzt (FO.w24.trans b0) ?_ ?_
    · rw [show s.getReg .x10 + 24 + 8 = s.getReg .x10 + 32 by rw [BitVec.add_assoc]; rfl, show s.getReg .x2 - 768 + 8 = s.getReg .x2 - 760 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]; exact FO.w32.trans b8
    · rw [show s.getReg .x10 + 24 + 16 = s.getReg .x10 + 40 by rw [BitVec.add_assoc]; rfl, show s.getReg .x2 - 768 + 16 = s.getReg .x2 - 752 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]; exact FO.w40.trans b16
  -- the point
  have NR := F.point
  have hP0 : t.getMem (s.getReg .x10 + 48) = z.getMem (s.getReg .x2 - 1320) := FO.w48.trans p0
  have hP8 : t.getMem (s.getReg .x10 + 48 + 8) = z.getMem (s.getReg .x2 - 1256) := by
    rw [show s.getReg .x10 + 48 + 8 = s.getReg .x10 + 56 by rw [BitVec.add_assoc]; rfl]; exact FO.w56.trans hx27
  have hP16 : t.getMem (s.getReg .x10 + 48 + 16) = z.getMem (s.getReg .x2 - 1144) := by
    rw [show s.getReg .x10 + 48 + 16 = s.getReg .x10 + 64 by rw [BitVec.add_assoc]; rfl]; exact FO.w64.trans p16
  have hpt : NewVecE s t (s.getReg .x10 + 48) (restValue s k state mem mf bf bv).point := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · show Buf t (t.getMem (s.getReg .x10 + 48 + 8)) ((t.getMem (s.getReg .x10 + 48)).toNat * 24) 8
      rw [hP8, hP0]; exact NewBuf.bufAt NR.buf hpre.heap hzt
    · show (t.getMem (s.getReg .x10 + 48 + 16)).toNat ≤ (t.getMem (s.getReg .x10 + 48)).toNat
      rw [hP16, hP0]; exact NR.le
    · show NewBuf s t (t.getMem (s.getReg .x10 + 48 + 8)) ((t.getMem (s.getReg .x10 + 48)).toNat * 24) 8
      rw [hP8, hP0]
      have hb := NR.buf
      simp only [NewBuf] at hb ⊢
      exact ⟨hb.1, hb.2.imp_right fun h' ↦ ⟨h'.1, by omega⟩⟩
    · show eListAt t (t.getMem (s.getReg .x10 + 48 + 8)) (t.getMem (s.getReg .x10 + 48 + 16)).toNat = _
      rw [hP8, hP16, eListAt_heapKept hkZ hheZ (le_refl _) NR.buf (by have := NR.le; omega)]
      exact NR.elems
  have hpIn : BufIn s t (vecPtr t (s.getReg .x10 + 48)) (24 * (vecLen t (s.getReg .x10 + 48)).toNat) := by
    show BufIn s t (t.getMem (s.getReg .x10 + 48 + 8)) (24 * (t.getMem (s.getReg .x10 + 48 + 16)).toNat)
    rw [hP8, hP16]
    have hb := NR.buf
    have hl := NR.le
    have pz := C.ptrs.point
    simp only [NewBuf] at hb
    refine ⟨hb.1, by omega, ?_⟩
    rcases hb.2 with h0 | h0
    · exact Or.inl (by rw [Nat.mul_eq_zero] at h0; omega)
    · exact Or.inr h0.1
  -- the totals
  have htot : NewVecE s t (s.getReg .x10 + 96) (restValue s k state mem mf bf bv).totals := by
    rw [restValue_totals]
    refine (Sd.totals.widen hsz).heapKept hkH hht (le_refl _) (by rw [hnt]) FO.w96 ?_ ?_
    · rw [show s.getReg .x10 + 96 + 8 = s.getReg .x10 + 104 by rw [BitVec.add_assoc]; rfl, show s.getReg .x2 - 632 + 8 = s.getReg .x2 - 624 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]; exact FO.w104
    · rw [show s.getReg .x10 + 96 + 16 = s.getReg .x10 + 112 by rw [BitVec.add_assoc]; rfl, show s.getReg .x2 - 632 + 16 = s.getReg .x2 - 616 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]; exact FO.w112
  -- the forms
  have hn : (w.getReg .x25).toNat = tables.length := by rw [C.rows0.x25]; exact hpre.tablesLen
  have hnp : 0 < (w.getReg .x25).toNat := hn ▸ tables_pos
  have ob := C.rows1.obuf
  have hPb : heapNext z ≤ (w.getReg .x23).toNat ∧
      (w.getReg .x23).toNat + (w.getReg .x25).toNat * 24 ≤ heapNext v := by
    have ob' := ob
    simp only [NewBuf] at ob'
    rcases ob'.2 with h0 | h0
    · omega
    · exact h0
  have hvt : heapNext v ≤ heapNext t := le_trans stVH.mono (by rw [hnt])
  obtain ⟨Mt, hrowT, hcellT, hformT⟩ := Sd.mat.keep Sd.inv.heap (by rw [hnt]) (Or.inr hPb.1)
    (fun x h1 h2 ↦ hkH x (by omega) h2)
  have fcap : t.getMem (s.getReg .x10 + 72) = w.getReg .x25 := FO.w72.trans (f0.trans C.rows1.cap)
  have fptr : t.getMem (s.getReg .x10 + 72 + 8) = w.getReg .x23 := by
    rw [show s.getReg .x10 + 72 + 8 = s.getReg .x10 + 80 by rw [BitVec.add_assoc]; rfl]; exact FO.w80.trans (f8.trans C.rows1.ptr)
  have flen : t.getMem (s.getReg .x10 + 72 + 16) = w.getReg .x25 := by
    rw [show s.getReg .x10 + 72 + 16 = s.getReg .x10 + 88 by rw [BitVec.add_assoc]; rfl]; exact FO.w88.trans hx25
  have hfok : VecOk t (s.getReg .x10 + 72) 24 8 := by
    refine ⟨?_, ?_⟩
    · show Buf t (t.getMem (s.getReg .x10 + 72 + 8)) ((t.getMem (s.getReg .x10 + 72)).toNat * 24) 8
      rw [fptr, fcap]; exact NewBuf.bufAt ob F.inv.heap hvt
    · show (t.getMem (s.getReg .x10 + 72 + 16)).toNat ≤ (t.getMem (s.getReg .x10 + 72)).toNat
      rw [flen, fcap]
  have hfval : formRowsAt t (vecPtr t (s.getReg .x10 + 72)) (vecLen t (s.getReg .x10 + 72)).toNat =
      (restValue s k state mem mf bf bv).forms := by
    show formRowsAt t (t.getMem (s.getReg .x10 + 72 + 8)) (t.getMem (s.getReg .x10 + 72 + 16)).toNat = _
    rw [fptr, flen, formRowsAt_keep (fun i hi ↦ (Sd.mat.rows i hi).2) hrowT hformT, Sd.forms,
      restValue_forms]
  have hfIn : BufIn s t (vecPtr t (s.getReg .x10 + 72)) (24 * (vecLen t (s.getReg .x10 + 72)).toNat) := by
    show BufIn s t (t.getMem (s.getReg .x10 + 72 + 8)) (24 * (t.getMem (s.getReg .x10 + 72 + 16)).toNat)
    rw [fptr, flen]
    exact ⟨ob.1, by omega, Or.inr (by omega)⟩
  have hfRows : ∀ i < (vecLen t (s.getReg .x10 + 72)).toNat,
      vecLen t (vecPtr t (s.getReg .x10 + 72) + BitVec.ofNat 64 (24 * i)) = 3 ∧
      ∀ j ≤ 3, BufIn s t (formPiece t (vecPtr t (s.getReg .x10 + 72)) i j).1
        (formPiece t (vecPtr t (s.getReg .x10 + 72)) i j).2 := by
    show ∀ i < (t.getMem (s.getReg .x10 + 72 + 16)).toNat,
      vecLen t (t.getMem (s.getReg .x10 + 72 + 8) + BitVec.ofNat 64 (24 * i)) = 3 ∧
      ∀ j ≤ 3, BufIn s t (formPiece t (t.getMem (s.getReg .x10 + 72 + 8)) i j).1
        (formPiece t (t.getMem (s.getReg .x10 + 72 + 8)) i j).2
    rw [fptr, flen]
    intro i hi
    refine ⟨(Mt.rows i hi).2, fun j hj ↦ ?_⟩
    rcases Nat.lt_or_ge j 3 with h3 | h3
    · simp only [formPiece, h3, ↓reduceIte]
      show BufIn s t (vecPtr t (cellAt t (rowAt (w.getReg .x23) i) j))
        (48 * (vecLen t (cellAt t (rowAt (w.getReg .x23) i) j)).toNat)
      have fok := Mt.forms i hi j h3
      have bl := Sd.below i hi j h3
      have er : vecPtr t (rowAt (w.getReg .x23) i) = vecPtr h (rowAt (w.getReg .x23) i) := by
        simpa [vecPtr] using hrowT i hi 1 (by omega)
      have ec : cellAt t (rowAt (w.getReg .x23) i) j = cellAt h (rowAt (w.getReg .x23) i) j := by
        simp only [cellAt, er]
      have ep : vecPtr t (cellAt h (rowAt (w.getReg .x23) i) j) =
          vecPtr h (cellAt h (rowAt (w.getReg .x23) i) j) := by
        simpa [vecPtr] using hcellT i hi j h3 1 (by omega)
      have el : vecLen t (cellAt h (rowAt (w.getReg .x23) i) j) =
          vecLen h (cellAt h (rowAt (w.getReg .x23) i) j) := by
        simpa [vecLen] using hcellT i hi j h3 2 (by omega)
      have vb : Buf t _ _ 8 := fok.vec.raw
      have vl := fok.vec.len
      simp only [Buf] at vb
      refine ⟨vb.1, by rw [ec, ep, el, hnt]; exact bl, ?_⟩
      by_cases hl0 : (vecLen t (cellAt t (rowAt (w.getReg .x23) i) j)).toNat = 0
      · exact Or.inl (by omega)
      · refine Or.inr (le_trans hsz (Mt.fresh i hi j h3.le _ ((piece_form h3).mpr ?_)))
        simp only [Layout.formBuf, Within]
        omega
    · obtain rfl : j = 3 := by omega
      simp only [formPiece, Nat.lt_irrefl, ↓reduceIte]
      show BufIn s t (vecPtr t (rowAt (w.getReg .x23) i)) (24 * (vecLen t (rowAt (w.getReg .x23) i)).toNat)
      have rv := (Mt.rows i hi).1
      have l3 := (Mt.rows i hi).2
      have vb : Buf t _ _ 8 := rv.raw
      have vl := rv.len
      rw [l3] at vl ⊢
      have e3 : (3 : Word).toNat = 3 := rfl
      rw [e3] at vl ⊢
      simp only [Buf] at vb
      refine ⟨vb.1, by rcases vb.2 with h0 | h0 <;> omega,
        Or.inr (le_trans hsz (Mt.fresh i hi 3 (le_refl _) _ (piece_row.mpr ?_)))⟩
      simp only [Layout.formVecBuf, Within]
      omega
  have hfAp : ∀ i < (vecLen t (s.getReg .x10 + 72)).toNat, ∀ j ≤ 3,
      Apart (formPiece t (vecPtr t (s.getReg .x10 + 72)) i j).1
        (formPiece t (vecPtr t (s.getReg .x10 + 72)) i j).2
        (vecPtr t (s.getReg .x10 + 72)) (24 * (vecLen t (s.getReg .x10 + 72)).toNat) ∧
      ∀ i' < (vecLen t (s.getReg .x10 + 72)).toNat, ∀ j' ≤ 3, (i ≠ i' ∨ j ≠ j') →
        Apart (formPiece t (vecPtr t (s.getReg .x10 + 72)) i j).1
          (formPiece t (vecPtr t (s.getReg .x10 + 72)) i j).2
          (formPiece t (vecPtr t (s.getReg .x10 + 72)) i' j').1
          (formPiece t (vecPtr t (s.getReg .x10 + 72)) i' j').2 := by
    show ∀ i < (t.getMem (s.getReg .x10 + 72 + 16)).toNat, ∀ j ≤ 3,
      Apart (formPiece t (t.getMem (s.getReg .x10 + 72 + 8)) i j).1
        (formPiece t (t.getMem (s.getReg .x10 + 72 + 8)) i j).2
        (t.getMem (s.getReg .x10 + 72 + 8)) (24 * (t.getMem (s.getReg .x10 + 72 + 16)).toNat) ∧
      ∀ i' < (t.getMem (s.getReg .x10 + 72 + 16)).toNat, ∀ j' ≤ 3, (i ≠ i' ∨ j ≠ j') →
        Apart (formPiece t (t.getMem (s.getReg .x10 + 72 + 8)) i j).1
          (formPiece t (t.getMem (s.getReg .x10 + 72 + 8)) i j).2
          (formPiece t (t.getMem (s.getReg .x10 + 72 + 8)) i' j').1
          (formPiece t (t.getMem (s.getReg .x10 + 72 + 8)) i' j').2
    rw [fptr, flen]
    intro i hi j hj
    refine ⟨apart_of_disjoint fun x hx hx' ↦ Mt.outer i hi j hj x (formPiece_piece Mt hi hj hx) ?_,
      fun i' hi' j' hj' hne ↦ apart_of_disjoint fun x hx hx' ↦ Mt.apart i hi j hj i' hi' j' hj' hne x
        (formPiece_piece Mt hi hj hx) (formPiece_piece Mt hi' hj' hx')⟩
    simpa [Nat.mul_comm] using hx'
  have hfTag : ∀ i < (vecLen t (s.getReg .x10 + 72)).toNat,
      ∀ j < (vecLen t (vecPtr t (s.getReg .x10 + 72) + BitVec.ofNat 64 (24 * i))).toNat,
      ∀ q < (vecLen t (vecPtr t (vecPtr t (s.getReg .x10 + 72) + BitVec.ofNat 64 (24 * i)) +
          BitVec.ofNat 64 (24 * j))).toNat,
        (t.getMem (vecPtr t (vecPtr t (vecPtr t (s.getReg .x10 + 72) + BitVec.ofNat 64 (24 * i)) +
          BitVec.ofNat 64 (24 * j)) + BitVec.ofNat 64 (48 * q))).toNat ≤ 2 := by
    show ∀ i < (t.getMem (s.getReg .x10 + 72 + 16)).toNat,
      ∀ j < (vecLen t (t.getMem (s.getReg .x10 + 72 + 8) + BitVec.ofNat 64 (24 * i))).toNat,
      ∀ q < (vecLen t (vecPtr t (t.getMem (s.getReg .x10 + 72 + 8) + BitVec.ofNat 64 (24 * i)) +
          BitVec.ofNat 64 (24 * j))).toNat,
        (t.getMem (vecPtr t (vecPtr t (t.getMem (s.getReg .x10 + 72 + 8) + BitVec.ofNat 64 (24 * i)) +
          BitVec.ofNat 64 (24 * j)) + BitVec.ofNat 64 (48 * q))).toNat ≤ 2
    rw [fptr, flen]
    intro i hi j hj q hq
    have l3 := (Mt.rows i hi).2
    rw [show rowAt (w.getReg .x23) i = w.getReg .x23 + BitVec.ofNat 64 (24 * i) from rfl] at l3
    rw [l3, show (3 : Word).toNat = 3 from rfl] at hj
    exact (Mt.forms i hi j hj).tags q hq
  -- the transcript
  have frZT : DFrame z t fun a ↦ Within a (s.getReg .x2 - 4544) 4440 ∨ Within a nextAddr 8 ∨
      (heapNext s ≤ a.toNat ∧ a.toNat < heapEnd) ∨ Within a (s.getReg .x10) 120 := by
    refine (stZH.frame.mono fun a ha ↦ ?_).trans frHT fun a ha ↦ ?_
    · rcases ha with ha | ha | ha | ha
      · simp only [RowsW, SetupW, LoopW] at ha
        rcases ha with ((ha | ha | ha) | (ha | ha)) | (ha | ha | ha | ha | ha | ha | ha | ha) <;>
          first
          | exact Or.inl (by addr_omega [ha, hb1])
          | exact Or.inr (Or.inr (Or.inl ⟨by omega, ha.2⟩))
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr (Or.inl ha)
      · simp only [Fresh] at ha
        exact Or.inr (Or.inr (Or.inl ⟨by omega, by simp only [heapNext, heapEnd] at hht ha ⊢; omega⟩))
    · rcases ha with ha | ha
      · exact Or.inr (Or.inr (Or.inr ha))
      · exact Or.inl (by addr_omega [ha, hb1])
  exact ⟨hcapNe, ⟨⟨hcok, hcbuf, hclaims, hcvec⟩, hbp, hpt, ⟨hfok, hfval⟩, htot, hcIn, hcp, hpIn,
    hfIn, hfRows, hfAp, hfTag⟩, Inv.transcriptW hpre F.inv frZT hT'⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
