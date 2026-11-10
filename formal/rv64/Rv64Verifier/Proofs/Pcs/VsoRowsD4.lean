import Rv64Verifier.Proofs.Pcs.VsoRowsD3

/-!
# `verify_stacked_opening`'s level loop: a deeper level's rows, `dot` and the row's value

From `0x8000b1c8` (`RowCopied`): `dot(ext_row(row), kernel)` into `S - 384` (`callDot`), then
`0x8000b1dc` stores it as row `j`'s value at `O + 24 j` and steps to the next row (`DeepAt`) or,
after the last, to `0x8000b42c` (`Rowed`): `rowFinish`. `rowStep` is a whole row, from the loop's
head.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso.RowsD
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- What the rows write stays within what the function may write. -/
theorem rowW_inv {s k u r : MachineState} {nx : Word} (hpre : VsoPre s)
    (hk : InvR s k (k.getMem nextAddr)) (hu : InvR s u nx) (hfr : DFrame u r (RowW s k r))
    (hle : nx.toNat ≤ (r.getMem nextAddr).toNat) (hend : (r.getMem nextAddr).toNat ≤ heapEnd)
    (hsp : r.getReg .x2 = u.getReg .x2) : InvR s r (r.getMem nextAddr) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hkm := hk.mono
  refine Inv.step' hpre hu hfr (fun a ha ↦ ?_) (fun a ha ↦ ?_) rfl hle hend hsp
  · rcases ha with ha | ha | ha | ha | ha | ha | ⟨h1, h2⟩
    · exact frame_wr hpre (by addr_omega [ha, hb])
    · exact frame_wr hpre (by addr_omega [ha, hb])
    · exact frame_wr hpre (by addr_omega [ha, hb])
    · exact frame_wr hpre (by addr_omega [ha, hb])
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ⟨by simp only [heapNext] at h1; omega, h2⟩))
  · rcases ha with ha | ha | ha | ha | ha | ha | ⟨-, h2⟩
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb, hnx]
    · simp only [heapNext] at h2; addr_omega [h2, hend, hb]

/-- The kernel: aligned, in the heap below `heapNext k`, holding `eq_kernel`'s values. -/
theorem kerFacts {s t' k : MachineState} {lf : List E} (hk : Kerneled s t' k lf) :
    (vecPtr k (s.getReg .x2 - 536)).toNat % 8 = 0 ∧
      ((vecLen k (s.getReg .x2 - 536)).toNat = 0 ∨
        heapStart ≤ (vecPtr k (s.getReg .x2 - 536)).toNat ∧
        (vecPtr k (s.getReg .x2 - 536)).toNat + 24 * (vecLen k (s.getReg .x2 - 536)).toNat ≤
          heapNext k) ∧
      eListAt k (vecPtr k (s.getReg .x2 - 536)) (vecLen k (s.getReg .x2 - 536)).toNat =
        Model.eqKernelRust lf := by
  have hv := hk.ker.vec
  have hraw := hv.raw
  have hlen := hv.len
  simp only [RawVecOk, Buf] at hraw
  refine ⟨hraw.1, ?_, hk.ker.elems⟩
  rcases hraw.2 with h0 | h0
  · exact Or.inl (by omega)
  · exact Or.inr ⟨h0.1, by omega⟩

theorem rowsD_eListAt_snoc (t : MachineState) (p : Word) (n : ℕ) :
    eListAt t p (n + 1) = eListAt t p n ++ [eAt t (p + BitVec.ofNat 64 (24 * n))] := by
  simp only [eListAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem take_succ_map {ws : List (List K)} {j : ℕ} (hj : j < ws.length) (f : List K → E) :
    (ws.take (j + 1)).map f = (ws.take j).map f ++ [f ws[j]] := by
  rw [List.take_succ_eq_append_getElem hj, List.map_append, List.map_singleton]

/-- **`dot` and the row's value**: from `0x8000b1c8` to the next row's head or `0x8000b42c`. -/
theorem rowFinish (hDt : MultilinearContracts.DotSpec) {s t' k u w : MachineState} {lf : List E}
    {ws : List (List K)} {O B : Word} {j : ℕ} (C : DCtx s t' k lf ws)
    (hu : DeepAt s k u ws (Model.eqKernelRust lf) O j) (hj : j < ws.length)
    (hw : RowCopied s k u w (sliceP s k j) (sliceL s k j) B) :
    ∃ r, Reaches Image.code w r ∧ (FailR s r ∨
      (j + 1 < ws.length ∧ DeepAt s k r ws (Model.eqKernelRust lf) O (j + 1)) ∨
      (j + 1 = ws.length ∧ Rowed s k r (ws.map (rowF (Model.eqKernelRust lf))))) := by
  have hpre := C.pre
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hk := C.ker
  obtain ⟨hKa, hKr, hKe⟩ := kerFacts hk
  have hku := hu.mono
  have huw := hw.mono
  have hhw := hw.heap
  have hhwi := hhw.hi
  have hkh := hk.heap
  have hkhi := hkh.hi
  have hkl := hkh.lo
  have hhul := hu.heap.lo
  have hkm := hk.inv.mono
  have hn := C.leaves.n
  set n := ws.length with hnd
  set L := sliceL s k j with hLd
  set ker := Model.eqKernelRust lf with hkd
  have hLlt := L.isLt
  have hm : (BitVec.ofNat 64 (L.toNat / 3)).toNat = L.toNat / 3 := by
    rw [BitVec.toNat_ofNat]; omega
  obtain ⟨hOa, hOk, hOu⟩ := hu.buf
  simp only [heapStart, heapEnd] at hhul hhwi hkhi hkl
  have hO : Region O (24 * n) := heap_region (by omega) (by simp only [heapEnd]; omega) hOa
  have hOb := Region.bounds hO
  -- the frame to `dot`'s call
  have frW : DFrame u w (RowW s k w) := hw.fr.mono fun a ha ↦ by
    rcases ha with ha | ha | ha | ⟨h1, h2⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, h2⟩)))))
  have frKW : DFrame k w (RowW s k w) :=
    (hu.fr.mono fun _ ha ↦ rowW_mono huw ha).trans frW fun _ h ↦ h
  have invW : InvR s w (w.getMem nextAddr) :=
    rowW_inv hpre hk.inv hu.inv frW huw hhw.hi (hw.sp.trans hu.sp.symm)
  -- `0x8000b1c8`
  have hsp := hw.sp
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000b1c8_spec hw.pc (by
    rv_eval [hsp]; valid_access hst.valid [hb])
  have k₁ := b8000b1c8_keeps h₁
  have m₁ := b8000b1c8_mem_same h₁
  have inv₁ : InvR s t₁ (w.getMem nextAddr) := Inv.same' invW m₁ (k₁ .x2 (by decide))
  have e784 : w.getMem (s.getReg .x2 - 784) = vecPtr k (s.getReg .x2 - 536) := by
    rw [← hu.m784]
    exact hw.fr _ fun i hi hw' ↦ by
      rcases hw' with h | h | h | ⟨-, h⟩
      · addr_omega [h, hi, hb]
      · addr_omega [h, hi, hb]
      · addr_omega [h, hi, hb, hnx]
      · addr_omega [h, hi, hb, hhwi]
  have x11₁ : t₁.getReg .x11 = B := by rw [k₁ .x11 (by decide), hw.x11]
  have x12₁ : t₁.getReg .x12 = BitVec.ofNat 64 (L.toNat / 3) := by
    rw [k₁ .x12 (by decide), hw.x12]
  have x13₁ : t₁.getReg .x13 = vecPtr k (s.getReg .x2 - 536) := by
    rw [b8000b1c8_x13 h₁, hsp, show s.getReg .x2 - 1040 + 256 = s.getReg .x2 - 784 by rv_eval [],
      e784]
  have x14₁ : t₁.getReg .x14 = vecLen k (s.getReg .x2 - 536) := by
    rw [b8000b1c8_x14 h₁, hw.regs .x21 (by simp), hu.x21]
  obtain ⟨v, r₂, hv₂⟩ := callDot hDt hpre inv₁ (b8000b1c8_pc h₁)
    (by rw [b8000b1c8_x10 h₁, hsp]; rv_eval [])
    (by
      rw [x11₁, x12₁, hm]
      rcases hw.bnew with h0 | ⟨h1, h2⟩
      · exact Or.inl h0
      · exact Or.inr ⟨heap_region (by omega) (by simp only [heapEnd]; omega) hw.bal,
          by simp only [heapEnd]; omega⟩)
    (by
      rw [x13₁, x14₁]
      rcases hKr with h0 | ⟨h1, h2⟩
      · exact Or.inl h0
      · simp only [heapStart] at h1
        exact Or.inr ⟨heap_region (by omega) (by simp only [heapEnd]; omega) hKa,
          by simp only [heapEnd]; omega⟩)
  rcases hv₂ with hd | ⟨pc₂, pr₂, hlen, hval, fr₂⟩
  · exact ⟨v, r₁.trans r₂, Or.inl (Or.inl hd)⟩
  rw [x12₁, x14₁] at hlen
  have hmK : L.toNat / 3 = (vecLen k (s.getReg .x2 - 536)).toNat := by rw [← hm, hlen]
  have hval' : eAt v (s.getReg .x2 - 384) = rowF ker ws[j] := by
    rw [hval, x11₁, x12₁, x13₁, hm]
    have e1 : eListAt t₁ B (L.toNat / 3) = Model.Pcs.extRowRust ws[j] := by
      rw [rowWords C hj, ← hw.elems]; simp only [eListAt, eAt, m₁]
    have e2 : eListAt t₁ (vecPtr k (s.getReg .x2 - 536)) (L.toNat / 3) = ker := by
      rw [hmK, ← hKe]
      have e3 : eListAt t₁ (vecPtr k (s.getReg .x2 - 536)) (vecLen k (s.getReg .x2 - 536)).toNat =
          eListAt w (vecPtr k (s.getReg .x2 - 536)) (vecLen k (s.getReg .x2 - 536)).toNat := by
        simp only [eListAt, eAt, m₁]
      rw [e3]
      rcases hKr with h0 | ⟨h1, h2⟩
      · rw [h0]; rfl
      · exact frKW.eListAt fun i hi hw' ↦ low_notRowW hpre hkh.hi (by addr_omega [h1, h2, hi]) hw'
    rw [e1, e2]; rfl
  -- `0x8000b1dc`: the value stored at `O + 24 j`
  have sp₂ : v.getReg .x2 = s.getReg .x2 - 1040 := by
    rw [pr₂.reg .x2, k₁ .x2 (by decide), hsp]
  have rv (q : Reg) (hq : q ∈ [Reg.x9, .x18, .x20, .x21, .x23, .x24, .x25, .x26, .x27]) :
      v.getReg q = u.getReg q := by
    have hq' := hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
    rw [← hw.regs q hq]
    rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (pr₂.reg _).trans (k₁ _ (by decide))
  have x25v : v.getReg .x25 = O := (rv .x25 (by simp)).trans hu.x25
  have x27v : v.getReg .x27 = BitVec.ofNat 64 j := (rv .x27 (by simp)).trans hu.x27
  have x18v : v.getReg .x18 = BitVec.ofNat 64 j := (rv .x18 (by simp)).trans hu.x18
  have ea : v.getReg .x25 + (v.getReg .x27 * 16 + v.getReg .x27 * 8) =
      O + BitVec.ofNat 64 (24 * j) := by
    rw [x25v, x27v]; addr_omega [hOb, hj]
  obtain ⟨r, r₃, h₃⟩ := Sym.BlockSpec.reaches b8000b1dc_spec
    (by rw [pc₂, returnAddress_eq, b8000b1c8_x1 h₁]; rfl) (by
      rv_eval [sp₂, x25v, x27v]
      and_intros <;> first
        | exact Region.valid hO (by addr_omega [hOb, hj]) (by addr_omega [hOb, hj])
            (by addr_omega [hOb, hj])
        | valid_access hst.valid [hb]
        | addr_omega [hOb, hj, hb, hhwi, hOu, huw])
  have k₃ := b8000b1dc_keeps h₃
  have X : DFrame v r (Within · (O + BitVec.ofNat 64 (24 * j)) 24) :=
    (holds_dframe h₃).mono fun a ⟨q, hq, hw'⟩ ↦ by
      simp only [b8000b1dc, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> rv_eval [x25v, x27v] at hw' <;> addr_omega [hw', hOb, hj]
  have m0 := b8000b1dc_m0 h₃
  have m8 := b8000b1dc_m1 h₃
  have m16 := b8000b1dc_m2 h₃
  rw [ea] at m0 m8 m16
  have eR : eAt r (O + BitVec.ofNat 64 (24 * j)) = eAt v (s.getReg .x2 - 384) := by
    simp only [eAt]
    rw [m0, m8, m16, sp₂, show s.getReg .x2 - 1040 + 656 = s.getReg .x2 - 384 by rv_eval [],
      show s.getReg .x2 - 1040 + 664 = s.getReg .x2 - 384 + 8 by rv_eval [],
      show s.getReg .x2 - 1040 + 672 = s.getReg .x2 - 384 + 16 by rv_eval []]
  have nv : v.getMem nextAddr = w.getMem nextAddr := by
    rw [fr₂ nextAddr fun i hi hw' ↦ by rcases hw' with h | h <;> addr_omega [h, hi, hb, hnx], m₁]
  have nr : r.getMem nextAddr = v.getMem nextAddr :=
    X nextAddr fun i hi hw' ↦ by addr_omega [hw', hi, hOb, hj, hOu, huw, hhwi]
  have hnr : heapNext r = heapNext w := by simp only [heapNext, nr, nv]
  have hur : heapNext u ≤ heapNext r := by rw [hnr]; exact huw
  -- the frame from the loop's head
  have Y : DFrame u r fun a ↦ Within a (s.getReg .x2 - 384) 24 ∨
      Within a (s.getReg .x2 - 2464) 1424 ∨ Within a nextAddr 8 ∨ Fresh u r a ∨
      Within a (O + BitVec.ofNat 64 (24 * j)) 24 := by
    have d1 : DFrame u w fun a ↦ Within a (s.getReg .x2 - 384) 24 ∨
        Within a (s.getReg .x2 - 2464) 1424 ∨ Within a nextAddr 8 ∨ Fresh u r a ∨
        Within a (O + BitVec.ofNat 64 (24 * j)) 24 := hw.fr.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ⟨h1, h2⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, by rw [hnr]; exact h2⟩)))
    have d2 := (d1.trans (DFrame.of_same m₁ _) fun _ h ↦ h).trans fr₂ fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
    exact d2.trans X fun a ha ↦ Or.inr (Or.inr (Or.inr (Or.inr ha)))
  have frR : DFrame u r (RowW s k r) := Y.mono fun a ha ↦ by
    rcases ha with ha | ha | ha | ⟨h1, h2⟩ | ha
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, h2⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨by addr_omega [ha, hOk, hOb, hj], by addr_omega [ha, hOu, hur, hOb, hj]⟩)))))
  have sp₃ : r.getReg .x2 = s.getReg .x2 - 1040 := (k₃ .x2 (by decide)).trans sp₂
  have invR : InvR s r (r.getMem nextAddr) :=
    rowW_inv hpre hk.inv hu.inv frR hur (by have := hhw.hi; rw [← hnr] at this; exact this)
      (sp₃.trans hu.sp.symm)
  have frK : DFrame k r (RowW s k r) :=
    (hu.fr.mono fun _ ha ↦ rowW_mono hur ha).trans frR fun _ h ↦ h
  have val : eListAt r O (j + 1) = (ws.take (j + 1)).map (rowF ker) := by
    rw [rowsD_eListAt_snoc, take_succ_map hj, eR, hval', ← hu.value]
    congr 1
    exact Y.eListAt fun i hi hw' ↦ by
      rcases hw' with h | h | h | ⟨h1, -⟩ | h
      · addr_omega [h, hi, hOb, hj, hb, hOu, huw, hhwi]
      · addr_omega [h, hi, hOb, hj, hb, hOu, huw, hhwi]
      · addr_omega [h, hi, hOb, hj, hOu, huw, hhwi]
      · addr_omega [h1, hi, hOb, hj, hOu]
      · addr_omega [h, hi, hOb, hj]
  have x18r : r.getReg .x18 = BitVec.ofNat 64 (j + 1) := by
    rw [b8000b1dc_x18 h₃, x18v]; addr_omega [hOb, hj]
  have x27r : r.getReg .x27 = BitVec.ofNat 64 (j + 1) := by
    rw [b8000b1dc_x27 h₃, x27v]; addr_omega [hOb, hj]
  have x20v : v.getReg .x20 = k.getReg .x20 := (rv .x20 (by simp)).trans hu.x20
  have rk (q : Reg) (hq : q ∈ [Reg.x9, .x20, .x21, .x23, .x24, .x25, .x26]) :
      r.getReg q = u.getReg q := by
    have hq' := hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (k₃ _ (by decide)).trans (rv _ (by simp))
  have m784 : r.getMem (s.getReg .x2 - 784) = vecPtr k (s.getReg .x2 - 536) := by
    rw [← hu.m784]
    exact Y _ fun i hi hw' ↦ by
      rcases hw' with h | h | h | ⟨-, h⟩ | h
      · addr_omega [h, hi, hb]
      · addr_omega [h, hi, hb]
      · addr_omega [h, hi, hb, hnx]
      · addr_omega [h, hi, hb, hhwi, hnr]
      · addr_omega [h, hi, hb, hOb, hj, hOu, huw, hhwi]
  have heapR : HeapOk r := ⟨by rw [hnr]; exact hhw.lo, by rw [hnr]; exact hhw.hi⟩
  have hOr : O.toNat + 24 * n ≤ heapNext r := by omega
  have hnk : (k.getReg .x20).toNat = n := hn
  by_cases hlast : j + 1 = n
  · have hpc₃ := b8000b1dc_pc_taken h₃ (by
      rw [x18v, x20v]; apply BitVec.eq_of_toNat_eq; rw [hnk, ← hlast]; addr_omega [hOb, hj])
    refine ⟨r, r₁.trans (r₂.trans r₃), Or.inr (Or.inr ⟨hlast, {
      pc := hpc₃
      sp := sp₃
      regs := fun q hq ↦ by
        have hq' := hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
        rw [← hu.regs q hq]
        rcases hq' with rfl | rfl | rfl <;> exact rk _ (by simp)
      inv := invR
      heap := heapR
      mono := hku.trans hur
      value := by
        rw [k₃ .x25 (by decide), x25v, x27r,
          show (BitVec.ofNat 64 (j + 1)).toNat = j + 1 by rw [BitVec.toNat_ofNat]; omega, val,
          hlast, List.take_of_length_le (Nat.le_refl _)]
      buf := by
        rw [k₃ .x25 (by decide), x25v, x27r,
          show (BitVec.ofNat 64 (j + 1)).toNat = j + 1 by rw [BitVec.toNat_ofNat]; omega, hlast]
        exact ⟨hOa, Or.inr ⟨hOk, hOr⟩⟩
      fr := frK }⟩)⟩
  · have hpc₃ := b8000b1dc_pc_not_taken h₃ (by
      rw [x18v, x20v]; intro he
      have := congrArg BitVec.toNat he
      rw [hnk] at this; addr_omega [this, hOb, hj, hlast])
    refine ⟨r, r₁.trans (r₂.trans r₃), Or.inr (Or.inl ⟨by omega, {
      pc := hpc₃
      sp := sp₃
      x18 := x18r
      x27 := x27r
      x20 := (rk .x20 (by simp)).trans hu.x20
      x21 := (rk .x21 (by simp)).trans hu.x21
      x24 := (rk .x24 (by simp)).trans hu.x24
      x25 := (rk .x25 (by simp)).trans hu.x25
      regs := fun q hq ↦ by
        have hq' := hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
        rw [← hu.regs q hq]
        rcases hq' with rfl | rfl | rfl <;> exact rk _ (by simp)
      m784 := m784
      inv := invR
      heap := heapR
      mono := hku.trans hur
      buf := ⟨hOa, hOk, hOr⟩
      value := val
      fr := frK }⟩)⟩

end Rv64Verifier.Proofs.Pcs.Vso.RowsD
