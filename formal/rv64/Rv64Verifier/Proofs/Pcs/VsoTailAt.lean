import Rv64Verifier.Proofs.Pcs.VsoTailAtS
import Rv64Verifier.Proofs.Pcs.VsoTailAtP

/-!
# `verify_stacked_opening`'s level tail: `AtR`, what the tail reads at the rows' end

`atR` gathers it from the opening, the queries, `lam`, the Merkle checks, the slices, `eq_kernel`
and the rows, through the frames `Zh`, `Zt`, `Zu`, `X1` and `Zm`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol

section
variable {s : MachineState} {x : LCtx} {h t u v w m t' k r : MachineState} {ℓ : ℕ}
  {Wl : Model.Pcs.WhirLocals} {lf q res : List E}
  {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
  {rows : List E}

/-- The queries' count fits. -/
theorem Merkled.qlen (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs) :
    qs.length < 2 ^ 61 := by
  have hb := hm.qo.vec.buf
  have hhi := (hm.qo.inv.heap hpre.heap).hi
  simp only [NewBuf, heapEnd] at hb hhi
  rcases hb.2 with h0 | h0 <;> omega

/-- `lam`'s powers. -/
theorem Merkled.pwR (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) (hr : Rowed s k r rows) :
    VecOk r (s.getReg .x2 - 488) 24 8 ∧
    vecEs r (s.getReg .x2 - 488) = Verifier.powers (eAt w (s.getReg .x2 - 384)) qs.length ∧
    vecLen r (s.getReg .x2 - 488) = BitVec.ofNat 64 qs.length ∧
    ((vecLen r (s.getReg .x2 - 488)).toNat = 0 ∨
      heapNext u ≤ (vecPtr r (s.getReg .x2 - 488)).toNat ∧
      (vecPtr r (s.getReg .x2 - 488)).toNat + (vecCap r (s.getReg .x2 - 488)).toNat * 24 ≤
        heapNext w) := by
  have hb := bounds hpre
  obtain ⟨T0, hl⟩ := hm.lo
  obtain ⟨F1, mwr⟩ := hm.frW hpre hsl hk hr
  have hhi := hr.heap.hi
  simp only [heapEnd] at hhi
  have hsv : heapNext s ≤ heapNext v := hm.qo.inv.mono
  have muv := hm.qo.mono
  have mvw := hl.mono
  have hql := hm.qlen hpre
  have ec : vecCap r (s.getReg .x2 - 488) = vecCap w (s.getReg .x2 - 488) :=
    hm.kW hpre hsl hk hr (o := 488) (by unfold x1Free; decide)
  have ep : vecPtr r (s.getReg .x2 - 488) = vecPtr w (s.getReg .x2 - 488) := by
    simp only [vecPtr]
    rw [show s.getReg .x2 - 488 + 8 = s.getReg .x2 - 480 by rv_eval []]
    exact hm.kW hpre hsl hk hr (o := 480) (by unfold x1Free; decide)
  have el : vecLen r (s.getReg .x2 - 488) = vecLen w (s.getReg .x2 - 488) := by
    simp only [vecLen]
    rw [show s.getReg .x2 - 488 + 16 = s.getReg .x2 - 472 by rv_eval []]
    exact hm.kW hpre hsl hk hr (o := 472) (by unfold x1Free; decide)
  have hlen : vecLen w (s.getReg .x2 - 488) = BitVec.ofNat 64 qs.length := hl.len.trans hm.qo.x26
  have hln : (BitVec.ofNat 64 qs.length).toNat = qs.length :=
    by rw [BitVec.toNat_ofNat]; omega
  have hfr := hl.fresh
  rw [hm.qo.x26, hln] at hfr
  have hraw := hl.vec.raw
  simp only [RawVecOk, Buf] at hraw
  simp only [NewBuf] at hfr
  have hvl := hl.vec.len
  rw [hlen, hln] at hvl
  refine ⟨⟨?_, by rw [el, ec]; exact hl.vec.len⟩, ?_, by rw [el, hlen], ?_⟩
  · simp only [RawVecOk, Buf]
    rw [ep, ec]
    exact ⟨hraw.1, hraw.2.imp id fun h' ↦ ⟨h'.1, by omega⟩⟩
  · rw [hl.lam, show qs.length = (v.getReg .x26).toNat by rw [hm.qo.x26, hln], ← hl.elems]
    simp only [vecEs]
    rw [ep, el]
    refine F1.eListAt fun j hj ↦ X1.heap hpre hr.heap ?_ ?_ mwr
    · rw [hlen, hln] at hj
      rcases hfr.2 with h0 | h0
      · omega
      · addr_omega [h0, hj, hhi, hsv, mwr]
    · rw [hlen, hln] at hj
      rcases hfr.2 with h0 | h0
      · omega
      · addr_omega [h0, hj, hhi, hsv, mwr]
  · rw [el, hlen, hln, ep, ec]
    rcases hfr.2 with h0 | h0
    · exact Or.inl (by omega)
    · refine Or.inr ⟨by omega, ?_⟩
      rcases hraw.2 with h1 | h1
      · omega
      · exact h1.2

/-- The queries' `Vec`, as the weight reads it. -/
theorem Merkled.qR (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) (hr : Rowed s k r rows) :
    r.getMem (s.getReg .x2 - 1000) = BitVec.ofNat 64 qs.length ∧
    (r.readWords (r.getMem (s.getReg .x2 - 824)) qs.length = qs ∧
      (r.getMem (s.getReg .x2 - 824)).toNat % 8 = 0 ∧ (qs.length = 0 ∨
        heapNext u ≤ (r.getMem (s.getReg .x2 - 824)).toNat ∧
        (r.getMem (s.getReg .x2 - 824)).toNat + 8 * qs.length ≤ heapNext w)) ∧
    r.getReg .x26 = BitVec.ofNat 64 qs.length := by
  have hb := bounds hpre
  obtain ⟨T0, hl⟩ := hm.lo
  obtain ⟨F1, mwr⟩ := hm.frW hpre hsl hk hr
  have hhi := hr.heap.hi
  simp only [heapEnd] at hhi
  have hsu : heapNext s ≤ heapNext u := hm.op.inv.mono
  have muv := hm.qo.mono
  have mvw := hl.mono
  have hql := hm.qlen hpre
  have hln : (BitVec.ofNat 64 qs.length).toNat = qs.length := by rw [BitVec.toNat_ofNat]; omega
  have w26 : w.getReg .x26 = BitVec.ofNat 64 qs.length :=
    (hl.regs .x26 (by decide)).trans hm.qo.x26
  have e824 : r.getMem (s.getReg .x2 - 824) = vecPtr v (s.getReg .x2 - 464) :=
    (hm.kW hpre hsl hk hr (o := 824) (by unfold x1Free; decide)).trans (hl.qp.trans hm.qo.x1)
  have hbuf := hm.qo.vec.buf
  simp only [NewBuf] at hbuf
  refine ⟨(hm.kM hpre hsl hk hr (o := 1000) (by unfold zmFree; decide)).trans
      (hm.mo.s19.trans ((hl.regs .x19 (by decide)).trans (hm.qo.x19.trans hm.qo.vec.cap))),
    ⟨?_, by rw [e824]; exact hbuf.1, ?_⟩, ?_⟩
  · have hq := hm.qsw
    rw [w26, hln, hl.qp, hm.qo.x1] at hq
    have e : r.readWords (vecPtr v (s.getReg .x2 - 464)) qs.length =
        w.readWords (vecPtr v (s.getReg .x2 - 464)) qs.length := by
      refine DFrame.readWords' F1 (fun a hX hin ↦ ?_) ?_
      · rcases hbuf.2 with h0 | h0
        · simp only [Within] at hin; omega
        · exact X1.heap hpre hr.heap (by addr_omega [hin, h0, hsu])
            (by addr_omega [hin, h0, mvw]) mwr hX
      · rcases hbuf.2 with h0 | h0
        · omega
        · omega
    rw [e824, e, hq]
  · rw [e824]
    rcases hbuf.2 with h0 | h0
    · exact Or.inl (by omega)
    · exact Or.inr ⟨h0.1, by omega⟩
  · rw [hr.regs .x26 (by decide), hk.regs .x26 (by decide), hsl.regs .x26 (by decide),
      hm.mo.regs .x26 (by decide), w26]

/-- `FP` in `s1`. -/
theorem Merkled.x9R (_hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) (hr : Rowed s k r rows) :
    r.getReg .x9 = x.FP := by
  obtain ⟨T0, hl⟩ := hm.lo
  rw [hr.regs .x9 (by decide), hk.regs .x9 (by decide), hsl.regs .x9 (by decide),
    hm.mo.regs .x9 (by decide), hl.regs .x9 (by decide), hm.qo.x9, hm.op.x9]

/-- What `X0` keeps of the frame. -/
theorem X0.slot {u w : MachineState} (hpre : VsoPre s) (hw : HeapOk w) {o : ℕ}
    (ho : 8 ≤ o ∧ o ≤ 1040 ∧ o % 8 = 0 ∧ (o < 960 ∨ 968 < o) ∧ (o < 824 ∨ 832 < o) ∧
      (o < 472 ∨ 488 < o) ∧ (o < 440 ∨ 464 < o) ∧ (o < 360 ∨ 384 < o)) :
    ∀ i < 8, ¬ X0 s u w (s.getReg .x2 - BitVec.ofNat 64 o + BitVec.ofNat 64 i) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hS := Region.bounds hpre.self.ok.self
  have hIs := hpre.self.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hhi := hw.hi
  simp only [heapEnd] at hhi
  intro i hi hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx
  all_goals first
    | addr_omega [hx, hi, hb, ho]
    | addr_omega [hx, hi, hb, ho, hS, hIs]
    | addr_omega [hx, hi, hb, ho, hnx]
    | addr_omega [hx.2, hi, hb, ho, hhi]

/-- The fold rounds' quadratic. -/
theorem Merkled.quadR (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) (hr : Rowed s k r rows) :
    r.getMem (s.getReg .x2 - 896) = t.getReg .x22 ∧ r.getReg .x23 = t.getReg .x23 ∧
    r.getMem (s.getReg .x2 - 808) = t.getReg .x23 ∧
    eListAt r (t.getReg .x22) (t.getReg .x23).toNat = q := by
  have hb := bounds hpre
  obtain ⟨T0, hl⟩ := hm.lo
  obtain ⟨F0, -⟩ := hm.frU hpre
  obtain ⟨Ft, mtr⟩ := hm.yt hpre hsl hk hr
  have hf := hm.op.fo
  have hh := hf.head
  have hfa := hh.facts
  have hhh := hfa.hL
  have hsL := hfa.hs
  have mht : heapNext h ≤ heapNext t := hf.mono
  have u808 : u.getMem (s.getReg .x2 - 808) = t.getReg .x23 := hm.op.m232
  refine ⟨(hm.kU hpre hsl hk hr (o := 896) (by unfold zuFree; decide)).trans hm.op.m144, ?_,
    (hm.kU hpre hsl hk hr (o := 808) (by unfold zuFree; decide)).trans u808, ?_⟩
  · rw [hr.regs .x23 (by decide), hk.regs .x23 (by decide), hsl.regs .x23 (by decide),
      hm.mo.x23, ← u808]
    exact F0 _ (X0.slot hpre (hl.inv.heap hpre.heap) (o := 808) (by decide))
  · obtain ⟨hq, -, hqb⟩ := hf.Q
    rw [← hq]
    refine Ft.eListAt fun i hi ↦ Zt.heap hpre hr.heap ?_ ?_ mtr
    · rcases hqb with ⟨e1, e2⟩ | h0 | h0
      · have hQ := hh.quad.2.2
        rw [e2] at hi
        rcases hQ with h0 | h0
        · omega
        · rw [e1]; addr_omega [h0, hi, hhh, hsL]
      · omega
      · addr_omega [h0, hi, hhh, hsL]
    · rcases hqb with ⟨e1, e2⟩ | h0 | h0
      · have hQ := hh.quad.2.2
        rw [e2] at hi
        rcases hQ with h0 | h0
        · omega
        · rw [e1]; addr_omega [h0, hi, mht]
      · omega
      · addr_omega [h0, hi]

/-- The folds, `Wl.folds ++ lf`. -/
theorem Merkled.foldsR (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) (hr : Rowed s k r rows) :
    VecOk r (s.getReg .x2 - 688) 24 8 ∧ vecEs r (s.getReg .x2 - 688) = Wl.folds ++ lf ∧
    vecPtr r (s.getReg .x2 - 688) = vecPtr t (s.getReg .x2 - 688) ∧
    vecCap r (s.getReg .x2 - 688) = vecCap t (s.getReg .x2 - 688) := by
  obtain ⟨Ft, mtr⟩ := hm.yt hpre hsl hk hr
  have hf := hm.op.fo
  have hh := hf.head
  have hfa := hh.facts
  have hhh := hfa.hL
  have hsL := hfa.hs
  have mht : heapNext h ≤ heapNext t := hf.mono
  obtain ⟨hv, he, hsame⟩ := hf.F
  have ec : vecCap r (s.getReg .x2 - 688) = vecCap t (s.getReg .x2 - 688) :=
    hm.kT hpre hsl hk hr (o := 688) (by unfold ztFree; decide)
  have ep : vecPtr r (s.getReg .x2 - 688) = vecPtr t (s.getReg .x2 - 688) := by
    simp only [vecPtr]
    rw [show s.getReg .x2 - 688 + 8 = s.getReg .x2 - 680 by rv_eval []]
    exact hm.kT hpre hsl hk hr (o := 680) (by unfold ztFree; decide)
  have el : vecLen r (s.getReg .x2 - 688) = vecLen t (s.getReg .x2 - 688) := by
    simp only [vecLen]
    rw [show s.getReg .x2 - 688 + 16 = s.getReg .x2 - 672 by rv_eval []]
    exact hm.kT hpre hsl hk hr (o := 672) (by unfold ztFree; decide)
  have hraw := hv.raw
  simp only [RawVecOk, Buf] at hraw
  have hl := hv.len
  -- the buffer lies from the entry's `NEXT` on
  have hlo : (vecCap t (s.getReg .x2 - 688)).toNat * 24 = 0 ∨
      heapNext s ≤ (vecPtr t (s.getReg .x2 - 688)).toNat := by
    rcases hsame with ⟨e1, e2⟩ | hn
    · rcases hh.folds.lo with h0 | h0
      · exact Or.inl (by rw [e2, h0]; rfl)
      · exact Or.inr (by rw [e1]; omega)
    · simp only [NewBuf] at hn
      rcases hn.2 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (by omega)
  refine ⟨⟨?_, by rw [el, ec]; exact hl⟩, ?_, ep, ec⟩
  · simp only [RawVecOk, Buf]
    rw [ep, ec]
    exact ⟨hraw.1, hraw.2.imp id fun h' ↦ ⟨h'.1, by omega⟩⟩
  · rw [← he]
    simp only [vecEs]
    rw [ep, el]
    refine Ft.eListAt fun i hi ↦ Zt.heap hpre hr.heap ?_ ?_ mtr
    · rcases hraw.2 with h0 | h0
      · omega
      · rcases hlo with h1 | h1
        · omega
        · addr_omega [h0, h1, hi, hl]
    · rcases hraw.2 with h0 | h0
      · omega
      · addr_omega [h0, hi, hl]

/-- The residual, spilled by the grinding. -/
theorem Merkled.rsdR (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) (hr : Rowed s k r rows) :
    (eListAt r (r.getMem (s.getReg .x2 - 968)) (r.getMem (s.getReg .x2 - 960)).toNat = res ∧
      (r.getMem (s.getReg .x2 - 968)).toNat % 8 = 0 ∧
      ((r.getMem (s.getReg .x2 - 960)).toNat = 0 ∨
        heapNext t ≤ (r.getMem (s.getReg .x2 - 968)).toNat ∧
        (r.getMem (s.getReg .x2 - 968)).toNat + 24 * (r.getMem (s.getReg .x2 - 960)).toNat ≤
          heapNext u)) ∧
    ((r.getMem (s.getReg .x2 - 960)).toNat = 0 ∨ vecCap r (s.getReg .x2 - 616) = 0) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  obtain ⟨T0, hl⟩ := hm.lo
  obtain ⟨Fu, mur⟩ := hm.yu hpre hsl hk hr
  have hS := Region.bounds hpre.self.ok.self
  have hIs := hpre.self.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hhw := (hl.inv.heap hpre.heap).hi
  have kv (o : ℕ) (ho : o = 968 ∨ o = 960) :
      r.getMem (s.getReg .x2 - BitVec.ofNat 64 o) =
        v.getMem (s.getReg .x2 - BitVec.ofNat 64 o) := by
    refine (hm.kW hpre hsl hk hr (by unfold x1Free; rcases ho with rfl | rfl <;> decide)).trans
      (hl.fr _ fun i hi hw ↦ ?_)
    rcases hw with hw | hw | hw | hw | hw | hw | hw <;> rcases ho with rfl | rfl <;> first
      | addr_omega [hw, hi, hb]
      | addr_omega [hw, hi, hb, hS, hIs]
      | addr_omega [hw, hi, hb, hnx]
      | addr_omega [hw.2, hi, hb, hhw]
  have r968 : r.getMem (s.getReg .x2 - 968) = u.getReg .x1 := (kv 968 (Or.inl rfl)).trans hm.rs.1
  have r960 : r.getMem (s.getReg .x2 - 960) = u.getReg .x31 :=
    (kv 960 (Or.inr rfl)).trans hm.rs.2
  obtain ⟨hres, h8, hbd⟩ := hm.op.rsd
  have hst : heapNext s ≤ heapNext t := le_trans hm.op.fo.head.facts.hs
    (le_trans hm.op.fo.head.facts.hL hm.op.fo.mono)
  refine ⟨⟨?_, by rw [r968]; exact h8, by rw [r968, r960]; exact hbd⟩, ?_⟩
  · rw [r968, r960, ← hres]
    refine Fu.eListAt fun i hi ↦ Zu.heap hpre hr.heap ?_ ?_ mur
    · rcases hbd with h0 | h0
      · omega
      · addr_omega [h0, hi, hst]
    · rcases hbd with h0 | h0
      · omega
      · addr_omega [h0, hi]
  · have e : vecCap r (s.getReg .x2 - 616) = vecCap u (s.getReg .x2 - 616) :=
      hm.kU hpre hsl hk hr (o := 616) (by unfold zuFree; decide)
    rw [r960, e]
    exact hm.op.rsdp

/-- What the level wrote from its head on, but the glued claims' header. -/
theorem Merkled.gfrR (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) (hr : Rowed s k r rows) :
    DFrame h r fun a ↦ Within a (s.getReg .x2 - 2464) 1800 ∨ Within a (s.getReg .x2 - 640) 640 ∨
      Within a (s.getReg .x10 + 8) 352 ∨ Within a nextAddr 8 ∨
      (heapNext h ≤ a.toNat ∧ a.toNat < heapNext r) ∨
      Within a (vecPtr h (s.getReg .x2 - 688)) ((vecCap h (s.getReg .x2 - 688)).toNat * 24) := by
  have hb := bounds hpre
  refine (hm.yh hpre hsl hk hr).1.mono fun a ha ↦ ?_
  rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ha))))

/-- What the level wrote since the configured state. -/
theorem Merkled.frR (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) (hr : Rowed s k r rows) :
    DFrame x.c r (LM s x.L (r.getMem nextAddr)) := by
  have hb := bounds hpre
  obtain ⟨Fh, mhr⟩ := hm.yh hpre hsl hk hr
  have hh := hm.op.fo.head
  have hL := hh.facts.hL
  have hraw := hh.folds.vec.raw
  simp only [RawVecOk, Buf] at hraw
  have hlo := hh.folds.lo
  refine (hh.fr.mono fun a ha ↦ LM.mono (hi' := r.getMem nextAddr) mhr ha).trans
    (Fh.mono fun a ha ↦ ?_) fun _ h ↦ h
  rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))
  · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, ha.2⟩)))))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))
    simp only [Within] at ha
    rcases hlo with h0 | h0
    · rw [h0] at ha; simp at ha; omega
    · rcases hraw.2 with h1 | h1
      · omega
      · have : heapNext r = (r.getMem nextAddr).toNat := rfl
        exact ⟨by omega, by omega⟩

/-- The mirror, kept from the Merkle checks' end. -/
theorem Merkled.valueR (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) (hr : Rowed s k r rows) :
    RunsK s r ℓ 1 (Model.Pcs.afterWords (s.getReg .x12).toNat (cfgOf s) (basisOf s x) ℓ
      (restOf s ℓ) (Model.Pcs.foldSt Wl lf q).1 lf res pend (eAt w (s.getReg .x2 - 384)) qs
      (wordsAt s w)) (nextRoots s ℓ d) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  obtain ⟨Fm, mmr⟩ := hm.ym hpre hsl hk hr
  have hrst := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hrst
  have hrf := hpre.root.free
  simp only [Outside] at hrf
  have hsm : heapNext s ≤ heapNext m := hm.mo.inv.mono
  have hhi := hr.heap.hi
  refine hm.value.keep hpre hm.mo.inv Fm (fun a ha ↦ ?_) fun y hy ha ↦ ?_
  · rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inr (Or.inl ha)
    · simp only [Fresh] at ha; exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
  · rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha
    · addr_omega [ha, hy, hrst, hb]
    · addr_omega [ha, hy, hrst, hb]
    · addr_omega [ha, hy, hrst, hb]
    · addr_omega [ha, hy, hrst, hb]
    · addr_omega [ha, hy, hrst, hb]
    · addr_omega [ha, hy, hrst, hb]
    · addr_omega [ha, hy, hrst, hb]
    · addr_omega [ha, hy, hrf.2]
    · simp only [Fresh] at ha
      rcases hrf.1 with h1 | h1
      · addr_omega [hy, ha.1, h1, hsm]
      · addr_omega [hy, ha.2, h1, hhi]

/-- The pending claims, as the opening left them. -/
theorem Merkled.pndR (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) (hr : Rowed s k r rows) :
    PendOk r t (s.getReg .x2 - 616) pend ∧
      ∀ y, PBufs r (s.getReg .x2 - 616) y → y.toNat < heapNext u := by
  obtain ⟨Fu, mur⟩ := hm.yu hpre hsl hk hr
  have hst : heapNext s ≤ heapNext t := le_trans hm.op.fo.head.facts.hs
    (le_trans hm.op.fo.head.facts.hL hm.op.fo.mono)
  refine hm.op.pnd.keep hm.op.heap Fu (fun y h1 h2 ↦ Zu.heap hpre hr.heap (by omega) h2 mur)
    (hm.kU hpre hsl hk hr (o := 616) (by unfold zuFree; decide)) ?_ ?_ mur
  · simp only [vecPtr]
    rw [show s.getReg .x2 - 616 + 8 = s.getReg .x2 - 608 by rv_eval []]
    exact hm.kU hpre hsl hk hr (o := 608) (by unfold zuFree; decide)
  · simp only [vecLen]
    rw [show s.getReg .x2 - 616 + 16 = s.getReg .x2 - 600 by rv_eval []]
    exact hm.kU hpre hsl hk hr (o := 600) (by unfold zuFree; decide)

/-- **`AtR`**, what the level's tail reads at the rows' end. -/
theorem atR (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) (hr : Rowed s k r rows) :
    AtR s x h t u w r ℓ Wl lf q res pend d qs := by
  have hb := bounds hpre
  obtain ⟨T0, hl⟩ := hm.lo
  have ho := hm.op
  have hh := ho.fo.head
  have sl := ho.slots hpre
  obtain ⟨Fu, mur⟩ := hm.yu hpre hsl hk hr
  have hrst := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hrst
  have hrf := hpre.root.free
  simp only [Outside] at hrf
  have hrs := hpre.rootSponge
  have hsu : heapNext s ≤ heapNext u := ho.inv.mono
  have hhi := hr.heap.hi
  have kU (o : ℕ) (hz : zuFree o) := hm.kU hpre hsl hk hr hz
  have kM (o : ℕ) (hz : zmFree o) := hm.kM hpre hsl hk hr hz
  have kH (o : ℕ) (hz : zhFree o) := hm.kH hpre hsl hk hr hz
  have hdig : digestAt r (s.getReg .x11) = digestAt u (s.getReg .x11) :=
    digest_keep Fu (root_bound hpre) fun y hy ha ↦ by
      rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha
      all_goals first
        | addr_omega [ha, hy, hrst, hb]
        | addr_omega [ha, hy, hrs]
        | addr_omega [ha, hy, hrf.2]
        | (simp only [Fresh] at ha
           rcases hrf.1 with h1 | h1
           · addr_omega [hy, ha.1, h1, hsu]
           · addr_omega [hy, ha.2, h1, hhi])
  obtain ⟨hpnd, hpu⟩ := hm.pndR hpre hsl hk hr
  obtain ⟨h1000, hqb, h26⟩ := hm.qR hpre hsl hk hr
  obtain ⟨hrsd, hrsdp⟩ := hm.rsdR hpre hsl hk hr
  have hR := ho.root
  exact {
    head := hh
    fo := ho.fo
    pc := hr.pc
    sp := hr.sp
    inv := hr.inv
    heap := hr.heap
    ht := ho.fo.mono
    tu := ho.mono
    uw := (hm.frU hpre).2
    wr := (hm.frW hpre hsl hk hr).2
    rows := ⟨hr.buf.1, hr.buf.2.imp id fun h' ↦ ⟨le_trans hk.inv.mono h'.1, h'.2⟩⟩
    pw := hm.pwR hpre hsl hk hr
    m816 := (kU 816 (by unfold zuFree; decide)).trans sl.2.2.2.2.2.1
    pnd := hpnd
    pu := hpu
    m1000 := h1000
    qbuf := hqb
    x26 := h26
    m872 := (kU 872 (by unfold zuFree; decide)).trans ho.m168
    lam := by
      rw [limbs_eAt]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · exact (kM 976 (by unfold zmFree; decide)).trans (hm.mo.s24.trans hl.limbs.1.symm)
      · rw [show s.getReg .x2 - 384 + 8 = s.getReg .x2 - 376 by rv_eval []]
        exact (kM 984 (by unfold zmFree; decide)).trans (hm.mo.s25.trans hl.limbs.2.1.symm)
      · rw [show s.getReg .x2 - 384 + 16 = s.getReg .x2 - 368 by rv_eval []]
        exact (kM 992 (by unfold zmFree; decide)).trans (hm.mo.s18.trans hl.limbs.2.2.symm)
    quad := hm.quadR hpre hsl hk hr
    folds := hm.foldsR hpre hsl hk hr
    gfr := hm.gfrR hpre hsl hk hr
    m152 := (kH 888 (by unfold zhFree ztFree; decide)).trans hh.m152
    m160 := (kH 880 (by unfold zhFree ztFree; decide)).trans hh.m160
    m176 := (kH 864 (by unfold zhFree ztFree; decide)).trans
      ((LM.keep hpre hh.fr hh.heap.hi (by addr_omega [hb])).trans hh.cfg.rp)
    m184 := (hm.kT hpre hsl hk hr (o := 856) (by unfold ztFree; decide)).trans ho.fo.m184
    m32 := (kM 1008 (by unfold zmFree; decide)).trans hm.mo.s16
    m248 := (kU 792 (by unfold zuFree; decide)).trans ho.m248
    m128 := (kU 912 (by unfold zuFree; decide)).trans ho.m128
    m200 := (kU 840 (by unfold zuFree; decide)).trans sl.2.2.1
    m112 := (kU 928 (by unfold zuFree; decide)).trans ho.m112
    rsd := hrsd
    rsdp := hrsdp
    root := ⟨by rw [show r.getMem (s.getReg .x2 - 592) = u.getMem (s.getReg .x2 - 592) from
          kU 592 (by unfold zuFree; decide)]; exact hR.1,
        (kU 944 (by unfold zuFree; decide)).trans hR.2.1,
        (kU 952 (by unfold zuFree; decide)).trans hR.2.2.1,
        (kU 920 (by unfold zuFree; decide)).trans hR.2.2.2.1,
        (kU 936 (by unfold zuFree; decide)).trans hR.2.2.2.2⟩
    last := fun hl' ↦ (ho.last hl').trans hdig.symm
    rlen := ho.rlen
    x9 := hm.x9R hpre hsl hk hr
    fr := hm.frR hpre hsl hk hr
    value := hm.valueR hpre hsl hk hr }

end

end Rv64Verifier.Proofs.Pcs.Vso
