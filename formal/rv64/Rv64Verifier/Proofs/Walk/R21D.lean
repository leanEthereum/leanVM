import Rv64Verifier.Proofs.Walk.R21C

/-!
# `walk` R21: `extend_desugared`

`r21ext`: from `ExtR21`, `extend_desugared` (`ExtendSpecE`) appends the claims on the stack to
`vec![ringswitch]`; it returns at `0x80004104` (`VsoR21`) with the claims the mirror batches, every
weight's buffers in the heap.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.PcsContracts Rv64Verifier.Pcs

/-- At `0x80004104`, `extend_desugared` returned: the stack claims' `Vec` at `S - 512`. -/
structure VsoR21 (OI : MachineState → Word → List (List Opening) → Prop)
    (s u₀ f : MachineState) (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64))
    (lir : BitVec 64) (bus : BusResultRust) (cl : List ColumnClaim) (ks ke : ℕ) (tg : E)
    (rw : Pcs.RingWeightRust) : Prop where
  pc : f.pc = 0x80004104
  rest : Rest s u₀ f
  proofPtr : f.getMem (tp s) = s.getReg .x13
  x22 : f.getReg .x22 = lir
  x23 : f.getReg .x23 = s.getReg .x10
  x24 : f.getReg .x24 = s.getReg .x2 - 512
  vec : VecOk f (s.getReg .x2 - 512) 88 8
  claims : stackClaimsAt f (s.getReg .x2 - 512) =
    ⟨.placedRing layout.qkeccak rw, tg⟩ :: cl.filterMap (onStackRust layout)
  weights : ∀ i < (vecLen f (s.getReg .x2 - 512)).toNat,
    WeightIn f (vecPtr f (s.getReg .x2 - 512) + BitVec.ofNat 64 (88 * i))
  tracks : TracksR OI s f
    (digestAt u₀ (s.getReg .x2 - 1800), stackShape layout.stackLog lir.toNat)
    (afterRing layout rows lir bus cl ks ke (tg, rw))

/-- The claims `on_stack` gives have `Eq` weights. -/
theorem mem_filterMap_onStack {pl : List (Option Model.PlacementRust)} {sl : ℕ}
    {l : List LayoutMirror.ColumnClaimRust} {x : Pcs.StackClaimRust}
    (h : x ∈ l.filterMap (onStackAt pl sl)) : ∃ q v, x = ⟨.eq q, v⟩ := by
  obtain ⟨c, -, hc⟩ := List.mem_filterMap.mp h
  unfold onStackAt at hc
  split at hc
  · cases hc
  · cases hc; exact ⟨_, _, rfl⟩

/-- An `Eq` weight's tag. -/
theorem tag_of_eq {f : MachineState} {a : Word} {q : List E} (h : stackWeightAt f a = .eq q) :
    f.getMem a = eqTag := by
  unfold stackWeightAt at h
  split_ifs at h with h1 h2
  · exact h1

/-- A `PlacedRing` weight's tag is neither of the others. -/
theorem tag_of_placed {f : MachineState} {a : Word} {q : Model.PlacementRust} {r : Pcs.RingWeightRust}
    (h : stackWeightAt f a = .placedRing q r) : f.getMem a ≠ eqTag ∧ f.getMem a ≠ ringTag := by
  unfold stackWeightAt at h
  split_ifs at h with h1 h2
  exact ⟨h1, h2⟩

/-- The weights after `extend`: the ring claim's moved, the new claims' points in the heap. -/
theorem weights_after {f : MachineState} {p : Word} {n : Nat} {c0 : Pcs.StackClaimRust}
    {rest : List Pcs.StackClaimRust} (hv : claimsAt f p n = c0 :: rest)
    (hr : ∀ x ∈ rest, ∃ q v, x = ⟨.eq q, v⟩) (h0 : WeightIn f p)
    (hadd : ∀ i, 1 ≤ i → i < n →
      HeapBuf f (vecPtr f (p + BitVec.ofNat 64 (88 * i + 8)))
        (24 * (vecLen f (p + BitVec.ofNat 64 (88 * i + 8))).toNat)) :
    ∀ i < n, WeightIn f (p + BitVec.ofNat 64 (88 * i)) := by
  intro i hi
  rcases i with _ | i
  · simpa using h0
  have hg := congrArg (·[i + 1]?) hv
  simp only [claimsAt, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    List.getElem?_cons_succ] at hg
  obtain ⟨q, v, hq⟩ := hr _ (List.mem_of_getElem? hg.symm)
  have ht := tag_of_eq (congrArg Pcs.StackClaimRust.weight hq)
  unfold WeightIn
  rw [ite_eq_left_of_eq_true _ _ (eq_true ht)]
  have e : p + BitVec.ofNat 64 (88 * (i + 1)) + 8 = p + BitVec.ofNat 64 (88 * (i + 1) + 8) := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl
  rw [e]
  exact hadd (i + 1) (by omega) hi

section Ext
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t e : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {P C L : Word} {cl : List ColumnClaim}
  {ks ke : ℕ} {tg : E} {rw : Pcs.RingWeightRust}

/-- The placements as `walk` built them. -/
theorem placements_kept (hpre : WalkPre s) (h : AtR17 OI s u₀ layout rows lir bus)
    (hPl : PlApart s u₀) (R : Rest s u₀ e) :
    vecPtr e (s.getReg .x2 - 1984) = vecPtr u₀ (s.getReg .x2 - 1984) ∧
      vecLen e (s.getReg .x2 - 1984) = vecLen u₀ (s.getReg .x2 - 1984) ∧
      placementsAt e (vecPtr u₀ (s.getReg .x2 - 1984))
        (vecLen u₀ (s.getReg .x2 - 1984)).toNat = layout.placements := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have e1 : vecPtr e (s.getReg .x2 - 1984) = vecPtr u₀ (s.getReg .x2 - 1984) := by
    simp only [vecPtr]
    rw [show s.getReg .x2 - 1984 + 8 = s.getReg .x2 - BitVec.ofNat 64 1976 by bv_omega,
      R.get (keep_slot hpre (by omega))]
  have e2 : vecLen e (s.getReg .x2 - 1984) = vecLen u₀ (s.getReg .x2 - 1984) := by
    simp only [vecLen]
    rw [show s.getReg .x2 - 1984 + 16 = s.getReg .x2 - BitVec.ofNat 64 1968 by bv_omega,
      R.get (keep_slot hpre (by omega))]
  refine ⟨e1, e2, ?_⟩
  rw [← h.layoutIn.placementsVal]
  have ho := h.layoutIn.placements
  have hb := ho
  simp only [Old] at hb
  have hh := R.inv.heap.hi
  simp only [heapNext, heapEnd] at hh
  have g (x : Word) (h1 : (vecPtr u₀ (s.getReg .x2 - 1984)).toNat ≤ x.toNat)
      (h2 : x.toNat + 8 ≤ (vecPtr u₀ (s.getReg .x2 - 1984)).toNat +
        24 * (vecLen u₀ (s.getReg .x2 - 1984)).toNat) : e.getMem x = u₀.getMem x :=
    R.get (keep_old ho hPl h1 h2)
  unfold placementsAt placementAt
  refine List.map_congr_left fun i hi ↦ ?_
  simp only [List.mem_range] at hi
  have m₀ := R.inv.mono
  rw [g _ (by addr_omega [hb, hi]) (by addr_omega [hb, hi]),
    g _ (by addr_omega [hb, hi]) (by addr_omega [hb, hi]),
    g _ (by addr_omega [hb, hi]) (by addr_omega [hb, hi])]

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8192 in
/-- `extend_desugared`, to its return at `0x80004104`, or a dead end. -/
theorem r21ext (hE : ExtendSpecE) (hpre : WalkPre s) (h : AtR17 OI s u₀ layout rows lir bus)
    (hPl : PlApart s u₀) (hWi : LayoutWithin layout)
    (X : ExtR21 OI s u₀ w t e layout rows lir bus evs P C L cl ks ke tg rw) :
    ∃ f, Reaches Image.code e f ∧
      (VsoR21 OI s u₀ f layout rows lir bus cl ks ke tg rw ∨ Dead Image.code f) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have H := X.toCoreT
  have I := H.rest.inv
  have sp := I.sp
  have hh := I.heap.hi
  have hs0 := hpre.heap.lo
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  simp only [heapEnd, heapStart] at hh hs0 hab
  have hk : extendStack ≤ 8736 := by decide
  have hEnd : heapEnd ≤ (stackLo e extendStack).toNat := by
    rw [stackLo_callee I]; have : extendStack ≤ 8736 := hk
    simp only [heapEnd]; addr_omega [hab, hb1, this]
  have fo (c : Word) (k n : Nat) (hc : c.toNat = k) (hk1 : 104 + n ≤ k) (hk2 : k ≤ 2656) :=
    fr_ok hpre I (c := c) (k := k) (n := n) (m := extendStack) hc hk1 hk2 hk
  obtain ⟨a0, ha0⟩ : ∃ a0, vecPtr e (s.getReg .x2 - 512) = a0 := ⟨_, rfl⟩
  have cb : HeapBuf e a0 88 := ha0 ▸ X.cbuf
  have cb' := cb
  simp only [HeapBuf] at cb'
  have hcur : itCur e = P := by simp only [itCur]; rw [X.x11]; exact X.itCur
  have hlay : itLayout e = s.getReg .x2 - 2080 := by
    simp only [itLayout]; rw [X.x11, show s.getReg .x2 - 928 + 16 = s.getReg .x2 - 912 by bv_omega]
    exact X.itLay
  obtain ⟨bal, bhi, blo, -⟩ := H.buf
  have hL := H.len
  have hPe : (P + BitVec.ofNat 64 (56 * L.toNat)).toNat = P.toNat + 56 * L.toNat := by
    addr_omega [bhi, hL, hh]
  have hend : itEnd e = P + BitVec.ofNat 64 (56 * L.toNat) := by
    simp only [itEnd]; rw [X.x11, show s.getReg .x2 - 928 + 8 = s.getReg .x2 - 920 by bv_omega]
    exact X.itEnd
  have hcnt : itCount e = L.toNat := by
    simp only [itCount]; rw [hcur, hend, hPe]; omega
  have hPB : HeapBuf e P (56 * L.toNat) := ⟨bal, by omega, by
    rcases blo with h0 | h0
    · left; omega
    · rcases Nat.eq_zero_or_pos L.toNat with hz | hz
      · left; omega
      · right; simp only [heapStart]; omega⟩
  obtain ⟨pe1, pe2, pv⟩ := placements_kept hpre h hPl H.rest
  have hpl : placementsPtr e = vecPtr u₀ (s.getReg .x2 - 1984) := by
    simp only [placementsPtr]; rw [hlay, show s.getReg .x2 - 2080 + 104 = s.getReg .x2 - 1984 + 8 by
      bv_omega]; exact pe1
  have hpn : placementsLen e = (vecLen u₀ (s.getReg .x2 - 1984)).toNat := by
    simp only [placementsLen]; rw [hlay, show s.getReg .x2 - 2080 + 112 = s.getReg .x2 - 1984 + 16 by
      bv_omega]; exact congrArg BitVec.toNat pe2
  have hsl : stackLogAt e = layout.stackLog := by
    simp only [stackLogAt]; rw [hlay, show s.getReg .x2 - 2080 + 184 = s.getReg .x2 - BitVec.ofNat 64 1896 by
      bv_omega, H.rest.get (keep_slot hpre (by omega))]
    exact h.layoutIn.stackLog
  have hplb : HeapBuf e (placementsPtr e) (24 * placementsLen e) := by
    rw [hpl, hpn]; exact (h.layoutIn.placements.heapBuf hpre.heap).mono H.rest.mono
  have hpts : ∀ i < L.toNat, (vecLen e (P + BitVec.ofNat 64 (56 * i))).toNat = 0 ∨
      HeapBuf e (vecPtr e (P + BitVec.ofNat 64 (56 * i)))
        (24 * (vecLen e (P + BitVec.ofNat 64 (56 * i))).toNat) := fun i hi ↦
    ((H.points i hi).1).imp_right fun ho ↦ ho.heapBuf hpre.heap
  have has : heapStart ≤ a0.toNat := cb.2.2.resolve_left (by omega)
  have ha64 : HeapBuf e a0 64 := ⟨cb.1, by have := cb.2.1; omega, Or.inr has⟩
  have hw : WeightIn e a0 := ha0 ▸ X.weight
  have hw0 : WeightIn e (a0 + BitVec.ofNat 64 (88 * 0)) := by simpa using hw
  have hw0' : HeapBuf e (a0 + BitVec.ofNat 64 (88 * 0)) 64 := by simpa using ha64
  have he1 : (vecLen e (s.getReg .x2 - 512)).toNat = 1 := by rw [X.len1]; rfl
  have aSt (lo : Word) (n : Nat) (hl : heapEnd ≤ lo.toNat) := fun (b : HeapBuf e lo n) ↦ b
  have ofs (k : Nat) (hk1 : k ≤ 2080) : heapEnd ≤ (s.getReg .x2 - BitVec.ofNat 64 k).toNat := by
    simp only [heapEnd]; addr_omega [hab, hb1, hk1]
  have pre : ExtendPreE e := {
    heap := I.heap
    stack := hpre.stack.sub 2656 I.sp (by rw [stack_eq]; decide) (by decide) (by decide)
      (by decide) (by decide)
    rodata := I.rodata hpre
    self := by
      rw [X.x10]
      obtain ⟨o1, o2, o3⟩ := fo 512 512 24 rfl (by omega) (by omega)
      exact ⟨by addr_omega [hb1, hb2, hb3], o2, o1, o3⟩
    vec := by
      rw [X.x10]
      refine ⟨?_, by rw [X.len1, X.cap1]⟩
      simp only [RawVecOk, Buf]; rw [X.cap1, ha0]
      exact ⟨cb.1, Or.inr ⟨has, by have := cb.2.1; simpa using this⟩⟩
    iter := by
      rw [X.x11]
      obtain ⟨o1, o2, o3⟩ := fo 928 928 24 rfl (by omega) (by omega)
      exact ⟨by addr_omega [hb1, hb2, hb3], o2, o1, o3⟩
    bounds := by rw [hcur, hend, hPe]; omega
    claims := by rw [hcur, hcnt]; exact hPB.src I.heap hEnd
    points := fun i hi ↦ by
      rw [hcnt] at hi; rw [hcur]
      exact (hpts i hi).imp_right fun b ↦ b.src I.heap hEnd
    layout := by
      rw [hlay]
      obtain ⟨o1, o2, -⟩ := fo 2080 2080 192 rfl (by omega) (by omega)
      exact ⟨Or.inr (by addr_omega [hb1, hb2, hb3]), o2, o1⟩
    placements := hplb.src I.heap hEnd
    within := by
      rw [hpl, hpn, pv, hsl]; exact hWi
    selfIter := by rw [X.x10, X.x11]; addr_omega [hb1]
    full := by rw [X.x10, X.len1, X.cap1]
    elems := by
      rw [X.x10, he1, ha0]; exact cb.src I.heap hEnd
    weights := fun i hi ↦ by
      rw [X.x10, he1] at *; rw [ha0]
      obtain rfl : i = 0 := by omega
      exact hw0.src I.heap hEnd hw0' (by simpa using has)
    elemsOff := by
      simp only [ExtendOff]; rw [X.x10, X.x11, he1, ha0]
      exact ⟨cb.apart I.heap (ofs 512 (by omega)), cb.apart I.heap (ofs 928 (by omega))⟩
    weightsOff := fun i hi ↦ by
      rw [X.x10, he1] at hi; rw [X.x10, X.x11, ha0]
      obtain rfl : i = 0 := by omega
      exact ⟨hw0.apart I.heap (ofs 512 (by omega)), hw0.apart I.heap (ofs 928 (by omega))⟩
    claimsOff := by
      simp only [ExtendOff]; rw [hcur, hcnt, X.x10, X.x11]
      exact ⟨hPB.apart I.heap (ofs 512 (by omega)), hPB.apart I.heap (ofs 928 (by omega))⟩
    pointsOff := fun i hi ↦ by
      rw [hcnt] at hi; simp only [ExtendOff]; rw [hcur, X.x10, X.x11]
      rcases hpts i hi with h0 | b
      · rw [h0]; exact ⟨Or.inl rfl, Or.inl rfl⟩
      · exact ⟨b.apart I.heap (ofs 512 (by omega)), b.apart I.heap (ofs 928 (by omega))⟩
    layoutOff := by simp only [ExtendOff]; rw [hlay, X.x10, X.x11]; constructor <;> addr_omega [hb1]
    placementsOff := by
      simp only [ExtendOff]; rw [X.x10, X.x11]
      exact ⟨hplb.apart I.heap (ofs 512 (by omega)), hplb.apart I.heap (ofs 928 (by omega))⟩ }
  obtain ⟨f, hr, ⟨hpc, hp, post⟩ | hd⟩ := hE.call (Reaches.refl e) X.pc pre
  swap
  · exact ⟨f, hr, Or.inr hd⟩
  have fr := post.frame
  rw [X.x10, X.x11] at fr
  have st : StepW s e f (fun a ↦ Within a (s.getReg .x2 - 512) 24 ∨
      Within a (s.getReg .x2 - 928) 8) False :=
    StepW.ofCall hpre I hk (fr.mono fun a ha ↦ by
      rcases ha with ha | ha | ha
      · exact Or.inl (Or.inl ha)
      · exact Or.inl (Or.inr ha)
      · exact Or.inr ha) post.heap post.mono (hp .x2 (by decide))
  have C' := H.stepW hpre st (fun a ha ↦ by
      rcases ha with ha | ha
      · obtain ⟨o1, o2⟩ := range_ok hpre H.rest (c := 512) (k := 512) (n := 24) rfl (by omega)
          (by omega) ha
        exact ⟨o1, o2, by rw [tp]; simp only [Within] at ha ⊢; addr_omega [ha, hb1]⟩
      · obtain ⟨o1, o2⟩ := range_ok hpre H.rest (c := 928) (k := 928) (n := 8) rfl (by omega)
          (by omega) ha
        exact ⟨o1, o2, by rw [tp]; simp only [Within] at ha ⊢; addr_omega [ha, hb1]⟩)
    (fun a ha ↦ by
      rcases ha with ha | ha <;> simp only [Within] at ha ⊢ <;> refine ⟨?_, ?_⟩ <;>
        addr_omega [ha, hb1])
  have h1 : stackClaimsAt e (s.getReg .x2 - 512) = [⟨.placedRing layout.qkeccak rw, tg⟩] := by
    rw [stackClaimsAt, claimsAt, he1]
    show [stackClaimAt e (vecPtr e (s.getReg .x2 - 512) + BitVec.ofNat 64 (88 * 0))] = _
    rw [show vecPtr e (s.getReg .x2 - 512) + BitVec.ofNat 64 (88 * 0) =
      vecPtr e (s.getReg .x2 - 512) by simp, X.claim]
  have hval := post.value
  rw [X.x10, h1, hcur, hcnt, hpl, hpn, pv, hsl, columnClaimsAt_eq, H.claims] at hval
  have hcl : stackClaimsAt f (s.getReg .x2 - 512) =
      ⟨.placedRing layout.qkeccak rw, tg⟩ :: cl.filterMap (onStackRust layout) := by
    rw [hval, filterMap_onStack]; rfl
  have mv := post.moved
  rw [X.x10, he1, ha0] at mv
  have mv0 (k : Nat) (hk : k < 11) : f.getMem (vecPtr f (s.getReg .x2 - 512) + BitVec.ofNat 64 (8 * k)) =
      e.getMem (a0 + BitVec.ofNat 64 (8 * k)) := by
    have := mv 0 (by omega) k hk; simpa using this
  obtain ⟨t1, t2⟩ := tag_of_placed (congrArg Pcs.StackClaimRust.weight (ha0 ▸ X.claim))
  have hnf := post.mono
  have hw' := hw
  unfold WeightIn RingIn at hw'
  rw [ite_eq_right_of_eq_false _ _ (eq_false t1), ite_eq_right_of_eq_false _ _ (eq_false t2)] at hw'
  have m0 : f.getMem (vecPtr f (s.getReg .x2 - 512)) = e.getMem a0 := by
    have := mv0 0 (by omega)
    rw [show vecPtr f (s.getReg .x2 - 512) + BitVec.ofNat 64 (8 * 0) = vecPtr f (s.getReg .x2 - 512)
      by bv_omega, show a0 + BitVec.ofNat 64 (8 * 0) = a0 by bv_omega] at this
    exact this
  have m1 := mv0 1 (by omega)
  have m2 := mv0 2 (by omega)
  have m4 := mv0 4 (by omega)
  have m5 := mv0 5 (by omega)
  have h0 : WeightIn f (vecPtr f (s.getReg .x2 - 512)) := by
    generalize vecPtr f (s.getReg .x2 - 512) = pf at m0 m1 m2 m4 m5 ⊢
    unfold WeightIn RingIn
    rw [m0, ite_eq_right_of_eq_false _ _ (eq_false t1), ite_eq_right_of_eq_false _ _ (eq_false t2)]
    simp only [vecPtr, vecLen] at hw' ⊢
    rw [show pf + 8 = pf + BitVec.ofNat 64 (8 * 1) from rfl, m1,
      show pf + 16 = pf + BitVec.ofNat 64 (8 * 2) from rfl, m2,
      show pf + 24 + 8 = pf + BitVec.ofNat 64 (8 * 4) by bv_omega, m4,
      show pf + 24 + 16 = pf + BitVec.ofNat 64 (8 * 5) by bv_omega, m5]
    rw [show a0 + 24 + 8 = a0 + BitVec.ofNat 64 (8 * 4) by bv_omega,
      show a0 + 24 + 16 = a0 + BitVec.ofNat 64 (8 * 5) by bv_omega] at hw'
    exact ⟨hw'.1.mono hnf, hw'.2.mono hnf⟩
  have hadd := post.added
  rw [X.x10, he1] at hadd
  have hv : claimsAt f (vecPtr f (s.getReg .x2 - 512)) (vecLen f (s.getReg .x2 - 512)).toNat =
      ⟨.placedRing layout.qkeccak rw, tg⟩ :: cl.filterMap (onStackRust layout) := hcl
  refine ⟨f, hr, Or.inl {
    pc := by rw [hpc, returnAddress_eq, X.x1]; decide
    rest := C'.rest
    proofPtr := C'.proofPtr
    x22 := by rw [hp .x22 (by decide), X.x22]
    x23 := by rw [hp .x23 (by decide), X.x23]
    x24 := by rw [hp .x24 (by decide), X.x24]
    vec := by have := post.vec; rwa [X.x10] at this
    claims := hcl
    weights := weights_after hv (fun x hx ↦ mem_filterMap_onStack (by rw [filterMap_onStack]; exact hx))
      h0 hadd
    tracks := C'.tracks }⟩

end Ext

end Rv64Verifier.Proofs.Walk
