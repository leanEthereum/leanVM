import Rv64Verifier.Proofs.Walk.Zip10

/-!
# `walk`: calling `extend_trusted` from the bus blocks' loop

`extPre` builds `ExtendBlocksPre` for a call from the loop: the `Vec<BusBlock>` at a frame address
`hdr` reaching memory from `lo` on, the iterator at `sp + 1728` over a table's `push` or `pull`
(a `Vec<Vec<Form>>` below `lo`), the captures at `sp + 1168`, `sp + 1312` and the table. `vecKeep`
keeps a `Vec<BusBlock>` across a frame missing its header and footprint.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror

/-- A `Vec<BusBlock>` whose header and footprint a frame misses is kept. -/
theorem vecKeep {u v : MachineState} {w : Word → Prop} (fr : Layout.DFrame u v w) {a : Word}
    (hok : BlocksOk u a) (ha : a.toNat + 24 ≤ 2 ^ 64) (hh : ∀ x, Within x a 24 → ¬ w x)
    (hf : ∀ x, blocksFoot u a x → ¬ w x) (hheap : HeapOk u) (mono : heapNext u ≤ heapNext v) :
    BlocksOk v a ∧ blocksOf v a = blocksOf u a ∧ blocksFoot v a = blocksFoot u a := by
  have g (k : Nat) (hk : k + 8 ≤ 24) :
      v.getMem (a + BitVec.ofNat 64 k) = u.getMem (a + BitVec.ofNat 64 k) :=
    fr.getMem_of (fun x hx ↦ hh x (by addr_omega [hx, hk, ha])) (by addr_omega [hk, ha])
  have hc : vecCap v a = vecCap u a := by simpa [vecCap] using g 0 (by decide)
  have hp : vecPtr v a = vecPtr u a := g 8 (by decide)
  have hl : vecLen v a = vecLen u a := g 16 (by decide)
  have hle := hok.le
  have K := blocksAt_frame fr hok (fun x hx ↦ hf x (Or.inl (by simp only [Within] at hx ⊢; omega)))
    (fun x hx ↦ hf x (Or.inr hx)) hheap mono
  refine ⟨?_, ?_, ?_⟩
  · simp only [BlocksOk, hc, hp, hl]; exact K.2.1
  · simp only [blocksOf, hp, hl]; exact K.1
  · funext x; simp only [blocksFoot, hc, hp, hl, K.2.2]

/-- The callee's stack, below the frame. -/
theorem stk10 {s u : MachineState} (hpre : WalkPre s) (h : Inv s u) {m : Nat} (hm : m ≤ 8736)
    (hm8 : m % 8 = 0) : RtStack u m :=
  hpre.stack.sub 2656 h.sp (by rw [stack_eq]; omega) (by decide) hm8 (by decide) (by decide)

theorem extStack_le : extendBlocksStack ≤ 8736 := by decide

/-- Read-only bytes of the frame apart from the `Vec`'s header. -/
theorem extRO_frame {OI : MachineState → Word → List (List Opening) → Prop} {s c : MachineState}
    {A : List E} {k : Nat} {R Q B : Word} {lo : Nat} (hpre : WalkPre s)
    (h : Base10 OI s c A k R Q B lo) {hdr : Word} (x10 : c.getReg .x10 = hdr)
    (hok : BlocksOk c hdr) {o n : Nat} (hn : n % 8 = 0)
    (ho1 : 104 + n ≤ o) (ho2 : o ≤ 2656) (ho8 : o % 8 = 0)
    (hap : Apart (s.getReg .x2 - BitVec.ofNat 64 o) n hdr 24) :
    ExtRO c (s.getReg .x2 - BitVec.ofNat 64 o) n := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hv := hpre.stack.valid
  have hx := hpre.stack.next
  have hab := hpre.stack.above
  rw [stackLo_eq] at hx hab
  rw [stack_eq] at hx
  simp only [heapEnd] at hab
  have hhi := h.inv.heap.hi
  simp only [heapEnd] at hhi
  refine ⟨?_, by addr_omega [hb1, hb3, ho2, ho8], Or.inr ⟨Or.inr (by addr_omega [hab, hb1, ho2]), by
    simp only [Apart]; addr_omega [hx, hb1, ho1, ho2]⟩, by
    rw [stackLo_callee h.inv]; simp only [Apart]; addr_omega [hb1, ho1, ho2], fun x hx' hw ↦ ?_⟩
  · refine validMemRange_of (by addr_omega [hb1, hb3, ho2, ho8]) (Or.inr ⟨by addr_omega [hb1, ho2],
      by addr_omega [hb1, hb2, ho1, ho2, hn]⟩)
  · simp only [selfW, x10] at hw
    rcases hw with hw | hw
    · simp only [Within, Apart] at hx' hw hap; addr_omega [hx', hw, hap, hb1, ho1, ho2]
    · have hbd := BlocksSound.bounds hok
      simp only [Within] at hx' hw
      rcases hbd.2 with h0 | h0
      · rw [h0] at hw; omega
      · addr_omega [hx', hw, h0, hhi, hb1, ho2]

/-- Read-only bytes of the heap below `lo`. -/
theorem extRO_heap {OI : MachineState → Word → List (List Opening) → Prop} {s c : MachineState}
    {A : List E} {k : Nat} {R Q B : Word} {lo : Nat} (hpre : WalkPre s)
    (h : Base10 OI s c A k R Q B lo) {hdr : Word} (hh1 : (s.getReg .x2 - 2080).toNat ≤ hdr.toNat)
    (hh2 : hdr.toNat + 24 ≤ (s.getReg .x2 - 104).toNat) (x10 : c.getReg .x10 = hdr)
    (hf : ∀ x, blocksFoot c hdr x → lo ≤ x.toNat) {a : Word} {n : Nat} (ha8 : a.toNat % 8 = 0)
    (hr : n = 0 ∨ 0x20000000 ≤ a.toNat ∧ a.toNat + n ≤ lo) : ExtRO c a n := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hhi := h.inv.heap.hi
  have hl := h.loLe
  simp only [heapEnd] at hhi
  rcases hr with h0 | ⟨h1, h2⟩
  · subst h0
    exact ⟨fun i hi ↦ absurd hi (by omega), ha8, Or.inl rfl, Or.inl rfl, fun x hx ↦ by
      simp only [Within] at hx; omega⟩
  refine ⟨validMemRange_of ha8 (Or.inl ⟨by omega, by omega⟩), ha8,
    Or.inr ⟨Or.inl (by omega), by simp only [Apart, nextAddr]; addr_omega [h2, hl, hhi]⟩, by
    rw [stackLo_callee h.inv]; simp only [Apart]; addr_omega [hb1, h2, hl, hhi], fun x hx hw ↦ ?_⟩
  simp only [selfW, x10] at hw
  rcases hw with hw | hw
  · simp only [Within] at hx hw; addr_omega [hx, hw, hh1, hh2, hb1, h2, hl, hhi]
  · have := hf x (Or.inl hw)
    simp only [Within] at hx
    omega

/-- `extend_trusted`'s precondition, from the loop: the `Vec<BusBlock>` at `hdr` (in the frame from
`sp + 576`), the iterator at `sp + 1728` over the `Vec<Vec<Form>>` at `V` (below `lo`), the
captures `sp + 1168`, `sp + 1312` and the table at `tbl`. -/
theorem extPre {OI : MachineState → Word → List (List Opening) → Prop} {s c : MachineState}
    {A : List E} {k : Nat} {R Q B : Word} {lo : Nat} (hpre : WalkPre s)
    (h : Base10 OI s c A k R Q B lo) {hdr : Word} (hh1 : (s.getReg .x2 - 2080).toNat ≤ hdr.toNat)
    (hh2 : hdr.toNat + 24 ≤ (s.getReg .x2 - 104).toNat) (hh3 : hdr.toNat % 8 = 0)
    (hap : Apart hdr 24 (s.getReg .x2 - 1488) 8 ∧ Apart hdr 24 (s.getReg .x2 - 1344) 8 ∧
      Apart hdr 24 (s.getReg .x2 - 928) 40)
    (x10 : c.getReg .x10 = hdr) (x11 : c.getReg .x11 = s.getReg .x2 - 928)
    (hok : BlocksOk c hdr) (hf : ∀ x, blocksFoot c hdr x → lo ≤ x.toNat)
    {V tbl : Word} (hV : FormVecsOk c V) (hVlo : ∀ x, formVecsDeep c V x → x.toNat < lo)
    (ht : 0x20000000 ≤ tbl.toNat ∧ tbl.toNat + 80 ≤ lo ∧ tbl.toNat % 8 = 0)
    (m0 : c.getMem (s.getReg .x2 - 928) = vecPtr c V)
    (m8 : c.getMem (s.getReg .x2 - 920) = vecPtr c V + BitVec.ofNat 64 (24 * (vecLen c V).toNat))
    (m16 : c.getMem (s.getReg .x2 - 912) = s.getReg .x2 - 1488)
    (m24 : c.getMem (s.getReg .x2 - 904) = s.getReg .x2 - 1344)
    (m32 : c.getMem (s.getReg .x2 - 896) = tbl) :
    ExtendBlocksPre c ∧ itBegin c = vecPtr c V ∧ itLen c = (vecLen c V).toNat ∧
      itHeight c = s.getReg .x2 - 1488 ∧ itRows c = s.getReg .x2 - 1344 ∧ itTable c = tbl := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hx := hpre.stack.next
  have hab := hpre.stack.above
  rw [stackLo_eq] at hx hab
  rw [stack_eq] at hx
  simp only [heapEnd] at hab
  have hhi := h.inv.heap.hi
  have hl := h.loLe
  simp only [heapEnd] at hhi
  have e8 : s.getReg .x2 - 928 + 8 = s.getReg .x2 - 920 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e16 : s.getReg .x2 - 928 + 16 = s.getReg .x2 - 912 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e24 : s.getReg .x2 - 928 + 24 = s.getReg .x2 - 904 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e32 : s.getReg .x2 - 928 + 32 = s.getReg .x2 - 896 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hbV := vecBuf_bounds hV.vec (by decide)
  have hLc := hV.vec.len
  -- the slice lies below `lo`
  have hsl : (vecLen c V).toNat = 0 ∨
      0x20000000 ≤ (vecPtr c V).toNat ∧ (vecPtr c V).toNat + 24 * (vecLen c V).toNat ≤ lo := by
    rcases Nat.eq_zero_or_pos (vecLen c V).toNat with h0 | h0
    · exact Or.inl h0
    rcases hbV.2 with h1 | h1
    · omega
    have := hVlo (vecPtr c V + BitVec.ofNat 64 (24 * (vecLen c V).toNat - 1)) (Or.inl (by
      simp only [formVecsBuf, Within]; addr_omega [h1, h0, hLc, hhi]))
    simp only [heapStart] at h1
    exact Or.inr ⟨h1.1, by addr_omega [this, h1, h0, hLc, hhi]⟩
  have hB : itBegin c = vecPtr c V := by simp only [itBegin, x11, m0]
  have hEnd : (c.getMem (c.getReg .x11 + 8)).toNat = (vecPtr c V).toNat + 24 * (vecLen c V).toNat := by
    rw [x11, e8, m8]
    rcases hsl with h0 | h0
    · rw [h0]; simp
    · addr_omega [h0, hl, hhi]
  have hLen : itLen c = (vecLen c V).toNat := by
    simp only [itLen, hB, hEnd]; omega
  have hH : itHeight c = s.getReg .x2 - 1488 := by simp only [itHeight, x11, e16, m16]
  have hR : itRows c = s.getReg .x2 - 1344 := by simp only [itRows, x11, e24, m24]
  have hT : itTable c = tbl := by simp only [itTable, x11, e32, m32]
  refine ⟨{
    heap := h.inv.heap
    stack := stk10 hpre h.inv extStack_le (by decide)
    self := by
      rw [x10]
      exact validMemRange_of hh3 (Or.inr ⟨by addr_omega [hh1, hb1], by addr_omega [hh2, hb1, hb2]⟩)
    ok := by rw [x10]; exact hok
    selfFree := by
      rw [x10]; exact ⟨Or.inr (by addr_omega [hab, hb1, hh1]), by
        simp only [Apart]; addr_omega [hx, hb1, hh1]⟩
    selfStack := by rw [x10, stackLo_callee h.inv]; simp only [Apart]; addr_omega [hb1, hh1]
    header := fun x hx' hfx ↦ by
      rw [x10] at hx' hfx
      have h1 := hf x hfx
      have hbd := BlocksSound.bounds hok
      simp only [Within] at hx'
      rcases hfx with hfx | ⟨j, hj, hfx⟩
      · simp only [Within] at hfx
        rcases hbd.2 with h0 | h0
        · rw [h0] at hfx; omega
        · addr_omega [hx', hfx, h0, hhi, hh1, hb1]
      · have := (hok.elems j hj).deep_below hfx
        addr_omega [hx', this, hhi, hh1, hb1]
    env := by
      rw [x11]
      exact extRO_frame (o := 928) hpre h x10 hok (by decide) (by decide) (by decide) (by decide)
        (by have := hap.2.2; simp only [Apart] at this ⊢; addr_omega [this, hb1])
    whole := by rw [hB, hEnd]; omega
    src := by
      rw [hB, hLen]
      exact extRO_heap hpre h hh1 hh2 x10 hf hbV.1 (by
        rcases hsl with h0 | h0
        · exact Or.inl (by rw [h0])
        · exact Or.inr h0)
    srcOk := fun i hi ↦ by
      rw [hLen] at hi; rw [hB]; exact hV.elems i hi
    srcDeep := fun i hi x hx' hw ↦ by
      rw [hLen] at hi; rw [hB] at hx'
      have h1 := hVlo x (Or.inr ⟨i, hi, hx'⟩)
      have h2 := (hV.elems i hi).deep_below hx'
      simp only [selfW, x10] at hw
      rcases hw with hw | hw
      · simp only [Within] at hw; addr_omega [hw, h2, hhi, hh1, hb1]
      · exact absurd (hf x (Or.inl hw)) (by omega)
    height := by
      rw [hH]
      exact extRO_frame (o := 1488) hpre h x10 hok (by decide) (by decide) (by decide) (by decide)
        (by have := hap.1; simp only [Apart] at this ⊢; addr_omega [this, hb1])
    rows := by
      rw [hR]
      exact extRO_frame (o := 1344) hpre h x10 hok (by decide) (by decide) (by decide) (by decide)
        (by have := hap.2.1; simp only [Apart] at this ⊢; addr_omega [this, hb1])
    table := by
      rw [hT]
      exact extRO_heap hpre h hh1 hh2 x10 hf (by addr_omega [ht, hl, hhi])
        (Or.inr ⟨by addr_omega [ht, hl, hhi], by addr_omega [ht, hl, hhi]⟩) }, hB, hLen, hH, hR, hT⟩

/-- What a call growing the `Vec<BusBlock>` at `a` writes: its header and buffer, the stack below
the frame, `NEXT`, and what it allocates. -/
@[rv_addr] def GrowW (s c t : MachineState) (a x : Word) : Prop :=
  Within x a 24 ∨ Within x (vecPtr c a) (48 * (vecCap c a).toNat) ∨
    Within x (s.getReg .x2 - 11392) 8736 ∨ Within x nextAddr 8 ∨ Fresh c t x

/-- The footprint of a sound `Vec<BusBlock>` is in the heap below `NEXT`. -/
theorem BlocksOk.foot_below {u : MachineState} {a : Word} (h : BlocksOk u a) {x : Word}
    (hx : blocksFoot u a x) : heapStart ≤ x.toNat ∧ x.toNat < heapNext u := by
  rcases hx with hx | hx
  · have hb := BlocksSound.bounds h
    simp only [Within] at hx
    rcases hb.2 with h0 | h0
    · rw [h0] at hx; omega
    · omega
  · exact BlocksSound.deep_below h hx

/-- Another `Vec<BusBlock>` in the frame is kept by a `GrowW` frame whose `Vec` its footprint
misses. -/
theorem growKeep {s c t : MachineState} (hpre : WalkPre s) (hc : HeapOk c) (ht : HeapOk t)
    (mono : heapNext c ≤ heapNext t) {a b : Word} {w : Word → Prop}
    (fr : Layout.DFrame c t w) (hw : ∀ x, w x → GrowW s c t a x)
    (hb1 : (s.getReg .x2 - 2080).toNat ≤ b.toNat) (hb2 : b.toNat + 24 ≤ (s.getReg .x2 - 104).toNat)
    (ha1 : (s.getReg .x2 - 2080).toNat ≤ a.toNat)
    (hab : Apart a 24 b 24) (hoka : BlocksOk c a) (hok : BlocksOk c b)
    (hd : ∀ x, blocksFoot c b x → ¬ Within x (vecPtr c a) (48 * (vecCap c a).toNat)) :
    BlocksOk t b ∧ blocksOf t b = blocksOf c b ∧ blocksFoot t b = blocksFoot c b := by
  obtain ⟨h1, h2, -, -⟩ := bounds hpre
  have hhi := ht.hi
  simp only [heapEnd] at hhi
  have hba := BlocksSound.bounds hoka
  refine vecKeep fr hok (by addr_omega [hb2, h1, h2]) (fun x hx hwx ↦ ?_) (fun x hx hwx ↦ ?_) hc mono
  · rcases hw x hwx with h | h | h | h | ⟨-, h⟩
    · simp only [Within, Apart] at h hx hab; addr_omega [h, hx, hab]
    · simp only [Within] at h hx
      rcases hba.2 with h0 | h0
      · rw [h0] at h; omega
      · have := hc.hi; simp only [heapEnd] at this; addr_omega [h, hx, h0, this, hb1, h1]
    · simp only [Within] at h hx; addr_omega [h, hx, hb1, h1]
    · simp only [Within, nextAddr] at h hx; addr_omega [h, hx, hb1, h1]
    · simp only [Within, heapNext] at h hx hhi; addr_omega [h, hx, hb1, h1, hhi]
  · have hfb := hok.foot_below hx
    simp only [heapStart] at hfb
    have hci := hc.hi
    simp only [heapEnd] at hci
    rcases hw x hwx with h | h | h | h | ⟨h, -⟩
    · simp only [Within] at h; addr_omega [h, hfb, hci, ha1, h1]
    · exact hd x hx h
    · simp only [Within] at h; addr_omega [h, hfb, hci, h1]
    · simp only [Within, nextAddr] at h; addr_omega [h, hfb, hci]
    · omega

section Grow
variable {s c t : MachineState} {lo : Nat} {P : List BusBlockRust × List BusBlockRust × List BusBlockRust}
  {w : Word → Prop} {X : List BusBlockRust}

/-- `push` grown, `pull` and `count` kept. -/
theorem Vecs10.withPush (hpre : WalkPre s) (V : Vecs10 s c lo P) (hc : HeapOk c) (ht : HeapOk t)
    (mono : heapNext c ≤ heapNext t) (hlo : lo ≤ heapNext c) (fr : Layout.DFrame c t w)
    (hw : ∀ x, w x → GrowW s c t (s.getReg .x2 - 416) x) (ok : BlocksOk t (s.getReg .x2 - 416))
    (val : blocksOf t (s.getReg .x2 - 416) = P.1 ++ X)
    (foot : ∀ x, blocksFoot t (s.getReg .x2 - 416) x →
      blocksFoot c (s.getReg .x2 - 416) x ∨ Fresh c t x) :
    Vecs10 s t lo (P.1 ++ X, P.2.1, P.2.2) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have kp := growKeep hpre hc ht mono fr hw (b := s.getReg .x2 - 224) (by addr_omega [hb1])
    (by addr_omega [hb1]) (by addr_omega [hb1]) (by simp only [Apart]; addr_omega [hb1]) V.push V.pull
    fun x hx hb ↦ V.d1 x (Or.inl hb) hx
  have kc := growKeep hpre hc ht mono fr hw (b := s.getReg .x2 - 512) (by addr_omega [hb1])
    (by addr_omega [hb1]) (by addr_omega [hb1]) (by simp only [Apart]; addr_omega [hb1]) V.push V.count
    fun x hx hb ↦ V.d2 x (Or.inl hb) hx
  refine ⟨ok, kp.1, kc.1, val, by rw [kp.2.1]; exact V.pullV, by rw [kc.2.1]; exact V.countV,
    fun x hx ↦ ?_, fun x hx hy ↦ ?_, fun x hx hy ↦ ?_, fun x hx hy ↦ ?_⟩
  · rw [kp.2.2, kc.2.2] at hx
    rcases hx with hx | hx | hx
    · rcases foot x hx with h | h
      · exact V.fresh x (Or.inl h)
      · exact le_trans hlo h.1
    · exact V.fresh x (Or.inr (Or.inl hx))
    · exact V.fresh x (Or.inr (Or.inr hx))
  · rw [kp.2.2] at hy
    rcases foot x hx with h | h
    · exact V.d1 x h hy
    · exact absurd (V.pull.foot_below hy).2 (by have := h.1; omega)
  · rw [kc.2.2] at hy
    rcases foot x hx with h | h
    · exact V.d2 x h hy
    · exact absurd (V.count.foot_below hy).2 (by have := h.1; omega)
  · rw [kp.2.2] at hx; rw [kc.2.2] at hy; exact V.d3 x hx hy

/-- `pull` grown, `push` and `count` kept. -/
theorem Vecs10.withPull (hpre : WalkPre s) (V : Vecs10 s c lo P) (hc : HeapOk c) (ht : HeapOk t)
    (mono : heapNext c ≤ heapNext t) (hlo : lo ≤ heapNext c) (fr : Layout.DFrame c t w)
    (hw : ∀ x, w x → GrowW s c t (s.getReg .x2 - 224) x) (ok : BlocksOk t (s.getReg .x2 - 224))
    (val : blocksOf t (s.getReg .x2 - 224) = P.2.1 ++ X)
    (foot : ∀ x, blocksFoot t (s.getReg .x2 - 224) x →
      blocksFoot c (s.getReg .x2 - 224) x ∨ Fresh c t x) :
    Vecs10 s t lo (P.1, P.2.1 ++ X, P.2.2) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have kp := growKeep hpre hc ht mono fr hw (b := s.getReg .x2 - 416) (by addr_omega [hb1])
    (by addr_omega [hb1]) (by addr_omega [hb1]) (by simp only [Apart]; addr_omega [hb1]) V.pull V.push
    fun x hx hb ↦ V.d1 x hx (Or.inl hb)
  have kc := growKeep hpre hc ht mono fr hw (b := s.getReg .x2 - 512) (by addr_omega [hb1])
    (by addr_omega [hb1]) (by addr_omega [hb1]) (by simp only [Apart]; addr_omega [hb1]) V.pull V.count
    fun x hx hb ↦ V.d3 x (Or.inl hb) hx
  refine ⟨kp.1, ok, kc.1, by rw [kp.2.1]; exact V.pushV, val, by rw [kc.2.1]; exact V.countV,
    fun x hx ↦ ?_, fun x hx hy ↦ ?_, fun x hx hy ↦ ?_, fun x hx hy ↦ ?_⟩
  · rw [kp.2.2, kc.2.2] at hx
    rcases hx with hx | hx | hx
    · exact V.fresh x (Or.inl hx)
    · rcases foot x hx with h | h
      · exact V.fresh x (Or.inr (Or.inl h))
      · exact le_trans hlo h.1
    · exact V.fresh x (Or.inr (Or.inr hx))
  · rw [kp.2.2] at hx
    rcases foot x hy with h | h
    · exact V.d1 x hx h
    · exact absurd (V.push.foot_below hx).2 (by have := h.1; omega)
  · rw [kp.2.2] at hx; rw [kc.2.2] at hy; exact V.d2 x hx hy
  · rw [kc.2.2] at hy
    rcases foot x hx with h | h
    · exact V.d3 x h hy
    · exact absurd (V.count.foot_below hy).2 (by have := h.1; omega)

end Grow

/-- The call of `extend_trusted` from the loop, onto the `Vec<BusBlock>` at `hdr`: `Base10` kept,
the frame below `sp + 2080` and the heap below `lo` unchanged, the `Vec` grown by the blocks of
the `Vec<Vec<Form>>` at `V`'s coordinates. -/
theorem extCall (hE : ExtendBlocksSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s c : MachineState} {A : List E} {k : Nat} {R Q B : Word} {lo : Nat} (hpre : WalkPre s)
    (hpc : c.pc = 0x80005f94) (h : Base10 OI s c A k R Q B lo) {hdr : Word}
    (hh1 : (s.getReg .x2 - 2080).toNat ≤ hdr.toNat)
    (hh2 : hdr.toNat + 24 ≤ (s.getReg .x2 - 104).toNat) (hh3 : hdr.toNat % 8 = 0)
    (hap : Apart hdr 24 (s.getReg .x2 - 1488) 8 ∧ Apart hdr 24 (s.getReg .x2 - 1344) 8 ∧
      Apart hdr 24 (s.getReg .x2 - 928) 40)
    (x10 : c.getReg .x10 = hdr) (x11 : c.getReg .x11 = s.getReg .x2 - 928)
    (hok : BlocksOk c hdr) (hf : ∀ x, blocksFoot c hdr x → lo ≤ x.toNat)
    {V tbl : Word} (hV : FormVecsOk c V) (hVlo : ∀ x, formVecsDeep c V x → x.toNat < lo)
    (ht : 0x20000000 ≤ tbl.toNat ∧ tbl.toNat + 80 ≤ lo ∧ tbl.toNat % 8 = 0)
    (m0 : c.getMem (s.getReg .x2 - 928) = vecPtr c V)
    (m8 : c.getMem (s.getReg .x2 - 920) = vecPtr c V + BitVec.ofNat 64 (24 * (vecLen c V).toNat))
    (m16 : c.getMem (s.getReg .x2 - 912) = s.getReg .x2 - 1488)
    (m24 : c.getMem (s.getReg .x2 - 904) = s.getReg .x2 - 1344)
    (m32 : c.getMem (s.getReg .x2 - 896) = tbl) :
    ∃ t, Reaches Image.code c t ∧ (Dead Image.code t ∨ (t.pc = returnAddress c ∧
      Preserves c t ∧ Base10 OI s t A k R Q B lo ∧ HeapOk t ∧ heapNext c ≤ heapNext t ∧
      (∃ w, Layout.DFrame c t w ∧ ∀ x, w x → GrowW s c t hdr x) ∧
      (∀ x, (s.getReg .x2 - 2656).toNat ≤ x.toNat → x.toNat + 8 ≤ (s.getReg .x2 - 104).toNat →
        Apart x 8 hdr 24 → t.getMem x = c.getMem x) ∧
      (∀ x, 0x20000000 ≤ x.toNat → x.toNat + 8 ≤ lo → t.getMem x = c.getMem x) ∧
      BlocksOk t hdr ∧
      blocksOf t hdr = blocksOf c hdr ++ ((formVecsOf c V).map fun co ↦
        (⟨(c.getMem (s.getReg .x2 - 1488)).toNat, c.getMem (s.getReg .x2 - 1344), co,
          (c.getMem (tbl + 72)).toNat⟩ : BusBlockRust)) ∧
      ∀ x, blocksFoot t hdr x → blocksFoot c hdr x ∨ Fresh c t x)) := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  obtain ⟨pre, hB, hL, hH, hR, hT⟩ := extPre hpre h hh1 hh2 hh3 hap x10 x11 hok hf hV hVlo ht
    m0 m8 m16 m24 m32
  obtain ⟨t, hr, ⟨hpct, hp, post⟩ | hd⟩ := hE c hpc pre
  swap
  · exact ⟨t, hr, Or.inl hd⟩
  have hhi := post.heap.hi
  have hl := h.loLe
  have hci := h.inv.heap.hi
  simp only [heapEnd] at hhi hci
  have hbd := BlocksSound.bounds hok
  have hw : ∀ x, (selfW c x ∨ Within x (stackLo c extendBlocksStack) extendBlocksStack ∨
      Within x nextAddr 8 ∨ Fresh c t x) → GrowW s c t hdr x := fun x hx ↦ by
    simp only [selfW, x10] at hx
    rcases hx with (hx | hx) | hx | hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
    · rw [stackLo_callee h.inv] at hx
      exact Or.inr (Or.inr (Or.inl (by simp only [Within] at hx ⊢; addr_omega [hx, hb1])))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hx)))
  have hX : ∀ x, GrowW s c t hdr x → X10 s lo B t x := fun x hx ↦ by
    simp only [GrowW] at hx
    rcases hx with hx | hx | hx | hx | hx
    · exact Or.inl (Or.inl ⟨by simp only [Within] at hx; omega, by simp only [Within] at hx; omega⟩)
    · refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨hf x (Or.inl hx), ?_⟩))))
      simp only [Within] at hx
      rcases hbd.2 with h0 | h0
      · rw [h0] at hx; omega
      · have := post.mono; omega
    · exact Or.inl (Or.inr (Or.inr (Or.inl hx)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hx))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨by have := hx.1; omega, hx.2⟩))))
  have fr := post.frame
  have B' := h.keep hpre (w := fun x ↦ GrowW s c t hdr x) (fr.mono hw) hX post.heap post.mono (hp _ (by decide))
  refine ⟨t, hr, Or.inr ⟨hpct, hp, B', post.heap, post.mono, ⟨_, fr.mono hw, fun _ h ↦ h⟩,
    fun x h1 h2 h3 ↦ ?_, fun x h1 h2 ↦ ?_, by rw [← x10]; exact post.ok, ?_, ?_⟩⟩
  · refine fr x (fun y hy hwy ↦ ?_) (by addr_omega [h2, hb1])
    have := hw y hwy
    simp only [GrowW] at this
    rcases this with h4 | h4 | h4 | h4 | h4
    · simp only [Within, Apart] at hy h4 h3; addr_omega [hy, h4, h3]
    · simp only [Within] at hy h4
      rcases hbd.2 with h0 | h0
      · rw [h0] at h4; omega
      · addr_omega [hy, h4, h0, hci, h1, hb1]
    · simp only [Within] at hy h4; addr_omega [hy, h4, h1, hb1]
    · simp only [Within, nextAddr] at hy h4; addr_omega [hy, h4, h1, hb1]
    · simp only [Within, Fresh, heapNext] at hy h4 hhi; addr_omega [hy, h4, h1, hb1, hhi]
  · refine fr x (fun y hy hwy ↦ ?_) (by addr_omega [h2, hl, hci])
    have := hw y hwy
    simp only [GrowW] at this
    rcases this with h4 | h4 | h4 | h4 | h4
    · simp only [Within] at hy h4; addr_omega [hy, h4, h2, hl, hci, hh1, hb1]
    · have := hf y (Or.inl h4); simp only [Within] at hy; omega
    · simp only [Within] at hy h4; addr_omega [hy, h4, h2, hl, hci, hb1]
    · simp only [Within, nextAddr] at hy h4; addr_omega [hy, h4, h2, hl, hci]
    · simp only [Within, Fresh] at hy h4; omega
  · rw [← x10, post.value, hB, hL, hH, hR, hT, x10]
    rfl
  · rw [← x10]; exact post.foot

end Rv64Verifier.Proofs.Walk
