import Rv64Verifier.Proofs.Walk.Blocks10

/-!
# `walk` from `0x80002e40` to the `Layout`: what stays put

`Base10 s u A k R Q B lo` is `AtR10` without the registers: the transcript and the mirror's
position, the spills, `table_rows`, `table_log_heights` and the tables, everything of it below `lo`
in the heap or below `sp + 576` in the frame. A step that writes only the frame from `sp + 576`, the
slot at `sp + 184`, the stack below the frame, `NEXT` and the heap from `lo` (`W10`) keeps it
(`Base10.keep`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror

/-- What the code writes from `0x80002e40` until the `Layout` stands: the frame from `sp + 576` to
the saved registers, `sp + 184`, the stack below the frame, `NEXT`, the heap from `lo` on. -/
@[rv_addr] def W10 (s : MachineState) (lo : Nat) (v : MachineState) (a : Word) : Prop :=
  ((s.getReg .x2 - 2080).toNat ≤ a.toNat ∧ a.toNat < (s.getReg .x2 - 104).toNat) ∨
    Within a (s.getReg .x2 - 2472) 8 ∨ Within a (s.getReg .x2 - 11392) 8736 ∨
    Within a nextAddr 8 ∨ (lo ≤ a.toNat ∧ a.toNat < heapNext v)

/-- `AtR10` but for the registers and the last opcode; what it holds in the heap lies below `lo`. -/
structure Base10 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) (lo : Nat) : Prop where
  inv : Inv s u
  proofPtr : u.getMem (tp s) = s.getReg .x13
  checked : byteAt u (tp s + 360) = 1
  ok : HeadOk s A k
  rate : 1#64 ≤ rateOf A ∧ rateOf A ≤ 4#64
  tracks : Tracks OI s u (afterRate s A)
  spills : u.getMem (s.getReg .x2 - 2584) = rateOf A ∧
    u.getMem (s.getReg .x2 - 2576) = s.getMem (s.getReg .x12 + 16) ∧
    u.getMem (s.getReg .x2 - 2568) = s.getMem (s.getReg .x12) ∧
    u.getMem (s.getReg .x2 - 2560) = s.getMem (s.getReg .x12 + 24) ∧
    u.getMem (s.getReg .x2 - 2552) = s.getMem (s.getReg .x12 + 8) ∧
    u.getMem (s.getReg .x2 - 2528) = s.getReg .x11 ∧ u.getMem (s.getReg .x2 - 2512) = lmOf A ∧
    u.getMem (s.getReg .x2 - 2496) = BitVec.ofNat 64 (k - 4) ∧
    u.getMem (s.getReg .x2 - 2488) = s.getReg .x10
  slots : u.getMem (s.getReg .x2 - 2536) = 6 ∧ u.getMem (s.getReg .x2 - 2520) = 6 ∧
    u.getMem (s.getReg .x2 - 2504) = 0 ∧ u.getMem (s.getReg .x2 - 2480) = R ∧
    u.getMem (s.getReg .x2 - 2464) = Q ∧ u.getMem (s.getReg .x2 - 2456) = B
  bufR : R.toNat % 8 = 0 ∧ 0x20000000 ≤ R.toNat ∧ R.toNat + 48 ≤ lo
  bufQ : heapNext s ≤ Q.toNat ∧ Q.toNat % 8 = 0 ∧ Q.toNat + 48 ≤ lo
  bufB : heapNext s ≤ B.toNat ∧ B.toNat % 8 = 0 ∧ B.toNat + 480 ≤ lo
  loLe : lo ≤ heapNext u
  apartB : Apart B 480 R 48 ∧ Apart B 480 Q 48
  rows : ∀ i < 6, u.getMem (R + BitVec.ofNat 64 (8 * i)) = (rowsOf A).getD i 0
  rowsLen : (rowsOf A).length = 6
  heights : ∀ i < 6, u.getMem (Q + BitVec.ofNat 64 (8 * i)) =
    BitVec.ofNat 64 ((tableLogHeightsRust (rowsOf A)).getD i 0)
  tables : ∀ i t, tablesRust[i]? = some t → TableAt u (B + BitVec.ofNat 64 (80 * i)) t
  opcodes : ∀ i < 5, u.getMem (B + BitVec.ofNat 64 (80 * i + 72)) = BitVec.ofNat 64 i
  below : ∀ i < 6, ∀ x, tableDeep u (B + BitVec.ofNat 64 (80 * i)) x → x.toNat < lo
  /-- What a table reaches misses the last opcode's word. -/
  sep : ∀ i < 6, ∀ x, tableDeep u (B + BitVec.ofNat 64 (80 * i)) x → ¬ Within x (B + 472) 8

theorem tablesRust_some {i : Nat} {t : TableRust} (h : tablesRust[i]? = some t) : i < 6 := by
  have : tablesRust.length = 6 := rfl
  have := (List.getElem?_eq_some_iff.mp h).1
  omega

/-- What a table reaches is in the heap below `NEXT`. -/
theorem TableAt.deep_below {u : MachineState} {a : Word} {t : TableRust} (h : TableAt u a t)
    {x : Word} (hx : tableDeep u a x) : heapStart ≤ x.toNat ∧ x.toNat < heapNext u := by
  rcases hx with hx | hx
  · have hb := vecBuf_bounds h.padVec (by decide)
    simp only [Within] at hx
    rcases hb.2 with h0 | h0
    · omega
    · exact ⟨by omega, by omega⟩
  · exact h.ok.deep_below hx

theorem AtR10.base {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q B : Word} (h : AtR10 OI s u A k R Q B) :
    Base10 OI s u A k R Q B (heapNext u) where
  inv := h.inv
  proofPtr := h.proofPtr
  checked := h.checked
  ok := h.ok
  rate := h.rate
  tracks := h.tracks
  spills := h.spills
  slots := h.slots
  bufR := h.bufR
  bufQ := ⟨h.bufQ.1, h.bufQ.2.1, h.bufQ.2.2⟩
  bufB := h.bufB
  loLe := le_refl _
  apartB := h.apartB
  rows := fun i hi ↦ by
    rw [← h.rows]
    interval_cases i <;> simp
  rowsLen := by rw [← h.rows]; rfl
  heights := h.heights
  tables := h.tables
  opcodes := h.opcodes
  below := fun i hi x hx ↦ by
    have hl : i < tablesRust.length := by
      have : tablesRust.length = 6 := rfl
      omega
    obtain ⟨t, ht⟩ : ∃ t, tablesRust[i]? = some t := ⟨_, List.getElem?_eq_getElem hl⟩
    exact ((h.tables i t ht).deep_below hx).2
  sep := fun i hi x hx hw ↦ by
    have hB := h.bufB
    have hh := h.inv.heap.hi
    simp only [heapEnd] at hh
    exact h.sep i hi x hx (by simp only [Within] at hw ⊢; addr_omega [hw, hB, hh])

/-- Two ranges no byte of which is in both are apart. -/
theorem apart_of_bytes {a b : Word} {n m : Nat}
    (h : ∀ y, Within y a n → ¬ Within y b m) : Apart a n b m := by
  simp only [Apart]
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨hn, hm, h1, h2⟩ := hc
  by_cases hab : a.toNat ≤ b.toNat
  · exact h b ⟨hab, by omega⟩ ⟨le_refl _, by omega⟩
  · exact h a ⟨le_refl _, by omega⟩ ⟨by omega, by omega⟩

/-- What the code writes from `0x80002e40` on, and the last opcode's word. -/
@[rv_addr] def X10 (s : MachineState) (lo : Nat) (B : Word) (v : MachineState) (a : Word) : Prop :=
  W10 s lo v a ∨ Within a (B + 472) 8

section Keep
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
  {A : List E} {k : Nat} {R Q B : Word} {lo : Nat}

/-- The heap below `lo` but the last opcode's word, and the frame below `sp + 576` but `sp + 184`,
are not in `X10`. -/
theorem X10.heap (hpre : WalkPre s) (h : Base10 OI s u A k R Q B lo) {x : Word}
    (hx1 : heapStart ≤ x.toNat) (hx2 : x.toNat < lo) (hx3 : ¬ Within x (B + 472) 8) :
    ¬ X10 s lo B v x := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hh := h.inv.heap.hi; have hl := h.loLe; simp only [heapEnd] at hh
  simp only [X10, W10, Within, heapStart] at hx1 hx3 ⊢
  rintro ((⟨h1, -⟩ | h1 | h1 | h1 | ⟨h1, -⟩) | h1)
  · addr_omega [h1, hx1, hx2, hb1, hh, hl]
  · addr_omega [h1, hx1, hx2, hb1, hh, hl]
  · addr_omega [h1, hx1, hx2, hb1, hh, hl]
  · addr_omega [h1, hx1, hx2, hh, hl]
  · omega
  · exact hx3 h1

theorem X10.frame (hpre : WalkPre s) (h : Base10 OI s u A k R Q B lo) (hv : HeapOk v) {x : Word}
    (hx1 : (s.getReg .x2 - 2656).toNat ≤ x.toNat)
    (hx2 : x.toNat < (s.getReg .x2 - 2080).toNat) (hx3 : ¬ Within x (s.getReg .x2 - 2472) 8) :
    ¬ X10 s lo B v x := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hB := h.bufB
  have hh0 := h.inv.heap.hi; have hl := h.loLe; simp only [heapEnd] at hh0
  simp only [X10, W10, Within] at hx3 ⊢
  rintro ((⟨h1, -⟩ | h1 | h1 | h1 | ⟨h1, h2⟩) | h1)
  · omega
  · exact hx3 h1
  · addr_omega [h1, hx1, hb1]
  · addr_omega [h1, hx1, hx2, hb1]
  · have hh := hv.hi
    simp only [heapEnd] at hh
    addr_omega [h2, hh, hx1, hb1]
  · addr_omega [h1, hx1, hb1, hB, hh0, hl]

/-- `X10` is what the function may write, apart from the saved registers. -/
theorem X10.w (hpre : WalkPre s) (h : Base10 OI s u A k R Q B lo) (hv : HeapOk v)
    (mono : heapNext u ≤ heapNext v) {a : Word}
    (ha : X10 s lo B v a) : WalkW s v a ∧ ¬ Within a (s.getReg .x2 - 104) 104 := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hB := h.bufB
  have hh := hv.hi
  have hl := h.loLe
  simp only [heapEnd] at hh
  simp only [X10, W10, Within] at ha
  rcases ha with (⟨h1, h2⟩ | h1 | h1 | h1 | ⟨h1, h2⟩) | h1
  · exact ⟨Or.inr (Or.inl (by rw [stackLo_eq, stack_eq]; simp only [Within]; addr_omega [h1, h2, hb1])),
      by simp only [Within]; addr_omega [h1, h2, hb1]⟩
  · exact ⟨Or.inr (Or.inl (by rw [stackLo_eq, stack_eq]; simp only [Within]; addr_omega [h1, hb1])),
      by simp only [Within]; addr_omega [h1, hb1]⟩
  · exact ⟨Or.inr (Or.inl (by rw [stackLo_eq, stack_eq]; simp only [Within]; addr_omega [h1, hb1])),
      by simp only [Within]; addr_omega [h1, hb1]⟩
  · exact ⟨Or.inr (Or.inr (Or.inl h1)), by simp only [Within]; addr_omega [h1, hb1]⟩
  · refine ⟨Or.inr (Or.inr (Or.inr ⟨by omega, h2⟩)), ?_⟩
    simp only [Within, heapNext] at h2 hh ⊢
    addr_omega [h2, hh, hb1]
  · simp only [heapNext] at hh hl mono hB
    refine ⟨Or.inr (Or.inr (Or.inr ⟨by addr_omega [h1, hB, hl], by addr_omega [h1, hB, hl, mono]⟩)), ?_⟩
    simp only [Within]
    addr_omega [h1, hB, hl, mono, hh, hb1]

/-- A word of the heap below `lo` apart from the last opcode's is kept. -/
theorem X10.heapWord (hpre : WalkPre s) (h : Base10 OI s u A k R Q B lo) {w : Word → Prop}
    (fr : Layout.DFrame u v w) (hw : ∀ a, w a → X10 s lo B v a) {x : Word} (h1 : heapStart ≤ x.toNat)
    (h2 : x.toNat + 8 ≤ lo) (h3 : Apart x 8 (B + 472) 8) : v.getMem x = u.getMem x := by
  have hh := h.inv.heap.hi
  have hl := h.loLe
  have hB := h.bufB
  simp only [heapEnd] at hh
  exact fr x (fun y hy hwy ↦ X10.heap hpre h (by simp only [Within, heapStart] at hy h1 ⊢; addr_omega [hy, h1, h2, hh, hl])
    (by simp only [Within] at hy; addr_omega [hy, h1, h2, hh, hl])
    (by simp only [Within, Apart] at hy h3 ⊢; addr_omega [hy, h3, hB, hh, hl]) (hw y hwy))
    (by addr_omega [h2, hh, hl])

/-- A word of the frame below `sp + 576` but `sp + 184` is kept. -/
theorem X10.frameWord (hpre : WalkPre s) (h : Base10 OI s u A k R Q B lo) (hv : HeapOk v)
    {w : Word → Prop} (fr : Layout.DFrame u v w) (hw : ∀ a, w a → X10 s lo B v a) {x : Word}
    (h1 : (s.getReg .x2 - 2656).toNat ≤ x.toNat) (h2 : x.toNat + 8 ≤ (s.getReg .x2 - 2080).toNat)
    (h3 : Apart x 8 (s.getReg .x2 - 2472) 8) : v.getMem x = u.getMem x := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  exact fr x (fun y hy hwy ↦ X10.frame hpre h hv (by simp only [Within] at hy; addr_omega [hy, h1, hb1])
    (by simp only [Within] at hy; addr_omega [hy, h2, hb1])
    (by simp only [Within, Apart] at hy h3 ⊢; addr_omega [hy, h3, hb1]) (hw y hwy))
    (by addr_omega [h2, hb1])

theorem Base10.keep (hpre : WalkPre s) (h : Base10 OI s u A k R Q B lo) {w : Word → Prop}
    (fr : Layout.DFrame u v w) (hw : ∀ a, w a → X10 s lo B v a) (hv : HeapOk v)
    (mono : heapNext u ≤ heapNext v) (sp : v.getReg .x2 = u.getReg .x2) :
    Base10 OI s v A k R Q B lo := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have fr' : Layout.DFrame u v (X10 s lo B v) := fr.mono hw
  have Iv : Inv s v := h.inv.stepL hpre fr' (fun a ha ↦ X10.w hpre h hv mono ha) hv mono sp
  have hh := h.inv.heap.hi
  have hl := h.loLe
  simp only [heapEnd] at hh
  have hR := h.bufR
  have hQ := h.bufQ
  have hB := h.bufB
  have fw (x : Word) (h1 : (s.getReg .x2 - 2656).toNat ≤ x.toNat)
      (h2 : x.toNat + 8 ≤ (s.getReg .x2 - 2080).toNat) (h3 : Apart x 8 (s.getReg .x2 - 2472) 8) :
      v.getMem x = u.getMem x := X10.frameWord hpre h hv fr hw h1 h2 h3
  have hw8 (x : Word) (h1 : heapStart ≤ x.toNat) (h2 : x.toNat + 8 ≤ lo) (h3 : Apart x 8 (B + 472) 8) :
      v.getMem x = u.getMem x := X10.heapWord hpre h fr hw h1 h2 h3
  have nw (x : Word) (h1 : heapStart ≤ x.toNat) (h2 : x.toNat < lo) (h3 : ¬ Within x (B + 472) 8) :
      ¬ X10 s lo B v x := X10.heap hpre h h1 h2 h3
  have slot (o : Nat) (ho1 : 2080 + 8 ≤ o) (ho2 : o ≤ 2656) (ho3 : o ≠ 2472) (ho4 : o % 8 = 0) :
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 o) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 o) :=
    fw _ (by addr_omega [hb1, ho2]) (by addr_omega [hb1, ho1, ho2])
      (by simp only [Apart]; addr_omega [hb1, ho1, ho2, ho3, ho4])
  have hT : ∀ T, TranscriptAt u (tp s) T → TranscriptAt v (tp s) T := fun T hT' ↦ by
    obtain ⟨e0, e1, e2⟩ := proofVals hpre h.inv h.proofPtr
    have pRO := hpre.proofRO
    have sRO := hpre.streamRO
    have hP := hpre.proof
    have hS := hpre.stream
    simp only [ReadOnly, Outside, stack_eq, heapEnd] at pRO sRO
    obtain ⟨⟨p1, p1'⟩, p2, -⟩ := pRO
    obtain ⟨⟨s1, s1'⟩, s2, -⟩ := sRO
    simp only [Region] at hP
    have hm0 := h.inv.mono
    have hvh := hv.hi
    simp only [heapEnd] at hvh
    refine (lframe_d fr').transcriptAt hT' (tok hpre h.inv h.proofPtr) ?_ ?_ ?_ ?_
    · intro y hy hw
      simp only [X10, W10, Within, tp, heapNext] at hy hw hvh hB hl hh
      rcases hw with ((hw | hw | hw | hw | hw) | hw) | hw <;> addr_omega [hy, hw, hvh, hb1, hB, hl, hh]
    · rw [e0]; intro y hy hw
      simp only [X10, W10, Within, heapNext] at hy hw hvh hm0 p1 hl hh
      rcases hw with ((hw | hw | hw | hw | hw) | hw) | hw <;>
        addr_omega [hy, hw, hvh, hb1, p1, p1', p2, hP, hB, hm0, hl, hh]
    · rw [e1, e2]; intro y hy hw
      simp only [X10, W10, Within, heapNext] at hy hw hvh hm0 s1 hl hh
      rcases hS with h0 | h0
      · rw [h0] at hy; omega
      simp only [Region] at h0
      rcases hw with ((hw | hw | hw | hw | hw) | hw) | hw <;>
        addr_omega [hy, hw, hvh, hb1, s1, s1', s2, h0, hB, hm0, hl, hh]
    · intro y hy hw
      simp only [X10, W10, Within, tp, heapNext] at hy hw hvh hB hl hh
      rcases hw with ((hw | hw | hw | hw | hw) | hw) | hw <;> addr_omega [hy, hw, hvh, hb1, hB, hl, hh]
  -- the tables
  have hTab (i : Nat) (t : TableRust) (ht : tablesRust[i]? = some t) :
      TableAt v (B + BitVec.ofNat 64 (80 * i)) t ∧
        tableDeep v (B + BitVec.ofNat 64 (80 * i)) = tableDeep u (B + BitVec.ofNat 64 (80 * i)) := by
    have hi := tablesRust_some ht
    have hs0 := hpre.heap.lo
    simp only [heapStart] at hs0
    have T := h.tables i t ht
    have hbl := h.below i hi
    set a := B + BitVec.ofNat 64 (80 * i) with ha
    have haN : a.toNat = B.toNat + 80 * i := by rw [ha]; addr_omega [hB, hh, hi, hl, hh, hs0]
    clear_value a
    have ha80 : a.toNat + 80 ≤ lo ∧ 536870912 ≤ a.toNat := by omega
    have hsp := h.sep i hi
    rw [← ha] at hsp
    have fl := flushesOf_frame fr' T.ok (fun x hx ↦ nw x (by simp only [Within] at hx; addr_omega [hx, haN, hB, hl, hh, hs0, ha80])
        (by simp only [Within] at hx; addr_omega [hx, haN, hB, hi, hl, hh, hs0, ha80])
        (by simp only [Within] at hx ⊢; addr_omega [hx, haN, hB, hi, hl, hh, hs0, ha80]))
      (fun x hx ↦ nw x ((T.ok.deep_below hx).1) (hbl x (Or.inr hx)) (hsp x (Or.inr hx))) (by addr_omega [haN, hB, hh, hi, hl, hh, hs0, ha80])
      h.inv.heap mono
    have g0 : v.getMem a = u.getMem a := hw8 a (by simp only [heapStart]; omega) (by omega)
      (by simp only [Apart]; addr_omega [haN, hB, hi, hl, hh, hs0, ha80])
    have g8 : v.getMem (a + 8) = u.getMem (a + 8) :=
      hw8 _ (by simp only [heapStart]; addr_omega [haN, hB, hl, hh, hs0, ha80]) (by addr_omega [haN, hB, hi, hl, hh, hs0, ha80])
        (by simp only [Apart]; addr_omega [haN, hB, hi, hl, hh, hs0, ha80])
    have g16 : v.getMem (a + 16) = u.getMem (a + 16) :=
      hw8 _ (by simp only [heapStart]; addr_omega [haN, hB, hl, hh, hs0, ha80]) (by addr_omega [haN, hB, hi, hl, hh, hs0, ha80])
        (by simp only [Apart]; addr_omega [haN, hB, hi, hl, hh, hs0, ha80])
    have hpb := vecBuf_bounds T.padVec (by decide)
    have hpl := T.padVec.len
    have hcap : vecCap v a = vecCap u a := g0
    have hptr : vecPtr v a = vecPtr u a := g8
    have hlen : vecLen v a = vecLen u a := g16
    have hdeep : tableDeep v a = tableDeep u a := by
      funext x
      simp only [tableDeep, hcap, hptr, fl.2.2.1]
    refine ⟨⟨⟨?_, ?_⟩, ?_, fl.2.1, by rw [fl.1]; exact T.flushes⟩, hdeep⟩
    · have hraw := T.padVec.raw
      simp only [RawVecOk, Buf, hptr, hcap] at hraw ⊢
      exact ⟨hraw.1, hraw.2.imp id fun h' ↦ ⟨h'.1, Nat.le_trans h'.2 mono⟩⟩
    · rw [hcap, hlen]; exact hpl
    · rw [← T.pad]
      simp only [vecEs, hptr, hlen]
      refine Bus.eListAt_congr fun j hj ↦ ?_
      have hbuf : (vecPtr u a).toNat + 24 * j + 24 ≤ lo ∧ heapStart ≤ (vecPtr u a).toNat := by
        rcases hpb.2 with h0 | h0
        · omega
        · have := hbl (vecPtr u a + BitVec.ofNat 64 (24 * j + 23)) (Or.inl (by
            simp only [Within]; addr_omega [h0, hj, hpl, hh, hl, hh, hs0, ha80]))
          refine ⟨by addr_omega [this, h0, hj, hpl, hh, hl, hh, hs0, ha80], h0.1⟩
      simp only [heapStart] at hbuf
      have hap : Apart (vecPtr u a + BitVec.ofNat 64 (24 * j)) 24 (B + 472) 8 := by
        rcases hpb.2 with h0 | h0
        · omega
        refine apart_of_bytes fun y hy hy' ↦ hsp y (Or.inl (by
            simp only [Within] at hy ⊢; addr_omega [hy, h0, hj, hpl, hh, hl, hs0, ha80])) hy'
      simp only [Apart] at hap
      exact eAt_congr (hw8 _ (by simp only [heapStart]; addr_omega [hbuf, hh, hl, hh, hs0, ha80]) (by addr_omega [hbuf, hh, hl, hh, hs0, ha80])
          (by simp only [Apart]; addr_omega [hap, hbuf, hh, hl, hs0, ha80, hB]))
        (hw8 _ (by simp only [heapStart]; addr_omega [hbuf, hh, hl, hh, hs0, ha80]) (by addr_omega [hbuf, hh, hl, hh, hs0, ha80])
          (by simp only [Apart]; addr_omega [hap, hbuf, hh, hl, hs0, ha80, hB]))
        (hw8 _ (by simp only [heapStart]; addr_omega [hbuf, hh, hl, hh, hs0, ha80]) (by addr_omega [hbuf, hh, hl, hh, hs0, ha80])
          (by simp only [Apart]; addr_omega [hap, hbuf, hh, hl, hs0, ha80, hB]))
  exact {
    inv := Iv
    proofPtr := by
      rw [fw _ (by rw [tp]; addr_omega [hb1]) (by rw [tp]; addr_omega [hb1])
        (by simp only [Apart, tp]; addr_omega [hb1])]
      exact h.proofPtr
    checked := by
      have ha : (tp s + 360).toNat % 8 = 0 := by rw [tp]; addr_omega [hb1, hb3]
      rw [byteAt_congr ha (fw _ (by rw [tp]; addr_omega [hb1]) (by rw [tp]; addr_omega [hb1])
        (by simp only [Apart, tp]; addr_omega [hb1]))]
      exact h.checked
    ok := h.ok
    rate := h.rate
    tracks := h.tracks.keep hT
    spills := by
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h.spills
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (slot 2584 (by decide) (by decide) (by decide) (by decide)).trans a1
      · exact (slot 2576 (by decide) (by decide) (by decide) (by decide)).trans a2
      · exact (slot 2568 (by decide) (by decide) (by decide) (by decide)).trans a3
      · exact (slot 2560 (by decide) (by decide) (by decide) (by decide)).trans a4
      · exact (slot 2552 (by decide) (by decide) (by decide) (by decide)).trans a5
      · exact (slot 2528 (by decide) (by decide) (by decide) (by decide)).trans a6
      · exact (slot 2512 (by decide) (by decide) (by decide) (by decide)).trans a7
      · exact (slot 2496 (by decide) (by decide) (by decide) (by decide)).trans a8
      · exact (slot 2488 (by decide) (by decide) (by decide) (by decide)).trans a9
    slots := by
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h.slots
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (slot 2536 (by decide) (by decide) (by decide) (by decide)).trans a1
      · exact (slot 2520 (by decide) (by decide) (by decide) (by decide)).trans a2
      · exact (slot 2504 (by decide) (by decide) (by decide) (by decide)).trans a3
      · exact (slot 2480 (by decide) (by decide) (by decide) (by decide)).trans a4
      · exact (slot 2464 (by decide) (by decide) (by decide) (by decide)).trans a5
      · exact (slot 2456 (by decide) (by decide) (by decide) (by decide)).trans a6
    bufR := h.bufR
    bufQ := h.bufQ
    bufB := h.bufB
    loLe := h.loLe.trans mono
    apartB := h.apartB
    rows := fun i hi ↦ by
      have ap := h.apartB.1
      simp only [Apart] at ap
      rw [hw8 _ (by simp only [heapStart]; addr_omega [hR, hi, hl, hh, hpre.heap.lo]) (by addr_omega [hR, hi, hl, hh, hpre.heap.lo])
        (by simp only [Apart]; addr_omega [ap, hR, hB, hi, hl, hh, hpre.heap.lo])]
      exact h.rows i hi
    rowsLen := h.rowsLen
    heights := fun i hi ↦ by
      rw [hw8 _ (by simp only [heapStart]; addr_omega [hQ, hR, hi, h.inv.heap.lo, hl, hh, hpre.heap.lo])
        (by addr_omega [hQ, hi, hl, hh, hpre.heap.lo])
        (by have ap := h.apartB.2; simp only [Apart] at ap ⊢; addr_omega [ap, hQ, hB, hi, hl, hh, hpre.heap.lo])]
      exact h.heights i hi
    tables := fun i t ht ↦ (hTab i t ht).1
    opcodes := fun i hi ↦ by
      rw [hw8 _ (by simp only [heapStart]; addr_omega [hB, hi, h.inv.heap.lo, hl, hh, hpre.heap.lo]) (by addr_omega [hB, hi, hl, hh, hpre.heap.lo])
        (by simp only [Apart]; addr_omega [hB, hi, hl, hh, hpre.heap.lo])]
      exact h.opcodes i hi
    below := fun i hi x hx ↦ by
      have hl6 : i < tablesRust.length := by
        have : tablesRust.length = 6 := rfl
        omega
      rw [(hTab i _ (List.getElem?_eq_getElem hl6)).2] at hx
      exact h.below i hi x hx
    sep := fun i hi x hx ↦ by
      have hl6 : i < tablesRust.length := by
        have : tablesRust.length = 6 := rfl
        omega
      rw [(hTab i _ (List.getElem?_eq_getElem hl6)).2] at hx
      exact h.sep i hi x hx }

end Keep

end Rv64Verifier.Proofs.Walk
