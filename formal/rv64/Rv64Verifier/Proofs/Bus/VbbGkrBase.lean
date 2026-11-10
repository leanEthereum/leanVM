import Rv64Verifier.Proofs.Bus.VbbSpine

/-!
# `verify_bus_balance`: the GKR loop's frame

An iteration pushes the layer's three values into the buffer `values` has held since the start, at
`P`: its first 72 bytes lie in the heap allocated before the loop, so a step of an iteration
writes `Free` or `[P, P + 72)` (`FreeV`). `Kept`'s buffers lie below `P` (`Fence`,
`AfterStart.fence`), so the pushes keep them.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript

/-- What an iteration writes: `Free` and `values`' first 72 bytes. -/
def FreeV (s : MachineState) (P : Word) (a : Word) : Prop := Free s a ∨ Within a P 72

theorem Free.lo {s : MachineState} (hpre : BusBalancePre s) {y : Word} (h : Free s y) :
    (s.getReg .x2 - 1344).toNat ≤ y.toNat := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rcases h with h | h | h | h | h | h | h <;> addr_omega [h, hb1]

/-- A word of a step writing `FreeV` keeps its value: in the frame outside `Free`, or allocated
since the entry and below `P`. -/
theorem StepR.wordV {s v w : MachineState} {P : Word} (hpre : BusBalancePre s)
    (st : StepR s v w (FreeV s P)) (hP : P.toNat + 72 ≤ heapEnd) {x : Word}
    (hx : ((s.getReg .x2 - 1344).toNat ≤ x.toNat ∧ x.toNat + 8 ≤ (s.getReg .x2).toNat ∧
      ∀ y, Within y x 8 → ¬ Free s y) ∨
      (heapNext s ≤ x.toNat ∧ x.toNat + 8 ≤ heapNext v ∧ x.toNat + 8 ≤ P.toNat)) :
    w.getMem x = v.getMem x := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hh := st.heap.hi
  have hm := st.mono
  simp only [heapEnd, heapNext] at hP hh hm
  rcases hx with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine st.word hpre (fun y hy hf ↦ ?_) (Or.inl ⟨h1, h2⟩)
    rcases hf with hf | hf
    · exact h3 y hy hf
    · addr_omega [hy, hf, hb1, hP, h1]
  · refine st.word hpre (fun y hy hf ↦ ?_) (Or.inr ⟨h1, h2⟩)
    rcases hf with hf | hf
    · have := Free.lo hpre hf
      simp only [heapNext] at h1 h2
      addr_omega [hy, this, hb1, h2, hh, hm]
    · addr_omega [hy, hf, h3]

theorem _root_.Rv64Verifier.Transcript.NewVecE.keepMem {s v w : MachineState} {a : Word}
    {xs : List E} (h : NewVecE s v a xs) (hv : HeapOk v) (hm : heapNext v ≤ heapNext w)
    (e0 : w.getMem a = v.getMem a) (e8 : w.getMem (a + 8) = v.getMem (a + 8))
    (e16 : w.getMem (a + 16) = v.getMem (a + 16))
    (hb : ∀ x : Word, (vecPtr v a).toNat ≤ x.toNat →
      x.toNat + 8 ≤ (vecPtr v a).toNat + (vecCap v a).toNat * 24 → w.getMem x = v.getMem x) :
    NewVecE s w a xs := by
  have hvec := h.vec
  have hbuf := h.buf
  have hlen := hvec.len
  refine ⟨hvec.keep e0 e8 e16 hm, ?_, ?_⟩
  · simp only [NewBuf, vecPtr, vecCap] at hbuf ⊢
    rw [e8, e0]
    exact ⟨hbuf.1, hbuf.2.imp_right fun h' ↦ ⟨h'.1, by omega⟩⟩
  · rw [← h.elems]
    simp only [vecEs, vecPtr, vecLen] at hlen hbuf hb ⊢
    rw [e8, e16]
    refine eListAt_congr fun i hi ↦ ?_
    have hc : 24 * i + 24 ≤ (vecCap v a).toNat * 24 := by omega
    have hbd : (v.getMem (a + 8)).toNat + (vecCap v a).toNat * 24 ≤ 2 ^ 64 := by
      rcases hbuf.2 with h0 | ⟨b1, b2⟩
      · omega
      · have := hv.hi
        simp only [heapNext, heapEnd] at *; omega
    have bw (j : Nat) (hj : j + 8 ≤ 24) : w.getMem (v.getMem (a + 8) + BitVec.ofNat 64 (24 * i) +
        BitVec.ofNat 64 j) = v.getMem (v.getMem (a + 8) + BitVec.ofNat 64 (24 * i) +
        BitVec.ofNat 64 j) :=
      hb _ (by addr_omega [hbd, hc, hj]) (by addr_omega [hbd, hc, hj])
    exact eAt_congr (by simpa using bw 0 (by omega)) (bw 8 (by omega)) (bw 16 (by omega))

theorem LayoutAt.keepMem {s v w : MachineState} {a : Word} {l : BusLayoutRust}
    (h : LayoutAt s v a l) (hv : HeapOk v) (hm : heapNext v ≤ heapNext w)
    (hw : ∀ j, j + 8 ≤ 56 → w.getMem (a + BitVec.ofNat 64 j) = v.getMem (a + BitVec.ofNat 64 j))
    (hf : ∀ x : Word, (vecPtr v a).toNat ≤ x.toNat →
      x.toNat + 8 ≤ (vecPtr v a).toNat + 16 * (vecCap v a).toNat → w.getMem x = v.getMem x)
    (ht : ∀ x : Word, (vecPtr v (a + 24)).toNat ≤ x.toNat →
      x.toNat + 8 ≤ (vecPtr v (a + 24)).toNat + 16 * (vecCap v (a + 24)).toNat →
      w.getMem x = v.getMem x) :
    LayoutAt s w a l := by
  have e0 : w.getMem a = v.getMem a := by simpa using hw 0 (by omega)
  have e8 : w.getMem (a + 8) = v.getMem (a + 8) := hw 8 (by omega)
  have e16 : w.getMem (a + 16) = v.getMem (a + 16) := hw 16 (by omega)
  have e24 : w.getMem (a + 24) = v.getMem (a + 24) := hw 24 (by omega)
  have e32 : w.getMem (a + 24 + 8) = v.getMem (a + 24 + 8) := by
    rw [BitVec.add_assoc]; exact hw 32 (by omega)
  have e40 : w.getMem (a + 24 + 16) = v.getMem (a + 24 + 16) := by
    rw [BitVec.add_assoc]; exact hw 40 (by omega)
  have e48 : w.getMem (a + 48) = v.getMem (a + 48) := hw 48 (by omega)
  have pk {b : Word} (hvb : VecOk v b 16 8)
      (hb : NewBuf s v (vecPtr v b) (16 * (vecCap v b).toNat) 8)
      (h8 : w.getMem (b + 8) = v.getMem (b + 8)) (h16 : w.getMem (b + 16) = v.getMem (b + 16))
      (ho : ∀ x : Word, (vecPtr v b).toNat ≤ x.toNat →
        x.toNat + 8 ≤ (vecPtr v b).toNat + 16 * (vecCap v b).toNat → w.getMem x = v.getMem x) :
      placementsAt w b = placementsAt v b := by
    have hlen := hvb.len
    simp only [placementsAt, vecPtr, vecLen] at hb hlen ho ⊢
    rw [h8, h16]
    refine List.map_congr_left fun i hi ↦ ?_
    simp only [List.mem_range] at hi
    have hc : 16 * i + 16 ≤ 16 * (vecCap v b).toNat := by omega
    have hbd : (v.getMem (b + 8)).toNat + 16 * (vecCap v b).toNat ≤ 2 ^ 64 := by
      rcases hb.2 with h0 | ⟨b1, b2⟩
      · omega
      · have := hv.hi
        simp only [heapNext, heapEnd] at *; omega
    rw [ho _ (by addr_omega [hbd, hc]) (by addr_omega [hbd, hc]),
      ho _ (by addr_omega [hbd, hc]) (by addr_omega [hbd, hc])]
  refine ⟨?_, h.framework.keep e0 e8 e16 hm, ?_, h.tables.keep e24 e32 e40 hm, ?_⟩
  · rw [← h.value]
    simp only [busLayoutOf, e48]
    rw [pk h.framework h.frameworkNew e8 e16 hf, pk h.tables h.tablesNew e32 e40 ht]
  · have := h.frameworkNew
    simp only [NewBuf, vecPtr, vecCap] at this ⊢
    rw [e8, e0]
    exact ⟨this.1, this.2.imp_right fun h' ↦ ⟨h'.1, by omega⟩⟩
  · have := h.tablesNew
    simp only [NewBuf, vecPtr, vecCap] at this ⊢
    rw [e32, e24]
    exact ⟨this.1, this.2.imp_right fun h' ↦ ⟨h'.1, by omega⟩⟩

section V
variable {s v w : MachineState} {P : Word}

theorem LayoutAt.keepV (hpre : BusBalancePre s) (hv : HeapOk v) (st : StepR s v w (FreeV s P))
    (hP : P.toNat + 72 ≤ heapEnd) {a : Word} {l : BusLayoutRust} (h : LayoutAt s v a l)
    (hin : InFrame s a 56) (hap : ∀ y, Within y a 56 → ¬ Free s y)
    (hf : BufBelow v a 16 P ∧ BufBelow v (a + 24) 16 P) :
    LayoutAt s w a l ∧ BufBelow w a 16 P ∧ BufBelow w (a + 24) 16 P := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  simp only [InFrame] at hin
  have hw (j : Nat) (hj : j + 8 ≤ 56) : w.getMem (a + BitVec.ofNat 64 j) =
      v.getMem (a + BitVec.ofNat 64 j) :=
    st.wordV hpre hP (Or.inl ⟨by addr_omega [hin, hj, hb1], by addr_omega [hin, hj, hb1],
      fun y hy ↦ hap y (by addr_omega [hy, hin, hj, hb1])⟩)
  have hbuf {b : Word} (hb : NewBuf s v (vecPtr v b) (16 * (vecCap v b).toNat) 8)
      (hbe : BufBelow v b 16 P) (x : Word) (h1 : (vecPtr v b).toNat ≤ x.toNat)
      (h2 : x.toNat + 8 ≤ (vecPtr v b).toNat + 16 * (vecCap v b).toNat) :
      w.getMem x = v.getMem x := by
    simp only [NewBuf, BufBelow] at hb hbe
    rcases hb.2 with h0 | ⟨b1, b2⟩
    · omega
    rcases hbe with h0 | hbe
    · omega
    exact st.wordV hpre hP (Or.inr ⟨by omega, by omega, by omega⟩)
  have e0 : w.getMem a = v.getMem a := by simpa using hw 0 (by omega)
  have e8 : w.getMem (a + 8) = v.getMem (a + 8) := hw 8 (by omega)
  have e24 : w.getMem (a + 24) = v.getMem (a + 24) := hw 24 (by omega)
  have e32 : w.getMem (a + 24 + 8) = v.getMem (a + 24 + 8) := by
    rw [BitVec.add_assoc]; exact hw 32 (by omega)
  refine ⟨h.keepMem hv st.mono hw (hbuf h.frameworkNew hf.1) (hbuf h.tablesNew hf.2), ?_, ?_⟩
  · simp only [BufBelow, vecPtr, vecCap, e0, e8]; exact hf.1
  · simp only [BufBelow, vecPtr, vecCap, e24, e32]; exact hf.2

theorem _root_.Rv64Verifier.Transcript.NewVecE.keepV (hpre : BusBalancePre s) (hv : HeapOk v)
    (st : StepR s v w (FreeV s P)) (hP : P.toNat + 72 ≤ heapEnd) {a : Word} {xs : List E}
    (h : NewVecE s v a xs)
    (hin : (s.getReg .x2 - 1344).toNat ≤ a.toNat ∧ a.toNat + 24 ≤ (s.getReg .x2).toNat)
    (hap : ∀ y, Within y a 24 → ¬ Free s y) (hf : BufBelow v a 24 P) :
    NewVecE s w a xs ∧ BufBelow w a 24 P := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hw (j : Nat) (hj : j + 8 ≤ 24) : w.getMem (a + BitVec.ofNat 64 j) =
      v.getMem (a + BitVec.ofNat 64 j) :=
    st.wordV hpre hP (Or.inl ⟨by addr_omega [hin, hj, hb1], by addr_omega [hin, hj, hb1],
      fun y hy ↦ hap y (by addr_omega [hy, hin, hj, hb1])⟩)
  have e0 : w.getMem a = v.getMem a := by simpa using hw 0 (by omega)
  have e8 : w.getMem (a + 8) = v.getMem (a + 8) := hw 8 (by omega)
  have e16 : w.getMem (a + 16) = v.getMem (a + 16) := hw 16 (by omega)
  refine ⟨h.keepMem hv st.mono e0 e8 e16 fun x h1 h2 ↦ ?_, ?_⟩
  · have hb := h.buf
    have hbe := hf
    simp only [NewBuf, BufBelow] at hb hbe
    rcases hb.2 with h0 | ⟨b1, b2⟩
    · omega
    rcases hbe with h0 | hbe
    · omega
    exact st.wordV hpre hP (Or.inr ⟨by omega, by omega, by omega⟩)
  · simp only [BufBelow, vecPtr, vecCap, e0, e8]; exact hf

/-- A step writing `FreeV` keeps what the start left, and the fence. -/
theorem Kept.stepV {k : Start} (hpre : BusBalancePre s) (h : Kept s v k) (F : Fence s v P)
    (hv : HeapOk v) (hP : P.toNat + 72 ≤ heapEnd) (st : StepR s v w (FreeV s P)) :
    Kept s w k ∧ Fence s w P := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have wd (j : Nat) (hj : 8 ≤ j) (hj2 : j ≤ 1344)
      (hm : ∀ i, j - 8 < i → i ≤ j → (1312 < i ∧ i ≤ 1344 → False) ∧
        (1264 < i ∧ i ≤ 1304 → False) ∧ (1248 < i ∧ i ≤ 1256 → False) ∧
        (1200 < i ∧ i ≤ 1216 → False) ∧ (1136 < i ∧ i ≤ 1144 → False) ∧
        (1080 < i ∧ i ≤ 1128 → False) ∧ (104 < i ∧ i ≤ 864 → False)) :
      w.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = v.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    st.wordV hpre hP (Or.inl ⟨by addr_omega [hb1, hj, hj2], by addr_omega [hb1, hj, hj2],
      Free.miss hpre hj hj2 hm⟩)
  obtain ⟨p1, p2, p3⟩ := h.push.keepV hpre hv st hP
    (inFrame hpre (k := 1080) (n := 56) (by omega) (by omega))
    (Free.miss hpre (j := 1080) (by omega) (by omega) (by intro i h1 h2; omega)) F.push
  obtain ⟨q1, q2, q3⟩ := h.pull.keepV hpre hv st hP
    (inFrame hpre (k := 1024) (n := 56) (by omega) (by omega))
    (Free.miss hpre (j := 1024) (by omega) (by omega) (by intro i h1 h2; omega)) F.pull
  obtain ⟨r1, r2, r3⟩ := h.count.keepV hpre hv st hP
    (inFrame hpre (k := 968) (n := 56) (by omega) (by omega))
    (Free.miss hpre (j := 968) (by omega) (by omega) (by intro i h1 h2; omega)) F.count
  obtain ⟨a1, a2⟩ := h.alphas.keepV hpre hv st hP (by addr_omega [hb1])
    (Free.miss hpre (j := 912) (by omega) (by omega) (by intro i h1 h2; omega)) F.alphas
  obtain ⟨w1, w2⟩ := h.weights.keepV hpre hv st hP (by addr_omega [hb1])
    (Free.miss hpre (j := 888) (by omega) (by omega) (by intro i h1 h2; omega)) F.weights
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, p1, q1, r1, a1, w1⟩,
    ⟨⟨p2, p3⟩, ⟨q2, q3⟩, ⟨r2, r3⟩, a2, w2⟩⟩
  · rw [← h.out]; exact wd 1312 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.pushLen]; exact wd 1264 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.countLen]; exact wd 1248 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.layout]; exact wd 1240 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.count1]; exact wd 1232 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.count0]; exact wd 1224 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.beta1]; exact wd 1200 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.beta0]; exact wd 1192 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.beta2]; exact wd 1184 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.lm]; exact wd 1136 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.lb]; exact wd 1152 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.pullPtr]; exact wd 1168 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.pullLen]; exact wd 1176 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.countPtr]; exact wd 1160 (by omega) (by omega) (by intro i h1 h2; omega)

/-- A step writing `FreeV`, `values`' bytes allocated since the entry, keeps `Inv`. -/
theorem Inv.afterV (hpre : BusBalancePre s) (h : Inv s v) (st : StepR s v w (FreeV s P))
    (hP1 : heapNext s ≤ P.toNat) (hP2 : P.toNat + 72 ≤ heapNext v) : Inv s w := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hS := hpre.self.self
  have ss := hpre.selfStack
  rw [stackLo_eq] at ss
  have hm := st.mono
  have hh := st.heap.hi
  refine h.step hpre st.frame (fun a ha ↦ ?_) st.heap st.mono st.sp
  rcases ha with (ha | ha) | ha | ha
  · have := Free.frameW hpre a ha
    exact ⟨Or.inr (Or.inr (Or.inl (by rw [stackLo_eq]; addr_omega [this, hb1]))),
      by addr_omega [this, hb1]⟩
  · simp only [Within] at ha
    simp only [heapNext, heapEnd] at hh hm hP1 hP2
    refine ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))), ?_⟩
    · simp only [heapNext]; omega
    · simp only [heapNext]; omega
    · addr_omega [ha, hb1, hP2, hm, hh]
  · exact ⟨Or.inr (Or.inl ha), by addr_omega [ha, hS, ss, hb1]⟩
  · exact Loc.w hpre h st.heap (by
      rcases ha with ha | ha | ha
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ha))

end V

/-! ## The loop's invariant -/

/-- An iteration's layer count: `layer % 2 == 1` takes one level, otherwise two. -/
def stepOf (n : ℕ) : ℕ := if n % 2 = 1 then 1 else 2

/-- At `0x8000669c` (or at the exit `0x80006c7c`), `n` layers left, the loop's state `st`:
`values` at `S - 176` with its buffer at `P`, `point` in `s11`/`s5` with capacity `c`. -/
structure Loop (bev : MachineState → Word → List E → Option E) (s u : MachineState) (k : Start)
    (cnt : E) (P c : Word) (n : ℕ) (st : GkrState) : Prop where
  inv : Inv s u
  kept : Kept s u k
  fence : Fence s u P
  x9 : u.getReg .x9 = 0xffffffffffffffff
  x19 : u.getReg .x19 = P
  x20 : u.getReg .x20 = s.getReg .x12
  x22 : u.getReg .x22 = s.getReg .x12 + 8
  x24 : u.getReg .x24 = 1
  x25 : (u.getReg .x25).toNat = n
  cnt2 : cnt = eOf3 k.count0 k.count1 (u.getMem (s.getReg .x2 - 1256))
  pushPtr : u.getMem (s.getReg .x2 - 1272) = vecPtr s (s.getReg .x11 + 24)
  ptr : vecPtr u (s.getReg .x2 - 176) = P
  point : NewVecR s u c (u.getReg .x27) (u.getReg .x21) st.point
  values : NewVecE s u (s.getReg .x2 - 176) st.values
  len : st.values.length = 3
  tracks : Tracks (prog bev s) (s.getReg .x12) s u (gkrLoopM n st >>= tail bev s k cnt)

/-- A `Vec<E>` of three elements allocated since the entry: its first 72 bytes lie in the heap. -/
theorem _root_.Rv64Verifier.Transcript.NewVecE.heap3 {s u : MachineState} {a : Word}
    {xs : List E} (h : NewVecE s u a xs) (hl : xs.length = 3) (hh : HeapOk u) :
    heapNext s ≤ (vecPtr u a).toNat ∧ (vecPtr u a).toNat + 72 ≤ heapNext u ∧
      (vecPtr u a).toNat + 72 ≤ heapEnd := by
  have hb := h.buf
  have hc := h.vec.len
  have hi := hh.hi
  simp only [NewBuf] at hb
  have h3 : (vecLen u a).toNat = 3 := by rw [← hl, ← h.elems, vecEs, eListAt_length]
  rcases hb.2 with h0 | ⟨b1, b2⟩
  · omega
  · exact ⟨b1, by omega, by omega⟩

theorem Loop.heapP {bev : MachineState → Word → List E → Option E} {s u : MachineState}
    {k : Start} {cnt : E} {P c : Word} {n : ℕ} {st : GkrState}
    (h : Loop bev s u k cnt P c n st) :
    heapNext s ≤ P.toNat ∧ P.toNat + 72 ≤ heapNext u ∧ P.toNat + 72 ≤ heapEnd := by
  have := h.values.heap3 h.len h.inv.heap
  rw [h.ptr] at this
  exact this

/-- One iteration from `0x8000669c`, to the next test's target, or out. -/
def Iter (bev : MachineState → Word → List E → Option E) : Prop :=
  ∀ s u k cnt P c n st, BusBalancePre s → Loop bev s u k cnt P c n st → u.pc = 0x8000669c →
    0 < n → ∃ v, Reaches Image.code u v ∧ (Done bev s v ∨ Dead Image.code v ∨
      ∃ st', Loop bev s v k cnt P (v.getMem (s.getReg .x2 - 248)) (n - stepOf n) st' ∧
        v.pc = if n - stepOf n = 0 then 0x80006c7c else 0x8000669c)

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
