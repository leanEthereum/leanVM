import Rv64Verifier.Proofs.Bus.VbbStart

/-!
# `verify_bus_balance`: the prologue and the three `bus_layout`s

`0x80006428` saves the registers, keeps `out`, `layout`, the transcript and `push` in saved
registers (`Regs`), stores `framework_log_rows = [0, log_memory, log_bytecode]` at `S - 1104` and
the two logs again at `S - 1136`, `S - 1152`, and calls `bus_layout` for push into `S - 1080`.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `log_memory`, `log_bytecode` as stored. -/
def logMem (s : MachineState) : Word := s.getMem (s.getReg .x11 + 152)
def logBc (s : MachineState) : Word := s.getMem (s.getReg .x11 + 160)

/-- The values the function keeps in saved registers from the prologue on. -/
structure Regs (s u : MachineState) : Prop where
  x18 : u.getReg .x18 = s.getReg .x10
  x19 : u.getReg .x19 = s.getReg .x11
  x20 : u.getReg .x20 = s.getReg .x12

/-- The prologue, to the first call of `bus_layout`. -/
theorem prologue {s : MachineState} (hpc : s.pc = 0x80006428) (hpre : BusBalancePre s) :
    ∃ u, Reaches Image.code s u ∧ Inv s u ∧ u.pc = 0x80010acc ∧
      u.getReg .x1 = 0x800064ac ∧
      Regs s u ∧ u.getReg .x10 = s.getReg .x2 - 1080 ∧ u.getReg .x11 = s.getReg .x2 - 1104 ∧
      u.getReg .x12 = 3 ∧ u.getReg .x13 = vecPtr s (s.getReg .x11 + 24) ∧
      u.getReg .x14 = vecLen s (s.getReg .x11 + 24) ∧
      u.getReg .x24 = vecPtr s (s.getReg .x11 + 24) ∧
      u.getReg .x9 = vecLen s (s.getReg .x11 + 24) ∧
      u.getMem (s.getReg .x2 - 1104) = 0 ∧ u.getMem (s.getReg .x2 - 1096) = logMem s ∧
      u.getMem (s.getReg .x2 - 1088) = logBc s ∧ u.getMem (s.getReg .x2 - 1136) = logMem s ∧
      u.getMem (s.getReg .x2 - 1152) = logBc s ∧ heapNext u = heapNext s ∧
      ∀ T, TranscriptAt s (s.getReg .x12) T → TranscriptAt u (s.getReg .x12) T := by
  obtain ⟨hb1, hb2, hb3, hlo⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hs := hpre.layout.stack
  have hbd := hpre.layout.bound
  rw [stackLo_eq] at hs
  have hR : Region (s.getReg .x11) 168 := by
    rcases hpre.layout.region with h0 | h0
    · exact absurd h0 (by decide)
    · exact h0
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006428_spec hpc (by
    rv_eval []
    and_intros <;> first
      | valid_access hval [hb1]
      | exact Region.valid hR (by addr_omega [hR]) (by addr_omega [hR]) (by addr_omega [hR])
      | addr_omega [hs, hbd, hb1])
  have hm₁ := DFrame.of_memFrame (b80006428_frame h₁ (by omega))
  have hsp₁ := b80006428_x2 h₁
  have hn₁ : heapNext u₁ = heapNext s := by
    simp only [heapNext]
    have hx := hpre.stack.next
    rw [stackLo_eq] at hx
    exact congrArg BitVec.toNat (hm₁ nextAddr fun i hi hw ↦ by addr_omega [hx, hw, hi, hb1])
  have e24 : s.getReg .x11 + 24 + 8 = s.getReg .x11 + 32 := by rw [BitVec.add_assoc]; rfl
  have e40 : s.getReg .x11 + 24 + 16 = s.getReg .x11 + 40 := by rw [BitVec.add_assoc]; rfl
  refine ⟨u₁, hr₁, {
    sp := hsp₁
    heap := ⟨hn₁ ▸ hpre.heap.lo, hn₁ ▸ hpre.heap.hi⟩
    mono := hn₁.ge
    frame := hm₁.mono fun a ha ↦ Or.inr (Or.inr (Or.inl (by
      rw [stackLo_eq]; addr_omega [ha, hb1])))
    saved := fun i hi ↦ by
      interval_cases i
      exacts [b80006428_m_x2_n8 h₁, b80006428_m_x2_n16 h₁, b80006428_m_x2_n24 h₁,
        b80006428_m_x2_n32 h₁, b80006428_m_x2_n40 h₁, b80006428_m_x2_n48 h₁,
        b80006428_m_x2_n56 h₁, b80006428_m_x2_n64 h₁, b80006428_m_x2_n72 h₁,
        b80006428_m_x2_n80 h₁, b80006428_m_x2_n88 h₁, b80006428_m_x2_n96 h₁,
        b80006428_m_x2_n104 h₁] }, b80006428_pc h₁, b80006428_x1 h₁,
    ⟨b80006428_x18 h₁, b80006428_x19 h₁, b80006428_x20 h₁⟩, b80006428_x10 h₁,
    b80006428_x11 h₁,
    b80006428_x12 h₁, ?_, ?_, ?_, ?_, b80006428_m_x2_n1104 h₁, b80006428_m_x2_n1096 h₁,
    b80006428_m_x2_n1088 h₁, b80006428_m_x2_n1136 h₁, b80006428_m_x2_n1152 h₁, hn₁,
    fun T hT ↦ ?_⟩
  · rw [b80006428_x13 h₁, vecPtr, e24]
  · rw [b80006428_x14 h₁, vecLen, e40]
  · rw [b80006428_x24 h₁, vecPtr, e24]
  · rw [b80006428_x9 h₁, vecLen, e40]
  · have ss := hpre.selfStack
    have ps := hpre.proofStack
    have hS := hpre.self.self
    have hP := hpre.self.proof
    rw [stackLo_eq] at ss ps
    simp only [ProofApart] at ps
    have hw (lo : Word) (n : Nat) (h1 : Apart lo n (s.getReg .x2 - 4544) 4544) (hn : lo.toNat + n ≤ 2 ^ 64) :
        Misses (fun a ↦ Within a (stackLo s busBalanceStack) busBalanceStack) lo n :=
      fun y hy hw ↦ by rw [stackLo_eq] at hw; addr_omega [hy, hw, h1, hn]
    refine (hm₁.mono fun a ha ↦ ?_).transcriptAt hT hpre.self (hw _ _ (by addr_omega [ss, hS])
      (by addr_omega [hS])) (hw _ _ ps.1 (by addr_omega [hP])) ?_
      (hw _ _ (by addr_omega [ss, hS]) (by addr_omega [hS]))
    · rw [stackLo_eq]; addr_omega [ha, hb1]
    · rcases hpre.self.stream with h0 | h0
      · intro y hy; rw [h0] at hy; addr_omega [hy]
      · exact hw _ _ ps.2 (by addr_omega [h0])

/-- A step that leaves the transcript alone keeps what it stands for. -/
theorem Step.transcript {s v w : MachineState} (hpre : BusBalancePre s) (h : Inv s v) {lo : Word}
    {n : Nat} (hl : InFrame s lo n) (st : Step s v w lo n) {T : TState}
    (hT : TranscriptAt v (s.getReg .x12) T) : TranscriptAt w (s.getReg .x12) T :=
  h.transcript hpre st.heap (st.frame.mono fun _ ha ↦ Below.loc hpre hl ha) hT

/-! ## The three layouts -/

/-- The `BusLayout` at `a` holds `l`, its two buffers allocated since the entry. -/
structure LayoutAt (s v : MachineState) (a : Word) (l : BusLayoutRust) : Prop where
  value : busLayoutOf v a = l
  framework : VecOk v a 16 8
  frameworkNew : NewBuf s v (vecPtr v a) (16 * (vecCap v a).toNat) 8
  tables : VecOk v (a + 24) 16 8
  tablesNew : NewBuf s v (vecPtr v (a + 24)) (16 * (vecCap v (a + 24)).toNat) 8

theorem busLayoutRust_congr (f : List ℕ) {b b' : List BusBlock}
    (h : b.map (·.logRows) = b'.map (·.logRows)) : busLayoutRust f b = busLayoutRust f b' := by
  unfold busLayoutRust
  rw [h]

theorem blocksFrom_logRows (s : MachineState) (p : Word) (n : Nat) :
    (blocksFrom s p n).map (·.logRows) =
      (List.range n).map fun i ↦ (s.getMem (p + BitVec.ofNat 64 (48 * i) + 24)).toNat := by
  simp only [blocksFrom, List.map_map]
  rfl

/-- A word in a buffer allocated since the entry, or in the frame, apart from what a step writes,
keeps its value. -/
theorem Step.bufWord {s v w : MachineState} (hpre : BusBalancePre s) {lo : Word} {n : Nat}
    (st : Step s v w lo n) (hl : InFrame s lo n) {p x : Word} {m : Nat}
    (hb : NewBuf s v p m 8) (h1 : p.toNat ≤ x.toNat) (h2 : x.toNat + 8 ≤ p.toNat + m) :
    w.getMem x = v.getMem x := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hlo := hpre.heap.lo
  have hhi := st.heap.hi
  have hm := st.mono
  simp only [NewBuf, InFrame] at hb hl
  rcases hb.2 with h0 | ⟨b1, b2⟩
  · omega
  refine st.word hpre ?_ (Or.inr ⟨by simp only [heapStart] at hlo ⊢; omega, by omega⟩)
  simp only [heapNext, heapEnd] at b1 b2 hhi hm
  addr_omega [b1, b2, h1, h2, hl, hb1, hhi, hm]

theorem _root_.Rv64Verifier.Runtime.VecOk.keep {v w : MachineState} {a : Word} {size align : Nat}
    (h : VecOk v a size align)
    (h0 : w.getMem a = v.getMem a) (h8 : w.getMem (a + 8) = v.getMem (a + 8))
    (h16 : w.getMem (a + 16) = v.getMem (a + 16)) (hm : heapNext v ≤ heapNext w) :
    VecOk w a size align := by
  obtain ⟨⟨r1, r2⟩, hl⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp only [vecCap, vecPtr, vecLen, h0, h8, h16] at r1 r2 hl ⊢
  · exact r1
  · rcases r2 with r | ⟨r3, r4⟩
    · exact Or.inl r
    · exact Or.inr ⟨r3, by omega⟩
  · exact hl

theorem placementsAt_keep {s v w : MachineState} (hpre : BusBalancePre s) {lo : Word} {n : Nat}
    (st : Step s v w lo n) (hl : InFrame s lo n) {a : Word} (hv : VecOk v a 16 8)
    (hb : NewBuf s v (vecPtr v a) (16 * (vecCap v a).toNat) 8)
    (h8 : w.getMem (a + 8) = v.getMem (a + 8)) (h16 : w.getMem (a + 16) = v.getMem (a + 16)) :
    placementsAt w a = placementsAt v a := by
  have hlen := hv.len
  simp only [placementsAt, vecPtr, vecLen] at hb hlen ⊢
  rw [h8, h16]
  refine List.map_congr_left fun i hi ↦ ?_
  simp only [List.mem_range] at hi
  have hc : 16 * i + 16 ≤ 16 * (vecCap v a).toNat := by omega
  have hbd : (v.getMem (a + 8)).toNat + 16 * (vecCap v a).toNat ≤ 2 ^ 64 := by
    rcases hb.2 with h0 | ⟨b1, b2⟩
    · omega
    · have := st.heap.hi; have := st.mono
      simp only [heapNext, heapEnd] at *; omega
  rw [st.bufWord hpre hl hb (by addr_omega [hbd, hc]) (by addr_omega [hbd, hc]),
    st.bufWord hpre hl hb (by addr_omega [hbd, hc]) (by addr_omega [hbd, hc])]

theorem LayoutAt.keep {s v w : MachineState} (hpre : BusBalancePre s) {lo : Word} {n : Nat}
    (st : Step s v w lo n) (hl : InFrame s lo n) {a : Word} {l : BusLayoutRust}
    (h : LayoutAt s v a l) (hin : InFrame s a 56) (hap : Apart a 56 lo n) : LayoutAt s w a l := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  simp only [InFrame] at hin
  have hw (j : Nat) (hj : j + 8 ≤ 56) : w.getMem (a + BitVec.ofNat 64 j) =
      v.getMem (a + BitVec.ofNat 64 j) :=
    st.word hpre (by addr_omega [hap, hin, hj, hb1]) (Or.inl (by addr_omega [hin, hj, hb1]))
  have e0 : w.getMem a = v.getMem a := by simpa using hw 0 (by omega)
  have e8 : w.getMem (a + 8) = v.getMem (a + 8) := hw 8 (by omega)
  have e16 : w.getMem (a + 16) = v.getMem (a + 16) := hw 16 (by omega)
  have e24 : w.getMem (a + 24) = v.getMem (a + 24) := hw 24 (by omega)
  have e32 : w.getMem (a + 24 + 8) = v.getMem (a + 24 + 8) := by
    rw [BitVec.add_assoc]; exact hw 32 (by omega)
  have e40 : w.getMem (a + 24 + 16) = v.getMem (a + 24 + 16) := by
    rw [BitVec.add_assoc]; exact hw 40 (by omega)
  have e48 : w.getMem (a + 48) = v.getMem (a + 48) := hw 48 (by omega)
  have hm := st.mono
  refine ⟨?_, h.framework.keep e0 e8 e16 hm, ?_, h.tables.keep e24 e32 e40 hm, ?_⟩
  · rw [← h.value]
    simp only [busLayoutOf, e48]
    rw [placementsAt_keep hpre st hl h.framework h.frameworkNew e8 e16,
      placementsAt_keep hpre st hl h.tables h.tablesNew e32 e40]
  · have := h.frameworkNew
    simp only [NewBuf, vecPtr, vecCap] at this ⊢
    rw [e8, e0]
    exact ⟨this.1, this.2.imp_right fun h' ↦ ⟨h'.1, by omega⟩⟩
  · have := h.tablesNew
    simp only [NewBuf, vecPtr, vecCap] at this ⊢
    rw [e32, e24]
    exact ⟨this.1, this.2.imp_right fun h' ↦ ⟨h'.1, by omega⟩⟩

/-- The logs of the rows of the `Vec<BusBlock>` at `c`, read only, are the entry's. -/
theorem blocks_logRows {s u : MachineState} (h : Inv s u) {c : Word}
    (hb : BlocksRO s busBalanceStack [(s.getReg .x10, 120)] (s.getReg .x12) c) :
    (blocksFrom u (vecPtr s c) (vecLen s c).toNat).map (·.logRows) =
      (blocksAt s c).map (·.logRows) := by
  rw [blocksAt_eq, blocksFrom_logRows, blocksFrom_logRows]
  have hbd := hb.blocks.bound
  refine List.map_congr_left fun i hi ↦ ?_
  simp only [List.mem_range] at hi
  rw [h.word hb.blocks (by addr_omega [hbd, hi]) (by addr_omega [hbd, hi])]

/-- A call of `bus_layout` on the blocks of the `Vec<BusBlock>` at `c`, into `S - k`. -/
theorem layoutStep (hBL : BusLayoutSpec) {s u₀ u : MachineState} (hpre : BusBalancePre s)
    (h : Inv s u) (hr : Reaches Image.code u₀ u) (hpc : u.pc = 0x80010acc) {k : Nat}
    (hout : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 k) (hk1 : 160 ≤ k) (hk2 : k ≤ 1344)
    (hk8 : k % 8 = 0) {f : List ℕ}
    (hrows : LayoutRead u (u.getReg .x10) (u.getReg .x11) (8 * (u.getReg .x12).toNat))
    (hf : natsAt u (u.getReg .x11) (u.getReg .x12).toNat = f) {c : Word}
    (hb : BlocksRO s busBalanceStack [(s.getReg .x10, 120)] (s.getReg .x12) c)
    (h13 : u.getReg .x13 = vecPtr s c) (h14 : u.getReg .x14 = vecLen s c) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧
      Step s u v (s.getReg .x2 - BitVec.ofNat 64 k) 56 ∧ Inv s v ∧
      LayoutAt s v (s.getReg .x2 - BitVec.ofNat 64 k) (busLayoutRust f (blocksAt s c))) ∨
      Dead Image.code v) := by
  obtain ⟨v, hrv, ⟨hpcv, hp, post, st⟩ | hd⟩ :=
    layoutCall hBL hpre h hr hpc hout hk1 hk2 hk8 hrows (by rw [h13, h14]; exact hb.blocks)
  · have hm := h.mono
    have nb {p : Word} {n : Nat} (hn : NewBuf u v p n 8) : NewBuf s v p n 8 :=
      ⟨hn.1, hn.2.imp_right fun h' ↦ ⟨by omega, h'.2⟩⟩
    have hv := post.value
    have hfw := post.framework
    have htb := post.tables
    rw [hout] at hv hfw htb
    refine ⟨v, hrv, Or.inl ⟨hpcv, hp, st, h.after hpre (inFrame hpre (by omega) hk2) st,
      ⟨?_, hfw.1, nb hfw.2, htb.1, nb htb.2⟩⟩⟩
    rw [hv, hf, h13, h14]
    exact busLayoutRust_congr f (blocks_logRows h hb)
  · exact ⟨v, hrv, Or.inr hd⟩

/-- A block past the prologue that writes `n` bytes at `lo`, in the frame. -/
theorem Step.ofMemFrame {s u w : MachineState} (hpre : BusBalancePre s) (h : Inv s u) {lo : Word}
    {n : Nat} (hl : InFrame s lo n) (hf : MemFrame u w lo n) (hsp : w.getReg .x2 = u.getReg .x2) :
    Step s u w lo n := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  simp only [InFrame] at hl
  have hd := DFrame.of_memFrame hf
  have hn : heapNext w = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (hd nextAddr fun i hi hw ↦ by addr_omega [hw, hi, hl, hb1])
  exact ⟨hd.mono fun a ha ↦ Or.inl ha, ⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩, hn.ge, hsp⟩

theorem rowsRead {s u : MachineState} (hpre : BusBalancePre s) (h : Inv s u) {k : Nat}
    (hk1 : 1104 + 56 ≤ k + 1104 + 56) (hk : k = 1080 ∨ k = 1024) :
    LayoutRead u (s.getReg .x2 - BitVec.ofNat 64 k) (s.getReg .x2 - 1104) (8 * 3) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨o1, o2, o3⟩ := frameSlot (m := busLayoutStack) hpre h (k := 1104) (n := 24) (by omega)
    (by omega) (by omega) (by decide)
  exact ⟨Or.inr o1, o2, o3, by rcases hk with rfl | rfl <;> addr_omega [hb1]⟩

/-- What the three layouts leave at `0x800064f4`. -/
structure AfterLayouts (s v : MachineState) : Prop where
  inv : Inv s v
  regs : Regs s v
  x24 : v.getReg .x24 = vecPtr s (s.getReg .x11 + 24)
  x9 : v.getReg .x9 = vecLen s (s.getReg .x11 + 24)
  x8 : v.getReg .x8 = vecLen s (s.getReg .x11 + 72)
  lm : v.getMem (s.getReg .x2 - 1136) = logMem s
  lb : v.getMem (s.getReg .x2 - 1152) = logBc s
  pullPtr : v.getMem (s.getReg .x2 - 1168) = vecPtr s (s.getReg .x11 + 48)
  pullLen : v.getMem (s.getReg .x2 - 1176) = vecLen s (s.getReg .x11 + 48)
  countPtr : v.getMem (s.getReg .x2 - 1160) = vecPtr s (s.getReg .x11 + 72)
  push : LayoutAt s v (s.getReg .x2 - 1080)
    (busLayoutRust [0, (logMem s).toNat, (logBc s).toNat] (busLayoutAt s (s.getReg .x11)).push)
  pull : LayoutAt s v (s.getReg .x2 - 1024)
    (busLayoutRust [0, (logMem s).toNat, (logBc s).toNat] (busLayoutAt s (s.getReg .x11)).pull)
  count : LayoutAt s v (s.getReg .x2 - 968) (busLayoutRust [] (busLayoutAt s (s.getReg .x11)).count)
  transcript : ∀ T, TranscriptAt s (s.getReg .x12) T → TranscriptAt v (s.getReg .x12) T

theorem natsAt_frl {s u : MachineState} (hpre : BusBalancePre s)
    (h0 : u.getMem (s.getReg .x2 - 1104) = 0) (h1 : u.getMem (s.getReg .x2 - 1096) = logMem s)
    (h2 : u.getMem (s.getReg .x2 - 1088) = logBc s) :
    natsAt u (s.getReg .x2 - 1104) (3 : Word).toNat = [0, (logMem s).toNat, (logBc s).toNat] := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have e1 : s.getReg .x2 - 1104 + BitVec.ofNat 64 (8 * 1) = s.getReg .x2 - 1096 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e2 : s.getReg .x2 - 1104 + BitVec.ofNat 64 (8 * 2) = s.getReg .x2 - 1088 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e0 : s.getReg .x2 - 1104 + BitVec.ofNat 64 (8 * 0) = s.getReg .x2 - 1104 := by simp
  rw [natsAt, readWords_eq_map, show (3 : Word).toNat = 3 from rfl]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append]
  rw [e0, e1, e2, h0, h1, h2]
  rfl

/-- The prologue and the three calls of `bus_layout`, to `0x800064f4`. -/
theorem layouts (hBL : BusLayoutSpec) {s : MachineState} (hpc : s.pc = 0x80006428)
    (hpre : BusBalancePre s) :
    ∃ v, Reaches Image.code s v ∧
      ((v.pc = 0x800064f4 ∧ AfterLayouts s v) ∨ Dead Image.code v) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hR : Region (s.getReg .x11) 168 := by
    rcases hpre.layout.region with h0 | h0
    · exact absurd h0 (by decide)
    · exact h0
  obtain ⟨u₁, hr₁, I₁, hpc₁, hx1, R₁, h10, h11, h12, h13, h14, h24, h9, m0, m1, m2, m3,
    m4, hn₁, tr₁⟩ :=
    prologue hpc hpre
  -- push
  obtain ⟨v₁, hrv₁, ⟨hpcv₁, hp₁, st₁, J₁, L₁⟩ | hd⟩ :=
    layoutStep hBL hpre I₁ hr₁ hpc₁ (k := 1080)
      (f := [0, (logMem s).toNat, (logBc s).toNat]) h10 (by omega) (by omega) (by omega)
      (by rw [h10, h11, h12]; exact rowsRead hpre I₁ (by omega) (Or.inl rfl))
      (by rw [h11, h12]; exact natsAt_frl hpre m0 m1 m2) hpre.push h13 h14
  swap
  · exact ⟨v₁, hrv₁, Or.inr hd⟩
  have if₁ := inFrame hpre (k := 1080) (n := 56) (by omega) (by omega)
  have sp₁ : v₁.getReg .x2 = s.getReg .x2 - 1344 := J₁.sp
  have ry (r : Reg) (hr : r ∈ calleeSaved) : v₁.getReg r = u₁.getReg r := hp₁ r hr
  have hpc₁' : v₁.pc = 0x800064ac := by rw [hpcv₁, returnAddress_eq, hx1]; decide
  have x19₁ : v₁.getReg .x19 = s.getReg .x11 := (ry .x19 (by decide)).trans R₁.x19
  have lw (j : Nat) (hj : j + 8 ≤ 168) {u : MachineState} (hu : Inv s u) :
      u.getMem (s.getReg .x11 + BitVec.ofNat 64 j) = s.getMem (s.getReg .x11 + BitVec.ofNat 64 j) :=
    hu.word hpre.layout (by addr_omega [hR, hj]) (by addr_omega [hR, hj])
  -- the pull arguments
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800064ac_spec hpc₁' (by
    rv_eval [sp₁, x19₁]
    and_intros <;> first
      | valid_access hval [hb1]
      | exact Region.valid hR (by addr_omega [hR]) (by addr_omega [hR]) (by addr_omega [hR]))
  have k₂ := b800064ac_keeps h₂
  have fr₂ := b800064ac_frame h₂ (by rw [sp₁]; addr_omega [hb1])
  have e168 : v₁.getReg .x2 + 168 = s.getReg .x2 - 1176 := by
    rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  rw [e168] at fr₂
  have st₂ := Step.ofMemFrame hpre J₁ (inFrame hpre (k := 1176) (n := 16) (by omega) (by omega))
    fr₂ (k₂ .x2 (by decide))
  have J₂ := J₁.after hpre (inFrame hpre (k := 1176) (n := 16) (by omega) (by omega)) st₂
  have kw₂ {x : Word} (hx1 : Apart x 8 (s.getReg .x2 - BitVec.ofNat 64 1080) 56)
      (hx2 : Apart x 8 (s.getReg .x2 - BitVec.ofNat 64 1176) 16)
      (hy : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧ x.toNat + 8 ≤ (s.getReg .x2).toNat) :
      u₂.getMem x = u₁.getMem x :=
    (st₂.word hpre hx2 (Or.inl hy)).trans (st₁.word hpre hx1 (Or.inl hy))
  have e48 : s.getReg .x11 + 48 + 8 = s.getReg .x11 + BitVec.ofNat 64 56 := by
    rw [BitVec.add_assoc]; rfl
  have e64 : s.getReg .x11 + 48 + 16 = s.getReg .x11 + BitVec.ofNat 64 64 := by
    rw [BitVec.add_assoc]; rfl
  obtain ⟨v₂, hrv₂, ⟨hpcv₂, hp₂, st₂', J₂', L₂⟩ | hd⟩ :=
    layoutStep hBL hpre J₂ (hrv₁.trans hr₂) (b800064ac_pc h₂) (k := 1024)
      (f := [0, (logMem s).toNat, (logBc s).toNat])
      (by rw [b800064ac_x10 h₂, sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
      (by omega) (by omega) (by omega)
      (by rw [b800064ac_x10 h₂, b800064ac_x11 h₂, b800064ac_x12 h₂, sp₁]
          have := rowsRead hpre J₂ (k := 1024) (by omega) (Or.inr rfl)
          rw [show s.getReg .x2 - 1344 + 320 = s.getReg .x2 - BitVec.ofNat 64 1024 by
              apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
            show s.getReg .x2 - 1344 + 240 = s.getReg .x2 - 1104 by
              apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
          exact this)
      (by rw [b800064ac_x11 h₂, b800064ac_x12 h₂, sp₁,
            show s.getReg .x2 - 1344 + 240 = s.getReg .x2 - 1104 by
              apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
          exact natsAt_frl hpre
            ((kw₂ (by addr_omega [hb1]) (by addr_omega [hb1]) (by addr_omega [hb1])).trans m0)
            ((kw₂ (by addr_omega [hb1]) (by addr_omega [hb1]) (by addr_omega [hb1])).trans m1)
            ((kw₂ (by addr_omega [hb1]) (by addr_omega [hb1]) (by addr_omega [hb1])).trans m2))
      hpre.pull
      (by rw [b800064ac_x13 h₂, x19₁, vecPtr, e48]; exact lw 56 (by omega) J₁)
      (by rw [b800064ac_x14 h₂, x19₁, vecLen, e64]; exact lw 64 (by omega) J₁)
  swap
  · exact ⟨v₂, hrv₂, Or.inr hd⟩
  have sp₂ : v₂.getReg .x2 = s.getReg .x2 - 1344 := J₂'.sp
  have ry₂ (r : Reg) (hr : r ∈ calleeSaved) : v₂.getReg r = u₂.getReg r := hp₂ r hr
  have hpc₂' : v₂.pc = 0x800064d0 := by
    rw [hpcv₂, returnAddress_eq, b800064ac_x1 h₂]; decide
  have x19₂ : v₂.getReg .x19 = s.getReg .x11 :=
    (ry₂ .x19 (by decide)).trans ((k₂ .x19 (by decide)).trans x19₁)
  -- the count arguments
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800064d0_spec hpc₂' (by
    rv_eval [sp₂, x19₂]
    and_intros <;> first
      | valid_access hval [hb1]
      | exact Region.valid hR (by addr_omega [hR]) (by addr_omega [hR]) (by addr_omega [hR]))
  have k₃ := b800064d0_keeps h₃
  have fr₃ := b800064d0_frame h₃ (by rw [sp₂]; addr_omega [hb1])
  have e184 : v₂.getReg .x2 + 184 = s.getReg .x2 - 1160 := by
    rw [sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  rw [e184] at fr₃
  have st₃ := Step.ofMemFrame hpre J₂' (inFrame hpre (k := 1160) (n := 8) (by omega) (by omega))
    fr₃ (k₃ .x2 (by decide))
  have J₃ := J₂'.after hpre (inFrame hpre (k := 1160) (n := 8) (by omega) (by omega)) st₃
  have e80 : s.getReg .x11 + 72 + 8 = s.getReg .x11 + BitVec.ofNat 64 80 := by
    rw [BitVec.add_assoc]; rfl
  have e88 : s.getReg .x11 + 72 + 16 = s.getReg .x11 + BitVec.ofNat 64 88 := by
    rw [BitVec.add_assoc]; rfl
  have x10₃ : u₃.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 968 := by
    rw [b800064d0_x10 h₃, sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hlo := J₃.heap.lo
  obtain ⟨v₃, hrv₃, ⟨hpcv₃, hp₃, st₃', J₃', L₃⟩ | hd⟩ :=
    layoutStep hBL hpre J₃ (hrv₂.trans hr₃) (b800064d0_pc h₃) (k := 968) (f := []) x10₃
      (by omega) (by omega) (by omega)
      (by
        rw [b800064d0_x11 h₃, b800064d0_x12 h₃]
        simp only [heapStart] at hlo
        exact ⟨Or.inl rfl,
          ⟨Or.inl (by simp only [heapNext] at hlo ⊢; simp; omega), Or.inl rfl⟩,
          Or.inl rfl, Or.inl rfl⟩)
      (by rw [b800064d0_x12 h₃]; rfl)
      hpre.count
      (by rw [b800064d0_x13 h₃, x19₂, vecPtr, e80]; exact lw 80 (by omega) J₂')
      (by rw [b800064d0_x14 h₃, x19₂, vecLen, e88]; exact lw 88 (by omega) J₂')
  swap
  · exact ⟨v₃, hrv₃, Or.inr hd⟩
  have if₂ := inFrame hpre (k := 1176) (n := 16) (by omega) (by omega)
  have if₂' := inFrame hpre (k := 1024) (n := 56) (by omega) (by omega)
  have if₃ := inFrame hpre (k := 1160) (n := 8) (by omega) (by omega)
  have if₃' := inFrame hpre (k := 968) (n := 56) (by omega) (by omega)
  have W {u v : MachineState} {lo : Word} {n : Nat} (st : Step s u v lo n) {x : Word}
      (hx : Apart x 8 lo n)
      (hy : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧ x.toNat + 8 ≤ (s.getReg .x2).toNat) :
      v.getMem x = u.getMem x := st.word hpre hx (Or.inl hy)
  have ra : returnAddress u₃ = 0x800064f4 := by rw [returnAddress_eq, b800064d0_x1 h₃]; decide
  have rg (r : Reg) (hr : r ∈ calleeSaved) (h2 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9,
      .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29,
      .x30, .x31] : List Reg)) (h3 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x9, .x15, .x16, .x17,
      .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] :
      List Reg)) : v₃.getReg r = u₁.getReg r := by
    rw [hp₃ r hr, k₃ r h3, hp₂ r hr, k₂ r h2, hp₁ r hr]
  have sl {x : Word} (h1 : Apart x 8 (s.getReg .x2 - BitVec.ofNat 64 1080) 56)
      (h2 : Apart x 8 (s.getReg .x2 - 1176) 16)
      (h3 : Apart x 8 (s.getReg .x2 - BitVec.ofNat 64 1024) 56)
      (h4 : Apart x 8 (s.getReg .x2 - 1160) 8)
      (h5 : Apart x 8 (s.getReg .x2 - BitVec.ofNat 64 968) 56)
      (hy : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧ x.toNat + 8 ≤ (s.getReg .x2).toNat) :
      v₃.getMem x = u₁.getMem x := by
    rw [W st₃' h5 hy, W st₃ h4 hy, W st₂' h3 hy, W st₂ h2 hy, W st₁ h1 hy]
  have m176 := b800064ac_m_x2_176 h₂
  have m168 := b800064ac_m_x2_168 h₂
  have m184 := b800064d0_m_x2_184 h₃
  rw [sp₁, x19₁, show s.getReg .x2 - 1344 + 176 = s.getReg .x2 - 1168 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at m176
  rw [sp₁, x19₁, show s.getReg .x2 - 1344 + 168 = s.getReg .x2 - 1176 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at m168
  rw [sp₂, x19₂, show s.getReg .x2 - 1344 + 184 = s.getReg .x2 - 1160 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at m184
  refine ⟨v₃, hrv₃, Or.inl ⟨by rw [hpcv₃, ra], {
    inv := J₃'
    regs := ⟨(rg .x18 (by decide) (by decide) (by decide)).trans R₁.x18,
      (rg .x19 (by decide) (by decide) (by decide)).trans R₁.x19,
      (rg .x20 (by decide) (by decide) (by decide)).trans R₁.x20⟩
    x24 := (rg .x24 (by decide) (by decide) (by decide)).trans h24
    x9 := (rg .x9 (by decide) (by decide) (by decide)).trans h9
    x8 := by
      rw [hp₃ .x8 (by decide), b800064d0_x8 h₃, x19₂, vecLen, e88]
      exact lw 88 (by omega) J₂'
    lm := (sl (by addr_omega [hb1]) (by addr_omega [hb1]) (by addr_omega [hb1])
      (by addr_omega [hb1]) (by addr_omega [hb1]) (by addr_omega [hb1])).trans m3
    lb := (sl (by addr_omega [hb1]) (by addr_omega [hb1]) (by addr_omega [hb1])
      (by addr_omega [hb1]) (by addr_omega [hb1]) (by addr_omega [hb1])).trans m4
    pullPtr := by
      rw [W st₃' (by addr_omega [hb1]) (by addr_omega [hb1]),
        W st₃ (by addr_omega [hb1]) (by addr_omega [hb1]),
        W st₂' (by addr_omega [hb1]) (by addr_omega [hb1]), m176, vecPtr, e48]
      exact lw 56 (by omega) J₁
    pullLen := by
      rw [W st₃' (by addr_omega [hb1]) (by addr_omega [hb1]),
        W st₃ (by addr_omega [hb1]) (by addr_omega [hb1]),
        W st₂' (by addr_omega [hb1]) (by addr_omega [hb1]), m168, vecLen, e64]
      exact lw 64 (by omega) J₁
    countPtr := by
      rw [W st₃' (by addr_omega [hb1]) (by addr_omega [hb1]), m184, vecPtr, e80]
      exact lw 80 (by omega) J₂'
    push := ((((L₁.keep hpre st₂ if₂ if₁ (by addr_omega [hb1])).keep hpre st₂' if₂'
      if₁ (by addr_omega [hb1])).keep hpre st₃ if₃ if₁ (by addr_omega [hb1])).keep hpre
      st₃' if₃' if₁ (by addr_omega [hb1]))
    pull := ((L₂.keep hpre st₃ if₃ if₂' (by addr_omega [hb1])).keep hpre st₃' if₃'
      if₂' (by addr_omega [hb1]))
    count := L₃
    transcript := fun T hT ↦ st₃'.transcript hpre J₃ if₃' (st₃.transcript hpre J₂' if₃
      (st₂'.transcript hpre J₂ if₂' (st₂.transcript hpre J₁ if₂
        (st₁.transcript hpre I₁ if₁ (tr₁ T hT))))) }⟩⟩
end Rv64Verifier.Proofs.Bus.VerifyBusBalance
