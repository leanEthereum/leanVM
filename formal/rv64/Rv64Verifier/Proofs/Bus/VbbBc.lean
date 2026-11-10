import Rv64Verifier.Proofs.Bus.VbbTail20
import Rv64Verifier.Proofs.Bytecode.Contracts
import Rv64Verifier.Proofs.Bytecode.Bits

/-!
# `Bytecode::evaluate` as `verify_bus_balance` reads it

`BcOk s n p`: the `Bytecode` at `p` is mapped (`BytecodeMem`), and each of its parts, and each
aligned doubleword holding one of their bytes, lies outside the free heap and `NEXT` and apart from
`busBalanceStack` bytes from `stackLo s n` (`verify_bus_balance`'s stack, or a callee's stack and
the caller's frame above it). The doublewords are what a frame of doublewords keeps: a buffer of
`u16`s may end inside one. `bevOf` reads the `Bytecode` as `evaluateRust`. `bcTransfer` carries
both across `verify_bus_balance`'s steps, `bytecodeEval` is `Vbb.BytecodeEvalSpec` from
`Bytecode::evaluate`'s contract.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Bus
  Rv64Verifier.Transcript

/-- The `Bytecode` at `p`, read only by a callee with an `n`-byte stack. -/
def BcOk (s : MachineState) (n : Nat) (p : Word) : Prop :=
  Proofs.Bytecode.BytecodeMem s p ∧ ∀ q ∈ bcParts s p,
    (Outside s q.1 q.2 ∧ Apart q.1 q.2 (stackLo s n) busBalanceStack) ∧
    ∀ a, Meets a q.1 q.2 → Outside s a 8 ∧ Apart a 8 (stackLo s n) busBalanceStack

/-- What `Bytecode::evaluate` computes. -/
def bevOf (s : MachineState) (p : Word) (pt : List E) : Option E :=
  evaluateRust (Proofs.Bytecode.readBytecode s p) pt

theorem bcParts_end {s : MachineState} {p : Word} (hm : Proofs.Bytecode.BytecodeMem s p) :
    ∀ q ∈ bcParts s p, q.2 = 0 ∨ q.1.toNat + q.2 ≤ 0xc0000000 := by
  have e {a : Word} {n : Nat} (h : Mapped a n) : a.toNat + n ≤ 0xc0000000 := by
    simp only [Mapped] at h; omega
  intro q hq
  simp only [bcParts, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (e hm.self)
  · rcases hm.blocks with h | h
    · exact Or.inl (by simp only [h, Nat.mul_zero])
    · exact Or.inr (e h)
  · rcases hm.words with h | h
    · exact Or.inl (by simp only [h, Nat.mul_zero])
    · exact Or.inr (e h)
  · rcases hm.positions with h | h
    · exact Or.inl (by simp only [h, Nat.mul_zero])
    · exact Or.inr (e h)
  · rcases hm.bytes with h | h
    · exact Or.inl (by simp only [h, Nat.mul_zero])
    · exact Or.inr (e h)

/-- A byte of the `n` bytes from `q`, its doubleword kept. -/
theorem byteAt_meets {s u : MachineState} {q : Word} {n : Nat}
    (hk : ∀ a, Meets a q n → u.getMem a = s.getMem a) {x : Word} (h1 : q.toNat ≤ x.toNat)
    (h2 : x.toNat < q.toNat + n) : byteAt u x = byteAt s x := by
  have ha := toNat_alignDown x
  rw [byteAt_eq, byteAt_eq, hk _ ⟨by rw [ha]; omega, by rw [ha]; omega, by rw [ha]; omega, by omega⟩]

/-- An aligned doubleword of the `n` bytes from `q`, kept. -/
theorem getMem_meets {s u : MachineState} {q : Word} {n : Nat}
    (hk : ∀ a, Meets a q n → u.getMem a = s.getMem a) (a : Word) (ha : a.toNat % 8 = 0)
    (h1 : q.toNat ≤ a.toNat) (h2 : a.toNat + 8 ≤ q.toNat + n) : u.getMem a = s.getMem a :=
  hk a ⟨ha, by omega, by omega, by omega⟩

/-- `u16`s of the `2 m` bytes from `q`, their doublewords kept. -/
theorem halvesAt_meets {s u : MachineState} {q : Word} {m : Nat} (hq : q.toNat % 2 = 0)
    (hend : 2 * m = 0 ∨ q.toNat + 2 * m ≤ 0xc0000000)
    (hk : ∀ a, Meets a q (2 * m) → u.getMem a = s.getMem a) :
    Proofs.Bytecode.halvesAt u q m = Proofs.Bytecode.halvesAt s q m := by
  unfold Proofs.Bytecode.halvesAt
  refine List.map_congr_left fun i hi ↦ ?_
  simp only [List.mem_range] at hi
  have hend := hend.resolve_left (by omega)
  exact Proofs.Bytecode.getHalfword_eq_of_bytes (by addr_omega [hq, hend, hi])
    (byteAt_meets hk (by addr_omega [hend, hi]) (by addr_omega [hend, hi]))
    (byteAt_meets hk (by addr_omega [hend, hi]) (by addr_omega [hend, hi]))

/-- The `Bytecode`, every doubleword holding a byte of it kept. -/
theorem readBytecode_congr {s u : MachineState} {p : Word}
    (hm : Proofs.Bytecode.BytecodeMem s p)
    (hk : ∀ q ∈ bcParts s p, ∀ a, Meets a q.1 q.2 → u.getMem a = s.getMem a) :
    Proofs.Bytecode.readBytecode u p = Proofs.Bytecode.readBytecode s p ∧
      bcParts u p = bcParts s p ∧
      (vecPtr u p = vecPtr s p ∧ vecLen u p = vecLen s p) ∧
      (vecPtr u (p + 24) = vecPtr s (p + 24) ∧ vecLen u (p + 24) = vecLen s (p + 24)) ∧
      (vecPtr u (p + 48) = vecPtr s (p + 48) ∧ vecLen u (p + 48) = vecLen s (p + 48)) ∧
      (vecPtr u (p + 72) = vecPtr s (p + 72) ∧ vecLen u (p + 72) = vecLen s (p + 72)) := by
  have hend := bcParts_end hm
  have mem (i : Nat) (hi : i < 5) : (bcParts s p)[i]'(by simp [bcParts]; omega) ∈ bcParts s p :=
    List.getElem_mem _
  have e0 := hend _ (mem 0 (by omega))
  have e1 := hend _ (mem 1 (by omega))
  have e2 := hend _ (mem 2 (by omega))
  have e3 := hend _ (mem 3 (by omega))
  have e4 := hend _ (mem 4 (by omega))
  simp only [bcParts, List.getElem_cons_zero, List.getElem_cons_succ] at e0 e1 e2 e3 e4
  replace e0 := e0.resolve_left (by omega)
  have k0 := hk _ (mem 0 (by omega))
  have k1 := hk _ (mem 1 (by omega))
  have k2 := hk _ (mem 2 (by omega))
  have k3 := hk _ (mem 3 (by omega))
  have k4 := hk _ (mem 4 (by omega))
  simp only [bcParts, List.getElem_cons_zero, List.getElem_cons_succ] at k0 k1 k2 k3 k4
  have pa := hm.align
  have w (j : Nat) (hj : j % 8 = 0) (hj2 : j + 8 ≤ 136) :
      u.getMem (p + BitVec.ofNat 64 j) = s.getMem (p + BitVec.ofNat 64 j) :=
    getMem_meets k0 _ (by addr_omega [pa, e0, hj, hj2]) (by addr_omega [e0, hj2])
      (by addr_omega [e0, hj2])
  have w2 (b : Nat) (j : Nat) (hb : b + j + 8 ≤ 136) (hj : (b + j) % 8 = 0) :
      u.getMem (p + BitVec.ofNat 64 b + BitVec.ofNat 64 j) =
        s.getMem (p + BitVec.ofNat 64 b + BitVec.ofNat 64 j) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact w _ hj hb
  have p0 : vecPtr u p = vecPtr s p := w 8 rfl (by omega)
  have l0 : vecLen u p = vecLen s p := w 16 rfl (by omega)
  have p1 : vecPtr u (p + 24) = vecPtr s (p + 24) := w2 24 8 (by omega) rfl
  have l1 : vecLen u (p + 24) = vecLen s (p + 24) := w2 24 16 (by omega) rfl
  have p2 : vecPtr u (p + 48) = vecPtr s (p + 48) := w2 48 8 (by omega) rfl
  have l2 : vecLen u (p + 48) = vecLen s (p + 48) := w2 48 16 (by omega) rfl
  have p3 : vecPtr u (p + 72) = vecPtr s (p + 72) := w2 72 8 (by omega) rfl
  have l3 : vecLen u (p + 72) = vecLen s (p + 72) := w2 72 16 (by omega) rfl
  have n96 : u.getMem (p + 96) = s.getMem (p + 96) := w 96 rfl (by omega)
  have hiv : bytesAt u (p + 104) 32 = bytesAt s (p + 104) 32 := by
    unfold bytesAt
    refine List.map_congr_left fun i hi ↦ ?_
    simp only [List.mem_range] at hi
    exact byteAt_meets k0 (by addr_omega [e0, hi]) (by addr_omega [e0, hi])
  have ba := hm.blocksAlign
  have hbl : Proofs.Bytecode.blocksAt u (vecPtr s p) (vecLen s p).toNat =
      Proofs.Bytecode.blocksAt s (vecPtr s p) (vecLen s p).toNat := by
    unfold Proofs.Bytecode.blocksAt
    refine List.map_congr_left fun i hi ↦ ?_
    simp only [List.mem_range] at hi
    have e1 := e1.resolve_left (by omega)
    rw [getMem_meets k1 (vecPtr s p + BitVec.ofNat 64 (24 * i)) (by addr_omega [ba, e1, hi])
        (by addr_omega [e1, hi]) (by addr_omega [e1, hi]),
      getMem_meets k1 (vecPtr s p + BitVec.ofNat 64 (24 * i) + 8) (by addr_omega [ba, e1, hi])
        (by addr_omega [e1, hi]) (by addr_omega [e1, hi]),
      getMem_meets k1 (vecPtr s p + BitVec.ofNat 64 (24 * i) + 16) (by addr_omega [ba, e1, hi])
        (by addr_omega [e1, hi]) (by addr_omega [e1, hi])]
  have wa := hm.wordsAlign
  have hwd : Proofs.Bytecode.wordsAt u (vecPtr s (p + 24)) (vecLen s (p + 24)).toNat =
      Proofs.Bytecode.wordsAt s (vecPtr s (p + 24)) (vecLen s (p + 24)).toNat := by
    unfold Proofs.Bytecode.wordsAt
    refine List.map_congr_left fun i hi ↦ ?_
    simp only [List.mem_range] at hi
    have e2 := e2.resolve_left (by omega)
    rw [getMem_meets k2 (vecPtr s (p + 24) + BitVec.ofNat 64 (16 * i)) (by addr_omega [wa, e2, hi])
        (by addr_omega [e2, hi]) (by addr_omega [e2, hi]),
      getMem_meets k2 (vecPtr s (p + 24) + BitVec.ofNat 64 (16 * i) + 8)
        (by addr_omega [wa, e2, hi]) (by addr_omega [e2, hi]) (by addr_omega [e2, hi])]
  have hps := halvesAt_meets hm.positionsAlign e3 k3
  have hby := halvesAt_meets hm.bytesAlign e4 k4
  refine ⟨?_, ?_, ⟨p0, l0⟩, ⟨p1, l1⟩, ⟨p2, l2⟩, ⟨p3, l3⟩⟩
  · simp only [Proofs.Bytecode.readBytecode, p0, l0, p1, l1, p2, l2, p3, l3, n96, hiv, hbl, hwd,
      hps, hby]
  · simp only [bcParts, p0, l0, p1, l1, p2, l2, p3, l3]

/-- **`BcOk` and `bevOf` across `verify_bus_balance`'s steps.** -/
theorem bcTransfer : BcTransfer BcOk bevOf := by
  intro s u hpre hbc I
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hend := bcParts_end hbc.1
  have hhi := I.heap.hi
  have hmo := I.mono
  have hk : ∀ q ∈ bcParts s (bytecodeOf s (s.getReg .x11)), ∀ a, Meets a q.1 q.2 →
      u.getMem a = s.getMem a := by
    intro q hq a ha
    obtain ⟨⟨ho, hn⟩, hst⟩ := (hbc.2 q hq).2 a ha
    obtain ⟨hx, hy⟩ := hpre.bytecodeApart q hq a ha
    simp only [Meets] at ha
    have he := (hend q hq).resolve_left (by omega)
    rw [stackLo_eq] at hst
    refine I.frame a fun i hi hw ↦ ?_
    simp only [W, Fresh, stackLo_eq] at hw
    simp only [heapNext, heapEnd] at ho hhi hmo
    rcases hw with hw | hw | hw | hw | ⟨f1, f2⟩
    · addr_omega [hw, hx, hi, ha, he]
    · addr_omega [hw, hy, hi, ha, he]
    · addr_omega [hw, hst, hi, ha, he, hb1]
    · addr_omega [hw, hn, hi, ha, he]
    · simp only [heapNext] at f1 f2; addr_omega [f1, f2, ho, hhi, hmo, hi, ha, he]
  obtain ⟨hrd, hpa, ⟨p0, l0⟩, ⟨p1, l1⟩, ⟨p2, l2⟩, ⟨p3, l3⟩⟩ := readBytecode_congr hbc.1 hk
  have hsl : stackLo u Vbb.bytecodeEvalStack = stackLo s busBalanceStack := by
    simp only [stackLo, I.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hm := hbc.1
  have hmU : Proofs.Bytecode.BytecodeMem u (bytecodeOf s (s.getReg .x11)) := {
    self := hm.self
    align := hm.align
    blocks := p0 ▸ l0 ▸ hm.blocks
    blocksAlign := p0 ▸ hm.blocksAlign
    words := p1 ▸ l1 ▸ hm.words
    wordsAlign := p1 ▸ hm.wordsAlign
    positions := p2 ▸ l2 ▸ hm.positions
    positionsAlign := p2 ▸ hm.positionsAlign
    bytes := p3 ▸ l3 ▸ hm.bytes
    bytesAlign := p3 ▸ hm.bytesAlign }
  refine ⟨⟨hmU, fun q hq ↦ ?_⟩, ?_⟩
  · rw [hpa] at hq
    obtain ⟨⟨ho, ha⟩, hd⟩ := hbc.2 q hq
    rw [hsl]
    refine ⟨⟨⟨ho.1.imp_left fun h ↦ Nat.le_trans h hmo, ho.2⟩, ha⟩, fun a hma ↦ ?_⟩
    obtain ⟨⟨ho', hn'⟩, hst'⟩ := hd a hma
    exact ⟨⟨ho'.imp_left fun h ↦ Nat.le_trans h hmo, hn'⟩, hst'⟩
  · funext pt; unfold bevOf; rw [hrd]

/-- `Bytecode::evaluate`'s precondition from `Vbb.BytecodeEvalPre`. -/
theorem evalPre {s : MachineState} (h : Vbb.BytecodeEvalPre BcOk s) :
    Proofs.Bytecode.EvaluatePre s := by
  have hf := h.outFrame
  have clr : ∀ q ∈ bcParts s (s.getReg .x11),
      Proofs.Bytecode.Clear s q.1 q.2 Proofs.Bytecode.evalStack (s.getReg .x10) := by
    intro q hq
    obtain ⟨⟨ho, ha⟩, -⟩ := h.bytecode.2 q hq
    have hs : stackLo s Proofs.Bytecode.evalStack = stackLo s Vbb.bytecodeEvalStack := rfl
    have e1 : Proofs.Bytecode.evalStack = 3200 := rfl
    have e2 : busBalanceStack = 4544 := rfl
    refine ⟨ho, ?_, ?_⟩
    · rw [hs]
      simp only [Apart, e1] at ha ⊢
      rw [e2] at ha
      omega
    · simp only [Apart] at ha ⊢
      omega
  have clrDw : ∀ q ∈ bcParts s (s.getReg .x11),
      Proofs.Bytecode.ClearDw s q.1 q.2 Proofs.Bytecode.evalStack (s.getReg .x10) := by
    intro q hq a h8 h1 h2 h0
    obtain ⟨ho, ha⟩ := (h.bytecode.2 q hq).2 a (by unfold Meets; exact ⟨h8, h1, h2, h0⟩)
    have hs : stackLo s Proofs.Bytecode.evalStack = stackLo s Vbb.bytecodeEvalStack := rfl
    have e1 : Proofs.Bytecode.evalStack = 3200 := rfl
    have e2 : busBalanceStack = 4544 := rfl
    refine ⟨ho, ?_, ?_⟩
    · rw [hs]
      simp only [Apart, e1] at ha ⊢
      rw [e2] at ha
      omega
    · simp only [Apart] at ha ⊢
      omega
  have hv := h.point.valid
  rw [show 24 * (s.getReg .x13).toNat / 8 = 3 * (s.getReg .x13).toNat by omega] at hv
  exact {
    heap := h.heap
    out := regionRange h.out (Nat.le_refl _) (by omega) h.out.2
    outFree := h.outFree
    outStack := h.outStack
    bc := h.bytecode.1
    bcClear := ⟨clr (s.getReg .x11, 136) (by simp [bcParts]),
      clr (vecPtr s (s.getReg .x11), 24 * (vecLen s (s.getReg .x11)).toNat) (by simp [bcParts]),
      clr (vecPtr s (s.getReg .x11 + 24), 16 * (vecLen s (s.getReg .x11 + 24)).toNat)
        (by simp [bcParts]),
      clr (vecPtr s (s.getReg .x11 + 48), 2 * (vecLen s (s.getReg .x11 + 48)).toNat)
        (by simp [bcParts]),
      clr (vecPtr s (s.getReg .x11 + 72), 2 * (vecLen s (s.getReg .x11 + 72)).toNat)
        (by simp [bcParts]),
      clrDw (vecPtr s (s.getReg .x11 + 48), 2 * (vecLen s (s.getReg .x11 + 48)).toNat)
        (by simp [bcParts]),
      clrDw (vecPtr s (s.getReg .x11 + 72), 2 * (vecLen s (s.getReg .x11 + 72)).toNat)
        (by simp [bcParts])⟩
    point := hv
    pointRegion := h.pointRegion
    pointClear := ⟨h.point.free, h.point.stack, h.pointOut⟩
    stack := h.stack
    rodata := h.rodata }

/-- `Vbb.BytecodeEvalPost` from `Bytecode::evaluate`'s postcondition. -/
theorem evalPost {s t : MachineState} (c : Proofs.Bytecode.EvaluatePost s t) :
    Vbb.BytecodeEvalPost bevOf s t := by
  refine ⟨c.heap, c.mono, ?_, fun a ha ↦ c.frame a ha⟩
  rcases c.result with ⟨h0, he⟩ | ⟨h1, he⟩
  · simp only [bevOf, he, and_true]; exact h0
  · simp only [bevOf, he]; rw [h1]; decide

/-- **`Bytecode::evaluate` as `verify_bus_balance` calls it.** -/
theorem bytecodeEval (hE : Proofs.Bytecode.EvaluateSpec) : Vbb.BytecodeEvalSpec BcOk bevOf :=
  fun s hpc h ↦ (hE s hpc (evalPre h)).imp fun _ ⟨hr, ht⟩ ↦
    ⟨hr, ht.imp_left fun ⟨a, b, c⟩ ↦ ⟨a, b, evalPost c⟩⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
