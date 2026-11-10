import Rv64Verifier.Proofs.Bus.VbbTail3

/-!
# `verify_bus_balance` past the GKR loop: from `0x80006b60` to `0x80006ca0`

`scalarsStage` composes `checkStep`, `memoryStep`, `memFinalStep` and `bcFinalStep`.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- A `Vec<E>` in registers keeps what it holds across a step writing the frame's `A`. -/
theorem NewVecR.keepR {s v w : MachineState} {A : Word → Prop} (hpre : BusBalancePre s)
    (st : StepR s v w A) (hA : FrameW s A) {cap ptr len : Word} {xs : List E}
    (h : NewVecR s v cap ptr len xs) : NewVecR s w cap ptr len xs := by
  have hm := st.mono
  have hle := h.le
  have hbuf := h.buf
  refine ⟨hle, ?_, ?_⟩
  · simp only [NewBuf] at hbuf ⊢
    exact ⟨hbuf.1, hbuf.2.imp_right fun h' ↦ ⟨h'.1, by omega⟩⟩
  · rw [← h.elems]
    refine eListAt_congr fun i hi ↦ ?_
    have hc : 24 * i + 24 ≤ cap.toNat * 24 := by omega
    have hbd : ptr.toNat + cap.toNat * 24 ≤ 2 ^ 64 := by
      simp only [NewBuf] at hbuf
      rcases hbuf.2 with h0 | ⟨b1, b2⟩
      · omega
      · have := st.heap.hi
        simp only [heapNext, heapEnd] at *; omega
    have bw (j : Nat) (hj : j + 8 ≤ 24) : w.getMem (ptr + BitVec.ofNat 64 (24 * i) +
        BitVec.ofNat 64 j) = v.getMem (ptr + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 j) :=
      st.bufWord hpre hA hbuf (by addr_omega [hbd, hc, hj]) (by addr_omega [hbd, hc, hj])
    exact eAt_congr (by simpa using bw 0 (by omega)) (bw 8 (by omega)) (bw 16 (by omega))

/-- What the steps from `0x80006b60` to `0x80006ca0` write in the frame. -/
def ScalarsW (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 608) 32 ∨ Within a (s.getReg .x2 - 864) 24 ∨
    Within a (s.getReg .x2 - 1320) 8

theorem ScalarsW.frameW {s : MachineState} (hpre : BusBalancePre s) : FrameW s (ScalarsW s) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  intro a ha
  rcases ha with ha | ha | ha <;> addr_omega [ha, hb1]

theorem ScalarsW.free {s : MachineState} (hpre : BusBalancePre s) {a : Word} (ha : ScalarsW s a) :
    Free s a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rcases ha with ha | ha | ha
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1]))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1]))))))
  · exact Or.inl (by addr_omega [ha, hb1])

/-- At `0x80006ca0`, past the three scalars: `memory`'s `Vec` at `S - 864` (its buffer and length
in `s0`, `s1`), `memory_final`'s limbs in `s9`, `s6`, `s7`, `bytecode_final`'s in `s10`, `a1` and
at `S - 584`, the point in `s11`, `s5` and its capacity at `S - 1320`. -/
structure Scalars (bev : MachineState → Word → List E → Option E) (s q : MachineState) (k : Start)
    (state : GkrState) (mem : List E) (mf bf : E) : Prop where
  inv : Inv s q
  kept : Kept s q k
  x18 : q.getReg .x18 = s.getReg .x10
  x19 : q.getReg .x19 = vecPtr q (s.getReg .x2 - 176)
  x20 : q.getReg .x20 = s.getReg .x12
  x24 : q.getReg .x24 = vecPtr s (s.getReg .x11 + 24)
  x8 : q.getReg .x8 = vecPtr q (s.getReg .x2 - 864)
  x9 : q.getReg .x9 = vecLen q (s.getReg .x2 - 864)
  memory : NewVecE s q (s.getReg .x2 - 864) mem
  values : NewVecE s q (s.getReg .x2 - 176) state.values
  point : NewVecR s q (q.getMem (s.getReg .x2 - 1320)) (q.getReg .x27) (q.getReg .x21) state.point
  lm : (logMem s).toNat ≤ state.point.length
  lb : (logBc s).toNat ≤ state.point.length
  mfEq : mf = eOf3 (q.getReg .x25) (q.getReg .x22) (q.getReg .x23)
  bfEq : bf = eOf3 (q.getReg .x26) (q.getReg .x11) (q.getMem (s.getReg .x2 - 584))
  tracks : Tracks (prog bev s) (s.getReg .x12) s q (rest bev s k state mem mf bf)

theorem scalarsStage (hNS : NextScalarsSpec) (hN : NextScalarSpec)
    {bev : MachineState → Word → List E → Option E} {s u : MachineState} {k : Start} {cnt : E}
    {state : GkrState} (hpre : BusBalancePre s) (G : AfterGkr bev s u k cnt state)
    (hpc : u.pc = 0x80006b60) :
    ∃ q, Reaches Image.code u q ∧ (Done bev s q ∨ Dead Image.code q ∨
      (q.pc = 0x80006ca0 ∧ ∃ memory mf bf, Scalars bev s q k state memory mf bf)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨w, hrw, hdone | hd | ⟨hpcw, hmw, hrg, hc, hl, hl'⟩⟩ := checkStep hpre G hpc
  · exact ⟨w, hrw, Or.inl hdone⟩
  · exact ⟨w, hrw, Or.inr (Or.inl hd)⟩
  have I₀ := G.inv.same hmw (hrg .x2 (by decide))
  have htr := G.tracks
  simp only [tail, vbbTail_eq] at htr
  have htr₀ := (htr.require hc).keep fun T hT ↦ TranscriptAt.same hpre G.inv hmw hT
  obtain ⟨y, hry, hdone | hd | ⟨hpcy, memory, M, trM⟩⟩ := memoryStep hNS hpre I₀ hpcw
    ((hrg .x18 (by decide)).trans G.x18) ((hrg .x20 (by decide)).trans G.x20) htr₀
  · exact ⟨y, hrw.trans hry, Or.inl hdone⟩
  · exact ⟨y, hrw.trans hry, Or.inr (Or.inl hd)⟩
  have ry (r : Reg) (h1 : r ∈ ([.x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] :
      List Reg)) : y.getReg r = u.getReg r := by
    rw [M.regs r h1, hrg r (mem_of_mem h1 _)]
  obtain ⟨z, hrz, hdone | hd | ⟨hpcz, F, trF⟩⟩ := memFinalStep hN hpre M.inv hpcy M.x1 M.x10 M.x11
    ((ry .x18 (by decide)).trans G.x18) ((ry .x20 (by decide)).trans G.x20) trM
  · exact ⟨z, hrw.trans (hry.trans hrz), Or.inl hdone⟩
  · exact ⟨z, hrw.trans (hry.trans hrz), Or.inr (Or.inl hd)⟩
  obtain ⟨q, hrq, hdone | hd | ⟨hpcq, B, trB⟩⟩ := bcFinalStep hN hpre F.inv hpcz F.x1 F.x10 F.x11
    ((F.regs .x18 (by decide)).trans ((ry .x18 (by decide)).trans G.x18)) trF
  · exact ⟨q, hrw.trans (hry.trans (hrz.trans hrq)), Or.inl hdone⟩
  · exact ⟨q, hrw.trans (hry.trans (hrz.trans hrq)), Or.inr (Or.inl hd)⟩
  have rq (r : Reg) (h1 : r ∈ ([.x18, .x19, .x20, .x21, .x24, .x27] : List Reg)) :
      q.getReg r = u.getReg r := by
    rw [B.regs r (mem_of_mem h1 _), F.regs r (mem_of_mem h1 _), ry r (mem_of_mem h1 _)]
  have stYQ : StepR s y q (Within · (s.getReg .x2 - 608) 32) :=
    (F.step.trans B.step).weaken fun a ha ↦ by rcases ha with ha | ha <;> exact ha
  have stUQ : StepR s u q (ScalarsW s) :=
    ((((StepR.same hmw G.inv.heap (hrg .x2 (by decide))).trans M.step).trans F.step).trans
      B.step).weaken fun a ha ↦ by
        rcases ha with (((ha | ha | ha | ha) | ha) | ha)
        · exact False.elim ha
        · exact Or.inl (by addr_omega [ha, hb1])
        · exact Or.inr (Or.inl ha)
        · exact Or.inr (Or.inr ha)
        · exact Or.inl ha
        · exact Or.inl ha
  have fYQ : FrameW s (Within · (s.getReg .x2 - 608) 32) :=
    frameW_slot hpre (k := 608) (n := 32) (by omega) (by omega)
  have fW := ScalarsW.frameW hpre
  have hvals := G.values.keepR hpre stUQ fW (by addr_omega [hb1]) fun y' hy h' ↦ by
    rcases h' with h' | h' | h' <;> addr_omega [hy, h', hb1]
  have hlen : state.point.length = (u.getReg .x21).toNat := by
    rw [← G.point.elems, eListAt_length]
  have cap : q.getMem (s.getReg .x2 - 1320) = u.getReg .x22 := by
    rw [stYQ.word hpre (fun y' hy h' ↦ by addr_omega [hy, h', hb1]) (Or.inl (by addr_omega [hb1])),
      M.ptCap, hrg .x22 (by decide)]
  have w864 (j : Nat) (hj : j ≤ 16) :
      q.getMem (s.getReg .x2 - 864 + BitVec.ofNat 64 j) =
        y.getMem (s.getReg .x2 - 864 + BitVec.ofNat 64 j) :=
    stYQ.word hpre (fun y' hy h' ↦ by addr_omega [hy, h', hb1, hj]) (Or.inl (by addr_omega [hb1, hj]))
  refine ⟨q, hrw.trans (hry.trans (hrz.trans hrq)), Or.inr (Or.inr ⟨hpcq, memory,
    eOf3 (z.getReg .x25) (z.getReg .x22) (z.getReg .x23),
    eOf3 (q.getReg .x26) (q.getReg .x11) (q.getMem (s.getReg .x2 - 584)), {
    inv := B.inv
    kept := G.kept.step hpre (stUQ.weaken fun _ ha ↦ ScalarsW.free hpre ha)
    x18 := (rq .x18 (by decide)).trans G.x18
    x19 := by
      rw [rq .x19 (by decide), G.x19, vecPtr, vecPtr]
      exact (stUQ.word hpre (fun y' hy h' ↦ by rcases h' with h' | h' | h' <;>
        addr_omega [hy, h', hb1]) (Or.inl (by addr_omega [hb1]))).symm
    x20 := (rq .x20 (by decide)).trans G.x20
    x24 := (rq .x24 (by decide)).trans G.x24
    x8 := by
      rw [B.regs .x8 (by decide), F.regs .x8 (by decide), M.x8, vecPtr, vecPtr]
      exact (w864 8 (by omega)).symm
    x9 := by
      rw [B.regs .x9 (by decide), F.regs .x9 (by decide), M.x9, vecLen, vecLen]
      exact (w864 16 (by omega)).symm
    memory := M.memory.keepR hpre stYQ fYQ (by addr_omega [hb1])
      fun y' hy h' ↦ by addr_omega [hy, h', hb1]
    values := hvals
    point := by
      rw [cap, rq .x27 (by decide), rq .x21 (by decide)]
      exact G.point.keepR hpre stUQ fW
    lm := by rw [hlen]; exact hl
    lb := by rw [hlen]; exact hl'
    mfEq := by
      rw [B.regs .x25 (by decide), B.regs .x22 (by decide), B.regs .x23 (by decide)]
    bfEq := rfl
    tracks := trB }⟩)⟩

/-- From `0x80006ca0` to the return. -/
def RestStage (BcOk : MachineState → Nat → Word → Prop)
    (bev : MachineState → Word → List E → Option E) : Prop :=
  ∀ s q k state mem mf bf, BusBalancePre s →
    BcOk s busBalanceStack (bytecodeOf s (s.getReg .x11)) → Scalars bev s q k state mem mf bf →
    q.pc = 0x80006ca0 → ∃ t, Reaches Image.code q t ∧ (Done bev s t ∨ Dead Image.code t)

/-- `TailStage`, from the rest's stage. -/
theorem tailStage (hNS : NextScalarsSpec) (hN : NextScalarSpec)
    {BcOk : MachineState → Nat → Word → Prop} {bev : MachineState → Word → List E → Option E}
    (hR : RestStage BcOk bev) : TailStage BcOk bev := by
  intro s u k cnt state hpre hbc G hpc
  obtain ⟨q, hrq, hdone | hd | ⟨hpcq, mem, mf, bf, S⟩⟩ := scalarsStage hNS hN hpre G hpc
  · exact ⟨q, hrq, Or.inl hdone⟩
  · exact ⟨q, hrq, Or.inr hd⟩
  obtain ⟨t, hrt, ht⟩ := hR s q k state mem mf bf hpre hbc S hpcq
  exact ⟨t, hrq.trans hrt, ht⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
