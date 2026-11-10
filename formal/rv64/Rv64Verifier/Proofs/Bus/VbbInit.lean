import Rv64Verifier.Proofs.Bus.VbbFence

/-!
# `verify_bus_balance` from its entry to the GKR loop

The prologue and the three layouts (`layouts`), the challenges (`alphasStep`, `betaStep`), the
loop's start (`sharedStep`, `countStep`, `valuesStep`): at `0x80006614` (a positive depth) or
`0x80006b54` (depth zero), what the rest reads is in place (`Kept`) and the code runs the GKR loop
and the rest of the mirror (`AfterStart.tracks`); or the function has returned `Err`, or the run
reached a dead end.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript

/-- The push side's tree depth, the GKR loop's layer count. -/
def pushDepth (s : MachineState) : ℕ :=
  (busLayoutRust [0, (logMem s).toNat, (logBc s).toNat] (busLayoutAt s (s.getReg .x11)).push).depth

/-- What runs after the GKR loop, from its state. -/
def tail (bev : MachineState → Word → List E → Option E) (s : MachineState) (k : Start) (cnt : E) :
    GkrState → TM BusResultRust :=
  vbbTail (bev s (bytecodeOf s (s.getReg .x11))) (busLayoutAt s (s.getReg .x11)) k.alphas k.beta cnt

/-- At the GKR loop's test: the loop's state `⟨[sh, sh, cnt], []⟩` in `values` at `S - 176`. -/
structure AfterStart (bev : MachineState → Word → List E → Option E) (s u : MachineState)
    (k : Start) (sh cnt : E) : Prop where
  inv : Inv s u
  kept : Kept s u k
  x18 : u.getReg .x18 = s.getReg .x10
  x20 : u.getReg .x20 = s.getReg .x12
  x22 : u.getReg .x22 = s.getReg .x12 + 8
  x24 : u.getReg .x24 = vecPtr s (s.getReg .x11 + 24)
  x25 : (u.getReg .x25).toNat = pushDepth s
  x11 : u.getReg .x11 = k.count0
  x12 : u.getReg .x12 = k.count1
  cntEq : cnt = eOf3 k.count0 k.count1 (u.getReg .x13)
  x19 : u.getReg .x19 = vecPtr u (s.getReg .x2 - 176)
  values : NewVecE s u (s.getReg .x2 - 176) [sh, sh, cnt]
  tracks : Tracks (prog bev s) (s.getReg .x12) s u
    (gkrLoopM (pushDepth s) ⟨[sh, sh, cnt], []⟩ >>= tail bev s k cnt)
  branch : (u.pc = 0x80006b54 ∧ pushDepth s = 0) ∨ (u.pc = 0x80006614 ∧ 0 < pushDepth s)
  fence : Fence s u (vecPtr u (s.getReg .x2 - 176))

theorem prog_eq (bev : MachineState → Word → List E → Option E) (s : MachineState) :
    Tracks (prog bev s) (s.getReg .x12) s s (do
      let alphas ← TM.samples busBits
      let beta ← TM.sample
      let shared ← TM.nextScalar
      let count ← TM.nextScalar
      let state ← gkrLoopM (pushDepth s) ⟨[shared, shared, count], []⟩
      vbbTail (bev s (bytecodeOf s (s.getReg .x11))) (busLayoutAt s (s.getReg .x11)) alphas beta
        count state) :=
  fun T hT ↦ ⟨T, hT, by rw [prog, verifyBusBalanceM_eq]; rfl⟩

/-- At the first `next_scalar`'s entry. -/
structure Head (bev : MachineState → Word → List E → Option E) (s u : MachineState) (al : List E)
    (beta : E) : Prop where
  inv : Inv s u
  x1 : u.getReg .x1 = 0x80006558
  x10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608
  x11 : u.getReg .x11 = s.getReg .x12
  x8 : u.getReg .x8 = vecLen s (s.getReg .x11 + 72)
  x9 : u.getReg .x9 = vecLen s (s.getReg .x11 + 24)
  x18 : u.getReg .x18 = s.getReg .x10
  x19 : u.getReg .x19 = s.getReg .x11
  x20 : u.getReg .x20 = s.getReg .x12
  x22 : u.getReg .x22 = s.getReg .x12 + 8
  x24 : u.getReg .x24 = vecPtr s (s.getReg .x11 + 24)
  x25 : (u.getReg .x25).toNat = pushDepth s
  betaEq : beta = eOf3 (u.getMem (s.getReg .x2 - 1192)) (u.getMem (s.getReg .x2 - 1200))
    (u.getMem (s.getReg .x2 - 1184))
  lm : u.getMem (s.getReg .x2 - 1136) = logMem s
  lb : u.getMem (s.getReg .x2 - 1152) = logBc s
  pullPtr : u.getMem (s.getReg .x2 - 1168) = vecPtr s (s.getReg .x11 + 48)
  pullLen : u.getMem (s.getReg .x2 - 1176) = vecLen s (s.getReg .x11 + 48)
  countPtr : u.getMem (s.getReg .x2 - 1160) = vecPtr s (s.getReg .x11 + 72)
  push : LayoutAt s u (s.getReg .x2 - 1080)
    (busLayoutRust [0, (logMem s).toNat, (logBc s).toNat] (busLayoutAt s (s.getReg .x11)).push)
  pull : LayoutAt s u (s.getReg .x2 - 1024)
    (busLayoutRust [0, (logMem s).toNat, (logBc s).toNat] (busLayoutAt s (s.getReg .x11)).pull)
  count : LayoutAt s u (s.getReg .x2 - 968) (busLayoutRust [] (busLayoutAt s (s.getReg .x11)).count)
  alphas : NewVecE s u (s.getReg .x2 - 912) al
  weights : NewVecE s u (s.getReg .x2 - 888) (eqKernelRust al)
  len : al.length = 4
  tracks : Tracks (prog bev s) (s.getReg .x12) s u (do
    let shared ← TM.nextScalar
    let count ← TM.nextScalar
    let state ← gkrLoopM (pushDepth s) ⟨[shared, shared, count], []⟩
    vbbTail (bev s (bytecodeOf s (s.getReg .x11))) (busLayoutAt s (s.getReg .x11)) al beta
      count state)

theorem headStep (hBL : BusLayoutSpec) (hS : SamplesSpec) (hEK : Vbb.EqKernelSpec)
    (hD : DuplexSpec) {bev : MachineState → Word → List E → Option E} {s : MachineState}
    (hpc : s.pc = 0x80006428) (hpre : BusBalancePre s) :
    ∃ u, Reaches Image.code s u ∧
      ((u.pc = 0x8000c720 ∧ ∃ al beta, Head bev s u al beta) ∨ Dead Image.code u) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨v₀, hr₀, ⟨hpc₀, L⟩ | hd⟩ := layouts hBL hpc hpre
  swap
  · exact ⟨v₀, hr₀, Or.inr hd⟩
  obtain ⟨v₁, hr₁, ⟨hpc₁, al, A⟩ | hd⟩ := alphasStep hS hEK hpre L hpc₀
  swap
  · exact ⟨v₁, hr₀.trans hr₁, Or.inr hd⟩
  obtain ⟨u, hr₂, ⟨hpc₂, B⟩ | hd⟩ := betaStep hD hpre A.inv hpc₁
    ((A.regs .x20 (by decide)).trans L.regs.x20)
  swap
  · exact ⟨u, hr₀.trans (hr₁.trans hr₂), Or.inr hd⟩
  have stAB := A.step.trans B.step
  have fAB : FrameW s fun a ↦ Within a (s.getReg .x2 - 912) 48 ∨
      Within a (s.getReg .x2 - 1200) 24 := fun a ha ↦ by
    rcases ha with ha | ha <;> addr_omega [ha, hb1]
  have wd {x : Word} (hx : ∀ y, Within y x 8 → ¬ (Within y (s.getReg .x2 - 912) 48 ∨
      Within y (s.getReg .x2 - 1200) 24))
      (hy : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧ x.toNat + 8 ≤ (s.getReg .x2).toNat) :
      u.getMem x = v₀.getMem x := stAB.word hpre hx (Or.inl hy)
  have rg (r : Reg) (h1 : r ∈ ([.x8, .x9, .x18, .x19, .x20, .x24] : List Reg)) :
      u.getReg r = v₀.getReg r := by
    rw [B.regs r h1, A.regs r (mem_of_mem h1 _)]
  have hdepth : (v₁.getMem (s.getReg .x2 - 1032)).toNat = pushDepth s := by
    rw [A.step.word hpre (fun y hy hy' ↦ by addr_omega [hy, hy', hb1])
      (Or.inl (by addr_omega [hb1]))]
    have := congrArg BusLayoutRust.depth L.push.value
    simp only [busLayoutOf] at this
    rw [pushDepth, ← this, show s.getReg .x2 - 1080 + 48 = s.getReg .x2 - 1032 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
  refine ⟨u, hr₀.trans (hr₁.trans hr₂), Or.inl ⟨hpc₂, al, _, {
    inv := B.inv
    x1 := B.x1
    x10 := B.x10
    x11 := B.x11
    x8 := (rg .x8 (by decide)).trans L.x8
    x9 := (rg .x9 (by decide)).trans L.x9
    x18 := (rg .x18 (by decide)).trans L.regs.x18
    x19 := (rg .x19 (by decide)).trans L.regs.x19
    x20 := (rg .x20 (by decide)).trans L.regs.x20
    x22 := B.x22
    x24 := (rg .x24 (by decide)).trans L.x24
    x25 := by rw [B.x25, hdepth]
    betaEq := rfl
    lm := (wd (fun y hy hy' ↦ by addr_omega [hy, hy', hb1]) (by addr_omega [hb1])).trans L.lm
    lb := (wd (fun y hy hy' ↦ by addr_omega [hy, hy', hb1]) (by addr_omega [hb1])).trans L.lb
    pullPtr := (wd (fun y hy hy' ↦ by addr_omega [hy, hy', hb1]) (by addr_omega [hb1])).trans
      L.pullPtr
    pullLen := (wd (fun y hy hy' ↦ by addr_omega [hy, hy', hb1]) (by addr_omega [hb1])).trans
      L.pullLen
    countPtr := (wd (fun y hy hy' ↦ by addr_omega [hy, hy', hb1]) (by addr_omega [hb1])).trans
      L.countPtr
    push := L.push.keepR hpre stAB fAB (inFrame hpre (k := 1080) (n := 56) (by omega) (by omega))
      fun y hy hy' ↦ by addr_omega [hy, hy', hb1]
    pull := L.pull.keepR hpre stAB fAB (inFrame hpre (k := 1024) (n := 56) (by omega) (by omega))
      fun y hy hy' ↦ by addr_omega [hy, hy', hb1]
    count := L.count.keepR hpre stAB fAB (inFrame hpre (k := 968) (n := 56) (by omega) (by omega))
      fun y hy hy' ↦ by addr_omega [hy, hy', hb1]
    alphas := A.alphas.keepR hpre B.step (frameW_slot hpre (k := 1200) (n := 24) (by omega) (by omega))
      (by addr_omega [hb1]) fun y hy hy' ↦ by addr_omega [hy, hy', hb1]
    weights := A.weights.keepR hpre B.step (frameW_slot hpre (k := 1200) (n := 24) (by omega) (by omega))
      (by addr_omega [hb1]) fun y hy hy' ↦ by addr_omega [hy, hy', hb1]
    len := A.len
    tracks := ((prog_eq bev s).keep L.transcript |>.bind A.run).bind B.run }⟩⟩

/-- From the entry to the GKR loop's test, or out. -/
theorem start (hBL : BusLayoutSpec) (hS : SamplesSpec) (hEK : Vbb.EqKernelSpec)
    (hD : DuplexSpec) (hN : NextScalarSpec) (hA : AllocSpec)
    {bev : MachineState → Word → List E → Option E} {s : MachineState}
    (hpc : s.pc = 0x80006428) (hpre : BusBalancePre s) :
    ∃ z, Reaches Image.code s z ∧ (Done bev s z ∨ Dead Image.code z ∨
      ∃ k sh cnt, AfterStart bev s z k sh cnt) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨u, hr, ⟨hpcu, al, beta, H⟩ | hd⟩ := headStep (bev := bev) hBL hS hEK hD hpc hpre
  swap
  · exact ⟨u, hr, Or.inr (Or.inl hd)⟩
  obtain ⟨w, hrw, hdone | hd | ⟨hpcw, C, trC⟩⟩ :=
    sharedStep hN hpre H.inv hpcu H.x1 H.x10 H.x11 H.x18 H.x20 H.tracks
  · exact ⟨w, hr.trans hrw, Or.inl hdone⟩
  · exact ⟨w, hr.trans hrw, Or.inr (Or.inl hd)⟩
  obtain ⟨y, hry, hdone | hd | ⟨hpcy, D, trD⟩⟩ :=
    countStep hN hpre C.inv hpcw C.x1 C.x10 C.x11 ((C.regs .x18 (by decide)).trans H.x18) trC
  · exact ⟨y, hr.trans (hrw.trans hry), Or.inl hdone⟩
  · exact ⟨y, hr.trans (hrw.trans hry), Or.inr (Or.inl hd)⟩
  obtain ⟨z, hrz, hd | E⟩ := valuesStep hA hpre D.inv hpcy D.x1 D.x10 D.x11
  · exact ⟨z, hr.trans (hrw.trans (hry.trans hrz)), Or.inr (Or.inl hd)⟩
  have stE := E.step
  have stDE := D.step.trans E.step
  have stCDE := C.step.trans stDE
  have fE : FrameW s fun a ↦ Within a (s.getReg .x2 - 1312) 8 ∨
      Within a (s.getReg .x2 - 176) 24 := fun a ha ↦ by addr_omega [ha, hb1]
  have fCDE : FrameW s fun a ↦ (Within a (s.getReg .x2 - 608) 32 ∨
      Within a (s.getReg .x2 - 1248) 8) ∨ ((Within a (s.getReg .x2 - 608) 32 ∨
      Within a (s.getReg .x2 - 1264) 8 ∨ Within a (s.getReg .x2 - 1240) 24) ∨
      (Within a (s.getReg .x2 - 1312) 8 ∨ Within a (s.getReg .x2 - 176) 24)) :=
    fun a ha ↦ by addr_omega [ha, hb1]
  have fr (j : Nat) (hj1 : 8 ≤ j) (hj2 : j ≤ 1344) :
      (s.getReg .x2 - 1344).toNat ≤ (s.getReg .x2 - BitVec.ofNat 64 j).toNat ∧
        (s.getReg .x2 - BitVec.ofNat 64 j).toNat + 8 ≤ (s.getReg .x2).toNat := by
    addr_omega [hb1, hj1, hj2]
  have rz (r : Reg) (h1 : r ∈ ([.x8, .x9, .x18, .x20, .x21, .x22, .x24, .x25, .x27] : List Reg))
      (h2 : r ∈ ([.x8, .x18, .x19, .x20, .x21, .x22, .x24, .x25, .x27] : List Reg)) :
      z.getReg r = w.getReg r := by
    rw [E.regs r h1, D.regs r h2]
  have ru (r : Reg) (h1 : r ∈ ([.x9, .x18, .x19, .x20, .x22, .x24, .x25] : List Reg))
      (h2 : r ∈ ([.x8, .x9, .x18, .x20, .x21, .x22, .x24, .x25, .x27] : List Reg))
      (h3 : r ∈ ([.x8, .x18, .x19, .x20, .x21, .x22, .x24, .x25, .x27] : List Reg)) :
      z.getReg r = u.getReg r := by
    rw [rz r h2 h3, C.regs r h1]
  have hx25 : (z.getReg .x25).toNat = pushDepth s := by
    rw [ru .x25 (by decide) (by decide) (by decide)]; exact H.x25
  let k : Start := ⟨al, u.getMem (s.getReg .x2 - 1192), u.getMem (s.getReg .x2 - 1200),
    u.getMem (s.getReg .x2 - 1184), y.getMem (s.getReg .x2 - 1224), y.getMem (s.getReg .x2 - 1232),
    H.len⟩
  have hk : k.beta = beta := H.betaEq.symm
  have wy (j : Nat) (hj1 : 8 ≤ j) (hj2 : j ≤ 1344)
      (hm : ∀ y', Within y' (s.getReg .x2 - BitVec.ofNat 64 j) 8 → ¬ (Within y' (s.getReg .x2 - 1312) 8 ∨
        Within y' (s.getReg .x2 - 176) 24)) :
      z.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = y.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    stE.word hpre hm (Or.inl (fr j hj1 hj2))
  have wu (j : Nat) (hj1 : 8 ≤ j) (hj2 : j ≤ 1344)
      (hm : ∀ y', Within y' (s.getReg .x2 - BitVec.ofNat 64 j) 8 → ¬ ((Within y' (s.getReg .x2 - 608) 32 ∨
        Within y' (s.getReg .x2 - 1248) 8) ∨ ((Within y' (s.getReg .x2 - 608) 32 ∨
        Within y' (s.getReg .x2 - 1264) 8 ∨ Within y' (s.getReg .x2 - 1240) 24) ∨
        (Within y' (s.getReg .x2 - 1312) 8 ∨ Within y' (s.getReg .x2 - 176) 24)))) :
      z.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    stCDE.word hpre hm (Or.inl (fr j hj1 hj2))
  refine ⟨z, hr.trans (hrw.trans (hry.trans hrz)), Or.inr (Or.inr ⟨k,
    eOf3 (w.getReg .x27) (w.getReg .x21) (w.getReg .x8),
    eOf3 (y.getMem (s.getReg .x2 - 1224)) (y.getMem (s.getReg .x2 - 1232)) (y.getReg .x9), {
    inv := E.inv
    kept := {
      out := by rw [E.out, D.regs .x18 (by decide), C.regs .x18 (by decide), H.x18]
      pushLen := (wy 1264 (by omega) (by omega) fun y' hy h' ↦ by addr_omega [hy, h', hb1]).trans
        (D.pushLen.trans ((C.regs .x9 (by decide)).trans H.x9))
      countLen := (wy 1248 (by omega) (by omega) fun y' hy h' ↦ by addr_omega [hy, h', hb1]).trans
        ((D.step.word hpre (fun y' hy h' ↦ by addr_omega [hy, h', hb1])
          (Or.inl (fr 1248 (by omega) (by omega)))).trans (C.countLen.trans H.x8))
      layout := (wy 1240 (by omega) (by omega) fun y' hy h' ↦ by addr_omega [hy, h', hb1]).trans
        (D.layout.trans ((C.regs .x19 (by decide)).trans H.x19))
      count1 := wy 1232 (by omega) (by omega) fun y' hy h' ↦ by addr_omega [hy, h', hb1]
      count0 := wy 1224 (by omega) (by omega) fun y' hy h' ↦ by addr_omega [hy, h', hb1]
      beta1 := wu 1200 (by omega) (by omega) fun y' hy h' ↦ by addr_omega [hy, h', hb1]
      beta0 := wu 1192 (by omega) (by omega) fun y' hy h' ↦ by addr_omega [hy, h', hb1]
      beta2 := wu 1184 (by omega) (by omega) fun y' hy h' ↦ by addr_omega [hy, h', hb1]
      lm := (wu 1136 (by omega) (by omega) fun y' hy h' ↦ by addr_omega [hy, h', hb1]).trans H.lm
      lb := (wu 1152 (by omega) (by omega) fun y' hy h' ↦ by addr_omega [hy, h', hb1]).trans H.lb
      pullPtr := (wu 1168 (by omega) (by omega) fun y' hy h' ↦ by
        addr_omega [hy, h', hb1]).trans H.pullPtr
      pullLen := (wu 1176 (by omega) (by omega) fun y' hy h' ↦ by
        addr_omega [hy, h', hb1]).trans H.pullLen
      countPtr := (wu 1160 (by omega) (by omega) fun y' hy h' ↦ by
        addr_omega [hy, h', hb1]).trans H.countPtr
      push := H.push.keepR hpre stCDE fCDE (inFrame hpre (k := 1080) (n := 56) (by omega)
        (by omega)) fun y' hy h' ↦ by addr_omega [hy, h', hb1]
      pull := H.pull.keepR hpre stCDE fCDE (inFrame hpre (k := 1024) (n := 56) (by omega)
        (by omega)) fun y' hy h' ↦ by addr_omega [hy, h', hb1]
      count := H.count.keepR hpre stCDE fCDE (inFrame hpre (k := 968) (n := 56) (by omega)
        (by omega)) fun y' hy h' ↦ by addr_omega [hy, h', hb1]
      alphas := H.alphas.keepR hpre stCDE fCDE (by addr_omega [hb1])
        fun y' hy h' ↦ by addr_omega [hy, h', hb1]
      weights := H.weights.keepR hpre stCDE fCDE (by addr_omega [hb1])
        fun y' hy h' ↦ by addr_omega [hy, h', hb1] }
    x18 := (ru .x18 (by decide) (by decide) (by decide)).trans H.x18
    x20 := (ru .x20 (by decide) (by decide) (by decide)).trans H.x20
    x22 := (ru .x22 (by decide) (by decide) (by decide)).trans H.x22
    x24 := (ru .x24 (by decide) (by decide) (by decide)).trans H.x24
    x25 := hx25
    x11 := E.x11
    x12 := E.x12
    cntEq := by rw [E.x13]
    x19 := E.x19
    values := by
      have hv := E.values
      rw [D.regs .x27 (by decide), D.regs .x21 (by decide), D.regs .x8 (by decide)] at hv
      exact hv
    tracks := by
      have := trD.keep E.transcript
      rw [← hk] at this
      exact this
    fence := by
      have hm : heapNext u ≤ (vecPtr z (s.getReg .x2 - 176)).toNat :=
        (C.step.trans D.step).mono.trans E.above
      have hk (x : Word) (h1 : (s.getReg .x2 - 1080).toNat ≤ x.toNat)
          (h2 : x.toNat + 8 ≤ (s.getReg .x2 - 864).toNat) : z.getMem x = u.getMem x :=
        stCDE.word hpre (fun y' hy h' ↦ by
          rcases h' with (h' | h') | ((h' | h' | h') | (h' | h')) <;>
            addr_omega [hy, h', h1, h2, hb1])
          (Or.inl (by addr_omega [h1, h2, hb1]))
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
      · exact BufBelow.of_newBuf H.push.frameworkNew (hk _ (by addr_omega [hb1]) (by addr_omega [hb1]))
          (hk _ (by addr_omega [hb1]) (by addr_omega [hb1])) hm
      · exact BufBelow.of_newBuf H.push.tablesNew (hk _ (by addr_omega [hb1]) (by addr_omega [hb1]))
          (hk _ (by addr_omega [hb1]) (by addr_omega [hb1])) hm
      · exact BufBelow.of_newBuf H.pull.frameworkNew (hk _ (by addr_omega [hb1]) (by addr_omega [hb1]))
          (hk _ (by addr_omega [hb1]) (by addr_omega [hb1])) hm
      · exact BufBelow.of_newBuf H.pull.tablesNew (hk _ (by addr_omega [hb1]) (by addr_omega [hb1]))
          (hk _ (by addr_omega [hb1]) (by addr_omega [hb1])) hm
      · exact BufBelow.of_newBuf H.count.frameworkNew (hk _ (by addr_omega [hb1])
          (by addr_omega [hb1])) (hk _ (by addr_omega [hb1]) (by addr_omega [hb1])) hm
      · exact BufBelow.of_newBuf H.count.tablesNew (hk _ (by addr_omega [hb1]) (by addr_omega [hb1]))
          (hk _ (by addr_omega [hb1]) (by addr_omega [hb1])) hm
      · exact BufBelow.of_newVecE H.alphas (hk _ (by addr_omega [hb1]) (by addr_omega [hb1]))
          (hk _ (by addr_omega [hb1]) (by addr_omega [hb1])) hm
      · exact BufBelow.of_newVecE H.weights (hk _ (by addr_omega [hb1]) (by addr_omega [hb1]))
          (hk _ (by addr_omega [hb1]) (by addr_omega [hb1])) hm
    branch := by
      rcases E.branch with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, by rw [← hx25, h2]; rfl⟩
      · exact Or.inr ⟨h1, by
          rw [← hx25]; exact Nat.pos_of_ne_zero fun h0 ↦ h2 (BitVec.eq_of_toNat_eq h0)⟩ }⟩)⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
