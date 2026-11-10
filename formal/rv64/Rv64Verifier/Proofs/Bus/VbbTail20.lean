import Rv64Verifier.Proofs.Bus.VbbTail19

/-!
# `verify_bus_balance` past the GKR loop: `concat` and `Bytecode::evaluate`

From `concat`'s entry (`Indexed`): `bytecode_point = [point[..log_bytecode], alphas].concat()` at
`S - 768` (`concatCall`), the checked branch, `Bytecode::evaluate` into `S - 608`; its `Err`
returns through `s5` (`errDoneAt'`), its value moves to `S - 744` (`evalStage`, `Evaluated` at
`0x80007170`). `tailValue` is the mirror's result past the bytecode's value (`tailRest_eq`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
  Rv64Verifier.MultilinearContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The mirror past the bytecode's value -/

/-- `tailRest`'s result from the bytecode's value on. -/
def tailValue (layout : Layout) (alphas : List E) (beta : E) (state : GkrState)
    (memory : List E) (memoryFinal bytecodeFinal bytecodeValue : E) : BusResultRust :=
  let point := state.point
  let treeValues := state.values
  let frameworkLogRows := [0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayoutRust frameworkLogRows layout.push
  let pullLayout := busLayoutRust frameworkLogRows layout.pull
  let countLayout := busLayoutRust [] layout.count
  let weights := eqKernelRust alphas
  let memoryLow := point.take layout.logMemory
  let bytecodeLow := point.take layout.logBytecode
  let claims : List ColumnClaim :=
    [memory0, memory1, memory2].map (fun column ↦ ⟨column, memoryLow, memory.getD column 0⟩) ++
      [⟨memoryFinalCounters, memoryLow, memoryFinal⟩,
        ⟨bytecodeFinalCounters, bytecodeLow, bytecodeFinal⟩]
  let memoryIndex := indexMleRust memoryLow
  let bytecodeIndex := indexMleRust bytecodeLow
  let bytecodePoint := bytecodeLow ++ alphas
  let fingerprints := fun (pc memoryCount bytecodeCount : E) ↦
    [dotRust (weights.take 3) [sepStateRust, pc, gpowRust 0#64],
      dotRust (weights.take 6) [sepMemRust, memoryIndex, memoryCount, memory.getD 0 0,
        memory.getD 1 0, memory.getD 2 0],
      dotRust (weights.take 3) [sepBytecodeRust, bytecodeIndex, bytecodeCount] + bytecodeValue]
  let finalPc := gpowRust ((1#64 <<< (layout.logBytecode % 64)) - 1#64)
  let sides : List (List BusBlock × BusLayoutRust × List E × List E × E) :=
    [(layout.push, pushLayout, fingerprints (gpowRust 0#64) 1 1, weights, beta),
      (layout.pull, pullLayout, fingerprints finalPc memoryFinal bytecodeFinal, weights, beta),
      (layout.count, countLayout, [], [1], 0)]
  let r := sides.zipIdx.foldl (fun (acc : List (List Form) × List E) sd ↦
      let side := sideStepRust point treeValues acc.1 sd.2 sd.1.1 sd.1.2.1 sd.1.2.2.1 sd.1.2.2.2.1
        sd.1.2.2.2.2
      (side.1, acc.2 ++ [side.2]))
    (List.replicate tables.length (List.replicate 3 {}), [])
  ⟨claims, bytecodePoint, point, r.1, r.2⟩

theorem tailRest_eq (bytecodeEvaluate : List E → Option E) (layout : Layout) (alphas : List E)
    (beta : E) (state : GkrState) (memory : List E) (memoryFinal bytecodeFinal : E) :
    tailRest bytecodeEvaluate layout alphas beta state memory memoryFinal bytecodeFinal =
      TM.lift (bytecodeEvaluate (state.point.take layout.logBytecode ++ alphas)) >>= fun bv ↦
        pure (tailValue layout alphas beta state memory memoryFinal bytecodeFinal bv) :=
  rfl

/-- `rest`'s value past the bytecode's. -/
def restValue (s : MachineState) (k : Start) (state : GkrState) (memory : List E)
    (memoryFinal bytecodeFinal bytecodeValue : E) : BusResultRust :=
  tailValue (busLayoutAt s (s.getReg .x11)) k.alphas k.beta state memory memoryFinal bytecodeFinal
    bytecodeValue

/-! ## The `Err` exit through any register -/

/-- A block that wrote `errNiche` at `out` and jumped to the epilogue: the function returns `Err`,
what the mirror gives when it fails. -/
theorem errDoneAt' {bev : MachineState → Word → List E → Option E} {s u v : MachineState} {n : Nat}
    (hpre : BusBalancePre s) (h : Inv s u) (hn : n ≤ 120)
    (fr : MemFrame u v (s.getReg .x10) n) (sp : v.getReg .x2 = u.getReg .x2)
    (hpc : v.pc = 0x80007114) (hcap : v.getMem (s.getReg .x10) = 0xffffffffffffffff)
    (hnone : ∀ T, TranscriptAt s (s.getReg .x12) T → (prog bev s).run T = none) :
    ∃ t, Reaches Image.code v t ∧ Done bev s t := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have ho := hpre.out
  have hos := hpre.outStack
  have hof := hpre.outFree
  rw [stackLo_eq] at hos
  have fr' := DFrame.of_memFrame fr
  have hn' : heapNext v = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr' nextAddr fun i hi hw ↦ by addr_omega [hof.2, hw, hi, hn])
  have I : Inv s v := h.step hpre fr' (fun a ha ↦ ⟨Or.inl (by addr_omega [ha, hn]),
      by addr_omega [ha, hos, hb1, hn]⟩) ⟨hn' ▸ h.heap.lo, hn' ▸ h.heap.hi⟩ hn'.ge sp
  obtain ⟨t, hr, ex, hm⟩ := exit hpre I hpc
  refine ⟨t, hr, ex.pc, ex.preserves, ex.heap, ex.mono, fun T hT ↦ ?_, ex.frame⟩
  rw [show (verifyBusBalanceM (bev s (bytecodeOf s (s.getReg .x11)))
      (busLayoutAt s (s.getReg .x11))).run T = none from hnone T hT]
  show vecCap t (s.getReg .x10) = errNiche
  rw [vecCap, hm, hcap]
  rfl

/-! ## `concat` -/

/-- A buffer allocated since the entry, `n` of its elements read by a callee with an `m`-byte
stack below the frame, apart from a frame slot. -/
theorem bufPart {s v : MachineState} (hpre : BusBalancePre s) (h : Inv s v) {p : Word} {c n : Nat}
    (hb : NewBuf s v p (c * 24) 8) (hn : n ≤ c) {m : Nat} (hm : 1344 + m ≤ 4544) {k l : Nat}
    (hk : k ≤ 1344) :
    n = 0 ∨ (Region p (24 * n) ∧ Outside v p (24 * n) ∧ Apart p (24 * n) (stackLo v m) m ∧
      Apart p (24 * n) (s.getReg .x2 - BitVec.ofNat 64 k) l) := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have ha := hpre.stack.above
  have hhi := h.heap.hi
  have hlo := hpre.heap.lo
  have hmo := h.mono
  rw [stackLo_eq] at ha
  simp only [NewBuf] at hb
  rcases hb.2 with h0 | ⟨b1, b2⟩
  · exact Or.inl (by omega)
  simp only [heapNext, heapEnd, heapStart] at hhi hlo hmo b1 b2 ha
  refine Or.inr ⟨⟨Or.inl ⟨by omega, by omega⟩, hb.1⟩, ⟨Or.inl (by simp only [heapNext]; omega),
    by addr_omega [b2, hhi, hn]⟩, ?_, ?_⟩
  · simp only [stackLo, h.sp]; addr_omega [b2, hhi, ha, hb1, hm, hn]
  · addr_omega [b2, hhi, ha, hb1, hk, hn]

/-- `concat`'s call: `bytecode_point` at `S - 768`. -/
theorem concatCall (hC : SliceConcatSpec) {bev : MachineState → Word → List E → Option E}
    {s v : MachineState} {k : Start} {state : GkrState} {mem : List E} {mf bf : E}
    (hpre : BusBalancePre s) (X : Indexed bev s v k state mem mf bf) (hpc : v.pc = 0x8000cfc4) :
    ∃ w, Reaches Image.code v w ∧ ((w.pc = 0x800070b0 ∧ Preserves v w ∧ Inv s w ∧
      StepS s v w (Within · (s.getReg .x2 - BitVec.ofNat 64 768) 24) ∧
      NewVecE s w (s.getReg .x2 - 768) (state.point.take (logBc s).toNat ++ k.alphas)) ∨
      Dead Image.code w) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  obtain ⟨o1, o2, o3⟩ := frameSlot (m := sliceConcatStack) hpre X.inv (n := 24) (k := 768)
    (by omega) (by omega) (by omega) (by decide)
  obtain ⟨p1, p2, p3⟩ := frameSlot (m := sliceConcatStack) hpre X.inv (n := 32) (k := 608)
    (by omega) (by omega) (by omega) (by decide)
  have hst : RtStack v sliceConcatStack :=
    hpre.stack.sub 1344 X.inv.sp (by decide) (by decide) (by decide) (by decide) (by decide)
  have e608 (j : Nat) (hj : j ≤ 32) : v.getReg .x11 + BitVec.ofNat 64 j =
      s.getReg .x2 - BitVec.ofNat 64 (608 - j) := by
    rw [X.x11]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj]
  have pp0 : partPtr v 0 = v.getMem (s.getReg .x2 - 1256) := by
    simp only [partPtr]; rw [e608 _ (by omega)]; exact X.slice0
  have pl0 : partLen v 0 = (logBc s).toNat := by
    simp only [partLen]
    rw [BitVec.add_assoc, show BitVec.ofNat 64 (16 * 0) + 8 = BitVec.ofNat 64 8 from rfl,
      e608 _ (by omega)]
    exact congrArg BitVec.toNat X.slice0Len
  have pp1 : partPtr v 1 = vecPtr v (s.getReg .x2 - 912) := by
    simp only [partPtr]; rw [e608 _ (by omega)]; exact X.slice1
  have pl1 : partLen v 1 = (vecLen v (s.getReg .x2 - 912)).toNat := by
    simp only [partLen]
    rw [BitVec.add_assoc, show BitVec.ofNat 64 (16 * 1) + 8 = BitVec.ofNat 64 24 from rfl,
      e608 _ (by omega)]
    exact congrArg BitVec.toNat X.slice1Len
  have hP := X.point
  have hA := X.kept.alphas
  have hlb : (logBc s).toNat ≤ (v.getMem (s.getReg .x2 - 1144)).toNat := by
    have := X.lb
    rw [← hP.elems, eListAt_length] at this
    exact this
  have hpl := hP.le
  have hal := hA.vec.len
  have hbP : NewBuf s v (v.getMem (s.getReg .x2 - 1256))
      ((v.getMem (s.getReg .x2 - 1320)).toNat * 24) 8 := hP.buf
  have pre : SliceConcatPre v := {
    heap := X.inv.heap
    out := X.x10 ▸ o1
    count := by rw [X.x12]; decide
    slices := by rw [X.x11, X.x12]; exact p1
    stack := hst
    outFree := X.x10 ▸ o2
    outStack := X.x10 ▸ o3
    slicesFree := by rw [X.x11, X.x12]; exact p2
    slicesStack := by rw [X.x11, X.x12]; exact p3
    slicesOut := by rw [X.x11, X.x12, X.x10]; addr_omega [hb1]
    part := by
      intro i hi
      rw [X.x12] at hi
      have hi2 : i < 2 := hi
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · rw [pp0, pl0, X.x10]
        exact bufPart hpre X.inv hbP (hlb.trans hpl) (by decide) (k := 768) (by omega)
      · rw [pp1, pl1, X.x10]
        exact bufPart hpre X.inv hA.buf hal (by decide) (k := 768) (by omega) }
  obtain ⟨w, hrw, ⟨hpcw, hpw, post⟩ | hd⟩ := hC.call (Reaches.refl v) hpc pre
  swap
  · exact ⟨w, hrw, Or.inr hd⟩
  have hx := hpre.stack.next
  rw [stackLo_eq] at hx
  have hsl : stackLo v sliceConcatStack = s.getReg .x2 - BitVec.ofNat 64 (1344 + 224) := by
    simp only [stackLo, X.inv.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have fr : DFrame v w fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 768) 24 ∨
      Within a (s.getReg .x2 - 4544) 3200 ∨ Within a nextAddr 8 ∨ Fresh v w a :=
    post.frame.mono fun a ha ↦ by
      rcases ha with ha | ha | ha
      · exact Or.inl (by rw [X.x10] at ha; exact ha)
      · rw [hsl] at ha; exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
      · exact Or.inr (Or.inr ha)
  have st : StepS s v w (Within · (s.getReg .x2 - BitVec.ofNat 64 768) 24) :=
    ⟨fr, post.heap, post.mono, hpw .x2 (by decide)⟩
  have hval := post.value
  have hparts : parts v = [state.point.take (logBc s).toNat, k.alphas] := by
    simp only [parts, X.x12]
    show [eListAt v (partPtr v 0) (partLen v 0), eListAt v (partPtr v 1) (partLen v 1)] = _
    rw [pp0, pl0, pp1, pl1, eListAt_take _ _ (hlb.trans (Nat.le_refl _)), hP.elems]
    exact congrArg (fun x ↦ [_, x]) hA.elems
  rw [hparts, X.x10] at hval
  refine ⟨w, hrw, Or.inl ⟨by rw [hpcw, returnAddress_eq, X.x1]; decide, hpw,
    X.inv.afterR hpre (frameW_slot hpre (by omega) (by omega)) st.toR, st, ?_⟩⟩
  simpa using hval.widen X.inv.mono

/-! ## `Bytecode::evaluate` -/

/-- The `Bytecode` as `evaluate` reads it, from the entry's to a state past the prologue: what
`BcOk` says at the entry holds there for `evaluate`'s stack below the frame, and `bev` reads the
same. -/
def BcTransfer (BcOk : MachineState → Nat → Word → Prop)
    (bev : MachineState → Word → List E → Option E) : Prop :=
  ∀ s u, BusBalancePre s → BcOk s busBalanceStack (bytecodeOf s (s.getReg .x11)) → Inv s u →
    BcOk u Vbb.bytecodeEvalStack (bytecodeOf s (s.getReg .x11)) ∧
      bev u (bytecodeOf s (s.getReg .x11)) = bev s (bytecodeOf s (s.getReg .x11))

/-- At `0x80007170`, past `evaluate`: `bytecode_point` at `S - 768`, the bytecode's value `bv` at
`S - 744`, the rest a pure result. -/
structure Evaluated (bev : MachineState → Word → List E → Option E) (s y : MachineState)
    (k : Start) (state : GkrState) (mem : List E) (mf bf bv : E) : Prop where
  inv : Inv s y
  kept : Kept s y k
  claims : ClaimsOk s y (y.getMem (s.getReg .x2 - 840)) (y.getMem (s.getReg .x2 - 832))
    (y.getMem (s.getReg .x2 - 824)) (allClaims s state mem mf bf)
  len : y.getMem (s.getReg .x2 - 824) = 5
  x8 : y.getReg .x8 = y.getMem (s.getReg .x2 - 1128)
  x20 : y.getReg .x20 = s.getReg .x12
  x21 : y.getReg .x21 = s.getReg .x10
  x23 : y.getReg .x23 = logBc s
  x24 : y.getReg .x24 = logMem s
  x27 : y.getReg .x27 = y.getMem (s.getReg .x2 - 1256)
  memLen : 3 ≤ mem.length
  bcPoint : NewVecE s y (s.getReg .x2 - 768) (state.point.take (logBc s).toNat ++ k.alphas)
  bcValue : eAt y (s.getReg .x2 - 744) = bv
  memIndex : eAt y (s.getReg .x2 - 816) = indexMleRust (state.point.take (logMem s).toNat)
  bcIndex : eAt y (s.getReg .x2 - 792) = indexMleRust (state.point.take (logBc s).toNat)
  memory : NewVecE s y (s.getReg .x2 - 864) mem
  values : NewVecE s y (s.getReg .x2 - 176) state.values
  point : NewVecR s y (y.getMem (s.getReg .x2 - 1320)) (y.getMem (s.getReg .x2 - 1256))
    (y.getMem (s.getReg .x2 - 1144)) state.point
  valuesPtr : y.getMem (s.getReg .x2 - 1280) = vecPtr y (s.getReg .x2 - 176)
  pushPtr : y.getMem (s.getReg .x2 - 1272) = vecPtr s (s.getReg .x11 + 24)
  lm : (logMem s).toNat ≤ state.point.length
  lb : (logBc s).toNat ≤ state.point.length
  mfEq : mf = eOf3 (y.getReg .x25) (y.getReg .x22) (y.getMem (s.getReg .x2 - 1112))
  bfEq : bf = eOf3 (y.getReg .x26) (y.getMem (s.getReg .x2 - 1120))
    (y.getMem (s.getReg .x2 - 1128))
  tracks : Tracks (prog bev s) (s.getReg .x12) s y (pure (restValue s k state mem mf bf bv))

/-- What the steps from `concat`'s entry to `0x80007170` write in the frame. -/
def EvalW (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 768) 24 ∨ Within a (s.getReg .x2 - 608) 32 ∨
    Within a (s.getReg .x2 - 744) 24

theorem EvalW.frameW {s : MachineState} (hpre : BusBalancePre s) : FrameW s (EvalW s) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  intro a ha
  rcases ha with ha | ha | ha <;> addr_omega [ha, hb1]

theorem EvalW.free {s : MachineState} (hpre : BusBalancePre s) {a : Word} (ha : EvalW s a) :
    Free s a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
  rcases ha with ha | ha | ha <;> addr_omega [ha, hb1]

theorem evalStage (hC : SliceConcatSpec) {BcOk : MachineState → Nat → Word → Prop}
    {bev : MachineState → Word → List E → Option E} (hB : Vbb.BytecodeEvalSpec BcOk bev)
    (hBT : BcTransfer BcOk bev) {s v : MachineState} {k : Start} {state : GkrState}
    {mem : List E} {mf bf : E} (hpre : BusBalancePre s)
    (hbc : BcOk s busBalanceStack (bytecodeOf s (s.getReg .x11)))
    (X : Indexed bev s v k state mem mf bf) (hpc : v.pc = 0x8000cfc4) :
    ∃ y, Reaches Image.code v y ∧ (Done bev s y ∨ Dead Image.code y ∨
      (y.pc = 0x80007170 ∧ ∃ bv, Evaluated bev s y k state mem mf bf bv)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  obtain ⟨w, hrw, ⟨hpcw, hpw, I₀, st₀, BP⟩ | hd⟩ := concatCall hC hpre X hpc
  swap
  · exact ⟨w, hrw, Or.inr (Or.inl hd)⟩
  have sp₀ := I₀.sp
  have x20w : w.getReg .x20 = s.getReg .x12 := (hpw .x20 (by decide)).trans X.x20
  have hS := hpre.self.self
  have hck : extractByte (w.getMem (s.getReg .x12 + 360)) 0 ≠ 0 := by
    have hc := hpre.checked
    rwa [← Transcript.add_ofNat_zero (s.getReg .x12 + 360),
      Runtime.byteAt_add (by addr_omega [hS]) (by decide), ← I₀.checkedWord hpre] at hc
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800070b0_spec hpcw (by
    rv_eval [x20w]
    exact ⟨by addr_omega [hS], Mapped.valid hS.1 (i := 360) (by decide)⟩)
  have k₁ := b800070b0_keeps h₁
  have m₁ := b800070b0_mem_same h₁
  have pc₁ : u₁.pc = 0x800070b8 := Sym.Expect.Holds.pc_eq h₁ (by
    rv_eval [x20w]
    exact ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hck (by
      have := congrArg BitVec.toNat (beq_iff_eq.mp h)
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth] at this
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))] at this
      simpa using this)))
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 1344 := (k₁ .x2 (by decide)).trans sp₀
  have K₀ : Kept s w k := X.kept.step hpre (st₀.toR.weaken fun a ha ↦
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1])))))))
  have hlay' : u₁.getMem (s.getReg .x2 - 1240) = s.getReg .x11 := by rw [m₁]; exact K₀.layout
  have hlay : u₁.getMem (u₁.getReg .x2 + 104) = s.getReg .x11 := by
    rw [sp₁, show s.getReg .x2 - 1344 + 104 = s.getReg .x2 - 1240 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
    exact hlay'
  have hl := hpre.layout
  have hR : Region (s.getReg .x11) 168 := by
    rcases hl.region with h0 | h0
    · exact absurd h0 (by decide)
    · exact h0
  have hR' := hR
  simp only [Region, Mapped] at hR'
  have hbcw : u₁.getMem (s.getReg .x11 + 144) = bytecodeOf s (s.getReg .x11) := by
    rw [m₁]; exact I₀.word hl (by addr_omega [hR']) (by addr_omega [hR'])
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800070b8_spec pc₁ (by
    rv_eval [sp₁, hlay']
    and_intros <;> first
      | valid_access hval [hb1]
      | exact Region.valid hR (by addr_omega [hR']) (by addr_omega [hR']) (by addr_omega [hR']))
  have k₂ := b800070b8_keeps h₂
  have m₂ := b800070b8_mem_same h₂
  have sp₂ : u₂.getReg .x2 = s.getReg .x2 - 1344 := (k₂ .x2 (by decide)).trans sp₁
  have mw (a : Word) : u₂.getMem a = w.getMem a := by rw [m₂, m₁]
  have I₂ : Inv s u₂ := I₀.same mw (sp₂.trans sp₀.symm)
  have BP₂ : NewVecE s u₂ (s.getReg .x2 - 768) (state.point.take (logBc s).toNat ++ k.alphas) :=
    BP.keepR hpre (StepR.same mw I₀.heap (sp₂.trans sp₀.symm)) (A := fun _ ↦ False)
      (fun _ h ↦ h.elim) (by addr_omega [hb1]) fun _ _ h ↦ h
  have x10₂ : u₂.getReg .x10 = s.getReg .x2 - 608 := by
    rw [b800070b8_x10 h₂, sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x11₂ : u₂.getReg .x11 = bytecodeOf s (s.getReg .x11) := by
    rw [b800070b8_x11 h₂, hlay, hbcw]
  have x12₂ : u₂.getReg .x12 = vecPtr u₂ (s.getReg .x2 - 768) := by
    rw [b800070b8_x12 h₂, sp₁, vecPtr, mw, m₁]
    exact congrArg w.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have x13₂ : u₂.getReg .x13 = vecLen u₂ (s.getReg .x2 - 768) := by
    rw [b800070b8_x13 h₂, sp₁, vecLen, mw, m₁]
    exact congrArg w.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have hlen : (vecLen u₂ (s.getReg .x2 - 768)).toNat = (logBc s).toNat + 4 := by
    have he := congrArg List.length BP₂.elems
    rw [vecEs, eListAt_length, List.length_append, List.length_take, k.alphasLen,
      Nat.min_eq_left X.lb] at he
    exact he
  obtain ⟨hBc, hbev⟩ := hBT s u₂ hpre hbc I₂
  obtain ⟨o1, o2, o3⟩ := frameSlot (m := Vbb.bytecodeEvalStack) hpre I₂ (n := 32) (k := 608)
    (by omega) (by omega) (by omega) (by decide)
  have hst : RtStack u₂ Vbb.bytecodeEvalStack :=
    hpre.stack.sub 1344 sp₂ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsl : stackLo u₂ Vbb.bytecodeEvalStack = s.getReg .x2 - BitVec.ofNat 64 (1344 + 3200) := by
    simp only [stackLo, sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hr4 := hpre.stack.rodata
  have hrb : rodataBase.toNat = 2684354560 := rfl
  rw [stackLo_eq] at hr4
  obtain ⟨PR, PO, PA1, PA2⟩ : Region (vecPtr u₂ (s.getReg .x2 - 768))
      (24 * (vecLen u₂ (s.getReg .x2 - 768)).toNat) ∧
      Outside u₂ (vecPtr u₂ (s.getReg .x2 - 768)) (24 * (vecLen u₂ (s.getReg .x2 - 768)).toNat) ∧
      Apart (vecPtr u₂ (s.getReg .x2 - 768)) (24 * (vecLen u₂ (s.getReg .x2 - 768)).toNat)
        (stackLo u₂ Vbb.bytecodeEvalStack) Vbb.bytecodeEvalStack ∧
      Apart (vecPtr u₂ (s.getReg .x2 - 768)) (24 * (vecLen u₂ (s.getReg .x2 - 768)).toNat)
        (s.getReg .x2 - BitVec.ofNat 64 608) 32 := by
    rcases bufPart hpre I₂ BP₂.buf BP₂.vec.len (m := Vbb.bytecodeEvalStack) (by decide)
      (k := 608) (l := 32) (by omega) with h0 | h0
    · omega
    · exact h0
  have pre : Vbb.BytecodeEvalPre BcOk u₂ := {
    heap := I₂.heap
    stack := hst
    rodata := I₂.rodata hpre
    out := x10₂ ▸ o1
    outFree := x10₂ ▸ o2
    outStack := x10₂ ▸ o3
    outRodata := by rw [x10₂]; addr_omega [hr4, hrb, hb1]
    bytecode := x11₂ ▸ hBc
    point := by
      rw [x12₂, x13₂]
      refine ⟨regionRange PR (Nat.le_refl _) (by omega) PR.2, PO, PA1⟩
    pointOut := by rw [x12₂, x13₂, x10₂]; exact PA2 }
  obtain ⟨t, hrt, ⟨hpct, hpt, post⟩ | hd⟩ := hB.call (Reaches.refl u₂) (b800070b8_pc h₂) pre
  swap
  · exact ⟨t, hrw.trans (hr₁.trans (hr₂.trans hrt)), Or.inr (Or.inl hd)⟩
  have hr₀₂ := hrw.trans (hr₁.trans hr₂)
  have hx := hpre.stack.next
  rw [stackLo_eq] at hx
  have frt : DFrame u₂ t fun a ↦ Within a (s.getReg .x2 - 608) 32 ∨
      Within a (s.getReg .x2 - 4544) 3200 ∨ Within a nextAddr 8 ∨ Fresh u₂ t a :=
    post.frame.mono fun a ha ↦ by
      rcases ha with ha | ha | ha
      · exact Or.inl (by rw [x10₂] at ha; exact ha)
      · rw [hsl] at ha; exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
      · exact Or.inr (Or.inr ha)
  have stt : StepS s u₂ t (Within · (s.getReg .x2 - 608) 32) :=
    ⟨frt, post.heap, post.mono, hpt .x2 (by decide)⟩
  have f608 : FrameW s (Within · (s.getReg .x2 - 608) 32) := fun a ha ↦ by addr_omega [ha, hb1]
  have It : Inv s t := I₂.afterR hpre f608 stt.toR
  have spt : t.getReg .x2 = s.getReg .x2 - 1344 := It.sp
  have hpct' : t.pc = 0x800070d4 := by rw [hpct, returnAddress_eq, b800070b8_x1 h₂]; decide
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800070d4_spec hpct' (by
    rv_eval [spt]
    and_intros <;> valid_access hval [hb1])
  have k₃ := b800070d4_keeps h₃
  have m₃ := b800070d4_mem_same h₃
  have I₃ : Inv s u₃ := It.same m₃ (k₃ .x2 (by decide))
  have hv := post.value
  have hpt0 : eListAt u₂ (u₂.getReg .x12) (u₂.getReg .x13).toNat =
      state.point.take (logBc s).toNat ++ k.alphas := by
    rw [x12₂, x13₂]; exact BP₂.elems
  rw [hpt0, x11₂, hbev, x10₂] at hv
  have htr := X.tracks
  rw [rest, tailRest_eq] at htr
  have rg (r : Reg) (hr : r ∈ ([.x8, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg)) :
      u₃.getReg r = v.getReg r := by
    rw [k₃ r (mem_of_mem hr _), hpt r (by unfold calleeSaved; exact mem_of_mem hr _),
      k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _),
      hpw r (by unfold calleeSaved; exact mem_of_mem hr _)]
  have e736 : t.getReg .x2 + 736 = s.getReg .x2 - 608 := by
    rw [spt]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  rcases hbv : bev s (bytecodeOf s (s.getReg .x11)) (state.point.take (logBc s).toNat ++ k.alphas)
    with _ | bv
  · -- `Err`: through `s5`
    rw [hbv] at hv
    have pc₃ := b800070d4_pc_not_taken h₃ (by rw [e736]; exact hv)
    have ho := hpre.out
    have x21₃ : u₃.getReg .x21 = s.getReg .x10 := (rg .x21 (by decide)).trans X.x21
    obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800070e4_spec pc₃ (by
      rv_eval [x21₃]
      and_intros <;> exact Region.valid ho (by addr_omega [ho]) (by addr_omega [ho])
        (by addr_omega [ho]))
    have fr₄ := b800070e4_frame h₄ (by rw [x21₃]; addr_omega [ho])
    rw [x21₃] at fr₄
    have cap₄ := b800070e4_m_x21_0 h₄
    rw [x21₃] at cap₄
    have hnone : ∀ T, TranscriptAt s (s.getReg .x12) T → (prog bev s).run T = none :=
      htr.fail fun _ _ ↦ by
        rw [show bev s (bytecodeOf s (s.getReg .x11))
          (state.point.take (busLayoutAt s (s.getReg .x11)).logBytecode ++ k.alphas) = none
          from hbv]
        rfl
    obtain ⟨t', hrt', hdone⟩ := errDoneAt' (bev := bev) hpre I₃ (by omega) fr₄
      ((b800070e4_keeps h₄) .x2 (by decide)) (b800070e4_pc h₄) cap₄ hnone
    exact ⟨t', hr₀₂.trans (hrt.trans (hr₃.trans (hr₄.trans hrt'))), Or.inl hdone⟩
  rw [hbv] at hv
  obtain ⟨hv0, hv1⟩ := hv
  have pc₃ := b800070d4_pc_taken h₃ (by rw [e736]; exact hv0)
  have sp₃ : u₃.getReg .x2 = s.getReg .x2 - 1344 := I₃.sp
  obtain ⟨y, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80007160_spec pc₃ (by
    rv_eval [sp₃]
    and_intros <;> valid_access hval [hb1])
  have k₄ := b80007160_keeps h₄
  have fr₄ : DFrame u₃ y (Within · (s.getReg .x2 - 744) 24) :=
    (DFrame.of_memFrame (b80007160_frame h₄ (by rw [sp₃]; addr_omega [hb1]))).mono
      fun a ha ↦ by rw [sp₃] at ha; addr_omega [ha, hb1]
  have st₄ : StepS s u₃ y (Within · (s.getReg .x2 - 744) 24) :=
    StepS.ofDFrame I₃.heap fr₄ (fun _ h ↦ h) (fun i hi hw ↦ by addr_omega [hw, hi, hb1])
      (k₄ .x2 (by decide))
  have I₄ : Inv s y := I₃.afterR hpre (fun a ha ↦ by addr_omega [ha, hb1]) st₄.toR
  have st : StepS s v y (EvalW s) :=
    ((((st₀.trans (StepS.same mw I₀.heap (sp₂.trans sp₀.symm))).trans stt).trans
      (StepS.same m₃ It.heap (k₃ .x2 (by decide)))).trans st₄).weaken fun a ha ↦ by
        rcases ha with ((((ha | ha) | ha) | ha) | ha)
        · exact Or.inl (by addr_omega [ha, hb1])
        · exact False.elim ha
        · exact Or.inr (Or.inl ha)
        · exact False.elim ha
        · exact Or.inr (Or.inr ha)
  have fT := EvalW.frameW hpre
  have K1 (x : Word) (hx : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2 - 768).toNat) : y.getMem x = v.getMem x :=
    st.slot hpre (fun z hz h' ↦ by
      rcases h' with h' | h' | h' <;> addr_omega [hz, h', hx, hb1]) (by
      constructor <;> addr_omega [hb1, hx])
  have rgy (r : Reg) (hr : r ∈ ([.x8, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg)) :
      y.getReg r = v.getReg r := by
    rw [k₄ r (mem_of_mem hr _), rg r hr]
  have hm3 (a : Word) : u₃.getMem a = t.getMem a := m₃ a
  have y0 : y.getMem (s.getReg .x2 - 744) = t.getMem (s.getReg .x2 - 608 + 8) := by
    rw [show s.getReg .x2 - 744 = u₃.getReg .x2 + 600 by
      rw [sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1], b80007160_m_x2_600 h₄,
      b800070d4_x11 h₃, spt]
    exact congrArg t.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have y8 : y.getMem (s.getReg .x2 - 744 + 8) = t.getMem (s.getReg .x2 - 608 + 8 + 8) := by
    rw [show s.getReg .x2 - 744 + 8 = u₃.getReg .x2 + 608 by
      rw [sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1], b80007160_m_x2_608 h₄,
      b800070d4_x10 h₃, spt]
    exact congrArg t.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have y16 : y.getMem (s.getReg .x2 - 744 + 16) = t.getMem (s.getReg .x2 - 608 + 8 + 16) := by
    rw [show s.getReg .x2 - 744 + 16 = u₃.getReg .x2 + 616 by
      rw [sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1], b80007160_m_x2_616 h₄, hm3, sp₃]
    exact congrArg t.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have stB : StepR s u₂ y fun a ↦ (Within a (s.getReg .x2 - 608) 32 ∨ False) ∨
      Within a (s.getReg .x2 - 744) 24 :=
    ((stt.trans (StepS.same m₃ It.heap (k₃ .x2 (by decide)))).trans st₄).toR
  have fB : FrameW s fun a ↦ (Within a (s.getReg .x2 - 608) 32 ∨ False) ∨
      Within a (s.getReg .x2 - 744) 24 := fun a ha ↦ by
    rcases ha with (ha | ha) | ha
    · addr_omega [ha, hb1]
    · exact ha.elim
    · addr_omega [ha, hb1]
  refine ⟨y, hr₀₂.trans (hrt.trans (hr₃.trans hr₄)), Or.inr (Or.inr ⟨b80007160_pc h₄, bv, {
    inv := I₄
    kept := X.kept.step hpre (st.toR.weaken fun _ ha ↦ EvalW.free hpre ha)
    claims := by
      rw [K1 _ (by constructor <;> addr_omega [hb1]), K1 _ (by constructor <;> addr_omega [hb1]),
        K1 _ (by constructor <;> addr_omega [hb1])]
      exact X.claims.keepR hpre st.toR fT
    len := by rw [K1 _ (by constructor <;> addr_omega [hb1])]; exact X.len
    x8 := by rw [rgy .x8 (by decide), K1 _ (by constructor <;> addr_omega [hb1])]; exact X.x8
    x20 := by rw [rgy .x20 (by decide)]; exact X.x20
    x21 := by rw [rgy .x21 (by decide)]; exact X.x21
    x23 := by rw [rgy .x23 (by decide)]; exact X.x23
    x24 := by rw [rgy .x24 (by decide)]; exact X.x24
    x27 := by rw [rgy .x27 (by decide), K1 _ (by constructor <;> addr_omega [hb1])]; exact X.x27
    memLen := X.memLen
    bcPoint := BP₂.keepR hpre stB fB (by addr_omega [hb1]) fun z hz h' ↦ by
      rcases h' with (h' | h') | h'
      · addr_omega [hz, h', hb1]
      · exact h'
      · addr_omega [hz, h', hb1]
    bcValue := by
      rw [← hv1]
      exact eAt_congr y0 y8 y16
    memIndex := by
      rw [st.eSlot hpre (fun z hz h' ↦ by rcases h' with h' | h' | h' <;> addr_omega [hz, h', hb1])
        (by constructor <;> addr_omega [hb1])]
      exact X.memIndex
    bcIndex := by
      rw [st.eSlot hpre (fun z hz h' ↦ by rcases h' with h' | h' | h' <;> addr_omega [hz, h', hb1])
        (by constructor <;> addr_omega [hb1])]
      exact X.bcIndex
    memory := X.memory.keepR hpre st.toR fT (by addr_omega [hb1]) fun z hz h' ↦ by
      rcases h' with h' | h' | h' <;> addr_omega [hz, h', hb1]
    values := X.values.keepR hpre st.toR fT (by addr_omega [hb1]) fun z hz h' ↦ by
      rcases h' with h' | h' | h' <;> addr_omega [hz, h', hb1]
    point := by
      rw [K1 _ (by constructor <;> addr_omega [hb1]), K1 _ (by constructor <;> addr_omega [hb1]),
        K1 _ (by constructor <;> addr_omega [hb1])]
      exact X.point.keepR hpre st.toR fT
    valuesPtr := by
      rw [K1 _ (by constructor <;> addr_omega [hb1]), X.valuesPtr, vecPtr, vecPtr,
        st.slot hpre (fun z hz h' ↦ by rcases h' with h' | h' | h' <;> addr_omega [hz, h', hb1])
          (by constructor <;> addr_omega [hb1])]
    pushPtr := by rw [K1 _ (by constructor <;> addr_omega [hb1])]; exact X.pushPtr
    lm := X.lm
    lb := X.lb
    mfEq := by
      rw [rgy .x25 (by decide), rgy .x22 (by decide), K1 _ (by constructor <;> addr_omega [hb1])]
      exact X.mfEq
    bfEq := by
      rw [rgy .x26 (by decide), K1 _ (by constructor <;> addr_omega [hb1]),
        K1 _ (by constructor <;> addr_omega [hb1])]
      exact X.bfEq
    tracks := htr.bind fun T hT ↦ ⟨T, by
      rw [show bev s (bytecodeOf s (s.getReg .x11))
        (state.point.take (busLayoutAt s (s.getReg .x11)).logBytecode ++ k.alphas) = some bv
        from hbv]
      rfl, st.transcript hpre X.inv fT hT⟩ }⟩)⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
