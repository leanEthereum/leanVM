import Rv64Verifier.Proofs.Gkr.KeccakWeights

/-!
# `keccak::verify_keccak`: the last segment's value

`eq_kernel(&segment)` into `f + 416` (`to_eqseg`), the bounds checks, `dot(&lanes[..25], output)`
into `f + 1952` and its product with `eq_kernel(&segment)[1]` into `f + 152` (`to_last`).
-/

namespace Rv64Verifier.Gkr.Keccak
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F35 Rv64Verifier.MultilinearContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- The weights in their buffer `wp`, allocated since the entry. -/
structure WB (s u : MachineState) (wp : Word) (lp : List E) : Prop where
  x8 : u.getReg .x8 = wp
  x20 : u.getReg .x20 = 1600
  x26 : u.getReg .x26 = 1600
  wbuf : NewBuf s u wp 38400 8
  weights : eListAt u wp 1600 = kWeights (eqKernelRust lp)

theorem WB.step {s u v : MachineState} {wp : Word} {lp : List E} (hpre : VerifyKeccakPre s)
    (B : Base s u) (W : WB s u wp lp) (hN : heapNext u ≤ heapNext v)
    {rs : List (Nat × Nat)} {sp : Bool} (hok : SlotsOk rs = true)
    (F : DFrame u v (SW s u v rs sp))
    (hregs : ∀ r ∈ ([.x8, .x20, .x26] : List Reg), v.getReg r = u.getReg r) : WB s v wp lp := by
  have hw := W.wbuf
  simp only [NewBuf] at hw
  exact {
    x8 := (hregs .x8 (by decide)).trans W.x8
    x20 := (hregs .x20 (by decide)).trans W.x20
    x26 := (hregs .x26 (by decide)).trans W.x26
    wbuf := by simp only [NewBuf]; omega
    weights := by
      rw [← W.weights]
      exact F.eListAt ((SW.buf hpre B hok W.wbuf).bytes (Nat.le_refl _) (by omega)
        (by have := B.heap.hi; unfold heapEnd at this; omega)) }

/-- Back from `eq_kernel(&segment)`: its weights at `f + 416`. -/
structure A7 (s u : MachineState) (seg lp : List E) (wp : Word) : Prop extends M s u seg where
  pc : u.pc = 0x800090b0
  wb : WB s u wp lp
  x18 : u.getReg .x18 = s.getReg .x12
  x19 : u.getReg .x19 = 12
  x21 : u.getReg .x21 = 32
  x25 : u.getReg .x25 = vecPtr u (s.getReg .x2 - 5120)
  lanesV : NewVecE s u (s.getReg .x2 - 5120) (eqKernelRust lp)
  eqsegV : NewVecE s u (s.getReg .x2 - 4832) (eqKernelRust seg)
  lpLen : lp.length = 5
  rest : Rest s u (kLanes (s.getReg .x12).toNat (instOf s) (outOf s) seg lp)

theorem regs_mem {l : List Reg} (hl : l.all (fun r ↦ decide (r ∈ calleeSaved)) = true) {r : Reg}
    (hr : r ∈ l) : r ∈ calleeSaved := by
  have := List.all_eq_true.mp hl r hr
  simpa using this

theorem to_eqseg (hEK : EqKernelSpec) {s u : MachineState} {seg lp : List E}
    (hpre : VerifyKeccakPre s) (A : A6 s u seg lp) : ∃ v, Reaches Image.code u v ∧
      (A7 s v seg lp (u.getMem (s.getReg .x2 - 4824)) ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have B := A.base
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80009098_spec A.pc (by
    rv_eval [B.x2]
    valid_access hpre.stack.valid [hb])
  have k₁ := b80009098_keeps h₁
  have m₁ := b80009098_mem_same h₁
  have B₁ := B.same ((k₁ .x2 (by decide)).trans B.x2) m₁
  have hN₁ : heapNext u₁ = heapNext u := by simp only [heapNext, m₁]
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 4832 := by
    rw [b80009098_x10 h₁, B.x2]; exact BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have x11₁ : u₁.getReg .x11 = vecPtr u (s.getReg .x2 - 5168) := by rw [b80009098_x11 h₁, A.x23]
  have x12₁ : u₁.getReg .x12 = vecLen u (s.getReg .x2 - 5168) := by rw [b80009098_x12 h₁, A.x24]
  have hlen : (vecLen u (s.getReg .x2 - 5168)).toNat = 1 := by
    have := A.segLen; rw [← A.segV.elems] at this; simpa only [vecEs, eListAt_length] using this
  have H : Heaped s u (vecPtr u (s.getReg .x2 - 5168)) (24 * 1) := by
    rcases vec_heaped hpre B A.segV with h0 | H
    · omega
    · rw [hlen] at H; exact H
  have hab := hpre.stack.above
  have hrs := hpre.stack.rodata
  unfold verifyKeccakStack at hb hab hrs
  have hek : EqKernelPre u₁ := {
    heap := B₁.heap
    out := by rw [x10₁]; addr_omega [hb, hsm]
    point := by rw [x11₁, x12₁, hlen]; exact Or.inr H.region
    stack := hpre.stack.sub 5248 B₁.x2 (by unfold verifyKeccakStack; decide) (by decide)
      (by decide) (by decide) (by decide)
    outFree := by
      rw [x10₁]; have hnx := hpre.stack.next; unfold verifyKeccakStack at hnx
      refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    pointFree := by
      rw [x11₁, x12₁, hlen]; right
      exact Open.outside_mono H.outside (le_of_eq hN₁.symm)
    outStack := by rw [x10₁]; simp only [stackLo, B₁.x2]; addr_omega [hb]
    pointStack := by
      rw [x11₁, x12₁, hlen]; simp only [stackLo, B₁.x2]
      exact H.above _ _ (by addr_omega [hb, hab])
    pointOut := by rw [x11₁, x12₁, hlen, x10₁]; exact H.above _ _ (by addr_omega [hb, hab])
    rodata := B₁.rodata hpre
    outRodata := by rw [x10₁]; addr_omega [hb, hrs] }
  obtain ⟨v, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ := hEK.call hr₁ (b80009098_pc h₁) hek
  swap
  · exact ⟨v, hr₂, Or.inr hd⟩
  have x2₂ : v.getReg .x2 = s.getReg .x2 - 5248 := (hpres₂.reg .x2).trans B₁.x2
  have F₂ : DFrame u₁ v (SW s u₁ v [(4832, 24)] false) := DFrame.mono hpost₂.frame
    fun a ha ↦ cframe_sw hpre 4832 B₁.x2 x10₁ (by decide) a ha
  have M₁ : M s u₁ seg := A.toM.step hpre B₁.x2 B₁.heap (le_of_eq hN₁.symm) (rs := [])
    (sp := false) (by decide) (by decide) (DFrame.of_same m₁ _)
  have M₂ := M₁.step hpre x2₂ hpost₂.heap hpost₂.mono (by decide) (by decide) F₂
  have kv (J : Nat) (hJ : J ≤ 5248) (h24 : 24 ≤ J) (hsep : SlotsSep [(4832, 24)] J 24 = true)
      {xs : List E} (h : NewVecE s u₁ (s.getReg .x2 - BitVec.ofNat 64 J) xs) :=
    SW.vec hpre B₁ hpost₂.heap hpost₂.mono (by decide) hJ h24 hsep F₂ h
  have km (J : Nat) (hJ : J ≤ 5248) (h8 : 8 ≤ J) (hsep : SlotsSep [(4832, 24)] J 8 = true) :=
    SW.mem hpre hpost₂.heap (by decide) hJ h8 hsep F₂
  have hreg (r : Reg) (hr : r ∈ calleeSaved)
      (h1 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x13, .x14, .x15, .x16, .x17, .x18, .x19,
        .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg)) :
      v.getReg r = u.getReg r := (hpres₂.reg r hr).trans (k₁ r h1)
  have hval := hpost₂.value
  have hel : eListAt u₁ (u₁.getReg .x11) (u₁.getReg .x12).toNat = seg := by
    rw [x11₁, x12₁, ← A.segV.elems, vecEs]
    exact (DFrame.of_same m₁ (fun _ ↦ False)).eListAt fun _ _ h ↦ h
  rw [hel, x10₁] at hval
  have hwb := A.wbuf
  simp only [NewBuf] at hwb
  have WB₁ : WB s u₁ (u.getMem (s.getReg .x2 - 4824)) lp := {
    x8 := (k₁ .x8 (by decide)).trans A.x8
    x20 := by rw [b80009098_x20 h₁, B.x2]; exact A.cap.symm.trans (by
      congr 1; exact BitVec.eq_of_toNat_eq (by addr_omega [hb])) |>.symm
    x26 := (k₁ .x26 (by decide)).trans A.x26
    wbuf := by simp only [NewBuf, hN₁]; exact hwb
    weights := by
      rw [← A.weights]
      exact (DFrame.of_same m₁ (fun _ ↦ False)).eListAt fun _ _ h ↦ h }
  refine ⟨v, hr₂, Or.inl { M₂ with
    pc := by rw [hpc₂, returnAddress_eq, b80009098_x1 h₁]; decide
    wb := WB₁.step hpre B₁ hpost₂.mono (by decide) F₂ fun r hr ↦
      hpres₂.reg r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                       rcases hr with rfl | rfl | rfl <;> decide)
    x18 := (hreg .x18 (by decide) (by decide)).trans A.x18
    x19 := (hreg .x19 (by decide) (by decide)).trans A.x19
    x21 := (hreg .x21 (by decide) (by decide)).trans A.x21
    x25 := by
      rw [hreg .x25 (by decide) (by decide), A.x25]; simp only [vecPtr]
      rw [show s.getReg .x2 - 5120 + 8 = s.getReg .x2 - 5112 from
        BitVec.eq_of_toNat_eq (by addr_omega [hb])]
      exact ((km 5112 (by decide) (by decide) (by decide)).trans (m₁ _)).symm
    lanesV := kv 5120 (by decide) (by decide) (by decide) (Layer.newVecE_congr m₁ A.lanesV)
    eqsegV := Open.newVecE_mono hval B₁.mono
    lpLen := A.lpLen
    rest := (A.rest.keep fun T hT ↦ Layer.transcriptAt_congr m₁ hT).keep fun T hT ↦
      SW.tat hpre B₁ hpost₂.heap hpost₂.mono (by decide) F₂ hT }⟩

theorem eListAt_take (u : MachineState) (p : Word) {k n : Nat} (h : k ≤ n) :
    (eListAt u p n).take k = eListAt u p k := by
  apply List.ext_getElem (by simp [eListAt_length, h])
  intro i h1 h2
  simp only [List.getElem_take, eListAt_getElem]

/-- `eq_kernel(&segment)[1] * dot(&lanes[..25], output)`. -/
def lastOf (s : MachineState) (seg lp : List E) : E :=
  (eqKernelRust seg).getD 1 0 * dotRust ((eqKernelRust lp).take 25) (outOf s)

/-- The last segment's value at `f + 152`. -/
structure A9 (s u : MachineState) (seg lp : List E) (wp : Word) : Prop extends M s u seg where
  pc : u.pc = 0x80009110
  wb : WB s u wp lp
  x9 : u.getReg .x9 = s.getReg .x11
  x18 : u.getReg .x18 = s.getReg .x12
  x19 : u.getReg .x19 = 12
  x24 : u.getReg .x24 = 1
  last : eAt u (s.getReg .x2 - 5096) = lastOf s seg lp
  lpLen : lp.length = 5
  rest : Rest s u (kLanes (s.getReg .x12).toNat (instOf s) (outOf s) seg lp)

theorem to_last (hD : DotSpec) (hM : MulSpec) {s u : MachineState} {seg lp : List E} {wp : Word}
    (hpre : VerifyKeccakPre s) (A : A7 s u seg lp wp) : ∃ v, Reaches Image.code u v ∧
      (A9 s v seg lp wp ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have B := A.base
  have hab := hpre.stack.above
  have hrs := hpre.stack.rodata
  have hlo := hpre.heap.lo
  have heq := A.eqsegV
  have hlv := A.lanesV
  have hseg2 : (eqKernelRust seg).length = 2 := by
    rw [eqKernelRust_eq, eqKernel_length, A.segLen]; rfl
  have hl32 : (eqKernelRust lp).length = 32 := by
    rw [eqKernelRust_eq, eqKernel_length, A.lpLen]; rfl
  have heqlen : (vecLen u (s.getReg .x2 - 4832)).toNat = 2 := by
    rw [← hseg2, ← heq.elems, vecEs, eListAt_length]
  have hllen : (vecLen u (s.getReg .x2 - 5120)).toNat = 32 := by
    rw [← hl32, ← hlv.elems, vecEs, eListAt_length]
  -- the bounds checks
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800090b0_spec A.pc (by
    rv_eval [B.x2]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have m64 : u.getMem (u.getReg .x2 + 64) = 2 := by
    rw [B.x2, show s.getReg .x2 - 5248 + 64 = s.getReg .x2 - 5184 from
      BitVec.eq_of_toNat_eq (by addr_omega [hb])]; exact A.m64
  have m432 : u.getMem (u.getReg .x2 + 432) = vecLen u (s.getReg .x2 - 4832) := by
    rw [B.x2]; simp only [vecLen]; congr 1; exact BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have pc₁ := b800090b0_pc_not_taken h₁ (by rw [m64, m432, heqlen]; decide)
  have k₁ := b800090b0_keeps h₁
  have m₁ := b800090b0_mem_same h₁
  have x24₁ : u₁.getReg .x24 = 1 := by rw [b800090b0_x24 h₁, m64]; rfl
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800090c0_spec pc₁ (by
    rv_eval [k₁ .x2 (by decide), B.x2]
    valid_access hpre.stack.valid [hb])
  have pc₂ := b800090c0_pc_not_taken h₂ (by rw [k₁ .x21 (by decide), A.x21]; decide)
  have k₂ := b800090c0_keeps h₂
  have m₂ := b800090c0_mem_same h₂
  have x9₂ : u₂.getReg .x9 = s.getReg .x11 := by
    rw [b800090c0_x9 h₂, k₁ .x2 (by decide), m₁, B.x2, show s.getReg .x2 - 5248 + 72 =
      s.getReg .x2 - 5176 from BitVec.eq_of_toNat_eq (by addr_omega [hb])]; exact A.m72
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800090cc_spec pc₂ (by
    rv_eval [k₂ .x2 (by decide), k₁ .x2 (by decide), B.x2]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₃ := b800090cc_keeps h₃
  have m₃ := b800090cc_mem_same h₃
  have mu : ∀ a, u₃.getMem a = u.getMem a := fun a ↦ by rw [m₃, m₂, m₁]
  have x2₃ : u₃.getReg .x2 = s.getReg .x2 - 5248 := by
    rw [k₃ .x2 (by decide), k₂ .x2 (by decide), k₁ .x2 (by decide), B.x2]
  have B₃ := B.same x2₃ mu
  have hN₃ : heapNext u₃ = heapNext u := by simp only [heapNext, mu]
  have x10₃ : u₃.getReg .x10 = s.getReg .x2 - 3296 := by
    rw [b800090cc_x10 h₃, k₂ .x2 (by decide), k₁ .x2 (by decide), B.x2]
    exact BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have x11₃ : u₃.getReg .x11 = vecPtr u (s.getReg .x2 - 5120) := by
    rw [b800090cc_x11 h₃, k₂ .x25 (by decide), k₁ .x25 (by decide), A.x25]
  have x13₃ : u₃.getReg .x13 = s.getReg .x16 := by
    rw [b800090cc_x13 h₃, k₂ .x2 (by decide), k₁ .x2 (by decide), m₂, m₁, B.x2,
      show s.getReg .x2 - 5248 + 40 = s.getReg .x2 - 5208 from
        BitVec.eq_of_toNat_eq (by addr_omega [hb])]; exact A.m40
  have x23₃ : u₃.getReg .x23 = vecPtr u (s.getReg .x2 - 4832) + 24 := by
    rw [b800090cc_x23 h₃, k₂ .x24 (by decide), x24₁, k₂ .x2 (by decide), k₁ .x2 (by decide), m₂,
      m₁, B.x2]
    simp only [vecPtr]
    rw [show s.getReg .x2 - 5248 + 424 = s.getReg .x2 - 4832 + 8 from
      BitVec.eq_of_toNat_eq (by addr_omega [hb])]
    rfl
  -- `dot`
  have hor := hpre.output
  rw [hpre.outputLen] at hor
  rcases hor with h0 | hor
  · simp at h0
  have hos := hpre.outputStack
  rw [hpre.outputLen] at hos
  simp only [kOutput] at hor hos
  have hlh := vec_inHeap hlv
  rw [hllen] at hlh
  rcases hlh with h0 | ⟨hl1, hl2, hl8⟩
  · simp at h0
  have hhi := B.heap.hi
  unfold verifyKeccakStack at hb hab hrs hos
  have hdp : DotPre u₃ := {
    ret := by rw [x10₃]; exact slot_vmr hpre (by decide) (by decide) (by decide)
    left := by
      rw [x11₃, b800090cc_x12 h₃]
      exact Layer.heap_vmr (by addr_omega [hl1, hlo]) (by addr_omega [hl2, hhi]) hl8
    right := by
      rw [x13₃, b800090cc_x14 h₃]
      exact fun i hi ↦ Region.valid hor (by addr_omega [hor, hi]) (by addr_omega [hor, hi])
        (by addr_omega [hor, hi])
    stack := (hpre.stack.sub 5248 x2₃ (by unfold verifyKeccakStack; decide) (by decide)
      (by decide) (by decide) (by decide)).toStackOk
    retLeft := by rw [x10₃, x11₃, b800090cc_x12 h₃]; addr_omega [hb, hl2, hhi, hab]
    retRight := by rw [x10₃, x13₃, b800090cc_x14 h₃]; addr_omega [hb, hos]
    retStack := by rw [x10₃]; simp only [stackLo, x2₃]; addr_omega [hb]
    leftStack := by
      rw [x11₃, b800090cc_x12 h₃]; simp only [stackLo, x2₃]; addr_omega [hb, hl2, hhi, hab]
    rightStack := by rw [x13₃, b800090cc_x14 h₃]; simp only [stackLo, x2₃]; addr_omega [hb, hos]
    rodata := B₃.rodata hpre
    retRodata := by rw [x10₃]; addr_omega [hb, hrs]
    stackRodata := by simp only [stackLo, x2₃]; addr_omega [hb, hrs] }
  obtain ⟨u₄, hr₄, ⟨hpc₄, hpres₄, hpost₄⟩ | hd⟩ :=
    hD.call (hr₁.trans (hr₂.trans hr₃)) (b800090cc_pc h₃) hdp
  swap
  · exact ⟨u₄, hr₄, Or.inr hd⟩
  have x2₄ : u₄.getReg .x2 = s.getReg .x2 - 5248 := (hpres₄.reg .x2).trans x2₃
  have F₄ : DFrame u₃ u₄ (SW s u₃ u₄ [(3296, 24)] false) :=
    (DFrame.of_two hpost₄.frame).mono fun a ha ↦ fframe_sw hpre 3296 x2₃ x10₃ (by decide) a ha
  have hnx := hpre.stack.next
  unfold verifyKeccakStack at hnx
  have hN₄ : heapNext u₄ = heapNext u₃ := by
    simp only [heapNext]
    rw [hpost₄.frame _ (by rw [x10₃]; addr_omega [hb, hnx])
      (by simp only [stackLo, x2₃, dotStack, mulStack]; addr_omega [hb, hnx])]
  have hdot := hpost₄.value
  rw [x10₃, x11₃, x13₃, b800090cc_x12 h₃] at hdot
  have el : eListAt u₃ (vecPtr u (s.getReg .x2 - 5120)) (25 : Word).toNat =
      (eqKernelRust lp).take 25 := by
    rw [← hlv.elems, vecEs, hllen, eListAt_take _ _ (by decide)]
    exact (DFrame.of_same mu (fun _ ↦ False)).eListAt fun _ _ h ↦ h
  have eo : eListAt u₃ (s.getReg .x16) (25 : Word).toNat = outOf s := by
    rw [outOf, kOutput, hpre.outputLen]
    have hm := missOutput hpre B₃.heap
    rw [hpre.outputLen] at hm
    exact B₃.eListAt hm (Or.inr (by addr_omega [hor]))
  rw [el, eo] at hdot
  obtain ⟨u₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b800090fc_spec
    (by rw [hpc₄, returnAddress_eq, b800090cc_x1 h₃]; decide) trivial
  have k₅ := b800090fc_keeps h₅
  have m₅ := b800090fc_mem_same h₅
  have x2₅ : u₅.getReg .x2 = s.getReg .x2 - 5248 := (k₅ .x2 (by decide)).trans x2₄
  have B₄ := B₃.step hpre x2₄ ⟨by rw [hN₄]; exact B₃.heap.lo, by rw [hN₄]; exact B₃.heap.hi⟩
    (le_of_eq hN₄.symm) (by decide) F₄
  have B₅ := B₄.same x2₅ m₅
  have x10₅ : u₅.getReg .x10 = s.getReg .x2 - 5096 := by
    rw [b800090fc_x10 h₅, x2₄]; exact BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have x11₅ : u₅.getReg .x11 = vecPtr u (s.getReg .x2 - 4832) + 24 := by
    rw [b800090fc_x11 h₅, hpres₄.reg .x23, x23₃]
  have x12₅ : u₅.getReg .x12 = s.getReg .x2 - 3296 := by
    rw [b800090fc_x12 h₅, x2₄]; exact BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have heh := vec_inHeap heq
  rw [heqlen] at heh
  rcases heh with h0 | ⟨he1, he2, he8⟩
  · simp at h0
  have hl₅ : ValidMemRange (vecPtr u (s.getReg .x2 - 4832) + 24) 3 :=
    Layer.heap_vmr (by addr_omega [he1, hlo, he2, hhi]) (by addr_omega [he2, hhi])
      (by addr_omega [he8, he2, hhi])
  have hmp : MulPre u₅ := mul_pre hpre x2₅ (B₅.rodata hpre) 5096 x10₅ (by decide) (by decide)
    (by decide) (by rw [x11₅]; exact hl₅)
    (by rw [x11₅]; addr_omega [he2, hhi, hab, hb])
    (by rw [x10₅, x11₅]; addr_omega [he2, hhi, hab, hb])
    (by rw [x12₅]; exact slot_vmr hpre (by decide) (by decide) (by decide))
    (by rw [x12₅]; addr_omega [hb]) (by rw [x10₅, x12₅]; addr_omega [hb])
  obtain ⟨t, hr₆, ⟨hpc₆, hpres₆, hpost₆⟩ | hd⟩ := hM.call hr₅ (b800090fc_pc h₅) hmp
  swap
  · exact ⟨t, hr₄.trans hr₆, Or.inr hd⟩
  have x2₆ : t.getReg .x2 = s.getReg .x2 - 5248 := (hpres₆.reg .x2).trans x2₅
  have F₆ : DFrame u₅ t (SW s u₅ t [(5096, 24)] false) := (mul_frame x2₅ hpost₆).mono fun a h ↦ by
    rcases h with h | h
    · exact Or.inl (out_sw (K := 5096) (n := 24) x10₅ h)
    · exact Or.inr (Or.inl (by unfold verifyKeccakStack; addr_omega [h, hb]))
  have hN₆ : heapNext t = heapNext u₅ := by
    simp only [heapNext]
    rw [hpost₆.frame _ (by rw [x10₅]; addr_omega [hb, hnx])
      (by simp only [stackLo, x2₅, mulStack]; addr_omega [hb, hnx])]
  -- the whole step
  have hN₅ : heapNext u₅ = heapNext u₄ := by simp only [heapNext, m₅]
  have Ft : DFrame u t (SW s u t [(3296, 24), (5096, 24)] false) := by
    have F₃₅ : DFrame u₃ u₅ (SW s u₃ u₅ [(3296, 24)] false) :=
      SW.trans F₄ (DFrame.of_same m₅ (SW s u₄ u₅ [] false)) (fun _ h ↦ h) (by simp) (fun h ↦ h)
        (fun h ↦ h) (le_of_eq hN₄.symm) (le_of_eq hN₅.symm)
    have F₀₅ : DFrame u u₅ (SW s u u₅ [(3296, 24)] false) :=
      SW.trans (DFrame.of_same mu (SW s u u₃ [] false)) F₃₅ (by simp) (fun _ h ↦ h) (fun h ↦ h)
        (fun h ↦ h) (le_of_eq hN₃.symm) (le_of_eq (by rw [hN₅, hN₄]))
    exact SW.trans F₀₅ F₆ (fun p hp ↦ by simp at hp ⊢; exact Or.inl hp)
      (fun p hp ↦ by simp at hp ⊢; exact Or.inr hp) (fun h ↦ h) (fun h ↦ h)
      (le_of_eq (by rw [hN₅, hN₄, hN₃])) (le_of_eq hN₆.symm)
  have hNt : heapNext u ≤ heapNext t := le_of_eq (by rw [hN₆, hN₅, hN₄, hN₃])
  have Ht : HeapOk t := ⟨by rw [hN₆]; exact B₅.heap.lo, by rw [hN₆]; exact B₅.heap.hi⟩
  have hcb : (vecPtr u (s.getReg .x2 - 4832)).toNat + (vecCap u (s.getReg .x2 - 4832)).toNat * 24 ≤
      heapNext u := by
    have h1 := heq.buf; have h2 := heq.vec.len; rw [heqlen] at h2; simp only [NewBuf] at h1; omega
  have hlast : eAt t (s.getReg .x2 - 5096) = lastOf s seg lp := by
    have hv := hpost₆.value
    rw [x10₅, x11₅, x12₅] at hv
    rw [hv, lastOf]
    congr 1
    · rw [← heq.elems, vecEs, heqlen, getD_eListAt' _ _ (by decide)]
      have e : eAt u₅ (vecPtr u (s.getReg .x2 - 4832) + 24) =
          eAt u₃ (vecPtr u (s.getReg .x2 - 4832) + 24) := by
        rw [show eAt u₅ (vecPtr u (s.getReg .x2 - 4832) + 24) =
          eAt u₄ (vecPtr u (s.getReg .x2 - 4832) + 24) by unfold eAt; simp only [m₅]]
        exact F₄.eAt ((SW.buf (p := vecPtr u (s.getReg .x2 - 4832))
          (N := (vecCap u (s.getReg .x2 - 4832)).toNat * 24) hpre B₃ (by decide) (by
            have := heq.buf; simp only [NewBuf, hN₃] at this ⊢; exact this)).bytes (by addr_omega [he2, hhi]) (by
            have := heq.vec.len; rw [heqlen] at this; addr_omega [he2, hhi, this])
            (by addr_omega [hcb, hhi]))
      rw [e]
      unfold eAt; simp only [mu]
      rfl
    · rw [← hdot]; unfold eAt; simp only [m₅]
  have chain (r : Reg) (hc : r ∈ calleeSaved)
      (h1 : r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16,
        .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x25, .x26, .x27, .x28, .x29, .x30,
        .x31] : List Reg))
      (h2 : r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
        .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30,
        .x31] : List Reg))
      (h3 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x15, .x16, .x17, .x18, .x19, .x20, .x21,
        .x22, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg))
      (h5 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x13, .x14, .x15, .x16, .x17, .x18, .x19,
        .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg)) :
      t.getReg r = u.getReg r := by
    rw [hpres₆.reg r hc, k₅ r h5, hpres₄.reg r hc, k₃ r h3, k₂ r h2, k₁ r h1]
  refine ⟨t, hr₄.trans hr₆, Or.inl {
      A.toM.step hpre x2₆ Ht hNt (by decide) (by decide) Ft with
    pc := by rw [hpc₆, returnAddress_eq, b800090fc_x1 h₅]; decide
    wb := A.wb.step hpre B hNt (by decide) Ft fun r hr ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact chain _ (by decide) (by decide) (by decide)
        (by decide) (by decide)
    x9 := by
      rw [hpres₆.reg .x9, k₅ .x9 (by decide), hpres₄.reg .x9, k₃ .x9 (by decide), x9₂]
    x18 := (chain .x18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans A.x18
    x19 := (chain .x19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans A.x19
    x24 := by
      rw [hpres₆.reg .x24, k₅ .x24 (by decide), hpres₄.reg .x24, k₃ .x24 (by decide),
        k₂ .x24 (by decide), x24₁]
    last := hlast
    lpLen := A.lpLen
    rest := A.rest.keep fun T hT ↦ SW.tat hpre B Ht hNt (by decide) Ft hT }⟩

end Rv64Verifier.Gkr.Keccak
