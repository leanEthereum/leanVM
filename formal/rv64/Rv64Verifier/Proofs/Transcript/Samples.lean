import Rv64Verifier.Proofs.Transcript.SamplesModel
import Rv64Verifier.Proofs.Transcript.Frames
import Rv64Verifier.Proofs.Transcript.Contracts
import Rv64Verifier.Blocks.F45

/-!
# `Transcript::samples`

```rust
pub fn samples(&mut self, count: usize) -> Vec<E> {
    (0..count).map(|_| self.sample()).collect()
}
```

compiled at `0x8000c618` (`Blocks/F45.lean`), `sample` inlined: an 80-byte frame saving `ra`,
`s0`..`s5`; `try_allocate_in` for `count` elements, a trap on its error; the `Vec` at the frame's
bottom and `reserve(count)`; the loop (`0x8000c6b4`, `0x8000c6c0`): `duplex`, the state's first
three lanes appended; `0x8000c6e4` copies the `Vec` out with length `count` and returns.

`Body s u cap ptr d` is the loop head after `d` challenges: the buffer holds the first `d` of
`sqs count`, the sponge the state after them, every write since entry in the result, the sponge,
the stack, `NEXT` or the heap allocated (`W`).
-/

namespace Rv64Verifier.Transcript.Samples
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F45
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen

theorem bounds {s : MachineState} (h : SamplesPre s) :
    0xa0000000 + samplesStack ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000000 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧
      (stackLo s samplesStack).toNat = (s.getReg .x2).toNat - samplesStack := by
  have hm := h.stack.mapped (by decide) (by decide)
  have hb := h.stack.bounds (by decide) (by decide)
  omega

theorem heap_valid {x : Word} (h1 : heapStart ≤ x.toNat) (h2 : x.toNat + 8 ≤ heapEnd)
    (h3 : x.toNat % 8 = 0) : Sym.validAccess 8 x = true :=
  (Sym.validAccess_eight x).mpr ⟨Or.inl ⟨by simp only [heapStart] at h1; omega,
    by simp only [heapEnd] at h2; omega⟩, h3⟩

/-- What the function may write, `NEXT` at `nx`. -/
def W (s : MachineState) (nx : Word) (a : Word) : Prop :=
  Within a (s.getReg .x10) 24 ∨ Within a (s.getReg .x11 + 8) 336 ∨
    Within a (stackLo s samplesStack) samplesStack ∨ Within a nextAddr 8 ∨
    (heapNext s ≤ a.toNat ∧ a.toNat < nx.toNat)

/-- The callee-saved registers the function never touches. -/
def keptRegs : List Reg := [.x22, .x23, .x24, .x25, .x26, .x27]

/-- The loop head after `d` challenges, the `Vec`'s capacity `cap` and buffer `ptr`. -/
structure Body (s u : MachineState) (nx cap ptr : Word) (d : Nat) : Prop where
  x2 : u.getReg .x2 = s.getReg .x2 - 80
  x8 : u.getReg .x8 = s.getReg .x10
  x9 : u.getReg .x9 = BitVec.ofNat 64 ((s.getReg .x12).toNat - d)
  x18 : u.getReg .x18 = s.getReg .x11
  x19 : u.getReg .x19 = s.getReg .x11 + 8
  x20 : u.getReg .x20 = s.getReg .x12
  x21 : u.getReg .x21 = ptr + BitVec.ofNat 64 (24 * d) + 16
  kept : ∀ r ∈ keptRegs, u.getReg r = s.getReg r
  ra : u.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : u.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s1 : u.getMem (s.getReg .x2 - 24) = s.getReg .x9
  s2 : u.getMem (s.getReg .x2 - 32) = s.getReg .x18
  s3 : u.getMem (s.getReg .x2 - 40) = s.getReg .x19
  s4 : u.getMem (s.getReg .x2 - 48) = s.getReg .x20
  s5 : u.getMem (s.getReg .x2 - 56) = s.getReg .x21
  capM : u.getMem (s.getReg .x2 - 80) = cap
  ptrM : u.getMem (s.getReg .x2 - 72) = ptr
  next : u.getMem nextAddr = nx
  frame : DFrame s u (W s nx)
  sponge : spongeAt u (s.getReg .x11 + 8) = (sqs d (spongeAt s (s.getReg .x11 + 8))).2
  elems : eListAt u ptr d = (sqs d (spongeAt s (s.getReg .x11 + 8))).1

/-- Where the buffer lies: allocated since entry, within the heap. -/
structure Buffer (s : MachineState) (nx ptr : Word) : Prop where
  lo : heapNext s ≤ ptr.toNat
  hi : ptr.toNat + 24 * (s.getReg .x12).toNat ≤ nx.toNat
  heap : nx.toNat ≤ heapEnd
  al : ptr.toNat % 8 = 0

theorem eListAt_succ (s : MachineState) (p : Word) (d : Nat) :
    eListAt s p (d + 1) = eListAt s p d ++ [eAt s (p + BitVec.ofNat 64 (24 * d))] := by
  simp only [eListAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem challengeOf_stateAt (u : MachineState) (a : Word) :
    challengeOf (stateAt u a) = eAt u a := by
  simp only [challengeOf, lane_stateAt u a (by decide : 0 < 25), lane_stateAt u a (by decide : 1 < 25),
    lane_stateAt u a (by decide : 2 < 25), Nat.mul_zero, Nat.mul_one, Nat.reduceMul, add_ofNat_zero]
  rfl

theorem ofNat_sub_one {m : Nat} (h1 : 1 ≤ m) (h2 : m < 2 ^ 64) :
    BitVec.ofNat 64 m - 1 = BitVec.ofNat 64 (m - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]
  omega

theorem ofNat_eq_zero {m : Nat} (h2 : m < 2 ^ 64) : BitVec.ofNat 64 m = 0 ↔ m = 0 := by
  constructor
  · intro h; have := congrArg BitVec.toNat h; rw [BitVec.toNat_ofNat] at this; simp at this; omega
  · intro h; subst h; rfl

set_option maxHeartbeats 1000000 in
/-- One iteration: `duplex`, the challenge appended. -/
theorem body (hD : DuplexSpec) {s u : MachineState} {nx cap ptr : Word} {d : Nat}
    (hpre : SamplesPre s) (hbuf : Buffer s nx ptr) (hpc : u.pc = 0x8000c6b4)
    (h : Body s u nx cap ptr d) (hd : d < (s.getReg .x12).toNat) :
    ∃ v, Reaches Image.code u v ∧ ((Body s v nx cap ptr (d + 1) ∧
      ((v.pc = 0x8000c6b4 ∧ d + 1 < (s.getReg .x12).toNat) ∨
        (v.pc = 0x8000c6e4 ∧ d + 1 = (s.getReg .x12).toNat))) ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have hro := hpre.stack.rodata
  have hsf := hpre.selfFree
  have hnxt := hpre.stack.next
  have hlo := hpre.heap.lo
  have hn64 := (s.getReg .x12).isLt
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000c6b4_spec hpc trivial
  have k₁ := b8000c6b4_keeps h₁
  have hm₁ := b8000c6b4_mem_same h₁
  have x10₁ : u₁.getReg .x10 = s.getReg .x11 + 8 := (b8000c6b4_x10 h₁).trans h.x19
  have x2₁ : u₁.getReg .x2 = s.getReg .x2 - 80 := (k₁ .x2 (by decide)).trans h.x2
  have F₁ : DFrame s u₁ (W s nx) := h.frame.trans (DFrame.of_same hm₁ _) fun _ h ↦ h
  have hdp : DuplexPre u₁ := {
    sponge := by rw [x10₁]; addr_omega [hS]
    stack := hpre.stack.sub 80 x2₁ (by simp only [samplesStack]; omega) (by decide) (by decide)
      (by decide) (by decide)
    spongeStack := by rw [x10₁]; simp only [stackLo, x2₁]; addr_omega [hb, hss, hS]
    rodata := hpre.rodata.dframe F₁ fun a ha hw ↦ by
      simp only [W] at hw
      rcases hw with hw | hw | hw | hw | hw <;>
        addr_omega [ha, hw, hro, hb, hpre.outRodata, hpre.selfRodata, hS, hbuf.heap]
    spongeRodata := by rw [x10₁]; addr_omega [hpre.selfRodata, hS] }
  obtain ⟨w, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd'⟩ := hD.call hr₁ (b8000c6b4_pc h₁) hdp
  swap
  · exact ⟨_, hr₂, Or.inr hd'⟩
  have val₂ := hpost₂.value
  rw [x10₁] at val₂
  have G₂ : DFrame u₁ w (fun a ↦ Within a (s.getReg .x11 + 8) 336 ∨
      Within a (stackLo s samplesStack) (samplesStack - 80)) :=
    hpost₂.frame.mono fun a ha ↦ by
      rw [x10₁] at ha
      simp only [stackLo, x2₁] at ha
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (by addr_omega [ha, hb])
  have rw' (r : Reg) (hr : r ∈ calleeSaved) (hk : r ∈ [Reg.x2, .x8, .x9, .x18, .x19, .x20, .x21,
      .x22, .x23, .x24, .x25, .x26, .x27]) : w.getReg r = u.getReg r := by
    rw [hpres₂ r hr, k₁ r (mem_of_mem hk _)]
  have x18w : w.getReg .x18 = s.getReg .x11 := (rw' .x18 (by decide) (by decide)).trans h.x18
  have x21w : w.getReg .x21 = ptr + BitVec.ofNat 64 (24 * d) + 16 :=
    (rw' .x21 (by decide) (by decide)).trans h.x21
  have x9w : w.getReg .x9 = BitVec.ofNat 64 ((s.getReg .x12).toNat - d) :=
    (rw' .x9 (by decide) (by decide)).trans h.x9
  have hbv := hbuf
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hbv
  obtain ⟨v, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000c6c0_spec
    (by rw [hpc₂, returnAddress_eq, b8000c6b4_x1 h₁]; decide) (by
      rv_eval [x18w, x21w]
      and_intros <;> first
        | (refine Region.valid hS ?_ ?_ ?_ <;> addr_omega [hS])
        | (refine heap_valid ?_ ?_ ?_ <;> addr_omega [hlo, hb1, hb2, hb3, hb4, hd]))
  have k₃ := b8000c6c0_keeps h₃
  have m0 := b8000c6c0_m_x21_0 h₃
  have m8 := b8000c6c0_m_x21_n8 h₃
  have m16 := b8000c6c0_m_x21_n16 h₃
  have f₃ := b8000c6c0_frame h₃ (by rw [x21w]; addr_omega [hlo, hb1, hb2, hb3, hd])
  rw [x21w, x18w] at m0 m8 m16
  rw [x21w] at f₃
  have e16 : ptr + BitVec.ofNat 64 (24 * d) + 16 - 16 = ptr + BitVec.ofNat 64 (24 * d) := by
    bv_omega
  have e8 : ptr + BitVec.ofNat 64 (24 * d) + 16 - 8 = ptr + BitVec.ofNat 64 (24 * d) + 8 := by
    bv_omega
  rw [e16] at m16 f₃
  rw [e8] at m8
  -- what the iteration writes
  have Fv : DFrame s v (W s nx) :=
    (F₁.trans G₂ fun a ha ↦ by
      simp only [W]
      rcases ha with ha | ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hS]))
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))).trans (DFrame.of_memFrame f₃)
      fun a ha ↦ by
        simp only [W]
        exact Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1, hb2, hd]))))
  have stk (y : Word) (h1 : (s.getReg .x2).toNat - 80 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat) : v.getMem y = u.getMem y := by
    rw [f₃ y (by addr_omega [h1, h2, hb, hb1, hb2, hb3, hd]),
      G₂ y fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, h1, h2, hb, hss, hS], hm₁]
  have x9v : v.getReg .x9 = BitVec.ofNat 64 ((s.getReg .x12).toNat - (d + 1)) := by
    rw [b8000c6c0_x9 h₃, x9w, ofNat_sub_one (by omega) (by omega)]
    congr 1
  have hsw : spongeAt v (s.getReg .x11 + 8) = spongeAt w (s.getReg .x11 + 8) :=
    spongeAt_congr (by addr_omega [hS]) fun y h1 h2 ↦
      f₃ y (by addr_omega [h1, h2, hS, hsf, hb1, hb2, hb3, hd])
  have hsu : spongeAt u₁ (s.getReg .x11 + 8) = spongeAt u (s.getReg .x11 + 8) :=
    spongeAt_congr (by addr_omega [hS]) fun y _ _ ↦ hm₁ y
  have hst : (spongeAt w (s.getReg .x11 + 8)).state = stateAt w (s.getReg .x11 + 8 + 128) := rfl
  have body : Body s v nx cap ptr (d + 1) := {
    x2 := by rw [k₃ .x2 (by decide), rw' .x2 (by decide) (by decide), h.x2]
    x8 := by rw [k₃ .x8 (by decide), rw' .x8 (by decide) (by decide), h.x8]
    x9 := x9v
    x18 := by rw [k₃ .x18 (by decide), x18w]
    x19 := by rw [k₃ .x19 (by decide), rw' .x19 (by decide) (by decide), h.x19]
    x20 := by rw [k₃ .x20 (by decide), rw' .x20 (by decide) (by decide), h.x20]
    x21 := by rw [b8000c6c0_x21 h₃, x21w]; bv_omega
    kept := fun r hr ↦ by
      rw [k₃ r (mem_of_mem hr _), hpres₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _), h.kept r hr]
    ra := by rw [stk _ (by addr_omega [hb]) (by addr_omega [hb]), h.ra]
    s0 := by rw [stk _ (by addr_omega [hb]) (by addr_omega [hb]), h.s0]
    s1 := by rw [stk _ (by addr_omega [hb]) (by addr_omega [hb]), h.s1]
    s2 := by rw [stk _ (by addr_omega [hb]) (by addr_omega [hb]), h.s2]
    s3 := by rw [stk _ (by addr_omega [hb]) (by addr_omega [hb]), h.s3]
    s4 := by rw [stk _ (by addr_omega [hb]) (by addr_omega [hb]), h.s4]
    s5 := by rw [stk _ (by addr_omega [hb]) (by addr_omega [hb]), h.s5]
    capM := by rw [stk _ (by addr_omega [hb]) (by addr_omega [hb]), h.capM]
    ptrM := by rw [stk _ (by addr_omega [hb]) (by addr_omega [hb]), h.ptrM]
    next := by
      rw [f₃ _ (by addr_omega [hb1, hb2, hb3, hd]), G₂ _ fun i hi hw ↦ by
        rcases hw with hw | hw <;> addr_omega [hw, hi, hsf, hS, hnxt, hb], hm₁, h.next]
    frame := Fv
    sponge := by
      rw [hsw, val₂, hsu, h.sponge]
      rfl
    elems := by
      rw [eListAt_succ, (DFrame.of_memFrame f₃).eListAt fun i hi hw ↦ by addr_omega [hw, hi, hb4, hb2, hb3, hd],
        G₂.eListAt fun i hi hw ↦ by
          rcases hw with hw | hw <;> addr_omega [hw, hi, hsf, hS, hb, hb1, hb2, hb3, hd, hlo],
        (DFrame.of_same hm₁ fun _ ↦ False).eListAt fun _ _ h ↦ h, h.elems]
      rw [sqs]
      refine congrArg (fun z ↦ (sqs d (spongeAt s (s.getReg .x11 + 8))).1 ++ [z]) ?_
      change eAt v (ptr + BitVec.ofNat 64 (24 * d)) =
        challengeOf (spDuplex (sqs d (spongeAt s (s.getReg .x11 + 8))).2).state
      rw [← h.sponge, ← hsu, ← val₂, hst, challengeOf_stateAt]
      unfold Rv64Verifier.eAt
      have a1 : s.getReg .x11 + 8 + 128 = s.getReg .x11 + 136 := by bv_omega
      have a2 : s.getReg .x11 + 136 + 8 = s.getReg .x11 + 144 := by bv_omega
      have a3 : s.getReg .x11 + 136 + 16 = s.getReg .x11 + 152 := by bv_omega
      rw [a1, a2, a3, m16, m8, m0] }
  refine ⟨v, hr₂.trans hr₃, Or.inl ⟨body, ?_⟩⟩
  by_cases hl : d + 1 < (s.getReg .x12).toNat
  · refine Or.inl ⟨b8000c6c0_pc_taken h₃ ?_, hl⟩
    rw [x9w, ofNat_sub_one (by omega) (by omega)]
    exact fun h0 ↦ by rw [ofNat_eq_zero (by omega)] at h0; omega
  · refine Or.inr ⟨b8000c6c0_pc_not_taken h₃ ?_, by omega⟩
    rw [x9w, ofNat_sub_one (by omega) (by omega), ofNat_eq_zero (by omega)]
    omega

/-- At `0x8000c6e4`, every challenge in the buffer. -/
structure AtExit (s u : MachineState) (nx cap ptr : Word) : Prop where
  x2 : u.getReg .x2 = s.getReg .x2 - 80
  x8 : u.getReg .x8 = s.getReg .x10
  x20 : u.getReg .x20 = s.getReg .x12
  kept : ∀ r ∈ keptRegs, u.getReg r = s.getReg r
  ra : u.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : u.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s1 : u.getMem (s.getReg .x2 - 24) = s.getReg .x9
  s2 : u.getMem (s.getReg .x2 - 32) = s.getReg .x18
  s3 : u.getMem (s.getReg .x2 - 40) = s.getReg .x19
  s4 : u.getMem (s.getReg .x2 - 48) = s.getReg .x20
  s5 : u.getMem (s.getReg .x2 - 56) = s.getReg .x21
  capM : u.getMem (s.getReg .x2 - 80) = cap
  ptrM : u.getMem (s.getReg .x2 - 72) = ptr
  next : u.getMem nextAddr = nx
  frame : DFrame s u (W s nx)
  sponge : spongeAt u (s.getReg .x11 + 8) =
    (sqs (s.getReg .x12).toNat (spongeAt s (s.getReg .x11 + 8))).2
  elems : eListAt u ptr (s.getReg .x12).toNat =
    (sqs (s.getReg .x12).toNat (spongeAt s (s.getReg .x11 + 8))).1

theorem Body.toExit {s u : MachineState} {nx cap ptr : Word} (h : Body s u nx cap ptr
    (s.getReg .x12).toNat) : AtExit s u nx cap ptr :=
  ⟨h.x2, h.x8, h.x20, h.kept, h.ra, h.s0, h.s1, h.s2, h.s3, h.s4, h.s5, h.capM, h.ptrM, h.next,
    h.frame, h.sponge, h.elems⟩

/-- `0x8000c6e4`: the `Vec` out, the saved registers back, return. -/
theorem exit {s u : MachineState} {nx cap ptr : Word} (hpre : SamplesPre s)
    (hpc : u.pc = 0x8000c6e4) (h : AtExit s u nx cap ptr) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      vecCap t (s.getReg .x10) = cap ∧ vecPtr t (s.getReg .x10) = ptr ∧
      vecLen t (s.getReg .x10) = s.getReg .x12 ∧ MemFrame u t (s.getReg .x10) 24 := by
  have hb := bounds hpre
  have ho := hpre.out
  have hos := hpre.outStack
  obtain ⟨t, hr, h₁⟩ := Sym.BlockSpec.reaches b8000c6e4_spec hpc (by
    rv_eval [h.x2, h.x8]
    and_intros <;> first
      | addr_omega [hb, ho, hos]
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
  have k := b8000c6e4_keeps h₁
  have pc := b8000c6e4_pc h₁
  have y1 := b8000c6e4_x1 h₁
  have y2 := b8000c6e4_x2 h₁
  have y8 := b8000c6e4_x8 h₁
  have y9 := b8000c6e4_x9 h₁
  have y18 := b8000c6e4_x18 h₁
  have y19 := b8000c6e4_x19 h₁
  have y20 := b8000c6e4_x20 h₁
  have y21 := b8000c6e4_x21 h₁
  have m0 := b8000c6e4_m_x8_0 h₁
  have m8 := b8000c6e4_m_x8_8 h₁
  have m16 := b8000c6e4_m_x8_16 h₁
  have f := b8000c6e4_frame h₁ (by rw [h.x8]; addr_omega [ho])
  rv_eval [h.x2] at pc y2 y8 y9 y18 y19 y20 y21 m0 m8
  rw [h.x8] at m0 m8 m16 f
  refine ⟨t, hr, by rw [pc, h.ra, returnAddress_eq], ?_, by rw [vecCap, m0, h.capM],
    by rw [vecPtr, m8, h.ptrM], by rw [vecLen, m16, h.x20], f⟩
  intro r hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact y2
  · rw [y8, h.s0]
  · rw [y9, h.s1]
  · rw [y18, h.s2]
  · rw [y19, h.s3]
  · rw [y20, h.s4]
  · rw [y21, h.s5]
  all_goals rw [k _ (by decide), h.kept _ (by decide)]

/-- What the setup writes: the stack, `NEXT` and the heap allocated. -/
def W0 (s : MachineState) (nx : Word) (a : Word) : Prop :=
  Within a (stackLo s samplesStack) samplesStack ∨ Within a nextAddr 8 ∨
    (heapNext s ≤ a.toNat ∧ a.toNat < nx.toNat)

theorem W0.mono {s : MachineState} {nx nx' a : Word} (h : nx.toNat ≤ nx'.toNat) (hw : W0 s nx a) :
    W0 s nx' a := by
  rcases hw with hw | hw | hw
  · exact Or.inl hw
  · exact Or.inr (Or.inl hw)
  · exact Or.inr (Or.inr ⟨hw.1, Nat.lt_of_lt_of_le hw.2 h⟩)

/-- What the setup writes after the prologue: the stack below the saved registers, `NEXT` and the
heap allocated. -/
def W1 (s : MachineState) (nx : Word) (a : Word) : Prop :=
  Within a (stackLo s samplesStack) (samplesStack - 56) ∨ Within a nextAddr 8 ∨
    (heapNext s ≤ a.toNat ∧ a.toNat < nx.toNat)

theorem W1.mono {s : MachineState} {nx nx' a : Word} (h : nx.toNat ≤ nx'.toNat) (hw : W1 s nx a) :
    W1 s nx' a := by
  rcases hw with hw | hw | hw
  · exact Or.inl hw
  · exact Or.inr (Or.inl hw)
  · exact Or.inr (Or.inr ⟨hw.1, Nat.lt_of_lt_of_le hw.2 h⟩)

theorem W1.toW0 {s : MachineState} {nx a : Word} (hw : W1 s nx a) : W0 s nx a := by
  rcases hw with hw | hw | hw
  · exact Or.inl (by simp only [Within, samplesStack] at hw ⊢; omega)
  · exact Or.inr (Or.inl hw)
  · exact Or.inr (Or.inr hw)

theorem W0.toW {s : MachineState} {nx a : Word} (hw : W0 s nx a) : W s nx a :=
  Or.inr (Or.inr hw)

/-- Back from `reserve`, at `0x8000c68c`: the `Vec` at the frame's bottom, empty, with room for
`count` in a buffer allocated since entry. -/
structure Setup (s u : MachineState) (nx cap ptr : Word) : Prop where
  x2 : u.getReg .x2 = s.getReg .x2 - 80
  x8 : u.getReg .x8 = s.getReg .x10
  x9 : u.getReg .x9 = s.getReg .x12
  x18 : u.getReg .x18 = s.getReg .x11
  kept : ∀ r ∈ [Reg.x19, .x20, .x21] ++ keptRegs, u.getReg r = s.getReg r
  ra : u.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : u.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s1 : u.getMem (s.getReg .x2 - 24) = s.getReg .x9
  s2 : u.getMem (s.getReg .x2 - 32) = s.getReg .x18
  s3 : u.getMem (s.getReg .x2 - 40) = s.getReg .x19
  s4 : u.getMem (s.getReg .x2 - 48) = s.getReg .x20
  s5 : u.getMem (s.getReg .x2 - 56) = s.getReg .x21
  capM : u.getMem (s.getReg .x2 - 80) = cap
  ptrM : u.getMem (s.getReg .x2 - 72) = ptr
  lenM : u.getMem (s.getReg .x2 - 64) = 0
  next : u.getMem nextAddr = nx
  heap : HeapOk u
  mono : heapNext s ≤ heapNext u
  frame : DFrame s u (W0 s nx)
  room : (s.getReg .x12).toNat ≤ cap.toNat
  buf : Buf u ptr (cap.toNat * 24) 8
  fresh : NewBuf s u ptr (cap.toNat * 24) 8
  sponge : spongeAt u (s.getReg .x11 + 8) = spongeAt s (s.getReg .x11 + 8)

set_option maxHeartbeats 1000000 in
/-- The frame, `try_allocate_in(count)`, the `Vec`, `reserve(count)`. -/
theorem setup (hT : TryAllocZeroedSpec) (hR : ReserveFreshSpec 0x80008a10 24 8)
    {s : MachineState} (hpc : s.pc = 0x8000c618) (hpre : SamplesPre s) :
    ∃ u, Reaches Image.code s u ∧ ((u.pc = 0x8000c68c ∧ ∃ nx cap ptr, Setup s u nx cap ptr) ∨
      Dead Image.code u) := by
  have hb := bounds hpre
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  have hst := hpre.stack
  have hnxt := hst.next
  have hab := hst.above
  have hlo := hpre.heap.lo
  have hhi := hpre.heap.hi
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000c618_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000c618_keeps h₁
  have x2₁ := b8000c618_x2 h₁
  have x10₁ := b8000c618_x10 h₁
  have x11₁ := b8000c618_x11 h₁
  have x13₁ := b8000c618_x13 h₁
  have x14₁ := b8000c618_x14 h₁
  have f₁ := b8000c618_frame h₁ (by addr_omega [hb])
  have F₁ : DFrame s t₁ (W0 s (s.getMem nextAddr)) := (DFrame.of_memFrame f₁).mono fun a ha ↦
    Or.inl (by addr_omega [ha, hb])
  have nx₁ : t₁.getMem nextAddr = s.getMem nextAddr := f₁ _ (by addr_omega [hnxt, hb])
  have hheap₁ : HeapOk t₁ := ⟨by simp only [heapNext, nx₁]; exact hlo,
    by simp only [heapNext, nx₁]; exact hhi⟩
  have hta : TryAllocPre .x13 .x14 t₁ := {
    heap := hheap₁
    out := by rw [x10₁]; valid_sub hst.valid [hb]
    align := by rw [x13₁]; decide
    size := by rw [x14₁]; decide
    stack := hst.sub 80 x2₁ (by decide) (by decide)
      (by decide) (by decide) (by decide)
    outFree := by
      rw [x10₁]; simp only [Outside, heapNext, nx₁]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnxt, hb]⟩
    outStack := by rw [x10₁]; simp only [stackLo, x2₁]; addr_omega [hb] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂, -⟩ | hd⟩ := hT.call hr₁ (b8000c618_pc h₁) hta
  swap
  · exact ⟨_, hr₂, Or.inr hd⟩
  have G₂ : DFrame t₁ t₂ (W1 s (t₂.getMem nextAddr)) :=
    (DFrame.of_byteFrame hpost₂.frame).mono fun a ha ↦ by
      rw [x10₁] at ha
      simp only [W1, stackLo, x2₁, Fresh, heapNext, nx₁] at ha ⊢
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ha)
  have k2 (r : Reg) (hr : r ∈ calleeSaved) : t₂.getReg r = t₁.getReg r := hpres₂ r hr
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000c660_spec
    (by rw [hpc₂, returnAddress_eq, b8000c618_x1 h₁]; decide) (by
      rv_eval [k2 .x2 (by decide), x2₁]
      valid_access hst.valid [hb])
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 80 := (k2 .x2 (by decide)).trans x2₁
  by_cases herr : t₂.getMem (s.getReg .x2 - 80) = 0
  swap
  · refine ⟨t₃, hr₂.trans hr₃, Or.inr (dead_of_fetch ?_)⟩
    rw [b8000c660_pc_taken h₃ (by rw [x2₂]; exact herr)]
    exact Option.isNone_iff_eq_none.mp (by decide +kernel)
  obtain ⟨hcap₂, hnew₂⟩ := hpost₂.ok (by rw [x10₁]; exact herr)
  rw [x10₁, x11₁] at hcap₂ hnew₂
  rw [x14₁, x13₁, show (24 : Word).toNat = 24 from rfl, show (8 : Word).toNat = 8 from rfl] at hnew₂
  have k₃ := b8000c660_keeps h₃
  have hm₃ := b8000c660_mem_same h₃
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000c668_spec
    (b8000c660_pc_not_taken h₃ (by rw [x2₂]; exact herr)) (by
      rv_eval [k₃ .x2 (by decide), x2₂]
      and_intros <;> first | addr_omega [hb] | valid_access hst.valid [hb])
  have k₄ := b8000c668_keeps h₄
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 80 := (k₃ .x2 (by decide)).trans x2₂
  have m0 := b8000c668_m_x2_0 h₄
  have m8 := b8000c668_m_x2_8 h₄
  have m16 := b8000c668_m_x2_16 h₄
  have f₄ := b8000c668_frame h₄ (by rw [x2₃]; addr_omega [hb])
  rw [x2₃] at m0 m8 m16 f₄
  rw [hm₃, hcap₂] at m0
  rw [hm₃] at m8
  have x10₄ : t₄.getReg .x10 = s.getReg .x2 - 80 := (b8000c668_x10 h₄).trans x2₃
  have x11₄ : t₄.getReg .x11 = s.getReg .x12 := by
    rw [b8000c668_x11 h₄, k₃ .x9 (by decide), k2 .x9 (by decide), b8000c618_x9 h₁]
  have x2₄ : t₄.getReg .x2 = s.getReg .x2 - 80 := (k₄ .x2 (by decide)).trans x2₃
  have nx₄ : t₄.getMem nextAddr = t₂.getMem nextAddr := by
    rw [f₄ _ (by addr_omega [hnxt, hb]), hm₃]
  have hh₄ : heapNext t₄ = heapNext t₂ := by simp only [heapNext, nx₄]
  have hheap₄ : HeapOk t₄ := ⟨hh₄ ▸ hpost₂.heap.lo, hh₄ ▸ hpost₂.heap.hi⟩
  have hbuf₂ := hnew₂.buf hheap₁
  have hrp : ReservePre 24 8 t₄ := {
    heap := hheap₄
    self := by rw [x10₄]; valid_sub hst.valid [hb]
    vec := by
      rw [x10₄]
      refine ⟨?_, ?_⟩
      · have := hbuf₂
        simp only [RawVecOk, Buf, vecPtr, vecCap, m0, m8, hh₄] at this ⊢
        exact this
      · simp only [vecLen, vecCap, m16, m0]; simp
    stack := hst.sub 80 x2₄ (by decide) (by decide) (by decide) (by decide) (by decide)
    selfFree := by
      rw [x10₄]; simp only [Outside, hh₄]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnxt, hb]⟩
    selfStack := by rw [x10₄]; simp only [stackLo, x2₄]; addr_omega [hb] }
  obtain ⟨t₅, hr₅, ⟨hpc₅, hpres₅, hpost₅, hfr₅⟩ | hd⟩ :=
    hR.call (hr₂.trans (hr₃.trans hr₄)) (b8000c668_pc h₄) hrp
  swap
  · exact ⟨_, hr₅, Or.inr hd⟩
  rw [x10₄] at hfr₅
  have hcap₅ := hpost₅.cap
  have hlen₅ := hpost₅.len
  rw [x10₄, x11₄] at hcap₅
  rw [x10₄] at hlen₅
  have e0 : vecLen t₄ (s.getReg .x2 - 80) = 0 := by simp only [vecLen]; rw [m16]
  rw [e0] at hcap₅ hlen₅
  have G₅ : DFrame t₄ t₅ (W1 s (t₅.getMem nextAddr)) :=
    (DFrame.of_byteFrame hpost₅.frame).mono fun a ha ↦ by
      rw [x10₄] at ha
      simp only [W1, stackLo, x2₄, Fresh, heapNext] at ha ⊢
      have := hpost₂.mono
      simp only [heapNext, nx₁] at this
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ⟨by rw [nx₄] at ha; omega, ha.2⟩)
  have mono₂ := hpost₂.mono
  have mono₅ := hpost₅.mono
  simp only [heapNext, nx₁, nx₄] at mono₂ mono₅
  have H₁ : DFrame s t₁ (W0 s (t₅.getMem nextAddr)) := F₁.mono fun a h ↦ W0.mono (by omega) h
  have H₂ : DFrame t₁ t₂ (W1 s (t₅.getMem nextAddr)) := G₂.mono fun a h ↦ W1.mono (by omega) h
  have H₄ : DFrame t₂ t₄ (W1 s (t₅.getMem nextAddr)) :=
    (DFrame.of_same hm₃ _).trans (DFrame.of_memFrame f₄) fun a h ↦ Or.inl (by addr_omega [h, hb])
  have H₁₅ : DFrame t₁ t₅ (W1 s (t₅.getMem nextAddr)) :=
    (H₂.trans H₄ fun _ h ↦ h).trans G₅ fun _ h ↦ h
  have F₅ : DFrame s t₅ (W0 s (t₅.getMem nextAddr)) := H₁.trans H₁₅ fun _ h ↦ W1.toW0 h
  have hhi₅ := hpost₅.heap.hi
  have rg (r : Reg) (hr : r ∈ calleeSaved) (hk : r ∈ [Reg.x2, .x8, .x9, .x18, .x19, .x20, .x21,
      .x22, .x23, .x24, .x25, .x26, .x27]) : t₅.getReg r = t₁.getReg r := by
    rw [hpres₅ r hr, k₄ r (mem_of_mem hk _), k₃ r (mem_of_mem hk _), k2 r hr]
  have slot (y : Word) (h1 : (s.getReg .x2).toNat - 56 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat) : t₅.getMem y = t₁.getMem y :=
    H₁₅ y fun i hi hw ↦ by
      rcases hw with hw | hw | hw <;> addr_omega [hw, hi, h1, h2, hb, hnxt, hab, hhi₅]
  have hvec := hpost₅.vec
  rw [x10₄] at hvec
  rw [show (0 : Word).toNat = 0 from rfl] at hcap₅
  have hh1 : heapNext t₁ = heapNext s := by simp only [heapNext, nx₁]
  have hA : heapNext t₂ ≤ heapNext t₅ := by have := hpost₅.mono; rw [hh₄] at this; exact this
  have hB : heapNext s ≤ heapNext t₂ := hh1 ▸ hpost₂.mono
  have hC : heapNext t₄ ≤ heapNext t₅ := hpost₅.mono
  refine ⟨t₅, hr₅, Or.inl ⟨by rw [hpc₅, returnAddress_eq, b8000c668_x1 h₄]; decide,
    t₅.getMem nextAddr, vecCap t₅ (s.getReg .x2 - 80), vecPtr t₅ (s.getReg .x2 - 80), ?_⟩⟩
  exact {
    x2 := by rw [rg .x2 (by decide) (by decide), x2₁]
    x8 := by rw [rg .x8 (by decide) (by decide), b8000c618_x8 h₁]
    x9 := by rw [rg .x9 (by decide) (by decide), b8000c618_x9 h₁]
    x18 := by rw [rg .x18 (by decide) (by decide), b8000c618_x18 h₁]
    kept := fun r hr ↦ by
      rw [rg r (mem_of_mem hr _) (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
    ra := by rw [slot _ (by addr_omega [hb]) (by addr_omega [hb]), b8000c618_m_x2_n8 h₁]
    s0 := by rw [slot _ (by addr_omega [hb]) (by addr_omega [hb]), b8000c618_m_x2_n16 h₁]
    s1 := by rw [slot _ (by addr_omega [hb]) (by addr_omega [hb]), b8000c618_m_x2_n24 h₁]
    s2 := by rw [slot _ (by addr_omega [hb]) (by addr_omega [hb]), b8000c618_m_x2_n32 h₁]
    s3 := by rw [slot _ (by addr_omega [hb]) (by addr_omega [hb]), b8000c618_m_x2_n40 h₁]
    s4 := by rw [slot _ (by addr_omega [hb]) (by addr_omega [hb]), b8000c618_m_x2_n48 h₁]
    s5 := by rw [slot _ (by addr_omega [hb]) (by addr_omega [hb]), b8000c618_m_x2_n56 h₁]
    capM := rfl
    ptrM := by simp only [vecPtr]; congr 1; bv_omega
    lenM := by
      have e := hlen₅
      simp only [vecLen] at e
      rw [show s.getReg .x2 - 64 = s.getReg .x2 - 80 + 16 by bv_omega]; exact e
    next := rfl
    heap := hpost₅.heap
    mono := Nat.le_trans hB hA
    frame := F₅
    room := by omega
    buf := hvec.raw
    fresh := by
      rcases hfr₅ with ⟨ep, ec⟩ | hn
      · rw [ep, ec]
        simp only [vecPtr, vecCap, m8, m0]
        simp only [NewBuf] at hnew₂ ⊢
        rw [hh1] at hnew₂
        omega
      · simp only [NewBuf] at hn ⊢
        omega
    sponge := spongeAt_congr (by addr_omega [hS]) fun y h1 h2 ↦ F₅ y fun i hi hw ↦ by
      rcases hw with hw | hw | hw <;> addr_omega [hw, hi, h1, h2, hS, hss, hsf, hb, hhi₅] }

set_option maxHeartbeats 1000000 in
/-- From `reserve`'s return: to the copy-out with every challenge in the buffer, through the
loop. -/
theorem fill (hD : DuplexSpec) {s u : MachineState} {nx cap ptr : Word} (hpre : SamplesPre s)
    (hpc : u.pc = 0x8000c68c) (hS : Setup s u nx cap ptr) :
    ∃ v, Reaches Image.code u v ∧ ((v.pc = 0x8000c6e4 ∧ AtExit s v nx cap ptr) ∨
      Dead Image.code v) := by
  have hb := bounds hpre
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000c68c_spec hpc (by
    rv_eval [hS.x2]
    valid_access hpre.stack.valid [hb])
  have k₁ := b8000c68c_keeps h₁
  have hm₁ := b8000c68c_mem_same h₁
  have x20₁ : u₁.getReg .x20 = 0 := by
    rw [b8000c68c_x20 h₁, hS.x2, show s.getReg .x2 - 80 + 16 = s.getReg .x2 - 64 by bv_omega,
      hS.lenM]
  have kr (r : Reg) (hr : r ∈ keptRegs) : u₁.getReg r = s.getReg r := by
    rw [k₁ r (mem_of_mem hr _), hS.kept r (by simp [hr])]
  by_cases hn0 : s.getReg .x12 = 0
  · have h0 : (s.getReg .x12).toNat = 0 := by rw [hn0]; rfl
    refine ⟨u₁, hr₁, Or.inl ⟨b8000c68c_pc_taken h₁ (by rw [hS.x9, hn0]), ?_⟩⟩
    exact {
      x2 := by rw [k₁ .x2 (by decide), hS.x2]
      x8 := by rw [k₁ .x8 (by decide), hS.x8]
      x20 := by rw [x20₁, hn0]
      kept := kr
      ra := by rw [hm₁, hS.ra]
      s0 := by rw [hm₁, hS.s0]
      s1 := by rw [hm₁, hS.s1]
      s2 := by rw [hm₁, hS.s2]
      s3 := by rw [hm₁, hS.s3]
      s4 := by rw [hm₁, hS.s4]
      s5 := by rw [hm₁, hS.s5]
      capM := by rw [hm₁, hS.capM]
      ptrM := by rw [hm₁, hS.ptrM]
      next := by rw [hm₁, hS.next]
      frame := (hS.frame.trans (DFrame.of_same hm₁ _) fun _ h ↦ h).mono fun _ h ↦ W0.toW h
      sponge := by
        rw [h0, spongeAt_congr (s := u) (by addr_omega [hpre.self.self]) fun y _ _ ↦ hm₁ y,
          hS.sponge]
        rfl
      elems := by rw [h0]; rfl }
  have hn : 0 < (s.getReg .x12).toNat := by
    rcases Nat.eq_zero_or_pos (s.getReg .x12).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq h) hn0
    · exact h
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000c694_spec
    (b8000c68c_pc_not_taken h₁ (by rw [hS.x9]; exact hn0)) (by
      rv_eval [k₁ .x2 (by decide), hS.x2]
      valid_access hpre.stack.valid [hb])
  have k₂ := b8000c694_keeps h₂
  have hm₂ := b8000c694_mem_same h₂
  have hbuf : Buffer s nx ptr := by
    have hf := hS.fresh
    have hbu := hS.buf
    have hr := hS.room
    have hhi := hS.heap.hi
    have hnx : heapNext u = nx.toNat := by simp only [heapNext, hS.next]
    simp only [NewBuf, Buf] at hf hbu
    exact ⟨by omega, by omega, by simp only [heapEnd] at hhi ⊢; omega, hbu.1⟩
  have B₀ : Body s u₂ nx cap ptr 0 := {
    x2 := by rw [k₂ .x2 (by decide), k₁ .x2 (by decide), hS.x2]
    x8 := by rw [k₂ .x8 (by decide), k₁ .x8 (by decide), hS.x8]
    x9 := by rw [k₂ .x9 (by decide), k₁ .x9 (by decide), hS.x9, Nat.sub_zero]; simp
    x18 := by rw [k₂ .x18 (by decide), k₁ .x18 (by decide), hS.x18]
    x19 := by rw [b8000c694_x19 h₂, k₁ .x18 (by decide), hS.x18]
    x20 := by rw [b8000c694_x20 h₂, x20₁, k₁ .x9 (by decide), hS.x9]; simp
    x21 := by
      rw [b8000c694_x21 h₂, x20₁, k₁ .x2 (by decide), hS.x2, hm₁,
        show s.getReg .x2 - 80 + 8 = s.getReg .x2 - 72 by bv_omega, hS.ptrM]
      bv_omega
    kept := fun r hr ↦ by rw [k₂ r (mem_of_mem hr _), kr r hr]
    ra := by rw [hm₂, hm₁, hS.ra]
    s0 := by rw [hm₂, hm₁, hS.s0]
    s1 := by rw [hm₂, hm₁, hS.s1]
    s2 := by rw [hm₂, hm₁, hS.s2]
    s3 := by rw [hm₂, hm₁, hS.s3]
    s4 := by rw [hm₂, hm₁, hS.s4]
    s5 := by rw [hm₂, hm₁, hS.s5]
    capM := by rw [hm₂, hm₁, hS.capM]
    ptrM := by rw [hm₂, hm₁, hS.ptrM]
    next := by rw [hm₂, hm₁, hS.next]
    frame := (((hS.frame.trans (DFrame.of_same hm₁ _) fun _ h ↦ h).trans
      (DFrame.of_same hm₂ _) fun _ h ↦ h).mono fun _ h ↦ W0.toW h)
    sponge := by
      rw [spongeAt_congr (s := u) (by addr_omega [hpre.self.self]) fun y _ _ ↦ by rw [hm₂, hm₁],
        hS.sponge]
      rfl
    elems := rfl }
  obtain ⟨v, huv, hv⟩ := Reaches.loop
    (fun t ↦ ∃ d, d < (s.getReg .x12).toNat ∧ t.pc = 0x8000c6b4 ∧ Body s t nx cap ptr d)
    (fun t ↦ (t.getReg .x9).toNat)
    (fun t ↦ (t.pc = 0x8000c6e4 ∧ AtExit s t nx cap ptr) ∨ Dead Image.code t)
    (fun t ⟨d, hd, hpct, ht⟩ ↦ by
      obtain ⟨w, htw, ⟨hw, ⟨hpw, hl⟩ | ⟨hpw, he⟩⟩ | hdw⟩ := body hD hpre hbuf hpct ht hd
      · refine Or.inr ⟨w, htw, ⟨d + 1, hl, hpw, hw⟩, ?_⟩
        have hn64 := (s.getReg .x12).isLt
        rw [hw.x9, ht.x9, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)]
        omega
      · exact Or.inl ⟨w, htw, Or.inl ⟨hpw, Body.toExit (he ▸ hw)⟩⟩
      · exact Or.inl ⟨w, htw, Or.inr hdw⟩)
    u₂ ⟨0, hn, b8000c694_pc h₂, B₀⟩
  exact ⟨v, (hr₁.trans hr₂).trans huv, hv⟩

set_option maxHeartbeats 1000000 in
/-- **`Transcript::samples` meets its contract**, given `duplex`'s, `try_allocate_in`'s and
`reserve`'s (with its buffer new or kept). -/
theorem samples_spec (hD : DuplexSpec) (hT : TryAllocZeroedSpec)
    (hR : ReserveFreshSpec 0x80008a10 24 8) : SamplesSpec := by
  intro s hpc hpre
  obtain ⟨u, hsu, ⟨hpcu, nx, cap, ptr, hS⟩ | hd⟩ := setup hT hR hpc hpre
  swap
  · exact ⟨u, hsu, Or.inr hd⟩
  obtain ⟨v, huv, ⟨hpcv, hv⟩ | hd⟩ := fill hD hpre hpcu hS
  swap
  · exact ⟨v, hsu.trans huv, Or.inr hd⟩
  obtain ⟨t, hvt, pc, pres, ec, ep, el, f⟩ := exit hpre hpcv hv
  have ho := hpre.out
  have hS' := hpre.self.self
  have hP := hpre.self.proof
  have hb := bounds hpre
  have hbu := hS.buf
  have hf := hS.fresh
  have hro := hS.room
  have hhi := hS.heap.hi
  have hsf := hpre.selfFree
  have hof := hpre.outFree
  have hpf := hpre.proofFree
  have hstf := hpre.streamFree
  have hnt : t.getMem nextAddr = nx := by
    rw [f _ (by addr_omega [ho, hof]), hv.next]
  have hnu : heapNext t = heapNext u := by simp only [heapNext, hnt, hS.next]
  have Ft : DFrame s t (W s nx) :=
    hv.frame.trans (DFrame.of_memFrame f) fun a h ↦ Or.inl h
  have keepW (y : Word) (n : Nat) (hy : ∀ i < 8, ¬ W s nx (y + BitVec.ofNat 64 i)) :
      t.getMem y = s.getMem y := Ft y hy
  refine ⟨t, hsu.trans (huv.trans hvt), Or.inl ⟨pc, pres, ⟨hnu ▸ hS.heap.lo, hnu ▸ hS.heap.hi⟩,
    hnu ▸ hS.mono, fun T hT' ↦ ?_, ?_⟩⟩
  · refine ⟨_, _, samples_run _ T, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · have := hbu; simp only [RawVecOk, Buf, ec, ep, hnu] at this ⊢; exact this
    · rw [el, ec]; exact hro
    · rw [ec, ep]; simp only [NewBuf, hnu] at hf ⊢; exact hf
    · simp only [vecEs, ep, el]
      rw [(DFrame.of_memFrame f).eListAt fun i hi h ↦ by
        simp only [NewBuf, Buf] at hf hbu
        have := hS.heap.hi
        simp only [heapNext, hS.next] at hf hbu this
        addr_omega [h, hi, hof, hf, hbu, hro, this], hv.elems, hT'.sponge]
    · have hnxe : nx.toNat ≤ heapEnd := by
        have := hS.heap.hi; simp only [heapNext, hS.next] at this; exact this
      have mW (lo : Word) (n : Nat) (h0 : Apart lo n (s.getReg .x10) 24)
          (h1 : Apart lo n (s.getReg .x11 + 8) 336)
          (h2 : Apart lo n (stackLo s samplesStack) samplesStack) (h3 : Outside s lo n)
          (hn : lo.toNat + n ≤ 2 ^ 64) : ∀ i < n, ¬ W s nx (lo + BitVec.ofNat 64 i) :=
        fun i hi h ↦ by
          simp only [W] at h
          rcases h with h | h | h | h | h <;> addr_omega [h, hi, h0, h1, h2, h3, hn, hnxe]
      have hpa := hpre.self.apart
      have mp := mW (s.getReg .x11) 8 (by addr_omega [hpre.outSelf]) (by addr_omega [hS']) (by addr_omega [hpre.selfStack])
        (by addr_omega [hsf]) (by addr_omega [hS'])
      refine ⟨?_, ?_, ?_, ?_⟩
      · show _ = T.proof.stream
        rw [← hT'.stream]
        refine Ft.eListAt_stream mp (mW (proofAt s (s.getReg .x11)) 48 (by addr_omega [hpre.proofOut])
          (by addr_omega [hpa]) (by addr_omega [hpre.proofStack]) hpf (by addr_omega [hP])) ?_
        rcases hpre.self.stream with h0 | hB
        · intro i hi; rw [h0] at hi; omega
        · exact mW (streamPtr s (s.getReg .x11)) _ (by addr_omega [hpre.proofOut]) (by addr_omega [hpa])
            (by addr_omega [hpre.proofStack]) hstf (by addr_omega [hB])
      · show _ = (sqs _ T.sponge).2
        rw [spongeAt_congr (s := v) (by addr_omega [hS']) fun y h1 h2 ↦
          f y (by addr_omega [h1, h2, hpre.outSelf, hS']), hv.sponge, hT'.sponge]
      · show _ = T.streamOffset
        rw [← hT'.streamOffset, keepW _ 0 fun i hi h ↦ by
          simp only [W] at h
          rcases h with h | h | h | h | h <;>
            addr_omega [h, hi, hpre.outSelf, hS', hpre.selfStack, hsf, hnxe]]
      · show _ = T.openingOffset
        rw [← hT'.openingOffset, keepW _ 0 fun i hi h ↦ by
          simp only [W] at h
          rcases h with h | h | h | h | h <;>
            addr_omega [h, hi, hpre.outSelf, hS', hpre.selfStack, hsf, hnxe]]
  · exact Ft.mono fun a h ↦ by
      simp only [W] at h
      rcases h with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by addr_omega [h, hS']))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by simp only [Fresh, heapNext, hnt]; exact h))))

end Rv64Verifier.Transcript.Samples
