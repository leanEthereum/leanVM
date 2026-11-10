import Rv64Verifier.Proofs.Gkr.LayerR11

/-!
# `keccak::verify_layer`: the next weights

`keccak.rs:191-195` at `0x8000fcbc..0x8000fd7c`: a `Vec` of 1600 `E` allocated and reserved at
`f + 1584`, then `lane_weights[j / 64] * eq_z[j % 64]` pushed for each `j` (`push_loop`), the
buffer in `s9` and the length in `s0`.

From `J12` on, `R12..R17` write `mul`'s and the callees' stack, `f + 960`, `f + 1560 .. f + 1608`,
`NEXT` and the heap from `J12`'s `NEXT` (`SW2`), then the result.
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- What `R12..R16` write, from `u`, the heap up to `N`. -/
@[rv_addr] def SW2 (s : MachineState) (H N : Nat) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 2736) 1024 ∨ Within a (s.getReg .x2 - 752) 24 ∨
    Within a (s.getReg .x2 - 152) 48 ∨ Within a nextAddr 8 ∨ (H ≤ a.toNat ∧ a.toNat < N)

theorem sw2_mono {s : MachineState} {H N N' : Nat} (h : N ≤ N') {a : Word} (ha : SW2 s H N a) :
    SW2 s H N' a := by
  simp only [SW2] at ha ⊢
  rcases ha with ha | ha | ha | ha | ha
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ha.1, by omega⟩)))

/-- The `j`-th next weight. -/
def nw (eqZ eqLane : List E) (beta : E) (j : Nat) : E :=
  laneModel eqLane beta (j / 64) * eqZ.getD (j % 64) 0

theorem nextWeights_getD (eqZ eqLane : List E) (beta : E) {j : Nat} (hj : j < 1600) :
    (nextWeightsRust eqZ eqLane beta).getD j 0 = nw eqZ eqLane beta j := by
  unfold nextWeightsRust
  rw [getD_range_map _ _ (show j < keccakBits from hj), getD_range_map _ _ (by omega : j / 64 < 25)]
  rfl

theorem nextWeights_length (eqZ eqLane : List E) (beta : E) :
    (nextWeightsRust eqZ eqLane beta).length = 1600 := by
  simp [nextWeightsRust, keccakBits]

/-- A list of 1600 from its elements. -/
theorem eListAt_of_getD {u : MachineState} {p : Word} {n : Nat} {l : List E} (hl : l.length = n)
    (h : ∀ i < n, eAt u (p + BitVec.ofNat 64 (24 * i)) = l.getD i 0) : eListAt u p n = l := by
  unfold Rv64Verifier.eListAt
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [h i (by simp at h1; omega), List.getD_eq_getElem _ _ h2]

theorem ushr6 {j : Nat} (hj : j < 2 ^ 64) : BitVec.ofNat 64 j >>> 6 = BitVec.ofNat 64 (j / 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt (by omega)]

theorem and63 {j : Nat} (hj : j < 2 ^ 64) : BitVec.ofNat 64 j &&& 63 = BitVec.ofNat 64 (j % 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (63 : Word).toNat = 63 from rfl,
    Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt (by omega)]
  exact Nat.and_two_pow_sub_one_eq_mod j 6

/-! ## The push loop -/

/-- What the push loop writes: `mul`'s result and stack, the buffer. -/
@[rv_addr] def PshW (s : MachineState) (P : Word) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 752) 24 ∨ Within a (s.getReg .x2 - 2736) 1024 ∨ Within a P 38400

/-- What the push loop reads, at its start `w₀`. -/
structure PshC (s w₀ : MachineState) (P eZp eZn : Word) (eqZ : List E) (lw : Nat → E) : Prop where
  pbuf : heapNext s ≤ P.toNat ∧ P.toNat + 38400 ≤ heapNext w₀ ∧ P.toNat % 8 = 0
  ez : eZn.toNat = 0 ∨ heapStart ≤ eZp.toNat ∧ eZp.toNat + 24 * eZn.toNat ≤ P.toNat
  ezA : eZp.toNat % 8 = 0
  ezE : eListAt w₀ eZp eZn.toNat = eqZ
  hH : heapNext w₀ ≤ heapEnd
  lw : ∀ i < 25, eAt w₀ (s.getReg .x2 - 1448 + BitVec.ofNat 64 (24 * i)) = lw i

/-- The push loop at its head `0x8000fd18`, `j` pushed. -/
structure PshN (s w₀ w : MachineState) (P eZp eZn : Word) (eqZ : List E) (lw : Nat → E) (j : Nat) :
    Prop where
  base : Base s w
  frame : DFrame w₀ w (PshW s P)
  x8 : w.getReg .x8 = BitVec.ofNat 64 j
  x9 : w.getReg .x9 = s.getReg .x2 - 1448
  x10 : w.getReg .x10 = BitVec.ofNat 64 j
  x19 : w.getReg .x19 = 1600
  x20 : w.getReg .x20 = P + BitVec.ofNat 64 (24 * j)
  x21 : w.getReg .x21 = eZp
  x22 : w.getReg .x22 = eZn
  x25 : w.getReg .x25 = w₀.getReg .x25
  x26 : w.getReg .x26 = w₀.getReg .x26
  x27 : w.getReg .x27 = w₀.getReg .x27
  el : ∀ i < j, eAt w (P + BitVec.ofNat 64 (24 * i)) = lw (i / 64) * eqZ.getD (i % 64) 0
  lt : j < 1600

/-- The push loop done, at `0x8000fd7c`. -/
structure PshX (s w₀ w : MachineState) (P : Word) (eqZ : List E) (lw : Nat → E) : Prop where
  base : Base s w
  frame : DFrame w₀ w (PshW s P)
  x8 : w.getReg .x8 = 1600
  x25 : w.getReg .x25 = w₀.getReg .x25
  x26 : w.getReg .x26 = w₀.getReg .x26
  x27 : w.getReg .x27 = w₀.getReg .x27
  el : ∀ i < 1600, eAt w (P + BitVec.ofNat 64 (24 * i)) = lw (i / 64) * eqZ.getD (i % 64) 0

set_option maxHeartbeats 16000000 in
theorem push_step (hM : MulSpec) {s w₀ w : MachineState} {P eZp eZn : Word} {eqZ : List E}
    {lw : Nat → E} {j : Nat} (hpre : VerifyLayerPre s) (C : PshC s w₀ P eZp eZn eqZ lw)
    (Q : PshN s w₀ w P eZp eZn eqZ lw j) (hpc : w.pc = 0x8000fd18) :
    ∃ v, Reaches Image.code w v ∧ ((PshN s w₀ v P eZp eZn eqZ lw (j + 1) ∧ v.pc = 0x8000fd18) ∨
      (PshX s w₀ v P eqZ lw ∧ v.pc = 0x8000fd7c) ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have B := Q.base
  have hj := Q.lt
  have hnx := hpre.stack.next
  have hA := hpre.stack.above
  have hP := C.pbuf
  have hez := C.ez
  have hezA := C.ezA
  simp only [stackLo] at hA hnx
  unfold verifyLayerStack at hb hnx hA
  have pw (a : Word) (h : PshW s P a) : ((s.getReg .x2).toNat - 2736 ≤ a.toNat ∧
      a.toNat < (s.getReg .x2).toNat - 1712) ∨ ((s.getReg .x2).toNat - 752 ≤ a.toNat ∧
      a.toNat < (s.getReg .x2).toNat - 728) ∨ (P.toNat ≤ a.toNat ∧ a.toNat < P.toNat + 38400) := by
    simp only [PshW] at h
    rcases h with h | h | h
    · exact Or.inr (Or.inl (by addr_omega [h, hb]))
    · exact Or.inl (by addr_omega [h, hb])
    · exact Or.inr (Or.inr (by addr_omega [h, hP]))
  have hHw := C.hH
  -- `0x8000fd18`: `j % 64` against `eq_z`'s length
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000fd18_spec hpc trivial
  have hjm : BitVec.ofNat 64 j &&& 63 = BitVec.ofNat 64 (j % 64) := and63 (by omega)
  have hjm' : (BitVec.ofNat 64 (j % 64)).toNat = j % 64 := by
    rw [BitVec.toNat_ofNat]; omega
  by_cases hz : j % 64 < eZn.toNat
  swap
  · exact ⟨t₁, hr₁, Or.inr (Or.inr (dead_of_fetch (by
      rw [b8000fd18_pc_taken h₁ (by rw [Q.x22, Q.x10, hjm, hjm']; omega)]; exact trap)))⟩
  have pc₁ := b8000fd18_pc_not_taken h₁ (by rw [Q.x22, Q.x10, hjm, hjm']; omega)
  have k₁ := b8000fd18_keeps h₁
  have hm₁ := b8000fd18_mem_same h₁
  have hez' : heapStart ≤ eZp.toNat ∧ eZp.toNat + 24 * eZn.toNat ≤ P.toNat := by
    rcases hez with h | h
    · omega
    · exact h
  -- `0x8000fd20`: `mul(f + 960, lane_weights[j / 64], eq_z[j % 64])`
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000fd20_spec pc₁ trivial
  have k₂ := b8000fd20_keeps h₂
  have hm₂ := b8000fd20_mem_same h₂
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 1712 := by
    rw [k₂ .x2 (by decide), k₁ .x2 (by decide), B.x2]
  have x10₂ : t₂.getReg .x10 = s.getReg .x2 - 752 := by
    rw [b8000fd20_x10 h₂, k₁ .x2 (by decide), B.x2]; rv_eval []
  have x11₂ : t₂.getReg .x11 = s.getReg .x2 - 1448 + BitVec.ofNat 64 (24 * (j / 64)) := by
    rw [b8000fd20_x11 h₂, k₁ .x9 (by decide), k₁ .x10 (by decide), Q.x9, Q.x10, ushr6 (by omega),
      mul24n]
  have x12₂ : t₂.getReg .x12 = eZp + BitVec.ofNat 64 (24 * (j % 64)) := by
    rw [b8000fd20_x12 h₂, b8000fd18_x11 h₁, k₁ .x21 (by decide), Q.x21, Q.x10, hjm, mul24n]
  have hm12 (a : Word) : t₂.getMem a = w.getMem a := by rw [hm₂, hm₁]
  have B₂ : Base s t₂ := B.same x2₂ hm12
  have F₂ : DFrame w₀ t₂ (PshW s P) := Q.frame.trans (DFrame.of_same hm12 _) fun _ h ↦ h
  have hEV : ValidMemRange eZp (3 * eZn.toNat) := heap_vmr hez'.1 (by omega) hezA
  have hmp : MulPre t₂ := mul_pre hpre x2₂ (B₂.rodata hpre) 752 x10₂ (by decide) (by decide)
    (by decide)
    (by rw [x11₂]; valid_sub hpre.stack.valid [hb, hj])
    (by rw [x11₂]; addr_omega [hb, hj])
    (by rw [x10₂, x11₂]; addr_omega [hb, hj])
    (by rw [x12₂]; valid_sub hEV [hez', hz, hezA])
    (by rw [x12₂]; addr_omega [hb, hA, hez', hz, hP, hHw])
    (by rw [x10₂, x12₂]; addr_omega [hb, hA, hez', hz, hP, hHw])
  obtain ⟨t₃, hr₃, ⟨hpc₃, hpres₃, hpost₃⟩ | hd⟩ := hM.call (hr₁.trans hr₂) (b8000fd20_pc h₂) hmp
  swap
  · exact ⟨_, hr₃, Or.inr (Or.inr hd)⟩
  have G₃ := mul_frame x2₂ hpost₃
  rw [x10₂] at G₃
  have v₃ := hpost₃.value
  have lwj : eAt t₂ (s.getReg .x2 - 1448 + BitVec.ofNat 64 (24 * (j / 64))) = lw (j / 64) := by
    rw [F₂.eAt fun i hi hw ↦ by
        rcases pw _ hw with h | h | h <;> addr_omega [h, hi, hb, hP, hj, hA, hHw],
      C.lw _ (by omega)]
  have ezj : eAt t₂ (eZp + BitVec.ofNat 64 (24 * (j % 64))) = eqZ.getD (j % 64) 0 := by
    rw [F₂.eAt fun i hi hw ↦ by
        rcases pw _ hw with h | h | h <;> addr_omega [h, hi, hb, hP, hez', hz, hA, hHw],
      ← C.ezE, getD_eListAt _ _ hz]
  rw [x10₂, x11₂, x12₂, lwj, ezj] at v₃
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 1712 := (hpres₃.reg .x2).trans x2₂
  have F₃ : DFrame w₀ t₃ (PshW s P) := F₂.trans G₃ fun a h ↦ by
    simp only [PshW]; rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hN₃ : t₃.getMem nextAddr = t₂.getMem nextAddr := G₃ _ fun i hi hw ↦ by
    rcases hw with hw | hw <;> addr_omega [hi, hw, hb, hnx]
  have B₃ : Base s t₃ := B₂.next hpre x2₃
    ⟨by simp only [heapNext, hN₃]; exact B₂.heap.lo, by simp only [heapNext, hN₃]; exact B₂.heap.hi⟩
    (by simp only [heapNext, hN₃]; exact le_refl _) G₃ fun a h ↦ by
      refine ⟨Or.inr (Or.inr (Or.inl ?_)), ?_⟩ <;> rcases h with h | h <;> addr_omega [h, hb]
  have cs (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x25, .x26, .x27]) :
      t₃.getReg r = t₂.getReg r :=
    hpres₃.reg r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have r₂ (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x19, .x20, .x21, .x22, .x25, .x26, .x27]) :
      t₂.getReg r = w.getReg r := by
    rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have x20₃ : t₃.getReg .x20 = P + BitVec.ofNat 64 (24 * j) := by
    rw [cs .x20 (by decide), r₂ .x20 (by decide), Q.x20]
  have hNw : heapNext w₀ ≤ heapNext t₃ := by
    have : t₃.getMem nextAddr = w₀.getMem nextAddr := F₃ _ fun i hi hw ↦ by
      rcases pw _ hw with h | h | h <;> addr_omega [h, hi, hb, hnx, hP, hHw]
    simp only [heapNext, this]; exact le_refl _
  -- `0x8000fd54`: the product pushed
  have hPV : ValidMemRange P 4800 := heap_vmr (by have := B.heap.lo; omega) (by omega) hP.2.2
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000fd54_spec
    (by rw [hpc₃, returnAddress_eq, b8000fd20_x1 h₂]; decide) (by
      rv_eval [x2₃, x20₃]
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | valid_access hPV [hP, hj]
        | addr_omega [hb, hA, hP, hj, hHw])
  have k₄ := b8000fd54_keeps h₄
  have f₄ := b8000fd54_frame h₄ (by rw [x20₃]; addr_omega [hP, hj, hHw])
  rw [x20₃] at f₄
  have x2₄ : t₄.getReg .x2 = s.getReg .x2 - 1712 := (k₄ .x2 (by decide)).trans x2₃
  have hN₄ : t₄.getMem nextAddr = t₃.getMem nextAddr := f₄ _ (by addr_omega [hP, hj, hHw])
  have B₄ : Base s t₄ := B₃.next hpre x2₄
    ⟨by simp only [heapNext, hN₄]; exact B₃.heap.lo, by simp only [heapNext, hN₄]; exact B₃.heap.hi⟩
    (by simp only [heapNext, hN₄]; exact le_refl _) (DFrame.of_memFrame f₄) fun a h ↦ by
      refine ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))), ?_⟩
      · addr_omega [h, hP, hj]
      · simp only [heapNext, hN₄]; addr_omega [h, hP, hj, hNw]
      · addr_omega [h, hb, hP, hj, hA, hHw]
  have F₄ : DFrame w₀ t₄ (PshW s P) := F₃.trans (DFrame.of_memFrame f₄) fun a h ↦ by
    simp only [PshW]; exact Or.inr (Or.inr (by addr_omega [h, hP, hj]))
  have enew : eAt t₄ (P + BitVec.ofNat 64 (24 * j)) = lw (j / 64) * eqZ.getD (j % 64) 0 := by
    apply eAt_eq_of_limbs
    rw [← v₃]; simp only [limbs_eAt]
    have n0 := b8000fd54_m_x20_0 h₄
    have n8 := b8000fd54_m_x20_8 h₄
    have n16 := b8000fd54_m_x20_16 h₄
    rw [x20₃, x2₃] at n0 n8 n16
    rv_eval [] at n0 n8 n16
    rv_eval [n0, n8, n16]
  have hnot (i : Nat) (hi : i < j) : eAt t₄ (P + BitVec.ofNat 64 (24 * i)) =
      eAt w (P + BitVec.ofNat 64 (24 * i)) := by
    rw [f₄.eAt (by addr_omega [hP, hj, hi]) (by addr_omega [hP, hj, hi]),
      G₃.eAt fun k hk hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hk, hb, hP, hj, hi, hA, hHw]]
    unfold Rv64Verifier.eAt; rw [hm12, hm12, hm12]
  have el₄ (i : Nat) (hi : i < j + 1) :
      eAt t₄ (P + BitVec.ofNat 64 (24 * i)) = lw (i / 64) * eqZ.getD (i % 64) 0 := by
    by_cases hij : i = j
    · rw [hij, enew]
    · rw [hnot i (by omega), Q.el i (by omega)]
  have x18₃ : t₃.getReg .x18 = BitVec.ofNat 64 (j + 1) := by
    rw [cs .x18 (by decide), b8000fd20_x18 h₂, k₁ .x10 (by decide), Q.x10, ofNat_succ]
  have x19₃ : t₃.getReg .x19 = 1600 := by rw [cs .x19 (by decide), r₂ .x19 (by decide), Q.x19]
  have x8₄ : t₄.getReg .x8 = BitVec.ofNat 64 (j + 1) := by
    rw [b8000fd54_x8 h₄, cs .x8 (by decide), r₂ .x8 (by decide), Q.x8, ofNat_succ]
  have kr (r : Reg) (hr : r ∈ [Reg.x9, .x21, .x22, .x25, .x26, .x27]) : t₄.getReg r = w.getReg r := by
    rw [k₄ r (mem_of_mem hr _), cs r (mem_of_mem hr _), r₂ r (mem_of_mem hr _)]
  by_cases hl : j + 1 < 1600
  · refine ⟨t₄, hr₃.trans hr₄, Or.inl ⟨{
      base := B₄
      frame := F₄
      x8 := x8₄
      x9 := by rw [kr .x9 (by decide), Q.x9]
      x10 := by rw [b8000fd54_x10 h₄, x18₃]
      x19 := by rw [k₄ .x19 (by decide), x19₃]
      x20 := by rw [b8000fd54_x20 h₄, x20₃, st24]
      x21 := by rw [kr .x21 (by decide), Q.x21]
      x22 := by rw [kr .x22 (by decide), Q.x22]
      x25 := by rw [kr .x25 (by decide), Q.x25]
      x26 := by rw [kr .x26 (by decide), Q.x26]
      x27 := by rw [kr .x27 (by decide), Q.x27]
      el := el₄
      lt := hl }, b8000fd54_pc_taken h₄ ?_⟩⟩
    rw [x18₃, x19₃]
    intro h; have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, show (1600 : Word).toNat = 1600 from rfl] at this; omega
  · refine ⟨t₄, hr₃.trans hr₄, Or.inr (Or.inl ⟨{
      base := B₄
      frame := F₄
      x8 := by rw [x8₄, show j + 1 = 1600 by omega]; rfl
      x25 := by rw [kr .x25 (by decide), Q.x25]
      x26 := by rw [kr .x26 (by decide), Q.x26]
      x27 := by rw [kr .x27 (by decide), Q.x27]
      el := fun i hi ↦ el₄ i (by omega) }, b8000fd54_pc_not_taken h₄ ?_⟩)⟩
    rw [x18₃, x19₃, show j + 1 = 1600 by omega]; rfl

theorem push_loop (hM : MulSpec) {s w₀ : MachineState} {P eZp eZn : Word} {eqZ : List E}
    {lw : Nat → E} (hpre : VerifyLayerPre s) (C : PshC s w₀ P eZp eZn eqZ lw) :
    ∀ n j w, j + n = 1600 → PshN s w₀ w P eZp eZn eqZ lw j → w.pc = 0x8000fd18 →
      ∃ v, Reaches Image.code w v ∧ ((PshX s w₀ v P eqZ lw ∧ v.pc = 0x8000fd7c) ∨ Dead Image.code v)
  | 0, j, w, hn, Q, _ => absurd Q.lt (by omega)
  | n + 1, j, w, hn, Q, hpc => by
    obtain ⟨v, hr, ⟨Q', hpc'⟩ | ⟨X, hpc'⟩ | hd⟩ := push_step hM hpre C Q hpc
    · obtain ⟨t, hr', ht⟩ := push_loop hM hpre C n (j + 1) v (by omega) Q' hpc'
      exact ⟨t, hr.trans hr', ht⟩
    · exact ⟨v, hr, Or.inl ⟨X, hpc'⟩⟩
    · exact ⟨v, hr, Or.inr hd⟩

/-! ## From `J12` -/

/-- After the next weights, at `0x8000fd7c`: their buffer in `s9`, its length in `s0`. -/
structure J13 (s u v : MachineState) (eqZ eqLane : List E) (beta : E) : Prop where
  pc : v.pc = 0x8000fd7c
  base : Base s v
  mono : heapNext u ≤ heapNext v
  frame : DFrame u v (SW2 s (heapNext u) (heapNext v))
  x8 : v.getReg .x8 = 1600
  wbuf : heapNext u ≤ (v.getReg .x25).toNat ∧ (v.getReg .x25).toNat + 38400 ≤ heapNext v ∧
    (v.getReg .x25).toNat % 8 = 0
  wE : ∀ i < 1600, eAt v (v.getReg .x25 + BitVec.ofNat 64 (24 * i)) = nw eqZ eqLane beta i
  x26 : v.getReg .x26 = u.getReg .x26
  x27 : v.getReg .x27 = 0x3333333333333334

set_option maxHeartbeats 16000000 in
theorem next_weights (hA : AllocSpec) (hR : ReserveFreshSpec 0x80008a10 24 8) (hM : MulSpec)
    {s u : MachineState} {mu point eqZ eqLane t : List E} {beta : E} (hpre : VerifyLayerPre s)
    (J : J12 s u mu point eqZ eqLane t beta) :
    ∃ v, Reaches Image.code u v ∧ (J13 s u v eqZ eqLane beta ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have B := J.base
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  simp only [stackLo] at hnx hab
  unfold verifyLayerStack at hb hnx hab
  have hHu := B.heap.hi
  have hsu := B.mono
  have hH0 := hpre.heap.lo
  -- `0x8000fcbc`: `alloc(8, 38400)`
  obtain ⟨t₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b8000fcbc_spec J.pc trivial
  have k₀ := b8000fcbc_keeps h₀
  have hm₀ := b8000fcbc_mem_same h₀
  have x2₀ : t₀.getReg .x2 = s.getReg .x2 - 1712 := (k₀ .x2 (by decide)).trans B.x2
  have B₀ : Base s t₀ := B.same x2₀ hm₀
  have hN₀ : heapNext t₀ = heapNext u := by simp only [heapNext, hm₀]
  obtain ⟨t₁, hr₁, ⟨hpc₁, hp₁, A⟩ | hd⟩ := hA.call hr₀ (b8000fcbc_pc h₀)
    ⟨B₀.heap, by rw [b8000fcbc_x10 h₀]; decide⟩
  swap
  · exact ⟨_, hr₁, Or.inr hd⟩
  have hal := A.aligned
  have hab₁ := A.above
  have hnx₁ := A.next
  rw [b8000fcbc_x10 h₀] at hal
  rw [b8000fcbc_x11 h₀] at hnx₁
  simp only [show (8 : Word).toNat = 8 from rfl] at hal
  simp only [show (38400 : Word).toNat = 38400 from rfl] at hnx₁
  rw [hN₀] at hab₁
  have F₁ : DFrame t₀ t₁ (Within · nextAddr 8) := fun a ha ↦ A.mem a fun h ↦
    ha 0 (by decide) (by rw [h, add_ofNat_zero]; addr_omega [])
  have x2₁ : t₁.getReg .x2 = s.getReg .x2 - 1712 := (hp₁.reg .x2).trans x2₀
  have B₁ : Base s t₁ := B₀.next hpre x2₁ A.heap (by omega) F₁ fun a h ↦
    ⟨Or.inr (Or.inr (Or.inr (Or.inl h))), by addr_omega [h, hb, hnx]⟩
  -- `0x8000fcd0`: `eq_z`, the null check
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000fcd0_spec
    (by rw [hpc₁, returnAddress_eq, b8000fcbc_x1 h₀]; decide) (by
      rv_eval [x2₁]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₂ := b8000fcd0_keeps h₂
  have hm₂ := b8000fcd0_mem_same h₂
  have hne : t₁.getReg .x10 ≠ 0 := fun h ↦ by
    rw [h, show (0 : Word).toNat = 0 from rfl] at hab₁
    simp only [heapStart] at hH0
    omega
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 1712 := (k₂ .x2 (by decide)).trans x2₁
  have B₂ : Base s t₂ := B₁.same x2₂ hm₂
  have m1 (a : Word) (ha : a ≠ nextAddr) : t₁.getMem a = u.getMem a := by rw [A.mem a ha, hm₀]
  have x21₂ : t₂.getReg .x21 = u.getMem (s.getReg .x2 - 1632) := by
    rw [b8000fcd0_x21 h₂, x2₁]; rv_eval []; exact m1 _ (by addr_omega [hb, hnx])
  have x22₂ : t₂.getReg .x22 = u.getMem (s.getReg .x2 - 1640) := by
    rw [b8000fcd0_x22 h₂, x2₁]; rv_eval []; exact m1 _ (by addr_omega [hb, hnx])
  -- `0x8000fcdc`: the `Vec` `{1600, ptr, 0}` at `f + 1584`, `reserve(1600)`
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000fcdc_spec
    (b8000fcd0_pc_not_taken h₂ hne) (by
      rv_eval [x2₂]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₃ := b8000fcdc_keeps h₃
  have f₃ := b8000fcdc_frame h₃ (by rw [x2₂]; addr_omega [hb])
  rw [x2₂] at f₃
  rv_eval [] at f₃
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 1712 := (k₃ .x2 (by decide)).trans x2₂
  have B₃ : Base s t₃ := B₂.slots hpre x2₃ f₃ (by addr_omega [hb]) (by addr_omega [hb])
  have n0 := b8000fcdc_m_x2_1584 h₃
  have n8 := b8000fcdc_m_x2_1592 h₃
  have n16 := b8000fcdc_m_x2_1600 h₃
  rw [x2₂] at n0 n8 n16
  rw [k₂ .x10 (by decide)] at n8
  rv_eval [] at n0 n8 n16
  have x10₃ : t₃.getReg .x10 = s.getReg .x2 - 128 := by rw [b8000fcdc_x10 h₃, x2₂]; rv_eval []
  have x11₃ : t₃.getReg .x11 = 1600 := b8000fcdc_x11 h₃
  have hN₃ : heapNext t₃ = heapNext t₁ := by
    simp only [heapNext]
    rw [f₃ _ (by addr_omega [hb, hnx]), hm₂]
  have pre : ReservePre 24 8 t₃ := {
    heap := B₃.heap
    self := by rw [x10₃]; exact slot_vmr hpre (by decide) (by decide) (by decide)
    vec := {
      raw := by
        simp only [RawVecOk, Buf, vecPtr, vecCap, x10₃]
        rv_eval [n0, n8]
        rw [hN₃, hnx₁]
        simp only [heapStart] at hH0 ⊢
        omega
      len := by simp only [vecLen, vecCap, x10₃]; rv_eval [n0, n16]; decide }
    stack := hpre.stack.sub 1712 x2₃ (by unfold verifyLayerStack; decide) (by decide) (by decide)
      (by decide) (by decide)
    selfFree := by rw [x10₃]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    selfStack := by rw [x10₃]; simp only [stackLo, x2₃]; addr_omega [hb] }
  obtain ⟨t₄, hr₄, ⟨hpc₄, hp₄, R, Rf⟩ | hd⟩ := hR.call hr₃ (b8000fcdc_pc h₃) pre
  swap
  · exact ⟨_, hr₁.trans (hr₂.trans hr₄), Or.inr hd⟩
  have x2₄ : t₄.getReg .x2 = s.getReg .x2 - 1712 := (hp₄.reg .x2).trans x2₃
  have rcap := R.cap
  have rlen := R.len
  have rraw := R.vec.raw
  have rH := R.heap.hi
  simp only [x10₃, x11₃, vecLen, vecCap, vecPtr, RawVecOk, Buf] at rcap rlen rraw Rf
  rv_eval [n0, n8, n16] at rcap rlen rraw Rf
  obtain ⟨P, hPd⟩ : ∃ P, t₄.getMem (s.getReg .x2 - 120) = P := ⟨_, rfl⟩
  rw [hPd] at rraw Rf
  have hip : heapNext u ≤ P.toNat ∧ P.toNat + 38400 ≤ heapNext t₄ := by
    rcases Rf with ⟨e1, e2⟩ | ⟨-, h0 | ⟨h1, h2⟩⟩
    · rw [e1]; have := R.mono; rw [hN₃] at this; omega
    · omega
    · rw [hN₃] at h1; omega
  have B₄ : Base s t₄ := B₃.next hpre x2₄ R.heap R.mono (DFrame.of_byteFrame R.frame)
    fun a ha ↦ cframe_lw hpre B₃ 128 (by decide) (by decide) (by decide) R.heap x10₃ a ha
  have F₄ : DFrame u t₄ (SW2 s (heapNext u) (heapNext t₄)) :=
    ((((DFrame.of_same hm₀ _).trans F₁ fun a h ↦ Or.inr (Or.inr (Or.inr (Or.inl h)))).trans
      (DFrame.of_same hm₂ _) fun _ h ↦ h).trans (DFrame.of_memFrame f₃) fun a h ↦
        Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))).trans
      (DFrame.of_byteFrame R.frame) fun a h ↦ by
        simp only [Fresh, stackLo, x10₃, x2₃] at h ⊢
        rcases h with h | h | h | h
        · exact Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))
        · exact Or.inl (by addr_omega [h, hb])
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by rw [hN₃] at h; omega, h.2⟩)))
  -- `0x8000fcfc`: the loop's registers
  obtain ⟨w₀, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000fcfc_spec
    (by rw [hpc₄, returnAddress_eq, b8000fcdc_x1 h₃]; decide) (by
      rv_eval [x2₄]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₅ := b8000fcfc_keeps h₅
  have hm₅ := b8000fcfc_mem_same h₅
  have x2₅ : w₀.getReg .x2 = s.getReg .x2 - 1712 := (k₅ .x2 (by decide)).trans x2₄
  have B₅ : Base s w₀ := B₄.same x2₅ hm₅
  have hN₅ : heapNext w₀ = heapNext t₄ := by simp only [heapNext, hm₅]
  have F₅ : DFrame u w₀ (SW2 s (heapNext u) (heapNext w₀)) := by
    rw [hN₅]; exact F₄.trans (DFrame.of_same hm₅ _) fun _ h ↦ h
  have keep (y : Word) (hy : ∀ i < 8, ¬ SW2 s (heapNext u) (heapNext w₀) (y + BitVec.ofNat 64 i)) :
      w₀.getMem y = u.getMem y := F₅ y hy
  have ezB := J.ezBuf
  simp only [NewBuf] at ezB
  have hZ (i : Nat) (hi : i < 24 * (u.getMem (s.getReg .x2 - 1640)).toNat) :
      ¬ SW2 s (heapNext u) (heapNext w₀) (u.getMem (s.getReg .x2 - 1632) + BitVec.ofNat 64 i) := by
    intro hw
    simp only [SW2] at hw
    rcases ezB.2 with h0 | ⟨z1, z2⟩
    · omega
    rcases hw with hw | hw | hw | hw | hw <;> addr_omega [hw, hi, z1, z2, hb, hab, hnx, hHu, hsu, hN₅, rH]
  have hez : eListAt w₀ (u.getMem (s.getReg .x2 - 1632)) (u.getMem (s.getReg .x2 - 1640)).toNat =
      eqZ := by
    rw [F₅.eListAt hZ, J.ezE]
  have C : PshC s w₀ P (u.getMem (s.getReg .x2 - 1632)) (u.getMem (s.getReg .x2 - 1640)) eqZ
      (laneModel eqLane beta) := {
    pbuf := ⟨by omega, by rw [hN₅]; exact hip.2, rraw.1⟩
    ez := by
      rcases ezB.2 with h0 | ⟨z1, z2⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by simp only [heapStart] at hH0 ⊢; omega, by omega⟩
    ezA := ezB.1
    ezE := hez
    hH := by rw [hN₅]; exact rH
    lw := fun i hi ↦ by
      rw [F₅.eAt fun k hk hw ↦ by
        simp only [SW2] at hw
        rcases hw with hw | hw | hw | hw | hw <;> addr_omega [hw, hk, hi, hb, hab, hnx, hHu, hN₅, rH]]
      exact J.lw i hi }
  have x20₅ : w₀.getReg .x20 = P + BitVec.ofNat 64 (24 * 0) := by
    rw [Nat.mul_zero, add_ofNat_zero, b8000fcfc_x20 h₅, x2₄]; rv_eval [rlen, hPd]
  have Q₀ : PshN s w₀ w₀ P (u.getMem (s.getReg .x2 - 1632)) (u.getMem (s.getReg .x2 - 1640)) eqZ
      (laneModel eqLane beta) 0 := {
    base := B₅
    frame := DFrame.refl _ _
    x8 := by rw [b8000fcfc_x8 h₅, x2₄]; rv_eval [rlen]
    x9 := by
      rw [k₅ .x9 (by decide), hp₄.reg .x9, k₃ .x9 (by decide), k₂ .x9 (by decide), hp₁.reg .x9,
        k₀ .x9 (by decide), J.x9]
    x10 := b8000fcfc_x10 h₅
    x19 := by rw [k₅ .x19 (by decide), hp₄.reg .x19, b8000fcdc_x19 h₃]
    x20 := x20₅
    x21 := by rw [k₅ .x21 (by decide), hp₄.reg .x21, k₃ .x21 (by decide), x21₂]
    x22 := by rw [k₅ .x22 (by decide), hp₄.reg .x22, k₃ .x22 (by decide), x22₂]
    x25 := rfl
    x26 := rfl
    x27 := rfl
    el := fun i hi ↦ absurd hi (Nat.not_lt_zero i)
    lt := by decide }
  obtain ⟨v, hr₆, ⟨X, hpc₆⟩ | hd⟩ := push_loop hM hpre C 1600 0 w₀ rfl Q₀ (b8000fcfc_pc h₅)
  swap
  · exact ⟨v, hr₁.trans (hr₂.trans (hr₄.trans (hr₅.trans hr₆))), Or.inr hd⟩
  have hNv : heapNext v = heapNext w₀ := by
    have : v.getMem nextAddr = w₀.getMem nextAddr := X.frame _ fun i hi hw ↦ by
      simp only [PshW] at hw
      rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hb, hnx, hip, rH]
    simp only [heapNext, this]
  have x25₅ : w₀.getReg .x25 = P := by rw [b8000fcfc_x25 h₅, x2₄]; rv_eval [hPd]
  have rg (r : Reg) (hr : r ∈ [Reg.x26, .x27]) : w₀.getReg r = u.getReg r := by
    rw [k₅ r (mem_of_mem hr _), hp₄.reg r (mem_of_mem hr _), k₃ r (mem_of_mem hr _),
      k₂ r (mem_of_mem hr _), hp₁.reg r (mem_of_mem hr _), k₀ r (mem_of_mem hr _)]
  refine ⟨v, hr₁.trans (hr₂.trans (hr₄.trans (hr₅.trans hr₆))), Or.inl {
    pc := hpc₆
    base := X.base
    mono := by rw [hNv, hN₅]; have := R.mono; rw [hN₃] at this; omega
    frame := (F₅.mono fun a h ↦ sw2_mono (by rw [hNv]) h).trans X.frame fun a h ↦ by
      simp only [PshW] at h
      rcases h with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [h, hip], by
          rw [hNv, hN₅]; addr_omega [h, hip]⟩)))
    x8 := X.x8
    wbuf := by rw [X.x25, x25₅, hNv, hN₅]; exact ⟨hip.1, hip.2, rraw.1⟩
    wE := fun i hi ↦ by rw [X.x25, x25₅]; exact X.el i hi
    x26 := by rw [X.x26, rg .x26 (by decide)]
    x27 := by rw [X.x27, rg .x27 (by decide), J.x27] }⟩

end Rv64Verifier.Gkr.Layer
