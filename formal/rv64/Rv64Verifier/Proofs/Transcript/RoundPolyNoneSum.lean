import Rv64Verifier.Proofs.Transcript.RoundPolyNoneTail
import Rv64Verifier.Proofs.Transcript.RoundPolySomeSum

/-!
# `sumcheck_round_poly`'s `None` path: the buffer and `claim` plus the tail's sum

`0x8000c4ec`: 48 bytes from the allocator (`a0`), the claim's limbs into `a1`, `a2`, `a3`, XORed
with the tail's sum (the loop at `0x8000c554`) (`AtHeadN`, at `0x8000c580`).
-/

namespace Rv64Verifier.Transcript.RoundPoly
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F44
  Rv64Verifier.Contracts LeanVM.Protocol.Verifier
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- The second loop's accumulator after `k` elements. -/
structure Acc2 (u : MachineState) (p : Word) (k : Nat) (t : MachineState) : Prop where
  x16 : t.getReg .x16 = (Model.limbs (sumE (eListAt u p k))).1
  x15 : t.getReg .x15 = (Model.limbs (sumE (eListAt u p k))).2.1
  x14 : t.getReg .x14 = (Model.limbs (sumE (eListAt u p k))).2.2
  kept : ∀ r ∈ loop2Kept, t.getReg r = u.getReg r
  mem : ∀ a, t.getMem a = u.getMem a

theorem step2 {u t : MachineState} {p : Word} {n k : Nat} (hk : k < n)
    (hal : p.toNat % 8 = 0) (hlo : heapStart ≤ p.toNat) (hhi : p.toNat + 24 * n ≤ heapEnd)
    (hpc : t.pc = 0x8000c554) (x17 : t.getReg .x17 = p + 16 + BitVec.ofNat 64 (24 * k))
    (x5 : t.getReg .x5 = p + 16 + BitVec.ofNat 64 (24 * n)) (h : Acc2 u p k t) :
    ∃ t', Reaches Image.code t t' ∧ Acc2 u p (k + 1) t' ∧
      t'.getReg .x17 = p + 16 + BitVec.ofNat 64 (24 * (k + 1)) ∧
      t'.getReg .x5 = p + 16 + BitVec.ofNat 64 (24 * n) ∧
      t'.pc = if k + 1 < n then 0x8000c554 else 0x8000c574 := by
  obtain ⟨t', htt, h'⟩ := Sym.BlockSpec.reaches b8000c554_spec hpc (by
    rv_eval [x17]
    and_intros <;> (refine Samples.heap_valid ?_ ?_ ?_ <;> addr_omega [hal, hlo, hhi, hk]))
  have k' := b8000c554_keeps h'
  have hs := eListAt_sum_succ u p k
  have hp24 : p.toNat + 16 + 24 * n < 2 ^ 64 := by simp only [heapEnd] at hhi; omega
  refine ⟨t', htt, ⟨?_, ?_, ?_, fun r hr ↦ (k' r (mem_of_mem hr _)).trans (h.kept r hr),
    fun a ↦ (b8000c554_mem_same h' a).trans (h.mem a)⟩,
    by rw [b8000c554_x17 h', x17, loop_step], (k' .x5 (by decide)).trans x5, ?_⟩
  · rw [b8000c554_x16 h', x17, off0, h.mem, h.x16, hs, BitVec.xor_comm]
  · rw [b8000c554_x15 h', x17, off8, h.mem, h.x15, hs, BitVec.xor_comm]
  · rw [b8000c554_x14 h', x17, off16, h.mem, h.x14, hs, BitVec.xor_comm]
  · by_cases hl : k + 1 < n
    · rw [ite_eq_left hl]
      exact b8000c554_pc_taken h' (by rw [x17, x5, loop_step]; exact loop_ne p hl hp24)
    · rw [ite_eq_right hl]
      exact b8000c554_pc_not_taken h' (by rw [x17, x5, loop_step, show k + 1 = n by omega])

/-- The loop at `0x8000c554` over the `n` elements from `p`: their sum's limbs in `a6`, `a5`,
`a4`. -/
theorem sumLoop2 {u : MachineState} {p : Word} {n : Nat} (hpc : u.pc = 0x8000c554) (hn : 0 < n)
    (hal : p.toNat % 8 = 0) (hlo : heapStart ≤ p.toNat) (hhi : p.toNat + 24 * n ≤ heapEnd)
    (x17 : u.getReg .x17 = p + 16) (x5 : u.getReg .x5 = p + 16 + BitVec.ofNat 64 (24 * n))
    (x14 : u.getReg .x14 = 0) (x15 : u.getReg .x15 = 0) (x16 : u.getReg .x16 = 0) :
    ∃ v, Reaches Image.code u v ∧ v.pc = 0x8000c574 ∧ Acc2 u p n v := by
  have h0 : Model.limbs (sumE (eListAt u p 0)) = (0, 0, 0) := limbs_zero
  have h24 : 24 * n < 2 ^ 64 := by simp only [heapEnd] at hhi; omega
  refine Reaches.loop
    (fun t ↦ ∃ k, k < n ∧ t.pc = 0x8000c554 ∧ t.getReg .x17 = p + 16 + BitVec.ofNat 64 (24 * k) ∧
      t.getReg .x5 = p + 16 + BitVec.ofNat 64 (24 * n) ∧ Acc2 u p k t)
    (fun t ↦ (t.getReg .x5 - t.getReg .x17).toNat)
    (fun t ↦ t.pc = 0x8000c574 ∧ Acc2 u p n t) (fun t ⟨k, hk, hpct, h17, h5, hA⟩ ↦ ?_) u
    ⟨0, hn, hpc, by rw [x17]; simp, x5, ⟨by rw [x16, h0], by rw [x15, h0], by rw [x14, h0],
      fun _ _ ↦ rfl, fun _ ↦ rfl⟩⟩
  obtain ⟨t', htt, hA', n17, n5, npc⟩ := step2 hk hal hlo hhi hpct h17 h5 hA
  by_cases hl : k + 1 < n
  · rw [ite_eq_left hl] at npc
    refine Or.inr ⟨t', htt, ⟨k + 1, hl, npc, n17, n5, hA'⟩, ?_⟩
    rw [n17, n5, h17, h5, loop_meas p (by omega) h24, loop_meas p (by omega) h24]
    omega
  · rw [ite_eq_right hl] at npc
    rw [show k + 1 = n by omega] at hA'
    exact Or.inl ⟨t', htt, npc, hA'⟩

theorem b8000c510_x5' {s t : MachineState} (h : b8000c510.Holds s t)
    (hb : (s.getReg .x21).toNat + 16 + 24 * (s.getReg .x9).toNat < 2 ^ 64) :
    t.getReg .x5 = s.getReg .x21 + 16 + BitVec.ofNat 64 (24 * (s.getReg .x9).toNat) :=
  h.reg_eq .x5 rfl (by rv_eval []; exact end_ptr16 _ _ hb)

/-- At `0x8000c580`: the buffer `a0` (48 bytes, after `NEXT` at the tail's return), the limbs of
`claim` plus the tail's sum in `a1`, `a2`, `a3`. -/
structure AtHeadN (s w : MachineState) : Prop where
  fr : Fr s w
  x11 : w.getReg .x11 = (Model.limbs (eAt s (s.getReg .x13) +
    sumE (eListAt w (w.getReg .x21) (w.getReg .x9).toNat))).1
  x12 : w.getReg .x12 = (Model.limbs (eAt s (s.getReg .x13) +
    sumE (eListAt w (w.getReg .x21) (w.getReg .x9).toNat))).2.1
  x13 : w.getReg .x13 = (Model.limbs (eAt s (s.getReg .x13) +
    sumE (eListAt w (w.getReg .x21) (w.getReg .x9).toNat))).2.2
  bAl : (w.getReg .x10).toNat % 8 = 0
  bNext : heapNext w = (w.getReg .x10).toNat + 48
  bLo : heapNext s ≤ (w.getReg .x10).toNat
  room : (w.getReg .x9).toNat ≤ (w.getReg .x23).toNat
  buf : (w.getReg .x21).toNat % 8 = 0 ∧ ((w.getReg .x23).toNat * 24 = 0 ∨
    heapNext s ≤ (w.getReg .x21).toNat ∧
      (w.getReg .x21).toNat + (w.getReg .x23).toNat * 24 ≤ (w.getReg .x10).toNat)
  value : ∀ T, TranscriptAt s (s.getReg .x11) T → ∃ x T₁ T',
    TM.nextScalar.run T = some (x, T₁) ∧
    Model.limbs x = (w.getReg .x20, w.getReg .x19, w.getReg .x22) ∧
    (TM.nextScalars ((s.getReg .x12).toNat - 2)).run T₁ =
      some (eListAt w (w.getReg .x21) (w.getReg .x9).toNat, T') ∧
    TranscriptAt w (s.getReg .x11) T'

/-- What the second sum keeps. -/
def sumKept2 : List Reg :=
  [.x1, .x2, .x8, .x9, .x10, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

theorem limbs_claim_sum (c : E) (l : List E) (a b d : Word)
    (h : Model.limbs (sumE l) = (a, b, d)) (c0 c1 c2 : Word) (hc : Model.limbs c = (c0, c1, c2)) :
    Model.limbs (c + sumE l) = (a ^^^ c0, b ^^^ c1, d ^^^ c2) := by
  rw [limbs_add, h, hc]
  simp only [Prod.mk.injEq]
  exact ⟨BitVec.xor_comm _ _, BitVec.xor_comm _ _, BitVec.xor_comm _ _⟩

set_option maxHeartbeats 2000000 in
theorem noneSum (hA : AllocSpec) {s v : MachineState} (hpre : RoundPolyPre s)
    (hpc : v.pc = 0x8000c4ec) (h : TailN s v) :
    ∃ w, Reaches Image.code v w ∧ ((w.pc = 0x8000c580 ∧ AtHeadN s w) ∨ Done s w) := by
  have hb := bounds hpre
  have hS : 80 ≤ (s.getReg .x2).toNat := by addr_omega [hb]
  have hst := hpre.stack
  have hcl := hpre.claim
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000c4ec_spec hpc trivial
  have k₁ := b8000c4ec_keeps h₁
  have hm₁ := b8000c4ec_mem_same h₁
  have F₁ : Fr s v₁ := h.fr.same hS (fun r hr ↦ k₁ r (mem_of_mem hr _)) hm₁
  obtain ⟨v₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ :=
    hA.call hr₁ (b8000c4ec_pc h₁) ⟨F₁.heap, by rw [b8000c4ec_x10 h₁]; decide⟩
  swap
  · exact ⟨v₂, hr₂, Or.inr (Or.inr hd)⟩
  have hB0 : heapNext v₁ ≤ (v₂.getReg .x10).toNat := hpost₂.above
  have hBn : heapNext v₂ = (v₂.getReg .x10).toNat + 48 := by
    rw [hpost₂.next, b8000c4ec_x11 h₁]; rfl
  have hBa : (v₂.getReg .x10).toNat % 8 = 0 := by
    have := hpost₂.aligned; rw [b8000c4ec_x10 h₁] at this; exact this
  have hlo := F₁.heap.lo
  have hmono := F₁.mono
  have hne : v₂.getReg .x10 ≠ 0 := fun h0 ↦ by
    rw [h0] at hB0; simp only [heapStart] at hlo; simp at hB0; omega
  have D₂ : DFrame v₁ v₂ (Within · nextAddr 8) :=
    fun a ha ↦ hpost₂.mem a fun he ↦ ha 0 (by decide) (by rw [add_ofNat_zero, he]; addr_omega [])
  have F₂ : Fr s v₂ := {
    saved := F₁.saved.step hS (hpres₂.reg .x2) (fun r hr ↦ hpres₂ r (by
        simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide))
      fun y h1 h2 ↦ D₂ y fun i hi hw ↦ by addr_omega [hw, hi, h1, h2, hb, hst.next]
    x8 := (hpres₂.reg .x8).trans F₁.x8
    heap := hpost₂.heap
    mono := by omega
    frame := (F₁.frame.mono fun a h ↦ V.mono (by omega) h).trans D₂ fun a hw ↦
      Or.inr (Or.inr (Or.inl hw)) }
  obtain ⟨v₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000c4fc_spec
    (by rw [hpc₂, returnAddress_eq, b8000c4ec_x1 h₁]; decide) trivial
  have hm₃ := b8000c4fc_mem_same h₃
  have k₃ := b8000c4fc_keeps h₃
  have F₃ : Fr s v₃ := F₂.same hS (fun r hr ↦ k₃ r (mem_of_mem hr _)) hm₃
  have x18₃ : v₃.getReg .x18 = s.getReg .x13 := by
    rw [k₃ .x18 (by decide), hpres₂.reg .x18, k₁ .x18 (by decide), h.x18]
  have c0 : v₃.getMem (s.getReg .x13) = s.getMem (s.getReg .x13) := by
    have := F₃.claim hpre (k := 0) (by decide)
    simp only [Nat.mul_zero, add_ofNat_zero] at this
    exact this
  have c8 : v₃.getMem (s.getReg .x13 + 8) = s.getMem (s.getReg .x13 + 8) :=
    F₃.claim hpre (k := 1) (by decide)
  have c16 : v₃.getMem (s.getReg .x13 + 16) = s.getMem (s.getReg .x13 + 16) :=
    F₃.claim hpre (k := 2) (by decide)
  have hcl3 : Model.limbs (eAt s (s.getReg .x13)) =
      (v₃.getMem (v₃.getReg .x18), v₃.getMem (v₃.getReg .x18 + 8),
        v₃.getMem (v₃.getReg .x18 + 16)) := by
    rw [limbs_eAt, x18₃, c0, c8, c16]
  obtain ⟨v₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000c500_spec
    (b8000c4fc_pc_not_taken h₃ hne) (by
      rv_eval [x18₃]
      and_intros <;> (refine Region.valid hcl ?_ ?_ ?_ <;> addr_omega [hcl]))
  have k₄ := b8000c500_keeps h₄
  have hm₄ := b8000c500_mem_same h₄
  have F₄ : Fr s v₄ := F₃.same hS (fun r hr ↦ k₄ r (mem_of_mem hr _)) hm₄
  have kr3 (r : Reg) (hr : r ∈ [Reg.x9, .x19, .x20, .x21, .x22, .x23]) :
      v₃.getReg r = v.getReg r := by
    rw [k₃ r (mem_of_mem hr _), hpres₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have kr (r : Reg) (hr : r ∈ [Reg.x9, .x19, .x20, .x21, .x22, .x23]) : v₄.getReg r = v.getReg r := by
    rw [k₄ r (mem_of_mem hr _), kr3 r hr]
  have hm (a : Word) (ha : a ≠ nextAddr) : v₄.getMem a = v.getMem a := by
    rw [hm₄, hm₃, hpost₂.mem a ha, hm₁]
  have x10₄ : v₄.getReg .x10 = v₂.getReg .x10 := by rw [k₄ .x10 (by decide), k₃ .x10 (by decide)]
  have nx₄ : heapNext v₄ = heapNext v₂ := by simp only [heapNext, hm₄, hm₃]
  have hroom := h.room
  have hbuf := h.buf
  simp only [NewBuf] at hbuf
  have hhiv := h.fr.heap.hi
  have nx₁ : heapNext v₁ = heapNext v := by simp only [heapNext, hm₁]
  have D : DFrame v v₄ (Within · nextAddr 8) := fun a ha ↦
    hm a fun he ↦ ha 0 (by decide) (by rw [add_ofNat_zero, he]; addr_omega [])
  have tailM : eListAt v₄ (v.getReg .x21) (v.getReg .x9).toNat =
      eListAt v (v.getReg .x21) (v.getReg .x9).toNat :=
    D.eListAt fun i hi hw ↦ by
      rcases hbuf.2 with h0 | h0
      · omega
      · addr_omega [hw, hi, h0, hroom, hhiv]
  have cl11 := b8000c500_x11 h₄
  have cl12 := b8000c500_x12 h₄
  have cl13 := b8000c500_x13 h₄
  -- the sum
  obtain ⟨w, hr₅, pc₅, kw, mw, s11, s12, s13⟩ : ∃ w, Reaches Image.code v₄ w ∧
      w.pc = 0x8000c580 ∧ (∀ r ∈ sumKept2, w.getReg r = v₄.getReg r) ∧
      (∀ a, w.getMem a = v₄.getMem a) ∧
      w.getReg .x11 = (Model.limbs (eAt s (s.getReg .x13) +
        sumE (eListAt v₄ (v.getReg .x21) (v.getReg .x9).toNat))).1 ∧
      w.getReg .x12 = (Model.limbs (eAt s (s.getReg .x13) +
        sumE (eListAt v₄ (v.getReg .x21) (v.getReg .x9).toNat))).2.1 ∧
      w.getReg .x13 = (Model.limbs (eAt s (s.getReg .x13) +
        sumE (eListAt v₄ (v.getReg .x21) (v.getReg .x9).toNat))).2.2 := by
    by_cases h0 : v.getReg .x9 = 0
    · have e0 : (v.getReg .x9).toNat = 0 := by rw [h0]; rfl
      have hz := limbs_claim_sum (eAt s (s.getReg .x13))
        (eListAt v₄ (v.getReg .x21) (v.getReg .x9).toNat) 0 0 0 (by rw [e0]; exact limbs_zero)
        _ _ _ hcl3
      simp only [Sym.zero_xor_lit] at hz
      refine ⟨v₄, Reaches.refl _, b8000c500_pc_taken h₄ (by rw [kr3 .x9 (by simp)]; exact h0),
        fun _ _ ↦ rfl, fun _ ↦ rfl, ?_, ?_, ?_⟩
      · rw [hz, cl11]
      · rw [hz, cl12]
      · rw [hz, cl13]
    · have hl : 0 < (v.getReg .x9).toNat := by
        rcases Nat.eq_zero_or_pos (v.getReg .x9).toNat with he | he
        · exact absurd (BitVec.eq_of_toNat_eq he) h0
        · exact he
      have h0' := hbuf.2.resolve_left (by omega)
      obtain ⟨v₅, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000c510_spec
        (b8000c500_pc_not_taken h₄ (by rw [kr3 .x9 (by simp)]; exact h0)) trivial
      have k₆ := b8000c510_keeps h₆
      have hm₆ := b8000c510_mem_same h₆
      have x17₆ : v₅.getReg .x17 = v.getReg .x21 + 16 := by
        rw [b8000c510_x17 h₆, kr .x21 (by simp)]
      have x5₆ : v₅.getReg .x5 = v.getReg .x21 + 16 +
          BitVec.ofNat 64 (24 * (v.getReg .x9).toNat) := by
        rw [b8000c510_x5' h₆ (by
            rw [kr .x21 (by simp), kr .x9 (by simp)]
            addr_omega [h0', hroom, hhiv]), kr .x21 (by simp), kr .x9 (by simp)]
      obtain ⟨v₆, hr₇, pc₇, A⟩ := sumLoop2 (b8000c510_pc h₆) hl hbuf.1
        (by have := hpre.heap.lo; omega) (by addr_omega [h0', hroom, hhiv]) x17₆ x5₆
        (b8000c510_x14 h₆) (b8000c510_x15 h₆) (b8000c510_x16 h₆)
      have el : eListAt v₅ (v.getReg .x21) (v.getReg .x9).toNat =
          eListAt v₄ (v.getReg .x21) (v.getReg .x9).toNat :=
        (DFrame.of_same hm₆ fun _ ↦ False).eListAt fun _ _ h ↦ h
      obtain ⟨w, hr₈, h₈⟩ := Sym.BlockSpec.reaches b8000c574_spec pc₇ trivial
      have k₈ := b8000c574_keeps h₈
      have hz := limbs_claim_sum (eAt s (s.getReg .x13))
        (eListAt v₄ (v.getReg .x21) (v.getReg .x9).toNat) (v₆.getReg .x16) (v₆.getReg .x15)
        (v₆.getReg .x14) (by rw [A.x16, A.x15, A.x14, el]) _ _ _ hcl3
      have ka (r : Reg) (hr : r ∈ [Reg.x11, .x12, .x13]) : v₆.getReg r = v₄.getReg r := by
        rw [A.kept r (mem_of_mem hr _), k₆ r (mem_of_mem hr _)]
      refine ⟨w, hr₆.trans (hr₇.trans hr₈), b8000c574_pc h₈, fun r hr ↦ by
          rw [k₈ r (mem_of_mem hr _), A.kept r (mem_of_mem hr _), k₆ r (mem_of_mem hr _)],
        fun a ↦ by rw [b8000c574_mem_same h₈, A.mem a, hm₆], ?_, ?_, ?_⟩
      · rw [hz, b8000c574_x11 h₈, ka .x11 (by simp), cl11]
      · rw [hz, b8000c574_x12 h₈, ka .x12 (by simp), cl12]
      · rw [hz, b8000c574_x13 h₈, ka .x13 (by simp), cl13]
  have krw (r : Reg) (hr : r ∈ sumKept2) : w.getReg r = v₄.getReg r := kw r hr
  have Fw : Fr s w := F₄.same hS (fun r hr ↦ kw r (mem_of_mem hr _)) mw
  have elw : eListAt w (w.getReg .x21) (w.getReg .x9).toNat =
      eListAt v (v.getReg .x21) (v.getReg .x9).toNat := by
    rw [krw .x21 (by decide), krw .x9 (by decide), kr .x21 (by simp), kr .x9 (by simp),
      (DFrame.of_same mw fun _ ↦ False).eListAt fun _ _ h ↦ h, tailM]
  have elw' : eListAt w (w.getReg .x21) (w.getReg .x9).toNat =
      eListAt v₄ (v.getReg .x21) (v.getReg .x9).toNat := by rw [elw, tailM]
  have nxw : heapNext w = heapNext v₂ := by
    have : heapNext w = heapNext v₄ := by simp only [heapNext, mw]
    exact this.trans nx₄
  have x10w : w.getReg .x10 = v₂.getReg .x10 := (krw .x10 (by decide)).trans x10₄
  have kvw (r : Reg) (hr : r ∈ [Reg.x9, .x19, .x20, .x21, .x22, .x23]) : w.getReg r = v.getReg r :=
    (krw r (mem_of_mem hr _)).trans (kr r hr)
  refine ⟨w, hr₂.trans (hr₃.trans (hr₄.trans hr₅)), Or.inl ⟨pc₅, {
    fr := Fw
    x11 := by rw [elw', s11]
    x12 := by rw [elw', s12]
    x13 := by rw [elw', s13]
    bAl := by rw [x10w]; exact hBa
    bNext := by rw [nxw, hBn, x10w]
    bLo := by rw [x10w]; omega
    room := by rw [kvw .x9 (by simp), kvw .x23 (by simp)]; exact hroom
    buf := by
      rw [kvw .x21 (by simp), kvw .x23 (by simp), x10w]
      refine ⟨hbuf.1, ?_⟩
      rcases hbuf.2 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨h0.1, by omega⟩
    value := fun T hT ↦ by
      obtain ⟨x, T₁, T', h1, hx, h2, h3⟩ := h.value T hT
      refine ⟨x, T₁, T', h1, by rw [kvw .x20 (by simp), kvw .x19 (by simp), kvw .x22 (by simp)]; exact hx,
        by rw [elw]; exact h2, Fr.transcriptAt hpre h.fr Fw.heap.hi
        ((D.trans (DFrame.of_same mw _) fun _ h ↦ h).mono fun a h ↦ Or.inr (Or.inl h)) h3⟩ }⟩⟩

end Rv64Verifier.Transcript.RoundPoly
