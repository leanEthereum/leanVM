import Rv64Verifier.Proofs.Gkr.Contracts
import Rv64Verifier.Proofs.Transcript.Frames
import Rv64Verifier.Proofs.Runtime.Contracts
import Rv64Verifier.Blocks.F75

/-!
# `keccak::open`: up to the loops

Compiled at `0x80010184` (`Blocks/F75.lean`), a 1856-byte frame `f` below the entry's `sp`: the
prologue computes the slot count (`prologue`), `vec![None; 6]` and `sumcheck` (`to_sumcheck`); its
`Err` returns (`err`); the row is copied out at the end (`final`). Addresses on the frame are written
from the entry's `sp`: `f + k` is `sp - (1856 - k)`.
-/

namespace Rv64Verifier.Gkr.Open
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F75
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

theorem bounds {s : MachineState} (h : OpenPre s) :
    0xa0000000 + openStack ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000000 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧
      (stackLo s openStack).toNat = (s.getReg .x2).toNat - openStack := by
  have hm := h.stack.mapped (by decide) (by decide)
  have hb := h.stack.bounds (by decide) (by decide)
  omega

/-- The callee-saved registers, saved at the top of the frame. -/
structure Saved (s u : MachineState) : Prop where
  ra : u.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : u.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s1 : u.getMem (s.getReg .x2 - 24) = s.getReg .x9
  s2 : u.getMem (s.getReg .x2 - 32) = s.getReg .x18
  s3 : u.getMem (s.getReg .x2 - 40) = s.getReg .x19
  s4 : u.getMem (s.getReg .x2 - 48) = s.getReg .x20
  s5 : u.getMem (s.getReg .x2 - 56) = s.getReg .x21
  s6 : u.getMem (s.getReg .x2 - 64) = s.getReg .x22
  s7 : u.getMem (s.getReg .x2 - 72) = s.getReg .x23
  s8 : u.getMem (s.getReg .x2 - 80) = s.getReg .x24
  s9 : u.getMem (s.getReg .x2 - 88) = s.getReg .x25
  s10 : u.getMem (s.getReg .x2 - 96) = s.getReg .x26
  s11 : u.getMem (s.getReg .x2 - 104) = s.getReg .x27

/-- The saved registers survive anything that keeps the frame's top 104 bytes. -/
theorem Saved.keep {s u v : MachineState} (h : Saved s u) (hsp : 104 ≤ (s.getReg .x2).toNat)
    (hk : ∀ y : Word, (s.getReg .x2).toNat - 104 ≤ y.toNat → y.toNat + 8 ≤ (s.getReg .x2).toNat →
      v.getMem y = u.getMem y) : Saved s v where
  ra := (hk _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans h.ra
  s0 := (hk _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans h.s0
  s1 := (hk _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans h.s1
  s2 := (hk _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans h.s2
  s3 := (hk _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans h.s3
  s4 := (hk _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans h.s4
  s5 := (hk _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans h.s5
  s6 := (hk _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans h.s6
  s7 := (hk _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans h.s7
  s8 := (hk _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans h.s8
  s9 := (hk _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans h.s9
  s10 := (hk _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans h.s10
  s11 := (hk _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans h.s11

/-- `0x800104f8`: the saved registers back, return. -/
theorem exit {s u : MachineState} (hpre : OpenPre s) (hpc : u.pc = 0x800104f8)
    (hsp : u.getReg .x2 = s.getReg .x2 - 1856) (h : Saved s u) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      ∀ a, t.getMem a = u.getMem a := by
  have hb := bounds hpre
  obtain ⟨t, hr, h₁⟩ := Sym.BlockSpec.reaches b800104f8_spec hpc (by
    rv_eval [hsp]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have pc := b800104f8_pc h₁
  have y2 := b800104f8_x2 h₁
  have y8 := b800104f8_x8 h₁
  have y9 := b800104f8_x9 h₁
  have y18 := b800104f8_x18 h₁
  have y19 := b800104f8_x19 h₁
  have y20 := b800104f8_x20 h₁
  have y21 := b800104f8_x21 h₁
  have y22 := b800104f8_x22 h₁
  have y23 := b800104f8_x23 h₁
  have y24 := b800104f8_x24 h₁
  have y25 := b800104f8_x25 h₁
  have y26 := b800104f8_x26 h₁
  have y27 := b800104f8_x27 h₁
  rv_eval [hsp, h.ra, h.s0, h.s1, h.s2, h.s3, h.s4, h.s5, h.s6, h.s7, h.s8, h.s9, h.s10, h.s11]
    at pc y2 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
  refine ⟨t, hr, by rw [pc, returnAddress_eq], ?_, b800104f8_mem_same h₁⟩
  exact preserves_of y2 y8 y9 y18 y19 fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-! ## The prologue: the slot count, and `vec![None; 6]` -/

/-- At `from_elem`'s entry. -/
structure P1 (s u : MachineState) : Prop where
  pc : u.pc = 0x80010724
  x1 : u.getReg .x1 = 0x800102b8
  x2 : u.getReg .x2 = s.getReg .x2 - 1856
  x10 : u.getReg .x10 = s.getReg .x2 - 1712
  x11 : u.getReg .x11 = s.getReg .x2 - 1768
  x12 : u.getReg .x12 = 6
  x8 : u.getReg .x8 = s.getReg .x10
  x19 : u.getReg .x19 = s.getReg .x17
  x20 : u.getReg .x20 = s.getReg .x11
  x21 : u.getReg .x21 = s.getReg .x14
  x22 : u.getReg .x22 = s.getReg .x12
  saved : Saved s u
  none : u.getMem (s.getReg .x2 - 1768) = 0
  first : u.getMem (s.getReg .x2 - 1792) = s.getReg .x15
  count : u.getMem (s.getReg .x2 - 1784) = s.getReg .x16
  frame : MemFrame s u (s.getReg .x2 - 1792) 1792

theorem prologue {s : MachineState} (hpre : OpenPre s) (hpc : s.pc = 0x80010184) :
    ∃ u, Reaches Image.code s u ∧ P1 s u := by
  have hb := bounds hpre
  have h13 := hpre.depth
  obtain ⟨t₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b80010184_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₀ := b80010184_keeps h₀
  have x11₀ : t₀.getReg .x11 = 49 :=
    Sym.Expect.Holds.reg_eq h₀ .x11 rfl (by rv_eval [h13]; decide)
  have pc₀ : t₀.pc = 0x80010200 := Sym.Expect.Holds.pc_eq h₀ (by rv_eval [h13]; decide)
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80010200_spec pc₀ trivial
  have k₁ := b80010200_keeps h₁
  have x12₁ : t₁.getReg .x12 = 58 :=
    Sym.Expect.Holds.reg_eq h₁ .x12 rfl (by rv_eval [x11₀]; decide)
  obtain ⟨u, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800102a4_spec (b80010200_pc h₁) trivial
  have k₂ := b800102a4_keeps h₂
  have x2₁ : t₁.getReg .x2 = s.getReg .x2 - 1856 := by
    rw [k₁ .x2 (by decide), b80010184_x2 h₀]
  have x2 : u.getReg .x2 = s.getReg .x2 - 1856 := by rw [k₂ .x2 (by decide), x2₁]
  have m := b80010200_mem_same h₁
  have m' := b800102a4_mem_same h₂
  have mm (a : Word) : u.getMem a = t₀.getMem a := by rw [m', m]
  refine ⟨u, (hr₀.trans hr₁).trans hr₂, {
    pc := b800102a4_pc h₂
    x1 := b800102a4_x1 h₂
    x2
    x10 := by rw [b800102a4_x10 h₂, x2₁]; rv_eval []
    x11 := by rw [b800102a4_x11 h₂, x2₁]; rv_eval []
    x12 := by rw [b800102a4_x12 h₂, k₁ .x10 (by decide), b80010184_x10 h₀, x12₁]; rfl
    x8 := by rw [k₂ .x8 (by decide), k₁ .x8 (by decide), b80010184_x8 h₀]
    x19 := by rw [k₂ .x19 (by decide), k₁ .x19 (by decide), b80010184_x19 h₀]
    x20 := by rw [k₂ .x20 (by decide), k₁ .x20 (by decide), b80010184_x20 h₀]
    x21 := by rw [k₂ .x21 (by decide), k₁ .x21 (by decide), b80010184_x21 h₀]
    x22 := by rw [k₂ .x22 (by decide), k₁ .x22 (by decide), b80010184_x22 h₀]
    saved := {
      ra := by rw [mm, b80010184_m_x2_n8 h₀]
      s0 := by rw [mm, b80010184_m_x2_n16 h₀]
      s1 := by rw [mm, b80010184_m_x2_n24 h₀]
      s2 := by rw [mm, b80010184_m_x2_n32 h₀]
      s3 := by rw [mm, b80010184_m_x2_n40 h₀]
      s4 := by rw [mm, b80010184_m_x2_n48 h₀]
      s5 := by rw [mm, b80010184_m_x2_n56 h₀]
      s6 := by rw [mm, b80010184_m_x2_n64 h₀]
      s7 := by rw [mm, b80010184_m_x2_n72 h₀]
      s8 := by rw [mm, b80010184_m_x2_n80 h₀]
      s9 := by rw [mm, b80010184_m_x2_n88 h₀]
      s10 := by rw [mm, b80010184_m_x2_n96 h₀]
      s11 := by rw [mm, b80010184_m_x2_n104 h₀] }
    none := by rw [mm, b80010184_m_x2_n1768 h₀]
    first := by rw [mm, b80010184_m_x2_n1792 h₀]
    count := by rw [mm, b80010184_m_x2_n1784 h₀]
    frame := fun a ha ↦ by rw [mm]; exact b80010184_frame h₀ (by addr_omega [hb]) a ha }⟩

/-! ## Frames -/

/-- What the stack, `NEXT` and the heap allocated from `m` on to `u` cover. -/
@[rv_addr] def SW (s m u : MachineState) (a : Word) : Prop :=
  Within a (stackLo s openStack) openStack ∨ Within a nextAddr 8 ∨ Fresh m u a

theorem outside_mono {s m : MachineState} {a : Word} {n : Nat} (h : Outside s a n)
    (hm : heapNext s ≤ heapNext m) : Outside m a n := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨by omega, h2⟩

/-- Bytes apart from the stack and outside the free heap at `m` miss `SW s m u`. -/
theorem missSW {s m u : MachineState} {lo : Word} {n : Nat} (hu : HeapOk u)
    (hst : Apart lo n (stackLo s openStack) openStack) (hfree : Outside m lo n)
    (hn : lo.toNat + n ≤ 2 ^ 64) : Misses (SW s m u) lo n := fun y hy hw ↦ by
  have := hu.hi
  obtain ⟨hf1, hf2⟩ := hfree
  simp only [SW] at hw
  rcases hw with hw | hw | hw <;> addr_omega [hy, hw, hst, hf1, hf2, hn, this]

theorem SW.mono {s m m' u u' : MachineState} (hm : heapNext m' ≤ heapNext m)
    (hu : heapNext u ≤ heapNext u') {a : Word} (h : SW s m u a) : SW s m' u' a := by
  simp only [SW, Fresh] at h ⊢
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨by omega, by omega⟩)

theorem SW.openW {s m u u' : MachineState} (hm : heapNext s ≤ heapNext m)
    (hu : heapNext u ≤ heapNext u') {a : Word} (h : SW s m u a) : OpenW s u' a := by
  simp only [SW, OpenW, Fresh] at h ⊢
  rcases h with h | h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))

theorem ProofApart.mono' {s : MachineState} {p lo lo' : Word} {n n' : Nat}
    (h : ProofApart s p lo n) (h1 : lo.toNat ≤ lo'.toNat) (h2 : lo'.toNat + n' ≤ lo.toNat + n) :
    ProofApart s p lo' n' := by
  obtain ⟨ha, hb⟩ := h
  exact ⟨by addr_omega [ha, h1, h2], by addr_omega [hb, h1, h2]⟩

/-- The transcript's reads (`p`, the `Proof`, the stream) miss `SW s m u`. -/
structure ReadsMiss (w : Word → Prop) (s : MachineState) (p : Word) : Prop where
  self : Misses w p 8
  proof : Misses w (proofAt s p) 48
  stream : Misses w (streamPtr s p) (24 * streamLen s p)
  sponge : Misses w (p + 8) 352

theorem readsMiss {s m u : MachineState} (hpre : OpenPre s) (hm : heapNext s ≤ heapNext m)
    (hu : HeapOk u) : ReadsMiss (SW s m u) s (oP s) := by
  have hS := hpre.self.self
  have hP := hpre.self.proof
  have hst := hpre.selfStack
  have hps := hpre.proofStack
  have hsf := outside_mono hpre.selfFree hm
  have hpf := outside_mono hpre.proofFree hm
  have hbf := outside_mono hpre.streamFree hm
  refine ⟨missSW hu (by addr_omega [hst]) (by addr_omega [hsf]) (by addr_omega [hS]),
    missSW hu hps.1 hpf (by addr_omega [hP]), ?_,
    missSW hu (by addr_omega [hst, hS]) (by addr_omega [hsf, hS]) (by addr_omega [hS])⟩
  rcases hpre.self.stream with h0 | hB
  · intro y hy
    simp only [oP] at h0 hy
    simp only [Within, h0] at hy; omega
  · exact missSW hu hps.2 hbf (by addr_omega [hB])

theorem newVecE_mono {s s' t : MachineState} {a : Word} {xs : List E} (h : NewVecE s' t a xs)
    (hs : heapNext s ≤ heapNext s') : NewVecE s t a xs :=
  ⟨h.vec, by have := h.buf; simp only [NewBuf] at this ⊢; omega, h.elems⟩

theorem optEListAt_congr {u v : MachineState} (h : ∀ a, v.getMem a = u.getMem a) (a : Word)
    (n : Nat) : optEListAt v a n = optEListAt u a n := by
  simp only [optEListAt, optEAt, eAt, h]

/-- A block whose writes all satisfy `w` is a frame of `w`. -/
theorem dframe_of_writes {x : Sym.Expect} {s t : MachineState} (h : x.Holds s t)
    {w : Word → Prop} (hw : ∀ k ∈ x.writes, w (k.eval s)) : DFrame s t w :=
  fun a ha ↦ h.frame a fun k hk heq ↦ ha 0 (by decide) (by rw [add_ofNat_zero, heq]; exact hw k hk)

/-- The transcript's reads miss what `open` writes but the sponge, and the result. -/
theorem readsMissOut {s m u : MachineState} (hpre : OpenPre s) (hm : heapNext s ≤ heapNext m)
    (hu : HeapOk u) :
    ReadsMiss (fun a ↦ SW s m u a ∨ Within a (oOut s) 1584) s (oP s) := by
  have r := readsMiss (m := m) (u := u) hpre hm hu
  have hS := hpre.self.self
  have hP := hpre.self.proof
  have hso := hpre.outSelf
  have hpo := hpre.proofOut
  refine ⟨fun y hy h ↦ ?_, fun y hy h ↦ ?_, fun y hy h ↦ ?_, fun y hy h ↦ ?_⟩
  · rcases h with h | h
    · exact r.self y hy h
    · addr_omega [hy, h, hso]
  · rcases h with h | h
    · exact r.proof y hy h
    · addr_omega [hy, h, hpo.1]
  · rcases h with h | h
    · exact r.stream y hy h
    · addr_omega [hy, h, hpo.2]
  · rcases h with h | h
    · exact r.sponge y hy h
    · addr_omega [hy, h, hso, hS]

/-- What `open` writes misses the transcript's reads. -/
theorem readsMissOpenW {s u : MachineState} (hpre : OpenPre s) (hu : HeapOk u) :
    Misses (OpenW s u) (oP s) 8 ∧ Misses (OpenW s u) (proofAt s (oP s)) 48 := by
  have r := readsMiss (m := s) (u := u) hpre (le_refl _) hu
  have hS := hpre.self.self
  have hso := hpre.outSelf
  have hvs := hpre.valueSelf
  have hpo := hpre.proofOut
  have hpv := hpre.proofValue
  have hpa := hpre.self.apart
  refine ⟨fun y hy h ↦ ?_, fun y hy h ↦ ?_⟩
  · simp only [OpenW] at h
    rcases h with h | h | h | h
    · addr_omega [hy, h, hso]
    · addr_omega [hy, h, hvs]
    · addr_omega [hy, h, hS]
    · exact r.self y hy h
  · simp only [OpenW] at h
    rcases h with h | h | h | h
    · addr_omega [hy, h, hpo.1]
    · addr_omega [hy, h, hpv.1]
    · addr_omega [hy, h, hpa.1]
    · exact r.proof y hy h

/-! ## Up to `sumcheck`'s return -/

/-- Back from `sumcheck`. -/
structure P2 (s m : MachineState) : Prop where
  pc : m.pc = 0x800102d8
  x2 : m.getReg .x2 = s.getReg .x2 - 1856
  x8 : m.getReg .x8 = s.getReg .x10
  x20 : m.getReg .x20 = s.getReg .x11
  x21 : m.getReg .x21 = s.getReg .x14
  x22 : m.getReg .x22 = s.getReg .x12
  saved : Saved s m
  first : m.getMem (s.getReg .x2 - 1792) = s.getReg .x15
  count : m.getMem (s.getReg .x2 - 1784) = s.getReg .x16
  heap : HeapOk m
  mono : heapNext s ≤ heapNext m
  frame : DFrame s m (OpenW s m)
  result : ∀ T, TranscriptAt s (oP s) T →
    match (TM.sumcheck (eAt s (oValue s)) 3 (List.replicate 6 none)).run T with
    | some ((pt, cl), T') => vecCap m (s.getReg .x2 - 1688) ≠ errNiche ∧
        NewVecE s m (s.getReg .x2 - 1688) pt ∧ eAt m (s.getReg .x2 - 1664) = cl ∧
        TranscriptAt m (oP s) T'
    | none => vecCap m (s.getReg .x2 - 1688) = errNiche

theorem to_sumcheck (hOF : OptFromElemSpec) (hSC : SumcheckSpec) {s : MachineState}
    (hpre : OpenPre s) (hpc : s.pc = 0x80010184) :
    ∃ m, Reaches Image.code s m ∧ (P2 s m ∨ Dead Image.code m) := by
  have hb := bounds hpre
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hrs := hpre.stack.rodata
  have hS := hpre.self.self
  have hP := hpre.self.proof
  obtain ⟨u, hr₁, P⟩ := prologue hpre hpc
  have hNu : u.getMem nextAddr = s.getMem nextAddr :=
    P.frame _ (by addr_omega [hb, hnx])
  have hHu : HeapOk u := ⟨by simp only [heapNext, hNu]; exact hpre.heap.lo,
    by simp only [heapNext, hNu]; exact hpre.heap.hi⟩
  have hfe : OptFromElemPre u := {
    heap := hHu
    out := by rw [P.x10]; addr_omega [hb, hsm]
    elem := by rw [P.x11]; addr_omega [hb, hsm]
    stack := hpre.stack.sub 1856 P.x2 (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by rw [P.x10]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    elemFree := by rw [P.x11]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    outStack := by rw [P.x10]; simp only [stackLo, P.x2]; addr_omega [hb]
    elemStack := by rw [P.x11]; simp only [stackLo, P.x2]; addr_omega [hb]
    elemOut := by rw [P.x11, P.x10]; addr_omega [hb] }
  obtain ⟨v, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ := hOF.call hr₁ P.pc hfe
  swap
  · exact ⟨_, hr₂, Or.inr hd⟩
  have F₂ := hpost₂.frame
  have hlen₂ := hpost₂.len
  have hel₂ := hpost₂.elems
  have hfr₂ := hpost₂.fresh
  rw [P.x10] at F₂ hlen₂ hel₂ hfr₂
  rw [P.x11, P.x12] at hel₂
  rw [P.x12] at hlen₂ hfr₂
  simp only [stackLo, P.x2] at F₂
  have x2v : v.getReg .x2 = s.getReg .x2 - 1856 := (hpres₂.reg .x2).trans P.x2
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800102b8_spec
    (by rw [hpc₂, returnAddress_eq, P.x1]; decide) (by
      rv_eval [x2v]
      and_intros <;> valid_access hpre.stack.valid [hb])
  have k₃ := b800102b8_keeps h₃
  have hm₃ := b800102b8_mem_same h₃
  have x2₃ : u₃.getReg .x2 = s.getReg .x2 - 1856 := (k₃ .x2 (by decide)).trans x2v
  have x10₃ : u₃.getReg .x10 = s.getReg .x2 - 1688 := by rw [b800102b8_x10 h₃, x2v]; rv_eval []
  have x11₃ : u₃.getReg .x11 = s.getReg .x11 := by
    rw [b800102b8_x11 h₃, hpres₂.reg .x20, P.x20]
  have x12₃ : u₃.getReg .x12 = s.getReg .x17 := by
    rw [b800102b8_x12 h₃, hpres₂.reg .x19, P.x19]
  have x13₃ : u₃.getReg .x13 = 3 := b800102b8_x13 h₃
  have x14₃ : u₃.getReg .x14 = vecPtr v (s.getReg .x2 - 1712) := by
    rw [b800102b8_x14 h₃, x2v]; simp only [vecPtr]; rv_eval []
  have x15₃ : u₃.getReg .x15 = 6 := by
    rw [b800102b8_x15 h₃, x2v, ← hlen₂]; simp only [vecLen]; rv_eval []
  have hHv := hpost₂.heap
  have hNv : u₃.getMem nextAddr = v.getMem nextAddr := hm₃ _
  have hH₃ : HeapOk u₃ := ⟨by simp only [heapNext, hNv]; exact hHv.lo,
    by simp only [heapNext, hNv]; exact hHv.hi⟩
  have mono₃ : heapNext s ≤ heapNext u₃ := by
    have := hpost₂.mono; simp only [heapNext, hNv, hNu] at this ⊢; exact this
  have F₃ : DFrame s u₃ (SW s s u₃) :=
    (((DFrame.of_memFrame P.frame).mono fun a h ↦ Or.inl (by addr_omega [h, hb])).trans F₂
      fun a h ↦ by
        simp only [Fresh, heapNext, hNv, hNu] at h ⊢
        rcases h with h | h | h | h
        · exact Or.inl (by addr_omega [h, hb])
        · exact Or.inl (by addr_omega [h, hb])
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)).trans (DFrame.of_same hm₃ _) fun _ h ↦ h
  have rm := readsMiss (u := u₃) hpre (le_refl _) hH₃
  have hS8 : (s.getReg .x11).toNat + 8 ≤ 2 ^ 64 := by addr_omega [hS]
  have hP48 : (proofAt s (s.getReg .x11)).toNat + 48 ≤ 2 ^ 64 := by addr_omega [hP]
  obtain ⟨e0, e1, e2⟩ := F₃.stream' rm.self hS8 rm.proof hP48
  simp only [oP] at e0 e1 e2
  have hfr := hfr₂
  simp only [NewBuf] at hfr
  have hfrN : heapNext v = heapNext u₃ := by simp only [heapNext, hNv]
  have hNs : heapNext u = heapNext s := by simp only [heapNext, hNu]
  have hsf := hpre.selfFree
  have hvf := hpre.valueFree
  have hvs := hpre.valueStack
  have hHu' := hHu.lo
  have hHv' := hHv.hi
  have hsc : SumcheckPre u₃ := {
    heap := hH₃
    out := by rw [x10₃]; addr_omega [hb, hsm]
    self := by rw [x11₃]; exact F₃.transcriptOk hpre.self rm.self rm.proof
    stack := hpre.stack.sub 1856 x2₃ (by decide) (by decide) (by decide) (by decide) (by decide)
    outStack := by rw [x10₃]; simp only [stackLo, x2₃]; addr_omega [hb]
    selfStack := by rw [x11₃]; simp only [stackLo, x2₃]; addr_omega [hpre.selfStack, hb]
    outSelf := by rw [x10₃, x11₃]; addr_omega [hpre.selfStack, hb, hS]
    proofStack := by
      rw [x11₃]
      refine F₃.proofApart rm.self hS8 rm.proof hP48 (ProofApart.mono' hpre.proofStack ?_ ?_) <;>
        simp only [stackLo, x2₃] <;> addr_omega [hb]
    proofOut := by
      rw [x11₃, x10₃]
      refine F₃.proofApart rm.self hS8 rm.proof hP48 (ProofApart.mono' hpre.proofStack ?_ ?_) <;>
        addr_omega [hb]
    outFree := by rw [x10₃]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    selfFree := by rw [x11₃]; exact outside_mono hsf mono₃
    proofFree := by rw [x11₃, e0]; exact outside_mono hpre.proofFree mono₃
    streamFree := by rw [x11₃, e1, e2]; exact outside_mono hpre.streamFree mono₃
    rodata := hpre.rodata.dframe F₃ fun a ha hw ↦ by
      have := hH₃.hi
      simp only [SW] at hw
      rcases hw with hw | hw | hw <;> addr_omega [ha, hw, hrs, this]
    outRodata := by rw [x10₃]; addr_omega [hrs, hb]
    selfRodata := by rw [x11₃]; exact hpre.selfRodata
    count := by rw [x13₃]; decide
    claim := by rw [x12₃]; exact hpre.value
    eqs := by rw [x15₃, x14₃]; right; addr_omega [hfr, hHu', hHv']
    claimFree := by rw [x12₃]; exact outside_mono hvf mono₃
    eqsFree := by rw [x15₃, x14₃]; addr_omega [hfr, hfrN, hHv']
    claimStack := by rw [x12₃]; simp only [stackLo, x2₃]; addr_omega [hvs, hb]
    eqsStack := by rw [x15₃, x14₃]; simp only [stackLo, x2₃]; addr_omega [hfr, hHv', hab, hb]
    claimSelf := by rw [x12₃, x11₃]; exact hpre.valueSelf
    eqsSelf := by rw [x15₃, x14₃, x11₃]; addr_omega [hfr, hsf, hNs, hHv']
    claimOut := by rw [x12₃, x10₃]; addr_omega [hvs, hb]
    eqsOut := by rw [x15₃, x14₃, x10₃]; addr_omega [hfr, hHv', hab, hb]
    claimEqs := by rw [x15₃, x14₃, x12₃]; addr_omega [hfr, hvf, hNs, hHv']
    proofClaim := by
      rw [x11₃, x12₃]
      exact F₃.proofApart rm.self hS8 rm.proof hP48 hpre.proofValue
    claimRodata := by rw [x12₃]; exact hpre.valueRodata }
  obtain ⟨m, hr₄, ⟨hpc₄, hpres₄, hpost₄⟩ | hd⟩ := hSC.call (hr₂.trans hr₃) (b800102b8_pc h₃) hsc
  swap
  · exact ⟨_, hr₄, Or.inr hd⟩
  have G := hpost₄.frame
  have hv := hpost₄.value
  rw [x10₃, x11₃, x12₃] at G
  rw [x10₃, x11₃, x12₃, x13₃, x14₃, x15₃] at hv
  simp only [stackLo, x2₃] at G
  have mono₄ : heapNext s ≤ heapNext m := mono₃.trans hpost₄.mono
  -- what neither callee writes: the frame's slots above `f + 168`'s 48 bytes and below
  have keep (y : Word) (h1 : (s.getReg .x2).toNat - 1856 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat)
      (h3 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1712 ∨ (s.getReg .x2).toNat - 1640 ≤ y.toNat) :
      m.getMem y = u.getMem y := by
    have := hpost₄.heap.hi
    rw [G y fun i hi h ↦ by
      rcases h with h | h | h | h | h | h <;>
        addr_omega [h, hi, h1, h2, h3, hb, hvs, hpre.selfStack, hS, hHv', this, hab, hnx],
      hm₃, F₂ y fun i hi h ↦ by
      rcases h with h | h | h | h <;> addr_omega [h, hi, h1, h2, h3, hb, hHv', hab, hnx]]
  refine ⟨m, hr₄, Or.inl {
    pc := by rw [hpc₄, returnAddress_eq, b800102b8_x1 h₃]; decide
    x2 := (hpres₄.reg .x2).trans x2₃
    x8 := by rw [hpres₄.reg .x8, k₃ .x8 (by decide), hpres₂.reg .x8, P.x8]
    x20 := by rw [hpres₄.reg .x20, k₃ .x20 (by decide), hpres₂.reg .x20, P.x20]
    x21 := by rw [hpres₄.reg .x21, k₃ .x21 (by decide), hpres₂.reg .x21, P.x21]
    x22 := by rw [hpres₄.reg .x22, k₃ .x22 (by decide), hpres₂.reg .x22, P.x22]
    saved := P.saved.keep (by addr_omega [hb]) fun y h1 h2 ↦
      keep y (by addr_omega [h1, hb]) h2 (Or.inr (by addr_omega [h1, hb]))
    first := by
      rw [keep _ (by addr_omega [hb]) (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), P.first]
    count := by
      rw [keep _ (by addr_omega [hb]) (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), P.count]
    heap := hpost₄.heap
    mono := mono₄
    frame := (F₃.mono fun a h ↦ SW.openW (le_refl _) hpost₄.mono h).trans G fun a h ↦ by
      simp only [OpenW, Fresh, oOut, oValue, oP] at h ⊢
      rcases h with h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [h, hb]))))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [h, hb]))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, h.2⟩))))
    result := fun T hT ↦ by
      have hv' := hv T (F₃.transcriptAt hT hpre.self rm.self rm.proof rm.stream rm.sponge)
      have ev : eAt u₃ (s.getReg .x17) = eAt s (s.getReg .x17) :=
        F₃.eAt (fun i hi h ↦ (missSW hH₃ hvs hvf (by addr_omega [hpre.value]))
          _ (by addr_omega [hi, hpre.value]) h)
      have eq : optEListAt u₃ (vecPtr v (s.getReg .x2 - 1712)) ((6 : Word).toNat) =
          List.replicate 6 none := by
        rw [optEListAt_congr hm₃, hel₂]; simp only [optEAt, P.none, ↓reduceIte]; rfl
      rw [ev, eq, show ((3 : Word).toNat : Nat) = 3 from rfl] at hv'
      simp only [oValue]
      generalize (TM.sumcheck (eAt s (s.getReg .x17)) 3 (List.replicate 6 none)).run T = o at hv' ⊢
      rcases o with _ | ⟨⟨pt, cl⟩, T'⟩
      · exact hv'
      · obtain ⟨h1, h2, h3, h4⟩ := hv'
        refine ⟨h1, newVecE_mono h2 mono₃, ?_, h4⟩
        rw [← h3]; rv_eval [] }⟩

/-! ## The mirror -/

theorem shapeOf_eq {s : MachineState} (h : s.getReg .x13 = 12) :
    shapeOf s = ⟨(s.getReg .x12).toNat, 12⟩ := by
  simp only [shapeOf, h]; rfl

/-- `openRust` at depth 12: the sumcheck, then the row. -/
theorem openRust_run (l : Nat) (claim : KeccakClaim) (first count : Nat) (value : E) (T : TState) :
    (openRust ⟨l, 12⟩ claim first count value).run T =
      match (TM.sumcheck value 3 (List.replicate 6 none)).run T with
      | some ((slot, v), T') => some ((slot, openRow (eqKernelRust (claim.point.drop (l - 4)))
          (eqKernelRust slot) claim.weights first count, v), T')
      | none => none := by
  unfold openRust
  rw [shape_slotBits, qkeccakSlotBits_eq, shape_packBits]
  simp only [StateT.run_bind]
  cases (TM.sumcheck value 3 (List.replicate 6 none)).run T with
  | none => rfl
  | some p => obtain ⟨⟨a, b⟩, T'⟩ := p; rfl

/-! ## `Err` from `sumcheck` -/

theorem err {s m : MachineState} (hpre : OpenPre s) (P : P2 s m)
    (herr : m.getMem (s.getReg .x2 - 1688) = 0xffffffffffffffff) :
    ∃ t, Reaches Image.code m t ∧ t.pc = returnAddress s ∧ Preserves s t ∧ OpenPost s t := by
  have hb := bounds hpre
  have ho := hpre.out
  have hos := hpre.outStack
  obtain ⟨u, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800102d8_spec P.pc (by
    rv_eval [P.x2]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b800102d8_keeps h₁
  have hm₁ := b800102d8_mem_same h₁
  obtain ⟨v, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800104ec_spec
    (b800102d8_pc_taken h₁ (by rw [P.x2]; rv_eval []; exact herr)) (by
      rv_eval [k₁ .x8 (by decide), P.x8]
      and_intros <;> (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
  have m0 := b800104ec_m_x8_0 h₂
  have f₂ := b800104ec_frame h₂ (by rw [k₁ .x8 (by decide), P.x8]; addr_omega [ho])
  rw [k₁ .x8 (by decide), P.x8] at m0 f₂
  have kv (y : Word) (hy : ¬ Within y (s.getReg .x10) 24) : v.getMem y = m.getMem y := by
    rw [f₂ y hy, hm₁]
  obtain ⟨t, hr₃, pc, pres, same⟩ := exit hpre (b800104ec_pc h₂)
    (by rw [b800104ec_keeps h₂ .x2 (by decide), k₁ .x2 (by decide), P.x2])
    (P.saved.keep (by addr_omega [hb]) fun y h1 h2 ↦ kv y (by addr_omega [h1, h2, hos, hb]))
  have hN : t.getMem nextAddr = m.getMem nextAddr := by
    rw [same, kv _ (by addr_omega [ho, hpre.outFree])]
  refine ⟨t, hr₁.trans (hr₂.trans hr₃), pc, pres, {
    heap := ⟨by simp only [heapNext, hN]; exact P.heap.lo, by simp only [heapNext, hN]; exact P.heap.hi⟩
    mono := by simp only [heapNext, hN] at P ⊢; exact P.mono
    value := fun T hT ↦ ?_
    frame := (P.frame.trans (DFrame.of_two (lo₂ := s.getReg .x10) (n₂ := 24) fun a h _ ↦ by
        rw [same, kv a h]) fun a h ↦ by
        simp only [OpenW]; rcases h with h | h
        · exact Or.inl (by addr_omega [h, ho])
        · exact Or.inl (by addr_omega [h, ho])).mono fun a h ↦ by
      simp only [OpenW, Fresh, heapNext, hN] at h ⊢; exact h }⟩
  have hr := P.result T hT
  rw [shapeOf_eq hpre.depth, openRust_run]
  simp only [oValue] at hr ⊢
  generalize (TM.sumcheck (eAt s (s.getReg .x17)) 3 (List.replicate 6 none)).run T = o at hr ⊢
  rcases o with _ | ⟨⟨pt, cl⟩, T'⟩
  · show t.getMem (s.getReg .x10) = _
    rw [same, m0, b800102d8_x10 h₁]; rfl
  · exact absurd herr hr.1

/-! ## The `Ok` path -/

/-- At `0x800104a0`, the row computed. -/
structure AtFinal (s m x : MachineState) : Prop where
  pc : x.pc = 0x800104a0
  x2 : x.getReg .x2 = s.getReg .x2 - 1856
  saved : Saved s x
  out : x.getMem (s.getReg .x2 - 1824) = s.getReg .x10
  cap : x.getMem (s.getReg .x2 - 1848) = m.getMem (s.getReg .x2 - 1688)
  ptr : x.getMem (s.getReg .x2 - 1840) = m.getMem (s.getReg .x2 - 1680)
  len : x.getMem (s.getReg .x2 - 1832) = m.getMem (s.getReg .x2 - 1672)
  value : eAt x (s.getReg .x2 - 152) = eAt m (s.getReg .x2 - 1664)
  row : eListAt x (s.getReg .x2 - 1688) 64 =
    openRow (eqKernelRust ((claimAt s (oClaim s)).point.drop ((s.getReg .x12).toNat - 4)))
      (eqKernelRust (vecEs m (s.getReg .x2 - 1688))) (claimAt s (oClaim s)).weights
      (s.getReg .x15).toNat (s.getReg .x16).toNat
  heap : HeapOk x
  mono : heapNext m ≤ heapNext x
  frame : DFrame m x (SW s m x)

theorem final (hMC : Runtime.MemcpySpec 0x800126e4) {s m x : MachineState} (hpre : OpenPre s)
    (P : P2 s m) (hok : m.getMem (s.getReg .x2 - 1688) ≠ 0xffffffffffffffff)
    (X : AtFinal s m x) :
    ∃ t, Reaches Image.code x t ∧
      ((t.pc = returnAddress s ∧ Preserves s t ∧ OpenPost s t) ∨ Dead Image.code t) := by
  have hb := bounds hpre
  have ho := hpre.out
  have hos := hpre.outStack
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have hnx := hpre.stack.next
  obtain ⟨u, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800104a0_spec X.pc (by
    rv_eval [X.x2]
    valid_access hpre.stack.valid [hb])
  have k₁ := b800104a0_keeps h₁
  have hm₁ := b800104a0_mem_same h₁
  have x2u : u.getReg .x2 = s.getReg .x2 - 1856 := (k₁ .x2 (by decide)).trans X.x2
  have x8u : u.getReg .x8 = s.getReg .x10 := by rw [b800104a0_x8 h₁, X.x2]; rv_eval [X.out]
  have x10u : u.getReg .x10 = s.getReg .x10 + 24 := by rw [b800104a0_x10 h₁, X.x2]; rv_eval [X.out]
  have x11u : u.getReg .x11 = s.getReg .x2 - 1688 := by rw [b800104a0_x11 h₁, X.x2]; rv_eval []
  have x12u : u.getReg .x12 = 1536 := b800104a0_x12 h₁
  have hmc : Runtime.MemcpyPre u := {
    dst := by rw [x10u, x12u]; addr_omega [ho]
    src := by rw [x11u, x12u]; addr_omega [hb, hsm]
    apart := by rw [x10u, x11u, x12u]; addr_omega [hos, hb, ho]
    stack := (hpre.stack.sub 1856 x2u (by decide) (by decide) (by decide) (by decide)
      (by decide)).toStackOk
    dstStack := by rw [x10u, x12u]; simp only [stackLo, x2u]; addr_omega [hos, hb, ho]
    srcStack := by rw [x11u, x12u]; simp only [stackLo, x2u]; addr_omega [hb] }
  obtain ⟨w, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ := hMC.call hr₁ (b800104a0_pc h₁) hmc
  swap
  · exact ⟨_, hr₂, Or.inr hd⟩
  have bytes := hpost₂.bytes
  have F₂ := DFrame.of_byteFrame hpost₂.frame
  rw [x10u, x11u, x12u] at bytes
  rw [x10u, x12u] at F₂
  simp only [stackLo, x2u] at F₂
  have kw (y : Word) (h1 : (s.getReg .x2).toNat - 1856 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat) : w.getMem y = x.getMem y := by
    rw [F₂ y fun i hi h ↦ by rcases h with h | h <;> addr_omega [h, hi, h1, h2, hos, hb, ho], hm₁]
  have x2w : w.getReg .x2 = s.getReg .x2 - 1856 := (hpres₂.reg .x2).trans x2u
  have x8w : w.getReg .x8 = s.getReg .x10 := (hpres₂.reg .x8).trans x8u
  obtain ⟨v, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800104b8_spec
    (by rw [hpc₂, returnAddress_eq, b800104a0_x1 h₁]; decide) (by
      rv_eval [x2w, x8w]
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho])
        | addr_omega [hos, hb, ho])
  have k₃ := b800104b8_keeps h₃
  have F₃ : DFrame w v fun a ↦ Within a (s.getReg .x10) 24 ∨ Within a (s.getReg .x10 + 1560) 24 :=
    dframe_of_writes h₃ (by
      rv_eval [x8w]
      and_intros <;> addr_omega [ho])
  have m0 := b800104b8_m_x8_0 h₃
  have m8 := b800104b8_m_x8_8 h₃
  have m16 := b800104b8_m_x8_16 h₃
  have m1560 := b800104b8_m_x8_1560 h₃
  have m1568 := b800104b8_m_x8_1568 h₃
  have m1576 := b800104b8_m_x8_1576 h₃
  rw [x8w, x2w] at m0 m8 m16 m1560 m1568 m1576
  rv_eval [] at m0 m8 m16 m1560 m1568 m1576
  obtain ⟨t, hr₄, pc, pres, same⟩ := exit hpre (b800104b8_pc h₃)
    (by rw [k₃ .x2 (by decide), x2w])
    (X.saved.keep (by addr_omega [hb]) fun y h1 h2 ↦ by
      rw [F₃ y fun i hi h ↦ by rcases h with h | h <;> addr_omega [h, hi, h1, h2, hos, hb, ho],
        kw y (by addr_omega [h1, hb]) h2])
  -- from `x` on: the result and the stack
  have Fxt : DFrame x t fun a ↦ Within a (s.getReg .x10) 1584 ∨
      Within a (stackLo s openStack) openStack :=
    ((((DFrame.of_same hm₁ _).trans F₂ fun a h ↦ by
      rcases h with h | h
      · exact Or.inl (by addr_omega [h, ho])
      · exact Or.inr (by addr_omega [h, hb])).trans F₃ fun a h ↦ by
      rcases h with h | h
      · exact Or.inl (by addr_omega [h, ho])
      · exact Or.inl (by addr_omega [h, ho])).trans (DFrame.of_same same _) fun _ h ↦ h)
  have hNt : t.getMem nextAddr = x.getMem nextAddr :=
    Fxt _ fun i hi h ↦ by
      have := hpre.outFree
      rcases h with h | h <;> addr_omega [h, hi, this, hnx]
  have hHx := X.heap
  have hHt : HeapOk t := ⟨by simp only [heapNext, hNt]; exact hHx.lo,
    by simp only [heapNext, hNt]; exact hHx.hi⟩
  have monoMx := X.mono
  have monoSm := P.mono
  have hmt : heapNext m ≤ heapNext t := by simp only [heapNext, hNt] at monoMx ⊢; exact monoMx
  have Fmt : DFrame m t fun a ↦ SW s m x a ∨ Within a (oOut s) 1584 :=
    (X.frame.mono fun a h ↦ Or.inl h).trans Fxt fun a h ↦ by
      rcases h with h | h
      · exact Or.inr h
      · exact Or.inl (Or.inl h)
  have wt (y : Word) (h1 : (s.getReg .x2).toNat - 1856 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat) : t.getMem y = x.getMem y := by
    rw [same, F₃ y fun i hi h ↦ by rcases h with h | h <;> addr_omega [h, hi, h1, h2, hos, hb, ho],
      kw y h1 h2]
  have hcap : vecCap t (s.getReg .x10) = vecCap m (s.getReg .x2 - 1688) := by
    simp only [vecCap]
    rw [same, m0, kw _ (by addr_omega [hb]) (by addr_omega [hb]), X.cap]
  have hptr : vecPtr t (s.getReg .x10) = vecPtr m (s.getReg .x2 - 1688) := by
    simp only [vecPtr]
    rw [same, m8, kw _ (by addr_omega [hb]) (by addr_omega [hb]), X.ptr]; rv_eval []
  have hlen : vecLen t (s.getReg .x10) = vecLen m (s.getReg .x2 - 1688) := by
    simp only [vecLen]
    rw [same, m16, kw _ (by addr_omega [hb]) (by addr_omega [hb]), X.len]; rv_eval []
  have rowt : eListAt t (s.getReg .x10 + 24) 64 = eListAt x (s.getReg .x2 - 1688) 64 := by
    have e1 : eListAt t (s.getReg .x10 + 24) 64 = eListAt w (s.getReg .x10 + 24) 64 := by
      have e := (F₃.trans (DFrame.of_same same _) fun _ h ↦ h).eListAt (p := s.getReg .x10 + 24)
        (n := 64) fun i hi h ↦ by rcases h with h | h <;> addr_omega [h, hi, ho]
      exact e
    have e2 : eListAt w (s.getReg .x10 + 24) 64 = eListAt u (s.getReg .x2 - 1688) 64 :=
      eListAt_eq_of_bytesAt (by rw [show 24 * 64 = ((1536 : Word)).toNat from rfl]; exact bytes)
        (by addr_omega [ho]) (by addr_omega [hb])
    rw [e1, e2]
    simp only [eListAt, eAt, hm₁]
  have valt : eAt t (s.getReg .x10 + 1560) = eAt x (s.getReg .x2 - 152) := by
    unfold Rv64Verifier.eAt
    rw [same, m1560, show s.getReg .x10 + 1560 + 8 = s.getReg .x10 + 1568 by rv_eval [],
      show s.getReg .x10 + 1560 + 16 = s.getReg .x10 + 1576 by rv_eval [], same, m1568, same,
      m1576, kw _ (by addr_omega [hb]) (by addr_omega [hb]),
      kw _ (by addr_omega [hb]) (by addr_omega [hb]), kw _ (by addr_omega [hb]) (by addr_omega [hb])]
    rv_eval []
  have rm := readsMissOut (m := m) (u := x) hpre monoSm hHx
  have rmo := readsMissOpenW (u := m) hpre P.heap
  have hS := hpre.self.self
  have hP := hpre.self.proof
  obtain ⟨e0, e1, e2⟩ := P.frame.stream' rmo.1 (by addr_omega [hS]) rmo.2 (by addr_omega [hP])
  have hokm : TranscriptOk m (oP s) := P.frame.transcriptOk hpre.self rmo.1 rmo.2
  refine ⟨t, hr₂.trans (hr₃.trans hr₄), Or.inl ⟨pc, pres, {
    heap := hHt
    mono := monoSm.trans hmt
    value := fun T hT ↦ ?_
    frame := ((P.frame.mono fun a h ↦ by
        simp only [OpenW, Fresh] at h ⊢
        rcases h with h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1, by omega⟩))))).trans Fmt
      fun a h ↦ by
        rcases h with h | h
        · exact SW.openW monoSm (by simp only [heapNext, hNt]; exact le_refl _) h
        · exact Or.inl h) }⟩⟩
  have hr := P.result T hT
  rw [shapeOf_eq hpre.depth, openRust_run]
  simp only [oValue] at hr ⊢
  generalize (TM.sumcheck (eAt s (s.getReg .x17)) 3 (List.replicate 6 none)).run T = o at hr ⊢
  rcases o with _ | ⟨⟨pt, cl⟩, T'⟩
  · exact absurd hr hok
  obtain ⟨-, hvec, hcl, hT'⟩ := hr
  have hbuf := hvec.buf
  have hvl := hvec.vec.len
  simp only [NewBuf] at hbuf
  have mbuf : Misses (fun a ↦ SW s m x a ∨ Within a (oOut s) 1584)
      (vecPtr m (s.getReg .x2 - 1688)) (24 * (vecLen m (s.getReg .x2 - 1688)).toNat) := by
    have hof := hpre.outFree
    have hab := hpre.stack.above
    have hHm := P.heap.hi
    intro y hy h
    by_cases hl0 : (vecLen m (s.getReg .x2 - 1688)).toNat = 0
    · simp only [Within, hl0] at hy; omega
    rcases h with h | h
    · exact missSW hHx (by addr_omega [hbuf, hvl, hHm, hab, hb, hl0])
        ⟨Or.inl (by addr_omega [hbuf, hvl, hl0]), by addr_omega [hbuf, hvl, hHm, hl0]⟩
        (by addr_omega [hbuf, hvl, hHm, hl0]) y hy h
    · simp only [oOut] at h
      addr_omega [hy, h, hof, hbuf, hvl, hHm, monoSm, hl0]
  refine ⟨by simp only [oOut]; rw [hcap]; exact hok, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_⟩
  · have := hvec.vec.raw
    simp only [RawVecOk, Buf] at this ⊢
    simp only [oOut] at hcap hptr ⊢
    rw [hcap, hptr]; omega
  · simp only [oOut]; rw [hlen, hcap]; exact hvl
  · simp only [oOut]; rw [hcap, hptr]; simp only [NewBuf]; omega
  · simp only [oOut, vecEs]
    rw [hptr, hlen, ← hvec.elems]
    exact Fmt.eListAt fun i hi h ↦ mbuf _ (by addr_omega [hi, hbuf, hvl, P.heap.hi]) h
  · simp only [oOut]; rw [rowt, X.row, hvec.elems]
  · simp only [oOut]; rw [valt, X.value, hcl]
  · simp only [oP] at e0 e1 e2 hT' hokm rm ⊢
    refine Fmt.transcriptAt hT' hokm rm.self (by rw [e0]; exact rm.proof)
      (by rw [e1, e2]; exact rm.stream) rm.sponge

/-- A transcript the machine's stands for: the statement's state read off memory. -/
theorem exists_T (s : MachineState) (p : Word) : ∃ T, TranscriptAt s p T :=
  ⟨⟨⟨eListAt s (streamPtr s p) (streamLen s p), []⟩, spongeAt s (p + 8),
    (s.getMem (p + 344)).toNat, (s.getMem (p + 352)).toNat, []⟩, rfl, rfl, rfl, rfl⟩

/-- `sumcheck`'s point, when it returned `Ok`: a `Vec` allocated since `s`. -/
theorem slotOk {s m : MachineState} (P : P2 s m)
    (hok : m.getMem (s.getReg .x2 - 1688) ≠ 0xffffffffffffffff) :
    VecOk m (s.getReg .x2 - 1688) 24 8 ∧
      NewBuf s m (vecPtr m (s.getReg .x2 - 1688)) ((vecCap m (s.getReg .x2 - 1688)).toNat * 24) 8 := by
  obtain ⟨T, hT⟩ := exists_T s (oP s)
  have hr := P.result T hT
  generalize (TM.sumcheck (eAt s (oValue s)) 3 (List.replicate 6 none)).run T = o at hr
  rcases o with _ | ⟨⟨pt, cl⟩, T'⟩
  · exact absurd hr hok
  · exact ⟨hr.2.1.vec, hr.2.1.buf⟩

theorem eListAt_drop (s : MachineState) (p : Word) (n k : Nat) :
    (eListAt s p n).drop k = eListAt s (p + BitVec.ofNat 64 (24 * k)) (n - k) := by
  apply List.ext_getElem (by simp [eListAt_length])
  intro i h1 h2
  simp only [List.getElem_drop, eListAt_getElem]
  rw [add_ofNat_add, Nat.mul_add]

theorem mul24 (w : Word) : w * 16 + w * 8 = BitVec.ofNat 64 (24 * w.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have h16 : (16 : Word).toNat = 16 := rfl
  have h8 : (8 : Word).toNat = 8 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h16, h8]
  omega

/-- Bytes apart from what `open` writes and outside the free heap miss it. -/
theorem missOpenW {s u : MachineState} (hu : HeapOk u) {lo : Word} {n : Nat}
    (h0 : Apart lo n (oOut s) 1584) (h1 : Apart lo n (oValue s) 24)
    (h2 : Apart lo n (oP s + 8) 344) (h3 : Apart lo n (stackLo s openStack) openStack)
    (h4 : Outside s lo n) (hn : lo.toNat + n ≤ 2 ^ 64) : Misses (OpenW s u) lo n := fun y hy h ↦ by
  have hsw := missSW (m := s) hu h3 h4 hn y hy
  simp only [OpenW] at h
  rcases h with h | h | h | h
  · addr_omega [hy, h, h0]
  · addr_omega [hy, h, h1]
  · addr_omega [hy, h, h2]
  · exact hsw h

/-- What the loops, and the zeroing before them, write: the row, `mul`'s results, `f + 80` and
the callees' stack. -/
@[rv_addr] def LoopW (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1688) 1536 ∨ Within a (s.getReg .x2 - 1768) 24 ∨
    Within a (s.getReg .x2 - 128) 24 ∨ Within a (s.getReg .x2 - 1776) 8 ∨
    Within a (stackLo s openStack) 1632

/-- The segments' and the slots' weights `open` computes. -/
def sgOf (s : MachineState) : List E :=
  eqKernelRust ((claimAt s (oClaim s)).point.drop ((s.getReg .x12).toNat - 4))

def slOf (s m : MachineState) : List E := eqKernelRust (vecEs m (s.getReg .x2 - 1688))

/-- After both `eq_kernel`s: what the rest reads. -/
structure Mid (s m u : MachineState) : Prop where
  x2 : u.getReg .x2 = s.getReg .x2 - 1856
  saved : Saved s u
  cap : u.getMem (s.getReg .x2 - 1848) = m.getMem (s.getReg .x2 - 1688)
  ptr : u.getMem (s.getReg .x2 - 1840) = m.getMem (s.getReg .x2 - 1680)
  len : u.getMem (s.getReg .x2 - 1832) = m.getMem (s.getReg .x2 - 1672)
  out : u.getMem (s.getReg .x2 - 1824) = s.getReg .x10
  first : u.getMem (s.getReg .x2 - 1792) = s.getReg .x15
  count : u.getMem (s.getReg .x2 - 1784) = s.getReg .x16
  value : eAt u (s.getReg .x2 - 152) = eAt m (s.getReg .x2 - 1664)
  sg : NewVecE m u (s.getReg .x2 - 1736) (sgOf s)
  sl : NewVecE m u (s.getReg .x2 - 1712) (slOf s m)
  heap : HeapOk u
  mono : heapNext m ≤ heapNext u
  frame : DFrame m u (SW s m u)

theorem newVecE_keep {m u v : MachineState} {a : Word} {xs : List E} (h : NewVecE m u a xs)
    {w : Word → Prop} (hf : DFrame u v w) (hu : HeapOk u) (hN : heapNext v = heapNext u)
    (ha : ∀ i < 24, ¬ w (a + BitVec.ofNat 64 i)) (hb : ∀ y, y.toNat < heapNext u → ¬ w y)
    : NewVecE m v a xs := by
  have e0 : v.getMem a = u.getMem a := hf a fun i hi ↦ ha i (by omega)
  have e8 : v.getMem (a + 8) = u.getMem (a + 8) := hf _ fun i hi ↦ by
    rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, add_ofNat_add]; exact ha _ (by omega)
  have e16 : v.getMem (a + 16) = u.getMem (a + 16) := hf _ fun i hi ↦ by
    rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, add_ofNat_add]; exact ha _ (by omega)
  have hv := h.vec
  have hbuf := h.buf
  have hl := hv.len
  have hr := hv.raw
  simp only [NewBuf] at hbuf
  simp only [RawVecOk, Buf] at hr
  simp only [vecCap, vecPtr, vecLen] at hl hr hbuf
  have := hu.hi
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [RawVecOk, Buf, vecCap, vecPtr, hN, e0, e8]; exact hr
  · simp only [vecLen, vecCap, e0, e16]; exact hl
  · simp only [NewBuf, vecCap, vecPtr, hN, e0, e8]; exact hbuf
  · rw [← h.elems]
    simp only [vecEs, vecPtr, vecLen, e8, e16]
    by_cases hl0 : (u.getMem (a + 16)).toNat = 0
    · simp only [hl0]; rfl
    · exact hf.eListAt fun i hi ↦ hb _ (by addr_omega [hi, hbuf, hl, hl0])

end Rv64Verifier.Gkr.Open
