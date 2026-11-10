import Rv64Verifier.Proofs.Multilinear.Contracts
import Rv64Verifier.Proofs.Runtime.Inv
import Rv64Verifier.Proofs.Transcript.Contracts
import Rv64Verifier.Blocks.F72

/-!
# `<[Vec<E>] as Concat<E>>::concat` for two `Vec`s

compiled at `0x8000eea4` (`Blocks/F72.lean`), with `S` the entry's `sp`: `0x8000eea4` saves `ra`,
`s0`..`s3` in a 64-byte frame (`s0` = the result, `s1` = the two `Vec`s, `s2`/`s3` their
lengths) and calls `try_allocate_in(S - 64, len₀ + len₁, 0, 8, 24)`; `0x8000eee8` traps on
`Err`; `0x8000eef0` makes the `Vec` at `S - 64` and extends it by the first part, `0x8000ef24` by
the second (`spec_extend`, room enough); `0x8000ef44` copies the `Vec` out, restores and returns.
Until that last block only the stack below the saved registers, `NEXT` and the new buffer are
written.
-/

namespace Rv64Verifier.Proofs.Multilinear.Concat
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.MultilinearContracts Rv64Verifier.Blocks.F72
  Rv64Verifier.Transcript
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

def slots : List (Nat × Reg) := [(8, .x1), (16, .x8), (24, .x9), (32, .x18), (40, .x19)]

def kept : List Reg := [.x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- The stack below the saved registers. -/
@[rv_addr] def W (s : MachineState) (a : Word) : Prop := Within a (stackLo s concatStack) 232

abbrev Inv (s u : MachineState) (nx : Word) : Prop := FnInv s u 64 slots kept (W s) nx

theorem bounds {s : MachineState} (h : ConcatPre s) :
    0x78000110 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (s.getReg .x10).toNat % 8 = 0 ∧
      (s.getReg .x10).toNat + 24 ≤ 0xc0000000 := by
  have := h.stack.bounds (by decide) (by decide)
  have ha := h.stack.above
  have ho := h.out
  simp only [concatStack, stackLo, heapEnd, Region, Mapped] at this ha ho
  rw [this.2.2.2] at ha
  omega

theorem stack64 {s : MachineState} (h : ConcatPre s) : RtStack s 64 := by
  have hb := bounds h
  have hst := h.stack
  have hn := hst.next
  have hro := hst.rodata
  refine ⟨⟨?_, hst.aligned⟩, by addr_omega [hb], by addr_omega [hb, hn], by addr_omega [hb, hro]⟩
  exact ValidMemRange.sub hst.valid (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])

theorem Inv.step {s u v : MachineState} {nx nx' : Word} {X : Word → Prop}
    (hpre : ConcatPre s) (h : Inv s u nx) (hX : ByteFrame u v X)
    (hXsub : ∀ a, X a → W s a ∨ Within a nextAddr 8 ∨ (heapNext s ≤ a.toNat ∧ a.toNat < nx'.toNat))
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hr : ∀ r ∈ Reg.x2 :: kept, v.getReg r = u.getReg r) : Inv s v nx' := by
  have hb := bounds hpre
  exact FnInv.step (m := 40) h (stack64 hpre) (by decide) (by decide) (by decide)
    (fun a ha ha' ↦ by simp only [W] at ha; addr_omega [ha, ha', hb]) hX hXsub hnx hle hend
    (hr _ (by decide)) fun r hr' ↦ hr r (List.mem_cons_of_mem _ hr')

theorem Inv.same {s u v : MachineState} {nx : Word} (hpre : ConcatPre s) (h : Inv s u nx)
    (hm : ∀ a, v.getMem a = u.getMem a) {l : List Reg} (hk : ∀ r ∈ l, v.getReg r = u.getReg r)
    (hl : ∀ r ∈ Reg.x2 :: kept, r ∈ l := by decide) : Inv s v nx :=
  h.step hpre (ByteFrame.of_same hm fun _ ↦ False) (fun _ h ↦ h.elim) ((hm _).trans h.next)
    (Nat.le_refl _) h.fits fun r hr ↦ hk r (hl r hr)

theorem eListAt_add (s : MachineState) (p : Word) (a b : Nat) :
    eListAt s p (a + b) = eListAt s p a ++ eListAt s (p + BitVec.ofNat 64 (24 * a)) b := by
  simp only [eListAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

theorem eListAt_same {u v : MachineState} (h : ∀ a, v.getMem a = u.getMem a) (P : Word) (N : Nat) :
    eListAt v P N = eListAt u P N := by
  simp only [eListAt, eAt, h]

/-- A part's elements: in the heap below `NEXT`, or none. -/
theorem part_ok {s : MachineState} {a : Word} (h : VecOk s a 24 8) :
    (vecPtr s a).toNat % 8 = 0 ∧ ((vecLen s a).toNat = 0 ∨
      heapStart ≤ (vecPtr s a).toNat ∧ (vecPtr s a).toNat + 24 * (vecLen s a).toNat ≤ heapNext s) := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, ?_⟩
  rcases h2 with h2 | h2
  · left; omega
  · right; omega

/-- The end of a part, `ptr + 24 len` as compiled. -/
theorem end_toNat {P L : Word} (h : L.toNat = 0 ∨ P.toNat + 24 * L.toNat ≤ heapEnd) :
    P + (L * 16 + L * 8) = P + BitVec.ofNat 64 (24 * L.toNat) := by
  rcases h with h | h
  · have : L = 0 := BitVec.eq_of_toNat_eq (by simpa using h)
    subst this; simp
  · addr_omega [h]

/-- `spec_extend`'s precondition at either call: the `Vec` at `S - 64` (capacity `C`, buffer `Q`,
length `l`), the part `Ps` of `Ls` elements. -/
theorem extend_pre {s u : MachineState} (hpre : ConcatPre s) {C Q Ps : Word} {l Ls : Nat}
    (hsp : u.getReg .x2 = s.getReg .x2 - 64) (hx10 : u.getReg .x10 = s.getReg .x2 - 64)
    (hx11 : u.getReg .x11 = Ps) (hx12 : u.getReg .x12 = Ps + BitVec.ofNat 64 (24 * Ls))
    (hcap : u.getMem (s.getReg .x2 - 64) = C) (hptr : u.getMem (s.getReg .x2 - 56) = Q)
    (hlen : u.getMem (s.getReg .x2 - 48) = BitVec.ofNat 64 l)
    (hroom : l + Ls ≤ C.toNat) (hQa : Q.toNat % 8 = 0)
    (hQ : C.toNat = 0 ∨ heapNext s ≤ Q.toNat ∧ Q.toNat + 24 * C.toNat ≤ heapNext u)
    (hPa : Ps.toNat % 8 = 0)
    (hPs : Ls = 0 ∨ heapStart ≤ Ps.toNat ∧ Ps.toNat + 24 * Ls ≤ heapNext s)
    (hheap : HeapOk u) (hmono : heapNext s ≤ heapNext u) :
    ExtendPre u ∧ extendLen u = Ls ∧ extendDst u = Q + BitVec.ofNat 64 (24 * l) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hro := hst.rodata
  have hfit := hheap.hi
  have hlo := hpre.heap.lo
  simp only [heapNext, heapStart, heapEnd] at hQ hPs hfit hmono hlo
  have hQ' : C.toNat = 0 ∨ heapNext s ≤ Q.toNat ∧ Q.toNat + 24 * C.toNat ≤ heapEnd := by
    simp only [heapNext, heapEnd]; omega
  have hPs' : Ls = 0 ∨ 0x20 ≤ Ps.toNat ∧ Ps.toNat + 24 * Ls ≤ heapNext s := by
    simp only [heapNext]; omega
  have hl : l < 2 ^ 32 := by omega
  have hLs : Ls < 2 ^ 32 := by omega
  have hel : extendLen u = Ls := by
    simp only [extendLen, hx11, hx12]
    rcases hPs' with h0 | h0
    · subst h0; simp
    · have : (Ps + BitVec.ofNat 64 (24 * Ls)).toNat = Ps.toNat + 24 * Ls := by
        addr_omega [h0, hfit, hmono]
      omega
  have hvl : (vecLen u (u.getReg .x10)).toNat = l := by
    simp only [vecLen, hx10]; rv_eval [hlen]; rw [BitVec.toNat_ofNat]; omega
  have hdst : extendDst u = Q + BitVec.ofNat 64 (24 * l) := by
    rw [extendDst, hvl]; simp only [vecPtr, hx10]; rv_eval [hptr]
  have hsl : stackLo u extendStack = s.getReg .x2 - 128 := by
    simp only [stackLo, extendStack, memcpyStack, hsp, Sym.sub_sub_lit]; rfl
  refine ⟨{
    heap := hheap
    vec := by rw [hx10]; valid_sub hst.valid [hb]
    ok := ⟨⟨by simp only [vecPtr, hx10]; rv_eval [hptr]; exact hQa, by
        simp only [vecPtr, vecCap, hx10]; rv_eval [hptr, hcap]
        simp only [heapStart, heapNext]
        rcases hQ with h0 | h0
        · left; omega
        · right; omega⟩, by
        rw [hvl]; simp only [vecCap, hx10, hcap]; omega⟩
    room := by rw [hvl, hel]; simp only [vecCap, hx10, hcap]; exact hroom
    bounds := by rw [hx11, hx12]; rcases hPs' with h0 | h0 <;> addr_omega [h0, hfit, hmono]
    whole := by
      rw [hx11, hx12]
      rcases hPs' with h0 | h0
      · subst h0; simp
      · have : (Ps + BitVec.ofNat 64 (24 * Ls)).toNat = Ps.toNat + 24 * Ls := by
          addr_omega [h0, hfit, hmono]
        omega
    src := by
      rw [hel, hx11]
      rcases hPs' with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (Or.inl ⟨h0.1, by simp only [heapNext] at h0; omega⟩)
    srcAlign := Or.inr (by rw [hx11]; exact hPa)
    stack := ⟨⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [hsp]; addr_omega [hb]⟩,
      by rw [hsl]; addr_omega [hab, hb], by rw [hsl]; addr_omega [hnx8, hb],
      by rw [hsl]; addr_omega [hro, hb]⟩
    vecStack := by rw [hx10, hsl]; addr_omega [hb]
    vecHeap := by
      rw [hx10]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    srcStack := by rw [hel, hx11, hsl]; rcases hPs' with h0 | h0 <;> addr_omega [h0, hb, hab, hmono, hfit]
    srcVec := by rw [hel, hx11, hx10]; rcases hPs' with h0 | h0 <;> addr_omega [h0, hb, hab, hmono, hfit]
    srcDst := by
      rw [hel, hx11, hdst]
      rcases hPs' with h0 | h0
      · addr_omega [h0]
      · rcases hQ' with h1 | h1 <;> addr_omega [h0, h1, hroom, hfit, hmono]
    dstVec := by
      rw [hel, hx10, hdst]
      rcases hQ' with h1 | h1 <;> addr_omega [h1, hroom, hb, hab] }, hel, hdst⟩

/-- The epilogue: the `Vec` (capacity `C`, buffer `Q`) copied out, the registers restored. -/
theorem exit {s u : MachineState} {nx C Q : Word} (hpre : ConcatPre s) (hu : Inv s u nx)
    (hpc : u.pc = 0x8000ef44) (hsp₇ : u.getReg .x2 = s.getReg .x2 - 64)
    (hx8₇ : u.getReg .x8 = s.getReg .x10) (hcap₇ : u.getMem (s.getReg .x2 - 64) = C)
    (hptr₇ : u.getMem (s.getReg .x2 - 56) = Q) (hlen₇ : (u.getMem (s.getReg .x2 - 48)).toNat = C.toNat)
    (hel : eListAt u Q C.toNat = vecEs s (s.getReg .x11) ++ vecEs s (s.getReg .x11 + 24))
    (hQa : Q.toNat % 8 = 0)
    (hQr : C.toNat = 0 ∨ heapNext s ≤ Q.toNat ∧ Q.toNat + 24 * C.toNat ≤ nx.toNat) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧ ConcatPost s t := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hof := hpre.outFree
  simp only [Outside] at hof
  have hos := hpre.outStack
  have hfit₂ := hu.fits
  have hmono := hu.mono
  have hlo := hpre.heap.lo
  have hro' := hpre.out
  simp only [Region, Mapped] at hro'
  obtain ⟨t, hr₈, h₈⟩ := Sym.BlockSpec.reaches b8000ef44_spec hpc (by
      rv_eval [hsp₇, hx8₇]
      and_intros <;> first
        | valid_access hst.valid [hb]
        | exact Region.valid hpre.out (by addr_omega [hro']) (by addr_omega [hro'])
            (by addr_omega [hro'])
        | addr_omega [hos, hb, hro'])
  have k₈ := b8000ef44_keeps h₈
  have hm₈ := b8000ef44_frame h₈ (by rw [hx8₇]; addr_omega [hro'])
  rw [hx8₇] at hm₈
  have hsl := hu.slots
  simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true] at hsl
  rv_eval [] at hsl
  obtain ⟨sl1, sl2, sl3, sl4, sl5⟩ := hsl
  have pc := b8000ef44_pc h₈
  have x2 := b8000ef44_x2 h₈
  have x8 := b8000ef44_x8 h₈
  have x9 := b8000ef44_x9 h₈
  have x18 := b8000ef44_x18 h₈
  have x19 := b8000ef44_x19 h₈
  have o0 := b8000ef44_m_x8_0 h₈
  have o8 := b8000ef44_m_x8_8 h₈
  have o16 := b8000ef44_m_x8_16 h₈
  rw [hx8₇] at o0 o8 o16
  rv_eval [hsp₇, sl1, sl2, sl3, sl4, sl5] at pc x2 x8 x9 x18 x19 o0 o8 o16
  rw [hcap₇] at o0
  rw [hptr₇] at o8
  have hnt : t.getMem nextAddr = nx := (hm₈ _ (by addr_omega [hof.2, hro'])).trans hu.next
  have hn : heapNext t = nx.toNat := by simp only [heapNext, hnt]
  have hLt : (t.getMem (s.getReg .x10 + 16)).toNat = C.toNat := by rw [o16]; exact hlen₇
  have hbf : ByteFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨ (W s a ∨
      Within a (stackLo s 64) 64 ∨ Within a nextAddr 8 ∨
        (heapNext s ≤ a.toNat ∧ a.toNat < nx.toNat)) :=
    (hu.mem.mono fun a ha ↦ Or.inr ha).trans (ByteFrame.of_memFrame hm₈ (by addr_omega [hro'])
      (by decide) (h₈.unaligned (by rv_eval [hx8₇]; and_intros <;> addr_omega [hro', hb])))
      fun a ha ↦ Or.inl ha
  have hE8 : eListAt t Q C.toNat = eListAt u Q C.toNat :=
    (DFrame.of_memFrame hm₈).eListAt fun i hi hx ↦ by
      rcases hQr with h0 | h0
      · omega
      · simp only [heapNext] at h0
        rcases hof.1 with h1 | h1 <;> addr_omega [hx, hi, h0, h1, hfit₂]
  refine ⟨t, hr₈, pc.trans (returnAddress_eq s).symm,
    preserves_of x2 x8 x9 x18 x19 fun r hr' ↦ ?_, {
      heap := ⟨by rw [hn]; omega, by rw [hn]; exact hfit₂⟩
      mono := by rw [hn]; exact hmono
      value := {
        vec := ⟨⟨by simp only [vecPtr, o8]; exact hQa, by
            simp only [vecPtr, vecCap, o8, o0, heapStart, hn]
            simp only [heapStart] at hlo
            rcases hQr with h0 | h0
            · left; omega
            · right; omega⟩,
          by simp only [vecLen, vecCap, hLt, o0]; omega⟩
        buf := ⟨by simp only [vecPtr, o8]; exact hQa, by
            simp only [vecPtr, vecCap, o8, o0, hn]
            rcases hQr with h0 | h0
            · left; omega
            · right; omega⟩
        elems := by rw [vecEs, vecPtr, vecLen, o8, hLt, hE8, hel] }
      frame := (DFrame.of_byteFrame hbf).mono fun a ha ↦ ?_ }⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (k₈ _ (by decide)).trans (hu.kept _ (by decide))
  · rcases ha with ha | ha | ha | ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inl (by simp only [W] at ha; addr_omega [ha, hb]))
    · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (by simp only [Fresh, hn]; exact ha)))

/-- **`concat` of two `Vec`s meets its contract**, given `try_allocate_in`'s and
`spec_extend`'s. -/
theorem concat_spec (hT : TryAllocZeroedSpec) (hE : ExtendSpec) : ConcatSpec := by
  intro s hpc hpre
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hro := hst.rodata
  have hheap := hpre.heap
  have hlo := hheap.lo
  have hos := hpre.outStack
  have hof := hpre.outFree
  simp only [Outside] at hof
  have hps := hpre.partsStack
  have hpf := hpre.partsFree
  simp only [Outside] at hpf
  have hpr := hpre.parts
  simp only [Region, Mapped] at hpr
  obtain ⟨ha0, hl0⟩ := part_ok hpre.left
  obtain ⟨ha1, hl1⟩ := part_ok hpre.right
  simp only [vecPtr, vecLen] at ha0 hl0 ha1 hl1
  rv_eval [] at ha1 hl1
  obtain ⟨P0, hP0⟩ : ∃ P, P = s.getMem (s.getReg .x11 + 8) := ⟨_, rfl⟩
  obtain ⟨L0, hL0⟩ : ∃ L, L = s.getMem (s.getReg .x11 + 16) := ⟨_, rfl⟩
  obtain ⟨P1, hP1⟩ : ∃ P, P = s.getMem (s.getReg .x11 + 32) := ⟨_, rfl⟩
  obtain ⟨L1, hL1⟩ : ∃ L, L = s.getMem (s.getReg .x11 + 40) := ⟨_, rfl⟩
  simp only [← hP0, ← hL0] at ha0 hl0
  simp only [← hP1, ← hL1] at ha1 hl1
  have hfit := hheap.hi
  simp only [heapStart, heapNext, heapEnd] at hl0 hl1 hlo hfit
  -- `0x8000eea4`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000eea4_spec hpc (by
    rv_eval []
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hpre.parts (by addr_omega [hpr]) (by addr_omega [hpr]) (by addr_omega [hpr])
      | addr_omega [hps, hb, hpr])
  have k₁ := b8000eea4_keeps h₁
  have inv₁ : Inv s t₁ (s.getMem nextAddr) := FnInv.init hheap (stack64 hpre)
    (by rw [b8000eea4_x2 h₁]; rfl)
    (by
      simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      rv_eval []
      exact ⟨b8000eea4_m_x2_n8 h₁, b8000eea4_m_x2_n16 h₁, b8000eea4_m_x2_n24 h₁,
        b8000eea4_m_x2_n32 h₁, b8000eea4_m_x2_n40 h₁⟩)
    (fun r hr ↦ k₁ r (mem_of_mem hr _))
    ((b8000eea4_frame h₁ (by addr_omega [hb])).mono fun a ha ↦ by addr_omega [ha, hb])
    (h₁.unaligned (by rv_eval []; and_intros <;> addr_omega [hb])) (by decide)
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - 64 := b8000eea4_x2 h₁
  have hx10₁ : t₁.getReg .x10 = s.getReg .x2 - 64 := b8000eea4_x10 h₁
  have hn₁ : heapNext t₁ = heapNext s := by simp only [heapNext, inv₁.next]
  have hsl : stackLo t₁ tryAllocStack = s.getReg .x2 - 112 := by
    simp only [stackLo, tryAllocStack, hsp₁, Sym.sub_sub_lit]; rfl
  have hN : (t₁.getReg .x11).toNat = L0.toNat + L1.toNat := by
    rw [b8000eea4_x11 h₁, ← hL0, ← hL1]
    rcases hl0 with h0 | h0 <;> rcases hl1 with h1 | h1 <;> addr_omega [h0, h1, hfit]
  have hpre₁ : TryAllocPre .x13 .x14 t₁ := {
    heap := ⟨hn₁ ▸ hheap.lo, hn₁ ▸ hheap.hi⟩
    out := by rw [hx10₁]; valid_sub hst.valid [hb]
    align := by rw [b8000eea4_x13 h₁]; decide
    size := by rw [b8000eea4_x14 h₁]; decide
    stack := ⟨⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [hsp₁]; addr_omega [hb]⟩,
      by rw [hsl]; addr_omega [hab, hb], by rw [hsl]; addr_omega [hnx8, hb],
      by rw [hsl]; addr_omega [hro, hb]⟩
    outFree := by
      rw [hx10₁]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    outStack := by rw [hx10₁, hsl]; addr_omega [hb] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂, -⟩ | hdead⟩ := hT.call hr₁ (b8000eea4_pc h₁) hpre₁
  swap
  · exact ⟨t₂, hr₂, Or.inr hdead⟩
  have hfr₂ := hpost₂.frame
  rw [hx10₁, hsl] at hfr₂
  have inv₂ : Inv s t₂ (t₂.getMem nextAddr) := inv₁.step hpre hfr₂ (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr (Or.inl ha)
      · simp only [Fresh, hn₁] at ha
        exact Or.inr (Or.inr ha))
    rfl (by rw [← heapNext, ← heapNext, ← hn₁]; exact hpost₂.mono) hpost₂.heap.hi
    fun r hr ↦ hpres₂ r (by unfold calleeSaved; exact mem_of_mem hr _)
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - 64 := (hpres₂.reg .x2).trans hsp₁
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000eee8_spec
    (by rw [hpc₂, returnAddress_eq, b8000eea4_x1 h₁]; decide) (by
      rv_eval [hsp₂]
      valid_access hst.valid [hb])
  rcases eq_or_ne (t₂.getMem (s.getReg .x2 - 64)) 0 with htag | htag
  swap
  · refine ⟨t₃, hr₂.trans hr₃, Or.inr (dead_of_fetch ?_)⟩
    rw [b8000eee8_pc_taken h₃ (by rw [hsp₂]; exact htag)]
    exact Option.isNone_iff_eq_none.mp (by decide +kernel)
  have k₃ := b8000eee8_keeps h₃
  have hm₃ := b8000eee8_mem_same h₃
  have inv₃ := inv₂.same hpre hm₃ k₃
  obtain ⟨hcap, hbuf⟩ := hpost₂.ok (by rw [hx10₁]; exact htag)
  rw [hx10₁] at hcap hbuf
  rw [b8000eea4_x14 h₁, b8000eea4_x13 h₁, hN] at hbuf
  rv_eval [] at hcap hbuf
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = t₂.getMem (s.getReg .x2 - 48) := ⟨_, rfl⟩
  rw [← hQ] at hbuf
  simp only [NewBuf, heapNext] at hbuf
  have hn₁' : (t₁.getMem nextAddr).toNat = (s.getMem nextAddr).toNat := hn₁
  have hfit₂ := hpost₂.heap.hi
  have hmono₂ := hpost₂.mono
  simp only [heapNext, heapEnd] at hfit₂ hmono₂
  have hQa : Q.toNat % 8 = 0 := hbuf.1
  have hQr : L0.toNat + L1.toNat = 0 ∨ (s.getMem nextAddr).toNat ≤ Q.toNat ∧
      Q.toNat + (L0.toNat + L1.toNat) * 24 ≤ (t₂.getMem nextAddr).toNat := by
    rcases hbuf.2 with h | h
    · left; omega
    · right; exact ⟨by rw [← hn₁']; exact h.1, h.2⟩
  -- what the run keeps: the parts and their elements
  have hpart (u : MachineState) (nx : Word) (hu : Inv s u nx) (c : Nat) (hc : c + 8 ≤ 48) :
      u.getMem (s.getReg .x11 + BitVec.ofNat 64 c) = s.getMem (s.getReg .x11 + BitVec.ofNat 64 c) := by
    have hf := hu.fits
    simp only [heapEnd] at hf
    exact hu.mem.getMem fun i hi hx ↦ by
      rcases hx with hx | hx | hx | hx
      · simp only [W] at hx; addr_omega [hx, hi, hc, hps, hb, hpr]
      · addr_omega [hx, hi, hc, hps, hb, hpr]
      · addr_omega [hx, hi, hc, hpf.2, hpr]
      · rcases hpf.1 with h | h <;> addr_omega [hx, hi, hc, h, hf, hpr]
  have hsrc (u : MachineState) (nx : Word) (hu : Inv s u nx) (P : Word) (L : Nat)
      (hPL : L = 0 ∨ 536870912 ≤ P.toNat ∧ P.toNat + 24 * L ≤ (s.getMem nextAddr).toNat) :
      eListAt u P L = eListAt s P L := by
    have hf := hu.fits
    simp only [heapEnd] at hf
    refine (DFrame.of_byteFrame hu.mem).eListAt fun i hi hx ↦ ?_
    rcases hPL with h0 | h0
    · omega
    rcases hx with hx | hx | hx | hx
    · simp only [W] at hx; addr_omega [hx, hi, h0, hb, hab, hlo, hfit]
    · addr_omega [hx, hi, h0, hb, hab, hlo, hfit]
    · addr_omega [hx, hi, h0, hfit]
    · simp only [heapNext] at hx; addr_omega [hx, hi, h0]
  -- `0x8000eef0`: the `Vec`, then the first part
  have hx9₃ : t₃.getReg .x9 = s.getReg .x11 := by
    rw [k₃ .x9 (by decide), hpres₂.reg .x9, b8000eea4_x9 h₁]
  have hx19₃ : t₃.getReg .x19 = L0 := by
    rw [k₃ .x19 (by decide), hpres₂.reg .x19, b8000eea4_x19 h₁, hL0]
  have hx18₃ : t₃.getReg .x18 = L1 := by
    rw [k₃ .x18 (by decide), hpres₂.reg .x18, b8000eea4_x18 h₁, hL1]
  have hsp₃ : t₃.getReg .x2 = s.getReg .x2 - 64 := (k₃ .x2 (by decide)).trans hsp₂
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000eef0_spec
    (b8000eee8_pc_not_taken h₃ (by rw [hsp₂]; exact htag)) (by
      rv_eval [hsp₃, hx9₃]
      and_intros <;> first
        | valid_access hst.valid [hb]
        | exact Region.valid hpre.parts (by addr_omega [hpr]) (by addr_omega [hpr])
            (by addr_omega [hpr]))
  have k₄ := b8000eef0_keeps h₄
  have hm₄ := b8000eef0_frame h₄ (by rw [hsp₃]; addr_omega [hb])
  rw [hsp₃] at hm₄
  have inv₄ := inv₃.step hpre (ByteFrame.of_memFrame hm₄ (by addr_omega [hb]) (by decide)
      (h₄.unaligned (by rv_eval [hsp₃]; and_intros <;> addr_omega [hb])))
    (fun a ha ↦ Or.inl (by addr_omega [ha, hb])) ((hm₄ _ (by addr_omega [hb, hnx8])).trans inv₃.next)
    (Nat.le_refl _) inv₃.fits fun r hr ↦ k₄ r (mem_of_mem hr _)
  have c0 := b8000eef0_m_x2_0 h₄
  have c8 := b8000eef0_m_x2_8 h₄
  have c16 := b8000eef0_m_x2_16 h₄
  rw [hsp₃] at c0 c8 c16
  rv_eval [hm₃] at c0 c8 c16
  rw [hcap] at c0
  rw [← hQ] at c8
  have hP0₃ : t₃.getMem (s.getReg .x11 + 8) = P0 := by
    have := hpart t₃ _ inv₃ 8 (by decide); rv_eval [] at this; rw [this, hP0]
  have hP1₅ (u : MachineState) (nx : Word) (hu : Inv s u nx) :
      u.getMem (s.getReg .x11 + 32) = P1 := by
    have := hpart u _ hu 32 (by decide); rv_eval [] at this; rw [this, hP1]
  have hsp₄ : t₄.getReg .x2 = s.getReg .x2 - 64 := (k₄ .x2 (by decide)).trans hsp₃
  have hfit₄ := inv₄.fits
  have hmono₄ := inv₄.mono
  have hnx₄ := inv₄.next
  have hheap₄ : HeapOk t₄ := ⟨by simp only [heapNext, heapStart, hnx₄] at hlo hmono₄ ⊢; omega,
    by simp only [heapNext, hnx₄]; exact hfit₄⟩
  have hmono₄' : heapNext s ≤ heapNext t₄ := by simp only [heapNext, hnx₄] at hmono₄ ⊢; omega
  have hQ₄ : (t₁.getReg .x11).toNat = 0 ∨ heapNext s ≤ Q.toNat ∧
      Q.toNat + 24 * (t₁.getReg .x11).toNat ≤ heapNext t₄ := by
    rw [hN]; simp only [heapNext, hnx₄]; omega
  obtain ⟨hep₄, hel₄, hdst₄⟩ := extend_pre (u := t₄) (l := 0) hpre hsp₄ (b8000eef0_x10 h₄ ▸ hsp₃)
    (by rw [b8000eef0_x11 h₄, hx9₃, hP0₃])
    (by rw [b8000eef0_x12 h₄, hx9₃, hP0₃, hx19₃]; exact end_toNat (by omega))
    c0 c8 (by rw [c16]; rfl) (by rw [hN]; omega) hQa hQ₄ ha0
    (by simp only [heapStart, heapNext]; omega) hheap₄ hmono₄'
  obtain ⟨t₅, hr₅, ⟨hpc₅, hpres₅, hpost₅⟩ | hdead⟩ := hE.call hr₄ (b8000eef0_pc h₄) hep₄
  swap
  · exact ⟨t₅, hr₂.trans (hr₃.trans hr₅), Or.inr hdead⟩
  have hx10₄ : t₄.getReg .x10 = s.getReg .x2 - 64 := b8000eef0_x10 h₄ ▸ hsp₃
  have hfr₅ := hpost₅.frame
  rw [hx10₄, hdst₄, hel₄] at hfr₅
  simp only [stackLo, extendStack, memcpyStack, hsp₄, Sym.sub_sub_lit] at hfr₅
  have hX₅ (a : Word) (ha : Within a (s.getReg .x2 - 64 + 16) 8 ∨
      Within a (Q + BitVec.ofNat 64 (24 * 0)) (24 * L0.toNat) ∨
      Within a (s.getReg .x2 - BitVec.ofNat 64 (64 + (48 + 16))) (48 + 16)) :
      W s a ∨ Within a nextAddr 8 ∨ (heapNext s ≤ a.toNat ∧ a.toNat < (t₂.getMem nextAddr).toNat) := by
    rcases ha with ha | ha | ha
    · exact Or.inl (by simp only [W]; addr_omega [ha, hb])
    · right; right
      simp only [heapNext]
      rcases hQr with h0 | h0
      · addr_omega [ha, h0]
      · addr_omega [ha, h0]
    · exact Or.inl (by simp only [W]; addr_omega [ha, hb])
  have hnext₅ : t₅.getMem nextAddr = t₂.getMem nextAddr := by
    have := hpost₅.next; simp only [heapNext] at this
    exact (BitVec.eq_of_toNat_eq this).trans inv₄.next
  have inv₅ := inv₄.step hpre hfr₅ hX₅ hnext₅ (Nat.le_refl _) inv₄.fits
    fun r hr ↦ hpres₅ r (by unfold calleeSaved; exact mem_of_mem hr _)
  have hlen₅ := hpost₅.len
  have hcap₅ := hpost₅.cap
  have hptr₅ := hpost₅.ptr
  have hnew₅ := hpost₅.new
  rw [hx10₄] at hlen₅ hcap₅ hptr₅
  rw [hdst₄, hel₄, b8000eef0_x11 h₄, hx9₃, hP0₃] at hnew₅
  simp only [vecLen, vecCap, vecPtr] at hlen₅ hcap₅ hptr₅
  rv_eval [c0, c8, c16] at hlen₅ hcap₅ hptr₅
  -- `0x8000ef24`: the second part
  have hx9₅ : t₅.getReg .x9 = s.getReg .x11 := by
    rw [hpres₅.reg .x9, k₄ .x9 (by decide), hx9₃]
  have hsp₅ : t₅.getReg .x2 = s.getReg .x2 - 64 := (hpres₅.reg .x2).trans hsp₄
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000ef24_spec
    (by rw [hpc₅, returnAddress_eq, b8000eef0_x1 h₄]; decide) (by
      rv_eval [hx9₅]
      exact Region.valid hpre.parts (by addr_omega [hpr]) (by addr_omega [hpr]) (by addr_omega [hpr]))
  have k₆ := b8000ef24_keeps h₆
  have hm₆ := b8000ef24_mem_same h₆
  have inv₆ := inv₅.same hpre hm₆ k₆
  have hsp₆ : t₆.getReg .x2 = s.getReg .x2 - 64 := (k₆ .x2 (by decide)).trans hsp₅
  have hfit₆ := inv₆.fits
  have hnx₆ := inv₆.next
  have hheap₆ : HeapOk t₆ := ⟨by simp only [heapNext, heapStart, hnx₆] at hlo hmono₄ ⊢; omega,
    by simp only [heapNext, hnx₆]; exact hfit₆⟩
  have hmono₆ : heapNext s ≤ heapNext t₆ := by simp only [heapNext, hnx₆] at hmono₄ ⊢; omega
  have hQ₆ : (t₁.getReg .x11).toNat = 0 ∨ heapNext s ≤ Q.toNat ∧
      Q.toNat + 24 * (t₁.getReg .x11).toNat ≤ heapNext t₆ := by
    rw [hN]; simp only [heapNext, hnx₆]; omega
  have hx18₅ : t₅.getReg .x18 = L1 := by rw [hpres₅.reg .x18, k₄ .x18 (by decide), hx18₃]
  have hL0w : t₆.getMem (s.getReg .x2 - 48) = BitVec.ofNat 64 L0.toNat := by
    rw [hm₆]; apply BitVec.eq_of_toNat_eq; rw [hlen₅, BitVec.toNat_ofNat]; omega
  obtain ⟨hep₆, hel₆, hdst₆⟩ := extend_pre (u := t₆) (l := L0.toNat) hpre hsp₆
    (by rw [b8000ef24_x10 h₆, hsp₅])
    (by rw [b8000ef24_x11 h₆, hx9₅, hP1₅ t₅ _ inv₅])
    (by rw [b8000ef24_x12 h₆, hx9₅, hP1₅ t₅ _ inv₅, hx18₅]; exact end_toNat (by omega))
    (by rw [hm₆, hcap₅]) (by rw [hm₆, hptr₅]) hL0w (by rw [hN]) hQa hQ₆ ha1
    (by simp only [heapStart, heapNext]; omega) hheap₆ hmono₆
  obtain ⟨t₇, hr₇, ⟨hpc₇, hpres₇, hpost₇⟩ | hdead⟩ := hE.call hr₆ (b8000ef24_pc h₆) hep₆
  swap
  · exact ⟨t₇, hr₂.trans (hr₃.trans (hr₅.trans hr₇)), Or.inr hdead⟩
  have hx10₆ : t₆.getReg .x10 = s.getReg .x2 - 64 := by rw [b8000ef24_x10 h₆, hsp₅]
  have hfr₇ := hpost₇.frame
  rw [hx10₆, hdst₆, hel₆] at hfr₇
  simp only [stackLo, extendStack, memcpyStack, hsp₆, Sym.sub_sub_lit] at hfr₇
  have hnext₇ : t₇.getMem nextAddr = t₂.getMem nextAddr := by
    have := hpost₇.next; simp only [heapNext] at this
    exact (BitVec.eq_of_toNat_eq this).trans inv₆.next
  have inv₇ := inv₆.step hpre hfr₇ (fun a ha ↦ by
      rcases ha with ha | ha | ha
      · exact Or.inl (by simp only [W]; addr_omega [ha, hb])
      · right; right
        simp only [heapNext]
        rcases hQr with h0 | h0
        · addr_omega [ha, h0]
        · addr_omega [ha, h0]
      · exact Or.inl (by simp only [W]; addr_omega [ha, hb]))
    hnext₇ (Nat.le_refl _) inv₆.fits
    fun r hr ↦ hpres₇ r (by unfold calleeSaved; exact mem_of_mem hr _)
  have hlen₇ := hpost₇.len
  have hcap₇ := hpost₇.cap
  have hptr₇ := hpost₇.ptr
  have hnew₇ := hpost₇.new
  rw [hx10₆] at hlen₇ hcap₇ hptr₇
  rw [hdst₆, hel₆, b8000ef24_x11 h₆, hx9₅, hP1₅ t₅ _ inv₅] at hnew₇
  simp only [vecLen, vecCap, vecPtr] at hlen₇ hcap₇ hptr₇
  rv_eval [hm₆, hL0w, hcap₅, hptr₅] at hlen₇ hcap₇ hptr₇
  have hsp₇ : t₇.getReg .x2 = s.getReg .x2 - 64 := (hpres₇.reg .x2).trans hsp₆
  have hx8₇ : t₇.getReg .x8 = s.getReg .x10 := by
    rw [hpres₇.reg .x8, k₆ .x8 (by decide), hpres₅.reg .x8, k₄ .x8 (by decide), k₃ .x8 (by decide),
      hpres₂.reg .x8, b8000eea4_x8 h₁]
  have h7 : eListAt t₇ Q L0.toNat = eListAt t₆ Q L0.toNat :=
    (DFrame.of_byteFrame hfr₇).eListAt fun i hi hx ↦ by
      rcases hQr with h0 | h0
      · omega
      · rcases hx with hx | hx | hx <;> addr_omega [hx, hi, h0, hfit₂, hb, hab]
  have h5 : eListAt t₅ Q L0.toNat = eListAt t₄ P0 L0.toNat := by
    have := hnew₅; simpa using this
  have hl0' : L0.toNat = 0 ∨ 536870912 ≤ P0.toNat ∧ P0.toNat + 24 * L0.toNat ≤
      (s.getMem nextAddr).toNat := by omega
  have hl1' : L1.toNat = 0 ∨ 536870912 ≤ P1.toNat ∧ P1.toNat + 24 * L1.toNat ≤
      (s.getMem nextAddr).toNat := by omega
  have hel : eListAt t₇ Q (t₁.getReg .x11).toNat =
      vecEs s (s.getReg .x11) ++ vecEs s (s.getReg .x11 + 24) := by
    rw [hN, eListAt_add, hnew₇, h7, eListAt_same hm₆, h5, hsrc t₄ _ inv₄ P0 _ hl0',
      hsrc t₆ _ inv₆ P1 _ hl1']
    simp only [vecEs, vecPtr, vecLen]
    rv_eval []
    rw [← hP0, ← hL0, ← hP1, ← hL1]
  obtain ⟨t, hr₈, ht⟩ := exit hpre inv₇ (by rw [hpc₇, returnAddress_eq, b8000ef24_x1 h₆]; decide)
    hsp₇ hx8₇ hcap₇ hptr₇ (by rw [hlen₇, hel₆, hN, ← hm₆, hL0w, BitVec.toNat_ofNat]; omega) hel hQa
    (by
      rw [hN]; simp only [heapNext]
      rcases hQr with h0 | h0
      · left; omega
      · right; omega)
  exact ⟨t, hr₂.trans (hr₃.trans (hr₅.trans (hr₇.trans hr₈))), Or.inl ht⟩

end Rv64Verifier.Proofs.Multilinear.Concat
