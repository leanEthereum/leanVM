import Rv64Verifier.Proofs.Multilinear.Concat
import Rv64Verifier.Blocks.F54

/-!
# `<[&[E]] as Concat<E>>::concat`

compiled at `0x8000cfc4` (`Blocks/F54.lean`), with `S` the entry's `sp`: `0x8000cfc4` saves `ra`,
`s0`..`s3` in a 64-byte frame (`s0` = the result, `s1` = the slices, `s2` = `16 count`);
`0x8000cff4` sums the lengths (a loop whose test follows its body: at least one slice);
`0x8000d004` calls `try_allocate_in(S - 64, total, 0, 8, 24)`, `0x8000d01c` traps on `Err`,
`0x8000d024` makes the `Vec` at `S - 64`; the loop at `0x8000d03c` extends it by each slice
(`spec_extend`, room enough) and `0x8000d064` moves to the next; `0x8000d06c` copies the `Vec`
out, restores and returns.
-/

namespace Rv64Verifier.Proofs.Multilinear.SliceConcat
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.MultilinearContracts Rv64Verifier.Blocks.F54
  Rv64Verifier.Transcript Rv64Verifier.Proofs.Multilinear.Concat
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The stack below the saved registers. -/
@[rv_addr] def W (s : MachineState) (a : Word) : Prop := Within a (stackLo s sliceConcatStack) 184

abbrev Inv (s u : MachineState) (nx : Word) : Prop := FnInv s u 64 Concat.slots Concat.kept (W s) nx

theorem bounds {s : MachineState} (h : SliceConcatPre s) :
    0x780000e0 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (s.getReg .x10).toNat % 8 = 0 ∧
      (s.getReg .x10).toNat + 24 ≤ 0xc0000000 := by
  have := h.stack.bounds (by decide) (by decide)
  have ha := h.stack.above
  have ho := h.out
  simp only [sliceConcatStack, reserveStack, stackLo, heapEnd, Region, Mapped] at this ha ho
  rw [this.2.2.2] at ha
  omega

theorem stack64 {s : MachineState} (h : SliceConcatPre s) : RtStack s 64 := by
  have hb := bounds h
  have hst := h.stack
  have hn := hst.next
  have hro := hst.rodata
  refine ⟨⟨?_, hst.aligned⟩, by addr_omega [hb], by addr_omega [hb, hn], by addr_omega [hb, hro]⟩
  exact ValidMemRange.sub hst.valid (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])

theorem Inv.step {s u v : MachineState} {nx nx' : Word} {X : Word → Prop}
    (hpre : SliceConcatPre s) (h : Inv s u nx) (hX : ByteFrame u v X)
    (hXsub : ∀ a, X a → W s a ∨ Within a nextAddr 8 ∨ (heapNext s ≤ a.toNat ∧ a.toNat < nx'.toNat))
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hr : ∀ r ∈ Reg.x2 :: Concat.kept, v.getReg r = u.getReg r) : Inv s v nx' := by
  have hb := bounds hpre
  exact FnInv.step (m := 40) h (stack64 hpre) (by decide) (by decide) (by decide)
    (fun a ha ha' ↦ by simp only [W] at ha; addr_omega [ha, ha', hb]) hX hXsub hnx hle hend
    (hr _ (by decide)) fun r hr' ↦ hr r (List.mem_cons_of_mem _ hr')

theorem Inv.same {s u v : MachineState} {nx : Word} (hpre : SliceConcatPre s) (h : Inv s u nx)
    (hm : ∀ a, v.getMem a = u.getMem a) {l : List Reg} (hk : ∀ r ∈ l, v.getReg r = u.getReg r)
    (hl : ∀ r ∈ Reg.x2 :: Concat.kept, r ∈ l := by decide) : Inv s v nx :=
  h.step hpre (ByteFrame.of_same hm fun _ ↦ False) (fun _ h ↦ h.elim) ((hm _).trans h.next)
    (Nat.le_refl _) h.fits fun r hr ↦ hk r (hl r hr)

/-! ## The slices -/

/-- The first `i` slices' total length. -/
def lenSum (s : MachineState) (i : Nat) : Nat := ((List.range i).map (partLen s)).sum

theorem lenSum_succ (s : MachineState) (i : Nat) : lenSum s (i + 1) = lenSum s i + partLen s i := by
  simp [lenSum, List.range_succ]

theorem lenSum_mono (s : MachineState) {i j : Nat} (h : i ≤ j) : lenSum s i ≤ lenSum s j := by
  induction j with
  | zero => rw [Nat.le_zero.mp h]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · rw [lenSum_succ]; exact Nat.le_trans (ih (by omega)) (Nat.le_add_right _ _)
    · rw [show i = j + 1 by omega]

theorem flatten_take_succ (s : MachineState) {i : Nat} (hi : i < (s.getReg .x12).toNat) :
    ((parts s).take (i + 1)).flatten =
      ((parts s).take i).flatten ++ eListAt s (partPtr s i) (partLen s i) := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [parts]; exact hi)]
  simp [parts, List.flatten_append]

theorem flatten_length (s : MachineState) (i : Nat) (hi : i ≤ (s.getReg .x12).toNat) :
    ((parts s).take i).flatten.length = lenSum s i := by
  induction i with
  | zero => simp [lenSum]
  | succ i ih => rw [flatten_take_succ s (by omega), List.length_append, ih (by omega),
      eListAt_length, lenSum_succ]

/-- Each slice is under `2^28` elements, and so is their count. -/
theorem part_small {s : MachineState} (h : SliceConcatPre s) {i : Nat}
    (hi : i < (s.getReg .x12).toNat) : partLen s i < 2 ^ 28 := by
  rcases h.part i hi with h0 | h0
  · omega
  · have := h0.1; simp only [Region, Mapped] at this; omega

theorem lenSum_small {s : MachineState} (h : SliceConcatPre s) :
    ∀ i ≤ (s.getReg .x12).toNat, lenSum s i ≤ i * 2 ^ 28
  | 0, _ => by simp [lenSum]
  | i + 1, hi => by
    rw [lenSum_succ, Nat.succ_mul]
    have := lenSum_small h i (by omega)
    have := part_small h (i := i) (by omega)
    omega

theorem count_small {s : MachineState} (h : SliceConcatPre s) : (s.getReg .x12).toNat < 2 ^ 28 := by
  have := h.slices; simp only [Region, Mapped] at this; omega

/-- A slice in place: empty, or mapped, aligned, outside the free heap and apart from the stack. -/
@[rv_addr] def SrcOk (s : MachineState) (P : Word) (L : Nat) : Prop :=
  L = 0 ∨ (Region P (24 * L) ∧ Outside s P (24 * L) ∧
    Apart P (24 * L) (stackLo s sliceConcatStack) sliceConcatStack)

theorem srcOk {s : MachineState} (h : SliceConcatPre s) {i : Nat} (hi : i < (s.getReg .x12).toNat) :
    SrcOk s (partPtr s i) (partLen s i) := by
  rcases h.part i hi with h0 | h0
  · exact Or.inl h0
  · exact Or.inr ⟨h0.1, h0.2.1, h0.2.2.1⟩

/-- `spec_extend`'s precondition in the loop: the `Vec` at `S - 64` (capacity `C`, buffer `Q`,
length `l`), the slice `Ps` of `Ls` elements. -/
theorem extend_pre {s u : MachineState} (hpre : SliceConcatPre s) {C Q Ps : Word} {l Ls : Nat}
    (hsp : u.getReg .x2 = s.getReg .x2 - 64) (hx10 : u.getReg .x10 = s.getReg .x2 - 64)
    (hx11 : u.getReg .x11 = Ps) (hx12 : u.getReg .x12 = Ps + BitVec.ofNat 64 (24 * Ls))
    (hcap : u.getMem (s.getReg .x2 - 64) = C) (hptr : u.getMem (s.getReg .x2 - 56) = Q)
    (hlen : u.getMem (s.getReg .x2 - 48) = BitVec.ofNat 64 l)
    (hroom : l + Ls ≤ C.toNat) (hQa : Q.toNat % 8 = 0)
    (hQ : C.toNat = 0 ∨ heapNext s ≤ Q.toNat ∧ Q.toNat + 24 * C.toNat ≤ heapNext u)
    (hPs : SrcOk s Ps Ls) (hheap : HeapOk u) (hmono : heapNext s ≤ heapNext u) :
    ExtendPre u ∧ extendLen u = Ls ∧ extendDst u = Q + BitVec.ofNat 64 (24 * l) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hro := hst.rodata
  have hfit := hheap.hi
  have hlo := hpre.heap.lo
  simp only [heapNext, heapStart, heapEnd] at hQ hfit hmono hlo
  have hQ' : C.toNat = 0 ∨ heapNext s ≤ Q.toNat ∧ Q.toNat + 24 * C.toNat ≤ heapEnd := by
    simp only [heapNext, heapEnd]; omega
  simp only [SrcOk, Region, Mapped, Outside] at hPs
  have hl : l < 2 ^ 32 := by omega
  have hend : (Ps + BitVec.ofNat 64 (24 * Ls)).toNat = Ps.toNat + 24 * Ls := by
    rcases hPs with h0 | h0
    · subst h0; simp
    · addr_omega [h0.1.1]
  have hel : extendLen u = Ls := by simp only [extendLen, hx11, hx12, hend]; omega
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
    bounds := by rw [hx11, hx12, hend]; omega
    whole := by rw [hx11, hx12, hend]; omega
    src := by
      rw [hel, hx11]
      rcases hPs with h0 | h0
      · exact Or.inl h0
      · exact Or.inr h0.1.1
    srcAlign := by
      rw [hel, hx11]
      rcases hPs with h0 | h0
      · exact Or.inl h0
      · exact Or.inr h0.1.2
    stack := ⟨⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [hsp]; addr_omega [hb]⟩,
      by rw [hsl]; addr_omega [hab, hb], by rw [hsl]; addr_omega [hnx8, hb],
      by rw [hsl]; addr_omega [hro, hb]⟩
    vecStack := by rw [hx10, hsl]; addr_omega [hb]
    vecHeap := by
      rw [hx10]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    srcStack := by
      rw [hel, hx11, hsl]; rcases hPs with h0 | h0 <;> addr_omega [h0, hb]
    srcVec := by rw [hel, hx11, hx10]; rcases hPs with h0 | h0 <;> addr_omega [h0, hb]
    srcDst := by
      rw [hel, hx11, hdst]
      rcases hPs with h0 | h0
      · addr_omega [h0]
      · rcases hQ' with h1 | h1
        · addr_omega [h1, hroom]
        · rcases h0.2.1.1 with h2 | h2 <;> addr_omega [h1, h2, hroom, hfit]
    dstVec := by
      rw [hel, hx10, hdst]
      rcases hQ' with h1 | h1 <;> addr_omega [h1, hroom, hb, hab] }, hel, hdst⟩

/-- A slice in place keeps its elements. -/
theorem Inv.src {s u : MachineState} {nx : Word} (hpre : SliceConcatPre s) (hu : Inv s u nx)
    {P : Word} {L : Nat} (h : SrcOk s P L) : eListAt u P L = eListAt s P L := by
  have hb := bounds hpre
  have hf := hu.fits
  simp only [heapEnd] at hf
  refine (DFrame.of_byteFrame hu.mem).eListAt fun i hi hx ↦ ?_
  simp only [SrcOk, Region, Mapped, Outside] at h
  rcases h with h0 | h0
  · omega
  rcases hx with hx | hx | hx | hx
  · simp only [W] at hx; addr_omega [hx, hi, h0.2.2, hb, h0.1.1]
  · addr_omega [hx, hi, h0.2.2, hb, h0.1.1]
  · addr_omega [hx, hi, h0.2.1.2, h0.1.1]
  · rcases h0.2.1.1 with h1 | h1 <;> addr_omega [hx, hi, h1, hf, h0.1.1]

/-- The slices' descriptors are never written. -/
theorem Inv.slot {s u : MachineState} {nx : Word} (hpre : SliceConcatPre s) (hu : Inv s u nx)
    {i : Nat} (hi : i < (s.getReg .x12).toNat) (c : Nat) (hc : c = 0 ∨ c = 8) :
    u.getMem (s.getReg .x11 + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 c) =
      s.getMem (s.getReg .x11 + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 c) := by
  have hb := bounds hpre
  have hf := hu.fits
  have hss := hpre.slicesStack
  have hsf := hpre.slicesFree
  have hsr := hpre.slices
  simp only [Outside] at hsf
  simp only [Region, Mapped] at hsr
  simp only [heapEnd] at hf
  exact hu.mem.getMem fun j hj hx ↦ by
    rcases hx with hx | hx | hx | hx
    · simp only [W] at hx; addr_omega [hx, hj, hc, hi, hss, hb, hsr]
    · addr_omega [hx, hj, hc, hi, hss, hb, hsr]
    · addr_omega [hx, hj, hc, hi, hsf.2, hsr]
    · rcases hsf.1 with h | h <;> addr_omega [hx, hj, hc, hi, h, hf, hsr]

/-- The end of a slice, `ptr + 24 len` as compiled. -/
theorem end_toNat2 {P L : Word} (h : L.toNat = 0 ∨ P.toNat + 24 * L.toNat ≤ 0xc0000000) :
    P + (L * 16 + L * 8) = P + BitVec.ofNat 64 (24 * L.toNat) := by
  rcases h with h | h
  · have : L = 0 := BitVec.eq_of_toNat_eq (by simpa using h)
    subst this; simp
  · addr_omega [h]

/-! ## The extend loop -/

/-- The `Vec` at `S - 64` after the first `i` slices: capacity `C` (the total), buffer `Q`. -/
structure VecAt (s u : MachineState) (C Q nx : Word) (i : Nat) : Prop where
  inv : Inv s u nx
  x8 : u.getReg .x8 = s.getReg .x10
  cap : u.getMem (s.getReg .x2 - 64) = C
  ptr : u.getMem (s.getReg .x2 - 56) = Q
  len : u.getMem (s.getReg .x2 - 48) = BitVec.ofNat 64 (lenSum s i)
  ctot : C.toNat = lenSum s (s.getReg .x12).toNat
  qa : Q.toNat % 8 = 0
  qr : C.toNat = 0 ∨ heapNext s ≤ Q.toNat ∧ Q.toNat + 24 * C.toNat ≤ nx.toNat
  elems : eListAt u Q (lenSum s i) = ((parts s).take i).flatten

/-- At `0x8000d03c`, the first `i` slices appended. -/
structure ExtInv (s u : MachineState) (C Q nx : Word) (i : Nat) : Prop
    extends VecAt s u C Q nx i where
  pc : u.pc = 0x8000d03c
  lt : i < (s.getReg .x12).toNat
  x9 : u.getReg .x9 = s.getReg .x11 + BitVec.ofNat 64 (16 * i)
  x18 : u.getReg .x18 = s.getReg .x11 + BitVec.ofNat 64 (16 * (s.getReg .x12).toNat)

theorem ext_body (hE : ExtendSpec) {s : MachineState} (hpre : SliceConcatPre s) {C Q nx : Word}
    {i : Nat} {u : MachineState} (hu : ExtInv s u C Q nx i) :
    ∃ v, Reaches Image.code u v ∧ (ExtInv s v C Q nx (i + 1) ∨
      (VecAt s v C Q nx (s.getReg .x12).toNat ∧ v.pc = 0x8000d06c) ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hi := hu.lt
  have hsr := hpre.slices
  simp only [Region, Mapped] at hsr
  have hcs := count_small hpre
  have hsum := lenSum_small hpre _ (Nat.le_refl _)
  have hmono := lenSum_mono s (show i + 1 ≤ (s.getReg .x12).toNat by omega)
  have hpsm := part_small hpre hi
  have hsp := hu.inv.sp
  rv_eval [] at hsp
  have e0 := hu.inv.slot hpre hi 0 (Or.inl rfl)
  have e8 := hu.inv.slot hpre hi 8 (Or.inr rfl)
  simp only [BitVec.add_zero] at e0 e8
  rw [show (BitVec.ofNat 64 8 : Word) = 8 from rfl] at e8
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000d03c_spec hu.pc (by
    rv_eval [hu.x9]
    exact ⟨Region.valid hpre.slices (by addr_omega [hsr, hi]) (by addr_omega [hsr, hi])
      (by addr_omega [hsr, hi]), Region.valid hpre.slices (by addr_omega [hsr, hi])
      (by addr_omega [hsr, hi]) (by addr_omega [hsr, hi])⟩)
  have k₁ := b8000d03c_keeps h₁
  have hm₁ := b8000d03c_mem_same h₁
  have inv₁ := hu.inv.same hpre hm₁ k₁
  have hx11 : u₁.getReg .x11 = partPtr s i := by
    rw [b8000d03c_x11 h₁, hu.x9, e0]; rfl
  have hlw : u.getMem (u.getReg .x9 + 8) = s.getMem (s.getReg .x11 + BitVec.ofNat 64 (16 * i) + 8) := by
    rw [hu.x9, e8]
  have hx12 : u₁.getReg .x12 = partPtr s i + BitVec.ofNat 64 (24 * partLen s i) := by
    rw [b8000d03c_x12 h₁, hlw, hu.x9, e0]
    exact end_toNat2 (by
      rcases srcOk hpre hi with h0 | h0
      · exact Or.inl h0
      · right; have := h0.1; simp only [Region, Mapped, partLen, partPtr] at this ⊢; omega)
  have hsp₁ : u₁.getReg .x2 = s.getReg .x2 - 64 := (k₁ .x2 (by decide)).trans hsp
  have hfit := hu.inv.fits
  have hmono₁ := hu.inv.mono
  have hnx := hu.inv.next
  have hheap₁ : HeapOk u₁ := ⟨by
      have := hpre.heap.lo; simp only [heapNext, heapStart, hm₁, hnx] at this hmono₁ ⊢; omega,
    by simp only [heapNext, hm₁, hnx]; exact hfit⟩
  have hmn : heapNext s ≤ heapNext u₁ := by simp only [heapNext, hm₁, hnx] at hmono₁ ⊢; omega
  obtain ⟨hep, hel, hdst⟩ := extend_pre (u := u₁) hpre hsp₁ (by rw [b8000d03c_x10 h₁, hsp])
    hx11 hx12 (by rw [hm₁, hu.cap]) (by rw [hm₁, hu.ptr]) (by rw [hm₁, hu.len])
    (by rw [hu.ctot, ← lenSum_succ]; exact hmono) hu.qa
    (by simp only [heapNext, hm₁, hnx]; exact hu.qr) (srcOk hpre hi) hheap₁ hmn
  obtain ⟨v, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hdead⟩ := hE.call hr₁ (b8000d03c_pc h₁) hep
  swap
  · exact ⟨v, hr₂, Or.inr (Or.inr hdead)⟩
  have hx10₁ : u₁.getReg .x10 = s.getReg .x2 - 64 := by rw [b8000d03c_x10 h₁, hsp]
  have hfr := hpost₂.frame
  rw [hx10₁, hdst, hel] at hfr
  simp only [stackLo, extendStack, memcpyStack, hsp₁, Sym.sub_sub_lit] at hfr
  have hqr := hu.qr
  have hnext : v.getMem nextAddr = nx := by
    have := hpost₂.next; simp only [heapNext] at this
    exact (BitVec.eq_of_toNat_eq this).trans (inv₁.next)
  have hroom : lenSum s i + partLen s i ≤ C.toNat := by
    rw [hu.ctot, ← lenSum_succ]; exact hmono
  have inv₂ := inv₁.step hpre hfr (fun a ha ↦ by
      rcases ha with ha | ha | ha
      · exact Or.inl (by simp only [W]; addr_omega [ha, hb])
      · right; right
        simp only [heapNext]
        rcases hqr with h0 | h0
        · addr_omega [ha, h0, hroom]
        · addr_omega [ha, h0, hroom]
      · exact Or.inl (by simp only [W]; addr_omega [ha, hb]))
    hnext (Nat.le_refl _) inv₁.fits
    fun r hr ↦ hpres₂ r (by unfold calleeSaved; exact mem_of_mem hr _)
  have hlen₂ := hpost₂.len
  have hcap₂ := hpost₂.cap
  have hptr₂ := hpost₂.ptr
  have hnew₂ := hpost₂.new
  rw [hx10₁] at hlen₂ hcap₂ hptr₂
  rw [hdst, hel, hx11] at hnew₂
  simp only [vecLen, vecCap, vecPtr] at hlen₂ hcap₂ hptr₂
  rv_eval [hm₁, hu.len, hu.cap, hu.ptr] at hlen₂ hcap₂ hptr₂
  -- `0x8000d064`
  obtain ⟨w, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000d064_spec
    (by rw [hpc₂, returnAddress_eq, b8000d03c_x1 h₁]; decide) (by rv_eval [])
  have k₃ := b8000d064_keeps h₃
  have hm₃ := b8000d064_mem_same h₃
  have inv₃ := inv₂.same hpre hm₃ k₃
  have hx19 : v.getReg .x19 = s.getReg .x11 + BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [hpres₂.reg .x19, b8000d03c_x19 h₁, hu.x9]; addr_omega [hsr, hi]
  have hx18 : v.getReg .x18 = s.getReg .x11 + BitVec.ofNat 64 (16 * (s.getReg .x12).toNat) := by
    rw [hpres₂.reg .x18, k₁ .x18 (by decide), hu.x18]
  have hlenv : (lenSum s (i + 1)) < 2 ^ 64 := by omega
  have hel₂ : eListAt w Q (lenSum s (i + 1)) = ((parts s).take (i + 1)).flatten := by
    rw [eListAt_same hm₃, lenSum_succ, eListAt_add, hnew₂, inv₁.src hpre (srcOk hpre hi),
      flatten_take_succ s hi, ← hu.elems, ← eListAt_same hm₁]
    congr 1
    refine (DFrame.of_byteFrame hfr).eListAt fun j hj hx ↦ ?_
    rcases hqr with h0 | h0
    · omega
    · rcases hx with hx | hx | hx <;> addr_omega [hx, hj, h0, hroom, hfit, hb, hab]
  have hvec : VecAt s w C Q nx (i + 1) := {
    inv := inv₃
    x8 := by rw [k₃ .x8 (by decide), hpres₂.reg .x8, k₁ .x8 (by decide), hu.x8]
    cap := by rw [hm₃, hcap₂]
    ptr := by rw [hm₃, hptr₂]
    len := by
      rw [hm₃]; apply BitVec.eq_of_toNat_eq
      rw [hlen₂, BitVec.toNat_ofNat, BitVec.toNat_ofNat, lenSum_succ]; omega
    ctot := hu.ctot
    qa := hu.qa
    qr := hu.qr
    elems := hel₂ }
  by_cases hlast : i + 1 = (s.getReg .x12).toNat
  · refine ⟨w, hr₂.trans hr₃, Or.inr (Or.inl ⟨by rw [← hlast]; exact hvec, ?_⟩)⟩
    exact b8000d064_pc_not_taken h₃ (by rw [hx19, hx18, hlast])
  · refine ⟨w, hr₂.trans hr₃, Or.inl {
      toVecAt := hvec
      pc := b8000d064_pc_taken h₃ (by rw [hx19, hx18]; addr_omega [hsr, hlast, hi])
      lt := by omega
      x9 := by rw [b8000d064_x9 h₃, hx19]
      x18 := by rw [k₃ .x18 (by decide), hx18] }⟩

/-! ## The epilogue, the prologue, the contract -/

/-- The epilogue: the `Vec` (capacity `C`, buffer `Q`) copied out, the registers restored. -/
theorem exit {s u : MachineState} {nx C Q : Word} (hpre : SliceConcatPre s) (hu : Inv s u nx)
    (hpc : u.pc = 0x8000d06c) (hsp₇ : u.getReg .x2 = s.getReg .x2 - 64)
    (hx8₇ : u.getReg .x8 = s.getReg .x10) (hcap₇ : u.getMem (s.getReg .x2 - 64) = C)
    (hptr₇ : u.getMem (s.getReg .x2 - 56) = Q) (hlen₇ : (u.getMem (s.getReg .x2 - 48)).toNat = C.toNat)
    (hel : eListAt u Q C.toNat = (parts s).flatten)
    (hQa : Q.toNat % 8 = 0)
    (hQr : C.toNat = 0 ∨ heapNext s ≤ Q.toNat ∧ Q.toNat + 24 * C.toNat ≤ nx.toNat) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧ SliceConcatPost s t := by
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
  obtain ⟨t, hr₈, h₈⟩ := Sym.BlockSpec.reaches b8000d06c_spec hpc (by
      rv_eval [hsp₇, hx8₇]
      and_intros <;> first
        | valid_access hst.valid [hb]
        | exact Region.valid hpre.out (by addr_omega [hro']) (by addr_omega [hro'])
            (by addr_omega [hro'])
        | addr_omega [hos, hb, hro'])
  have k₈ := b8000d06c_keeps h₈
  have hm₈ := b8000d06c_frame h₈ (by rw [hx8₇]; addr_omega [hro'])
  rw [hx8₇] at hm₈
  have hsl := hu.slots
  simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true] at hsl
  rv_eval [] at hsl
  obtain ⟨sl1, sl2, sl3, sl4, sl5⟩ := hsl
  have pc := b8000d06c_pc h₈
  have x2 := b8000d06c_x2 h₈
  have x8 := b8000d06c_x8 h₈
  have x9 := b8000d06c_x9 h₈
  have x18 := b8000d06c_x18 h₈
  have x19 := b8000d06c_x19 h₈
  have o0 := b8000d06c_m_x8_0 h₈
  have o8 := b8000d06c_m_x8_8 h₈
  have o16 := b8000d06c_m_x8_16 h₈
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

/-- The lengths' sum, at `0x8000cff4`. -/
structure SumInv (s t₁ u : MachineState) (i : Nat) : Prop where
  pc : u.pc = 0x8000cff4
  lt : i < (s.getReg .x12).toNat
  mem : ∀ a, u.getMem a = t₁.getMem a
  keep : ∀ r ∈ [Reg.x1, .x2, .x8, .x9, .x12, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25,
    .x26, .x27], u.getReg r = t₁.getReg r
  x10 : u.getReg .x10 = s.getReg .x11 + BitVec.ofNat 64 (16 * i + 8)
  x11 : u.getReg .x11 = BitVec.ofNat 64 (lenSum s i)

theorem sum_loop {s t₁ : MachineState} (hpre : SliceConcatPre s)
    (hmem : ∀ a, ¬ Within a (s.getReg .x2 - 40) 40 → t₁.getMem a = s.getMem a)
    (hx12 : t₁.getReg .x12 = s.getReg .x11 + 8 + s.getReg .x12 * 16) (h₀ : SumInv s t₁ t₁ 0) :
    ∃ v, Reaches Image.code t₁ v ∧ v.pc = 0x8000d004 ∧ (∀ a, v.getMem a = t₁.getMem a) ∧
      (∀ r ∈ [Reg.x1, .x2, .x8, .x9, .x12, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25,
        .x26, .x27], v.getReg r = t₁.getReg r) ∧
      v.getReg .x11 = BitVec.ofNat 64 (lenSum s (s.getReg .x12).toNat) := by
  have hb := bounds hpre
  have hsr := hpre.slices
  have hss := hpre.slicesStack
  simp only [Region, Mapped] at hsr
  have hcs := count_small hpre
  have hsum := lenSum_small hpre _ (Nat.le_refl _)
  refine Reaches.loop (code := Image.code) (fun u ↦ ∃ i, SumInv s t₁ u i)
    (fun u ↦ (s.getReg .x11).toNat + 16 * (s.getReg .x12).toNat + 8 - (u.getReg .x10).toNat) _
    (fun u ⟨i, hu⟩ ↦ ?_) t₁ ⟨0, h₀⟩
  have hi := hu.lt
  have hmono := lenSum_mono s (show i + 1 ≤ (s.getReg .x12).toNat by omega)
  have hps := part_small hpre hi
  obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b8000cff4_spec hu.pc (by
    rv_eval [hu.x10]
    exact Region.valid hpre.slices (by addr_omega [hsr, hi]) (by addr_omega [hsr, hi])
      (by addr_omega [hsr, hi]))
  have k := b8000cff4_keeps h
  have hm := b8000cff4_mem_same h
  have hrd : u.getMem (u.getReg .x10) = s.getMem (s.getReg .x11 + BitVec.ofNat 64 (16 * i) + 8) := by
    rw [hu.mem, hu.x10, hmem _ (by addr_omega [hsr, hi, hss, hb])]
    congr 1; addr_omega [hsr, hi]
  have hx11 : v.getReg .x11 = BitVec.ofNat 64 (lenSum s (i + 1)) := by
    rw [b8000cff4_x11 h, hrd, hu.x11, lenSum_succ]
    apply BitVec.eq_of_toNat_eq
    simp only [partLen] at hps ⊢
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have hx10 : v.getReg .x10 = s.getReg .x11 + BitVec.ofNat 64 (16 * (i + 1) + 8) := by
    rw [b8000cff4_x10 h, hu.x10]; addr_omega [hsr, hi]
  have hkeep (r : Reg) (hr' : r ∈ [Reg.x1, .x2, .x8, .x9, .x12, .x18, .x19, .x20, .x21, .x22, .x23,
      .x24, .x25, .x26, .x27]) : v.getReg r = t₁.getReg r :=
    (k r (mem_of_mem hr' _)).trans (hu.keep r hr')
  have hx12' : u.getReg .x12 = s.getReg .x11 + 8 + s.getReg .x12 * 16 :=
    (hu.keep .x12 (by decide)).trans hx12
  by_cases hlast : i + 1 = (s.getReg .x12).toNat
  · refine Or.inl ⟨v, hr, b8000cff4_pc_not_taken h (by rw [hu.x10, hx12']; addr_omega [hsr, hlast]),
      fun a ↦ (hm a).trans (hu.mem a), hkeep, by rw [hx11, hlast]⟩
  · refine Or.inr ⟨v, hr, ⟨i + 1, b8000cff4_pc_taken h (by rw [hu.x10, hx12']; addr_omega [hsr, hlast, hi]),
      by omega, fun a ↦ (hm a).trans (hu.mem a), hkeep, hx10, hx11⟩, ?_⟩
    rw [hx10, hu.x10]; addr_omega [hsr, hi, hlast]

theorem prologue (hT : TryAllocZeroedSpec) {s : MachineState} (hpc : s.pc = 0x8000cfc4)
    (hpre : SliceConcatPre s) :
    ∃ u, Reaches Image.code s u ∧ ((∃ C Q nx, ExtInv s u C Q nx 0) ∨ Dead Image.code u) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hro := hst.rodata
  have hheap := hpre.heap
  have hlo := hheap.lo
  have hsr := hpre.slices
  simp only [Region, Mapped] at hsr
  have hcs := count_small hpre
  have hsum := lenSum_small hpre _ (Nat.le_refl _)
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000cfc4_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000cfc4_keeps h₁
  have hm₁ := b8000cfc4_frame h₁ (by addr_omega [hb])
  have inv₁ : Inv s t₁ (s.getMem nextAddr) := FnInv.init hheap (stack64 hpre)
    (by rw [b8000cfc4_x2 h₁]; rfl)
    (by
      simp only [Concat.slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      rv_eval []
      exact ⟨b8000cfc4_m_x2_n8 h₁, b8000cfc4_m_x2_n16 h₁, b8000cfc4_m_x2_n24 h₁,
        b8000cfc4_m_x2_n32 h₁, b8000cfc4_m_x2_n40 h₁⟩)
    (fun r hr ↦ k₁ r (mem_of_mem hr _))
    (hm₁.mono fun a ha ↦ by addr_omega [ha, hb])
    (h₁.unaligned (by rv_eval []; and_intros <;> addr_omega [hb])) (by decide)
  obtain ⟨t₂, hr₂, hpc₂, hm₂, hk₂, hx11₂⟩ := sum_loop hpre hm₁ (b8000cfc4_x12 h₁)
    ⟨b8000cfc4_pc h₁, hpre.count, fun _ ↦ rfl, fun _ _ ↦ rfl,
      by rw [b8000cfc4_x10 h₁]; rfl, by rw [b8000cfc4_x11 h₁]; simp [lenSum]⟩
  have inv₂ := inv₁.same hpre hm₂ hk₂
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000d004_spec hpc₂ (by rv_eval [])
  have k₃ := b8000d004_keeps h₃
  have inv₃ := inv₂.same hpre (b8000d004_mem_same h₃) k₃
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - 64 := by
    rw [hk₂ .x2 (by decide), b8000cfc4_x2 h₁]
  have hsp₃ : t₃.getReg .x2 = s.getReg .x2 - 64 := (k₃ .x2 (by decide)).trans hsp₂
  have hx10₃ : t₃.getReg .x10 = s.getReg .x2 - 64 := (b8000d004_x10 h₃).trans hsp₂
  have hx11₃ : t₃.getReg .x11 = BitVec.ofNat 64 (lenSum s (s.getReg .x12).toNat) :=
    (k₃ .x11 (by decide)).trans hx11₂
  have hn₃ : heapNext t₃ = heapNext s := by simp only [heapNext, inv₃.next]
  have hsl : stackLo t₃ tryAllocStack = s.getReg .x2 - 112 := by
    simp only [stackLo, tryAllocStack, hsp₃, Sym.sub_sub_lit]; rfl
  have hpre₃ : TryAllocPre .x13 .x14 t₃ := {
    heap := ⟨hn₃ ▸ hheap.lo, hn₃ ▸ hheap.hi⟩
    out := by rw [hx10₃]; valid_sub hst.valid [hb]
    align := by rw [b8000d004_x13 h₃]; decide
    size := by rw [b8000d004_x14 h₃]; decide
    stack := ⟨⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [hsp₃]; addr_omega [hb]⟩,
      by rw [hsl]; addr_omega [hab, hb], by rw [hsl]; addr_omega [hnx8, hb],
      by rw [hsl]; addr_omega [hro, hb]⟩
    outFree := by
      rw [hx10₃]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    outStack := by rw [hx10₃, hsl]; addr_omega [hb] }
  obtain ⟨t₄, hr₄, ⟨hpc₄, hpres₄, hpost₄, -⟩ | hdead⟩ := hT.call (hr₂.trans hr₃) (b8000d004_pc h₃) hpre₃
  swap
  · exact ⟨t₄, hr₁.trans hr₄, Or.inr hdead⟩
  have hfr₄ := hpost₄.frame
  rw [hx10₃, hsl] at hfr₄
  have inv₄ : Inv s t₄ (t₄.getMem nextAddr) := inv₃.step hpre hfr₄ (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (by simp only [W]; addr_omega [ha, hb])
      · exact Or.inl (by simp only [W]; addr_omega [ha, hb])
      · exact Or.inr (Or.inl ha)
      · simp only [Fresh, hn₃] at ha
        exact Or.inr (Or.inr ha))
    rfl (by rw [← heapNext, ← heapNext, ← hn₃]; exact hpost₄.mono) hpost₄.heap.hi
    fun r hr ↦ hpres₄ r (by unfold calleeSaved; exact mem_of_mem hr _)
  have hsp₄ : t₄.getReg .x2 = s.getReg .x2 - 64 := (hpres₄.reg .x2).trans hsp₃
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000d01c_spec
    (by rw [hpc₄, returnAddress_eq, b8000d004_x1 h₃]; decide) (by
      rv_eval [hsp₄]
      valid_access hst.valid [hb])
  rcases eq_or_ne (t₄.getMem (s.getReg .x2 - 64)) 0 with htag | htag
  swap
  · refine ⟨t₅, hr₁.trans (hr₄.trans hr₅), Or.inr (dead_of_fetch ?_)⟩
    rw [b8000d01c_pc_taken h₅ (by rw [hsp₄]; exact htag)]
    exact Option.isNone_iff_eq_none.mp (by decide +kernel)
  have k₅ := b8000d01c_keeps h₅
  have hm₅ := b8000d01c_mem_same h₅
  have inv₅ := inv₄.same hpre hm₅ k₅
  obtain ⟨hcap, hbuf⟩ := hpost₄.ok (by rw [hx10₃]; exact htag)
  rw [hx10₃] at hcap hbuf
  rw [b8000d004_x14 h₃, b8000d004_x13 h₃, hx11₃] at hbuf
  rv_eval [] at hcap hbuf
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = t₄.getMem (s.getReg .x2 - 48) := ⟨_, rfl⟩
  rw [← hQ] at hbuf
  simp only [NewBuf, heapNext] at hbuf
  have hLt : (BitVec.ofNat 64 (lenSum s (s.getReg .x12).toNat)).toNat =
      lenSum s (s.getReg .x12).toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [hLt] at hbuf
  have hn₃' : (t₃.getMem nextAddr).toNat = (s.getMem nextAddr).toNat := hn₃
  have hsp₅ : t₅.getReg .x2 = s.getReg .x2 - 64 := (k₅ .x2 (by decide)).trans hsp₄
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000d024_spec
    (b8000d01c_pc_not_taken h₅ (by rw [hsp₄]; exact htag)) (by
      rv_eval [hsp₅]
      and_intros <;> valid_access hst.valid [hb])
  have k₆ := b8000d024_keeps h₆
  have hm₆ := b8000d024_frame h₆ (by rw [hsp₅]; addr_omega [hb])
  rw [hsp₅] at hm₆
  have inv₆ := inv₅.step hpre (ByteFrame.of_memFrame hm₆ (by addr_omega [hb]) (by decide)
      (h₆.unaligned (by rv_eval [hsp₅]; and_intros <;> addr_omega [hb])))
    (fun a ha ↦ Or.inl (by simp only [W]; addr_omega [ha, hb]))
    ((hm₆ _ (by addr_omega [hb, hnx8])).trans inv₅.next)
    (Nat.le_refl _) inv₅.fits fun r hr ↦ k₆ r (mem_of_mem hr _)
  have c0 := b8000d024_m_x2_0 h₆
  have c8 := b8000d024_m_x2_8 h₆
  have c16 := b8000d024_m_x2_16 h₆
  rw [hsp₅] at c0 c8 c16
  rv_eval [hm₅] at c0 c8 c16
  rw [hcap] at c0
  rw [← hQ] at c8
  have hreg (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18]) : t₅.getReg r = t₁.getReg r := by
    rw [k₅ r (mem_of_mem hr _), hpres₄ r (by unfold calleeSaved; exact mem_of_mem hr _),
      k₃ r (mem_of_mem hr _), hk₂ r (mem_of_mem hr _)]
  have hfit₄ := hpost₄.heap.hi
  have hmono₄ := hpost₄.mono
  simp only [heapNext, heapEnd] at hfit₄ hmono₄
  refine ⟨t₆, hr₁.trans (hr₄.trans (hr₅.trans hr₆)), Or.inl ⟨_, Q, _, {
    inv := inv₆
    x8 := by rw [k₆ .x8 (by decide), hreg .x8 (by decide), b8000cfc4_x8 h₁]
    cap := c0
    ptr := c8
    len := by rw [c16]; simp [lenSum]
    ctot := by
      rw [hx11₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    qa := hbuf.1
    qr := by
      rw [hx11₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [heapNext]
      rcases hbuf.2 with h0 | h0
      · left; omega
      · right; omega
    elems := by simp [lenSum, eListAt]
    pc := b8000d024_pc h₆
    lt := hpre.count
    x9 := by rw [k₆ .x9 (by decide), hreg .x9 (by decide), b8000cfc4_x9 h₁]; simp
    x18 := by
      rw [b8000d024_x18 h₆, hreg .x9 (by decide), hreg .x18 (by decide), b8000cfc4_x9 h₁,
        b8000cfc4_x18 h₁]
      addr_omega [hsr] }⟩⟩

/-- **The slice `concat` meets its contract**, given `try_allocate_in`'s and `spec_extend`'s. -/
theorem slice_concat_spec (hT : TryAllocZeroedSpec) (hE : ExtendSpec) : SliceConcatSpec := by
  intro s hpc hpre
  have hsr := hpre.slices
  simp only [Region, Mapped] at hsr
  obtain ⟨u, hr, ⟨C, Q, nx, hu⟩ | hd⟩ := prologue hT hpc hpre
  swap
  · exact ⟨u, hr, Or.inr hd⟩
  obtain ⟨v, hr', hv⟩ := Reaches.loop (code := Image.code) (fun v ↦ ∃ i, ExtInv s v C Q nx i)
    (fun v ↦ (s.getReg .x11).toNat + 16 * (s.getReg .x12).toNat - (v.getReg .x9).toNat)
    (fun v ↦ (VecAt s v C Q nx (s.getReg .x12).toNat ∧ v.pc = 0x8000d06c) ∨ Dead Image.code v)
    (fun v ⟨i, hv⟩ ↦ by
      obtain ⟨w, hw, h | h | h⟩ := ext_body hE hpre hv
      · refine Or.inr ⟨w, hw, ⟨i + 1, h⟩, ?_⟩
        have := hv.lt
        rw [h.x9, hv.x9]
        addr_omega [hsr, this, h.lt]
      · exact Or.inl ⟨w, hw, Or.inl h⟩
      · exact Or.inl ⟨w, hw, Or.inr h⟩) u ⟨0, hu⟩
  rcases hv with ⟨hv, hpc'⟩ | hd
  · have hel := hv.elems
    rw [← hv.ctot, List.take_of_length_le (by simp [parts])] at hel
    obtain ⟨t, hr'', hpc'', hpres, hpost⟩ := exit hpre hv.inv hpc' (by
        rw [hv.inv.sp]; rfl) hv.x8 hv.cap hv.ptr
      (by rw [hv.len, hv.ctot, BitVec.toNat_ofNat]; have := lenSum_small hpre _ (Nat.le_refl _);
          have := count_small hpre; omega) hel hv.qa hv.qr
    exact ⟨t, hr.trans (hr'.trans hr''), Or.inl ⟨hpc'', hpres, hpost⟩⟩
  · exact ⟨v, hr.trans hr', Or.inr hd⟩

end Rv64Verifier.Proofs.Multilinear.SliceConcat
