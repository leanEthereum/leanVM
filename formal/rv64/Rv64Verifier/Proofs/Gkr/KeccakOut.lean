import Rv64Verifier.Proofs.Gkr.KeccakOpen

/-!
# `keccak::verify_keccak`: the committed outputs' opening

`open(first, 1, 1, &committed)` at `0x80009254`, its row copied to `f + 3584` and its value kept
at `f + 3512` (`to_row`); `next_scalar()`, the word (`to_word`).
-/

namespace Rv64Verifier.Gkr.Keccak
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F35 Rv64Verifier.MultilinearContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- After the committed outputs' opening. -/
def kAfter (l : Nat) (inst : List E) (cl : KeccakClaim) (r : List E × List E × E) :
    TM KeccakOpenings :=
  TM.nextScalar >>= fun word ↦ TM.require (r.2.1.getD 0 0 * word = r.2.2) >>= fun _ ↦
    kInputs l cl (some (inst ++ r.1, word))

theorem kTail_eq (l : Nat) (inst : List E) (first : KeccakClaim) (c : E) (cl : KeccakClaim) :
    kTail l inst first c cl = (openRust ⟨l, 12⟩ first 1 1 c >>= kAfter l inst cl) := by
  unfold kTail
  congr 1

/-- A buffer allocated since the entry, kept by a step. -/
theorem buf_step {s u v : MachineState} (hpre : VerifyKeccakPreW s) (B : Base s u) {rs : List (Nat × Nat)}
    {sp : Bool} (hok : SlotsOk rs = true) (F : DFrame u v (SW s u v rs sp))
    (hN : heapNext u ≤ heapNext v) {p : Word} {n : Nat} {xs : List E}
    (h : NewBuf s u p (24 * n) 8 ∧ eListAt u p n = xs) : NewBuf s v p (24 * n) 8 ∧ eListAt v p n = xs := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simp only [NewBuf] at h1 ⊢; omega, ?_⟩
  rw [← h2]
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0; rfl
  · have hi := B.heap.hi
    simp only [NewBuf] at h1
    exact F.eListAt ((SW.buf hpre B hok h1).bytes (le_refl _) (le_refl _) (by unfold heapEnd at hi; omega))

/-- The last claim at `f + 296`, the spills, the outputs' slot `sp`/`sl` (its elements `slot`). -/
structure P2 (s u : MachineState) (cl : KeccakClaim) (mp ml sp sl : Word) (slot : List E) : Prop where
  base : Base s u
  ok : OK s
  m32 : u.getMem (s.getReg .x2 - 5216) = s.getReg .x12 - 4
  m48 : u.getMem (s.getReg .x2 - 5200) = s.getReg .x10
  m56 : u.getMem (s.getReg .x2 - 5192) = s.getReg .x14
  m64 : u.getMem (s.getReg .x2 - 5184) = 2
  claim : ClaimOut s u (s.getReg .x2 - 4952) cl
  lens : Lens cl
  mptr : u.getMem (s.getReg .x2 - 4944) = mp
  mlen : u.getMem (s.getReg .x2 - 4936) = ml
  sbuf : NewBuf s u sp (24 * sl.toNat) 8 ∧ eListAt u sp sl.toNat = slot
  sreg : sl.toNat = 0 ∨ (Region sp (24 * sl.toNat) ∧
    ∀ lo m, heapEnd ≤ lo.toNat → Apart sp (24 * sl.toNat) lo m)
  x9 : u.getReg .x9 = s.getReg .x11
  x18 : u.getReg .x18 = s.getReg .x12
  x19 : u.getReg .x19 = 12
  x22 : u.getReg .x22 = mp
  x23 : u.getReg .x23 = ml

theorem P2.step {s u v : MachineState} {cl : KeccakClaim} {mp ml sp sl : Word} {slot : List E}
    (hpre : VerifyKeccakPreW s) (P : P2 s u cl mp ml sp sl slot)
    (hx2 : v.getReg .x2 = s.getReg .x2 - 5248) (hH : HeapOk v) (hN : heapNext u ≤ heapNext v)
    {rs : List (Nat × Nat)} {spb : Bool} (hok : SlotsOk rs = true)
    (h1 : SlotsSep rs 5216 8 = true) (h2 : SlotsSep rs 5200 24 = true)
    (h3 : SlotsSep rs 4952 96 = true) (F : DFrame u v (SW s u v rs spb))
    (hregs : ∀ r ∈ ([.x9, .x18, .x19, .x22, .x23] : List Reg), v.getReg r = u.getReg r) :
    P2 s v cl mp ml sp sl slot :=
  { base := P.base.step hpre hx2 hH hN hok F
    ok := P.ok
    m32 := (SW.mem hpre hH hok (J := 5216) (by decide) (by decide) h1 F).trans P.m32
    m48 := (SW.mem hpre hH hok (J := 5200) (by decide) (by decide)
      (SlotsSep.sub h2 (le_refl _) (by omega)) F).trans P.m48
    m56 := (SW.mem hpre hH hok (J := 5192) (by decide) (by decide)
      (SlotsSep.sub h2 (by omega) (by omega)) F).trans P.m56
    m64 := (SW.mem hpre hH hok (J := 5184) (by decide) (by decide)
      (SlotsSep.sub h2 (by omega) (by omega)) F).trans P.m64
    claim := ClaimOut.step hpre P.base hH hN hok (J := 4952) (by decide) (by decide) h3 F P.claim
    lens := P.lens
    mptr := (SW.mem hpre hH hok (J := 4944) (by decide) (by decide)
      (SlotsSep.sub h3 (by omega) (by omega)) F).trans P.mptr
    mlen := (SW.mem hpre hH hok (J := 4936) (by decide) (by decide)
      (SlotsSep.sub h3 (by omega) (by omega)) F).trans P.mlen
    sbuf := buf_step hpre P.base hok F hN P.sbuf
    sreg := P.sreg
    x9 := (hregs .x9 (by decide)).trans P.x9
    x18 := (hregs .x18 (by decide)).trans P.x18
    x19 := (hregs .x19 (by decide)).trans P.x19
    x22 := (hregs .x22 (by decide)).trans P.x22
    x23 := (hregs .x23 (by decide)).trans P.x23 }

theorem P2.same {s u v : MachineState} {cl : KeccakClaim} {mp ml sp sl : Word} {slot : List E}
    (hpre : VerifyKeccakPreW s) (P : P2 s u cl mp ml sp sl slot)
    (hx2 : v.getReg .x2 = s.getReg .x2 - 5248) (hm : ∀ a, v.getMem a = u.getMem a)
    (hregs : ∀ r ∈ ([.x9, .x18, .x19, .x22, .x23] : List Reg), v.getReg r = u.getReg r) :
    P2 s v cl mp ml sp sl slot := by
  have hN : heapNext v = heapNext u := by simp only [heapNext, hm]
  exact P.step hpre hx2 ⟨by rw [hN]; exact P.base.heap.lo, by rw [hN]; exact P.base.heap.hi⟩
    (le_of_eq hN.symm) (rs := []) (spb := false) (by decide) (by decide) (by decide) (by decide)
    (DFrame.of_same hm _) hregs

theorem P2.block {s u v : MachineState} {cl : KeccakClaim} {mp ml sp sl : Word} {slot : List E}
    (hpre : VerifyKeccakPreW s) (P : P2 s u cl mp ml sp sl slot)
    (hx2 : v.getReg .x2 = s.getReg .x2 - 5248) {rs : List (Nat × Nat)} (hok : SlotsOk rs = true)
    (h1 : SlotsSep rs 5216 8 = true) (h2 : SlotsSep rs 5200 24 = true)
    (h3 : SlotsSep rs 4952 96 = true) (F : DFrame u v (Slots s rs))
    (hregs : ∀ r ∈ ([.x9, .x18, .x19, .x22, .x23] : List Reg), v.getReg r = u.getReg r) :
    P2 s v cl mp ml sp sl slot := by
  have hN := slots_next hpre hok F
  exact P.step hpre hx2
    ⟨by simp only [heapNext, hN]; exact P.base.heap.lo, by simp only [heapNext, hN]; exact P.base.heap.hi⟩
    (by simp only [heapNext, hN]; exact le_refl _) hok h1 h2 h3 (slots_sw F) hregs

/-- At `0x800092a4`: the row at `f + 3584`, the value at `f + 3512`. -/
structure Q1 (s u : MachineState) (cl : KeccakClaim) (mp ml sp sl : Word) (slot row : List E)
    (v : E) : Prop extends P2 s u cl mp ml sp sl slot where
  pc : u.pc = 0x800092a4
  x20 : u.getReg .x20 = sl
  x24 : u.getReg .x24 = sp
  row' : eListAt u (s.getReg .x2 - 1664) 64 = row
  value : eAt u (s.getReg .x2 - 1736) = v
  rest : Rest s u (kAfter (s.getReg .x12).toNat (instOf s) cl (slot, row, v))

theorem to_row (hO : OpenSpec) (hMC : Runtime.MemcpySpec 0x800126e4) {s u : MachineState}
    {first cl : KeccakClaim} {c : E} (hpre : VerifyKeccakPreW s) (A : A12 s u first c cl) :
    ∃ t, Reaches Image.code u t ∧ ((∃ sp sl slot row v, Q1 s t cl (vecPtr u (s.getReg .x2 - 4952))
      (vecLen u (s.getReg .x2 - 4952)) sp sl slot row v) ∨ Done s t) := by
  have hb := bounds hpre
  have B := A.base
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80009254_spec A.pc trivial
  have k₁ := b80009254_keeps h₁
  have m₁ := b80009254_mem_same h₁
  have x2₁ : u₁.getReg .x2 = s.getReg .x2 - 5248 := (k₁ .x2 (by decide)).trans B.x2
  have K₁ := A.toK.same hpre x2₁ m₁
  have R₁ : Rest s u₁ (openRust ⟨(s.getReg .x12).toNat, 12⟩ first 1 1
      (eAt u₁ (s.getReg .x2 - BitVec.ofNat 64 5072)) >>= kAfter (s.getReg .x12).toNat (instOf s) cl) :=
    (A.rest.keep fun T hT ↦ Layer.transcriptAt_congr m₁ hT).congr (by
      rw [kTail_eq, show eAt u₁ (s.getReg .x2 - BitVec.ofNat 64 5072) = c from K₁.committed])
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 3296 := by rw [b80009254_x10 h₁, B.x2]; rv_eval []
  have x11₁ : u₁.getReg .x11 = s.getReg .x11 := by rw [b80009254_x11 h₁, A.x9]
  have x12₁ : u₁.getReg .x12 = s.getReg .x12 := by rw [b80009254_x12 h₁, A.x18]
  have x13₁ : u₁.getReg .x13 = 12 := by rw [k₁ .x13 (by decide), A.x13]
  have x14₁ : u₁.getReg .x14 = s.getReg .x2 - BitVec.ofNat 64 5048 := by
    rw [b80009254_x14 h₁, B.x2]; exact BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have x16₁ : u₁.getReg .x16 = BitVec.ofNat 64 1 := by rw [b80009254_x16 h₁, A.x24]; rfl
  have x17₁ : u₁.getReg .x17 = s.getReg .x2 - BitVec.ofNat 64 5072 := by
    rw [b80009254_x17 h₁, B.x2]; exact BitVec.eq_of_toNat_eq (by addr_omega [hb])
  obtain ⟨t, hr₂, hd | ⟨hpc₂, hpres₂, B₂, hN₂, F₂, hres⟩⟩ := open_call hO hpre K₁.base
    (b80009254_pc h₁) (J := 5048) (V := 5072) (F := 1) (C := 1) (Or.inl ⟨rfl, rfl⟩) K₁.firstV
    K₁.firstLens x10₁ x11₁ x12₁ x13₁ x14₁ (b80009254_x15 h₁) x16₁ (by decide) x17₁ R₁
  · exact ⟨t, hr₁.trans hr₂, Or.inr (Or.inr hd)⟩
  have x2t : t.getReg .x2 = s.getReg .x2 - 5248 := (hpres₂.reg .x2).trans x2₁
  have hb4944 : s.getReg .x2 - 4952 + 8 = s.getReg .x2 - 4944 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have hb4936 : s.getReg .x2 - 4952 + 16 = s.getReg .x2 - 4936 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  -- what is kept from the loop, through the call
  have Pt : P2 s t cl (vecPtr u (s.getReg .x2 - 4952)) (vecLen u (s.getReg .x2 - 4952))
      0 0 [] := by
    have hregs : ∀ r ∈ ([.x9, .x18, .x19, .x22, .x23] : List Reg),
        t.getReg r = u₁.getReg r := fun r hr ↦ hpres₂.reg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
    exact P2.step (u := u₁) hpre {
      base := K₁.base, ok := K₁.ok, m32 := K₁.m32, m48 := K₁.m48, m56 := K₁.m56, m64 := K₁.m64
      claim := Layer.claimOut_congr m₁ A.claim
      lens := A.lens
      mptr := by rw [m₁, ← hb4944]; rfl
      mlen := by rw [m₁, ← hb4936]; rfl
      sbuf := ⟨by simp only [NewBuf]; simp, rfl⟩
      sreg := Or.inl rfl
      x9 := by rw [k₁ .x9 (by decide), A.x9]
      x18 := by rw [k₁ .x18 (by decide), A.x18]
      x19 := by rw [k₁ .x19 (by decide), A.x19]
      x22 := by rw [k₁ .x22 (by decide), A.x22]
      x23 := by rw [k₁ .x23 (by decide), A.x23] } x2t B₂.heap hN₂ (by decide) (by decide)
      (by decide) (by decide) F₂ hregs
  have pct : t.pc = 0x80009278 := by rw [hpc₂, returnAddress_eq, b80009254_x1 h₁]; decide
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80009278_spec pct (by
    rv_eval [x2t]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₃ := b80009278_keeps h₃
  have m₃ := b80009278_mem_same h₃
  have x2₃ : u₃.getReg .x2 = s.getReg .x2 - 5248 := (k₃ .x2 (by decide)).trans x2t
  have reg₃ : ∀ r ∈ ([.x9, .x18, .x19, .x22, .x23] : List Reg), u₃.getReg r = t.getReg r :=
    fun r hr ↦ k₃ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  have P₃ := Pt.same hpre x2₃ m₃ reg₃
  have tag (n : Nat) (hn : n ≤ 5248) : t.getMem (t.getReg .x2 + BitVec.ofNat 64 n) =
      t.getMem (s.getReg .x2 - BitVec.ofNat 64 (5248 - n)) := by
    rw [x2t]; exact congrArg _ (BitVec.eq_of_toNat_eq (by addr_omega [hb, hn]))
  have t1952 : t.getMem (t.getReg .x2 + 1952) = t.getMem (s.getReg .x2 - 3296) := tag 1952 (by decide)
  have t1960 : t.getMem (t.getReg .x2 + 1960) = t.getMem (s.getReg .x2 - 3288) := tag 1960 (by decide)
  have t1968 : t.getMem (t.getReg .x2 + 1968) = t.getMem (s.getReg .x2 - 3280) := tag 1968 (by decide)
  have ho := hpre.out
  have m48' : u₃.getMem (s.getReg .x2 - 5200) = s.getReg .x10 := P₃.m48
  have m48 : u₃.getMem (u₃.getReg .x2 + 48) = s.getReg .x10 := by
    rw [x2₃, show s.getReg .x2 - 5248 + 48 = s.getReg .x2 - 5200 from
      BitVec.eq_of_toNat_eq (by addr_omega [hb])]; exact m48'
  rcases hres with ⟨hcap, hfails⟩ | ⟨hcap, slot, row, v, hslot, hrow, hv, hR⟩
  · -- `Err`
    have pc₃ := b80009278_pc_taken h₃ (by rw [t1952, hcap]; rfl)
    obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800093a8_spec pc₃ (by
      rv_eval [x2₃]
      rv_eval [m48']
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
    have f₄ : MemFrame u₃ u₄ (s.getReg .x10) 24 := h₄.memFrame (by
      intro w hw
      simp only [b800093a8, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> rv_eval [m48] <;> addr_omega [ho])
    have hcap₄ := b800093a8_m2 h₄
    rw [m48, b80009278_x10 h₃] at hcap₄
    obtain ⟨w, hr₅, hw⟩ := err_exit hpre P₃.base (b800093a8_pc h₄)
      ((b800093a8_keeps h₄ .x2 (by decide)).trans x2₃) f₄ hcap₄ hfails
    exact ⟨w, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inr hw⟩
  -- `Ok`: the row to `f + 3584`
  have pc₃ := b80009278_pc_not_taken h₃ (by rw [t1952]; exact hcap)
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000928c_spec pc₃ trivial
  have k₄ := b8000928c_keeps h₄
  have m₄ := b8000928c_mem_same h₄
  have x2₄ : u₄.getReg .x2 = s.getReg .x2 - 5248 := (k₄ .x2 (by decide)).trans x2₃
  have P₄ := P₃.same hpre x2₄ m₄ fun r hr ↦ k₄ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  have m34 : ∀ a, u₄.getMem a = t.getMem a := fun a ↦ by rw [m₄, m₃]
  have x10₄ : u₄.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 1664 := by
    rw [b8000928c_x10 h₄, x2₃]; exact BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have x11₄ : u₄.getReg .x11 = s.getReg .x2 - BitVec.ofNat 64 3272 := by
    rw [b8000928c_x11 h₄, x2₃]; exact BitVec.eq_of_toNat_eq (by addr_omega [hb])
  obtain ⟨w, hr₅, hd | ⟨hpc₅, hpres₅, F₅, hN₅, hrow₅⟩⟩ := memcpy_row hMC hpre P₄.base
    (b8000928c_pc h₄) (D := 1664) (S := 3272) ⟨by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide⟩ (Or.inl (by decide)) x10₄ x11₄ (b8000928c_x12 h₄)
  · exact ⟨w, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inr (Or.inr hd)⟩
  have x2₅ : w.getReg .x2 = s.getReg .x2 - 5248 := (hpres₅.reg .x2).trans x2₄
  have hH₅ : HeapOk w := ⟨by rw [hN₅]; exact P₄.base.heap.lo, by rw [hN₅]; exact P₄.base.heap.hi⟩
  have P₅ := P₄.step hpre x2₅ hH₅ (le_of_eq hN₅.symm) (by decide) (by decide) (by decide)
    (by decide) F₅ fun r hr ↦ hpres₅.reg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  -- the slot
  have hp8 : s.getReg .x2 - 3296 + 8 = s.getReg .x2 - 3288 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have hp16 : s.getReg .x2 - 3296 + 16 = s.getReg .x2 - 3280 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have eptr : vecPtr t (s.getReg .x2 - 3296) = t.getMem (s.getReg .x2 - 3288) := by
    simp only [vecPtr, hp8]
  have elen : vecLen t (s.getReg .x2 - 3296) = t.getMem (s.getReg .x2 - 3280) := by
    simp only [vecLen, hp16]
  have sbt : NewBuf s t (t.getMem (s.getReg .x2 - 3288)) (24 * (t.getMem (s.getReg .x2 - 3280)).toNat) 8 ∧
      eListAt t (t.getMem (s.getReg .x2 - 3288)) (t.getMem (s.getReg .x2 - 3280)).toNat = slot := by
    have h1 := hslot.buf
    have h2 := hslot.vec.len
    have h3 := hslot.elems
    rw [eptr] at h1
    rw [elen] at h2
    simp only [vecEs, eptr, elen] at h3
    refine ⟨by simp only [NewBuf] at h1 ⊢; omega, h3⟩
  have sbw := buf_step hpre P₄.base (by decide) F₅ (le_of_eq hN₅.symm) (xs := slot)
    (⟨by have := sbt.1; simp only [NewBuf, heapNext, m34] at this ⊢; exact this,
      by rw [← sbt.2]; simp only [eListAt, eAt, m34]⟩)
  have sreg : (t.getMem (s.getReg .x2 - 3280)).toNat = 0 ∨
      (Region (t.getMem (s.getReg .x2 - 3288)) (24 * (t.getMem (s.getReg .x2 - 3280)).toNat) ∧
        ∀ lo m, heapEnd ≤ lo.toNat →
          Apart (t.getMem (s.getReg .x2 - 3288)) (24 * (t.getMem (s.getReg .x2 - 3280)).toNat) lo m) := by
    rcases vec_heaped hpre B₂ hslot with h0 | H
    · left; rw [← elen]; exact h0
    · right; rw [eptr, elen] at H; exact ⟨H.region, H.above⟩
  refine ⟨w, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inl ⟨_, _, slot, row, v,
    { P₅ with
      sbuf := sbw
      sreg := sreg
      pc := by rw [hpc₅, returnAddress_eq, b8000928c_x1 h₄]; decide
      x20 := by rw [hpres₅.reg .x20, k₄ .x20 (by decide), b80009278_x20 h₃, t1968]
      x24 := by rw [hpres₅.reg .x24, k₄ .x24 (by decide), b80009278_x24 h₃, t1960]
      row' := by
        rw [show s.getReg .x2 - 1664 = s.getReg .x2 - BitVec.ofNat 64 1664 from rfl, hrow₅,
          ← hrow]
        simp only [eListAt, eAt, m34]; rfl
      value := by
        rw [show s.getReg .x2 - 1736 = s.getReg .x2 - BitVec.ofNat 64 1736 from rfl,
          SW.e hpre hH₅ (by decide) (by decide) (by decide) (by decide) F₅, ← hv]
        simp only [eAt, m34]; rfl
      rest := (hR.keep fun T hT ↦ Layer.transcriptAt_congr m34 hT).keep fun T hT ↦
        SW.tat hpre P₄.base hH₅ (le_of_eq hN₅.symm) (by decide) F₅ hT }⟩⟩

/-- At `0x8000941c`: the word checked, its limbs in `s10`, `s9`, `a1`. -/
structure Q3 (s u : MachineState) (cl : KeccakClaim) (mp ml sp sl : Word) (slot : List E)
    (word : E) : Prop extends P2 s u cl mp ml sp sl slot where
  pc : u.pc = 0x8000941c
  x20 : u.getReg .x20 = sl
  x24 : u.getReg .x24 = sp
  x11 : u.getReg .x11 = (Model.limbs word).2.2
  x25 : u.getReg .x25 = (Model.limbs word).2.1
  x26 : u.getReg .x26 = (Model.limbs word).1
  rest : Rest s u (kInputs (s.getReg .x12).toNat cl (some (instOf s ++ slot, word)))

theorem regs5 {u v : MachineState} {l : List Reg} (hl : ∀ r ∈ l, v.getReg r = u.getReg r)
    (h : ([.x9, .x18, .x19, .x22, .x23] : List Reg).all (fun r ↦ decide (r ∈ l)) = true) :
    ∀ r ∈ ([.x9, .x18, .x19, .x22, .x23] : List Reg), v.getReg r = u.getReg r :=
  fun r hr ↦ hl r (by have := List.all_eq_true.mp h r hr; simpa using this)

theorem pres5 {u v : MachineState} (h : Preserves u v) :
    ∀ r ∈ ([.x9, .x18, .x19, .x22, .x23] : List Reg), v.getReg r = u.getReg r := fun r hr ↦
  h.reg r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)

theorem to_checked (hNS : NextScalarSpec) (hM : MulSpec) {s u : MachineState} {cl : KeccakClaim}
    {mp ml sp sl : Word} {slot row : List E} {v : E} (hpre : VerifyKeccakPreW s)
    (A : Q1 s u cl mp ml sp sl slot row v) :
    ∃ t, Reaches Image.code u t ∧ ((∃ word, Q3 s t cl mp ml sp sl slot word) ∨ Done s t) := by
  have hb := bounds hpre
  have B := A.base
  have hS := hpre.self.self
  have ho := hpre.out
  -- 0x800092a4: the value's limbs, `next_scalar()`
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800092a4_spec A.pc (by
    rv_eval [B.x2]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b800092a4_keeps h₁
  have m₁ := b800092a4_mem_same h₁
  have x2₁ : u₁.getReg .x2 = s.getReg .x2 - 5248 := (k₁ .x2 (by decide)).trans B.x2
  have P₁ := A.toP2.same hpre x2₁ m₁ (regs5 k₁ (by decide))
  have a2 (n : Nat) (hn : n ≤ 5248) :
      s.getReg .x2 - 5248 + BitVec.ofNat 64 n = s.getReg .x2 - BitVec.ofNat 64 (5248 - n) :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb, hn])
  have hv : Model.limbs v = (u₁.getReg .x27, u₁.getReg .x21, u₁.getReg .x8) := by
    rw [← A.value, limbs_eAt, b800092a4_x27 h₁, b800092a4_x21 h₁, b800092a4_x8 h₁, B.x2,
      show s.getReg .x2 - 5248 + 3512 = s.getReg .x2 - 1736 from a2 3512 (by decide),
      show s.getReg .x2 - 5248 + 3520 = s.getReg .x2 - 1736 + 8 from
        (a2 3520 (by decide)).trans (BitVec.eq_of_toNat_eq (by addr_omega [hb])),
      show s.getReg .x2 - 5248 + 3528 = s.getReg .x2 - 1736 + 16 from
        (a2 3528 (by decide)).trans (BitVec.eq_of_toNat_eq (by addr_omega [hb]))]
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 3296 := by rw [b800092a4_x10 h₁, B.x2]; rv_eval []
  have x11₁ : u₁.getReg .x11 = s.getReg .x11 := by rw [b800092a4_x11 h₁, A.x9]
  have tp := P₁.base.tpre hpre (n := 32) (k := nextScalarStack) 3296 x10₁ x11₁ (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hnp : NextScalarPre u₁ := {
    out := tp.out
    self := tp.self
    stack := tp.stack
    outStack := tp.outStack
    selfStack := tp.selfStack
    outSelf := tp.outSelf
    proofStack := tp.proofStack
    proofOut := tp.proofOut
    rodata := tp.rodata
    outRodata := tp.outRodata
    selfRodata := tp.selfRodata }
  obtain ⟨u₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ := hNS.call hr₁ (b800092a4_pc h₁) hnp
  swap
  · exact ⟨u₂, hr₂, Or.inr (Or.inr hd)⟩
  have x2₂ : u₂.getReg .x2 = s.getReg .x2 - 5248 := (hpres₂.reg .x2).trans x2₁
  have F₂ : DFrame u₁ u₂ (SW s u₁ u₂ [(3296, 32)] true) := DFrame.mono hpost₂.frame
    fun a ha ↦ by
      rcases ha with h | h | h
      · exact Or.inl (out_sw (K := 3296) (n := 32) x10₁ h)
      · rw [x11₁] at h; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h⟩)))
      · exact Or.inr (Or.inl (stk_sw hpre x2₁ (by decide) h))
  have hnx := hpre.stack.next
  unfold verifyKeccakStack at hnx
  have hN₂ : heapNext u₂ = heapNext u₁ := by
    simp only [heapNext]
    rw [hpost₂.frame _ fun i hi h ↦ by
      rw [x10₁, x11₁] at h
      have hsf := hpre.selfFree.2
      simp only [stackLo, x2₁] at h
      rcases h with h | h | h <;> addr_omega [h, hi, hb, hnx, hS, hsf]]
  have H₂ : HeapOk u₂ := ⟨by rw [hN₂]; exact P₁.base.heap.lo, by rw [hN₂]; exact P₁.base.heap.hi⟩
  have P₂ := P₁.step hpre x2₂ H₂ (le_of_eq hN₂.symm) (by decide) (by decide) (by decide)
    (by decide) F₂ (pres5 hpres₂)
  have R₁ : Rest s u₁ (TM.nextScalar >>= fun word ↦
      TM.require (row.getD 0 0 * word = v) >>= fun _ ↦
        kInputs (s.getReg .x12).toNat cl (some (instOf s ++ slot, word))) :=
    A.rest.keep fun T hT ↦ Layer.transcriptAt_congr m₁ hT
  -- 0x800092c8: the tag
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800092c8_spec
    (by rw [hpc₂, returnAddress_eq, b800092a4_x1 h₁]; decide) (by
      rv_eval [x2₂]
      and_intros <;> valid_access hpre.stack.valid [hb])
  have k₃ := b800092c8_keeps h₃
  have m₃ := b800092c8_mem_same h₃
  have x2₃ : u₃.getReg .x2 = s.getReg .x2 - 5248 := (k₃ .x2 (by decide)).trans x2₂
  have P₃ := P₂.same hpre x2₃ m₃ (regs5 k₃ (by decide))
  have tag : u₂.getMem (u₂.getReg .x2 + 1952) = u₂.getMem (s.getReg .x2 - 3296) := by
    rw [x2₂]; exact congrArg _ (a2 1952 (by decide))
  by_cases hok : u₂.getMem (s.getReg .x2 - 3296) = 0
  swap
  · -- `Err`
    have pc₃ := b800092c8_pc_not_taken h₃ (by rw [tag]; exact hok)
    have m48' : u₃.getMem (s.getReg .x2 - 5200) = s.getReg .x10 := P₃.m48
    have m48 : u₃.getMem (u₃.getReg .x2 + 48) = s.getReg .x10 := by
      rw [x2₃, show s.getReg .x2 - 5248 + 48 = s.getReg .x2 - 5200 from a2 48 (by decide)]
      exact m48'
    obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800092d8_spec pc₃ (by
      rv_eval [x2₃]
      rv_eval [m48']
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
    have f₄ : MemFrame u₃ u₄ (s.getReg .x10) 24 := h₄.memFrame (by
      intro w hw
      simp only [b800092d8, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> rv_eval [m48] <;> addr_omega [ho])
    have hcap₄ := b800092d8_m2 h₄
    rw [m48] at hcap₄
    obtain ⟨t, hr₅, ht⟩ := err_exit hpre P₃.base (b800092d8_pc h₄)
      ((b800092d8_keeps h₄ .x2 (by decide)).trans x2₃) f₄ hcap₄ (R₁.fail fun T hT ↦ by
        have h := hpost₂.value T (by rw [x11₁]; exact hT)
        rw [x10₁] at h
        generalize TM.nextScalar.run T = o at h
        rcases o with _ | ⟨x, T'⟩
        · rfl
        · exact absurd h.1 hok)
    exact ⟨t, hr₂.trans (hr₃.trans (hr₄.trans hr₅)), Or.inr ht⟩
  -- `Ok`: the word at `f + 1960`
  have pc₃ := b800092c8_pc_taken h₃ (by rw [tag]; exact hok)
  have a8 : s.getReg .x2 - 3296 + 8 = s.getReg .x2 - 3288 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have R₃ : Rest s u₃ (TM.require (row.getD 0 0 * eAt u₂ (s.getReg .x2 - 3288) = v) >>= fun _ ↦
      kInputs (s.getReg .x12).toNat cl (some (instOf s ++ slot, eAt u₂ (s.getReg .x2 - 3288)))) :=
    R₁.step fun T hT ↦ by
      have h := hpost₂.value T (by rw [x11₁]; exact hT)
      rw [x10₁, x11₁, a8] at h
      generalize TM.nextScalar.run T = o at h ⊢
      rcases o with _ | ⟨x, T'⟩
      · exact absurd (h.1.symm.trans hok) (by decide)
      · obtain ⟨-, hx, hT'⟩ := h
        exact ⟨T', by rw [hx], Layer.transcriptAt_congr m₃ hT'⟩
  set word := eAt u₂ (s.getReg .x2 - 3288) with hword
  have hwl : Model.limbs word = (u₂.getMem (s.getReg .x2 - 3288), u₂.getMem (s.getReg .x2 - 3280),
      u₂.getMem (s.getReg .x2 - 3272)) := by
    rw [hword, limbs_eAt, show s.getReg .x2 - 3288 + 8 = s.getReg .x2 - 3280 from
      BitVec.eq_of_toNat_eq (by addr_omega [hb]), show s.getReg .x2 - 3288 + 16 = s.getReg .x2 - 3272 from
      BitVec.eq_of_toNat_eq (by addr_omega [hb])]
  -- 0x800093bc: checked mode
  have x9₃ : u₃.getReg .x9 = s.getReg .x11 := P₃.x9
  have hck : extractByte (s.getMem (s.getReg .x11 + 360)) 0 ≠ 0 := by
    have h := hpre.checked
    simp only [Checked] at h
    rwa [← Transcript.add_ofNat_zero (s.getReg .x11 + 360),
      Runtime.byteAt_add (by addr_omega [hS]) (by decide)] at h
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800093bc_spec pc₃ (by
    rv_eval [x2₃, x9₃]
    refine ⟨by valid_access hpre.stack.valid [hb], by addr_omega [hS],
      Mapped.valid hS.1 (i := 360) (by decide)⟩)
  have pc₄ : u₄.pc = 0x800093c8 := Sym.Expect.Holds.pc_eq h₄ (by
    rv_eval [x9₃, P₃.base.byte hpre]
    exact ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hck (by
      have := congrArg BitVec.toNat (beq_iff_eq.mp h)
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth] at this
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))] at this
      simpa using this)))
  have k₄ := b800093bc_keeps h₄
  have m₄ := b800093bc_mem_same h₄
  have x2₄ : u₄.getReg .x2 = s.getReg .x2 - 5248 := (k₄ .x2 (by decide)).trans x2₃
  have P₄ := P₃.same hpre x2₄ m₄ (regs5 k₄ (by decide))
  -- 0x800093c8: the word to `f + 1952`, `row[0] * word` into `f + 416`
  obtain ⟨u₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b800093c8_spec pc₄ (by
    rv_eval [x2₄]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₅ := b800093c8_keeps h₅
  have x2₅ : u₅.getReg .x2 = s.getReg .x2 - 5248 := (k₅ .x2 (by decide)).trans x2₄
  have F₅ : DFrame u₄ u₅ (Slots s [(3296, 24), (5224, 8)]) := block_slots h₅ (by
    intro w hw
    simp only [b800093c8, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h <;> subst h <;> rv_eval [x2₄] <;> exact slots_of hpre (by decide))
  have P₅ := P₄.block hpre x2₅ (by decide) (by decide) (by decide) (by decide) F₅
    (regs5 k₅ (by decide))
  have s1952 : u₅.getMem (s.getReg .x2 - 3296) = u₄.getReg .x26 := by
    have h := b800093c8_m_x2_1952 h₅
    rwa [x2₄, show s.getReg .x2 - 5248 + 1952 = s.getReg .x2 - 3296 from a2 1952 (by decide)] at h
  have s1960 : u₅.getMem (s.getReg .x2 - 3288) = u₄.getReg .x25 := by
    have h := b800093c8_m_x2_1960 h₅
    rwa [x2₄, show s.getReg .x2 - 5248 + 1960 = s.getReg .x2 - 3288 from a2 1960 (by decide)] at h
  have s1968 : u₅.getMem (s.getReg .x2 - 3280) = u₄.getReg .x11 := by
    have h := b800093c8_m_x2_1968 h₅
    rwa [x2₄, show s.getReg .x2 - 5248 + 1968 = s.getReg .x2 - 3280 from a2 1968 (by decide)] at h
  have w5 : eAt u₅ (s.getReg .x2 - 3296) = word := by
    apply eq_of_limbs
    rw [limbs_eAt, hwl,
      show s.getReg .x2 - 3296 + 8 = s.getReg .x2 - 3288 from
        BitVec.eq_of_toNat_eq (by addr_omega [hb]),
      show s.getReg .x2 - 3296 + 16 = s.getReg .x2 - 3280 from
        BitVec.eq_of_toNat_eq (by addr_omega [hb]),
      s1952, s1960, s1968, k₄ .x26 (by decide), k₄ .x25 (by decide),
      b800093bc_x11 h₄, b800092c8_x26 h₃, b800092c8_x25 h₃, m₃, x2₂]
    simp only [Prod.mk.injEq]
    refine ⟨congrArg _ (a2 1960 (by decide)), congrArg _ (a2 1968 (by decide)), ?_⟩
    rw [x2₃]; exact congrArg _ (BitVec.eq_of_toNat_eq (by addr_omega [hb]))
  have e5 : eAt u₅ (s.getReg .x2 - 1664) = eAt u₄ (s.getReg .x2 - 1664) :=
    SW.e hpre P₅.base.heap (by decide) (J := 1664) (by decide) (by decide) (by decide) (slots_sw F₅)
  have e4 : eAt u₄ (s.getReg .x2 - 1664) = eAt u₂ (s.getReg .x2 - 1664) := by
    simp only [Rv64Verifier.eAt, m₄, m₃]
  have e2 : eAt u₂ (s.getReg .x2 - 1664) = eAt u₁ (s.getReg .x2 - 1664) :=
    SW.e hpre H₂ (by decide) (J := 1664) (by decide) (by decide) (by decide) F₂
  have e1 : eAt u₁ (s.getReg .x2 - 1664) = eAt u (s.getReg .x2 - 1664) := by
    simp only [Rv64Verifier.eAt, m₁]
  have hrow0 : row.getD 0 0 = eAt u₅ (s.getReg .x2 - 1664) := by
    rw [← A.row', List.getD_eq_getElem _ _ (by rw [eListAt_length]; decide), eListAt_getElem,
      show s.getReg .x2 - 1664 + BitVec.ofNat 64 (24 * 0) = s.getReg .x2 - 1664 from
        BitVec.add_zero _, e5, e4, e2, e1]
  have x10₅ : u₅.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 4832 := by
    rw [b800093c8_x10 h₅, x2₄]; exact a2 416 (by decide)
  have x11₅ : u₅.getReg .x11 = s.getReg .x2 - BitVec.ofNat 64 1664 := by
    rw [b800093c8_x11 h₅, x2₄]; exact a2 3584 (by decide)
  have x12₅ : u₅.getReg .x12 = s.getReg .x2 - BitVec.ofNat 64 3296 := by
    rw [b800093c8_x12 h₅, x2₄]; exact a2 1952 (by decide)
  obtain ⟨u₆, hr₆, hd | ⟨hpc₆, hpres₆, B₆, hN₆, F₆, hprod⟩⟩ := mul_slots hM hpre P₅.base
    (b800093c8_pc h₅) (Ko := 4832) (Kl := 1664) (Kr := 3296) ⟨by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩ (Or.inr (by decide))
    (Or.inr (by decide)) x10₅ x11₅ x12₅
  · exact ⟨u₆, hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆))), Or.inr (Or.inr hd)⟩
  have x2₆ : u₆.getReg .x2 = s.getReg .x2 - 5248 := (hpres₆.reg .x2).trans x2₅
  have P₆ := P₅.step hpre x2₆ B₆.heap (le_of_eq hN₆.symm) (by decide) (by decide) (by decide)
    (by decide) F₆ (pres5 hpres₆)
  have hprod' : eAt u₆ (s.getReg .x2 - 4832) = row.getD 0 0 * word := by
    rw [hrow0, ← w5]; exact hprod
  have hl6 : Model.limbs (row.getD 0 0 * word) = (u₆.getMem (u₆.getReg .x2 + 416),
      u₆.getMem (u₆.getReg .x2 + 424), u₆.getMem (u₆.getReg .x2 + 432)) := by
    rw [← hprod', limbs_eAt, x2₆]
    simp only [Prod.mk.injEq]
    refine ⟨congrArg _ (a2 416 (by decide)).symm, congrArg _ ?_, congrArg _ ?_⟩ <;>
      exact BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have y27 : u₆.getReg .x27 = u₁.getReg .x27 := by
    rw [hpres₆.reg .x27, k₅ .x27 (by decide), k₄ .x27 (by decide), k₃ .x27 (by decide),
      hpres₂.reg .x27]
  have y21 : u₆.getReg .x21 = u₁.getReg .x21 := by
    rw [hpres₆.reg .x21, k₅ .x21 (by decide), k₄ .x21 (by decide), k₃ .x21 (by decide),
      hpres₂.reg .x21]
  have y8 : u₆.getReg .x8 = u₁.getReg .x8 := by
    rw [hpres₆.reg .x8, k₅ .x8 (by decide), k₄ .x8 (by decide), k₃ .x8 (by decide),
      hpres₂.reg .x8]
  have hr06 : Reaches Image.code u u₆ := hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆)))
  -- a limb differs: `Err(22)`
  have err22 (y : MachineState) (hy : y.pc = 0x800095dc) (hry : Reaches Image.code u y)
      (hmy : ∀ a, y.getMem a = u₆.getMem a) (hx2y : y.getReg .x2 = s.getReg .x2 - 5248)
      (hne : row.getD 0 0 * word ≠ v) :
      ∃ t, Reaches Image.code u t ∧ ((∃ word, Q3 s t cl mp ml sp sl slot word) ∨ Done s t) := by
    have By := P₆.base.same hx2y hmy
    have m48' : y.getMem (s.getReg .x2 - 5200) = s.getReg .x10 := by rw [hmy]; exact P₆.m48
    have m48 : y.getMem (y.getReg .x2 + 48) = s.getReg .x10 := by
      rw [hx2y, show s.getReg .x2 - 5248 + 48 = s.getReg .x2 - 5200 from a2 48 (by decide)]
      exact m48'
    obtain ⟨y₁, hr₇, h₇⟩ := Sym.BlockSpec.reaches b800095dc_spec hy (by
      rv_eval [hx2y]
      rv_eval [m48']
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
    have f₇ : MemFrame y y₁ (s.getReg .x10) 24 := h₇.memFrame (by
      intro w hw
      simp only [b800095dc, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> rv_eval [m48] <;> addr_omega [ho])
    have hcap₇ := b800095dc_m1 h₇
    rw [m48] at hcap₇
    obtain ⟨t, hr₈, ht⟩ := err_exit hpre By (b800095dc_pc h₇)
      ((b800095dc_keeps h₇ .x2 (by decide)).trans hx2y) f₇ hcap₇ (R₃.require_fail hne)
    exact ⟨t, hry.trans (hr₇.trans hr₈), Or.inr ht⟩
  have limb_ne {a b c : Word} (h : (a, b, c) ≠ (u₁.getReg .x27, u₁.getReg .x21, u₁.getReg .x8))
      (e : Model.limbs (row.getD 0 0 * word) = (a, b, c)) : row.getD 0 0 * word ≠ v :=
    fun h' ↦ h (by rw [← e, ← hv, h'])
  -- the three limbs
  obtain ⟨u₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b800093f8_spec (by
      rw [hpc₆, returnAddress_eq, b800093c8_x1 h₅]; decide) (by
    rv_eval [x2₆]
    valid_access hpre.stack.valid [hb])
  have m₇ := b800093f8_mem_same h₇
  have k₇ := b800093f8_keeps h₇
  have x2₇ : u₇.getReg .x2 = s.getReg .x2 - 5248 := (k₇ .x2 (by decide)).trans x2₆
  by_cases c1 : u₆.getMem (u₆.getReg .x2 + 416) = u₆.getReg .x27
  swap
  · exact err22 u₇ (b800093f8_pc_taken h₇ c1) (hr06.trans hr₇) m₇ x2₇
      (limb_ne (fun h ↦ c1 (by rw [y27]; exact (Prod.mk.inj h).1)) hl6)
  obtain ⟨u₈, hr₈, h₈⟩ := Sym.BlockSpec.reaches b80009400_spec (b800093f8_pc_not_taken h₇ c1) (by
    rv_eval [x2₇]
    valid_access hpre.stack.valid [hb])
  have m₈ := b80009400_mem_same h₈
  have k₈ := b80009400_keeps h₈
  have x2₈ : u₈.getReg .x2 = s.getReg .x2 - 5248 := (k₈ .x2 (by decide)).trans x2₇
  have m78 : ∀ a, u₈.getMem a = u₆.getMem a := fun a ↦ by rw [m₈, m₇]
  have c2' : u₇.getMem (u₇.getReg .x2 + 424) = u₇.getReg .x21 ↔
      u₆.getMem (u₆.getReg .x2 + 424) = u₆.getReg .x21 := by
    rw [m₇, k₇ .x2 (by decide), k₇ .x21 (by decide)]
  by_cases c2 : u₆.getMem (u₆.getReg .x2 + 424) = u₆.getReg .x21
  swap
  · exact err22 u₈ (b80009400_pc_taken h₈ (fun h ↦ c2 (c2'.mp h))) (hr06.trans (hr₇.trans hr₈))
      m78 x2₈ (limb_ne (fun h ↦ c2 (by rw [y21]; exact (Prod.mk.inj (Prod.mk.inj h).2).1)) hl6)
  obtain ⟨u₉, hr₉, h₉⟩ := Sym.BlockSpec.reaches b80009408_spec
    (b80009400_pc_not_taken h₈ (c2'.mpr c2)) (by
    rv_eval [x2₈]
    valid_access hpre.stack.valid [hb])
  have m₉ := b80009408_mem_same h₉
  have k₉ := b80009408_keeps h₉
  have x2₉ : u₉.getReg .x2 = s.getReg .x2 - 5248 := (k₉ .x2 (by decide)).trans x2₈
  have m79 : ∀ a, u₉.getMem a = u₆.getMem a := fun a ↦ by rw [m₉, m78]
  have c3' : u₈.getMem (u₈.getReg .x2 + 432) = u₈.getReg .x8 ↔
      u₆.getMem (u₆.getReg .x2 + 432) = u₆.getReg .x8 := by
    rw [m78, k₈ .x2 (by decide), k₈ .x8 (by decide), k₇ .x2 (by decide), k₇ .x8 (by decide)]
  by_cases c3 : u₆.getMem (u₆.getReg .x2 + 432) = u₆.getReg .x8
  swap
  · exact err22 u₉ (b80009408_pc_taken h₉ (fun h ↦ c3 (c3'.mp h)))
      (hr06.trans (hr₇.trans (hr₈.trans hr₉))) m79 x2₉
      (limb_ne (fun h ↦ c3 (by rw [y8]; exact (Prod.mk.inj (Prod.mk.inj h).2).2)) hl6)
  have heq : row.getD 0 0 * word = v := by
    apply eq_of_limbs
    rw [hl6, hv, c1, c2, c3, y27, y21, y8]
  -- 0x80009410: the word's limbs back
  obtain ⟨u₁₀, hr₁₀, h₁₀⟩ := Sym.BlockSpec.reaches b80009410_spec
    (b80009408_pc_not_taken h₉ (c3'.mpr c3)) (by
    rv_eval [x2₉]
    valid_access hpre.stack.valid [hb])
  have m₁₀ := b80009410_mem_same h₁₀
  have k₁₀ := b80009410_keeps h₁₀
  have x2₁₀ : u₁₀.getReg .x2 = s.getReg .x2 - 5248 := (k₁₀ .x2 (by decide)).trans x2₉
  have m610 : ∀ a, u₁₀.getMem a = u₆.getMem a := fun a ↦ by rw [m₁₀, m79]
  have P₇ := P₆.same hpre x2₇ m₇ (regs5 k₇ (by decide))
  have P₈ := P₇.same hpre x2₈ m₈ (regs5 k₈ (by decide))
  have P₉ := P₈.same hpre x2₉ m₉ (regs5 k₉ (by decide))
  have P₁₀ := P₉.same hpre x2₁₀ m₁₀ (regs5 k₁₀ (by decide))
  have f24 : u₆.getMem (s.getReg .x2 - 5224) = u₄.getReg .x26 := by
    have h1 : u₆.getMem (s.getReg .x2 - 5224) = u₅.getMem (s.getReg .x2 - 5224) :=
      SW.mem hpre B₆.heap (by decide) (J := 5224) (by decide) (by decide) (by decide) F₆
    have h2 := b800093c8_m_x2_24 h₅
    rw [x2₄, show s.getReg .x2 - 5248 + 24 = s.getReg .x2 - 5224 from a2 24 (by decide)] at h2
    rw [h1, h2]
  have tat : ∀ T, TranscriptAt u₃ (s.getReg .x11) T → TranscriptAt u₁₀ (s.getReg .x11) T :=
    fun T hT ↦ Layer.transcriptAt_congr m610 (SW.tat hpre P₅.base B₆.heap (le_of_eq hN₆.symm)
      (by decide) F₆ (P₄.base.block_tat hpre (by decide) F₅ (Layer.transcriptAt_congr m₄ hT)))
  refine ⟨u₁₀, hr06.trans (hr₇.trans (hr₈.trans (hr₉.trans hr₁₀))), Or.inl ⟨word, { P₁₀ with
    pc := b80009410_pc h₁₀
    x20 := by
      rw [k₁₀ .x20 (by decide), k₉ .x20 (by decide), k₈ .x20 (by decide), k₇ .x20 (by decide),
        hpres₆.reg .x20, k₅ .x20 (by decide), k₄ .x20 (by decide), k₃ .x20 (by decide),
        hpres₂.reg .x20, k₁ .x20 (by decide), A.x20]
    x24 := by
      rw [k₁₀ .x24 (by decide), k₉ .x24 (by decide), k₈ .x24 (by decide), k₇ .x24 (by decide),
        hpres₆.reg .x24, k₅ .x24 (by decide), k₄ .x24 (by decide), k₃ .x24 (by decide),
        hpres₂.reg .x24, k₁ .x24 (by decide), A.x24]
    x11 := by
      rw [b80009410_x11 h₁₀, k₉ .x25 (by decide), k₈ .x25 (by decide), k₇ .x25 (by decide),
        hpres₆.reg .x25, b800093c8_x25 h₅, b800093bc_x11 h₄, hwl, m₃, x2₃]
      exact congrArg _ (BitVec.eq_of_toNat_eq (by addr_omega [hb]))
    x25 := by
      rw [b80009410_x25 h₁₀, k₉ .x26 (by decide), k₈ .x26 (by decide), k₇ .x26 (by decide),
        hpres₆.reg .x26, b800093c8_x26 h₅, k₄ .x25 (by decide), b800092c8_x25 h₃, hwl, x2₂]
      exact congrArg _ (BitVec.eq_of_toNat_eq (by addr_omega [hb]))
    x26 := by
      rw [b80009410_x26 h₁₀, x2₉, m79,
        show s.getReg .x2 - 5248 + 24 = s.getReg .x2 - 5224 from a2 24 (by decide), f24,
        k₄ .x26 (by decide), b800092c8_x26 h₃, hwl, x2₂]
      exact congrArg _ (BitVec.eq_of_toNat_eq (by addr_omega [hb]))
    rest := (R₃.require_pass heq).keep tat }⟩⟩

/-- At `0x80009454`, the inputs' opening next: the outputs' point `instance ++ slot` at
`f + 392`, the word's limbs in `s10`, `s9` and at `f + 40`. -/
structure I0 (s u : MachineState) (cl : KeccakClaim) (mp ml sp sl : Word) (slot : List E)
    (word : E) : Prop extends P2 s u cl mp ml sp sl slot where
  pc : u.pc = 0x80009454
  m40 : u.getMem (s.getReg .x2 - 5208) = (Model.limbs word).2.2
  outV : NewVecE s u (s.getReg .x2 - 4856) (instOf s ++ slot)
  x20 : u.getReg .x20 = u.getMem (s.getReg .x2 - 4856)
  x25 : u.getReg .x25 = (Model.limbs word).2.1
  x26 : u.getReg .x26 = (Model.limbs word).1
  rest : Rest s u (kInputs (s.getReg .x12).toNat cl (some (instOf s ++ slot, word)))

theorem to_concat (hC : SliceConcatSpec) {s u : MachineState} {cl : KeccakClaim}
    {mp ml sp sl : Word} {slot : List E} {word : E} (hpre : VerifyKeccakPreW s)
    (A : Q3 s u cl mp ml sp sl slot word) :
    ∃ t, Reaches Image.code u t ∧ (I0 s t cl mp ml sp sl slot word ∨ Dead Image.code t) := by
  have hb := bounds hpre
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have B := A.base
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000941c_spec A.pc (by
    rv_eval [B.x2]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b8000941c_keeps h₁
  have x2₁ : u₁.getReg .x2 = s.getReg .x2 - 5248 := (k₁ .x2 (by decide)).trans B.x2
  have F₁ : DFrame u u₁ (Slots s [(3296, 32), (5208, 8)]) := block_slots h₁ (by
    intro w hw
    simp only [b8000941c, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h | h <;> subst h <;> rv_eval [B.x2] <;>
      exact slots_of hpre (by decide))
  have P₁ := A.toP2.block hpre x2₁ (by decide) (by decide) (by decide) (by decide) F₁
    (regs5 k₁ (by decide))
  have a2 (n : Nat) (hn : n ≤ 5248) :
      s.getReg .x2 - 5248 + BitVec.ofNat 64 n = s.getReg .x2 - BitVec.ofNat 64 (5248 - n) :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb, hn])
  have st (n K : Nat) (hn : n + K = 5248) (x : Word)
      (h : u₁.getMem (u.getReg .x2 + BitVec.ofNat 64 n) = x) :
      u₁.getMem (s.getReg .x2 - BitVec.ofNat 64 K) = x := by
    rw [B.x2, a2 n (by omega), show 5248 - n = K by omega] at h; exact h
  have m1952 := st 1952 3296 rfl _ (b8000941c_m_x2_1952 h₁)
  have m1960 := st 1960 3288 rfl _ (b8000941c_m_x2_1960 h₁)
  have m1968 := st 1968 3280 rfl _ (b8000941c_m_x2_1968 h₁)
  have m1976 := st 1976 3272 rfl _ (b8000941c_m_x2_1976 h₁)
  have m40 := st 40 5208 rfl _ (b8000941c_m_x2_40 h₁)
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 4856 := by rw [b8000941c_x10 h₁, B.x2]; rv_eval []
  have x11₁ : u₁.getReg .x11 = s.getReg .x2 - 3296 := by rw [b8000941c_x11 h₁, B.x2]; rv_eval []
  have x12₁ : u₁.getReg .x12 = 2 := b8000941c_x12 h₁
  have hok := A.ok
  have hl := hok.2
  have hinst : kInstLen s = (s.getReg .x12).toNat := by simp only [kInstLen, hok.1]
  have p0 : partPtr u₁ 0 = s.getReg .x14 := by
    simp only [partPtr, x11₁]
    rw [show s.getReg .x2 - 3296 + BitVec.ofNat 64 (16 * 0) = s.getReg .x2 - BitVec.ofNat 64 3296 from
      BitVec.eq_of_toNat_eq (by addr_omega [hb]), m1952, B.x2,
      show s.getReg .x2 - 5248 + 56 = s.getReg .x2 - 5192 from a2 56 (by decide)]
    exact (SW.mem hpre P₁.base.heap (by decide) (J := 5192) (by decide) (by decide) (by decide)
      (slots_sw F₁)).symm.trans P₁.m56
  have l0 : partLen u₁ 0 = (s.getReg .x12).toNat := by
    simp only [partLen, x11₁]
    rw [show s.getReg .x2 - 3296 + BitVec.ofNat 64 (16 * 0) + 8 = s.getReg .x2 - BitVec.ofNat 64 3288 from
      BitVec.eq_of_toNat_eq (by addr_omega [hb]), m1960, A.x18]
  have p1 : partPtr u₁ 1 = sp := by
    simp only [partPtr, x11₁]
    rw [show s.getReg .x2 - 3296 + BitVec.ofNat 64 (16 * 1) = s.getReg .x2 - BitVec.ofNat 64 3280 from
      BitVec.eq_of_toNat_eq (by addr_omega [hb]), m1968, A.x24]
  have l1 : partLen u₁ 1 = sl.toNat := by
    simp only [partLen, x11₁]
    rw [show s.getReg .x2 - 3296 + BitVec.ofNat 64 (16 * 1) + 8 = s.getReg .x2 - BitVec.ofNat 64 3272 from
      BitVec.eq_of_toNat_eq (by addr_omega [hb]), m1976, A.x20]
  have hiR := hpre.inst
  have hiF := hpre.instFree.resolve_left (by rw [hinst]; have := hok.2; omega)
  have hiS := hpre.instStack
  rw [hinst] at hiR hiF hiS
  simp only [kInst] at hiR hiF hiS
  have hst : RtStack u₁ sliceConcatStack := hpre.stack.sub 5248 x2₁
    (by unfold verifyKeccakStack; decide) (by decide) (by decide) (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  unfold verifyKeccakStack at hb hab hnx hiS hsm
  have sb := P₁.sbuf
  have hhi := P₁.base.heap.hi
  have hcp : SliceConcatPre u₁ := {
    heap := P₁.base.heap
    out := by rw [x10₁]; addr_omega [hb, hsm]
    count := by rw [x12₁]; decide
    slices := by rw [x11₁, x12₁]; addr_omega [hb, hsm]
    stack := hst
    outFree := by rw [x10₁]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    outStack := by rw [x10₁]; simp only [stackLo, x2₁]; addr_omega [hb]
    slicesFree := by rw [x11₁, x12₁]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    slicesStack := by rw [x11₁, x12₁]; simp only [stackLo, x2₁]; addr_omega [hb]
    slicesOut := by rw [x11₁, x12₁, x10₁]; addr_omega [hb]
    part := by
      intro i hi
      rw [x12₁] at hi
      have hi' : i < 2 := hi
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · rw [p0, l0]
        right
        rcases hiR with h0 | hR
        · omega
        have hm := P₁.base.mono
        obtain ⟨f1, f2⟩ := hiF
        refine ⟨hR, ⟨by addr_omega [hR, f1, hm], f2⟩, ?_, ?_⟩
        · simp only [stackLo, x2₁]; addr_omega [hR, hiS, hb]
        · rw [x10₁]; addr_omega [hR, hiS, hb]
      · rw [p1, l1]
        rcases P₁.sreg with h0 | ⟨hR, hA⟩
        · left; exact h0
        by_cases hz : sl.toNat = 0
        · left; exact hz
        right
        have hbuf := sb.1
        simp only [NewBuf] at hbuf
        refine ⟨hR, ⟨Or.inl (by omega), by addr_omega [hR, hbuf, hhi]⟩, hA _ _ ?_, hA _ _ ?_⟩
        · simp only [stackLo, x2₁]; addr_omega [hb, hab]
        · rw [x10₁]; addr_omega [hb, hab] }
  obtain ⟨u₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ := hC.call hr₁ (b8000941c_pc h₁) hcp
  swap
  · exact ⟨u₂, hr₂, Or.inr hd⟩
  have x2₂ : u₂.getReg .x2 = s.getReg .x2 - 5248 := (hpres₂.reg .x2).trans x2₁
  have F₂ : DFrame u₁ u₂ (SW s u₁ u₂ [(4856, 24)] false) := DFrame.mono hpost₂.frame
    fun a ha ↦ cframe_sw hpre 4856 x2₁ x10₁ (by decide) a ha
  have P₂ := P₁.step hpre x2₂ hpost₂.heap hpost₂.mono (by decide) (by decide) (by decide)
    (by decide) F₂ (pres5 hpres₂)
  have hval := hpost₂.value
  have hparts : (parts u₁).flatten = eListAt u₁ (partPtr u₁ 0) (partLen u₁ 0) ++
      eListAt u₁ (partPtr u₁ 1) (partLen u₁ 1) := by
    simp [parts, x12₁, List.range_succ]
  have e0 : eListAt u₁ (partPtr u₁ 0) (partLen u₁ 0) = instOf s := by
    rw [p0, l0, instOf, kInst, kInstLen, hok.1]
    rcases hiR with h0 | hR
    · omega
    have hm := missInst hpre P₁.base.heap
    rw [hinst] at hm
    simp only [kInst] at hm
    exact P₁.base.eListAt hm (Or.inr (by addr_omega [hR]))
  have e1 : eListAt u₁ (partPtr u₁ 1) (partLen u₁ 1) = slot := by rw [p1, l1]; exact sb.2
  rw [hparts, e0, e1, x10₁] at hval
  -- 0x80009448
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80009448_spec
    (by rw [hpc₂, returnAddress_eq, b8000941c_x1 h₁]; decide) (by
      rv_eval [x2₂]
      valid_access hpre.stack.valid [hb])
  have k₃ := b80009448_keeps h₃
  have m₃ := b80009448_mem_same h₃
  have x2₃ : u₃.getReg .x2 = s.getReg .x2 - 5248 := (k₃ .x2 (by decide)).trans x2₂
  have P₃ := P₂.same hpre x2₃ m₃ (regs5 k₃ (by decide))
  refine ⟨u₃, hr₂.trans hr₃, Or.inl { P₃ with
    pc := b80009448_pc h₃
    m40 := by
      rw [m₃]
      have h : u₂.getMem (s.getReg .x2 - 5208) = u₁.getMem (s.getReg .x2 - 5208) :=
        SW.mem hpre hpost₂.heap (by decide) (J := 5208) (by decide) (by decide) (by decide) F₂
      exact h.trans (m40.trans A.x11)
    outV := Layer.newVecE_congr m₃ (Open.newVecE_mono hval P₁.base.mono)
    x20 := by rw [b80009448_x20 h₃, x2₂, m₃]; exact congrArg _ (a2 392 (by decide))
    x25 := by rw [k₃ .x25 (by decide), hpres₂.reg .x25, k₁ .x25 (by decide), A.x25]
    x26 := by rw [k₃ .x26 (by decide), hpres₂.reg .x26, k₁ .x26 (by decide), A.x26]
    rest := ((A.rest.keep fun T hT ↦ B.block_tat hpre (by decide) F₁ hT).keep fun T hT ↦
      SW.tat hpre P₁.base hpost₂.heap hpost₂.mono (by decide) F₂ hT).keep fun T hT ↦
        Layer.transcriptAt_congr m₃ hT }⟩

end Rv64Verifier.Gkr.Keccak
