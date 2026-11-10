import Rv64Verifier.Proofs.Main.NewRuns

/-!
# `Bytecode::new`'s blocks: `positions` resized

From the runs' exit (`RE` at `0x800007b8`, its state `t₀`), `positions.resize(end, 0)`: nothing to
do (`resize_skip`), or room made (`RZ`, at `0x800007d4`, through `grow_amortized` at `0x8000c184`
if full: `resize_room`), then the new halves zeroed (`memset` and a last `sh`: `resize_fill`), to
`RY` at `0x8000082c`.
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Proofs.Bytecode
  Rv64Verifier.Blocks.F3

/-- `n` `u16`s from two byte ranges with equal bytes. -/
theorem halvesAt_of_bytes {t s : MachineState} {a b : Word} {n m : Nat}
    (h : bytesAt t a m = bytesAt s b m) (hm : 2 * n ≤ m) (ha : a.toNat % 2 = 0)
    (hb : b.toNat % 2 = 0) (ha' : a.toNat + m < 2 ^ 64) (hb' : b.toNat + m < 2 ^ 64) :
    halvesAt t a n = halvesAt s b n := by
  have e : ∀ (x : Word) (j : Nat), x + BitVec.ofNat 64 (2 * j) + 1 = x + BitVec.ofNat 64 (2 * j + 1) :=
    fun x j ↦ by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl
  unfold halvesAt
  apply List.map_congr_left
  intro j hj
  simp only [List.mem_range] at hj
  rw [getHalfword_eq_append (by addr_omega [ha, ha', hj, hm]),
    getHalfword_eq_append (by addr_omega [hb, hb', hj, hm]), e, e,
    bytesAt_eq_iff.mp h (2 * j) (by omega), bytesAt_eq_iff.mp h (2 * j + 1) (by omega)]

/-- The position past the runs: `end`. -/
abbrev rend (words : List Word) (i L : Nat) (g : GrpSt) (st : Model.NewState) : Nat :=
  (rfold words i L g st g.2.2.length).2.1

/-- What the resize writes: `positions`' capacity and buffer, callees' stacks, `NEXT`, the heap
from `H` on and `positions`' old buffer. -/
@[rv_addr] def Wz (H : Nat) (P : Word) (n : Nat) (a : Word) : Prop :=
  Within a (msp + 448) 16 ∨ Within a (msp - 4096) 4096 ∨ Within a nextAddr 8 ∨
    (H ≤ a.toNat ∧ a.toNat < heapEnd) ∨ Within a P n

/-- Room made in `positions` for `end`: at `0x800007d4`, from `RE`'s `t₀`. -/
structure RZ (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (g : GrpSt) (D C N : Word) (H1 : Nat) (t₀ t : MachineState) : Prop where
  re : RE s words u₀ i L Hb st g D C N H1 t₀
  hlt : st.positions.length < rend words i L g st
  frame : BFrame t₀ t (Wz (heapNext t₀) (vecPtr t₀ (msp + 448))
    ((vecCap t₀ (msp + 448)).toNat * 2))
  heap : HeapOk t
  mono : heapNext t₀ ≤ heapNext t
  vin : VecIn t (msp + 448) 2 2 (heapNext u₀) (heapNext t)
  capE : rend words i L g st ≤ (vecCap t (msp + 448)).toNat
  sf : (vecPtr t (msp + 448) = vecPtr t₀ (msp + 448) ∧ vecCap t (msp + 448) = vecCap t₀ (msp + 448)) ∨
    (vecCap t (msp + 448)).toNat * 2 = 0 ∨ heapNext t₀ ≤ (vecPtr t (msp + 448)).toNat
  pos : halvesAt t (vecPtr t (msp + 448)) st.positions.length = st.positions
  len : vecLen t (msp + 448) = vecLen t₀ (msp + 448)
  x2 : t.getReg .x2 = msp
  x8 : t.getReg .x8 = u₀.getReg .x8
  x9 : t.getReg .x9 = BitVec.ofNat 64 (rfold words i L g st g.2.2.length).2.2.length
  x12 : t.getReg .x12 = D
  x15 : t.getReg .x15 = u₀.getReg .x9
  x18 : t.getReg .x18 = BitVec.ofNat 64 g.2.2.length
  x20 : t.getReg .x20 = BitVec.ofNat 64 (8 * L)
  x21 : t.getReg .x21 = inputBase + BitVec.ofNat 64 (8 * (1 + 2 ^ 14 * i))
  x23 : t.getReg .x23 = BitVec.ofNat 64 st.positions.length
  x24 : t.getReg .x24 = BitVec.ofNat 64 (rend words i L g st - st.positions.length)
  x27 : t.getReg .x27 = BitVec.ofNat 64 (rend words i L g st)

/-- `positions` resized: at `0x8000082c`, from `RE`'s `t₀`, its length not yet set. -/
structure RY (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (g : GrpSt) (D C N : Word) (H1 : Nat) (t₀ t : MachineState) : Prop where
  re : RE s words u₀ i L Hb st g D C N H1 t₀
  frame : BFrame t₀ t (Wz (heapNext t₀) (vecPtr t₀ (msp + 448))
    ((vecCap t₀ (msp + 448)).toNat * 2))
  heap : HeapOk t
  mono : heapNext t₀ ≤ heapNext t
  vin : VecIn t (msp + 448) 2 2 (heapNext u₀) (heapNext t)
  capE : rend words i L g st ≤ (vecCap t (msp + 448)).toNat
  sf : (vecPtr t (msp + 448) = vecPtr t₀ (msp + 448) ∧ vecCap t (msp + 448) = vecCap t₀ (msp + 448)) ∨
    (vecCap t (msp + 448)).toNat * 2 = 0 ∨ heapNext t₀ ≤ (vecPtr t (msp + 448)).toNat
  pos : halvesAt t (vecPtr t (msp + 448)) (rend words i L g st) =
    Model.resizeRust st.positions (rend words i L g st)
  x2 : t.getReg .x2 = msp
  x8 : t.getReg .x8 = u₀.getReg .x8
  x9 : t.getReg .x9 = BitVec.ofNat 64 (rfold words i L g st g.2.2.length).2.2.length
  x12 : t.getReg .x12 = D
  x15 : t.getReg .x15 = u₀.getReg .x9
  x18 : t.getReg .x18 = BitVec.ofNat 64 g.2.2.length
  x19 : t.getReg .x19 = vecPtr t (msp + 448)
  x20 : t.getReg .x20 = BitVec.ofNat 64 (8 * L)
  x21 : t.getReg .x21 = inputBase + BitVec.ofNat 64 (8 * (1 + 2 ^ 14 * i))
  x27 : t.getReg .x27 = BitVec.ofNat 64 (rend words i L g st)

section
variable {s u₀ t₀ : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C N : Word} {H1 : Nat}

/-- `positions`' facts at the runs' exit. -/
theorem RE.posFacts (h : RE s words u₀ i L Hb st g D C N H1 t₀) :
    (vecLen t₀ (msp + 448)).toNat = st.positions.length ∧ st.positions.length < 2 ^ 31 ∧
      st.positions.length ≤ rend words i L g st ∧
      rend words i L g st ≤ st.positions.length + L ∧ L ≤ 2 ^ 14 := by
  have e := congrArg List.length h.vs.vecs.positions
  simp only [halvesAt, List.length_map, List.length_range] at e
  have hl := h.vs.bufs.p.len_lt (by decide) (by
    have := h.rb.rc.k.ng.heap.hi; simp only [heapNext, heapEnd] at this ⊢; omega)
  have h2 := rfold_end_le words i L g st g.2.2.length
  have h3 := (rfold_spec words i L g st g.2.2.length).2.1
  have hL := h.rb.rc.k.hL
  refine ⟨e, by rw [← e]; exact hl, ?_, h2, by omega⟩
  simp only [rend]; omega

end

section
variable {s u₀ t₀ : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C N : Word} {H1 : Nat}

theorem resizeRust_self (l : List (BitVec 16)) : Model.resizeRust l l.length = l := by
  simp [Model.resizeRust]

/-- `0x800007b8`, `end` no further than `positions`' length: nothing to resize. -/
theorem resize_skip (h : RE s words u₀ i L Hb st g D C N H1 t₀) (hpc : t₀.pc = 0x800007b8)
    (hle : rend words i L g st ≤ st.positions.length) :
    ∃ v, Reaches Image.code t₀ v ∧ v.pc = 0x8000082c ∧ RY s words u₀ i L Hb st g D C N H1 t₀ v := by
  have rc := h.rb.rc
  have hsp := rc.k.ng.sp
  obtain ⟨hpl, hp31, hpe, hel, hL⟩ := h.posFacts
  have he : rend words i L g st = st.positions.length := by omega
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b800007b8_spec hpc (by rv_eval [hsp, msp]; decide)
  have k₁ := b800007b8_keeps h₁
  have hm₁ := b800007b8_mem_same h₁
  have hpc₁ := b800007b8_pc_taken h₁ (by
    rw [h.x27, hsp, h.rb.m32, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [rend] at hle; omega)
  have hsp₁ : t₁.getReg .x2 = msp := (k₁ .x2 (by decide)).trans hsp
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b80000828_spec hpc₁ (by rv_eval [hsp₁, msp]; decide)
  have k₂ := b80000828_keeps h₂
  have hm₂ := b80000828_mem_same h₂
  have hm : ∀ a, t₂.getMem a = t₀.getMem a := fun a ↦ (hm₂ a).trans (hm₁ a)
  have hn : heapNext t₂ = heapNext t₀ := by simp only [heapNext, hm]
  have p2 : vecPtr t₂ (msp + 448) = vecPtr t₀ (msp + 448) := hm _
  have c2 : vecCap t₂ (msp + 448) = vecCap t₀ (msp + 448) := hm _
  have l2 : vecLen t₂ (msp + 448) = vecLen t₀ (msp + 448) := hm _
  have R : ∀ r ∈ ([.x2, .x8, .x9, .x12, .x18, .x20, .x21, .x27] : List Reg),
      t₂.getReg r = t₀.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (k₂ _ (by decide)).trans (k₁ _ (by decide))
  refine ⟨t₂, r₁.trans r₂, b80000828_pc h₂, ⟨h, BFrame.of_same hm _, ⟨by rw [hn]; exact rc.k.ng.heap.lo,
    by rw [hn]; exact rc.k.ng.heap.hi⟩, le_of_eq hn.symm, ?_, ?_, Or.inl ⟨p2, c2⟩, ?_,
    (R .x2 (by simp)).trans hsp, (R .x8 (by simp)).trans h.rb.x8, (R .x9 (by simp)).trans h.x9,
    (R .x12 (by simp)).trans h.x12, ?_, (R .x18 (by simp)).trans h.rb.x18, ?_,
    (R .x20 (by simp)).trans h.rb.x20, (R .x21 (by simp)).trans h.rb.x21,
    (R .x27 (by simp)).trans h.x27⟩⟩
  · rw [hn]; exact h.vs.bufs.p.keep c2 p2 l2 le_rfl
  · rw [he, c2, ← hpl]; exact h.vs.bufs.p.len
  · rw [he, resizeRust_self, ← hpl]
    have e := h.vs.vecs.positions
    simp only at e
    rw [← e]
    simp only [halvesAt, getHalfword_same hm, p2]
  · rw [k₂ .x15 (by decide), b800007b8_x15 h₁, hsp]; exact rc.k.bm.m40
  · rw [b80000828_x19 h₂, hsp₁, hm₁]; exact p2.symm

end

section
variable {s u₀ t₀ : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C N : Word} {H1 : Nat}

/-- `0x800007b8`, `end` past `positions`' length: room made for it, through `grow_amortized` if
`positions` is too small. -/
theorem resize_room (h : RE s words u₀ i L Hb st g D C N H1 t₀) (hpc : t₀.pc = 0x800007b8)
    (hlt : st.positions.length < rend words i L g st) :
    ∃ v, Reaches Image.code t₀ v ∧ (Dead Image.code v ∨
      (v.pc = 0x800007d4 ∧ RZ s words u₀ i L Hb st g D C N H1 t₀ v)) := by
  have rc := h.rb.rc
  have hsp := rc.k.ng.sp
  obtain ⟨hpl, hp31, hpe, hel, hL⟩ := h.posFacts
  have bp := h.vs.bufs.p
  have hhi0 := rc.k.ng.heap.hi
  simp only [heapNext, heapEnd] at hhi0
  have hE : (rfold words i L g st g.2.2.length).2.1 < 2 ^ 32 := by simp only [rend] at hel; omega
  simp only [rend] at hlt hpe hel
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b800007b8_spec hpc (by rv_eval [hsp, msp]; decide)
  have k₁ := b800007b8_keeps h₁
  have hm₁ := b800007b8_mem_same h₁
  have hpc₁ := b800007b8_pc_not_taken h₁ (by
    rw [h.x27, hsp, h.rb.m32, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)
  have hsp₁ : t₁.getReg .x2 = msp := (k₁ .x2 (by decide)).trans hsp
  have x23₁ : t₁.getReg .x23 = BitVec.ofNat 64 st.positions.length := by
    rw [b800007b8_x23 h₁, hsp]; exact h.rb.m32
  have x27₁ : t₁.getReg .x27 = BitVec.ofNat 64 (rend words i L g st) :=
    (k₁ .x27 (by decide)).trans h.x27
  have x15₁ : t₁.getReg .x15 = u₀.getReg .x9 := by
    rw [b800007b8_x15 h₁, hsp]; exact rc.k.bm.m40
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b800007c4_spec hpc₁ (by rv_eval [hsp₁, msp]; decide)
  have k₂ := b800007c4_keeps h₂
  have hm₂ := b800007c4_mem_same h₂
  have hsp₂ : t₂.getReg .x2 = msp := (k₂ .x2 (by decide)).trans hsp₁
  have hm : ∀ a, t₂.getMem a = t₀.getMem a := fun a ↦ (hm₂ a).trans (hm₁ a)
  have hlc := bp.len
  rw [hpl] at hlc
  have hcap : (vecCap t₀ (msp + 448)).toNat < 2 ^ 32 := by
    rcases bp.buf with h0 | ⟨_, h2⟩
    · omega
    · simp only [heapNext] at h2; omega
  have ex : (t₁.getReg .x27 - t₁.getReg .x23).toNat =
      rend words i L g st - st.positions.length := by
    rw [x27₁, x23₁]; simp only [rend]; addr_omega [hlt, hE]
  have ec : (t₁.getMem (t₁.getReg .x2 + (448 : Word)) - t₁.getReg .x23).toNat =
      (vecCap t₀ (msp + 448)).toNat - st.positions.length := by
    rw [x23₁, hsp₁, hm₁, show t₀.getMem (msp + 448) = vecCap t₀ (msp + 448) from rfl]
    addr_omega [hlc, hcap, hp31]
  have x24₂ : t₂.getReg .x24 = BitVec.ofNat 64 (rend words i L g st - st.positions.length) := by
    rw [b800007c4_x24 h₂]; apply BitVec.eq_of_toNat_eq; rw [ex, BitVec.toNat_ofNat]; simp only [rend]; omega
  have R₂ : ∀ r ∈ ([.x2, .x8, .x9, .x12, .x15, .x18, .x20, .x21, .x23, .x27] : List Reg),
      t₂.getReg r = t₀.getReg r ∨ r = .x15 ∨ r = .x23 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr rfl)
      | exact Or.inl ((k₂ _ (by decide)).trans (k₁ _ (by decide)))
  have x15₂ : t₂.getReg .x15 = u₀.getReg .x9 := (k₂ .x15 (by decide)).trans x15₁
  have x23₂ : t₂.getReg .x23 = BitVec.ofNat 64 st.positions.length :=
    (k₂ .x23 (by decide)).trans x23₁
  have hpos₀ : halvesAt t₀ (vecPtr t₀ (msp + 448)) st.positions.length = st.positions := by
    have e := h.vs.vecs.positions
    simp only at e
    rw [hpl] at e
    exact e
  by_cases hroom : rend words i L g st ≤ (vecCap t₀ (msp + 448)).toNat
  · have hpc₂ := b800007c4_pc_not_taken h₂ (by rw [ex, ec]; simp only [rend] at hroom ⊢; omega)
    have hn : heapNext t₂ = heapNext t₀ := by simp only [heapNext, hm]
    have p2 : vecPtr t₂ (msp + 448) = vecPtr t₀ (msp + 448) := hm _
    have c2 : vecCap t₂ (msp + 448) = vecCap t₀ (msp + 448) := hm _
    have l2 : vecLen t₂ (msp + 448) = vecLen t₀ (msp + 448) := hm _
    have e2 : halvesAt t₂ (vecPtr t₀ (msp + 448)) st.positions.length =
        halvesAt t₀ (vecPtr t₀ (msp + 448)) st.positions.length := by
      simp only [halvesAt, getHalfword_same hm]
    refine ⟨t₂, r₁.trans r₂, Or.inr ⟨hpc₂, h, hlt, BFrame.of_same hm _,
      ⟨by rw [hn]; exact rc.k.ng.heap.lo, by rw [hn]; exact rc.k.ng.heap.hi⟩, le_of_eq hn.symm,
      by rw [hn]; exact bp.keep c2 p2 l2 le_rfl, by rw [c2]; exact hroom, Or.inl ⟨p2, c2⟩,
      by rw [p2, e2]; exact hpos₀, l2, hsp₂, ?_, ?_, ?_, x15₂,
      ?_, ?_, ?_, x23₂, x24₂, ?_⟩⟩
    all_goals first
      | exact (k₂ _ (by decide)).trans ((k₁ _ (by decide)).trans h.rb.x8)
      | exact (k₂ _ (by decide)).trans ((k₁ _ (by decide)).trans h.x9)
      | exact (k₂ _ (by decide)).trans ((k₁ _ (by decide)).trans h.x12)
      | exact (k₂ _ (by decide)).trans ((k₁ _ (by decide)).trans h.rb.x18)
      | exact (k₂ _ (by decide)).trans ((k₁ _ (by decide)).trans h.rb.x20)
      | exact (k₂ _ (by decide)).trans ((k₁ _ (by decide)).trans h.rb.x21)
      | exact (k₂ _ (by decide)).trans ((k₁ _ (by decide)).trans h.x27)
  -- `grow_amortized`
  have hpc₂ := b800007c4_pc_taken h₂ (by rw [ex, ec]; simp only [rend] at hroom ⊢; omega)
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b800009e8_spec hpc₂ trivial
  have k₃ := b800009e8_keeps h₃
  have hm₃ := b800009e8_mem_same h₃
  have hsp₃ : t₃.getReg .x2 = msp := (k₃ .x2 (by decide)).trans hsp₂
  have x10₃ : t₃.getReg .x10 = msp + 448 := by rw [b800009e8_x10 h₃, hsp₂]
  have hm03 : ∀ a, t₃.getMem a = t₀.getMem a := fun a ↦ (hm₃ a).trans (hm a)
  have hn₃ : heapNext t₃ = heapNext t₀ := by simp only [heapNext, hm03]
  have p3 : vecPtr t₃ (msp + 448) = vecPtr t₀ (msp + 448) := hm03 _
  have c3 : vecCap t₃ (msp + 448) = vecCap t₀ (msp + 448) := hm03 _
  have pre : GrowPre t₃ := {
    heap := ⟨by rw [hn₃]; exact rc.k.ng.heap.lo, by rw [hn₃]; exact rc.k.ng.heap.hi⟩
    self := by rw [x10₃]; exact validRange_of (by decide) (by decide) (by decide)
    align := by rw [b800009e8_x13 h₃]; decide
    size := by rw [b800009e8_x14 h₃]; decide
    raw := by
      rw [x10₃, b800009e8_x14 h₃, b800009e8_x13 h₃]
      simp only [RawVecOk, Buf, p3, c3, hn₃]
      refine ⟨bp.al, bp.buf.imp_right fun hb' ↦ ⟨?_, hb'.2⟩⟩
      have := rc.k.a.inv.heap.lo
      simp only [heapStart, heapNext] at hb' this ⊢; omega
    stack := rtStack_msp hsp₃ (by decide) (by decide)
    selfFree := by
      rw [x10₃]
      exact ⟨Or.inr (by simp only [heapEnd]; decide), by addr_omega []⟩
    selfStack := by rw [x10₃]; simp only [stackLo, hsp₃, growStack]; addr_omega [] }
  obtain ⟨t₄, r₄, ⟨hpc₄, hpv, post⟩ | hd⟩ := growAmortized.call r₃ (b800009e8_pc h₃) pre
  swap
  · exact ⟨t₄, r₁.trans (r₂.trans r₄), Or.inl hd⟩
  have hpc₄' : t₄.pc = 0x80000a08 := by rw [hpc₄, returnAddress, b800009e8_x1 h₃]; decide
  have hsp₄ : t₄.getReg .x2 = msp := (hpv.reg .x2).trans hsp₃
  obtain ⟨t₅, r₅, h₅⟩ := Sym.BlockSpec.reaches b80000a08_spec hpc₄' trivial
  have k₅ := b80000a08_keeps h₅
  have hm₅ := b80000a08_mem_same h₅
  by_cases hok : t₄.getReg .x10 = 0xffffffffffffffff
  swap
  · obtain ⟨w, rw', hw⟩ := abort (u := t₅) (by rw [b80000a08_pc_taken h₅ hok]; decide)
    exact ⟨w, r₁.trans (r₂.trans (r₄.trans (r₅.trans rw'))), Or.inl hw⟩
  have hsp₅ : t₅.getReg .x2 = msp := (k₅ .x2 (by decide)).trans hsp₄
  obtain ⟨t₆, r₆, h₆⟩ := Sym.BlockSpec.reaches b80000a10_spec (b80000a08_pc_not_taken h₅ hok)
    (by rv_eval [hsp₅, msp]; decide)
  have k₆ := b80000a10_keeps h₆
  have hm₆ := b80000a10_mem_same h₆
  have hsp₆ : t₆.getReg .x2 = msp := (k₆ .x2 (by decide)).trans hsp₅
  obtain ⟨pcap, praw, pby⟩ := post.ok hok
  have pfr := post.frame
  have pfresh := post.fresh hok
  rw [x10₃, b800009e8_x11 h₃, b800009e8_x12 h₃, x23₂, x24₂] at pcap
  rw [x10₃, b800009e8_x14 h₃] at pby pfresh
  rw [x10₃] at pfr
  rw [b800009e8_x13 h₃] at pfresh
  simp only [BitVec.toNat_ofNat, show (2 : Word).toNat = 2 from rfl] at pcap pby pfresh
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by simp only [rend]; omega)] at pcap
  have hhi₄ := post.heap.hi
  have hmo₄ := post.mono
  simp only [heapNext, heapEnd] at hhi₄ hmo₄
  have hm46 : ∀ a, t₆.getMem a = t₄.getMem a := fun a ↦ (hm₆ a).trans (hm₅ a)
  have hf : BFrame t₀ t₆ (Wz (heapNext t₀) (vecPtr t₀ (msp + 448))
      ((vecCap t₀ (msp + 448)).toNat * 2)) := fun a ha ↦ by
    have e1 : byteAt t₆ a = byteAt t₄ a := by rw [byteAt_eq, byteAt_eq, hm46]
    have e3 : byteAt t₃ a = byteAt t₀ a := by rw [byteAt_eq, byteAt_eq, hm03]
    rw [e1, ← e3]
    refine pfr.byte a fun hw ↦ ha ?_
    rcases hw with hw | hw | hw | ⟨hw1, hw2⟩
    · exact Or.inl hw
    · simp only [stackLo, hsp₃, growStack] at hw
      exact Or.inr (Or.inl (by addr_omega [hw]))
    · exact Or.inr (Or.inr (Or.inl hw))
    · rw [hn₃] at hw1
      simp only [heapNext] at hw2
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hw1, by simp only [heapEnd]; omega⟩)))
  have hn₆ : heapNext t₆ = heapNext t₄ := by simp only [heapNext, hm46]
  have p6 : vecPtr t₆ (msp + 448) = vecPtr t₄ (msp + 448) := hm46 _
  have c6 : vecCap t₆ (msp + 448) = vecCap t₄ (msp + 448) := hm46 _
  have l6 : vecLen t₆ (msp + 448) = vecLen t₀ (msp + 448) :=
    hf.getMem (by decide) fun j hj hw ↦ by
      rcases hw with hw | hw | hw | ⟨hw1, hw2⟩ | hw
      · addr_omega [hw, hj]
      · addr_omega [hw, hj]
      · addr_omega [hw, hj]
      · simp only [heapEnd] at hw2; addr_omega [hw2, hj]
      · rcases bp.buf with h0 | ⟨_, h2⟩
        · simp only [Within] at hw; omega
        · simp only [heapNext] at h2; addr_omega [hw, hj, h2, hhi0]
  have hlo0 := rc.k.a.inv.heap.lo
  have hmo0 := rc.k.ng.mono
  simp only [heapStart, heapNext] at hlo0 hmo0
  have R : ∀ r ∈ ([.x8, .x9, .x18, .x20, .x21, .x24, .x27] : List Reg),
      t₆.getReg r = t₂.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (k₆ _ (by decide)).trans ((k₅ _ (by decide)).trans ((hpv.reg _ (by decide)).trans
        (k₃ _ (by decide))))
  have R2 : ∀ r ∈ ([.x8, .x9, .x18, .x20, .x21, .x27] : List Reg), t₂.getReg r = t₀.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (k₂ _ (by decide)).trans (k₁ _ (by decide))
  refine ⟨t₆, r₁.trans (r₂.trans (r₄.trans (r₅.trans r₆))), Or.inr ⟨b80000a10_pc h₆, h, hlt, hf,
    ⟨by rw [hn₆]; exact post.heap.lo, by rw [hn₆]; exact post.heap.hi⟩,
    by rw [hn₆, ← hn₃]; exact post.mono, ?_, ?_, ?_, ?_, l6, hsp₆,
    (R .x8 (by simp)).trans ((R2 .x8 (by simp)).trans h.rb.x8),
    (R .x9 (by simp)).trans ((R2 .x9 (by simp)).trans h.x9), ?_, ?_,
    (R .x18 (by simp)).trans ((R2 .x18 (by simp)).trans h.rb.x18),
    (R .x20 (by simp)).trans ((R2 .x20 (by simp)).trans h.rb.x20),
    (R .x21 (by simp)).trans ((R2 .x21 (by simp)).trans h.rb.x21), ?_,
    (R .x24 (by simp)).trans x24₂, (R .x27 (by simp)).trans ((R2 .x27 (by simp)).trans h.x27)⟩⟩
  · refine ⟨?_, by rw [p6]; exact pfresh.1, ?_, fun h0 ↦ absurd h0 ?_⟩
    · rw [l6, c6, hpl]; simp only [rend] at pcap ⊢; omega
    · rw [p6, c6, hn₆]
      rcases pfresh.2 with h0 | ⟨h1, h2⟩
      · exact Or.inl h0
      · right; rw [hn₃] at h1; simp only [heapNext] at h1 h2 ⊢; omega
    · rw [c6]; simp only [rend] at pcap ⊢; omega
  · rw [c6]; simp only [rend] at pcap ⊢; omega
  · rw [p6, c6]
    rcases pfresh.2 with h0 | ⟨h1, _⟩
    · exact Or.inr (Or.inl h0)
    · rw [hn₃] at h1; exact Or.inr (Or.inr h1)
  · refine Eq.trans ?_ hpos₀
    have hb2 : bytesAt t₄ (vecPtr t₄ (msp + 448)) (2 * st.positions.length) =
        bytesAt t₀ (vecPtr t₀ (msp + 448)) (2 * st.positions.length) := by
      rw [← p3]
      refine bytesAt_eq_iff.mpr fun j hj ↦ ?_
      have e := bytesAt_eq_iff.mp pby j (by rw [c3]; omega)
      rw [e, byteAt_eq, byteAt_eq, hm03]
    have e1 : halvesAt t₆ (vecPtr t₆ (msp + 448)) st.positions.length =
        halvesAt t₄ (vecPtr t₄ (msp + 448)) st.positions.length := by
      rw [p6]; simp only [halvesAt, getHalfword_same hm46]
    rw [e1]
    refine halvesAt_of_bytes hb2 le_rfl pfresh.1 bp.al ?_ ?_
    · rcases pfresh.2 with h0 | ⟨_, h2⟩
      · simp only [rend] at pcap; omega
      · simp only [heapNext] at h2; simp only [rend] at pcap; omega
    · rcases bp.buf with h0 | ⟨_, h2⟩
      · omega
      · simp only [heapNext] at h2; omega
  · rw [b80000a10_x12 h₆, hsp₅, hm₅, ← hm46]
    rw [hf.getMem (by decide) fun j hj hw ↦ by
      rcases hw with hw | hw | hw | ⟨hw1, hw2⟩ | hw
      · addr_omega [hw, hj]
      · addr_omega [hw, hj]
      · addr_omega [hw, hj]
      · simp only [heapEnd] at hw2; addr_omega [hw2, hj]
      · rcases bp.buf with h0 | ⟨_, h2⟩
        · simp only [Within] at hw; omega
        · simp only [heapNext] at h2; addr_omega [hw, hj, h2, hhi0]]
    exact rc.m72
  · rw [b80000a10_x15 h₆, k₅ .x19 (by decide), hpv.reg .x19 (by decide), b800009e8_x19 h₃, x15₂]
  · rw [b80000a10_x23 h₆, hsp₅, hm₅, ← hm46]
    exact l6.trans (by rw [← hpl, BitVec.ofNat_toNat, BitVec.setWidth_eq])

end

/-- `positions` resized: kept below its old length, zero above. -/
theorem resize_content {t v : MachineState} {p : Word} {E : Nat} {l : List (BitVec 16)}
    (hl : halvesAt t p l.length = l) (hPE : l.length < E) (hp : p.toNat % 2 = 0)
    (hb : p.toNat + 2 * E < 2 ^ 64)
    (hkeep : ∀ j < 2 * l.length, byteAt v (p + BitVec.ofNat 64 j) = byteAt t (p + BitVec.ofNat 64 j))
    (hz : ∀ j, 2 * l.length ≤ j → j + 2 < 2 * E → byteAt v (p + BitVec.ofNat 64 j) = 0)
    (hlast : v.getHalfword (p + BitVec.ofNat 64 (2 * (E - 1))) = 0) :
    halvesAt v p E = Model.resizeRust l E := by
  have e : ∀ (j : Nat), p + BitVec.ofNat 64 (2 * j) + 1 = p + BitVec.ofNat 64 (2 * j + 1) :=
    fun j ↦ by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl
  apply List.ext_getElem
  · simp only [halvesAt, Model.resizeRust, List.length_map, List.length_range, List.length_append,
      List.length_take, List.length_replicate]
    omega
  · intro j h1 h2
    simp only [halvesAt, List.length_map, List.length_range] at h1
    simp only [halvesAt, List.getElem_map, List.getElem_range, Model.resizeRust]
    rw [List.getElem_append]
    split
    · rename_i hj
      simp only [List.length_take] at hj
      rw [List.getElem_take]
      have hj' : j < l.length := by omega
      have e2 : l[j] = t.getHalfword (p + BitVec.ofNat 64 (2 * j)) := by
        rw [List.getElem_of_eq hl.symm hj']
        simp only [halvesAt, List.getElem_map, List.getElem_range]
      rw [e2]
      exact getHalfword_eq_of_bytes (by addr_omega [hp, hb, h1])
        (hkeep _ (by omega)) (by rw [e]; exact hkeep _ (by omega))
    · rename_i hj
      simp only [List.length_take] at hj
      rw [List.getElem_replicate]
      by_cases hjE : j = E - 1
      · rw [hjE]; exact hlast
      · rw [getHalfword_eq_append (by addr_omega [hp, hb, h1]), e, hz _ (by omega) (by omega),
          hz _ (by omega) (by omega)]
        rfl

section
variable {s u₀ t₀ t : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C N : Word} {H1 : Nat}

/-- `0x800007d4` to `0x8000081c`: the new halves but the last zeroed (`memset`). -/
theorem resize_pre (h : RZ s words u₀ i L Hb st g D C N H1 t₀ t) (hpc : t.pc = 0x800007d4) :
    ∃ u, Reaches Image.code t u ∧ (Dead Image.code u ∨ (u.pc = 0x8000081c ∧
      BFrame t u (fun a ↦ Within a (vecPtr t (msp + 448) + BitVec.ofNat 64 (2 * st.positions.length))
        (2 * (rend words i L g st - st.positions.length) - 2)) ∧
      (∀ j, 2 * st.positions.length ≤ j → j + 2 < 2 * rend words i L g st →
        byteAt u (vecPtr t (msp + 448) + BitVec.ofNat 64 j) = 0) ∧
      u.getReg .x10 = vecPtr t (msp + 448) + BitVec.ofNat 64 (2 * (rend words i L g st - 1)) ∧
      u.getReg .x23 = BitVec.ofNat 64 (rend words i L g st - 1) ∧ u.getReg .x12 = D ∧
      u.getReg .x15 = u₀.getReg .x9 ∧ u.getReg .x19 = vecPtr t (msp + 448) ∧
      ∀ r ∈ ([.x2, .x8, .x9, .x18, .x20, .x21, .x27] : List Reg), u.getReg r = t.getReg r)) := by
  have hsp := h.x2
  obtain ⟨hpl, hp31, hpe, hel, hL⟩ := h.re.posFacts
  have hlt := h.hlt
  have capE := h.capE
  have vin := h.vin
  have hhi := h.heap.hi
  simp only [rend] at hlt hpe hel capE ⊢
  obtain ⟨hP1, hP2⟩ := vin.buf.resolve_left (by omega)
  simp only [heapNext, heapEnd] at hP1 hP2 hhi
  have hlo0 := h.re.rb.rc.k.a.inv.heap.lo
  simp only [heapStart, heapNext] at hlo0
  have hpal := vin.al
  have hvp : t.getMem (msp + 456) = vecPtr t (msp + 448) := rfl
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b800007d4_spec hpc (by rv_eval [hsp, msp]; decide)
  have k₁ := b800007d4_keeps h₁
  have hm₁ := b800007d4_mem_same h₁
  have hsp₁ : t₁.getReg .x2 = msp := (k₁ .x2 (by decide)).trans hsp
  have x10₁ : t₁.getReg .x10 = vecPtr t (msp + 448) + BitVec.ofNat 64 (2 * st.positions.length) := by
    rw [b800007d4_x10 h₁, hsp, hvp, h.x23]
    apply BitVec.eq_of_toNat_eq
    addr_omega [hP2, capE, hlt, hhi]
  have x19₁ : t₁.getReg .x19 = vecPtr t (msp + 448) := by rw [b800007d4_x19 h₁, hsp, hvp]
  have R₁ : ∀ r ∈ ([.x2, .x8, .x9, .x12, .x15, .x18, .x20, .x21, .x23, .x24, .x27] : List Reg),
      t₁.getReg r = t.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact k₁ _ (by decide)
  have hX : (t.getReg .x24).toNat = (rfold words i L g st g.2.2.length).2.1 - st.positions.length := by
    rw [h.x24, BitVec.toNat_ofNat]; simp only [rend]; omega
  by_cases h2 : (rfold words i L g st g.2.2.length).2.1 - st.positions.length < 2
  · -- one new half: straight to its store
    have hpc₁ := b800007d4_pc_taken h₁ (by rw [hX]; show _ < 2; omega)
    refine ⟨t₁, r₁, Or.inr ⟨hpc₁, BFrame.of_same hm₁ _, fun j hj1 hj2 ↦ by omega, ?_, ?_,
      (R₁ .x12 (by simp)).trans h.x12, (R₁ .x15 (by simp)).trans h.x15, x19₁,
      fun r hr ↦ R₁ r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto)⟩⟩
    · rw [x10₁, show 2 * ((rfold words i L g st g.2.2.length).2.1 - 1) = 2 * st.positions.length by
        omega]
    · rw [(R₁ .x23 (by simp)).trans h.x23, show (rfold words i L g st g.2.2.length).2.1 - 1 =
        st.positions.length by omega]
  -- `memset`
  have hpc₁ := b800007d4_pc_not_taken h₁ (by rw [hX]; show 2 ≤ _; omega)
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b800007e8_spec hpc₁ trivial
  have k₂ := b800007e8_keeps h₂
  have hm₂ := b800007e8_mem_same h₂
  have x10₂ : t₂.getReg .x10 = vecPtr t (msp + 448) + BitVec.ofNat 64 (2 * st.positions.length) :=
    (k₂ .x10 (by decide)).trans x10₁
  have x12₂ : (t₂.getReg .x12).toNat =
      2 * ((rfold words i L g st g.2.2.length).2.1 - st.positions.length) - 2 := by
    rw [b800007e8_x12 h₂, (R₁ .x24 (by simp)), h.x24]
    simp only [rend]
    addr_omega [hlt, hel, hp31, hL, h2]
  have pre : MemsetPre t₂ := by
    show Mapped _ _
    rw [x10₂, x12₂]
    left
    constructor <;> addr_omega [hP1, hP2, hlo0, hlt, capE, hhi]
  obtain ⟨t₃, r₃, ⟨hpc₃, hpv, post⟩ | hd⟩ := memset.call r₂ (b800007e8_pc h₂) pre
  swap
  · exact ⟨t₃, r₁.trans r₃, Or.inl hd⟩
  have hpc₃' : t₃.pc = 0x80000800 := by rw [hpc₃, returnAddress, b800007e8_x1 h₂]; decide
  have hsp₃ : t₃.getReg .x2 = msp := (hpv.reg .x2).trans ((k₂ .x2 (by decide)).trans hsp₁)
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b80000800_spec hpc₃' (by rv_eval [hsp₃, msp]; decide)
  have k₄ := b80000800_keeps h₄
  have hm₄ := b80000800_mem_same h₄
  have pfr := post.frame
  have pby := post.bytes
  rw [x10₂, x12₂] at pfr
  rw [x10₂, x12₂, b800007e8_x11 h₂] at pby
  have hf : BFrame t t₄ (fun a ↦ Within a (vecPtr t (msp + 448) +
      BitVec.ofNat 64 (2 * st.positions.length))
      (2 * ((rfold words i L g st g.2.2.length).2.1 - st.positions.length) - 2)) := fun a ha ↦ by
    have e1 : byteAt t₄ a = byteAt t₃ a := by rw [byteAt_eq, byteAt_eq, hm₄]
    have e2 : byteAt t₂ a = byteAt t a := by rw [byteAt_eq, byteAt_eq, hm₂, hm₁]
    rw [e1, ← e2]
    exact pfr.byte a ha
  have m72 : t.getMem (msp + 72) = D := by
    rw [← h.re.rb.rc.m72]
    exact h.frame.getMem (by decide) fun j hj hw ↦ by
      rcases hw with hw | hw | hw | ⟨hw1, hw2⟩ | hw
      · addr_omega [hw, hj]
      · addr_omega [hw, hj]
      · addr_omega [hw, hj]
      · simp only [heapEnd] at hw2; addr_omega [hw2, hj]
      · have bp := h.re.vs.bufs.p
        have hh := h.re.rb.rc.k.ng.heap.hi
        rcases bp.buf with h0 | ⟨_, h2⟩
        · simp only [Within] at hw; omega
        · simp only [heapNext, heapEnd] at h2 hh; addr_omega [hw, hj, h2, hh]
  have x19₃ : t₃.getReg .x19 = vecPtr t (msp + 448) :=
    (hpv.reg .x19 (by decide)).trans ((k₂ .x19 (by decide)).trans x19₁)
  have R : ∀ r ∈ ([.x2, .x8, .x9, .x18, .x20, .x21, .x27] : List Reg), t₄.getReg r = t.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (k₄ _ (by decide)).trans ((hpv.reg _ (by decide)).trans ((k₂ _ (by decide)).trans
        (R₁ _ (by simp))))
  have x23₃ : t₃.getReg .x23 = BitVec.ofNat 64 st.positions.length :=
    (hpv.reg .x23 (by decide)).trans ((k₂ .x23 (by decide)).trans ((R₁ .x23 (by simp)).trans h.x23))
  have x24₃ : t₃.getReg .x24 = BitVec.ofNat 64 (rend words i L g st - st.positions.length) :=
    (hpv.reg .x24 (by decide)).trans ((k₂ .x24 (by decide)).trans ((R₁ .x24 (by simp)).trans h.x24))
  refine ⟨t₄, r₁.trans (r₃.trans r₄), Or.inr ⟨b80000800_pc h₄, hf, fun j hj1 hj2 ↦ ?_, ?_, ?_, ?_,
    ?_, by rw [k₄ .x19 (by decide), x19₃], R⟩⟩
  · rw [hm₄ |> fun hm ↦ (show byteAt t₄ _ = byteAt t₃ _ by rw [byteAt_eq, byteAt_eq, hm])]
    have e := List.getElem_of_eq pby (i := j - 2 * st.positions.length)
      (by rw [bytesAt_length]; omega)
    rw [bytesAt_getElem, List.getElem_replicate, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 2 * st.positions.length + (j - 2 * st.positions.length) = j by omega] at e
    rw [e]; rfl
  · rw [b80000800_x10 h₄, x19₃, x23₃, x24₃]
    apply BitVec.eq_of_toNat_eq
    simp only [rend]
    addr_omega [hP2, capE, hlt, hhi, hp31, hel, hL]
  · rw [b80000800_x23 h₄, x23₃, x24₃]
    apply BitVec.eq_of_toNat_eq
    simp only [rend]
    addr_omega [hlt, hel, hp31, hL]
  · rw [b80000800_x12 h₄, hsp₃]
    rw [show t₃.getMem (msp + 72) = t.getMem (msp + 72) from (pfr.getMem fun j hj hw ↦ by
      addr_omega [hw, hj, hP2, capE, hhi]).trans (by rw [hm₂, hm₁])]
    exact m72
  · rw [b80000800_x15 h₄, hpv.reg .x22 (by decide), b800007e8_x22 h₂, R₁ .x15 (by simp), h.x15]

end

section
variable {s u₀ t₀ t : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C N : Word} {H1 : Nat}

/-- `0x800007d4` to `0x8000082c`: the new halves zeroed. -/
theorem resize_fill (h : RZ s words u₀ i L Hb st g D C N H1 t₀ t) (hpc : t.pc = 0x800007d4) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨
      (v.pc = 0x8000082c ∧ RY s words u₀ i L Hb st g D C N H1 t₀ v)) := by
  obtain ⟨u, ru, hd | ⟨hpcu, hfu, hzu, x10u, x23u, x12u, x15u, x19u, Ru⟩⟩ := resize_pre h hpc
  · exact ⟨u, ru, Or.inl hd⟩
  obtain ⟨hpl, hp31, hpe, hel, hL⟩ := h.re.posFacts
  have hlt := h.hlt
  have capE := h.capE
  have vin := h.vin
  have hhi := h.heap.hi
  have hmo := h.mono
  simp only [rend] at hlt hpe hel capE x10u x23u hzu hfu ⊢
  obtain ⟨hP1, hP2⟩ := vin.buf.resolve_left (by omega)
  simp only [heapNext, heapEnd] at hP1 hP2 hhi hmo
  have hlo0 := h.re.rb.rc.k.a.inv.heap.lo
  simp only [heapStart, heapNext] at hlo0
  have hpal := vin.al
  -- `0x8000081c`: the last half
  have hf : Image.code.fetch u.pc = some (.base (.SH .x10 .x0 0)) := by
    rw [hpcu]; exact fetch_of (by decide +kernel)
  obtain ⟨u₁, hu₁, hpc₁, hr₁, hh₁, hf₁⟩ := step_sh hf (by
    rw [off0, x10u]
    exact valid2_of (by addr_omega [hP1, hlo0, hlt, capE, hP2, hhi])
      (by addr_omega [hP2, hlt, capE, hhi]) (by addr_omega [hpal, hP2, hlt, capE, hhi]))
  rw [off0, x10u] at hh₁ hf₁
  obtain ⟨v, rv, hv⟩ := Sym.BlockSpec.reaches NB.g80000820_spec (by rw [hpc₁, hpcu]; rfl) trivial
  have kv := NB.g80000820_keeps hv
  have hmv := NB.g80000820_mem_same hv
  -- the bytes written since `t`
  have hfv : BFrame t v fun a ↦ Within a (vecPtr t (msp + 448) +
      BitVec.ofNat 64 (2 * st.positions.length))
      (2 * ((rfold words i L g st g.2.2.length).2.1 - st.positions.length)) := fun a ha ↦ by
    have e1 : byteAt v a = byteAt u₁ a := by rw [byteAt_eq, byteAt_eq, hmv]
    rw [e1, hf₁.byte a fun h' ↦ ha (by rcases h' with h' | h' <;> rw [h'] <;>
      addr_omega [hP2, hlt, capE, hhi])]
    exact hfu a fun h' ↦ ha (by addr_omega [h', hP2, hlt, capE, hhi])
  have hWz : ∀ a, Within a (vecPtr t (msp + 448) + BitVec.ofNat 64 (2 * st.positions.length))
      (2 * ((rfold words i L g st g.2.2.length).2.1 - st.positions.length)) →
      Wz (heapNext t₀) (vecPtr t₀ (msp + 448)) ((vecCap t₀ (msp + 448)).toNat * 2) a := by
    intro a ha
    rcases h.sf with ⟨e1, e2⟩ | h0 | hfr
    · right; right; right; right
      rw [← e1, ← e2]; addr_omega [ha, hP2, hlt, capE, hhi]
    · omega
    · right; right; right; left
      simp only [heapNext, heapEnd] at hfr ⊢
      constructor <;> addr_omega [ha, hfr, hP2, hlt, capE, hhi]
  have hm : ∀ a : Word, a.toNat < (vecPtr t (msp + 448)).toNat ∨
      (vecPtr t (msp + 448)).toNat + 2 * (rfold words i L g st g.2.2.length).2.1 ≤ a.toNat →
      byteAt v a = byteAt t a :=
    fun a ha ↦ hfv a fun h' ↦ by addr_omega [h', ha, hP2, hlt, capE, hhi]
  have hK : ∀ c : Nat, c % 8 = 0 → c < 4096 → v.getMem (msp + BitVec.ofNat 64 c) =
      t.getMem (msp + BitVec.ofNat 64 c) := fun c h8 hc ↦
    getMem_eq_of_bytes (by addr_omega [h8, hc]) (by addr_omega [h8, hc]) fun j hj ↦
      hm _ (Or.inr (by addr_omega [hj, hc, hP2, hlt, capE, hhi]))
  have hn : heapNext v = heapNext t := by
    simp only [heapNext]
    rw [getMem_eq_of_bytes (by decide) (by decide) fun j hj ↦
      hm _ (Or.inr (by addr_omega [hj, hP2, hlt, capE, hhi]))]
  have p1 : vecPtr v (msp + 448) = vecPtr t (msp + 448) := hK 456 (by decide) (by decide)
  have c1 : vecCap v (msp + 448) = vecCap t (msp + 448) := hK 448 (by decide) (by decide)
  have l1 : vecLen v (msp + 448) = vecLen t (msp + 448) := hK 464 (by decide) (by decide)
  have R : ∀ r ∈ ([.x2, .x8, .x9, .x12, .x15, .x18, .x19, .x20, .x21] : List Reg),
      v.getReg r = u.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (kv _ (by decide)).trans (hr₁ _)
  refine ⟨v, ru.trans ((show Reaches Image.code u u₁ from ⟨1, hu₁⟩).trans rv), Or.inr ⟨NB.g80000820_pc hv,
    h.re, fun a ha ↦ by
      rw [hfv a fun h' ↦ ha (hWz a h')]; exact h.frame a ha,
    ⟨by rw [hn]; exact h.heap.lo, by rw [hn]; exact h.heap.hi⟩, by rw [hn]; exact h.mono,
    by rw [hn]; exact vin.keep c1 p1 l1 le_rfl, by rw [c1]; exact h.capE,
    by rw [p1, c1]; exact h.sf, ?_, (R .x2 (by simp)).trans ((Ru .x2 (by simp)).trans h.x2),
    (R .x8 (by simp)).trans ((Ru .x8 (by simp)).trans h.x8),
    (R .x9 (by simp)).trans ((Ru .x9 (by simp)).trans h.x9), (R .x12 (by simp)).trans x12u,
    (R .x15 (by simp)).trans x15u, (R .x18 (by simp)).trans ((Ru .x18 (by simp)).trans h.x18),
    by rw [R .x19 (by simp), x19u, p1], (R .x20 (by simp)).trans ((Ru .x20 (by simp)).trans h.x20),
    (R .x21 (by simp)).trans ((Ru .x21 (by simp)).trans h.x21), ?_⟩⟩
  · rw [p1]
    simp only [rend]
    refine resize_content h.pos hlt hpal (by omega)
      (fun j hj ↦ hfv _ fun h' ↦ by addr_omega [h', hj, hP2, hlt, capE, hhi]) (fun j hj1 hj2 ↦ ?_) ?_
    · have e1 : byteAt v (vecPtr t (msp + 448) + BitVec.ofNat 64 j) =
          byteAt u₁ (vecPtr t (msp + 448) + BitVec.ofNat 64 j) := by
        rw [byteAt_eq, byteAt_eq, hmv]
      rw [e1, hf₁.byte _ fun h' ↦ by
        rcases h' with h' | h' <;> have := congrArg BitVec.toNat h' <;>
          addr_omega [this, hj2, hP2, hlt, capE, hhi]]
      exact hzu j hj1 hj2
    · rw [getHalfword_same hmv, hh₁]; rfl
  · rw [NB.g80000820_x27 hv, hr₁, x23u]
    apply BitVec.eq_of_toNat_eq
    simp only [rend]
    addr_omega [hlt, hel, hp31, hL]

end

/-- The resize, from the runs' exit (`0x800007b8`) to `0x8000082c`. -/
theorem resize_phase {s u₀ t₀ : MachineState} {words : List Word} {i L Hb : Nat}
    {st : Model.NewState} {g : GrpSt} {D C N : Word} {H1 : Nat}
    (h : RE s words u₀ i L Hb st g D C N H1 t₀) (hpc : t₀.pc = 0x800007b8) :
    ∃ v, Reaches Image.code t₀ v ∧ (Dead Image.code v ∨
      (v.pc = 0x8000082c ∧ RY s words u₀ i L Hb st g D C N H1 t₀ v)) := by
  by_cases hle : rend words i L g st ≤ st.positions.length
  · obtain ⟨v, rv, hpcv, hv⟩ := resize_skip h hpc hle
    exact ⟨v, rv, Or.inr ⟨hpcv, hv⟩⟩
  obtain ⟨t, rt, hd | ⟨hpct, ht⟩⟩ := resize_room h hpc (by omega)
  · exact ⟨t, rt, Or.inl hd⟩
  obtain ⟨v, rv, hv⟩ := resize_fill ht hpct
  exact ⟨v, rt.trans rv, hv⟩

end Rv64Verifier.Proofs.Main
