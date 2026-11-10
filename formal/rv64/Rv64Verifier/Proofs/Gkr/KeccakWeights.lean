import Rv64Verifier.Proofs.Gkr.KeccakLanes
import Rv64Verifier.Proofs.Field.Contracts

/-!
# `keccak::verify_keccak`: the first claim's position weights

`(0..1600).map(|j| lanes[j / 64] * K(1 << (j % 64))).collect()`, compiled as a loop at
`0x80009044` that multiplies into `f + 1952` (`<E as Mul<K>>::mul`) and copies the product to the
buffer reserved at `f + 416`: `w_step` is one iteration, `w_loop` the loop.
-/

namespace Rv64Verifier.Gkr.Keccak
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F35 Rv64Verifier.FieldContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem kWeights_take_succ (lanes : List E) {j : Nat} (hj : j < 1600) :
    (kWeights lanes).take (j + 1) =
      (kWeights lanes).take j ++ [lanes.getD (j / 64) 0 * eNew (1#64 <<< (j % 64))] := by
  have hl : j < (kWeights lanes).length := by simp [kWeights, keccakBits, hj]
  rw [List.take_add_one, List.getElem?_eq_getElem hl]
  simp [kWeights]

theorem eListAt_succ (u : MachineState) (p : Word) (j : Nat) :
    eListAt u p (j + 1) = eListAt u p j ++ [eAt u (p + BitVec.ofNat 64 (24 * j))] := by
  simp only [eListAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem getD_eListAt' (u : MachineState) (p : Word) {n c : Nat} (hc : c < n) :
    (eListAt u p n).getD c 0 = eAt u (p + BitVec.ofNat 64 (24 * c)) := by
  rw [List.getD_eq_getElem _ _ (by rw [eListAt_length]; exact hc), eListAt_getElem]

/-- What the loop writes: the buffer, `mul`'s result at `f + 1952`, the stack below the frame. -/
@[rv_addr] def LWr (s : MachineState) (wp a : Word) : Prop :=
  Within a wp 38400 ∨ Within a (s.getReg .x2 - 3296) 24 ∨
    Within a (stackLo s verifyKeccakStack) openStack

/-- The loop's constants: the lanes' weights and the buffer, allocated since the entry. -/
structure WK (s u₀ : MachineState) (wp lptr : Word) (lanes : List E) : Prop where
  lanes : eListAt u₀ lptr 32 = lanes
  lp1 : heapNext s ≤ lptr.toNat
  lp2 : lptr.toNat + 768 ≤ wp.toNat ∨ wp.toNat + 38400 ≤ lptr.toNat
  lp3 : lptr.toNat + 768 ≤ heapNext u₀
  lp8 : lptr.toNat % 8 = 0
  wp1 : heapNext s ≤ wp.toNat
  wp2 : wp.toNat + 38400 ≤ heapNext u₀
  wp8 : wp.toNat % 8 = 0

/-- After `j` iterations. -/
structure WS (s u₀ u : MachineState) (wp lptr : Word) (lanes : List E) (j : Nat) : Prop where
  base : Base s u
  x8 : u.getReg .x8 = wp
  x10 : u.getReg .x10 = BitVec.ofNat 64 j
  x20 : u.getReg .x20 = 1600
  x21 : u.getReg .x21 = 32
  x22 : u.getReg .x22 = 1
  x25 : u.getReg .x25 = lptr
  x26 : u.getReg .x26 = BitVec.ofNat 64 j
  x27 : u.getReg .x27 = wp + BitVec.ofNat 64 (24 * j)
  regs : ∀ r ∈ ([.x18, .x19, .x23, .x24] : List Reg), u.getReg r = u₀.getReg r
  frame : DFrame u₀ u (LWr s wp)
  heapEq : heapNext u = heapNext u₀
  elems : eListAt u wp j = (kWeights lanes).take j

theorem lwr_kw {s u₀ v : MachineState} (hpre : VerifyKeccakPreW s) {wp lptr : Word}
    {lanes : List E} (K : WK s u₀ wp lptr lanes) (hv : heapNext v = heapNext u₀) (hH : HeapOk v)
    {a : Word}
    (h : LWr s wp a) : KW s v a ∧ ¬ Within a (s.getReg .x2 - 104) 104 := by
  have hb := bounds hpre
  have hab := hpre.stack.above
  have w1 := K.wp1
  have w2 := K.wp2
  have hhi := hH.hi
  simp only [LWr, KW, Fresh] at h ⊢
  unfold verifyKeccakStack at hb hab ⊢
  rcases h with h | h | h
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [h, w1], by addr_omega [h, w2, hv]⟩))),
      by addr_omega [h, hb, hab, hv, w2, hhi]⟩
  · exact ⟨Or.inr (Or.inr (Or.inl (by addr_omega [h, hb]))), by addr_omega [h, hb]⟩
  · exact ⟨Or.inr (Or.inr (Or.inl (by addr_omega [h, hb]))), by addr_omega [h, hb]⟩

theorem w_step (hMK : MulKSpec) {s u₀ u : MachineState} {wp lptr : Word} {lanes : List E} {j : Nat}
    (hpre : VerifyKeccakPreW s) (K : WK s u₀ wp lptr lanes) (hj : j < 1600)
    (hpc : u.pc = 0x80009044) (W : WS s u₀ u wp lptr lanes j) :
    ∃ v, Reaches Image.code u v ∧ ((v.pc = 0x80009044 ∧ j + 1 < 1600 ∧
      WS s u₀ v wp lptr lanes (j + 1)) ∨ (v.pc = 0x80009098 ∧ WS s u₀ v wp lptr lanes 1600) ∨
      Dead Image.code v) := by
  have hb := bounds hpre
  have B := W.base
  have hjn : (BitVec.ofNat 64 j).toNat = j := by rw [BitVec.toNat_ofNat]; omega
  have hsh : (BitVec.ofNat 64 j >>> 6).toNat = j / 64 := by
    rw [BitVec.toNat_ushiftRight, hjn, Nat.shiftRight_eq_div_pow]
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80009044_spec hpc trivial
  have pc₁ := b80009044_pc_not_taken h₁ (by
    rw [W.x10, W.x21, hsh, show (32 : Word).toNat = 32 from rfl]; omega)
  have k₁ := b80009044_keeps h₁
  have m₁ := b80009044_mem_same h₁
  have x11₁ := b80009044_x11 h₁
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000904c_spec pc₁ trivial
  have k₂ := b8000904c_keeps h₂
  have m₂ := b8000904c_mem_same h₂
  have x2₂ : u₂.getReg .x2 = s.getReg .x2 - 5248 :=
    (k₂ .x2 (by decide)).trans ((k₁ .x2 (by decide)).trans B.x2)
  have x10₂ : u₂.getReg .x10 = s.getReg .x2 - 3296 := by
    rw [b8000904c_x10 h₂, k₁ .x2 (by decide), B.x2]
    exact BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have x11₂ : u₂.getReg .x11 = lptr + BitVec.ofNat 64 (24 * (j / 64)) := by
    rw [b8000904c_x11 h₂, x11₁, k₁ .x25 (by decide), W.x25, W.x10, Open.mul24, hsh]
  have x12₂ : u₂.getReg .x12 = 1#64 <<< (j % 64) := by
    have := h₂.reg_eq .x12 rfl (v := u₁.getReg .x22 <<< ((u₁.getReg .x10).toNat % 64))
      (by rv_eval [])
    rw [this, k₁ .x22 (by decide), k₁ .x10 (by decide), W.x22, W.x10, hjn]; rfl
  have x9₂ : u₂.getReg .x9 = BitVec.ofNat 64 (j + 1) := by
    rw [b8000904c_x9 h₂, k₁ .x10 (by decide), W.x10]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hjn, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]
  -- the product
  have hN : heapNext u = heapNext u₀ := W.heapEq
  have hhi : heapNext u₀ ≤ heapEnd := by rw [← hN]; exact B.heap.hi
  have l1 := K.lp1
  have l2 := K.lp2
  have l3 := K.lp3
  have l8 := K.lp8
  have w1 := K.wp1
  have w2 := K.wp2
  have w8 := K.wp8
  have hlo := hpre.heap.lo
  have hab := hpre.stack.above
  have hrs := hpre.stack.rodata
  unfold verifyKeccakStack at hb hab hrs
  have hj64 : j / 64 < 32 := by omega
  have B₂ : Base s u₂ := (B.same ((k₁ .x2 (by decide)).trans B.x2) m₁).same x2₂ m₂
  have hst : RtStack u₂ mulKStack := hpre.stack.sub 5248 x2₂ (by unfold verifyKeccakStack; decide)
    (by decide) (by decide) (by decide) (by decide)
  have slo : stackLo u₂ mulKStack = s.getReg .x2 - 5408 := by
    simp only [stackLo, x2₂, mulKStack, baseMulStack]
    exact BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have hmk : MulKPre u₂ := {
    out := by rw [x10₂]; exact slot_vmr hpre (by decide) (by decide) (by decide)
    lhs := by
      rw [x11₂]
      exact Layer.heap_vmr (by addr_omega [l1, hlo, l3, hhi, hj64]) (by addr_omega [l3, hhi, hj64])
        (by addr_omega [l8, l3, hhi, hj64])
    stack := hst.toStackOk
    pool := poolOk_of_rodata (B₂.rodata hpre) (by rw [slo]; addr_omega [hb, hrs])
    outStack := by rw [x10₂, slo]; addr_omega [hb]
    lhsStack := by rw [x11₂, slo]; addr_omega [hb, l3, hhi, hj64, hab] }
  obtain ⟨t, hr₃, ⟨hpc₃, hpres₃, hpost₃⟩ | hd⟩ := hMK.call (hr₁.trans hr₂) (b8000904c_pc h₂) hmk
  swap
  · exact ⟨t, hr₃, Or.inr (Or.inr hd)⟩
  have x2₃ : t.getReg .x2 = s.getReg .x2 - 5248 := (hpres₃.reg .x2).trans x2₂
  have x27₃ : t.getReg .x27 = wp + BitVec.ofNat 64 (24 * j) := by
    rw [hpres₃.reg .x27, k₂ .x27 (by decide), k₁ .x27 (by decide), W.x27]
  have pv : eAt t (s.getReg .x2 - 3296) =
      lanes.getD (j / 64) 0 * eNew (1#64 <<< (j % 64)) := by
    have hv := hpost₃.value
    rw [x10₂, x11₂, x12₂] at hv
    rw [hv, ← K.lanes, getD_eListAt' _ _ hj64]
    congr 1
    have e1 : eAt u₂ (lptr + BitVec.ofNat 64 (24 * (j / 64))) =
        eAt u (lptr + BitVec.ofNat 64 (24 * (j / 64))) := by
      unfold eAt; simp only [m₂, m₁]
    rw [e1]
    refine W.frame.eAt fun i hi h ↦ ?_
    simp only [LWr] at h
    rcases h with h | h | h <;> addr_omega [h, hi, l2, l3, hhi, hj64, hb, hab]
  -- the copy into the buffer
  have hW : ValidMemRange wp 4800 := Layer.heap_vmr (by addr_omega [w1, hlo])
    (by addr_omega [w2, hhi]) w8
  obtain ⟨v, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80009070_spec
    (by rw [hpc₃, returnAddress_eq, b8000904c_x1 h₂]; decide) (by
      rv_eval [x2₃, x27₃]
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | valid_access hW [hj, w2, hhi]
        | addr_omega [hb, w2, hhi, hab, hj])
  have k₄ := b80009070_keeps h₄
  have x2₄ : v.getReg .x2 = s.getReg .x2 - 5248 := (k₄ .x2 (by decide)).trans x2₃
  have f₄ := b80009070_frame h₄ (by rw [x27₃]; addr_omega [w2, hhi, hj])
  rw [x27₃] at f₄
  have c0 := b80009070_m_x27_0 h₄
  have c8 := b80009070_m_x27_8 h₄
  have c16 := b80009070_m_x27_16 h₄
  simp only [x27₃, x2₃] at c0 c8 c16
  have ev : eAt v (wp + BitVec.ofNat 64 (24 * j)) = eAt t (s.getReg .x2 - 3296) := by
    refine eAt_congr ?_ ?_ ?_
    · exact c0.trans (congrArg t.getMem (BitVec.eq_of_toNat_eq (by addr_omega [hb])))
    · exact c8.trans (congrArg t.getMem (BitVec.eq_of_toNat_eq (by addr_omega [hb])))
    · exact c16.trans (congrArg t.getMem (BitVec.eq_of_toNat_eq (by addr_omega [hb])))
  -- what the iteration wrote
  have Fuv : DFrame u v fun a ↦ Within a (wp + BitVec.ofNat 64 (24 * j)) 24 ∨
      Within a (s.getReg .x2 - 3296) 24 ∨ Within a (stackLo s verifyKeccakStack) openStack := by
    intro a ha
    have n0 := ha 0 (by decide)
    rw [add_ofNat_zero] at n0
    rw [f₄ a fun h ↦ n0 (Or.inl h), hpost₃.frame a (by rw [x10₂]; exact fun h ↦ n0 (Or.inr (Or.inl h)))
      (by rw [slo]; exact fun h ↦ n0 (Or.inr (Or.inr (by addr_omega [h, hb])))), m₂, m₁]
  have Flw : DFrame u v (LWr s wp) := Fuv.mono fun a h ↦ by
    simp only [LWr]
    rcases h with h | h | h
    · exact Or.inl (by addr_omega [h, hj, w2, hhi])
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hNv : v.getMem nextAddr = u.getMem nextAddr := Flw _ fun i hi h ↦ by
    have hnx := hpre.stack.next
    unfold verifyKeccakStack at hnx
    simp only [LWr] at h
    rcases h with h | h | h <;> addr_omega [h, hi, w2, hhi, hb, hnx]
  have hv : heapNext v = heapNext u₀ := by rw [← hN]; simp only [heapNext, hNv]
  have hHv : HeapOk v := ⟨by rw [hv, ← hN]; exact B.heap.lo, by rw [hv]; exact hhi⟩
  have Bv := B.next hpre x2₄ hHv (le_of_eq (by rw [hv, hN])) Flw fun a h ↦ lwr_kw hpre K hv hHv h
  have chain (r : Reg) (h4 : r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13,
      .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x28, .x29, .x30,
      .x31] : List Reg)) (hc : r ∈ calleeSaved)
      (h2 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x13, .x14, .x15, .x16, .x17, .x18, .x19,
        .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg))
      (h1 : r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x12, .x13, .x14, .x15, .x16,
        .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30,
        .x31] : List Reg)) : v.getReg r = u.getReg r := by
    rw [k₄ r h4, hpres₃.reg r hc, k₂ r h2, k₁ r h1]
  have hS : WS s u₀ v wp lptr lanes (j + 1) := {
    base := Bv
    x8 := (chain .x8 (by decide) (by decide) (by decide) (by decide)).trans W.x8
    x10 := by rw [b80009070_x10 h₄, hpres₃.reg .x9, x9₂]
    x20 := (chain .x20 (by decide) (by decide) (by decide) (by decide)).trans W.x20
    x21 := (chain .x21 (by decide) (by decide) (by decide) (by decide)).trans W.x21
    x22 := (chain .x22 (by decide) (by decide) (by decide) (by decide)).trans W.x22
    x25 := (chain .x25 (by decide) (by decide) (by decide) (by decide)).trans W.x25
    x26 := by
      rw [b80009070_x26 h₄, hpres₃.reg .x26, k₂ .x26 (by decide), k₁ .x26 (by decide), W.x26]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, hjn, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]
    x27 := by
      rw [b80009070_x27 h₄, x27₃]
      exact BitVec.eq_of_toNat_eq (by addr_omega [w2, hhi, hj])
    regs := fun r hr ↦ by
      have hr' := W.regs r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        exact (chain _ (by decide) (by decide) (by decide) (by decide)).trans hr'
    frame := W.frame.trans Flw fun _ h ↦ h
    heapEq := hv
    elems := by
      rw [eListAt_succ, kWeights_take_succ lanes hj, ← W.elems, ev, pv]
      congr 1
      exact Fuv.eListAt fun i hi h ↦ by
        rcases h with h | h | h <;> addr_omega [h, hi, w2, hhi, hj, hb, hab] }
  have hx9 : t.getReg .x9 = BitVec.ofNat 64 (j + 1) := by rw [hpres₃.reg .x9, x9₂]
  have hx20 : t.getReg .x20 = 1600 := by
    rw [hpres₃.reg .x20, k₂ .x20 (by decide), k₁ .x20 (by decide), W.x20]
  by_cases hlt : j + 1 < 1600
  · refine ⟨v, hr₃.trans hr₄, Or.inl ⟨b80009070_pc_taken h₄ ?_, hlt, hS⟩⟩
    rw [hx9, hx20]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, show (1600 : Word).toNat = 1600 from rfl] at this
    omega
  · have e : j + 1 = 1600 := by omega
    rw [e] at hS
    refine ⟨v, hr₃.trans hr₄, Or.inr (Or.inl ⟨b80009070_pc_not_taken h₄ ?_, hS⟩)⟩
    rw [hx9, hx20, e]; rfl

theorem w_loop (hMK : MulKSpec) {s u₀ u : MachineState} {wp lptr : Word} {lanes : List E}
    (hpre : VerifyKeccakPreW s) (K : WK s u₀ wp lptr lanes) (hpc : u.pc = 0x80009044)
    (W : WS s u₀ u wp lptr lanes 0) : ∃ v, Reaches Image.code u v ∧
      ((v.pc = 0x80009098 ∧ WS s u₀ v wp lptr lanes 1600) ∨ Dead Image.code v) := by
  refine Reaches.loop (fun v ↦ ∃ j, j < 1600 ∧ v.pc = 0x80009044 ∧ WS s u₀ v wp lptr lanes j)
    (fun v ↦ 1600 - (v.getReg .x10).toNat) _ (fun v ⟨j, hj, hpc, W⟩ ↦ ?_) u ⟨0, by decide, hpc, W⟩
  obtain ⟨w, hr, ⟨hpc', hj', W'⟩ | X | hd⟩ := w_step hMK hpre K hj hpc W
  · refine Or.inr ⟨w, hr, ⟨j + 1, hj', hpc', W'⟩, ?_⟩
    rw [W.x10, W'.x10, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · exact Or.inl ⟨w, hr, Or.inl X⟩
  · exact Or.inl ⟨w, hr, Or.inr hd⟩

/-- The loop's writes miss the bytes from `sp - J` below `f + 1952`. -/
theorem lwr_slot {s : MachineState} (hpre : VerifyKeccakPreW s) {wp : Word} {J m : Nat}
    (hJ : J ≤ 5248) (hm : 3296 + m ≤ J) (hw : 0x20000000 ≤ wp.toNat)
    (hw2 : wp.toNat + 38400 ≤ heapEnd) : Misses (LWr s wp) (s.getReg .x2 - BitVec.ofNat 64 J) m := by
  intro y hy h
  have hb := bounds hpre
  have hab := hpre.stack.above
  unfold verifyKeccakStack at hb hab
  simp only [LWr] at h
  rcases h with h | h | h <;> addr_omega [h, hy, hb, hab, hJ, hm, hw, hw2]

theorem lwr_buf {s : MachineState} (hpre : VerifyKeccakPreW s) {wp p : Word} {n : Nat}
    (hp : p.toNat + n ≤ heapEnd) (hw : Apart p n wp 38400) : Misses (LWr s wp) p n := by
  intro y hy h
  have hb := bounds hpre
  have hab := hpre.stack.above
  unfold verifyKeccakStack at hb hab
  simp only [LWr] at h
  rcases h with h | h | h <;> addr_omega [h, hy, hb, hab, hp, hw]

theorem vec_lwr {s u v : MachineState} (hpre : VerifyKeccakPreW s) {wp : Word} {J : Nat}
    {xs : List E} (h : NewVecE s u (s.getReg .x2 - BitVec.ofNat 64 J) xs) (hJ : J ≤ 5248)
    (hm : 3296 + 24 ≤ J) (hw : 0x20000000 ≤ wp.toNat) (hw2 : wp.toNat + 38400 ≤ heapEnd)
    (hu : heapNext u ≤ heapEnd) (F : DFrame u v (LWr s wp)) (hN : heapNext u ≤ heapNext v)
    (hsep : Apart (vecPtr u (s.getReg .x2 - BitVec.ofNat 64 J))
      ((vecCap u (s.getReg .x2 - BitVec.ofNat 64 J)).toNat * 24) wp 38400) :
    NewVecE s v (s.getReg .x2 - BitVec.ofNat 64 J) xs := by
  have hb := bounds hpre
  have hbuf := h.buf
  simp only [NewBuf] at hbuf
  refine newVecE_step h F hN (lwr_slot hpre hJ hm hw hw2) (by addr_omega [hb, hJ]) ?_ hu
  rcases hbuf with ⟨-, h0 | hbuf⟩
  · intro y hy; simp only [Within, h0] at hy; omega
  · exact lwr_buf hpre (by omega) hsep

theorem M.lwr {s u v : MachineState} {seg : List E} (hpre : VerifyKeccakPreW s) (c : M s u seg)
    (B : Base s v) {wp : Word} (F : DFrame u v (LWr s wp)) (hN : heapNext u ≤ heapNext v)
    (hw : 0x20000000 ≤ wp.toNat) (hw2 : wp.toNat + 38400 ≤ heapEnd)
    (hsw : Apart (vecPtr u (s.getReg .x2 - 5168)) ((vecCap u (s.getReg .x2 - 5168)).toNat * 24)
      wp 38400)
    (hpw : Apart (vecPtr u (s.getReg .x2 - 5144)) ((vecCap u (s.getReg .x2 - 5144)).toNat * 24)
      wp 38400) : M s v seg := by
  have hb := bounds hpre
  have hu := c.base.heap.hi
  have km (J : Nat) (h1 : J ≤ 5248) (h2 : 3304 ≤ J) :
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 J) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 J) :=
    F _ ((lwr_slot hpre h1 (m := 8) (by omega) hw hw2).bytes (Nat.le_refl _) (Nat.le_refl _)
      (by addr_omega [hb, h1]))
  exact {
    base := B
    ok := c.ok
    m32 := (km 5216 (by decide) (by decide)).trans c.m32
    m40 := (km 5208 (by decide) (by decide)).trans c.m40
    m48 := (km 5200 (by decide) (by decide)).trans c.m48
    m56 := (km 5192 (by decide) (by decide)).trans c.m56
    m64 := (km 5184 (by decide) (by decide)).trans c.m64
    m72 := (km 5176 (by decide) (by decide)).trans c.m72
    segV := vec_lwr hpre c.segV (by decide) (by decide) hw hw2 hu F hN hsw
    segLen := c.segLen
    pointV := vec_lwr hpre c.pointV (by decide) (by decide) hw hw2 hu F hN hpw }

/-- The weights computed: back at `0x80009098`, their buffer at `f + 424`, `1600` long. -/
structure A6 (s u : MachineState) (seg lp : List E) : Prop extends M s u seg where
  pc : u.pc = 0x80009098
  x8 : u.getReg .x8 = u.getMem (s.getReg .x2 - 4824)
  x18 : u.getReg .x18 = s.getReg .x12
  x19 : u.getReg .x19 = 12
  x23 : u.getReg .x23 = vecPtr u (s.getReg .x2 - 5168)
  x24 : u.getReg .x24 = vecLen u (s.getReg .x2 - 5168)
  x21 : u.getReg .x21 = 32
  x25 : u.getReg .x25 = vecPtr u (s.getReg .x2 - 5120)
  x26 : u.getReg .x26 = 1600
  cap : u.getMem (s.getReg .x2 - 4832) = 1600
  wbuf : NewBuf s u (u.getMem (s.getReg .x2 - 4824)) 38400 8
  weights : eListAt u (u.getMem (s.getReg .x2 - 4824)) 1600 = kWeights (eqKernelRust lp)
  lanesV : NewVecE s u (s.getReg .x2 - 5120) (eqKernelRust lp)
  lpLen : lp.length = 5
  rest : Rest s u (kLanes (s.getReg .x12).toNat (instOf s) (outOf s) seg lp)

theorem to_weights (hMK : MulKSpec) {s u : MachineState} {seg lp : List E}
    (hpre : VerifyKeccakPreW s) (A : A5 s u seg lp) :
    ∃ v, Reaches Image.code u v ∧ (A6 s v seg lp ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have B := A.base
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000901c_spec A.pc (by
    rv_eval [B.x2]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b8000901c_keeps h₁
  have m₁ := b8000901c_mem_same h₁
  have B₁ := B.same ((k₁ .x2 (by decide)).trans B.x2) m₁
  have hN₁ : heapNext u₁ = heapNext u := by simp only [heapNext, m₁]
  have hlen := A.lanesV.elems
  have hll : (eqKernelRust lp).length = 32 := by
    rw [eqKernelRust_eq, eqKernel_length, A.lpLen]; rfl
  have hl32 : (vecLen u (s.getReg .x2 - 5120)).toNat = 32 := by
    rw [← hll, ← hlen, vecEs, eListAt_length]
  have hwb := A.wbuf
  have hlw := A.lanesW
  simp only [NewBuf] at hwb
  have hhi := B.heap.hi
  have hlo := hpre.heap.lo
  have hvl := A.lanesV.vec.len
  have hvb := A.lanesV.buf
  simp only [NewBuf] at hvb
  rw [hl32] at hvl
  have K : WK s u₁ (u.getMem (s.getReg .x2 - 4824)) (vecPtr u (s.getReg .x2 - 5120))
      (eqKernelRust lp) := {
    lanes := by
      rw [← hlen, vecEs, hl32]
      exact (DFrame.of_same m₁ (fun _ ↦ False)).eListAt fun _ _ h ↦ h
    lp1 := by omega
    lp2 := by simp only [Apart] at hlw; omega
    lp3 := by rw [hN₁]; omega
    lp8 := hvb.1
    wp1 := by omega
    wp2 := by rw [hN₁]; omega
    wp8 := hwb.1 }
  have x2₁ : u₁.getReg .x2 = s.getReg .x2 - 5248 := B₁.x2
  have a424 : s.getReg .x2 - 5248 + 424 = s.getReg .x2 - 4824 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have a432 : s.getReg .x2 - 5248 + 432 = s.getReg .x2 - 4816 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have a136 : s.getReg .x2 - 5248 + 136 = s.getReg .x2 - 5120 + 8 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have a144 : s.getReg .x2 - 5248 + 144 = s.getReg .x2 - 5120 + 16 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have hlen0 : u.getMem (s.getReg .x2 - 4816) = 0 := A.len
  have W₀ : WS s u₁ u₁ (u.getMem (s.getReg .x2 - 4824)) (vecPtr u (s.getReg .x2 - 5120))
      (eqKernelRust lp) 0 := {
    base := B₁
    x8 := by rw [b8000901c_x8 h₁, B.x2, a424]
    x10 := b8000901c_x10 h₁
    x20 := (k₁ .x20 (by decide)).trans A.x20
    x21 := by
      rw [b8000901c_x21 h₁, B.x2, a144]
      exact BitVec.eq_of_toNat_eq (by rw [show (vecLen u (s.getReg .x2 - 5120)) =
        u.getMem (s.getReg .x2 - 5120 + 16) from rfl] at hl32; rw [hl32]; rfl)
    x22 := b8000901c_x22 h₁
    x25 := by rw [b8000901c_x25 h₁, B.x2, a136]; rfl
    x26 := by rw [b8000901c_x26 h₁, B.x2, a432, hlen0]; rfl
    x27 := by rw [b8000901c_x27 h₁, B.x2, a424, a432, hlen0]; simp
    regs := fun _ _ ↦ rfl
    frame := DFrame.refl _ _
    heapEq := rfl
    elems := rfl }
  obtain ⟨v, hr₂, ⟨hpc₂, X⟩ | hd⟩ := w_loop hMK hpre K (b8000901c_pc h₁) W₀
  swap
  · exact ⟨v, hr₁.trans hr₂, Or.inr hd⟩
  have hw : 0x20000000 ≤ (u.getMem (s.getReg .x2 - 4824)).toNat := by
    simp only [heapStart] at hlo; omega
  have hw2 : (u.getMem (s.getReg .x2 - 4824)).toNat + 38400 ≤ heapEnd := by omega
  have km (J : Nat) (h1 : J ≤ 5248) (h2 : 3304 ≤ J) :
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 J) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 J) :=
    (X.frame _ ((lwr_slot hpre h1 (m := 8) (by omega) hw hw2).bytes (Nat.le_refl _)
      (Nat.le_refl _) (by addr_omega [hb, h1]))).trans (m₁ _)
  have M₁ : M s u₁ seg := A.toC.toM.step hpre x2₁ B₁.heap (le_of_eq hN₁.symm) (rs := [])
    (sp := false) (by decide) (by decide) (DFrame.of_same m₁ _)
  have hN₂ : heapNext u₁ ≤ heapNext v := le_of_eq (by rw [X.heapEq])
  have hwp : v.getMem (s.getReg .x2 - 4824) = u.getMem (s.getReg .x2 - 4824) :=
    km 4824 (by decide) (by decide)
  have hu₁ : ∀ a, vecPtr u₁ a = vecPtr u a ∧ vecCap u₁ a = vecCap u a := fun a ↦
    ⟨m₁ _, m₁ _⟩
  have hl₁ : NewVecE s u₁ (s.getReg .x2 - 5120) (eqKernelRust lp) :=
    Layer.newVecE_congr m₁ A.lanesV
  refine ⟨v, hr₁.trans hr₂, Or.inl { M₁.lwr hpre X.base X.frame hN₂ hw hw2
      (by rw [(hu₁ _).1, (hu₁ _).2]; exact A.segW) (by rw [(hu₁ _).1, (hu₁ _).2]; exact A.pointW) with
    pc := hpc₂
    x8 := by rw [X.x8, hwp]
    x18 := by rw [X.regs .x18 (by decide), k₁ .x18 (by decide), A.x18]
    x19 := by rw [X.regs .x19 (by decide), k₁ .x19 (by decide), A.x19]
    x23 := by
      rw [X.regs .x23 (by decide), k₁ .x23 (by decide), A.x23]
      simp only [vecPtr, seg8 hpre]; exact (km 5160 (by decide) (by decide)).symm
    x24 := by
      rw [X.regs .x24 (by decide), k₁ .x24 (by decide), A.x24]
      simp only [vecLen, seg16 hpre]; exact (km 5152 (by decide) (by decide)).symm
    x21 := X.x21
    x25 := by
      rw [X.x25]; simp only [vecPtr]
      rw [show s.getReg .x2 - 5120 + 8 = s.getReg .x2 - 5112 from
        BitVec.eq_of_toNat_eq (by addr_omega [hb])]
      exact (km 5112 (by decide) (by decide)).symm
    x26 := X.x26
    cap := (km 4832 (by decide) (by decide)).trans A.cap
    wbuf := by
      rw [hwp]; simp only [NewBuf, X.heapEq, hN₁]; exact ⟨hwb.1, Or.inr (hwb.2.resolve_left (by decide))⟩
    weights := by
      rw [hwp, X.elems]
      exact List.take_of_length_le (by simp [kWeights, keccakBits])
    lanesV := vec_lwr hpre hl₁ (by decide) (by decide) hw hw2 B₁.heap.hi X.frame hN₂
      (by rw [(hu₁ _).1, (hu₁ _).2]; exact A.lanesW)
    lpLen := A.lpLen
    rest := (A.rest.keep fun T hT ↦ Layer.transcriptAt_congr m₁ hT).keep fun T hT ↦
      B₁.tat hpre X.base.heap X.frame (fun a ha ↦ ⟨fun hW ↦ ?_,
        (lwr_kw hpre K (by rw [X.heapEq]) X.base.heap ha).1⟩) hT }⟩
  have hS := hpre.self.self
  have hss := hpre.selfStack
  obtain ⟨f1, -⟩ := hpre.selfFree
  unfold verifyKeccakStack at hss
  simp only [LWr] at ha
  rcases ha with h | h | h <;> addr_omega [h, hW, hS, hss, hb, f1, hwb, hw2]

end Rv64Verifier.Gkr.Keccak
