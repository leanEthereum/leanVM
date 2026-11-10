import Rv64Verifier.Proofs.Walk.Base12

/-!
# `walk`: `blocks` (R12), the columns that get a block

`blk c` is the filter over the first `c` columns (`keepB`: neither a `q_keccak` slot nor an output
lane, inlined as `c < 73 ∨ c = 87 ∨ 138 ≤ c`). `blkHead` allocates the `Vec` at `sp + 1728` with
column `0`; the loop at `0x80003968` (`Flt12 .. c`) pushes each kept column (`blkGrow`, `reserve(1)`
when full, and `blkStore`) or skips it (`blkSkip`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror
  Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The columns that get a block, as the compiled code tests them. -/
def keepB (c : Nat) : Bool := decide (c < 73) || decide (c = 87) || decide (138 ≤ c)

/-- The kept columns among the first `c`. -/
def blk (c : Nat) : List Nat := (List.range c).filter keepB

theorem blk_succ (c : Nat) : blk (c + 1) = blk c ++ (if keepB c then [c] else []) := by
  simp only [blk, List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]

theorem blk_length_le (c : Nat) : (blk c).length ≤ c :=
  (List.length_filter_le _ _).trans (by simp)

theorem blk_ne {c : Nat} (hc : 1 ≤ c) : blk c ≠ [] :=
  List.ne_nil_of_mem (List.mem_filter.mpr ⟨List.mem_range.mpr hc, rfl⟩)

theorem blk_getD_lt {c j : Nat} (hj : j < (blk c).length) :
    (blk (c + 1)).getD j 0 = (blk c).getD j 0 := by
  rw [blk_succ]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hj]

theorem blk_getD_last {c : Nat} (hk : keepB c = true) : (blk (c + 1)).getD (blk c).length 0 = c := by
  rw [blk_succ, hk]
  simp

theorem blk_length_succ {c : Nat} (hk : keepB c = true) : (blk (c + 1)).length = (blk c).length + 1 := by
  rw [blk_succ, hk]; simp

theorem blk_succ_skip {c : Nat} (hk : keepB c = false) : blk (c + 1) = blk c := by
  rw [blk_succ, hk]; simp

/-- At the filter loop: the first `c` columns filtered into the `Vec` at `sp + 1728`. -/
structure Flt12 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) (lo lo2 lo3 c : Nat) : Prop where
  base : Base12 OI s u A k R Q B lo lo2 lo3
  bv : WVec u (s.getReg .x2 - 928) lo3 (blk c)
  le : c ≤ 165
  pos : 1 ≤ c
  x24 : u.getReg .x24 = 165
  x25 : u.getReg .x25 = BitVec.ofNat 64 (blk c).length
  x18 : u.getReg .x18 = BitVec.ofNat 64 ((hts A).getD 5 0)
  x23 : u.getReg .x23 = BitVec.ofNat 64 (k - 4)
  x26 : u.getReg .x26 = BitVec.ofNat 64 ((hts A).getD 5 0 + 6)

theorem kapLen_six : kapLen 6 = 165 := by decide

set_option maxRecDepth 8192 in
/-- From `0x800031dc`: `alloc(8, 32)`, `blocks = [0]` (capacity four), to the loop at `c = 1`. -/
theorem blkHead (hAS : AllocSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s u : MachineState} {A : List E} {k : Nat} {R Q B : Word} {lo lo2 : Nat} (hpre : WalkPre s)
    (hpc : u.pc = 0x800031dc) (h : Lat11 OI s u A k R Q B lo lo2 6) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨ (t.pc = 0x80003968 ∧
      Flt12 OI s t A k R Q B lo lo2 (heapNext u) 1 ∧ t.getReg .x9 = BitVec.ofNat 64 1 ∧
      t.getReg .x10 = vecPtr t (s.getReg .x2 - 928) ∧ t.getReg .x8 = 73)) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have B0 := h.base12
  have I := h.keep.at11.base.inv
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := I.sp
  have x24 : u.getReg .x24 = 165 := by rw [h.x24, kapLen_six]; rfl
  have hlo := I.heap.lo
  simp only [heapStart] at hlo
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800031dc_spec hpc (by rv_eval [])
  have pc₁ := b800031dc_pc_not_taken h₁ (by rw [x24]; decide)
  have m₁ := b800031dc_mem_same h₁
  have k₁ := b800031dc_keeps h₁
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800031e0_spec pc₁ (by rv_eval [])
  have m₂ (a : Word) : u₂.getMem a = u.getMem a := by rw [b800031e0_mem_same h₂, m₁]
  have k₂ := b800031e0_keeps h₂
  have hn₂ : heapNext u₂ = heapNext u := by simp only [heapNext, m₂]
  have preA : AllocPre u₂ := ⟨⟨hn₂ ▸ I.heap.lo, hn₂ ▸ I.heap.hi⟩, by
    rw [b800031e0_x10 h₂]; decide⟩
  obtain ⟨t₂, hrt₂, ⟨hpct₂, hp₂, postA⟩ | hd⟩ :=
    hAS.call (Reaches.refl u₂) (b800031e0_pc h₂) preA
  swap
  · exact ⟨t₂, hr₁.trans (hr₂.trans hrt₂), Or.inl hd⟩
  have hal := postA.aligned
  have hab := postA.above
  have hnx := postA.next
  rw [b800031e0_x10 h₂] at hal
  rw [b800031e0_x11 h₂] at hnx
  have e8 : (8 : Word).toNat = 8 := rfl
  have e32 : (32 : Word).toNat = 32 := rfl
  rw [e8] at hal
  rw [e32] at hnx
  rw [hn₂] at hab
  set F := t₂.getReg .x10 with hF
  have hht₂ := postA.heap.hi
  simp only [heapEnd] at hht₂
  have hFhi : F.toNat + 32 ≤ 2013265920 := by rw [← hnx]; exact hht₂
  have mt₂ (a : Word) (ha : a ≠ nextAddr) : t₂.getMem a = u.getMem a := by rw [postA.mem a ha, m₂]
  have frA : Layout.DFrame u t₂ (Within · nextAddr 8) := fun a ha _ ↦
    mt₂ a fun he ↦ ha a ⟨le_refl _, by omega⟩ (by rw [he]; simp only [Within]; omega)
  have hnA : heapNext u ≤ heapNext t₂ := by rw [hnx]; omega
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 2656 := by
    rw [hp₂ .x2 (by decide), k₂ .x2 (by decide), k₁ .x2 (by decide)]; exact sp
  have B₂ := B0.keep hpre frA (fun a ha ↦ Or.inr (Or.inr (Or.inl ha))) postA.heap hnA
    (sp₂.trans sp.symm)
  have pc₂ : t₂.pc = 0x800031f0 := by rw [hpct₂, returnAddress_eq, b800031e0_x1 h₂]; decide
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800031f0_spec pc₂ (by rv_eval [])
  have pc₃ := b800031f0_pc_not_taken h₃ (fun he ↦ by
    have := congrArg BitVec.toNat he; rw [← hF] at this
    have h0 : (0 : Word).toNat = 0 := rfl
    omega)
  have m₃ := b800031f0_mem_same h₃
  have k₃ := b800031f0_keeps h₃
  have sp₃ : u₃.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₃ .x2 (by decide)]; exact sp₂
  have x10₃ : u₃.getReg .x10 = F := k₃ .x10 (by decide)
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800031f4_spec pc₃ (by
    rv_eval [sp₃, x10₃]
    simp only [Sym.validAccess_eight]
    and_intros <;> addr_omega [hb1, hb2, hb3, hal, hab, hFhi, hlo])
  have fr₄ : Layout.DFrame u₃ u₄ fun a ↦ Within a F 8 ∨ Within a (s.getReg .x2 - 928) 24 :=
    exL h₄ (by
      rv_eval [sp₃, x10₃]
      simp only [Within]
      and_intros <;> addr_omega [hb1, hal, hab, hFhi, hlo])
  have k₄ := b800031f4_keeps h₄
  have fr₄' : Layout.DFrame t₂ u₄ fun a ↦ Within a F 8 ∨ Within a (s.getReg .x2 - 928) 24 :=
    fun a ha hw8 ↦ (fr₄ a ha hw8).trans (m₃ a)
  have hn₄ : heapNext u₄ = heapNext t₂ := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr₄' nextAddr (fun y hy hw ↦ by
      simp only [Within, nextAddr] at hy hw
      rcases hw with hw | hw <;> addr_omega [hy, hw, hb1, hFhi]) (by decide))
  have hv₄ : HeapOk u₄ := ⟨hn₄ ▸ postA.heap.lo, hn₄ ▸ postA.heap.hi⟩
  have sp₄ : u₄.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₄ .x2 (by decide)]; exact sp₃
  have B₄ := B₂.keep hpre fr₄' (fun a ha ↦ by
      rcases ha with ha | ha
      · simp only [Within] at ha
        exact Or.inr (Or.inr (Or.inr ⟨by omega, by rw [hn₄, hnx]; omega⟩))
      · simp only [Within] at ha
        exact Or.inl (by simp only [Within]; omega)) hv₄ hn₄.ge (sp₄.trans sp₂.symm)
  have e1728 : u₃.getReg .x2 + 1728 = s.getReg .x2 - 928 := by
    rw [sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e1736 : u₃.getReg .x2 + 1736 = s.getReg .x2 - 928 + 8 := by
    rw [sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e1744 : u₃.getReg .x2 + 1744 = s.getReg .x2 - 928 + 16 := by
    rw [sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hc4 : vecCap u₄ (s.getReg .x2 - 928) = 4 := by
    simp only [vecCap]; rw [← e1728]; exact b800031f4_m_x2_1728 h₄
  have hp4 : vecPtr u₄ (s.getReg .x2 - 928) = F := by
    simp only [vecPtr]; rw [← e1736, b800031f4_m_x2_1736 h₄, x10₃]
  have hl4 : vecLen u₄ (s.getReg .x2 - 928) = 1 := by
    simp only [vecLen]; rw [← e1744]; exact b800031f4_m_x2_1744 h₄
  have bv₄ : WVec u₄ (s.getReg .x2 - 928) (heapNext u) (blk 1) := {
    ok := ⟨by
      simp only [RawVecOk, Buf, hc4, hp4]
      refine ⟨hal, Or.inr ⟨by simp only [heapStart]; omega, ?_⟩⟩
      rw [hn₄, hnx]; simp, by rw [hl4, hc4]; decide⟩
    fresh := by rw [hp4]; exact hab
    len := by rw [hl4]; rfl
    vals := fun j hj ↦ by
      have hj0 : j = 0 := by simp [blk, keepB] at hj; omega
      subst hj0
      rw [hp4, show F + BitVec.ofNat 64 (8 * 0) = F by simp, ← x10₃, b800031f4_m_x10_0 h₄]
      rfl }
  have pc₄ := b800031f4_pc_taken h₄ (by rw [k₃ .x24 (by decide), hp₂ .x24 (by decide),
    k₂ .x24 (by decide), k₁ .x24 (by decide), x24]; decide)
  obtain ⟨u₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80003958_spec pc₄ (by rv_eval [])
  obtain ⟨u₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80003964_spec (b80003958_pc h₅) (by rv_eval [])
  have m₆ (a : Word) : u₆.getMem a = u₄.getMem a := by
    rw [b80003964_mem_same h₆, b80003958_mem_same h₅]
  have k₅ := b80003958_keeps h₅
  have k₆ := b80003964_keeps h₆
  have rg (r : Reg) (hr : r ∈ ([.x2, .x18, .x23, .x24, .x26] : List Reg)) :
      u₆.getReg r = u.getReg r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [k₆ _ (by decide), k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide),
        hp₂ _ (by decide), k₂ _ (by decide), k₁ _ (by decide)]
  have hp6 : vecPtr u₆ (s.getReg .x2 - 928) = F := by simp only [vecPtr, m₆]; exact hp4
  refine ⟨u₆, hr₁.trans (hr₂.trans (hrt₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆))))),
    Or.inr ⟨b80003964_pc h₆, {
      base := B₄.same hpre m₆ (by rw [rg .x2 (by decide), sp₄, sp])
      bv := bv₄.keep (blk_ne (le_refl 1)) (Layout.DFrame.of_same m₆ fun _ ↦ False)
        (fun _ _ h ↦ h) (fun _ _ h ↦ h) (by addr_omega [hb1]) hv₄.hi
        (by simp only [heapNext, m₆]; exact le_refl _)
      le := by decide
      pos := le_refl 1
      x24 := by rw [rg .x24 (by decide)]; exact x24
      x25 := by rw [k₆ .x25 (by decide), b80003958_x25 h₅]; rfl
      x18 := by rw [rg .x18 (by decide)]; exact h.x18
      x23 := by rw [rg .x23 (by decide)]; exact h.x23
      x26 := by rw [rg .x26 (by decide)]; exact h.x26 }, ?_, ?_, ?_⟩⟩
  · rw [b80003964_x9 h₆, b80003958_x19 h₅]; rfl
  · rw [hp6, k₆ .x10 (by decide), k₅ .x10 (by decide), k₄ .x10 (by decide), x10₃]
  · rw [k₆ .x8 (by decide), b80003958_x8 h₅]

/-- At `0x800039b0`: room for column `c`. -/
structure Psh12 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) (lo lo2 lo3 c : Nat) : Prop where
  base : Base12 OI s u A k R Q B lo lo2 lo3
  bv : WVec u (s.getReg .x2 - 928) lo3 (blk c)
  room : (blk c).length < (vecCap u (s.getReg .x2 - 928)).toNat
  lt : c < 165
  pos : 1 ≤ c
  kp : keepB c = true
  x8 : u.getReg .x8 = 73
  x9 : u.getReg .x9 = BitVec.ofNat 64 c
  x10 : u.getReg .x10 = vecPtr u (s.getReg .x2 - 928)
  x19 : u.getReg .x19 = BitVec.ofNat 64 (c + 1)
  x24 : u.getReg .x24 = 165
  x25 : u.getReg .x25 = BitVec.ofNat 64 (blk c).length
  x18 : u.getReg .x18 = BitVec.ofNat 64 ((hts A).getD 5 0)
  x23 : u.getReg .x23 = BitVec.ofNat 64 (k - 4)
  x26 : u.getReg .x26 = BitVec.ofNat 64 ((hts A).getD 5 0 + 6)

set_option maxRecDepth 8192 in
/-- Room for a kept column: `reserve(1)` when the `Vec` is full. -/
theorem blkGrow (hRS : ReserveFreshSpec 0x8000d628 8 8)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState} {A : List E}
    {k : Nat} {R Q B : Word} {lo lo2 lo3 c : Nat} (hpre : WalkPre s) (hpc : u.pc = 0x80003990)
    (h : Flt12 OI s u A k R Q B lo lo2 lo3 c) (hc : c < 165) (hk : keepB c = true)
    (x9 : u.getReg .x9 = BitVec.ofNat 64 c) (x10 : u.getReg .x10 = vecPtr u (s.getReg .x2 - 928))
    (x8 : u.getReg .x8 = 73) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨
      (t.pc = 0x800039b0 ∧ Psh12 OI s t A k R Q B lo lo2 lo3 c)) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have Bs := h.base
  have I := Bs.k11.at11.base.inv
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := I.sp
  have hne := blk_ne h.pos
  obtain ⟨b1, b2, b3, b4⟩ := h.bv.bounds hne
  have hL := h.bv.len
  have hlb := blk_length_le c
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80003990_spec hpc (by
    rv_eval [sp]; simp only [Sym.validAccess_eight]; addr_omega [hb1, hb2, hb3])
  have m₁ := b80003990_mem_same h₁
  have k₁ := b80003990_keeps h₁
  have e1728 : u.getReg .x2 + 1728 = s.getReg .x2 - 928 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x19₁ : u₁.getReg .x19 = BitVec.ofNat 64 (c + 1) := by
    rw [b80003990_x19 h₁, x9]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; have : (1 : Word).toNat = 1 := rfl; omega
  have hlN : (BitVec.ofNat 64 (blk c).length).toNat = (blk c).length := by
    rw [BitVec.toNat_ofNat]; omega
  by_cases hfull : (blk c).length = (vecCap u (s.getReg .x2 - 928)).toNat
  · have pc₁ := b80003990_pc_not_taken h₁ (by
      rw [h.x25, e1728]; apply BitVec.eq_of_toNat_eq; rw [hlN]; exact hfull)
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000399c_spec pc₁ (by rv_eval [])
    have m₂ (a : Word) : u₂.getMem a = u.getMem a := by rw [b8000399c_mem_same h₂, m₁]
    have k₂ := b8000399c_keeps h₂
    have sp₂ : u₂.getReg .x2 = u.getReg .x2 := by rw [k₂ .x2 (by decide), k₁ .x2 (by decide)]
    have B₂ := Bs.same hpre m₂ sp₂
    have I₂ := B₂.k11.at11.base.inv
    have bv₂ := h.bv.keep hne (Layout.DFrame.of_same m₂ fun _ ↦ False) (fun _ _ h ↦ h)
      (fun _ _ h ↦ h) (by addr_omega [hb1]) I.heap.hi (by simp only [heapNext, m₂]; exact le_refl _)
    have x10₂ : u₂.getReg .x10 = s.getReg .x2 - 928 := by rw [b8000399c_x10 h₂, k₁ .x2 (by decide), e1728]
    have hab := hpre.stack.above
    have hx := hpre.stack.next
    rw [stackLo_eq] at hab hx
    rw [stack_eq] at hx
    simp only [heapEnd] at hab
    have pre : ReservePre 8 8 u₂ := {
      heap := I₂.heap
      self := by
        rw [x10₂]; exact validMemRange_of (by addr_omega [hb1, hb3]) (Or.inr ⟨by addr_omega [hb1],
          by addr_omega [hb1, hb2]⟩)
      vec := by rw [x10₂]; exact bv₂.ok
      stack := stk10 hpre I₂ (by decide) (by decide)
      selfFree := by
        rw [x10₂]; exact ⟨Or.inr (by addr_omega [hab, hb1]), by simp only [Apart]; addr_omega [hx, hb1]⟩
      selfStack := by rw [x10₂, stackLo_callee I₂]; simp only [Apart]; addr_omega [hb1] }
    obtain ⟨t, hr, ⟨hpct, hp, post, hsame⟩ | hd⟩ := hRS u₂ (b8000399c_pc h₂) pre
    swap
    · exact ⟨t, hr₁.trans (hr₂.trans hr), Or.inl hd⟩
    have pcap := post.cap
    have pvec := post.vec
    have plen := post.len
    have pbytes := post.bytes
    have pframe := post.frame
    have phv := post.heap
    have pmono := post.mono
    rw [x10₂, b8000399c_x11 h₂] at pcap
    rw [x10₂] at pvec plen pbytes pframe hsame
    have fr := pframe.dframe
    have hht := phv.hi
    have hl3 := B₂.lo3le
    simp only [heapEnd] at hht
    have hone : (1 : Word).toNat = 1 := rfl
    rw [hone] at pcap
    have B₃ := B₂.keep hpre fr (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (by simp only [Within] at ha ⊢; omega)
      · rw [stackLo_callee I₂] at ha
        exact Or.inr (Or.inl (by simp only [Within, reserveStack] at ha ⊢; addr_omega [ha, hb1]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · simp only [Fresh] at ha; exact Or.inr (Or.inr (Or.inr ⟨by omega, ha.2⟩))) phv pmono
      (hp .x2 (by decide))
    have hraw := pvec.raw
    simp only [RawVecOk, Buf] at hraw
    obtain ⟨c1, c2, c3, c4⟩ := bv₂.bounds hne
    have hL₂ := bv₂.len
    rw [hL₂] at pcap
    have hfr : lo3 ≤ (vecPtr t (s.getReg .x2 - 928)).toNat := by
      rcases hsame with ⟨e1, -⟩ | hnb
      · rw [e1]; exact bv₂.fresh
      · simp only [NewBuf] at hnb; rcases hnb.2 with h0 | h0 <;> omega
    have bv₃ : WVec t (s.getReg .x2 - 928) lo3 (blk c) := ⟨pvec, hfr, by rw [plen]; exact hL₂,
      fun j hj ↦ by
        rw [getMem_eq_of_bytesAt pbytes hraw.1 c1 (by omega) (by omega)]
        exact bv₂.vals j hj⟩
    obtain ⟨t₁, hrt₁, ht₁⟩ := Sym.BlockSpec.reaches b800039ac_spec
      (by rw [hpct, returnAddress_eq, b8000399c_x1 h₂]; decide) (by
        rv_eval [hp .x2 (by decide), sp₂, sp]; simp only [Sym.validAccess_eight]
        addr_omega [hb1, hb2, hb3])
    have mt₁ := b800039ac_mem_same ht₁
    have kt₁ := b800039ac_keeps ht₁
    have rg (r : Reg) (hr : r ∈ ([.x2, .x8, .x9, .x18, .x19, .x23, .x24, .x25, .x26] : List Reg)) :
        t₁.getReg r = u₁.getReg r := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rw [kt₁ _ (by decide), hp _ (by decide), k₂ _ (by decide)]
    have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₁ .x2 (by decide)]; exact sp
    have e1736 : t.getReg .x2 + 1736 = s.getReg .x2 - 928 + 8 := by
      rw [hp .x2 (by decide), sp₂, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    refine ⟨t₁, hr₁.trans (hr₂.trans (hr.trans hrt₁)), Or.inr ⟨b800039ac_pc ht₁, {
      base := B₃.same hpre mt₁ (kt₁ .x2 (by decide))
      bv := bv₃.keep hne (Layout.DFrame.of_same mt₁ fun _ ↦ False) (fun _ _ h ↦ h)
        (fun _ _ h ↦ h) (by addr_omega [hb1]) phv.hi (by simp only [heapNext, mt₁]; exact le_refl _)
      room := by simp only [vecCap, mt₁]; exact pcap
      lt := hc
      pos := h.pos
      kp := hk
      x8 := by rw [rg .x8 (by decide), k₁ .x8 (by decide)]; exact x8
      x9 := by rw [rg .x9 (by decide), k₁ .x9 (by decide)]; exact x9
      x10 := by rw [b800039ac_x10 ht₁, e1736]; simp only [vecPtr, mt₁]
      x19 := by rw [rg .x19 (by decide)]; exact x19₁
      x24 := by rw [rg .x24 (by decide), k₁ .x24 (by decide)]; exact h.x24
      x25 := by rw [rg .x25 (by decide), k₁ .x25 (by decide)]; exact h.x25
      x18 := by rw [rg .x18 (by decide), k₁ .x18 (by decide)]; exact h.x18
      x23 := by rw [rg .x23 (by decide), k₁ .x23 (by decide)]; exact h.x23
      x26 := by rw [rg .x26 (by decide), k₁ .x26 (by decide)]; exact h.x26 }⟩⟩
  · have pc₁ := b80003990_pc_taken h₁ (by
      rw [h.x25, e1728]; intro he; have := congrArg BitVec.toNat he; rw [hlN] at this
      exact hfull this)
    have hv₁ : heapNext u₁ = heapNext u := by simp only [heapNext, m₁]
    refine ⟨u₁, hr₁, Or.inr ⟨pc₁, {
      base := Bs.same hpre m₁ (k₁ .x2 (by decide))
      bv := h.bv.keep hne (Layout.DFrame.of_same m₁ fun _ ↦ False) (fun _ _ h ↦ h)
        (fun _ _ h ↦ h) (by addr_omega [hb1]) I.heap.hi hv₁.ge
      room := by
        have hr : (blk c).length < (vecCap u (s.getReg .x2 - 928)).toNat := lt_of_le_of_ne b4 hfull
        simp only [vecCap, m₁] at hr ⊢; exact hr
      lt := hc
      pos := h.pos
      kp := hk
      x8 := by rw [k₁ .x8 (by decide)]; exact x8
      x9 := by rw [k₁ .x9 (by decide)]; exact x9
      x10 := by rw [k₁ .x10 (by decide), x10]; simp only [vecPtr, m₁]
      x19 := x19₁
      x24 := by rw [k₁ .x24 (by decide)]; exact h.x24
      x25 := by rw [k₁ .x25 (by decide)]; exact h.x25
      x18 := by rw [k₁ .x18 (by decide)]; exact h.x18
      x23 := by rw [k₁ .x23 (by decide)]; exact h.x23
      x26 := by rw [k₁ .x26 (by decide)]; exact h.x26 }⟩⟩

theorem Flt12.same {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {R Q B : Word} {lo lo2 lo3 c : Nat} (hpre : WalkPre s)
    (h : Flt12 OI s u A k R Q B lo lo2 lo3 c) (hm : ∀ a, v.getMem a = u.getMem a)
    (hr : ∀ r ∈ ([.x2, .x18, .x23, .x24, .x25, .x26] : List Reg), v.getReg r = u.getReg r) :
    Flt12 OI s v A k R Q B lo lo2 lo3 c := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  exact {
    base := h.base.same hpre hm (hr .x2 (by decide))
    bv := h.bv.keep (blk_ne h.pos) (Layout.DFrame.of_same hm fun _ ↦ False) (fun _ _ h ↦ h)
      (fun _ _ h ↦ h) (by addr_omega [hb1]) h.base.k11.at11.base.inv.heap.hi
      (by simp only [heapNext, hm]; exact le_refl _)
    le := h.le
    pos := h.pos
    x24 := by rw [hr .x24 (by decide)]; exact h.x24
    x25 := by rw [hr .x25 (by decide)]; exact h.x25
    x18 := by rw [hr .x18 (by decide)]; exact h.x18
    x23 := by rw [hr .x23 (by decide)]; exact h.x23
    x26 := by rw [hr .x26 (by decide)]; exact h.x26 }

/-- Where the filter loop goes after column `c`. -/
def Next12 (OI : MachineState → Word → List (List Opening) → Prop) (s t : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) (lo lo2 lo3 c : Nat) : Prop :=
  (c + 1 < 165 ∧ t.pc = 0x80003968 ∧ Flt12 OI s t A k R Q B lo lo2 lo3 (c + 1) ∧
    t.getReg .x9 = BitVec.ofNat 64 (c + 1) ∧ t.getReg .x10 = vecPtr t (s.getReg .x2 - 928) ∧
    t.getReg .x8 = 73) ∨
  (c + 1 = 165 ∧ t.pc = 0x80003210 ∧ Flt12 OI s t A k R Q B lo lo2 lo3 165)

theorem ofNat_succ' (n : Nat) : BitVec.ofNat 64 n + 1 = BitVec.ofNat 64 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have : (1 : Word).toNat = 1 := rfl
  omega

set_option maxRecDepth 8192 in
/-- Column `c` stored, the length stored, the loop's latch. -/
theorem blkStore {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q B : Word} {lo lo2 lo3 c : Nat} (hpre : WalkPre s)
    (hpc : u.pc = 0x800039b0) (h : Psh12 OI s u A k R Q B lo lo2 lo3 c) :
    ∃ t, Reaches Image.code u t ∧ Next12 OI s t A k R Q B lo lo2 lo3 c := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have Bs := h.base
  have I := Bs.k11.at11.base.inv
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := I.sp
  have hne := blk_ne h.pos
  obtain ⟨P, hP⟩ : ∃ P, vecPtr u (s.getReg .x2 - 928) = P := ⟨_, rfl⟩
  obtain ⟨b1, b2, b3, b4⟩ := h.bv.bounds hne
  rw [hP] at b1 b2 b3
  have hlb := blk_length_le c
  have room := h.room
  have hhu := I.heap.hi
  have fr0 := h.bv.fresh
  rw [hP] at fr0
  have hl3 := Bs.lo3le
  have hc := h.lt
  simp only [heapEnd, heapStart] at hhu b2
  have x10 : u.getReg .x10 = P := h.x10.trans hP
  have hD : (P + BitVec.ofNat 64 (8 * (blk c).length)).toNat = P.toNat + 8 * (blk c).length := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have eA : u.getReg .x10 + u.getReg .x25 * 8 = P + BitVec.ofNat 64 (8 * (blk c).length) := by
    rw [x10, h.x25, ofNat_mul8]
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800039b0_spec hpc (by
    rv_eval [sp, x10, h.x25, ofNat_mul8]; simp only [Sym.validAccess_eight]
    and_intros <;> addr_omega [hb1, hb2, hb3, hD, b1, b2, b3, room, hhu])
  have fr₁ : Layout.DFrame u u₁ fun a ↦ Within a (s.getReg .x2 - 912) 8 ∨
      Within a (P + BitVec.ofNat 64 (8 * (blk c).length)) 8 :=
    exL h₁ (by
      rv_eval [sp, x10, h.x25, ofNat_mul8]; simp only [Within]
      and_intros <;> addr_omega [hb1, hD, b2, b3, room, hhu])
  have k₁ := b800039b0_keeps h₁
  have hn₁ : heapNext u₁ = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr₁ nextAddr (fun y hy hw ↦ by
      simp only [Within, nextAddr] at hy hw
      rcases hw with hw | hw <;> addr_omega [hy, hw, hb1, hD, b2, b3, room, hhu]) (by decide))
  have hv₁ : HeapOk u₁ := ⟨hn₁ ▸ I.heap.lo, hn₁ ▸ I.heap.hi⟩
  have B₁ := Bs.keep hpre fr₁ (fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl (by simp only [Within] at ha ⊢; addr_omega [ha, hb1])
      · simp only [Within] at ha
        exact Or.inr (Or.inr (Or.inr ⟨by omega, by rw [hn₁]; omega⟩))) hv₁ hn₁.ge (k₁ .x2 (by decide))
  have g (o : Nat) (ho : o + 8 ≤ 16) : u₁.getMem (s.getReg .x2 - 928 + BitVec.ofNat 64 o) =
      u.getMem (s.getReg .x2 - 928 + BitVec.ofNat 64 o) :=
    fr₁.getMem_of (fun x hx hw' ↦ by
      simp only [Within] at hx hw'
      rcases hw' with h2 | h2 <;> addr_omega [hx, h2, hb1, hD, b2, b3, hhu, ho, room])
      (by addr_omega [ho, hb1])
  have hC₁ : vecCap u₁ (s.getReg .x2 - 928) = vecCap u (s.getReg .x2 - 928) := by
    simpa [vecCap] using g 0 (by decide)
  have hP₁ : vecPtr u₁ (s.getReg .x2 - 928) = P := by rw [← hP]; exact g 8 (by decide)
  have e1744 : u.getReg .x2 + 1744 = s.getReg .x2 - 928 + 16 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hl₁ : vecLen u₁ (s.getReg .x2 - 928) = BitVec.ofNat 64 ((blk c).length + 1) := by
    simp only [vecLen]; rw [← e1744, b800039b0_m_x2_1744 h₁, h.x25, ofNat_succ']
  have hlen1 := blk_length_succ h.kp
  have hraw := h.bv.ok.raw
  simp only [RawVecOk, Buf, hP] at hraw
  have bv₁ : WVec u₁ (s.getReg .x2 - 928) lo3 (blk (c + 1)) := {
    ok := ⟨by simp only [RawVecOk, Buf, hC₁, hP₁, hn₁]; exact hraw, by
      rw [hl₁, hC₁, BitVec.toNat_ofNat]; omega⟩
    fresh := by rw [hP₁]; exact fr0
    len := by rw [hl₁, hlen1, BitVec.toNat_ofNat]; omega
    vals := fun j hj ↦ by
      rw [hlen1] at hj
      rw [hP₁]
      by_cases hjL : j < (blk c).length
      · rw [fr₁.getMem_of (fun x hx hw' ↦ by
            simp only [Within] at hx hw'
            rcases hw' with h2 | h2 <;> addr_omega [hx, h2, hb1, hD, b2, b3, hhu, hjL, room])
          (by addr_omega [b2, b3, hhu, hjL, room]), blk_getD_lt hjL, ← hP]
        exact h.bv.vals j hjL
      · have hj' : j = (blk c).length := by omega
        subst hj'
        have := b800039b0_m1 h₁
        rw [eA, h.x9] at this
        rw [show 8 * (blk c).length = 8 * (blk c).length from rfl, this, blk_getD_last h.kp] }
  have x25₁ : u₁.getReg .x25 = BitVec.ofNat 64 (blk (c + 1)).length := by
    rw [b800039b0_x25 h₁, h.x25, hlen1, ofNat_succ']
  have F₁ : Flt12 OI s u₁ A k R Q B lo lo2 lo3 (c + 1) := {
    base := B₁
    bv := bv₁
    le := by omega
    pos := by omega
    x24 := by rw [k₁ .x24 (by decide)]; exact h.x24
    x25 := x25₁
    x18 := by rw [k₁ .x18 (by decide)]; exact h.x18
    x23 := by rw [k₁ .x23 (by decide)]; exact h.x23
    x26 := by rw [k₁ .x26 (by decide)]; exact h.x26 }
  have x19 := h.x19
  have x24 := h.x24
  have hc1 : (BitVec.ofNat 64 (c + 1)).toNat = c + 1 := by rw [BitVec.toNat_ofNat]; omega
  by_cases h165 : c + 1 = 165
  · have pc₁ := b800039b0_pc_not_taken h₁ (by rw [x19, x24, hc1]; show 165 ≤ c + 1; omega)
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800039c8_spec pc₁ (by rv_eval [])
    have k₂ := b800039c8_keeps h₂
    rw [h165] at F₁
    exact ⟨u₂, hr₁.trans hr₂, Or.inr ⟨h165, b800039c8_pc h₂,
      F₁.same hpre (b800039c8_mem_same h₂) fun r hr ↦ k₂ r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)⟩⟩
  · have pc₁ := b800039b0_pc_taken h₁ (by rw [x19, x24, hc1]; show c + 1 < 165; omega)
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80003964_spec pc₁ (by rv_eval [])
    have k₂ := b80003964_keeps h₂
    have m₂ := b80003964_mem_same h₂
    refine ⟨u₂, hr₁.trans hr₂, Or.inl ⟨by omega, b80003964_pc h₂,
      F₁.same hpre m₂ fun r hr ↦ k₂ r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide), ?_, ?_, ?_⟩⟩
    · rw [b80003964_x9 h₂, k₁ .x19 (by decide), x19]
    · rw [k₂ .x10 (by decide), k₁ .x10 (by decide), x10]; simp only [vecPtr, m₂]; exact hP₁.symm
    · rw [k₂ .x8 (by decide), k₁ .x8 (by decide)]; exact h.x8

theorem b8000396c_pc_of {s t : MachineState} (h : b8000396c.Holds s t) {c : Nat} (hc : c < 165)
    (h73 : 73 ≤ c) (x9 : s.getReg .x9 = BitVec.ofNat 64 c) :
    t.pc = if c = 87 ∨ 138 ≤ c then 0x80003990 else 0x80003984 := by
  apply h.pc_eq; rv_eval [x9]; interval_cases c <;> decide

set_option maxRecDepth 8192 in
/-- Column `c` of the filter loop. -/
theorem blkStep (hRS : ReserveFreshSpec 0x8000d628 8 8)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState} {A : List E}
    {k : Nat} {R Q B : Word} {lo lo2 lo3 c : Nat} (hpre : WalkPre s) (hpc : u.pc = 0x80003968)
    (h : Flt12 OI s u A k R Q B lo lo2 lo3 c) (hc : c < 165)
    (x9 : u.getReg .x9 = BitVec.ofNat 64 c) (x10 : u.getReg .x10 = vecPtr u (s.getReg .x2 - 928))
    (x8 : u.getReg .x8 = 73) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨ Next12 OI s t A k R Q B lo lo2 lo3 c) := by
  have push : ∀ v, Reaches Image.code u v → v.pc = 0x80003990 →
      Flt12 OI s v A k R Q B lo lo2 lo3 c → v.getReg .x9 = BitVec.ofNat 64 c →
      v.getReg .x10 = vecPtr v (s.getReg .x2 - 928) → v.getReg .x8 = 73 → keepB c = true →
      ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨ Next12 OI s t A k R Q B lo lo2 lo3 c) := by
    intro v hrv hpcv hv x9v x10v x8v hk
    obtain ⟨t₁, hrt₁, hd | ⟨hpct₁, ht₁⟩⟩ := blkGrow hRS hpre hpcv hv hc hk x9v x10v x8v
    · exact ⟨t₁, hrv.trans hrt₁, Or.inl hd⟩
    obtain ⟨t₂, hrt₂, ht₂⟩ := blkStore hpre hpct₁ ht₁
    exact ⟨t₂, hrv.trans (hrt₁.trans hrt₂), Or.inr ht₂⟩
  have lst : ∀ r ∈ ([.x2, .x18, .x23, .x24, .x25, .x26] : List Reg),
      r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x13, .x14, .x15, .x16, .x17, .x18,
        .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg) := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80003968_spec hpc (by rv_eval [])
  have m₁ := b80003968_mem_same h₁
  have k₁ := b80003968_keeps h₁
  have F₁ := h.same hpre m₁ fun r _ ↦ k₁ r (by revert r; decide)
  have hcN : (BitVec.ofNat 64 c).toNat = c := by rw [BitVec.toNat_ofNat]; omega
  have h73 : (73 : Word).toNat = 73 := rfl
  have x9₁ : u₁.getReg .x9 = BitVec.ofNat 64 c := by rw [k₁ .x9 (by decide)]; exact x9
  have x10₁ : u₁.getReg .x10 = vecPtr u₁ (s.getReg .x2 - 928) := by
    rw [k₁ .x10 (by decide), x10]; simp only [vecPtr, m₁]
  have x8₁ : u₁.getReg .x8 = 73 := by rw [k₁ .x8 (by decide)]; exact x8
  by_cases hlt : c < 73
  · exact push u₁ hr₁ (b80003968_pc_taken h₁ (by rw [x9, x8, hcN, h73]; exact hlt)) F₁ x9₁ x10₁
      x8₁ (by simp [keepB, hlt])
  have pc₁ := b80003968_pc_not_taken h₁ (by rw [x9, x8, hcN, h73]; omega)
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000396c_spec pc₁ (by rv_eval [])
  have hpc₂ := b8000396c_pc_of h₂ hc (by omega) x9₁
  have m₂ := b8000396c_mem_same h₂
  have k₂ := b8000396c_keeps h₂
  have F₂ := F₁.same hpre m₂ fun r hr ↦ k₂ r (lst r hr)
  have x9₂ : u₂.getReg .x9 = BitVec.ofNat 64 c := by rw [k₂ .x9 (by decide)]; exact x9₁
  have x10₂ : u₂.getReg .x10 = vecPtr u₂ (s.getReg .x2 - 928) := by
    rw [k₂ .x10 (by decide), x10₁]; simp only [vecPtr, m₂]
  have x8₂ : u₂.getReg .x8 = 73 := by rw [k₂ .x8 (by decide)]; exact x8₁
  split_ifs at hpc₂ with hk
  · exact push u₂ (hr₁.trans hr₂) hpc₂ F₂ x9₂ x10₂ x8₂ (by simp only [keepB]; simp; omega)
  have hkb : keepB c = false := by simp only [keepB]; simp; omega
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80003984_spec hpc₂ (by rv_eval [])
  have m₃ := b80003984_mem_same h₃
  have k₃ := b80003984_keeps h₃
  have F₃ := F₂.same hpre m₃ fun r hr ↦ k₃ r (by revert r hr; decide)
  have F₃' : Flt12 OI s u₃ A k R Q B lo lo2 lo3 (c + 1) := {
    base := F₃.base
    bv := by rw [blk_succ_skip hkb]; exact F₃.bv
    le := by omega
    pos := by omega
    x24 := F₃.x24
    x25 := by rw [blk_succ_skip hkb]; exact F₃.x25
    x18 := F₃.x18
    x23 := F₃.x23
    x26 := F₃.x26 }
  have x24₂ : u₂.getReg .x24 = 165 := F₂.x24
  by_cases h165 : c + 1 = 165
  · have pc₃ := b80003984_pc_not_taken h₃ (by rw [x24₂, x9₂, ofNat_succ', h165]; rfl)
    obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000398c_spec pc₃ (by rv_eval [])
    have k₄ := b8000398c_keeps h₄
    rw [h165] at F₃'
    exact ⟨u₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr (Or.inr ⟨h165, b8000398c_pc h₄,
      F₃'.same hpre (b8000398c_mem_same h₄) fun r hr ↦ k₄ r (by revert r hr; decide)⟩)⟩
  · have pc₃ := b80003984_pc_taken h₃ (by
      rw [x24₂, x9₂, ofNat_succ']; intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat] at this
      have h165' : (165 : Word).toNat = 165 := rfl
      rw [h165'] at this; omega)
    refine ⟨u₃, hr₁.trans (hr₂.trans hr₃), Or.inr (Or.inl ⟨by omega, pc₃, F₃', ?_, ?_, ?_⟩)⟩
    · rw [b80003984_x9 h₃, x9₂, ofNat_succ']
    · rw [k₃ .x10 (by decide), x10₂]; simp only [vecPtr, m₃]
    · rw [k₃ .x8 (by decide)]; exact x8₂

/-- The filter loop, from column `c` on. -/
theorem blkLoop (hRS : ReserveFreshSpec 0x8000d628 8 8)
    {OI : MachineState → Word → List (List Opening) → Prop} {s : MachineState} {A : List E}
    {k : Nat} {R Q B : Word} {lo lo2 lo3 : Nat} (hpre : WalkPre s) :
    ∀ d c u, 165 - c = d → u.pc = 0x80003968 → Flt12 OI s u A k R Q B lo lo2 lo3 c → c < 165 →
      u.getReg .x9 = BitVec.ofNat 64 c → u.getReg .x10 = vecPtr u (s.getReg .x2 - 928) →
      u.getReg .x8 = 73 → ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨
        (t.pc = 0x80003210 ∧ Flt12 OI s t A k R Q B lo lo2 lo3 165)) := by
  intro d
  induction d with
  | zero => intro c u hd _ _ hc; omega
  | succ d ih =>
    intro c u hd hpc h hc x9 x10 x8
    obtain ⟨t, hr, hd' | ⟨hc1, hpct, ht, x9t, x10t, x8t⟩ | ⟨-, hpct, ht⟩⟩ :=
      blkStep hRS hpre hpc h hc x9 x10 x8
    · exact ⟨t, hr, Or.inl hd'⟩
    · obtain ⟨t', hr', ht'⟩ := ih (c + 1) t (by omega) hpct ht hc1 x9t x10t x8t
      exact ⟨t', hr.trans hr', ht'⟩
    · exact ⟨t, hr, Or.inr ⟨hpct, ht⟩⟩

/-- R12's filter: from `0x800031dc` to `0x80003210`, `blocks` built. -/
theorem blkFilter (hAS : AllocSpec) (hRS : ReserveFreshSpec 0x8000d628 8 8)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState} {A : List E}
    {k : Nat} {R Q B : Word} {lo lo2 : Nat} (hpre : WalkPre s) (hpc : u.pc = 0x800031dc)
    (h : Lat11 OI s u A k R Q B lo lo2 6) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨
      (t.pc = 0x80003210 ∧ Flt12 OI s t A k R Q B lo lo2 (heapNext u) 165)) := by
  obtain ⟨v, hr, hd | ⟨hpcv, hv, x9, x10, x8⟩⟩ := blkHead hAS hpre hpc h
  · exact ⟨v, hr, Or.inl hd⟩
  obtain ⟨t, hrt, ht⟩ := blkLoop hRS hpre _ 1 v rfl hpcv hv (by decide) x9 x10 x8
  exact ⟨t, hr.trans hrt, ht⟩

end Rv64Verifier.Proofs.Walk
