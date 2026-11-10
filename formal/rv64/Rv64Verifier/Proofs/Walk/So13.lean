import Rv64Verifier.Proofs.Walk.Pl13
import Rv64Verifier.Proofs.Multilinear.StackOffsets

/-!
# `walk`: `stack_offsets(block_kappas)` (R13)

`soCall`: from `0x800032b8` (`AtR13`) through `stack_offsets`, to `0x800032c4` (`So13`): its
result `(Vec<u64>, usize)` at `sp + 1728`, the stacked offsets `sol K` in a new buffer `SO`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror
  Rv64Verifier.Blocks.F4 Rv64Verifier.MultilinearContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The stacked offsets. -/
abbrev sol (K : List Nat) : List Word := (stackOffsetsRust (bkl K)).1

theorem stackOffsetsRust_length (sizes : List Nat) : (stackOffsetsRust sizes).1.length = sizes.length := by
  unfold stackOffsetsRust
  simp only
  generalize (List.range (sizes.foldl max 0 + 1)).reverse = l
  suffices ∀ st : List Word × Word, st.1.length = sizes.length →
      (l.foldl (stackPass sizes) st).1.length = sizes.length from this _ (List.length_replicate ..)
  induction l with
  | nil => intro st h; exact h
  | cons x l ih =>
    intro st h
    refine ih _ ?_
    unfold stackPass
    generalize List.range sizes.length = m
    induction m generalizing st with
    | nil => exact h
    | cons y m ihm =>
      refine ihm _ ?_
      unfold stackStep
      split_ifs <;> simp [h]

theorem bkl_length (K : List Nat) : (bkl K).length = 101 := by simp [bkl, blk_165_length]

/-- After `stack_offsets`, at `0x800032c4`. -/
structure So13 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) (lo lo2 lo3 : Nat) (G SO : Word) : Prop where
  base : Base12 OI s u A k R Q B lo lo2 lo3
  gal : G.toNat % 8 = 0
  glo : lo3 ≤ G.toNat
  ghi : G.toNat + 808 ≤ SO.toNat
  gvals : ∀ i < 101, u.getMem (G + BitVec.ofNat 64 (8 * i)) = BitVec.ofNat 64 ((blk 165).getD i 0)
  soal : SO.toNat % 8 = 0
  sohi : SO.toNat + 808 ≤ heapNext u
  sovals : ∀ i < 101, u.getMem (SO + BitVec.ofNat 64 (8 * i)) = (sol (kapPre A k 6)).getD i 0
  hd8 : u.getMem (s.getReg .x2 - 920) = SO
  hd16 : u.getMem (s.getReg .x2 - 912) = 101
  hd24 : (u.getMem (s.getReg .x2 - 904)).toNat = (stackOffsetsRust (bkl (kapPre A k 6))).2
  x9 : u.getReg .x9 = G
  x24 : u.getReg .x24 = 165
  x25 : u.getReg .x25 = 101
  x18 : u.getReg .x18 = BitVec.ofNat 64 ((hts A).getD 5 0)
  x23 : u.getReg .x23 = BitVec.ofNat 64 (k - 4)
  x26 : u.getReg .x26 = BitVec.ofNat 64 ((hts A).getD 5 0 + 6)

set_option maxRecDepth 8192 in
/-- `stack_offsets(block_kappas)`. -/
theorem soCall (hSO : StackOffsetsSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s u : MachineState} {A : List E} {k : Nat} {R Q B : Word} {lo lo2 lo3 : Nat} {G BK : Word}
    (hpre : WalkPre s) (hpc : u.pc = 0x800032b8) (h : AtR13 OI s u A k R Q B lo lo2 lo3 G BK) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨
      (t.pc = 0x800032c4 ∧ ∃ SO, So13 OI s t A k R Q B lo lo2 lo3 G SO)) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have Bs := h.base
  have I := Bs.k11.at11.base.inv
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := I.sp
  have hle := Bs.k11.at11.base.ok
  have hhu := I.heap.hi
  simp only [heapEnd] at hhu
  have gl := h.glo
  have gh := h.ghi
  have bh := h.bkhi
  have bal := h.bkal
  have hl3 := Bs.lo3le
  obtain ⟨c1, c2, c3, -⟩ := Bs.kv.bounds (kapPre_ne A k (le_refl 6))
  have kb := Bs.kbelow
  simp only [heapStart] at c2
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800032b8_spec hpc (by rv_eval [])
  have m₁ := b800032b8_mem_same h₁
  have k₁ := b800032b8_keeps h₁
  have B₁ := Bs.same hpre m₁ (k₁ .x2 (by decide))
  have I₁ := B₁.k11.at11.base.inv
  have hn₁ : heapNext u₁ = heapNext u := by simp only [heapNext, m₁]
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 928 := by
    rw [b800032b8_x10 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x11₁ : u₁.getReg .x11 = BK := by rw [k₁ .x11 (by decide)]; exact h.x11
  have x12₁ : (u₁.getReg .x12).toNat = 101 := by rw [k₁ .x12 (by decide), h.x12]; rfl
  have hab := hpre.stack.above
  have hx := hpre.stack.next
  rw [stackLo_eq] at hab hx
  rw [stack_eq] at hx
  simp only [heapEnd] at hab
  have pre : StackOffsetsPre u₁ := {
    heap := I₁.heap
    out := by rw [x10₁]; simp only [Region, Mapped]; addr_omega [hb1, hb2, hb3]
    sizes := Or.inr (by rw [x11₁, x12₁]; simp only [Region, Mapped]; constructor <;> omega)
    stack := stk10 hpre I₁ (by decide) (by decide)
    outFree := by
      rw [x10₁]; exact ⟨Or.inr (by addr_omega [hab, hb1]), by simp only [Apart]; addr_omega [hx, hb1]⟩
    outStack := by
      rw [x10₁, stackLo_callee I₁]; simp only [Apart, stackOffsetsStack, tryAllocStack]
      addr_omega [hb1]
    sizesFree := Or.inr (by
      rw [x11₁, x12₁]; refine ⟨Or.inl (by rw [hn₁]; omega), ?_⟩
      simp only [Apart]; addr_omega [bh, hhu, hn₁])
    sizesStack := by
      rw [x11₁, x12₁, stackLo_callee I₁]; simp only [Apart, stackOffsetsStack, tryAllocStack]
      addr_omega [hb1, bh, hhu]
    sizesOut := by rw [x11₁, x12₁, x10₁]; simp only [Apart]; addr_omega [hb1, bh, hhu] }
  obtain ⟨t, hr, ⟨hpct, hp, post⟩ | hd⟩ := hSO u₁ (b800032b8_pc h₁) pre
  swap
  · exact ⟨t, hr₁.trans hr, Or.inl hd⟩
  have hht := post.heap.hi
  have hmono := post.mono
  simp only [heapEnd] at hht
  have fr := post.frame.dframe
  rw [x10₁] at fr
  have Bt := B₁.keep hpre fr (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · rw [stackLo_callee I₁] at ha
        exact Or.inr (Or.inl (by
          simp only [Within, stackOffsetsStack, tryAllocStack] at ha ⊢; addr_omega [ha, hb1]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · simp only [Fresh] at ha; exact Or.inr (Or.inr (Or.inr ⟨by rw [hn₁] at ha; omega, ha.2⟩)))
    post.heap hmono (hp .x2 (by decide))
  have hsz : sizesAt u₁ = bkl (kapPre A k 6) := by
    simp only [sizesAt, x11₁, x12₁, readWords_eq_map, List.map_map]
    apply List.ext_getElem (by simp [bkl_length])
    intro i h1 h2
    have hi : i < 101 := by simpa using h1
    simp only [List.getElem_map, List.getElem_range, Function.comp, bkl]
    rw [m₁, h.bkvals i hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := kapPre_le hle ((blk 165).getD i 0); omega)]
    simp only [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show i < (blk 165).length by rw [blk_165_length]; exact hi),
      Option.getD_some]
  have poff := post.offsets
  have plog := post.log
  have pfr := post.fresh
  have plen := post.len
  rw [x10₁, hsz] at poff plog
  rw [x10₁] at pfr plen
  rw [x12₁] at pfr
  obtain ⟨SO, hSOd⟩ : ∃ SO, vecPtr t (s.getReg .x2 - 928) = SO := ⟨_, rfl⟩
  rw [hSOd] at pfr
  simp only [NewBuf] at pfr
  obtain ⟨so1, so2⟩ := pfr
  have so3 : heapNext u ≤ SO.toNat ∧ SO.toNat + 808 ≤ heapNext t := by
    rcases so2 with h0 | h0
    · omega
    · rw [hn₁] at h0; exact h0
  have hlt : (vecLen t (s.getReg .x2 - 928)).toNat = 101 := by rw [plen, k₁ .x12 (by decide), h.x12]; rfl
  simp only [vecWords, hSOd, hlt, readWords_eq_map] at poff
  have e8 : s.getReg .x2 - 928 + 8 = s.getReg .x2 - 920 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e16 : s.getReg .x2 - 928 + 16 = s.getReg .x2 - 912 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e24 : s.getReg .x2 - 928 + 24 = s.getReg .x2 - 904 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have rg (r : Reg) (hr : r ∈ ([.x2, .x9, .x18, .x23, .x24, .x25, .x26] : List Reg)) :
      t.getReg r = u.getReg r := by
    rw [hp r (by revert r hr; decide), k₁ r (by revert r hr; decide)]
  refine ⟨t, hr₁.trans hr, Or.inr ⟨by rw [hpct, returnAddress_eq, b800032b8_x1 h₁]; decide, SO, {
    base := Bt
    gal := h.gal
    glo := gl
    ghi := by omega
    gvals := fun i hi ↦ by
      rw [fr.getMem_of (fun x hx hw ↦ by
          simp only [Within] at hx
          rcases hw with h2 | h2 | h2 | h2
          · simp only [Within] at h2; addr_omega [hx, h2, hb1, gl, gh, bh, hhu, hi, c2, c3, kb, hl3]
          · rw [stackLo_callee I₁] at h2; simp only [Within, stackOffsetsStack, tryAllocStack] at h2
            addr_omega [hx, h2, hb1, gl, gh, bh, hhu, hi, c2, c3, kb, hl3]
          · simp only [Within, nextAddr] at h2; addr_omega [hx, h2, gl, gh, bh, hhu, hi, c2, c3, kb, hl3]
          · simp only [Fresh] at h2; addr_omega [hx, h2, gl, gh, bh, hn₁, hi])
        (by addr_omega [gl, gh, bh, hhu, hi, c2, c3, kb, hl3]), m₁]
      exact h.gvals i hi
    soal := so1
    sohi := so3.2
    sovals := fun i hi ↦ by
      show _ = (stackOffsetsRust (bkl (kapPre A k 6))).1.getD i 0
      rw [← poff, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl
    hd8 := by rw [← e8]; exact hSOd
    hd16 := by
      have : vecLen t (s.getReg .x2 - 928) = 101 := by rw [plen, k₁ .x12 (by decide), h.x12]
      rw [← e16]; exact this
    hd24 := by rw [← e24]; exact plog
    x9 := by rw [rg .x9 (by decide)]; exact h.x9
    x24 := by rw [rg .x24 (by decide)]; exact h.x24
    x25 := by rw [rg .x25 (by decide)]; exact h.x25
    x18 := by rw [rg .x18 (by decide)]; exact h.x18
    x23 := by rw [rg .x23 (by decide)]; exact h.x23
    x26 := by rw [rg .x26 (by decide)]; exact h.x26 }⟩⟩

end Rv64Verifier.Proofs.Walk
