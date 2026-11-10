import Rv64Verifier.Proofs.Main.ParseLeaf

/-!
# A path, to its leaf

`0x80000c7c` checks two words are left, reads the leaf index and the leaf's length `l`, checks `l`
words follow, allocates the leaf's buffer (`try_allocate_in`, 8-byte elements) and copies the leaf
(`path_head`, to `PaL` at `0x80000cf0`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Proofs.Bytecode Rv64Verifier.Proofs.End Rv64Verifier.Blocks.F3

/-- What a path writes: the input slice, `main`'s result slots, the stack, `NEXT`, the heap from
`B` on, and the path's 56 bytes at `q`. -/
def Wpath (B : Nat) (q a : Word) : Prop :=
  Within a (msp + 88) 16 ∨ Within a (msp + 272) 80 ∨ Within a (msp - 4096) 4096 ∨
    Within a nextAddr 8 ∨ (B ≤ a.toNat ∧ a.toNat < heapEnd) ∨ Within a q 56

theorem Wpath.of_wc {B B' : Nat} {q a : Word} (hB : B ≤ B') (h : Wc B' a) : Wpath B q a := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨le_trans hB h.1, h.2⟩))))

theorem Wpath.heap {B : Nat} {q a : Word} (h1 : B ≤ a.toNat) (h2 : a.toNat < heapEnd) :
    Wpath B q a :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))

/-- Path `j` of a phase of `npi` paths at `P`, at `e`, `k` words read. -/
structure PaS (u₀ : MachineState) (words : List Word) (P : Word) (npi j k : Nat) (e : Word)
    (t : MachineState) : Prop where
  pg : PG u₀ t
  pc : t.pc = e
  x18 : t.getReg .x18 = BitVec.ofNat 64 npi
  x23 : t.getReg .x23 = P
  x24 : t.getReg .x24 = BitVec.ofNat 64 j
  room : k ≤ words.length
  ptr : t.getMem (msp + 88) = inputBase + BitVec.ofNat 64 (8 * k)
  rest : (t.getMem (msp + 96)).toNat = words.length - k
  buf : P.toNat % 8 = 0 ∧ heapNext u₀ ≤ P.toNat ∧ P.toNat + 56 * npi ≤ heapNext t

/-- At `0x80000cf0`, path `j`'s leaf (`l` words at `L`) copied; `t₀` where the path started. -/
structure PaL (u₀ : MachineState) (words : List Word) (P : Word) (npi j k : Nat)
    (t₀ : MachineState) (L : Word) (l : Nat) (t : MachineState) : Prop where
  start : PaS u₀ words P npi j k 0x80000c7c t₀
  lt : j < npi
  pg : PG u₀ t
  pc : t.pc = 0x80000cf0
  x8 : t.getReg .x8 = words.getD k 0
  x9 : t.getReg .x9 = inputBase + BitVec.ofNat 64 (8 * (k + 2))
  x10 : t.getReg .x10 = BitVec.ofNat 64 (8 * l)
  x18 : t.getReg .x18 = BitVec.ofNat 64 npi
  x19 : t.getReg .x19 = BitVec.ofNat 64 l
  x21 : t.getReg .x21 = BitVec.ofNat 64 (words.length - (k + 2))
  x23 : t.getReg .x23 = P
  x24 : t.getReg .x24 = BitVec.ofNat 64 j
  x25 : t.getReg .x25 = L
  room : k + 2 + l ≤ words.length
  lread : (readList (BF64.ofBitVec <$> readWord)).run (words.drop (k + 1)) =
    some (((words.drop (k + 2)).take l).map BF64.ofBitVec, words.drop (k + 2 + l))
  leaf : t.readWords L l = (words.drop (k + 2)).take l
  lbuf : InR L (8 * l) 8 (heapNext t₀) (heapNext t)
  frame : BFrame t₀ t (Wpath (heapNext t₀) (P + BitVec.ofNat 64 (56 * j)))
  mono : heapNext t₀ ≤ heapNext t

theorem toNat_8 : (8 : Word).toNat = 8 := rfl

section
variable {s u₀ t : MachineState} {words : List Word}

/-- **A path, to its leaf.** -/
theorem path_head (h0 : ParseA s words u₀) {P : Word} {npi j k : Nat}
    (hs : PaS u₀ words P npi j k 0x80000c7c t) (hj : j < npi) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ ∃ L l, PaL u₀ words P npi j k t L l v) := by
  have hg := hs.pg
  have hsp := hg.sp
  have hfit := h0.inv.fits
  simp only [inputWords] at hfit
  have hib : inputBase.toNat = 0x10000000 := rfl
  have hhi := hg.heap.hi
  have hlo0 := h0.inv.heap.lo
  simp only [heapStart, heapNext, heapEnd] at hlo0 hhi
  have hroom := hs.room
  have hin := input_mapped (words := words) (by simp only [inputWords]; exact hfit)
  have hrest := hs.rest
  -- `0x80000c7c`, `0x80000c84`: two words left
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b80000c7c_spec hs.pc (by rv_eval [hsp, msp]; decide)
  by_cases z0 : t.getMem (t.getReg .x2 + 96) = 0
  · obtain ⟨w, hw, hd⟩ := abort (u := t₁) (by rw [b80000c7c_pc_taken h₁ z0]; decide)
    exact ⟨w, r₁.trans hw, Or.inl hd⟩
  have k₁ := b80000c7c_keeps h₁
  have m₁ := b80000c7c_mem_same h₁
  have hsp₁ : t₁.getReg .x2 = msp := by rw [k₁ .x2 (by decide), hsp]
  have x21₁ : t₁.getReg .x21 = BitVec.ofNat 64 (words.length - k) := by
    rw [b80000c7c_x21 h₁, hsp]
    apply BitVec.eq_of_toNat_eq
    rw [hrest, BitVec.toNat_ofNat]
    omega
  rw [hsp] at z0
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b80000c84_spec (b80000c7c_pc_not_taken h₁ (by
    rw [hsp]; exact z0)) trivial
  by_cases z1 : t₁.getReg .x21 = 1
  · obtain ⟨w, hw, hd⟩ := abort (u := t₂) (by rw [b80000c84_pc_taken h₂ z1]; decide)
    exact ⟨w, r₁.trans (r₂.trans hw), Or.inl hd⟩
  have k₂ := b80000c84_keeps h₂
  have m₂ := b80000c84_mem_same h₂
  have hsp₂ : t₂.getReg .x2 = msp := by rw [k₂ .x2 (by decide), hsp₁]
  have hk2 : k + 2 ≤ words.length := by
    by_contra hc
    rcases (by omega : words.length - k = 0 ∨ words.length - k = 1) with e | e
    · apply z0
      apply BitVec.eq_of_toNat_eq
      rw [hrest, e]; rfl
    · apply z1
      rw [x21₁, e]; rfl
  have g88 : t₂.getMem (msp + 88) = inputBase + BitVec.ofNat 64 (8 * k) := by
    rw [m₂, m₁, hs.ptr]
  have hg₂ : PG u₀ t₂ := hg.same (fun a ↦ by rw [m₂, m₁]) hsp₂
  -- `0x80000c8c`: the leaf's length, `l` words left
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b80000c8c_spec (b80000c84_pc_not_taken h₂ z1) (by
    rv_eval [hsp₂, g88]
    and_intros <;> first
      | decide
      | valid_in hin [hib, hk2, hfit])
  have hl₂ : t₂.getMem (t₂.getMem (t₂.getReg .x2 + 88) + 8) = words[k + 1] := by
    rw [hsp₂, g88]; exact hg₂.word h0 (j := k + 1) (by omega) (by addr_omega [hib, hk2, hfit])
  set l := (words[k + 1]).toNat with hl
  have x21₂ : t₂.getReg .x21 = BitVec.ofNat 64 (words.length - k) := by
    rw [k₂ .x21 (by decide), x21₁]
  have e2 : (t₂.getReg .x21 - 2).toNat = words.length - (k + 2) := by
    rw [x21₂]; addr_omega [hk2, hfit]
  by_cases z2 : (t₂.getReg .x21 - 2).toNat < (t₂.getMem (t₂.getMem (t₂.getReg .x2 + 88) + 8)).toNat
  · obtain ⟨w, hw, hd⟩ := abort (u := t₃) (by rw [b80000c8c_pc_taken h₃ z2]; decide)
    exact ⟨w, r₁.trans (r₂.trans (r₃.trans hw)), Or.inl hd⟩
  have hkl : k + 2 + l ≤ words.length := by rw [e2, hl₂] at z2; omega
  have hlread : (readList (BF64.ofBitVec <$> readWord)).run (words.drop (k + 1)) =
      some (((words.drop (k + 2)).take l).map BF64.ofBitVec, words.drop (k + 2 + l)) := by
    rw [drop_cons (show k + 1 < words.length by omega), readList_run,
      readWords_rep _ _ _ (by simp only [List.length_drop]; omega), List.drop_drop]
  have pc₃ := b80000c8c_pc_not_taken h₃ (Nat.le_of_not_lt z2)
  have k₃ := b80000c8c_keeps h₃
  have m₃ := b80000c8c_mem_same h₃
  have hsp₃ : t₃.getReg .x2 = msp := by rw [k₃ .x2 (by decide), hsp₂]
  have x9₃ : t₃.getReg .x9 = inputBase + BitVec.ofNat 64 (8 * k) := by
    rw [b80000c8c_x9 h₃, hsp₂, g88]
  have x19₃ : t₃.getReg .x19 = words[k + 1] := by rw [b80000c8c_x19 h₃, hl₂]
  have hg₃ : PG u₀ t₃ := hg₂.same m₃ hsp₃
  -- `0x80000c9c`: the leaf index, `try_allocate_in`
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b80000c9c_spec pc₃ (by
    rv_eval [x9₃]
    valid_in hin [hib, hk2, hfit])
  have k₄ := b80000c9c_keeps h₄
  have m₄ := b80000c9c_mem_same h₄
  have hsp₄ : t₄.getReg .x2 = msp := by rw [k₄ .x2 (by decide), hsp₃]
  have hg₄ : PG u₀ t₄ := hg₃.same m₄ hsp₄
  have x8₄ : t₄.getReg .x8 = words.getD k 0 := by
    rw [b80000c9c_x8 h₄, x9₃, hg₃.word h0 (j := k) (by omega) rfl]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < words.length by omega),
      Option.getD_some]
  have hn₄ : heapNext t₄ = heapNext t := by
    simp only [heapNext, m₄, m₃, m₂, m₁]
  obtain ⟨w, rw', hd | ⟨pcw, regw, hgw, hfw, hmw, -, bufw⟩⟩ := alloc_call hg₄ (b80000c9c_pc h₄)
    (by rw [b80000c9c_x10 h₄, hsp₃]) (by rw [b80000c9c_x12 h₄]; decide)
    (by rw [b80000c9c_x13 h₄]; decide) (by rw [b80000c9c_x13 h₄]; decide)
    (Or.inl (by rw [b80000c9c_x12 h₄]; decide)) (by rw [returnAddress, b80000c9c_x1 h₄]; decide)
    b80000cb8_spec (fun v hv ↦ by rv_eval [hv]; decide)
    (fun _ _ h hc ↦ b80000cb8_pc_taken h hc) (fun _ _ h hc ↦ b80000cb8_pc_not_taken h hc)
    (fun _ _ h ↦ b80000cb8_mem_same h) (fun _ _ h r hr ↦ b80000cb8_keeps h r (mem_of_calleeSaved hr _))
  · exact ⟨w, r₁.trans (r₂.trans (r₃.trans (r₄.trans rw'))), Or.inl hd⟩
  have hspw : w.getReg .x2 = msp := by rw [regw .x2 (by decide), hsp₄]
  rw [b80000c9c_x11 h₄, x19₃, b80000c9c_x13 h₄, b80000c9c_x12 h₄] at bufw
  have x9w : w.getReg .x9 = inputBase + BitVec.ofNat 64 (8 * k) := by
    rw [regw .x9 (by decide), k₄ .x9 (by decide), x9₃]
  have x19w : w.getReg .x19 = words[k + 1] := by
    rw [regw .x19 (by decide), k₄ .x19 (by decide), x19₃]
  have x8w : w.getReg .x8 = words.getD k 0 := by rw [regw .x8 (by decide), x8₄]
  have x21w : w.getReg .x21 = BitVec.ofNat 64 (words.length - (k + 2)) := by
    rw [regw .x21 (by decide), k₄ .x21 (by decide), b80000c8c_x21 h₃, x21₂]; addr_omega [hk2, hfit]
  have regt : ∀ r ∈ ([.x18, .x23, .x24] : List Reg), w.getReg r = t.getReg r := by
    intro r hr
    rw [regw r (mem_of_mem hr _), k₄ r (mem_of_mem hr _), k₃ r (mem_of_mem hr _),
      k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  set L := w.getMem (msp + 336) with hLdef
  have hfr₀ : BFrame t w (Wpath (heapNext t) (P + BitVec.ofNat 64 (56 * j))) :=
    (BFrame.of_same (fun a ↦ by rw [m₄, m₃, m₂, m₁]) _).trans hfw fun a ha ↦
      Wpath.of_wc (le_of_eq hn₄.symm) ha
  have hmw' : heapNext t ≤ heapNext w := by rw [← hn₄]; exact hmw
  have hL8 : L.toNat % 8 = 0 := bufw.1
  have hLb : (8 * l = 0 ∧ L.toNat ≤ heapNext w) ∨
      heapNext t ≤ L.toNat ∧ L.toNat + 8 * l ≤ heapNext w := by
    rcases bufw.2 with h' | h'
    · left; rw [toNat_8] at h'; omega
    · right; rw [toNat_8, hn₄] at h'; exact ⟨h'.1, by omega⟩
  -- `0x80000cc0`
  obtain ⟨t₆, r₆, h₆⟩ := Sym.BlockSpec.reaches b80000cc0_spec pcw (by rv_eval [hspw, msp]; decide)
  have k₆ := b80000cc0_keeps h₆
  have m₆ := b80000cc0_mem_same h₆
  have hsp₆ : t₆.getReg .x2 = msp := by rw [k₆ .x2 (by decide), hspw]
  have hg₆ : PG u₀ t₆ := hgw.same m₆ hsp₆
  have hn₆ : heapNext t₆ = heapNext w := by simp only [heapNext, m₆]
  have x9₆ : t₆.getReg .x9 = inputBase + BitVec.ofNat 64 (8 * (k + 2)) := by
    rw [b80000cc0_x9 h₆, x9w]; addr_omega [hib, hk2, hfit]
  have x10₆ : t₆.getReg .x10 = BitVec.ofNat 64 (8 * l) := by rw [b80000cc0_x10 h₆, x19w, mul8]
  have x25₆ : t₆.getReg .x25 = L := by rw [b80000cc0_x25 h₆, hspw]
  have hfr₆ : BFrame t t₆ (Wpath (heapNext t) (P + BitVec.ofNat 64 (56 * j))) :=
    hfr₀.trans (BFrame.of_same m₆ _) fun _ h ↦ h
  have r : Reaches Image.code t t₆ := r₁.trans (r₂.trans (r₃.trans (r₄.trans (rw'.trans r₆))))
  have regs₆ : ∀ r ∈ ([.x18, .x23, .x24] : List Reg), t₆.getReg r = t.getReg r := by
    intro r hr; rw [k₆ r (mem_of_mem hr _), regt r hr]
  have x19₆ : t₆.getReg .x19 = BitVec.ofNat 64 l := by
    rw [k₆ .x19 (by decide), x19w, ofNat_toNat']
  have x8₆ : t₆.getReg .x8 = words.getD k 0 := by rw [k₆ .x8 (by decide), x8w]
  have x21₆ : t₆.getReg .x21 = BitVec.ofNat 64 (words.length - (k + 2)) := by
    rw [k₆ .x21 (by decide), x21w]
  by_cases hz : w.getReg .x19 = 0
  · -- an empty leaf
    have hl0 : l = 0 := by rw [x19w] at hz; rw [hl, hz]; rfl
    refine ⟨t₆, r, Or.inr ⟨L, l, ⟨hs, hj, hg₆, b80000cc0_pc_taken h₆ hz, x8₆, x9₆, x10₆, ?_, x19₆,
      x21₆, ?_, ?_, x25₆, hkl, hlread, by rw [hl0]; rfl, ?_, hfr₆, by rw [hn₆]; exact hmw'⟩⟩⟩
    · rw [regs₆ .x18 (by decide), hs.x18]
    · rw [regs₆ .x23 (by decide), hs.x23]
    · rw [regs₆ .x24 (by decide), hs.x24]
    · rw [hn₆]; exact ⟨hL8, hLb⟩
  · -- the copy
    have hlpos : 0 < l := by
      rcases Nat.eq_zero_or_pos l with h' | h'
      · exact absurd (by rw [x19w]; exact BitVec.eq_of_toNat_eq (by rw [← hl, h']; rfl)) hz
      · exact h'
    have hLb' : heapNext t ≤ L.toNat ∧ L.toNat + 8 * l ≤ heapNext w :=
      hLb.resolve_left fun h' ↦ by omega
    obtain ⟨t₇, r₇, h₇⟩ := Sym.BlockSpec.reaches b80000cd0_spec (b80000cc0_pc_not_taken h₆ hz) trivial
    have k₇ := b80000cd0_keeps h₇
    have m₇ := b80000cd0_mem_same h₇
    have hsp₇ : t₇.getReg .x2 = msp := by rw [k₇ .x2 (by decide), hsp₆]
    have hn₇ : heapNext t₇ = heapNext w := by simp only [heapNext, m₇]; exact hn₆
    have hhw := hgw.heap.hi
    simp only [heapNext, heapEnd] at hhw hLb'
    have hL : LfS u₀ words L l (k + 2) t₇ 0x80000cdc t₇ 0 := {
      pg := hg₆.same m₇ hsp₇
      pc := b80000cd0_pc h₇
      le := Nat.zero_le _
      regs := fun _ _ ↦ rfl
      x10 := rfl
      x11 := by rw [b80000cd0_x11 h₇, x25₆, x10₆]
      x12 := by rw [b80000cd0_x12 h₇, x9₆]
      x13 := by rw [b80000cd0_x13 h₇, x25₆]; addr_omega [hLb', hhw]
      room := hkl
      val := rfl
      frame := BFrame.refl _ _
      buf := ⟨hL8, by have := hg.mono; simp only [heapNext] at this ⊢; omega,
        by rw [hn₇]; simp only [heapNext]; omega⟩
      heap := rfl }
    obtain ⟨v, rv, hv⟩ := leaf_loop h0 hL hlpos
    have hnv : heapNext v = heapNext w := by rw [hv.heap, hn₇]
    have Rv : ∀ r ∈ ([.x8, .x9, .x18, .x19, .x21, .x23, .x24, .x25] : List Reg),
        v.getReg r = t₆.getReg r := by
      intro r hr
      rw [hv.regs r (mem_of_mem hr _), k₇ r (mem_of_mem hr _)]
    refine ⟨v, r.trans (r₇.trans rv), Or.inr ⟨L, l, ⟨hs, hj, hv.pg, hv.pc, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, hkl, hlread, hv.val, ?_, ?_, ?_⟩⟩⟩
    · rw [Rv .x8 (by decide), x8₆]
    · rw [Rv .x9 (by decide), x9₆]
    · rw [hv.x10, k₇ .x10 (by decide), x10₆]
    · rw [Rv .x18 (by decide), regs₆ .x18 (by decide), hs.x18]
    · rw [Rv .x19 (by decide), x19₆]
    · rw [Rv .x21 (by decide), x21₆]
    · rw [Rv .x23 (by decide), regs₆ .x23 (by decide), hs.x23]
    · rw [Rv .x24 (by decide), regs₆ .x24 (by decide), hs.x24]
    · rw [Rv .x25 (by decide), x25₆]
    · rw [hnv]; exact ⟨hL8, hLb⟩
    · exact (hfr₆.trans (BFrame.of_same m₇ _) fun _ h ↦ h).trans hv.frame fun a ha ↦
        Wpath.heap (by simp only [Within] at ha; simp only [heapNext] at hLb' ⊢; omega)
          (by simp only [Within] at ha; simp only [heapEnd]; omega)
    · rw [hnv]; exact hmw'

end

end Rv64Verifier.Proofs.Main
