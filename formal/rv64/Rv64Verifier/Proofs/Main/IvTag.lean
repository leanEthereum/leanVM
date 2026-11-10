import Rv64Verifier.Proofs.Main.IvAlloc

/-!
# `TAG`, stored a byte at a time

`0x8000037c` stores the nine bytes of `TAG` at the buffer's start. The buffer comes from the bump
allocator with alignment `1`, so the generated block, which wants its base 8-aligned, does not
apply: the loads before the stores are one expectation (`tagA`), each `sb` one step (`sb_step`),
the `addi` between them and the branch after them two more (`tagB`, `tagC`) (`iv_tag`, to `IvT`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Proofs.End
  Rv64Verifier.Runtime.Memcpy

/-- `0x8000037c`..`0x800003a0`: the buffer and its length, `TAG`'s first seven bytes, their
address. -/
def tagA : Sym.Expect where
  steps := 10
  pc := .c 0x800003a4
  regs := [(.x9, .ld (.bin .add (.reg .x2) (.c 112))), (.x18, .ld (.bin .add (.reg .x2) (.c 120))),
    (.x10, .c 108), (.x11, .c 101), (.x12, .c 97), (.x13, .c 110), (.x14, .c 118), (.x15, .c 109),
    (.x16, .c 45),
    (.x17, .bin .add (.ld (.bin .add (.reg .x2) (.c 112))) (.ld (.bin .add (.reg .x2) (.c 120))))] ++
    keepE [.x9, .x18, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]
  mem := []
  writes := []
  obl := [.valid ⟨some (.reg .x2), 112⟩ 8, .valid ⟨some (.reg .x2), 120⟩ 8]

/-- `0x800003b4`: `TAG`'s last byte. -/
def tagB : Sym.Expect where
  steps := 1
  pc := .c 0x800003b8
  regs := [(.x10, .c 49)] ++ keepE [.x10]
  mem := []
  writes := []
  obl := []

/-- `0x800003cc`: the length after `TAG`, and the branch on an empty table. -/
def tagC : Sym.Expect where
  steps := 2
  pc := .ite .eq (.reg .x19) (.c 0) (.c 0x800003f4) (.c 0x800003d4)
  regs := [(.x12, .bin .add (.reg .x18) (.c 9))] ++ keepE [.x12]
  mem := []
  writes := []
  obl := []

theorem tagA_spec : Spec 0x8000037c tagA :=
  spec_of 223 10 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem tagB_spec : Spec 0x800003b4 tagB :=
  spec_of 237 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem tagC_spec : Spec 0x800003cc tagC :=
  spec_of 243 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem sb_3a4 : Image.code.fetch 0x800003a4 = some (.base (.SB .x17 .x10 0)) :=
  fetch_of (by decide +kernel)
theorem sb_3a8 : Image.code.fetch 0x800003a8 = some (.base (.SB .x17 .x11 1)) :=
  fetch_of (by decide +kernel)
theorem sb_3ac : Image.code.fetch 0x800003ac = some (.base (.SB .x17 .x12 2)) :=
  fetch_of (by decide +kernel)
theorem sb_3b0 : Image.code.fetch 0x800003b0 = some (.base (.SB .x17 .x13 3)) :=
  fetch_of (by decide +kernel)
theorem sb_3b8 : Image.code.fetch 0x800003b8 = some (.base (.SB .x17 .x14 4)) :=
  fetch_of (by decide +kernel)
theorem sb_3bc : Image.code.fetch 0x800003bc = some (.base (.SB .x17 .x15 5)) :=
  fetch_of (by decide +kernel)
theorem sb_3c0 : Image.code.fetch 0x800003c0 = some (.base (.SB .x17 .x16 6)) :=
  fetch_of (by decide +kernel)
theorem sb_3c4 : Image.code.fetch 0x800003c4 = some (.base (.SB .x17 .x14 7)) :=
  fetch_of (by decide +kernel)
theorem sb_3c8 : Image.code.fetch 0x800003c8 = some (.base (.SB .x17 .x10 8)) :=
  fetch_of (by decide +kernel)

/-- A byte store's effect on `n` bytes from `p`. -/
theorem bytesAt_store {u t : MachineState} {p : Word} {n j : Nat} {v : BitVec 8}
    (hb : byteAt t (p + BitVec.ofNat 64 j) = v) (hf : ByteFrame u t (· = p + BitVec.ofNat 64 j))
    (hj : j < n) (hn : n < 2 ^ 64) : bytesAt t p n = (bytesAt u p n).set j v := by
  apply List.ext_getElem (by simp [bytesAt_length])
  intro i h1 h2
  rw [bytesAt_length] at h1
  rw [List.getElem_set, bytesAt_getElem, bytesAt_getElem]
  by_cases hij : j = i
  · subst hij; simp [hb]
  · simp only [hij, ↓reduceIte]
    refine hf.byte _ fun he ↦ hij ?_
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
    have := p.isLt
    omega

theorem bytesAt_same {s t : MachineState} (h : ∀ a, t.getMem a = s.getMem a) (p : Word) (n : Nat) :
    bytesAt t p n = bytesAt s p n := by
  unfold bytesAt
  congr 1
  funext i
  rw [byteAt_eq, byteAt_eq, h]

/-- After `TAG` (at `0x800003d4`, or `0x800003f4` for an empty table): the buffer at `s1`, its first
nine bytes `TAG`, `a2 = 9`. -/
structure IvT (s : MachineState) (words : List Word) (u : MachineState) : Prop where
  inv : MInv s words u
  pc : u.pc = if words.getD 0 0 = 0 then 0x800003f4 else 0x800003d4
  len : (words.getD 0 0).toNat + 1 ≤ words.length
  x19 : u.getReg .x19 = words.getD 0 0
  x8 : u.getReg .x8 = BitVec.ofNat 64 (8 * (words.getD 0 0).toNat)
  x18 : u.getReg .x18 = 0
  x12 : u.getReg .x12 = 9
  ptr : u.getMem (msp + 88) = inputBase + BitVec.ofNat 64 (8 * ((words.getD 0 0).toNat + 1))
  rest : (u.getMem (msp + 96)).toNat = words.length - ((words.getD 0 0).toNat + 1)
  buf : heapStart ≤ (u.getReg .x9).toNat ∧
    (u.getReg .x9).toNat + (8 * (words.getD 0 0).toNat + 9) ≤ heapNext u
  tag : bytesAt u (u.getReg .x9) 9 = Model.tagRust

/-- Between the stores: memory changed only in the nine bytes from `p`, which hold `B`, and `a7`
is `p`. -/
structure TagSt (u : MachineState) (p : Word) (t : MachineState) (B : List (BitVec 8)) : Prop where
  frame : ByteFrame u t (Within · p 9)
  bytes : bytesAt t p 9 = B
  x17 : t.getReg .x17 = p

theorem signExtend12_small {k : Nat} (hk : k < 9) :
    signExtend12 (BitVec.ofNat 12 k) = BitVec.ofNat 64 k := by
  interval_cases k <;> rfl

/-- One of `TAG`'s stores. -/
theorem tag_sb {u t : MachineState} {p pc pc' : Word} {B : List (BitVec 8)} {rs2 : Reg} (k : Nat)
    (h : TagSt u p t B) (hpc : t.pc = pc) (hpc' : pc + 4 = pc')
    (hf : Image.code.fetch pc = some (.base (.SB .x17 rs2 (BitVec.ofNat 12 k)))) (hk : k < 9)
    (hmap : Runtime.Mapped p 9) :
    ∃ t', Reaches Image.code t t' ∧ t'.pc = pc' ∧ (∀ r, t'.getReg r = t.getReg r) ∧
      TagSt u p t' (B.set k ((t.getReg rs2).truncate 8)) := by
  have ha : t.getReg .x17 + signExtend12 (BitVec.ofNat 12 k) = p + BitVec.ofNat 64 k := by
    rw [h.x17, signExtend12_small hk]
  obtain ⟨t', hr, hpc'', hreg, hb, hfr⟩ := sb_step (by rw [hpc]; exact hf)
    (by rw [ha]; exact Mapped.valid hmap hk)
  rw [ha] at hb hfr
  refine ⟨t', hr, by rw [hpc'.symm, ← hpc]; exact hpc'', hreg, h.frame.trans hfr fun a ha' ↦ ?_, ?_, ?_⟩
  · rw [ha']
    simp only [Runtime.Mapped] at hmap
    addr_omega [hk, hmap]
  · rw [bytesAt_store hb hfr hk (by decide), h.bytes]
  · rw [hreg, h.x17]

theorem set_nine (l : List (BitVec 8)) (hl : l.length = 9) (a0 a1 a2 a3 a4 a5 a6 a7 a8 : BitVec 8) :
    (((((((((l.set 0 a0).set 1 a1).set 2 a2).set 3 a3).set 4 a4).set 5 a5).set 6 a6).set 7 a7).set
      8 a8) = [a0, a1, a2, a3, a4, a5, a6, a7, a8] := by
  apply List.ext_getElem (by simp [hl])
  intro i h1 _
  simp only [List.length_set, hl] at h1
  interval_cases i <;> simp

/-- **`TAG`, to `IvT`.** -/
theorem iv_tag {s u : MachineState} {words : List Word} (h : IvB s words u) :
    ∃ v, Reaches Image.code u v ∧ IvT s words v := by
  have hsp := h.inv.sp
  have hfit := h.inv.fits
  have hbuf := h.buf
  have hhi := h.inv.heap.hi
  set p := u.getMem (msp + 112) with hp
  have hmap9 : Runtime.Mapped p 9 := by
    simp only [Runtime.Mapped, heapStart, heapEnd] at hbuf hhi ⊢; omega
  obtain ⟨t₀, hr₀, hA⟩ := Sym.BlockSpec.reaches tagA_spec h.pc (by rv_eval [hsp, msp]; decide)
  have kA : ∀ r ∉ ([.x9, .x18, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] : List Reg),
      t₀.getReg r = u.getReg r :=
    fun r hr ↦ keepE_reg hA (fun q hq ↦ List.mem_append_right _ hq) hr
  have mA : ∀ a, t₀.getMem a = u.getMem a := hA.mem_same rfl
  have e17 : t₀.getReg .x17 = p := by
    have e : t₀.getReg .x17 = u.getMem (u.getReg .x2 + 112) + u.getMem (u.getReg .x2 + 120) :=
      hA.reg_eq .x17 rfl rfl
    rw [e, hsp, h.vlen]; exact BitVec.add_zero _
  have st₀ : TagSt u p t₀ (bytesAt t₀ p 9) :=
    ⟨ByteFrame.of_same mA _, rfl, e17⟩
  have hpc₀ : t₀.pc = 0x800003a4 := hA.pc
  obtain ⟨t₁, hr₁, hpc₁, g₁, st₁⟩ := tag_sb (pc' := 0x800003a8) 0 st₀ hpc₀ (by decide) sb_3a4 (by decide) hmap9
  obtain ⟨t₂, hr₂, hpc₂, g₂, st₂⟩ := tag_sb (pc' := 0x800003ac) 1 st₁ hpc₁ (by decide) sb_3a8 (by decide) hmap9
  obtain ⟨t₃, hr₃, hpc₃, g₃, st₃⟩ := tag_sb (pc' := 0x800003b0) 2 st₂ hpc₂ (by decide) sb_3ac (by decide) hmap9
  obtain ⟨t₄, hr₄, hpc₄, g₄, st₄⟩ := tag_sb (pc' := 0x800003b4) 3 st₃ hpc₃ (by decide) sb_3b0 (by decide) hmap9
  obtain ⟨t₅, hr₅, hB⟩ := Sym.BlockSpec.reaches tagB_spec hpc₄ trivial
  have kB : ∀ r ∉ ([.x10] : List Reg), t₅.getReg r = t₄.getReg r :=
    fun r hr ↦ keepE_reg hB (fun q hq ↦ List.mem_append_right _ hq) hr
  have mB : ∀ a, t₅.getMem a = t₄.getMem a := hB.mem_same rfl
  have st₅ := TagSt.mk (st₄.frame.trans (ByteFrame.of_same mB _) fun _ h ↦ h)
      ((bytesAt_same mB p 9).trans st₄.bytes) (by rw [kB .x17 (by decide)]; exact st₄.x17)
  have hpc₅ : t₅.pc = 0x800003b8 := hB.pc
  have e10 : t₅.getReg .x10 = 49 := hB.reg_eq .x10 rfl rfl
  have a10 : t₀.getReg .x10 = 108 := hA.reg_eq .x10 rfl rfl
  have a11 : t₀.getReg .x11 = 101 := hA.reg_eq .x11 rfl rfl
  have a12 : t₀.getReg .x12 = 97 := hA.reg_eq .x12 rfl rfl
  have a13 : t₀.getReg .x13 = 110 := hA.reg_eq .x13 rfl rfl
  have a14 : t₀.getReg .x14 = 118 := hA.reg_eq .x14 rfl rfl
  have a15 : t₀.getReg .x15 = 109 := hA.reg_eq .x15 rfl rfl
  have a16 : t₀.getReg .x16 = 45 := hA.reg_eq .x16 rfl rfl
  obtain ⟨t₆, hr₆, hpc₆, g₆, st₆⟩ := tag_sb (pc' := 0x800003bc) 4 st₅ hpc₅ (by decide) sb_3b8 (by decide) hmap9
  obtain ⟨t₇, hr₇, hpc₇, g₇, st₇⟩ := tag_sb (pc' := 0x800003c0) 5 st₆ hpc₆ (by decide) sb_3bc (by decide) hmap9
  obtain ⟨t₈, hr₈, hpc₈, g₈, st₈⟩ := tag_sb (pc' := 0x800003c4) 6 st₇ hpc₇ (by decide) sb_3c0 (by decide) hmap9
  obtain ⟨t₉, hr₉, hpc₉, g₉, st₉⟩ := tag_sb (pc' := 0x800003c8) 7 st₈ hpc₈ (by decide) sb_3c4 (by decide) hmap9
  obtain ⟨t₁₀, hr₁₀, hpc₁₀, g₁₀, st₁₀⟩ := tag_sb (pc' := 0x800003cc) 8 st₉ hpc₉ (by decide) sb_3c8 (by decide) hmap9
  obtain ⟨t₁₁, hr₁₁, hC⟩ := Sym.BlockSpec.reaches tagC_spec hpc₁₀ trivial
  have kC : ∀ r ∉ ([.x12] : List Reg), t₁₁.getReg r = t₁₀.getReg r :=
    fun r hr ↦ keepE_reg hC (fun q hq ↦ List.mem_append_right _ hq) hr
  have mC : ∀ a, t₁₁.getMem a = t₁₀.getMem a := hC.mem_same rfl
  -- registers from `t₀` to `t₁₀`
  have g : ∀ r, r ≠ .x10 → t₁₀.getReg r = t₀.getReg r := by
    intro r hr
    rw [g₁₀, g₉, g₈, g₇, g₆, kB r (by simpa using hr), g₄, g₃, g₂, g₁]
  have gu : ∀ r ∉ ([.x9, .x18, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] : List Reg),
      t₁₁.getReg r = u.getReg r := by
    intro r hr
    rw [kC r (fun h ↦ hr (by simp at h; simp [h])), g r (fun h ↦ hr (by simp [h])), kA r hr]
  have e9 : t₁₁.getReg .x9 = p := by
    have e : t₀.getReg .x9 = u.getMem (u.getReg .x2 + 112) := hA.reg_eq .x9 rfl rfl
    rw [kC .x9 (by decide), g .x9 (by decide), e, hsp]
  have e18 : t₁₁.getReg .x18 = 0 := by
    have e : t₀.getReg .x18 = u.getMem (u.getReg .x2 + 120) := hA.reg_eq .x18 rfl rfl
    rw [kC .x18 (by decide), g .x18 (by decide), e, hsp]; exact h.vlen
  have hfr : ByteFrame u t₁₁ (Within · p 9) :=
    st₁₀.frame.trans (ByteFrame.of_same mC _) fun _ h ↦ h
  have hsp₁₁ : t₁₁.getReg .x2 = msp := by rw [gu .x2 (by decide), hsp]
  have hnx : t₁₁.getMem nextAddr = u.getMem nextAddr :=
    hfr.getMem fun i hi hw ↦ by simp only [heapEnd] at hhi; addr_omega [hw, hi, hhi, hbuf]
  have hheap : HeapOk t₁₁ := ⟨by simp only [heapNext, hnx]; exact h.inv.heap.lo,
    by simp only [heapNext, hnx]; exact hhi⟩
  have keep : ∀ k : Nat, k + 8 ≤ 576 → t₁₁.getMem (msp + BitVec.ofNat 64 k) =
      u.getMem (msp + BitVec.ofNat 64 k) := by
    intro k hk
    exact hfr.getMem fun i hi hw ↦ by simp only [heapEnd] at hhi; addr_omega [hw, hi, hk, hhi, hbuf]
  refine ⟨t₁₁, hr₀.trans (hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans (hr₆.trans
    (hr₇.trans (hr₈.trans (hr₉.trans (hr₁₀.trans hr₁₁)))))))))), ?_⟩
  refine ⟨h.inv.frame hfr hsp₁₁ hheap fun a ha ↦ not_kept_heap hfit (by
      simp only [heapEnd] at hhi; constructor <;> addr_omega [ha, hbuf, hhi]), ?_, h.len, ?_, ?_,
    e18, ?_, ?_, ?_, ?_, ?_⟩
  · have e19 : t₁₀.getReg .x19 = words.getD 0 0 := by
      rw [g .x19 (by decide), kA .x19 (by decide), h.x19]
    rw [hC.pc]
    simp only [tagC, Sym.E.eval, Sym.CmpOp.eval, e19, beq_iff_eq]
  · rw [gu .x19 (by decide), h.x19]
  · rw [gu .x8 (by decide), h.x8]
  · have e : t₁₁.getReg .x12 = t₁₀.getReg .x18 + 9 := hC.reg_eq .x12 rfl rfl
    rw [e, ← kC .x18 (by decide), e18]; rfl
  · rw [show (msp + 88 : Word) = msp + BitVec.ofNat 64 88 from rfl, keep 88 (by decide)]
    exact h.ptr
  · rw [show (msp + 96 : Word) = msp + BitVec.ofNat 64 96 from rfl, keep 96 (by decide)]
    exact h.rest
  · rw [e9, heapNext, hnx]; exact hbuf
  · have v0 : t₀.getReg .x10 = 108 := a10
    have v1 : t₁.getReg .x11 = 101 := by rw [g₁, a11]
    have v2 : t₂.getReg .x12 = 97 := by rw [g₂, g₁, a12]
    have v3 : t₃.getReg .x13 = 110 := by rw [g₃, g₂, g₁, a13]
    have v4 : t₅.getReg .x14 = 118 := by rw [kB .x14 (by decide), g₄, g₃, g₂, g₁, a14]
    have v5 : t₆.getReg .x15 = 109 := by rw [g₆, kB .x15 (by decide), g₄, g₃, g₂, g₁, a15]
    have v6 : t₇.getReg .x16 = 45 := by rw [g₇, g₆, kB .x16 (by decide), g₄, g₃, g₂, g₁, a16]
    have v7 : t₈.getReg .x14 = 118 := by rw [g₈, g₇, g₆, v4]
    have v8 : t₉.getReg .x10 = 49 := by rw [g₉, g₈, g₇, g₆, e10]
    rw [e9, bytesAt_same mC, st₁₀.bytes, v0, v1, v2, v3,
      v4, v5, v6, v7, v8, set_nine _ (bytesAt_length _ _ _)]
    decide

end Rv64Verifier.Proofs.Main
