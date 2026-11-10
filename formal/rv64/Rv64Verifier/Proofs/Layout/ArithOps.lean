import Rv64Verifier.Proofs.Layout.ArithStart

/-!
# `flushes_arith`: the operands and `bytecode`

`0x800054fc` and `0x80005510` call `col(sp' + 248, o_b, 0)` and `col(sp' + 272, o_c, 0)`;
`0x80005524` and `0x80005544` write `One`'s tag at `sp' + 80` and call `term(sp' + 296, One,
ZERO)` and `term(sp' + 320, One, ZERO)`; `0x8000555c` copies the four forms to `B + 24`.., makes
the `Vec` `(5, B, 5)` at `sp' + 56` and calls `bytecode(sp' + 8, cnt_bc, opcode, sp' + 56)`.
-/

namespace Rv64Verifier.Layout.Arith
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F19 Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Layout.Limb (Held)

/-- A header `(n, B, n)` at `v` over `24 n` allocated bytes at `B` holding `n` sound forms whose
buffers miss those bytes is a sound `Vec<Form>` of them. -/
theorem formVec_of {t : MachineState} {v B : Word} {n : Nat} (hn : n < 2 ^ 64)
    (hcap : t.getMem v = BitVec.ofNat 64 n) (hptr : t.getMem (v + 8) = B)
    (hlen : t.getMem (v + 16) = BitVec.ofNat 64 n) (hal : B.toNat % 8 = 0)
    (hlo : heapStart ≤ B.toNat) (hhi : B.toNat + 24 * n ≤ heapNext t)
    (hok : ∀ i < n, FormOk t (B + BitVec.ofNat 64 (24 * i)))
    (hsep : ∀ i < n, ∀ x, formBuf t (B + BitVec.ofNat 64 (24 * i)) x → ¬ Within x B (24 * n)) :
    FormVecOk t v ∧ formVecOf t v = formsAt t B n := by
  have hp : vecPtr t v = B := hptr
  have hl : (vecLen t v).toNat = n := by rw [vecLen, hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hc : (vecCap t v).toNat = n := by rw [vecCap, hcap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  refine ⟨⟨⟨?_, by rw [hl, hc]⟩, ?_, ?_⟩, by rw [formVecOf, hp, hl]⟩
  · simp only [RawVecOk, Buf, hp, hc]
    exact ⟨hal, Or.inr ⟨hlo, by omega⟩⟩
  · rw [hp, hl]; exact hok
  · rw [hp, hl]
    rintro x ⟨i, hi, hx⟩ hb
    simp only [formVecBuf, hp, hc] at hb
    exact hsep i hi x hx hb

/-- The `Flushes` after `bytecode`. -/
def flBc (opcode : ℕ) : FlushesRust :=
  (({} : FlushesRust).stateStep 0 1).bytecode 0 14 opcode
    [colRust 2 0, colRust 3 0, colRust 4 0, constantRust 0, constantRust 0]

/-- After `bytecode`. -/
structure AtCols (s u : MachineState) : Prop extends Inv s u where
  pc : u.pc = 0x800055e4
  x9 : u.getReg .x9 = s.getReg .x12
  fl : FHeld s u (flBc (s.getReg .x11).toNat) (heapNext u)

/-- A block writing nothing keeps what is held. -/
theorem sameKeeps {s u v : MachineState} (hpre : FlushesArithPre s) (c : Inv s u)
    (hm : ∀ a, v.getMem a = u.getMem a) : Keeps s u v 0xa0000000 0 (heapNext u) := by
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  exact keeps_of hpre c (DFrame.of_same hm fun _ ↦ False) hn.ge (hn ▸ c.heap.hi) (Nat.le_refl _)
    (fun _ h ↦ h.elim) (Or.inl (by simp only [heapEnd]; decide)) (Or.inl rfl)

/-- A block writing `k` bytes from `lo` in the locals keeps what is held. -/
theorem blockKeeps {s u v : MachineState} (hpre : FlushesArithPre s) (c : Inv s u) {lo : Word}
    {k : Nat} (hm : MemFrame u v lo k) (hlo : (s.getReg .x2).toNat - 424 ≤ lo.toNat)
    (hk : lo.toNat + k ≤ (s.getReg .x2).toNat - 64) : Keeps s u v lo k (heapNext u) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hn : heapNext v = heapNext u := by
    simp only [heapNext]; rw [hm _ (by addr_omega [hnx, hsb, hlo, hk])]
  exact keeps_of hpre c hm.dframe hn.ge (hn ▸ c.heap.hi) (Nat.le_refl _) (fun _ h ↦ Or.inl h)
    (Or.inl (by addr_omega [hsb, hab, hlo, hk])) (by addr_omega [hsb, hlo, hk])

/-- At the copy into `B`: the five operands built. -/
structure AtCopy (s u : MachineState) (B : Word) : Prop extends Inv s u where
  pc : u.pc = 0x8000555c
  x9 : u.getReg .x9 = s.getReg .x12
  x18 : u.getReg .x18 = s.getReg .x11
  x19 : u.getReg .x19 = B
  bal : B.toNat % 8 = 0
  blo : heapNext s ≤ B.toNat
  bhi : B.toNat + 120 ≤ heapNext u
  fl : FHeld s u (({} : FlushesRust).stateStep 0 1) B.toNat
  b0 : Held u B (colRust 2 0) (B.toNat + 120) (heapNext u)
  b1 : Held u (s.getReg .x2 - 232) (colRust 3 0) (B.toNat + 120) (heapNext u)
  b2 : Held u (s.getReg .x2 - 208) (colRust 4 0) (B.toNat + 120) (heapNext u)
  b3 : Held u (s.getReg .x2 - 184) (constantRust 0) (B.toNat + 120) (heapNext u)
  b4 : Held u (s.getReg .x2 - 160) (constantRust 0) (B.toNat + 120) (heapNext u)

/-- The four operands built in the locals. -/
theorem operands (hC : ColSpec) (hT : TermSpec) {s u0 u : MachineState} {B : Word}
    (hpre : FlushesArithPre s) (hr : Reaches Image.code u0 u) (A : AtB s u B) :
    ∃ v, Reaches Image.code u0 v ∧ (AtCopy s v B ∨ Dead Image.code v) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have c := A.toInv
  have x2 := c.x2
  have hBal := A.bal
  have hBlo := A.blo
  have hBhi := A.bhi
  have hlo₀ := hpre.heap.lo
  -- `col(sp' + 248, o_b, 0)`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800054fc_spec A.pc trivial
  have k₁ := b800054fc_keeps h₁
  have hm₁ := b800054fc_mem_same h₁
  have c₁ := c.same hpre hm₁ fun r hr ↦ k₁ r (mem_of_mem hr _)
  have K₁ := sameKeeps hpre c hm₁
  have hn₁ : heapNext t₁ = heapNext u := by simp only [heapNext, hm₁]
  obtain ⟨t₂, hr₂, ⟨hpc₂, hp₂, c₂, hn₂, b₂, K₂⟩ | hd⟩ := colCall hC hpre c₁ (hr.trans hr₁)
    (b800054fc_pc h₁) (o := s.getReg .x2 - 232) (by rw [b800054fc_x10 h₁, c.x2]; rv_eval [])
    (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]) (Nat.le_refl _)
    (Or.inl (by addr_omega [hsb, hab]))
  swap
  · exact ⟨t₂, hr₂, Or.inr hd⟩
  rw [b800054fc_x11 h₁, b800054fc_x12 h₁] at b₂
  have sB : ∀ M, B.toNat + 24 ≤ M → Slot s M B := fun M hM ↦
    Or.inr ⟨by simp only [heapStart] at hlo₀ ⊢; omega, hM⟩
  have bB₂ := K₂.1 _ _ _ _ (K₁.1 _ _ _ _ A.b0 (by omega) (sB _ (by omega)) (Or.inr (Or.inl rfl)))
    (by omega) (sB _ (by omega)) (by addr_omega [hsb, hab, hBhi, c.heap.hi])
  -- `col(sp' + 272, o_c, 0)`
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80005510_spec
    (by rw [hpc₂, returnAddress_eq, b800054fc_x1 h₁]; decide) trivial
  have k₃ := b80005510_keeps h₃
  have hm₃ := b80005510_mem_same h₃
  have c₃ := c₂.same hpre hm₃ fun r hr ↦ k₃ r (mem_of_mem hr _)
  have K₃ := sameKeeps hpre c₂ hm₃
  have hn₃ : heapNext t₃ = heapNext t₂ := by simp only [heapNext, hm₃]
  obtain ⟨t₄, hr₄, ⟨hpc₄, hp₄, c₄, hn₄, b₄, K₄⟩ | hd⟩ := colCall hC hpre c₃ (hr₂.trans hr₃)
    (b80005510_pc h₃) (o := s.getReg .x2 - 208) (by rw [b80005510_x10 h₃, c₂.x2]; rv_eval [])
    (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]) (Nat.le_refl _)
    (Or.inl (by addr_omega [hsb, hab]))
  swap
  · exact ⟨t₄, hr₄, Or.inr hd⟩
  rw [b80005510_x11 h₃, b80005510_x12 h₃] at b₄
  have bB₄ := K₄.1 _ _ _ _ (K₃.1 _ _ _ _ bB₂ (by omega) (sB _ (by omega)) (Or.inr (Or.inl rfl)))
    (by omega) (sB _ (by omega)) (by addr_omega [hsb, hab, hBhi, c.heap.hi])
  have b₂₄ := K₄.1 _ _ _ _ (K₃.1 _ _ _ _ b₂ (by omega) (Or.inl (by addr_omega [hsb]))
    (Or.inr (Or.inl rfl))) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  -- `term(sp' + 296, One, ZERO)`
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80005524_spec
    (by rw [hpc₄, returnAddress_eq, b80005510_x1 h₃]; decide)
    (by rv_eval [c₄.x2]; valid_access (stackValid hpre) [hsb])
  have k₅ := b80005524_keeps h₅
  have hm₅ := b80005524_frame h₅ (by addr_omega [hsb, c₄.x2])
  rw [c₄.x2] at hm₅
  obtain ⟨c₅, hn₅⟩ := c₄.block hpre hm₅ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₅ r (mem_of_mem hr _)
  have K₅ := blockKeeps hpre c₄ hm₅ (by addr_omega [hsb]) (by addr_omega [hsb])
  obtain ⟨t₆, hr₆, ⟨hpc₆, hp₆, c₆, hn₆, b₆, K₆⟩ | hd⟩ := termCall hT hpre c₅ (hr₄.trans hr₅)
    (b80005524_pc h₅) (o := s.getReg .x2 - 184) (by rw [b80005524_x10 h₅, c₄.x2]; rv_eval [])
    (by addr_omega [hsb]) (by addr_omega [hsb]) (by rw [b80005524_x11 h₅, c₄.x2]; rv_eval [])
    (b80005524_x12 h₅) (by
      have := b80005524_m_x2_80 h₅; rw [c₄.x2] at this; rv_eval [] at this; exact this)
  swap
  · exact ⟨t₆, hr₆, Or.inr hd⟩
  have bB₆ := K₆.1 _ _ _ _ (K₅.1 _ _ _ _ bB₄ (by omega) (sB _ (by omega))
    (by addr_omega [hsb, hab, hBhi, c.heap.hi])) (by omega) (sB _ (by omega))
    (by addr_omega [hsb, hab, hBhi, c.heap.hi])
  have b₂₆ := K₆.1 _ _ _ _ (K₅.1 _ _ _ _ b₂₄ (by omega) (Or.inl (by addr_omega [hsb]))
    (by addr_omega [hsb])) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  have b₄₆ := K₆.1 _ _ _ _ (K₅.1 _ _ _ _ b₄ (by omega) (Or.inl (by addr_omega [hsb]))
    (by addr_omega [hsb])) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  -- `term(sp' + 320, One, ZERO)`
  obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80005544_spec
    (by rw [hpc₆, returnAddress_eq, b80005524_x1 h₅]; decide)
    (by rv_eval [c₆.x2]; valid_access (stackValid hpre) [hsb])
  have k₇ := b80005544_keeps h₇
  have hm₇ := b80005544_frame h₇ (by addr_omega [hsb, c₆.x2])
  rw [c₆.x2] at hm₇
  obtain ⟨c₇, hn₇⟩ := c₆.block hpre hm₇ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₇ r (mem_of_mem hr _)
  have K₇ := blockKeeps hpre c₆ hm₇ (by addr_omega [hsb]) (by addr_omega [hsb])
  obtain ⟨t₈, hr₈, ⟨hpc₈, hp₈, c₈, hn₈, b₈, K₈⟩ | hd⟩ := termCall hT hpre c₇ (hr₆.trans hr₇)
    (b80005544_pc h₇) (o := s.getReg .x2 - 160) (by rw [b80005544_x10 h₇, c₆.x2]; rv_eval [])
    (by addr_omega [hsb]) (by addr_omega [hsb]) (by rw [b80005544_x11 h₇, c₆.x2]; rv_eval [])
    (by rw [b80005544_x12 h₇, hp₆.reg .x20, b80005524_x20 h₅])
    (by have := b80005544_m_x2_80 h₇; rw [c₆.x2] at this; rv_eval [] at this; exact this)
  swap
  · exact ⟨t₈, hr₈, Or.inr hd⟩
  have bB₈ := K₈.1 _ _ _ _ (K₇.1 _ _ _ _ bB₆ (by omega) (sB _ (by omega))
    (by addr_omega [hsb, hab, hBhi, c.heap.hi])) (by omega) (sB _ (by omega))
    (by addr_omega [hsb, hab, hBhi, c.heap.hi])
  have b₂₈ := K₈.1 _ _ _ _ (K₇.1 _ _ _ _ b₂₆ (by omega) (Or.inl (by addr_omega [hsb]))
    (by addr_omega [hsb])) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  have b₄₈ := K₈.1 _ _ _ _ (K₇.1 _ _ _ _ b₄₆ (by omega) (Or.inl (by addr_omega [hsb]))
    (by addr_omega [hsb])) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  have b₆₈ := K₈.1 _ _ _ _ (K₇.1 _ _ _ _ b₆ (by omega) (Or.inl (by addr_omega [hsb]))
    (by addr_omega [hsb])) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  have fl₈ := K₈.2 _ _ (K₇.2 _ _ (K₆.2 _ _ (K₅.2 _ _ (K₄.2 _ _ (K₃.2 _ _ (K₂.2 _ _
    (K₁.2 _ _ A.fl (by omega)) (by omega)) (by omega)) (by omega)) (by omega)) (by omega))
    (by omega)) (by omega)
  have r₈ : ∀ r ∈ [Reg.x9, .x18, .x19], t₈.getReg r = u.getReg r := fun r hr ↦ by
    rw [hp₈ r (mem_of_mem hr _), k₇ r (mem_of_mem hr _), hp₆ r (mem_of_mem hr _),
      k₅ r (mem_of_mem hr _), hp₄ r (mem_of_mem hr _), k₃ r (mem_of_mem hr _),
      hp₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  exact ⟨t₈, hr₈, Or.inl {
    toInv := c₈
    pc := by rw [hpc₈, returnAddress_eq, b80005544_x1 h₇]; decide
    x9 := by rw [r₈ .x9 (by decide), A.x9]
    x18 := by rw [r₈ .x18 (by decide), A.x18]
    x19 := by rw [r₈ .x19 (by decide), A.x19]
    bal := hBal
    blo := hBlo
    bhi := by omega
    fl := fl₈
    b0 := heldMono bB₈ (Nat.le_refl _) (by omega)
    b1 := heldMono b₂₈ (by omega) (by omega)
    b2 := heldMono b₄₈ (by omega) (by omega)
    b3 := heldMono b₆₈ (by omega) (by omega)
    b4 := heldMono b₈ (by omega) (by omega) }⟩

/-- The copy into `B` and `bytecode`. -/
theorem copyOps (hBc : BytecodeSpec) {s u0 t₈ : MachineState} {B : Word}
    (hpre : FlushesArithPre s) (hr : Reaches Image.code u0 t₈) (A : AtCopy s t₈ B) :
    ∃ v, Reaches Image.code u0 v ∧ (AtCols s v ∨ Dead Image.code v) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have c₈ := A.toInv
  have hBal := A.bal
  have hBlo := A.blo
  have hBhi := A.bhi
  have hlo₀ := hpre.heap.lo
  have x2₈ := c₈.x2
  have x19₈ := A.x19
  have hhu := c₈.heap.hi
  have hBv : ValidMemRange B 15 := validMemRange_of hBal (Or.inl ⟨by
    simp only [heapStart] at hlo₀; omega, by simp only [heapEnd] at hhu; omega⟩)
  obtain ⟨t₉, hr₉, h₉⟩ := Sym.BlockSpec.reaches b8000555c_spec A.pc (by
      rv_eval [x2₈, x19₈]
      and_intros <;> first
        | valid_access (stackValid hpre) [hsb]
        | valid_access hBv [hBal, hBhi, hhu]
        | addr_omega [hsb, hab, hBhi, hhu])
  have k₉ := b8000555c_keeps h₉
  have hf₉ : DFrame t₈ t₉ fun y ↦ Within y (B + 24) 96 ∨ Within y (s.getReg .x2 - 424) 24 :=
    (h₉.byteFrame (w := fun y ↦ Within y (B + 24) 96 ∨ Within y (s.getReg .x2 - 424) 24) (by
      rv_eval [x2₈, x19₈]
      and_intros <;> first
        | (intro i hi; exact Or.inl (by addr_omega [hi, hBal, hBhi, hhu]))
        | (intro i hi; exact Or.inr (by addr_omega [hi, hsb]))
        | addr_omega [hsb, hBal, hBhi, hhu])).dframe
  have hn₉ : heapNext t₉ = heapNext t₈ := by
    have : t₉.getMem nextAddr = t₈.getMem nextAddr := hf₉.getMem_of (fun x hx hw ↦ by
      rcases hw with h | h <;> addr_omega [hx, h, hsb, hnx, hBhi, hhu]) (by decide)
    simp only [heapNext, this]
  have hu₉ : heapNext t₈ ≤ heapNext t₉ := by omega
  have hW₉ (x : Word) (l h : Nat) (hl : B.toNat + 120 ≤ l) (hh : h ≤ heapNext t₈)
      (hw : Within x (B + 24) 96 ∨ Within x (s.getReg .x2 - 424) 24) :
      l ≤ x.toNat → h ≤ x.toNat := by
    have := c₈.heap.hi
    rcases hw with h | h
    · intro h'; addr_omega [h, h', hl, hBal, hBhi, hhu]
    · intro _; addr_omega [h, hsb, hab, this, hh]
  have c₉ := c₈.step hpre hf₉ (fun x hx ↦ by
    rcases hx with h | h
    · exact Or.inr (Or.inr ⟨by addr_omega [h, hBlo, hBhi, hhu], by
        addr_omega [h, hBhi, hu₉]⟩)
    · exact Or.inl (by addr_omega [h, hsb])) ⟨hn₉ ▸ c₈.heap.lo, hn₉ ▸ c₈.heap.hi⟩ hn₉.ge
    fun r hr ↦ k₉ r (mem_of_mem hr _)
  have fl₉ := A.fl.keep hf₉ c₈.heap hn₉.ge (fun x hw _ ↦ by
      have := c₈.heap.hi
      rcases hw with h | h <;> addr_omega [h, hsb, hab, hBhi, hhu, this])
    (fun x hx hw ↦ by rcases hw with h | h <;> addr_omega [hx, h, hsb, hab, hBhi, hhu])
    (by addr_omega [hsb])
  have bB₉ := keepHeld A.b0 hf₉ c₈.heap hn₉.ge (fun x hw hl ↦ by
      have := c₈.heap.hi
      rcases hw with h | h <;> addr_omega [h, hl, hsb, hab, hBhi, hhu, this])
    (fun x hx hw ↦ by rcases hw with h | h <;> addr_omega [hx, h, hsb, hab, hBhi, hhu])
    (by addr_omega [hBhi, hhu])
  have m₁ := moveHeld A.b1 hf₉ c₈.heap hn₉.ge (fun x ↦ hW₉ x _ _ (Nat.le_refl _) (Nat.le_refl _))
    (by have := b8000555c_m_x19_24 h₉; rw [x19₈, x2₈] at this; rv_eval [] at this ⊢; exact this)
    (by have := b8000555c_m_x19_32 h₉; rw [x19₈, x2₈] at this; rv_eval [] at this ⊢; exact this)
    (by have := b8000555c_m_x19_40 h₉; rw [x19₈, x2₈] at this; rv_eval [] at this ⊢; exact this)
  have m₂ := moveHeld A.b2 hf₉ c₈.heap hn₉.ge (fun x ↦ hW₉ x _ _ (Nat.le_refl _) (Nat.le_refl _))
    (by have := b8000555c_m_x19_48 h₉; rw [x19₈, x2₈] at this; rv_eval [] at this ⊢; exact this)
    (by have := b8000555c_m_x19_56 h₉; rw [x19₈, x2₈] at this; rv_eval [] at this ⊢; exact this)
    (by have := b8000555c_m_x19_64 h₉; rw [x19₈, x2₈] at this; rv_eval [] at this ⊢; exact this)
  have m₃ := moveHeld A.b3 hf₉ c₈.heap hn₉.ge (fun x ↦ hW₉ x _ _ (Nat.le_refl _) (Nat.le_refl _))
    (by have := b8000555c_m_x19_72 h₉; rw [x19₈, x2₈] at this; rv_eval [] at this ⊢; exact this)
    (by have := b8000555c_m_x19_80 h₉; rw [x19₈, x2₈] at this; rv_eval [] at this ⊢; exact this)
    (by have := b8000555c_m_x19_88 h₉; rw [x19₈, x2₈] at this; rv_eval [] at this ⊢; exact this)
  have m₄ := moveHeld A.b4 hf₉ c₈.heap hn₉.ge (fun x ↦ hW₉ x _ _ (Nat.le_refl _) (Nat.le_refl _))
    (by have := b8000555c_m_x19_96 h₉; rw [x19₈, x2₈] at this; rv_eval [] at this ⊢; exact this)
    (by have := b8000555c_m_x19_104 h₉; rw [x19₈, x2₈] at this; rv_eval [] at this ⊢; exact this)
    (by have := b8000555c_m_x19_112 h₉; rw [x19₈, x2₈] at this; rv_eval [] at this ⊢; exact this)
  have hv := formVec_of (t := t₉) (v := s.getReg .x2 - 424) (B := B) (n := 5) (by decide)
    (by have := b8000555c_m_x2_56 h₉; rw [x2₈] at this; rv_eval [] at this ⊢; exact this)
    (by have := b8000555c_m_x2_64 h₉; rw [x2₈, x19₈] at this; rv_eval [] at this ⊢; exact this)
    (by have := b8000555c_m_x2_72 h₉; rw [x2₈] at this; rv_eval [] at this ⊢; exact this)
    hBal (by simp only [heapStart] at hlo₀ ⊢; omega) (by omega)
    (fun i hi ↦ by
      rcases i with _ | _ | _ | _ | _ | i
      · simpa using bB₉.ok
      · exact m₁.ok
      · exact m₂.ok
      · exact m₃.ok
      · exact m₄.ok
      · omega)
    (fun i hi x hx hw ↦ by
      have hb : B.toNat + 120 ≤ x.toNat := by
        rcases i with _ | _ | _ | _ | _ | i
        · exact (bB₉.buf x (by simpa using hx)).1
        · exact (m₁.buf x hx).1
        · exact (m₂.buf x hx).1
        · exact (m₃.buf x hx).1
        · exact (m₄.buf x hx).1
        · omega
      simp only [Within] at hw; omega)
  have hlist : formsAt t₉ B 5 =
      [colRust 2 0, colRust 3 0, colRust 4 0, constantRust 0, constantRust 0] := by
    have e0 : B + BitVec.ofNat 64 (24 * 0) = B := by simp
    show [formOf t₉ (B + BitVec.ofNat 64 (24 * 0)), formOf t₉ (B + 24), formOf t₉ (B + 48),
      formOf t₉ (B + 72), formOf t₉ (B + 96)] = _
    rw [e0, bB₉.val, m₁.val, m₂.val, m₃.val, m₄.val]
  have x10₉ : t₉.getReg .x10 = s.getReg .x2 - 472 := by rw [b8000555c_x10 h₉, x2₈]; rv_eval []
  have x13₉ : t₉.getReg .x13 = s.getReg .x2 - 424 := by rw [b8000555c_x13 h₉, x2₈]; rv_eval []
  have hp9 : vecPtr t₉ (s.getReg .x2 - 424) = B := by
    simp only [vecPtr]
    have := b8000555c_m_x2_64 h₉; rw [x2₈, x19₈] at this; rv_eval [] at this ⊢; exact this
  have hl9 : vecLen t₉ (s.getReg .x2 - 424) = 5 := by
    simp only [vecLen]
    have := b8000555c_m_x2_72 h₉; rw [x2₈] at this; rv_eval [] at this ⊢; exact this
  have hh₉ := c₉.heap.hi
  have hbp : BytecodePre t₉ := {
    toFlushesPre := flushesPre hpre c₉ fl₉ x10₉ (by decide) (by decide) (by decide)
    ops := by rw [x13₉]; valid_sub (stackValid hpre) [hsb]
    opsOk := by rw [x13₉]; exact hv.1
    opsFree := by rw [x13₉]; addr_omega [hsb, hab, hnx]
    opsStack := by
      rw [x13₉]; simp only [stackLo, bytecodeStack, countedStack, colStack, powStack,
        Contracts.mulStack]; rw [c₉.x2]; addr_omega [hsb]
    opsBuf := by
      rw [x13₉, hp9, hl9]
      have e5 : (5 : Word).toNat = 5 := rfl
      refine ⟨Or.inl ?_, by addr_omega [hBhi, hhu]⟩
      simp only [heapNext] at hu₉ hBhi ⊢; omega
    opsBufStack := by
      rw [x13₉, hp9, hl9]; simp only [stackLo, bytecodeStack, countedStack, colStack, powStack,
        Contracts.mulStack]; rw [c₉.x2]; addr_omega [hsb, hab, hBhi, hhu] }
  obtain ⟨v, hrv, ⟨hpcv, hpresv, hgv, hvalv⟩ | hd⟩ := hBc.call (hr.trans hr₉) (b8000555c_pc h₉) hbp
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  rw [x10₉] at hgv hvalv
  obtain ⟨cv, fv⟩ := afterGrow hpre c₉ fl₉ (by omega) (by decide) hpresv hgv
  rw [hvalv, fl₉.val, x13₉, hv.2, hlist, b8000555c_x11 h₉, b8000555c_x12 h₉, A.x18] at fv
  exact ⟨v, hrv, Or.inl {
    toInv := cv
    pc := by rw [hpcv, returnAddress_eq, b8000555c_x1 h₉]; decide
    x9 := by rw [hpresv.reg .x9, k₉ .x9 (by decide), A.x9]
    fl := fv }⟩

end Rv64Verifier.Layout.Arith
