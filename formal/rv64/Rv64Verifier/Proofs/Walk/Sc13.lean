import Rv64Verifier.Proofs.Walk.Md13

/-!
# `walk`: `offsets` (R13), the scatter loop

From `f₀` at `0x80003304`: `x9` walks `blocks` (`G`), `x19` the stacked offsets (`SO`, the words
`sol`), each round storing `sol[j]` at `offsets[blocks[j]]` (`OF`, zero at `f₀`); `x10` and `x25`
count down from `808`. `scLoop` reaches `0x80003334` with `OF` holding `scat sol 101`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The first `j` stacked offsets scattered. -/
def scat (sol : List Word) (j : Nat) : List Word :=
  (((blk 165).zip sol).take j).foldl (fun o co ↦ o.set co.1 co.2) (List.replicate 165 0#64)

theorem scat_length (sol : List Word) (j : Nat) : (scat sol j).length = 165 := by
  unfold scat
  generalize ((blk 165).zip sol).take j = l
  suffices ∀ o : List Word, o.length = 165 → (l.foldl (fun o co ↦ o.set co.1 co.2) o).length = 165 from
    this _ (List.length_replicate ..)
  induction l with
  | nil => intro o h; exact h
  | cons x l ih => intro o h; exact ih _ (by rw [List.length_set]; exact h)

theorem scat_succ {sol : List Word} (hs : sol.length = 101) {j : Nat} (hj : j < 101) :
    scat sol (j + 1) = (scat sol j).set ((blk 165).getD j 0) (sol.getD j 0) := by
  have hz : ((blk 165).zip sol)[j]? = some ((blk 165).getD j 0, sol.getD j 0) := by
    rw [List.getElem?_zip_eq_some]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by rw [blk_165_length]; exact hj),
      List.getElem?_eq_getElem (by rw [hs]; exact hj)]
    simp
  simp only [scat, List.take_add_one, hz, Option.toList_some, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

theorem getD_set_word (l : List Word) {i : Nat} (hi : i < l.length) (v : Word) (c : Nat) :
    (l.set i v).getD c 0 = if c = i then v else l.getD c 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs with h1 h2 h2
  · subst h1; simp
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rfl

theorem scat_full {sol : List Word} (hs : sol.length = 101) :
    scat sol 101 = ((blk 165).zip sol).foldl (fun o co ↦ o.set co.1 co.2) (List.replicate 165 0#64) := by
  unfold scat
  rw [List.take_of_length_le (by simp [blk_165_length, hs])]

/-- The registers the loop leaves. -/
def scRegs : List Reg := [.x2, .x8, .x18, .x20, .x21, .x22, .x23, .x24, .x26]

/-- At `0x80003304`, `j` offsets scattered. -/
structure Sc13 (f₀ u : MachineState) (G SO OF : Word) (sol : List Word) (j : Nat) : Prop where
  pc : u.pc = 0x80003304
  lt : j < 101
  x9 : u.getReg .x9 = G + BitVec.ofNat 64 (8 * j)
  x19 : u.getReg .x19 = SO + BitVec.ofNat 64 (8 * j)
  x10 : u.getReg .x10 = BitVec.ofNat 64 (808 - 8 * j)
  x25 : u.getReg .x25 = BitVec.ofNat 64 (808 - 8 * j)
  regs : ∀ r ∈ scRegs, u.getReg r = f₀.getReg r
  fr : Layout.DFrame f₀ u fun a ↦ Within a OF (8 * 165)
  vals : ∀ c < 165, u.getMem (OF + BitVec.ofNat 64 (8 * c)) = (scat sol j).getD c 0

theorem ofNat_sub8 {n : Nat} (h : 8 ≤ n) (h2 : n < 2 ^ 64) :
    BitVec.ofNat 64 n - 8 = BitVec.ofNat 64 (n - 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have : (8 : Word).toNat = 8 := rfl
  omega

section
variable {f₀ : MachineState} {G SO OF : Word} {sol : List Word}
  (hG : G.toNat % 8 = 0) (hSO : SO.toNat % 8 = 0) (hOF : OF.toNat % 8 = 0)
  (hG1 : 0x20000000 ≤ G.toNat) (hGS : G.toNat + 808 ≤ SO.toNat) (hSF : SO.toNat + 808 ≤ OF.toNat)
  (hF2 : OF.toNat + 8 * 165 ≤ 0x78000000) (hs : sol.length = 101) (x24 : f₀.getReg .x24 = 165) (x20 : f₀.getReg .x20 = OF)
  (gv : ∀ i < 101, f₀.getMem (G + BitVec.ofNat 64 (8 * i)) = BitVec.ofNat 64 ((blk 165).getD i 0))
  (sv : ∀ i < 101, f₀.getMem (SO + BitVec.ofNat 64 (8 * i)) = sol.getD i 0)
include hG hSO hOF hG1 hGS hSF hF2 hs x24 x20 gv sv

set_option maxRecDepth 8192 in
/-- One round. -/
theorem scBody {u : MachineState} {j : Nat} (h : Sc13 f₀ u G SO OF sol j) :
    ∃ t, Reaches Image.code u t ∧ (∀ r ∈ scRegs, t.getReg r = f₀.getReg r) ∧
      Layout.DFrame f₀ t (fun a ↦ Within a OF (8 * 165)) ∧
      (∀ c < 165, t.getMem (OF + BitVec.ofNat 64 (8 * c)) = (scat sol (j + 1)).getD c 0) ∧
      ((j + 1 < 101 ∧ t.pc = 0x80003304 ∧ t.getReg .x9 = G + BitVec.ofNat 64 (8 * (j + 1)) ∧
        t.getReg .x19 = SO + BitVec.ofNat 64 (8 * (j + 1)) ∧
        t.getReg .x10 = BitVec.ofNat 64 (808 - 8 * (j + 1)) ∧
        t.getReg .x25 = BitVec.ofNat 64 (808 - 8 * (j + 1))) ∨ (j + 1 = 101 ∧ t.pc = 0x80003334)) := by
  have hj := h.lt
  have hbl := blk_165_lt j hj
  have x20u : u.getReg .x20 = OF := (h.regs .x20 (by decide)).trans x20
  have x24u : u.getReg .x24 = 165 := (h.regs .x24 (by decide)).trans x24
  have h165 : (165 : Word).toNat = 165 := rfl
  have gj : u.getMem (G + BitVec.ofNat 64 (8 * j)) = BitVec.ofNat 64 ((blk 165).getD j 0) := by
    rw [h.fr.getMem_of (fun x hx hw ↦ by
      simp only [Within] at hx hw; addr_omega [hx, hw, hGS, hSF, hj, hG1, hF2])
      (by addr_omega [hG1, hGS, hSF, hF2, hj])]
    exact gv j hj
  have sj : u.getMem (SO + BitVec.ofNat 64 (8 * j)) = sol.getD j 0 := by
    rw [h.fr.getMem_of (fun x hx hw ↦ by
      simp only [Within] at hx hw; addr_omega [hx, hw, hGS, hSF, hj, hG1, hF2])
      (by addr_omega [hG1, hGS, hSF, hF2, hj])]
    exact sv j hj
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80003304_spec h.pc (by rv_eval [])
  have pc₁ := b80003304_pc_not_taken h₁ (by
    rw [h.x10]; intro he; have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat] at this; have h0 : (0 : Word).toNat = 0 := rfl; omega)
  have m₁ := b80003304_mem_same h₁
  have k₁ := b80003304_keeps h₁
  have x9₁ : u₁.getReg .x9 = G + BitVec.ofNat 64 (8 * j) := by rw [k₁ .x9 (by decide)]; exact h.x9
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80003308_spec pc₁ (by
    rv_eval [x9₁]; simp only [Sym.validAccess_eight]; addr_omega [hG, hG1, hGS, hSF, hF2, hj])
  have pc₂ := b80003308_pc_not_taken h₂ (by
    rw [x9₁, m₁, gj, k₁ .x24 (by decide), x24u, BitVec.toNat_ofNat, h165]; omega)
  have m₂ := b80003308_mem_same h₂
  have k₂ := b80003308_keeps h₂
  have x11₂ : u₂.getReg .x11 = BitVec.ofNat 64 ((blk 165).getD j 0) := by
    rw [b80003308_x11 h₂, x9₁, m₁, gj]
  have x20₂ : u₂.getReg .x20 = OF := by rw [k₂ .x20 (by decide), k₁ .x20 (by decide)]; exact x20u
  have x19₂ : u₂.getReg .x19 = SO + BitVec.ofNat 64 (8 * j) := by
    rw [k₂ .x19 (by decide), k₁ .x19 (by decide)]; exact h.x19
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80003310_spec pc₂ (by
    rv_eval [x20₂, x11₂, x19₂, ofNat_mul8]; simp only [Sym.validAccess_eight]
    and_intros <;> addr_omega [hOF, hSO, hG1, hGS, hSF, hF2, hj, hbl])
  have fr₃ : Layout.DFrame u₂ u₃ fun a ↦ Within a (OF + BitVec.ofNat 64 (8 * (blk 165).getD j 0)) 8 :=
    exL h₃ (by
      rv_eval [x20₂, x11₂, ofNat_mul8]; simp only [Within]
      addr_omega [hOF, hG1, hGS, hSF, hF2, hbl])
  have k₃ := b80003310_keeps h₃
  have st : u₃.getMem (OF + BitVec.ofNat 64 (8 * (blk 165).getD j 0)) = sol.getD j 0 := by
    have := b80003310_m0 h₃
    rw [x20₂, x11₂, ofNat_mul8, x19₂, m₂, m₁, sj] at this
    exact this
  have hsl := scat_length sol j
  refine ⟨u₃, hr₁.trans (hr₂.trans hr₃), fun r hr ↦ ?_, ?_, fun c hc ↦ ?_, ?_⟩
  · rw [← h.regs r hr, k₃ r (by revert r hr; decide), k₂ r (by revert r hr; decide),
      k₁ r (by revert r hr; decide)]
  · intro a ha hw8
    rw [fr₃ a (fun x hx h' ↦ ha x hx (by simp only [Within] at h' ⊢; addr_omega [h', hOF, hG1, hGS, hSF, hF2, hbl]))
      hw8, m₂, m₁, h.fr a ha hw8]
  · rw [scat_succ hs hj, getD_set_word _ (by rw [hsl]; exact hbl)]
    split_ifs with hcb
    · subst hcb; exact st
    · rw [fr₃.getMem_of (fun x hx hw ↦ by
          simp only [Within] at hx hw; addr_omega [hx, hw, hcb, hc, hbl, hOF, hG1, hGS, hSF, hF2])
        (by addr_omega [hc, hG1, hGS, hSF, hF2]), m₂, m₁]
      exact h.vals c hc
  · have e25 : u₂.getReg .x25 = BitVec.ofNat 64 (808 - 8 * j) := by
      rw [k₂ .x25 (by decide), k₁ .x25 (by decide)]; exact h.x25
    have e10 : u₂.getReg .x10 = BitVec.ofNat 64 (808 - 8 * j) := by
      rw [k₂ .x10 (by decide), k₁ .x10 (by decide)]; exact h.x10
    have es : BitVec.ofNat 64 (808 - 8 * j) - 8 = BitVec.ofNat 64 (808 - 8 * (j + 1)) := by
      rw [ofNat_sub8 (by omega) (by omega)]; congr 1
    by_cases hj1 : j + 1 < 101
    · refine Or.inl ⟨hj1, b80003310_pc_taken h₃ (by
        rw [e25, es]; intro he; have := congrArg BitVec.toNat he
        rw [BitVec.toNat_ofNat] at this; have h0 : (0 : Word).toNat = 0 := rfl; omega), ?_, ?_, ?_, ?_⟩
      · rw [b80003310_x9 h₃, k₂ .x9 (by decide), x9₁]; apply BitVec.eq_of_toNat_eq
        addr_omega [hG1, hGS, hSF, hF2, hj]
      · rw [b80003310_x19 h₃, x19₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hG1, hGS, hSF, hF2, hj]
      · rw [b80003310_x10 h₃, e10, es]
      · rw [b80003310_x25 h₃, e25, es]
    · refine Or.inr ⟨by omega, b80003310_pc_not_taken h₃ (by
        rw [e25, es, show 808 - 8 * (j + 1) = 0 by omega]; rfl)⟩

theorem scLoop : ∀ d j u, 100 - j = d → Sc13 f₀ u G SO OF sol j → ∃ t, Reaches Image.code u t ∧
    t.pc = 0x80003334 ∧ (∀ r ∈ scRegs, t.getReg r = f₀.getReg r) ∧
    Layout.DFrame f₀ t (fun a ↦ Within a OF (8 * 165)) ∧
    ∀ c < 165, t.getMem (OF + BitVec.ofNat 64 (8 * c)) = (scat sol 101).getD c 0 := by
  intro d
  induction d with
  | zero =>
    intro j u hd h
    obtain ⟨t, hr, rg, fr, vals, ⟨hj1, -⟩ | ⟨hj1, pct⟩⟩ :=
      scBody hG hSO hOF hG1 hGS hSF hF2 hs x24 x20 gv sv h
    · omega
    · rw [hj1] at vals; exact ⟨t, hr, pct, rg, fr, vals⟩
  | succ d ih =>
    intro j u hd h
    obtain ⟨t, hr, rg, fr, vals, ⟨hj1, pct, x9, x19, x10, x25⟩ | ⟨hj1, -⟩⟩ :=
      scBody hG hSO hOF hG1 hGS hSF hF2 hs x24 x20 gv sv h
    · obtain ⟨t', hr', ht'⟩ := ih (j + 1) t (by omega) ⟨pct, hj1, x9, x19, x10, x25, rg, fr, vals⟩
      exact ⟨t', hr.trans hr', ht'⟩
    · omega

end

end Rv64Verifier.Proofs.Walk
