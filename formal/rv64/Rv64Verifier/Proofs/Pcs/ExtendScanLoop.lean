import Rv64Verifier.Proofs.Pcs.ExtendScan

/-!
# `Vec<StackClaim>::extend_desugared`: the scan's steps

`head_step` from `Head` and `skip_loop` from `Skip`, each to a trap, `Exit` or the next `Push`.
-/

namespace Rv64Verifier.Proofs.Pcs.Extend
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Transcript Rv64Verifier.Pcs
  Rv64Verifier.PcsContracts Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F37
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem keeps_sub {u v : MachineState} {l : List Reg} (k : ∀ r ∈ l, v.getReg r = u.getReg r)
    (hs : [Reg.x8, .x9, .x19, .x20, .x21, .x22, .x23, .x24] ⊆ l) :
    ∀ r ∈ [Reg.x8, .x9, .x19, .x20, .x21, .x22, .x23, .x24], v.getReg r = u.getReg r :=
  fun r hr ↦ k r (hs hr)

theorem clAt_succ (s : MachineState) (j : Nat) : clAt s j + 56 = clAt s (j + 1) := by
  simp only [clAt, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have : (56 : Word).toNat = 56 := rfl
  rw [this]
  omega

/-- Claim `j`'s placement, `none`: the claim is skipped. -/
theorem skip_none {s : MachineState} {j : Nat} (hc : colAt s j < placementsLen s)
    (hb : s.getMem (plAt s j) &&& 1 = 0) : onStackS s (columnClaimAt s (clAt s j)) = none :=
  onStack_none s hc hb

/-- After claim `j`, at `0x80009ca0`: the end, or the loop. -/
theorem after {s u : MachineState} {j : Nat} (hpre : ExtendPre s) (hI : Inv s u (j + 1))
    (hj : j < itCount s) (hpc : u.pc = 0x80009ca0) (hx12 : u.getReg .x12 = clAt s (j + 1))
    (hx10 : u.getReg .x10 = s.getMem (itLayout s + 112)) (hx11 : u.getReg .x11 = placementsPtr s) :
    ∃ v, Reaches Image.code u v ∧ (Exit s v ∨ Skip s v (j + 1)) := by
  have hf := facts hpre (by omega)
  obtain ⟨t, hr, h⟩ := Sym.BlockSpec.reaches b80009ca0_spec hpc (by rv_eval [])
  have k := b80009ca0_keeps h
  have hI' := hI.congr (b80009ca0_mem_same h) (k .x2 (by decide)) (keeps_sub k (by decide))
  refine ⟨t, hr, ?_⟩
  by_cases he : j + 1 = itCount s
  · left
    refine ⟨he ▸ hI', b80009ca0_pc_taken h ?_⟩
    rw [hx12, hI.x19]
    exact (clAt_end hf (by omega)).mpr he
  · right
    refine ⟨hI', b80009ca0_pc_not_taken h ?_, (k .x12 (by decide)).trans hx12,
      (k .x10 (by decide)).trans hx10, (k .x11 (by decide)).trans hx11, by omega⟩
    rw [hx12, hI.x19]
    exact fun h' ↦ he ((clAt_end hf (by omega)).mp h')

theorem skip_loop {s : MachineState} (hpre : ExtendPre s) : ∀ n j u, itCount s - j ≤ n →
    Skip s u j →
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ Exit s v ∨ ∃ k, j ≤ k ∧ Push s v k) := by
  intro n
  induction n with
  | zero => intro j u hn hs; have := hs.lt; omega
  | succ n ih =>
  intro j u hn hs
  have hI := hs.inv
  have hj := hs.lt
  have hf := facts hpre (by omega)
  have hCb := Region.bounds hf.claims
  have rC := rd_col hpre hf hI hj
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80009ca4_spec hs.pc (by
    rv_eval [hs.x12]
    exact Region.valid hf.claims (by addr_omega [hCb, hj]) (by addr_omega [hCb, hj])
      (by addr_omega [hCb, hj]))
  have k₁ := b80009ca4_keeps h₁
  have m₁ := b80009ca4_mem_same h₁
  have x13₁ : t₁.getReg .x13 = s.getMem (clAt s j + 24) := by rw [b80009ca4_x13 h₁, hs.x12, rC]
  by_cases hcol : colAt s j < placementsLen s
  swap
  · refine ⟨t₁, hr₁, Or.inl (dead_of_fetch ?_)⟩
    rw [b80009ca4_pc_taken h₁ (by
      rw [hs.x10, hs.x12, rC]; simp only [colAt, placementsLen] at hcol; omega)]
    exact htrap
  have pc₁ := b80009ca4_pc_not_taken h₁ (by rw [hs.x10, hs.x12, rC]; exact hcol)
  have hPR := pl_region hpre hcol
  have hPb := Region.bounds hPR
  have rP := rd_pl hpre hI hcol
  have hI₁ := hI.congr m₁ (k₁ .x2 (by decide)) (keeps_sub k₁ (by decide))
  have hA : t₁.getReg .x11 + (t₁.getReg .x13 * 16 + t₁.getReg .x13 * 8) = plAt s j := by
    rw [k₁ .x11 (by decide), hs.x11, x13₁, pl_eq]
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80009cac_spec pc₁ (by
    rv_eval [hA]
    exact Region.valid hPR (by simp only [plAt]; addr_omega [hPb, hcol])
      (by simp only [plAt]; addr_omega [hPb, hcol]) (by simp only [plAt]; addr_omega [hPb, hcol]))
  have k₂ := b80009cac_keeps h₂
  have hI₂ := hI₁.congr (b80009cac_mem_same h₂) (k₂ .x2 (by decide)) (keeps_sub k₂ (by decide))
  have hbitE : t₁.getMem (t₁.getReg .x11 + (t₁.getReg .x13 * 16 + t₁.getReg .x13 * 8)) =
      s.getMem (plAt s j) := by
    rw [hA, m₁, rP]
  have x12₂ : t₂.getReg .x12 = clAt s j := (k₂ .x12 (by decide)).trans ((k₁ .x12 (by decide)).trans hs.x12)
  by_cases hbit : s.getMem (plAt s j) &&& 1 = 0
  · have pc₂ := b80009cac_pc_not_taken h₂ (by rw [hbitE]; exact hbit)
    have hI₂' := hI₂.skip hj (skip_none hcol hbit)
    obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80009cc8_spec pc₂ (by rv_eval [])
    have k₃ := b80009cc8_keeps h₃
    have hI₃ := hI₂'.congr (b80009cc8_mem_same h₃) (k₃ .x2 (by decide)) (keeps_sub k₃ (by decide))
    have x19₂ : t₂.getReg .x19 = itEnd s := hI₂.x19
    by_cases he : j + 1 = itCount s
    · have pc₃ := b80009cc8_pc_not_taken h₃ (by
        rw [x12₂, x19₂, clAt_succ]; exact (clAt_end hf (by omega)).mpr he)
      obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80009cd0_spec pc₃ (by rv_eval [])
      have k₄ := b80009cd0_keeps h₄
      have hI₄ := hI₃.congr (b80009cd0_mem_same h₄) (k₄ .x2 (by decide)) (keeps_sub k₄ (by decide))
      exact ⟨t₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr (Or.inl ⟨he ▸ hI₄, b80009cd0_pc h₄⟩)⟩
    · have pc₃ := b80009cc8_pc_taken h₃ (by
        rw [x12₂, x19₂, clAt_succ]; exact fun h' ↦ he ((clAt_end hf (by omega)).mp h'))
      have hs₃ : Skip s t₃ (j + 1) := ⟨hI₃, pc₃,
        by rw [b80009cc8_x12 h₃, x12₂, clAt_succ],
        by rw [k₃ .x10 (by decide), k₂ .x10 (by decide), k₁ .x10 (by decide), hs.x10],
        by rw [k₃ .x11 (by decide), k₂ .x11 (by decide), k₁ .x11 (by decide), hs.x11], by omega⟩
      obtain ⟨v, hr, hv⟩ := ih (j + 1) t₃ (by omega) hs₃
      refine ⟨v, hr₁.trans (hr₂.trans (hr₃.trans hr)), ?_⟩
      rcases hv with hv | hv | ⟨k, hk, hv⟩
      · exact Or.inl hv
      · exact Or.inr (Or.inl hv)
      · exact Or.inr (Or.inr ⟨k, by omega, hv⟩)
  · have pc₂ := b80009cac_pc_taken h₂ (by rw [hbitE]; exact hbit)
    obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80009cd4_spec pc₂ (by rv_eval [])
    have k₃ := b80009cd4_keeps h₃
    have hI₃ := hI₂.congr (b80009cd4_mem_same h₃) (k₃ .x2 (by decide)) (keeps_sub k₃ (by decide))
    refine ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inr (Or.inr ⟨j, Nat.le_refl _, hI₃, b80009cd4_pc h₃,
      by rw [b80009cd4_x18 h₃, x12₂], by rw [b80009cd4_x25 h₃, x12₂, clAt_succ],
      by rw [k₃ .x13 (by decide), b80009cac_x13 h₂, hA], hcol, hbit, hj⟩)⟩

theorem head_step {s u : MachineState} {j : Nat} (hpre : ExtendPre s) (hh : Head s u j) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ Exit s v ∨ ∃ k, j ≤ k ∧ Push s v k) := by
  have hI := hh.inv
  have hj := hh.lt
  have hf := facts hpre (by omega)
  have hCb := Region.bounds hf.claims
  have hLb := Region.bounds hf.layout
  have hx25 := hh.x25
  have hx20 := hI.x20
  have rC := rd_col hpre hf hI hj
  have r112 := rd_layout hpre hf hI (o := 112) (by decide)
  have r104 : u.getMem (itLayout s + 104) = placementsPtr s := rd_layout hpre hf hI (by decide)
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80009c64_spec hh.pc (by
    rv_eval [hx25, hx20]
    and_intros
    · exact Region.valid hf.claims (by addr_omega [hCb, hj]) (by addr_omega [hCb, hj])
        (by addr_omega [hCb, hj])
    · exact Region.valid hf.layout (by addr_omega [hLb]) (by addr_omega [hLb]) (by addr_omega [hLb]))
  have k₁ := b80009c64_keeps h₁
  have m₁ := b80009c64_mem_same h₁
  have x12₁ := b80009c64_x12 h₁
  rw [hx25, rC] at x12₁
  by_cases hcol : colAt s j < placementsLen s
  swap
  · refine ⟨t₁, hr₁, Or.inl (dead_of_fetch ?_)⟩
    rw [b80009c64_pc_taken h₁ (by
      rw [hx20, hx25, r112, rC]; simp only [colAt, placementsLen] at hcol; omega)]
    exact htrap
  have pc₁ := b80009c64_pc_not_taken h₁ (by
    rw [hx20, hx25, r112, rC]; simp only [colAt, placementsLen] at hcol; exact hcol)
  have hPR := pl_region hpre hcol
  have hPb := Region.bounds hPR
  have rP := rd_pl hpre hI hcol
  have x20₁ : t₁.getReg .x20 = itLayout s := (k₁ .x20 (by decide)).trans hx20
  have x25₁ : t₁.getReg .x25 = clAt s j := (k₁ .x25 (by decide)).trans hx25
  have hI₁ := hI.congr m₁ (k₁ .x2 (by decide)) (keeps_sub k₁ (by decide))
  have hA : t₁.getMem (t₁.getReg .x20 + 104) + (t₁.getReg .x12 * 16 + t₁.getReg .x12 * 8) =
      plAt s j := by
    rw [x20₁, x12₁, m₁, r104, pl_eq]
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80009c70_spec pc₁ (by
    rv_eval [hA]
    and_intros
    · exact Region.valid hPR (by simp only [plAt]; addr_omega [hPb, hcol])
        (by simp only [plAt]; addr_omega [hPb, hcol]) (by simp only [plAt]; addr_omega [hPb, hcol])
    · rw [x20₁]
      exact Region.valid hf.layout (by addr_omega [hLb]) (by addr_omega [hLb]) (by addr_omega [hLb]))
  have k₂ := b80009c70_keeps h₂
  have hI₂ := hI₁.congr (b80009c70_mem_same h₂) (k₂ .x2 (by decide)) (keeps_sub k₂ (by decide))
  have hbitE : t₁.getMem (t₁.getMem (t₁.getReg .x20 + 104) + (t₁.getReg .x12 * 16 + t₁.getReg .x12 * 8)) =
      s.getMem (plAt s j) := by
    rw [hA, m₁, rP]
  by_cases hbit : s.getMem (plAt s j) &&& 1 = 0
  · have pc₂ := b80009c70_pc_taken h₂ (by rw [hbitE]; exact hbit)
    have x12₂ : t₂.getReg .x12 = clAt s (j + 1) := by
      rw [b80009c70_x12 h₂, x25₁, clAt_succ]
    have x10₂ : t₂.getReg .x10 = s.getMem (itLayout s + 112) := by
      rw [k₂ .x10 (by decide), b80009c64_x10 h₁, hx20, r112]
    have x11₂ : t₂.getReg .x11 = placementsPtr s := by
      rw [b80009c70_x11 h₂, x20₁, m₁, r104]
    obtain ⟨v, hr, hv⟩ := after hpre (hI₂.skip hj (skip_none hcol hbit)) hj pc₂ x12₂ x10₂ x11₂
    rcases hv with hv | hv
    · exact ⟨v, hr₁.trans (hr₂.trans hr), Or.inr (Or.inl hv)⟩
    · obtain ⟨w, hrw, hw⟩ := skip_loop hpre (itCount s - (j + 1)) (j + 1) v (Nat.le_refl _) hv
      refine ⟨w, hr₁.trans (hr₂.trans (hr.trans hrw)), ?_⟩
      rcases hw with hw | hw | ⟨k, hk, hw⟩
      · exact Or.inl hw
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr ⟨k, by omega, hw⟩)
  · have pc₂ := b80009c70_pc_not_taken h₂ (by rw [hbitE]; exact hbit)
    obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80009c94_spec pc₂ (by rv_eval [])
    have k₃ := b80009c94_keeps h₃
    have hI₃ := hI₂.congr (b80009c94_mem_same h₃) (k₃ .x2 (by decide)) (keeps_sub k₃ (by decide))
    refine ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inr (Or.inr ⟨j, Nat.le_refl _, hI₃, b80009c94_pc h₃,
      by rw [b80009c94_x18 h₃, k₂ .x25 (by decide), x25₁],
      by rw [b80009c94_x25 h₃, b80009c70_x12 h₂, x25₁, clAt_succ],
      by rw [k₃ .x13 (by decide), b80009c70_x13 h₂, hA], hcol, hbit, hj⟩)⟩

end Rv64Verifier.Proofs.Pcs.Extend
