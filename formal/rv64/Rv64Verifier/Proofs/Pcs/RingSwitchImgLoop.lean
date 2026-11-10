import Rv64Verifier.Proofs.Pcs.RingSwitchImgStage

/-!
# `ring_switch`: the images loop's push, and the loops
-/

namespace Rv64Verifier.Proofs.Pcs.RingSwitch
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.FieldContracts
  Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F36
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

section
variable {s B2 u : MachineState} {C chP I nx : Word} {ch : List E}

/-- `0x800099f4`: the push; the next value, or the end. -/
theorem iPush (hpre : RingSwitchPre s) (hctx : Ctx2 s B2 C chP I ch) {i : Nat}
    (hc : IPush s B2 u I ch nx i) :
    ∃ v, Reaches Image.code u v ∧ ((i + 1 < nS s ∧ IHead s B2 v I ch nx (i + 1)) ∨
      (i + 1 = nS s ∧ IExit s B2 v I ch nx)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp : u.getReg .x2 = s.getReg .x2 - 464 := hc.ph.sp.trans hctx.sp
  have hi := hc.lt
  have hH := hctx.heap.hi
  have hC := hctx.cHi
  have hI := hctx.iR
  have hiA := hctx.iA
  have hcL := hctx.chLo
  have hcC := hctx.chC
  have hlo := hpre.heap.lo
  simp only [heapStart] at hlo
  simp only [nS] at hi hI
  rcases hI with hI | hI
  · omega
  have hIV : ValidMemRange I (3 * (s.getReg .x13).toNat) :=
    MultilinearWords.heap_valid_range hiA (by simp only [heapStart]; omega)
      (by simp only [heapEnd] at hH ⊢; omega)
  have hI24 : u.getMem (u.getReg .x2 + 24) = I := by
    rw [hsp]; rv_eval []
    exact (keepF2 hpre hctx hc.ph (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))).trans hctx.iP
  have hn32 : u.getMem (u.getReg .x2 + 32) = s.getReg .x13 := by
    rw [hsp]; rv_eval []
    exact (keepF2 hpre hctx hc.ph (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))).trans
      hctx.sLen
  have hx21 := hc.x21
  obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b800099f4_spec hc.pc (by
    rv_eval [hsp, hx21]
    rw [hsp] at hI24; rv_eval [] at hI24
    rv_eval [hI24]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | valid_access hIV [hi, hI.2, hH, hiA]
      | addr_omega [hi, hI.2, hH, hb])
  have k₁ := b800099f4_keeps h
  have hw (a : Word) (h1 : a.toNat + 8 ≤ I.toNat + 24 * i ∨ I.toNat + 24 * (i + 1) ≤ a.toNat ∨
      (s.getReg .x2).toNat - 464 ≤ a.toNat) : v.getMem a = u.getMem a :=
    h.frame a (by
      rv_eval [hsp, hx21]
      rw [hsp] at hI24; rv_eval [] at hI24
      rv_eval [hI24]
      and_intros <;> addr_omega [h1, hi, hI.2, hH, hb])
  have hD : DFrame u v (w2 s I) := fun a ha ↦ hw a (by
    have h0 := ha 0 (by decide)
    have h7 := ha 7 (by decide)
    rw [add_ofNat_zero] at h0
    simp only [w2, nS] at h0 h7
    by_contra hc'
    by_cases hlt : I.toNat ≤ a.toNat
    · exact h0 (Or.inr (by addr_omega [hc', hlt, hi, hI.2, hH, hb]))
    · exact h7 (Or.inr (by addr_omega [hc', hlt, hi, hI.2, hH, hb])))
  have ph := hc.ph.step hD (fun a ha ↦ Or.inl ha)
    ((hD.word (fun x hx hW ↦ by
        rcases hW with hW | hW
        · addr_omega [hx, hW, hb]
        · simp only [nS] at hW; addr_omega [hx, hW, hi, hI.2, hH])
      (by decide)).trans hc.ph.next) (Nat.le_refl _) hc.ph.fits (k₁ .x2 (by decide))
  have m0 := b800099f4_m0 h
  have m1 := b800099f4_m1 h
  have m2 := b800099f4_m2 h
  have hR := hpre.slices.region.resolve_left (by omega)
  have hRb := Region.bounds hR
  rw [hI24, hx21, mul24g i (by addr_omega [hi, hI.2, hH])] at m0 m1 m2
  have hnew : eAt v (I + BitVec.ofNat 64 (24 * i)) = ringMapRust (sv s i) ch := by
    rw [ringMap_eq]
    apply eAt_eq_of_limbs
    rw [hc.val, m0, m1, m2]
  have hbuf (l : Nat) (hl : l < i + 1) : eAt v (I + BitVec.ofNat 64 (24 * l)) =
      ringMapRust (sv s l) ch := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
    · rw [eAt_congr (hw _ (Or.inl (by addr_omega [hl, hi, hI.2, hH])))
        (hw _ (Or.inl (by addr_omega [hl, hi, hI.2, hH])))
        (hw _ (Or.inl (by addr_omega [hl, hi, hI.2, hH])))]
      exact hc.buf l hl
    · exact hnew
  have r (r : Reg) (hr : r ∈ [Reg.x9, .x19, .x27]) : v.getReg r = u.getReg r :=
    k₁ r (mem_of_mem hr _)
  have hx26 : v.getReg .x26 = BitVec.ofNat 64 (i + 1) := by
    rw [b800099f4_x26 h, hc.x26]; addr_omega [hi, hI.2, hH]
  have hx21' : v.getReg .x21 = BitVec.ofNat 64 (i + 1) := by
    rw [b800099f4_x21 h, hx21]; addr_omega [hi, hI.2, hH]
  by_cases hn : i + 1 = (s.getReg .x13).toNat
  · refine ⟨v, hr, Or.inr ⟨hn, {
      ph := ph
      pc := b800099f4_pc_taken h (by
        rw [hc.x26, hn32]; apply BitVec.eq_of_toNat_eq; rw [← hn]; addr_omega [hi, hI.2, hH])
      x21 := by rw [hx21']; simp only [nS, hn]
      buf := fun l hl ↦ hbuf l (by simp only [nS] at hl; omega) }⟩⟩
  · refine ⟨v, hr, Or.inl ⟨by simp only [nS]; omega, {
      x9 := (r .x9 (by decide)).trans hc.x9
      x19 := (r .x19 (by decide)).trans hc.x19
      x27 := (r .x27 (by decide)).trans hc.x27
      ph := ph
      pc := b800099f4_pc_not_taken h (by
        rw [hc.x26, hn32]; intro he; apply hn
        have := congrArg BitVec.toNat he
        rw [show (BitVec.ofNat 64 i + 1).toNat = i + 1 by addr_omega [hi, hI.2, hH]] at this
        exact this)
      lt := by simp only [nS]; omega
      x21 := hx21'
      x26 := hx26
      buf := hbuf }⟩⟩

/-- The stages of value `i`. -/
theorem iStages (hP : PowSpec) (hM : MulSpec) (hpre : RingSwitchPre s)
    (hctx : Ctx2 s B2 C chP I ch) {i : Nat} (h0 : IStage s B2 u chP I ch nx i 0) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ IPush s B2 v I ch nx i) := by
  refine Reaches.loop (fun v ↦ ∃ j, IStage s B2 v chP I ch nx i j)
    (fun v ↦ (v.getReg .x20).toNat)
    (fun v ↦ Dead Image.code v ∨ IPush s B2 v I ch nx i) ?_ u ⟨0, h0⟩
  rintro v ⟨j, hv⟩
  obtain ⟨w, hvw, hw⟩ := iStage hP hM hpre hctx hv
  rcases hw with hd | ⟨hj, hw⟩ | ⟨-, hw⟩
  · exact Or.inl ⟨w, hvw, Or.inl hd⟩
  · refine Or.inr ⟨w, hvw, ⟨j + 1, hw⟩, ?_⟩
    rw [hw.x20, hv.x20, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · exact Or.inl ⟨w, hvw, Or.inr hw⟩

/-- The images loop: from value `0` to `0x80009b00`. -/
theorem iLoop (hP : PowSpec) (hM : MulSpec) (hpre : RingSwitchPre s) (hctx : Ctx2 s B2 C chP I ch)
    (h0 : IHead s B2 u I ch nx 0) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ IExit s B2 v I ch nx) := by
  refine Reaches.loop (fun v ↦ ∃ i, IHead s B2 v I ch nx i)
    (fun v ↦ nS s - (v.getReg .x26).toNat)
    (fun v ↦ Dead Image.code v ∨ IExit s B2 v I ch nx) ?_ u ⟨0, h0⟩
  rintro v ⟨i, hv⟩
  obtain ⟨w, hvw, hw⟩ := iHead hpre hctx hv
  obtain ⟨x, hwx, hx⟩ := iStages hP hM hpre hctx hw
  rcases hx with hd | hx
  · exact Or.inl ⟨x, hvw.trans hwx, Or.inl hd⟩
  obtain ⟨y, hxy, hy⟩ := iPush hpre hctx hx
  rcases hy with ⟨hi, hy⟩ | ⟨-, hy⟩
  · refine Or.inr ⟨y, hvw.trans (hwx.trans hxy), ⟨i + 1, hy⟩, ?_⟩
    have hR := hpre.slices.region.resolve_left (by simp only [nS] at hi; omega)
    have hRb := Region.bounds hR
    simp only [nS] at hi ⊢
    rw [hy.x26, hv.x26, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · exact Or.inl ⟨y, hvw.trans (hwx.trans hxy), Or.inr hy⟩

end

end Rv64Verifier.Proofs.Pcs.RingSwitch
