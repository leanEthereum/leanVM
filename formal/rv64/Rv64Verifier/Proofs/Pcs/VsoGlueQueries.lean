import Rv64Verifier.Proofs.Pcs.VsoGlueOod

/-!
# `verify_stacked_opening`'s final level: a queries claim

`0x8000bba8` compares the point's suffix's length with the weight's message log, an `Err` (`17`,
`0x8000c090`) when they differ; then `induced_weight` runs inline: the subspace roots
(`RootsSpec`), their inverses (`InvsSpec`) and the queries' products (`ProdsSpec`), to `GV`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `K`s of the heap below `w`'s `NEXT`, kept by the loop's writes from `w` on. -/
theorem GLW.kList {s w w' : MachineState} (hpre : VsoPre s) {hi : Word}
    (hX : DFrame w w' (GLW s (heapNext w) hi)) (hhw : heapNext w ≤ heapEnd) {p : Word} {n : ℕ}
    (hp : p.toNat + 8 * n ≤ heapNext w) : kListAt w' p n = kListAt w p n := by
  unfold kListAt
  apply List.map_congr_left
  intro i hi'
  simp only [List.mem_range] at hi'
  simp only [heapEnd] at hhw
  rw [hX _ fun k hk ↦ GLW.low hpre hhw (by addr_omega [hp, hi', hk, hhw])]

/-- The slots `GK` kept, the weight and the scalar with them. -/
theorem GK.eAt {s t t' : MachineState} (hpre : VsoPre s) (h : ∀ y, GK s y → t'.getMem y = t.getMem y)
    {p : Word} (hp : p = s.getReg .x2 - 232 ∨ p = s.getReg .x2 - 184) : eAt t' p = eAt t p := by
  have hb := bounds hpre
  rcases hp with rfl | rfl
  · exact eAt_congr (h _ (by simp [GK]))
      (h (s.getReg .x2 - 232 + 8) (by simp only [GK]; addr_omega [hb]))
      (h (s.getReg .x2 - 232 + 16) (by simp only [GK]; addr_omega [hb]))
  · exact eAt_congr (h _ (by simp [GK]))
      (h (s.getReg .x2 - 184 + 8) (by simp only [GK]; addr_omega [hb]))
      (h (s.getReg .x2 - 184 + 16) (by simp only [GK]; addr_omega [hb]))

/-- **A queries claim**: its message log checked, then `induced_weight` at the point's suffix. -/
theorem claimQueries (hRS : RootsSpec) (hIS : InvsSpec) (hPS : ProdsSpec)
    {OA : MachineState → Word → Model.TState → Prop} {s : MachineState} {x : LCtx}
    {u v w : MachineState} {Wl : Model.Pcs.WhirLocals} {residual tf : List E} {rt w0 : E} {j : ℕ}
    {a : Word} {acc : E} (hpre : VsoPre s) (h : GH OA s x u v w Wl residual tf rt w0 j a acc)
    (ht : u.getMem a ≠ 0xffffffffffffffff) :
    ∃ w', Reaches Image.code w w' ∧
      (FailR s w' ∨ ∃ val, GV OA s x u v w' Wl residual tf rt w0 j a acc val) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := h.gs.sp
  have fin := h.tb.toTI.fin
  obtain ⟨ea, ha1, ha2, ha8⟩ := fin.claimAt h.jlt
  rw [h.addr] at ea ha1 ha2 ha8
  have hs := fin.hs
  have hsu := fin.su
  have hhs := hpre.heap.lo
  have hhu := fin.heap.hi
  simp only [heapEnd] at hhu
  have hum := h.tb.mono
  have hR8 : Region a 88 := heap_region (by simp only [heapStart, heapNext] at hhs hs ⊢; omega)
    (by simp only [heapEnd]; omega) ha8
  have kw := (GS.ti hpre h.tb h.gs).claimWord hpre h.jlt
  rw [h.addr] at kw
  have c48 : w.getMem (a + 48) = u.getMem (a + 48) := kw 48 (by decide)
  -- `0x8000bba8`
  have hpc : w.pc = 0x8000bba8 := by rw [h.pc]; simp only [ht, ↓reduceIte]
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000bba8_spec hpc (by
    rv_eval [h.x8]
    exact Region.valid hR8 (by addr_omega [ha2, hhu]) (by addr_omega [ha2, hhu])
      (by addr_omega [ha2, hhu, ha8]))
  have hm₁ := b8000bba8_mem_same h₁
  have k₁ := b8000bba8_keeps h₁
  have G₁ := h.gs.same hpre hm₁ (k₁ .x2 (by decide))
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := G₁.sp
  by_cases hml : w.getReg .x26 = u.getMem (a + 48)
  swap
  · -- the `Err`, returned
    obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b8000c090_spec
      (b8000bba8_pc_taken h₁ (by rw [h.x8, c48]; exact hml)) (by
        rv_eval [sp₁]; and_intros <;> valid_access hst.valid [hb])
    have X₂ : DFrame t₁ t₂ fun y ↦ Within y (s.getReg .x2 - 896) 96 := by
      have := DFrame.of_memFrame (b8000c090_frame h₂ (by rw [sp₁]; addr_omega [hb]))
      rw [sp₁] at this
      exact this.mono fun y hy ↦ by addr_omega [hy, hb]
    obtain ⟨T₂, -⟩ := (GS.ti hpre h.tb G₁).stepS hpre X₂ (fun y hy ↦ Or.inl (by addr_omega [hy, hb]))
      (b8000c090_keeps h₂ .x2 (by decide))
    have sp₂ : t₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := T₂.sp
    obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b8000c084_spec (b8000c090_pc h₂) (by
      rv_eval [sp₂]; and_intros <;> valid_access hst.valid [hb])
    have inv₃ : InvR s t₃ (t₂.getMem nextAddr) := Inv.same' (T₂.inv hpre)
      (b8000c084_mem_same h₃) (by rw [b8000c084_keeps h₃ .x2 (by decide)])
    obtain ⟨t₄, r₄, hf⟩ := fail844 inv₃ (b8000c084_pc h₃) (by
      rw [b8000c084_x1 h₃, b8000c090_keeps h₂ .x2 (by decide), b8000c090_m_x2_144 h₂]; decide)
    exact ⟨t₄, r₁.trans (r₂.trans (r₃.trans r₄)), Or.inl hf⟩
  -- the point's suffix
  have hfs := h.fsle
  obtain ⟨hsl, hP8, hPb⟩ := h.tb.suffix hfs
  generalize hP : vecPtr v (s.getReg .x2 - 280) +
    BitVec.ofNat 64 (24 * (u.getMem (a + 80)).toNat) = P at hsl hP8 hPb
  generalize hn : (vecLen v (s.getReg .x2 - 280)).toNat - (u.getMem (a + 80)).toNat = n at hsl hPb
  have hm848 := h.m848
  rw [hP] at hm848
  have hx26 := h.x26
  rw [hn] at hx26
  have hn48 : (u.getMem (a + 48)).toNat = n := by
    rw [← hml, hx26, BitVec.toNat_ofNat]; omega
  -- the roots
  have hQA : QA s v t₁ a n := {
    gs := G₁
    pc := b8000bba8_pc_not_taken h₁ (by rw [h.x8, c48]; exact hml)
    x8 := by rw [k₁ .x8 (by decide), h.x8]
    x26 := by rw [k₁ .x26 (by decide), hx26]
    x18 := by rw [k₁ .x18 (by decide), k₁ .x9 (by decide), h.x18, h.x9]; omega
    claim := ⟨by omega, by omega, ha8⟩ }
  obtain ⟨t₂, r₂, hd | ⟨rs, hr⟩⟩ := hRS s v t₁ a n hpre hQA
  · exact ⟨t₂, r₁.trans r₂, Or.inl (Or.inl hd)⟩
  have hs₁ := G₁.su
  have hx21 := hr.x21
  -- the inverses
  obtain ⟨t₃, r₃, hd | hi⟩ := hIS s v t₂ n rs hpre
    ⟨hr.gs, hr.pc, hr.x20, ⟨hx21.1, by omega, hx21.2.2⟩, hr.rmem⟩
  · exact ⟨t₃, r₁.trans (r₂.trans r₃), Or.inl (Or.inl hd)⟩
  have hs₂ := hr.gs.su
  have hm₂ := hr.gs.mono
  -- the queries and their weights
  have hfz := fin.frozen j h.jlt
  have hal := fin.aligned j h.jlt
  rw [h.addr] at hfz hal
  simp only [WeightAligned, ht, ↓reduceIte] at hal
  have hqb := bufBound (L := x.L) (by simp only [heapEnd]; omega) fun y hy ↦ hfz y (by
    simp only [InBufs, ht, ↓reduceIte]; exact Or.inl hy)
  have hwb := bufBound (L := x.L) (by simp only [heapEnd]; omega) fun y hy ↦ hfz y (by
    simp only [InBufs, ht, ↓reduceIte]; exact Or.inr hy)
  have e8 : vecPtr u a = u.getMem (a + 8) := rfl
  have e16 : vecLen u a = u.getMem (a + 16) := rfl
  have e32 : vecPtr u (a + 24) = u.getMem (a + 32) := by simp only [vecPtr]; rv_eval []
  have e40 : vecLen u (a + 24) = u.getMem (a + 40) := by simp only [vecLen]; rv_eval []
  rw [e8, e16] at hqb
  rw [e32, e40] at hwb
  rw [e8, e32] at hal
  have kw₁ := (GS.ti hpre h.tb G₁).claimWord hpre h.jlt
  rw [h.addr] at kw₁
  have T₃ := GS.ti hpre h.tb hi.gs
  have hix := hi.ip
  have hvm₃ := hi.gs.mono
  have s856 : t₃.getMem (s.getReg .x2 - 856) = u.getMem (a + 8) := by
    rw [hi.keep _ (Or.inr (Or.inl rfl)), hr.m856]; exact kw₁ 8 (by decide)
  have s824 : t₃.getMem (s.getReg .x2 - 824) = u.getMem (a + 32) := by
    rw [hi.keep _ (Or.inr (Or.inr (Or.inl rfl))), hr.m824]; exact kw₁ 32 (by decide)
  have s816 : t₃.getMem (s.getReg .x2 - 816) = vecLen v (s.getReg .x2 - 280) := by
    rw [hi.keep _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hr.m816, k₁ .x18 (by decide), h.x18]
  have s808 : t₃.getMem (s.getReg .x2 - 808) = u.getMem (a + 80) := by
    rw [hi.keep _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), hr.m808, k₁ .x9 (by decide), h.x9]
  have gk (y : Word) (hy : GK s y) : t₃.getMem y = w.getMem y := by
    rw [hi.keep _ (Or.inl hy), hr.keep _ hy, hm₁]
  have s848 : t₃.getMem (s.getReg .x2 - 848) = P := by
    rw [gk _ (Or.inr (Or.inr (Or.inl rfl))), hm848]
  have x19₃ : t₃.getReg .x19 = u.getMem (a + 40) := by
    rw [hi.x19, hr.x19]; exact kw₁ 40 (by decide)
  have x23₃ : t₃.getReg .x23 = u.getMem (a + 16) := by
    rw [hi.x23, hr.x23]; exact kw₁ 16 (by decide)
  have hQC : QC s v t₃ n rs (eListAt v P n)
      (u.readWords (u.getMem (a + 8)) (u.getMem (a + 16)).toNat)
      (eListAt u (u.getMem (a + 32)) (u.getMem (a + 40)).toNat) := {
    gs := hi.gs
    pc := hi.pc
    rlen := hr.rlen
    x20 := hi.x20.trans hr.x20
    x21 := by rw [hi.x21]; exact ⟨hx21.1, by omega, by omega⟩
    rmem := by
      rw [hi.x21, GLW.kList hpre hi.fr hr.gs.heap.hi hx21.2.2]; exact hr.rmem
    x22 := hi.x22
    x26 := hi.x26.trans hr.x26
    ip := ⟨hix.1, by omega, hix.2.2⟩
    imem := hi.imem
    plen := by rw [s816, s808]; omega
    pt := by
      rw [s848]
      refine ⟨hP8, ?_⟩
      rcases hPb with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨by omega, by omega⟩
    xs := by
      rw [s848]
      exact hi.gs.eListLow hpre (by
        rcases hPb with h0 | h0
        · exact Or.inl h0
        · exact Or.inr ⟨by omega, h0.2⟩)
    wp := by
      rw [s824, x19₃]
      refine ⟨hal.2, ?_⟩
      rcases hwb with h0 | h0
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, by omega⟩
    qw := by
      rw [s824, x19₃]
      exact T₃.eList hpre (by
        rcases hwb with h0 | h0
        · exact Or.inl (by omega)
        · exact Or.inr ⟨by omega, h0.2⟩)
    qp := by
      rw [s856, x23₃]
      refine ⟨hal.1, ?_⟩
      rcases hqb with h0 | h0
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, by omega⟩
    qs := by
      rw [s856, x23₃]
      exact T₃.readWords hpre (by
        rcases hqb with h0 | h0
        · exact Or.inl (by omega)
        · exact Or.inr ⟨by omega, h0.2⟩) }
  -- the queries' products
  obtain ⟨t₄, r₄, hd | ho⟩ := hPS s v t₃ n rs _ _ _ hpre hQC
  · exact ⟨t₄, r₁.trans (r₂.trans (r₃.trans r₄)), Or.inl (Or.inl hd)⟩
  have gk4 (y : Word) (hy : GK s y) : t₄.getMem y = w.getMem y := by rw [ho.keep y hy, gk y hy]
  refine ⟨t₄, r₁.trans (r₂.trans (r₃.trans r₄)), Or.inr ⟨_, {
    tb := h.tb
    gs := ho.gs
    pc := ho.pc
    jlt := h.jlt
    addr := h.addr
    m880 := by rw [gk4 _ (Or.inl rfl)]; exact h.m880
    m872 := by rw [gk4 _ (Or.inr (Or.inl rfl))]; exact h.m872
    fold := h.fold
    wt := by rw [GK.eAt hpre gk4 (Or.inr rfl)]; exact h.wt
    scalar := by rw [GK.eAt hpre gk4 (Or.inl rfl)]; exact h.scalar
    value := ho.value
    eval := ⟨eListAt v P n, by simp only [gluedAt]; exact hsl, by
      simp only [gluedAt, weightAt, ht, ↓reduceIte, Model.Pcs.GluedWeightRust.evaluate, hn48,
        vecWords, vecEs, e8, e16, e32, e40]
      exact inducedWeight_eq (eListAt_length _ _ _) hr.roots⟩ }⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso
