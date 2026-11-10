import Rv64Verifier.Proofs.Multilinear.EqKernelHead

/-!
# `eq_kernel`: the inner loop, the outer loop's tail, the epilogue

`inner_body` takes the inner loop from its head through `h = scale.mul(out[j])` (`mul`, or the
table) to `0x8000ccb0` (`Pre`), `store` writes `out[j + 2^k]` and `out[j]` and returns to the head
(`IInv`) or, the pass done, to `0x8000cbf8` (`Done`); `tail` moves to the next coordinate (`OInv`)
or to the epilogue (`Exit`); `exit` restores and returns; `eq_kernel_spec` puts them together.
-/

namespace Rv64Verifier.Proofs.Multilinear.EqKernel
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Contracts
  Rv64Verifier.Runtime Rv64Verifier.MultilinearContracts Rv64Verifier.MultilinearWords
  Rv64Verifier.Blocks.F51 Rv64Verifier.Proofs.Multilinear.ScalerFill
  Rv64Verifier.Proofs.Multilinear.EqKernelWin
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The inner loop -/

/-- At `0x8000ccb0`, `h` at `S - 160`: pass `k` at `j`. -/
structure Pre (s u : MachineState) (C P T nx : Word) (k j : Nat) : Prop extends Mid s u C P nx where
  pc : u.pc = 0x8000ccb0
  lt : k < nm s
  jlt : j < 2 ^ k
  m168 : u.getMem (s.getReg .x2 - 168) = s.getReg .x11 + BitVec.ofNat 64 (24 * k)
  m176 : u.getMem (s.getReg .x2 - 176) = BitVec.ofNat 64 k
  x9 : u.getReg .x9 = BitVec.ofNat 64 (2 ^ k)
  x18 : u.getReg .x18 = P + BitVec.ofNat 64 (24 * j)
  x20 : u.getReg .x20 = P + BitVec.ofNat 64 (24 * 2 ^ k)
  x21 : u.getReg .x21 = BitVec.ofNat 64 (24 * j)
  x25 : u.getReg .x25 = BitVec.ofNat 64 j
  sc : Sc s u C P T nx ((pt s).getD k 0)
  buf : eListAt u P (2 ^ nm s) = (List.range j).foldl
    (Model.eqKernelStep ((pt s).getD k 0) (2 ^ k))
    (eqKernel ((pt s).take k) ++ List.replicate (2 ^ nm s - 2 ^ k) 0)
  prod : eAt u (s.getReg .x2 - 160) = eAt u (P + BitVec.ofNat 64 (24 * j)) * (pt s).getD k 0

/-- The `Scaler` survives a step writing the stack below it and the result's buffer. -/
theorem Sc.step {s u v : MachineState} {C P T nx : Word} {r : E} {X : Word → Prop}
    (hpre : EqKernelPre s) (hm : Mid s u C P nx) (h : Sc s u C P T nx r) (hX : DwFrame u v X)
    (hsub : ∀ a, X a → Within a (s.getReg .x2 - 1232) 1096 ∨ Within a P (24 * C.toNat))
    (hr : ∀ r ∈ [Reg.x19, .x22, .x23], v.getReg r = u.getReg r) : Sc s v C P T nx r := by
  have hb := bounds hpre
  have hab := hpre.stack.above
  have htop := hm.top
  have hfit := hm.inv.fits
  have hPlo := hm.lo
  have hlo := hpre.heap.lo
  refine ⟨(hr _ (by decide)).trans h.x19, fun hne ↦ ?_, fun he ↦ ?_⟩
  · rw [hr _ (by decide)] at hne
    rw [← h.plain hne]
    have w (c : Nat) (hc : c = 0 ∨ c = 8 ∨ c = 16) :
        v.getMem (s.getReg .x2 - 128 + BitVec.ofNat 64 c) =
          u.getMem (s.getReg .x2 - 128 + BitVec.ofNat 64 c) :=
      DwFrame.keep hX fun i hi hx ↦ by
        rcases hsub _ hx with hx | hx
        · addr_omega [hx, hi, hc, hb]
        · addr_omega [hx, hi, hc, hb, hab, htop, hfit]
    have e0 := w 0 (Or.inl rfl)
    have e1 := w 8 (Or.inr (Or.inl rfl))
    have e2 := w 16 (Or.inr (Or.inr rfl))
    simp only [BitVec.add_zero] at e0 e1 e2
    exact eAt_congr e0 e1 e2
  · rw [hr _ (by decide)] at he
    obtain ⟨h23, hB, hPT, hTt, htab⟩ := h.table he
    have hTh := hB.hi
    refine ⟨(hr _ (by decide)).trans h23, hB, hPT, hTt, ?_⟩
    rw [tab_dw hX (fun a ha hx ↦ by
        rcases hsub _ hx with hx | hx
        · addr_omega [hx, ha, hb, hab, hTh]
        · addr_omega [hx, ha, hPT])
      (by simp only [tabBytes, heapEnd] at hTh ⊢; omega), htab]

theorem store {s : MachineState} (hpre : EqKernelPre s) {C P T nx : Word} {k j : Nat}
    {u : MachineState} (hu : Pre s u C P T nx k j) :
    ∃ v, Reaches Image.code u v ∧ (IInv s v C P T nx k (j + 1) ∨ Done s v C P nx k) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  obtain ⟨hPN, hn27⟩ := hu.small
  simp only [heapEnd] at hPN
  have hk := hu.lt
  have hj := hu.jlt
  have hpow : 2 ^ (k + 1) ≤ 2 ^ nm s := Nat.pow_le_pow_right (by norm_num) hk
  rw [pow_succ] at hpow
  have hsp := hu.inv.sp
  have hPa := hu.align
  have hPlo := hu.lo
  have hlo := hpre.heap.lo
  have htop := hu.top
  have hroom := hu.room
  have hfit := hu.inv.fits
  obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b8000ccb0_spec hu.pc (by
    rv_eval [hu.x18, hu.x20, hu.x21, hsp]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact heap_valid' (by addr_omega [hPa, hPlo, hlo, hPN, hj, hpow])
          (by addr_omega [hPa, hPlo, hlo, hPN, hj, hpow])
          (by addr_omega [hPa, hPlo, hlo, hPN, hj, hpow])
      | addr_omega [hPa, hPlo, hlo, hPN, hj, hpow])
  have k₁ := b8000ccb0_keeps h
  have hx2021 : u.getReg .x20 + u.getReg .x21 = P + BitVec.ofNat 64 (24 * (j + 2 ^ k)) := by
    rw [hu.x20, hu.x21]; addr_omega [hPN, hj, hpow]
  have hfr : ∀ a, ¬ Within a (P + BitVec.ofNat 64 (24 * (j + 2 ^ k))) 24 →
      ¬ Within a (P + BitVec.ofNat 64 (24 * j)) 24 → v.getMem a = u.getMem a := by
    intro a h1 h2
    refine h.frame a ?_
    rv_eval [hu.x18, hx2021]
    and_intros <;> intro heq <;> rw [heq] at h1 h2 <;>
      first | exact h1 (by addr_omega [hPN, hj, hpow]) | exact h2 (by addr_omega [hPN, hj, hpow])
  have m3 := b8000ccb0_m3 h
  have m4 := b8000ccb0_m4 h
  have m5 := b8000ccb0_m5 h
  have n0 := b8000ccb0_m_x18_0 h
  have n1 := b8000ccb0_m_x18_8 h
  have n2 := b8000ccb0_m_x18_16 h
  rw [hx2021, hsp] at m3 m4 m5
  rw [hu.x18, hsp] at n0 n1 n2
  rv_eval [] at m3 m4 m5 n0 n1 n2
  have hnew1 : eAt v (P + BitVec.ofNat 64 (24 * (j + 2 ^ k))) = eAt u (s.getReg .x2 - 160) := by
    apply eAt_congr <;> rv_eval [m3, m4, m5]
  have hnew2 : eAt v (P + BitVec.ofNat 64 (24 * j)) =
      eAt u (P + BitVec.ofNat 64 (24 * j)) + eAt u (s.getReg .x2 - 160) := by
    apply eAt_eq_of_limbs
    rw [limbs_add, limbs_eAt, limbs_eAt, n0, n1, n2]
    rv_eval []
  have hN : P.toNat + 24 * 2 ^ nm s ≤ 2 ^ 64 := by omega
  have hbuf : eListAt v P (2 ^ nm s) = (List.range (j + 1)).foldl
      (Model.eqKernelStep ((pt s).getD k 0) (2 ^ k))
      (eqKernel ((pt s).take k) ++ List.replicate (2 ^ nm s - 2 ^ k) 0) := by
    rw [eListAt_set2 (by omega) (by omega) (by omega) hN hfr, hnew1, hnew2, List.range_succ,
      List.foldl_append, List.foldl_cons, List.foldl_nil, ← hu.buf]
    simp only [Model.eqKernelStep]
    rw [eListAt_getD' _ _ (by omega), hu.prod, Nat.add_comm j]
  have hX (a : Word) (ha : Within a (P + BitVec.ofNat 64 (24 * (j + 2 ^ k))) 24 ∨
      Within a (P + BitVec.ofNat 64 (24 * j)) 24) : Within a P (24 * C.toNat) := by
    rcases ha with ha | ha <;> addr_omega [ha, hPN, hj, hpow, hroom]
  have mid := hu.toMid.step hpre (DwFrame.of_two hfr)
    (fun a ha ↦ Or.inr (Or.inr ⟨by have := hX a ha; addr_omega [this, hPlo],
      by have := hX a ha; addr_omega [this, htop]⟩))
    (fun a ha ↦ by have := hX a ha; exact ⟨by addr_omega [this, hb, hab, htop, hfit],
      by addr_omega [this, hb, hab, htop, hfit]⟩)
    ((hfr _ (by addr_omega [hPN, hj, hpow]) (by addr_omega [hPN, hj, hpow])).trans hu.inv.next)
    (Nat.le_refl _) hfit fun r hr ↦ k₁ r (mem_of_mem hr _)
  have sc := Sc.step hpre hu.toMid hu.sc (DwFrame.of_two hfr) (fun a ha ↦ Or.inr (hX a ha))
    fun r hr ↦ k₁ r (mem_of_mem hr _)
  have m168 : v.getMem (s.getReg .x2 - 168) = s.getReg .x11 + BitVec.ofNat 64 (24 * k) :=
    (hfr _ (by addr_omega [hb, hab, hPN, hj, hpow]) (by addr_omega [hb, hab, hPN, hj, hpow])).trans
      hu.m168
  have m176 : v.getMem (s.getReg .x2 - 176) = BitVec.ofNat 64 k :=
    (hfr _ (by addr_omega [hb, hab, hPN, hj, hpow]) (by addr_omega [hb, hab, hPN, hj, hpow])).trans
      hu.m176
  by_cases hlast : j + 1 = 2 ^ k
  · refine ⟨v, hr, Or.inr {
      toMid := mid
      pc := b8000ccb0_pc_taken h (by rw [hu.x25, hu.x9]; addr_omega [hlast, hPN, hpow])
      lt := hk
      m168 := m168
      m176 := m176
      buf := ?_ }⟩
    have hlen : k < (pt s).length := by
      rw [pt, eListAt_length]; have := nm_le s; omega
    rw [hbuf, hlast, pass_eq (pt s) hlen (by rw [pow_succ]; exact hpow)]
  · refine ⟨v, hr, Or.inl {
      toMid := mid
      pc := b8000ccb0_pc_not_taken h (by rw [hu.x25, hu.x9]; addr_omega [hlast, hPN, hpow, hj])
      lt := hk
      jlt := by omega
      m168 := m168
      m176 := m176
      x9 := (k₁ .x9 (by decide)).trans hu.x9
      x20 := (k₁ .x20 (by decide)).trans hu.x20
      x25 := by rw [b8000ccb0_x25 h, hu.x25]; addr_omega [hPN, hpow, hj]
      sc := sc
      buf := hbuf }⟩

theorem inner_body (hMul : MulSpec) {s : MachineState} (hpre : EqKernelPre s) {C P T nx : Word}
    {k j : Nat} {u : MachineState} (hu : IInv s u C P T nx k j) :
    ∃ v, Reaches Image.code u v ∧ (Pre s v C P T nx k j ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  obtain ⟨hPN, hn27⟩ := hu.small
  simp only [heapEnd] at hPN
  have hk := hu.lt
  have hj := hu.jlt
  have hpow : 2 ^ (k + 1) ≤ 2 ^ nm s := Nat.pow_le_pow_right (by norm_num) hk
  rw [pow_succ] at hpow
  have hsp := hu.inv.sp
  have hPa := hu.align
  have hPlo := hu.lo
  have hlo := hpre.heap.lo
  have htop := hu.top
  have hroom := hu.room
  have hfit := hu.inv.fits
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000cd04_spec hu.pc (by rv_eval [])
  have k₁ := b8000cd04_keeps h₁
  have hm₁ := b8000cd04_mem_same h₁
  have hx18 : u₁.getReg .x18 = P + BitVec.ofNat 64 (24 * j) := by
    rw [b8000cd04_x18 h₁, hu.x8, hu.x25]; addr_omega [hPN, hj, hpow]
  have hx21 : u₁.getReg .x21 = BitVec.ofNat 64 (24 * j) := by
    rw [b8000cd04_x21 h₁, hu.x25]; addr_omega [hPN, hj, hpow]
  have mid₁ := hu.toMid.same hpre hm₁ fun r hr ↦ k₁ r (mem_of_mem hr _)
  have hsp₁ : u₁.getReg .x2 = s.getReg .x2 - 208 := (k₁ .x2 (by decide)).trans hsp
  have hjv (c : Nat) (hc : c = 0 ∨ c = 8 ∨ c = 16) :
      Sym.validAccess 8 (P + BitVec.ofNat 64 (24 * j) + BitVec.ofNat 64 c) = true :=
    heap_valid' (by addr_omega [hPa, hPlo, hlo, hPN, hj, hpow, hc])
      (by addr_omega [hPa, hPlo, hlo, hPN, hj, hpow, hc])
      (by addr_omega [hPa, hPlo, hlo, hPN, hj, hpow, hc])
  have hbuf₁ := (eListAt_same hm₁ P (2 ^ nm s)).trans hu.buf
  have hreg (r : Reg) (hr : r ∈ [Reg.x9, .x20, .x25]) : u₁.getReg r = u.getReg r :=
    k₁ r (mem_of_mem hr _)
  by_cases htag : u.getReg .x22 = 0
  · -- the table
    obtain ⟨h23, hBuf, hPT, hTt, htab⟩ := hu.sc.table htag
    obtain ⟨v, hr₂, hpc₂, hk₂, hm₂, hprod⟩ := table_mul hBuf (b8000cd04_pc_not_taken h₁ htag)
      ((k₁ .x19 (by decide)).trans hu.sc.x19) ((k₁ .x23 (by decide)).trans h23)
      ((k₁ .x24 (by decide)).trans hu.x24) ((k₁ .x26 (by decide)).trans hu.x26)
      ((k₁ .x27 (by decide)).trans hu.x27)
      (by
        rw [hx18]
        have e0 := hjv 0 (Or.inl rfl)
        have e1 := hjv 8 (Or.inr (Or.inl rfl))
        have e2 := hjv 16 (Or.inr (Or.inr rfl))
        simp only [BitVec.add_zero] at e0 e1 e2
        exact ⟨e2, e1, e0⟩)
      (by rw [hsp₁]; rv_eval []; exact ⟨by valid_access hst.valid [hb],
        by valid_access hst.valid [hb], by valid_access hst.valid [hb]⟩)
      (by rw [hsp₁]; addr_omega [hb])
    rw [hx18, hsp₁, tab_same hm₁, htab, Model.scaledMul_eq] at hprod
    rw [hsp₁] at hm₂
    rv_eval [] at hm₂ hprod
    have hP' : eAt v (P + BitVec.ofNat 64 (24 * j)) = eAt u₁ (P + BitVec.ofNat 64 (24 * j)) :=
      hm₂.eAt (by addr_omega [hb, hab, hPN, hj, hpow]) (by addr_omega [hPN, hj, hpow])
    have hdw := DwFrame.of_mem hm₂
    have hX (a : Word) (ha : Within a (s.getReg .x2 - 160) 24) : LW s nx a :=
      Or.inl (by addr_omega [ha, hb])
    refine ⟨v, hr₁.trans hr₂, Or.inl {
      toMid := mid₁.step hpre hdw hX (fun a ha ↦ ⟨by addr_omega [ha, hb], by addr_omega [ha, hb]⟩)
        ((hm₂ _ (by addr_omega [hb, hnx8])).trans mid₁.inv.next) (Nat.le_refl _) hfit
        fun r hr ↦ hk₂ r (mem_of_mem hr _)
      pc := hpc₂
      lt := hk
      jlt := hj
      m168 := (hm₂ _ (by addr_omega [hb])).trans ((hm₁ _).trans hu.m168)
      m176 := (hm₂ _ (by addr_omega [hb])).trans ((hm₁ _).trans hu.m176)
      x9 := by rw [hk₂ _ (by decide), hreg _ (by decide), hu.x9]
      x18 := (hk₂ _ (by decide)).trans hx18
      x20 := by rw [hk₂ _ (by decide), hreg _ (by decide), hu.x20]
      x21 := (hk₂ _ (by decide)).trans hx21
      x25 := by rw [hk₂ _ (by decide), hreg _ (by decide), hu.x25]
      sc := Sc.step hpre hu.toMid hu.sc (DwFrame.of_mem fun a ha ↦ (hm₂ a ha).trans (hm₁ a))
        (fun a ha ↦ Or.inl (by addr_omega [ha, hb])) fun r hr ↦ by
          rw [hk₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
      buf := by
        rw [← hbuf₁]
        exact eListAt_frame hm₂ (by addr_omega [hb, hab, hPN, hPlo, hlo]) (by omega)
      prod := ?_ }⟩
    apply eAt_eq_of_limbs
    rv_eval []
    rw [hprod, hP', mul_comm]
  · -- `mul`
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000cc9c_spec (b8000cd04_pc_taken h₁ htag)
      (by rv_eval [])
    have k₂ := b8000cc9c_keeps h₂
    have hm₂ := b8000cc9c_mem_same h₂
    have mid₂ := mid₁.same hpre hm₂ fun r hr ↦ k₂ r (mem_of_mem hr _)
    have hsp₂ : u₂.getReg .x2 = s.getReg .x2 - 208 := (k₂ .x2 (by decide)).trans hsp₁
    have hx10 : u₂.getReg .x10 = s.getReg .x2 - 160 := by
      rw [b8000cc9c_x10 h₂, hsp₁]; rv_eval []
    have hx11 : u₂.getReg .x11 = P + BitVec.ofNat 64 (24 * j) := (b8000cc9c_x11 h₂).trans hx18
    have hx12 : u₂.getReg .x12 = s.getReg .x2 - 128 := by
      rw [b8000cc9c_x12 h₂, hsp₁]; rv_eval []
    have hsl : stackLo u₂ mulStack = s.getReg .x2 - 1232 := by
      simp only [stackLo, mulStack, hsp₂, Sym.sub_sub_lit]; rfl
    have hpre₂ : MulPre u₂ := {
      out := by rw [hx10]; valid_sub hst.valid [hb]
      lhs := by
        rw [hx11]
        exact heap_valid_range (by addr_omega [hPa, hPN, hj, hpow])
          (by addr_omega [hPlo, hlo, hPN, hj, hpow]) (by addr_omega [hPN, hj, hpow])
      rhs := by rw [hx12]; valid_sub hst.valid [hb]
      stack := ⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [hsp₂]; addr_omega [hb]⟩
      outLhs := by rw [hx10, hx11]; addr_omega [hb, hab, hPN, hj, hpow]
      outRhs := by rw [hx10, hx12]; addr_omega [hb]
      outStack := by rw [hx10, hsl]; addr_omega [hb]
      lhsStack := by rw [hx11, hsl]; addr_omega [hb, hab, hPN, hj, hpow]
      rhsStack := by rw [hx12, hsl]; addr_omega [hb]
      rodata := mid₂.inv.rodataOk hpre
      stackRodata := by rw [hsl]; addr_omega [hb, hst.rodata] }
    obtain ⟨w, hr₃, ⟨hpc₃, hpres₃, hpost₃⟩ | hdead⟩ := hMul.call hr₂ (b8000cc9c_pc h₂) hpre₂
    swap
    · exact ⟨w, hr₁.trans hr₃, Or.inr hdead⟩
    have hdw := MulPost.dwFrame hpost₃
    rw [hx10, hsl] at hdw
    have hval := hpost₃.value
    rw [hx10, hx11, hx12] at hval
    have hX (a : Word) (ha : Within a (s.getReg .x2 - 160) 24 ∨
        Within a (s.getReg .x2 - 1232) mulStack) : Within a (s.getReg .x2 - 1232) 1096 := by
      rcases ha with ha | ha <;> addr_omega [ha, hb]
    have hr_eq : eAt u₂ (s.getReg .x2 - 128) = (pt s).getD k 0 := by
      rw [← hu.sc.plain htag]
      unfold eAt
      rw [hm₂, hm₂, hm₂, hm₁, hm₁, hm₁]
    have hP' : eAt w (P + BitVec.ofNat 64 (24 * j)) = eAt u₂ (P + BitVec.ofNat 64 (24 * j)) := by
      unfold eAt
      rw [DwFrame.keep hdw fun i hi hx ↦ by
          have := hX _ hx; addr_omega [this, hi, hb, hab, hPN, hj, hpow],
        DwFrame.keep hdw (a := P + BitVec.ofNat 64 (24 * j) + 8) fun i hi hx ↦ by
          have := hX _ hx; addr_omega [this, hi, hb, hab, hPN, hj, hpow],
        DwFrame.keep hdw (a := P + BitVec.ofNat 64 (24 * j) + 16) fun i hi hx ↦ by
          have := hX _ hx; addr_omega [this, hi, hb, hab, hPN, hj, hpow]]
    have hreg' (r : Reg) (hr : r ∈ [Reg.x9, .x18, .x19, .x20, .x21, .x22, .x23, .x25]) :
        w.getReg r = u₂.getReg r := hpres₃ r (by unfold calleeSaved; exact mem_of_mem hr _)
    have kk (a : Word) (h1 : (s.getReg .x2).toNat - 208 ≤ a.toNat)
        (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 160) : w.getMem a = u₂.getMem a :=
      DwFrame.keep hdw fun i hi hx ↦ by have := hx; rcases this with hx | hx <;> addr_omega [hx, hi, h1, h2, hb]
    have hnx : w.getMem nextAddr = nx := by
      rw [DwFrame.keep hdw fun i hi hx ↦ by rcases hx with hx | hx <;> addr_omega [hx, hi, hb, hnx8]]
      exact mid₂.inv.next
    have sc₂ : Sc s u₂ C P T nx ((pt s).getD k 0) :=
      Sc.step hpre hu.toMid hu.sc (DwFrame.same (fun a ↦ (hm₂ a).trans (hm₁ a)) fun _ ↦ False)
        (fun _ h ↦ h.elim) fun r hr ↦ by rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
    refine ⟨w, hr₁.trans hr₃, Or.inl {
      toMid := mid₂.step hpre hdw (fun a ha ↦ Or.inl (by have := hX a ha; addr_omega [this, hb]))
        (fun a ha ↦ by
          rcases ha with ha | ha
          · exact ⟨by addr_omega [ha, hb], by addr_omega [ha, hb]⟩
          · exact ⟨by addr_omega [ha, hb], by addr_omega [ha, hb]⟩)
        hnx (Nat.le_refl _) hfit
        fun r hr ↦ hpres₃ r (by unfold calleeSaved; exact mem_of_mem hr _)
      pc := by rw [hpc₃, returnAddress_eq, b8000cc9c_x1 h₂]; decide
      lt := hk
      jlt := hj
      m168 := by rw [kk _ (by addr_omega [hb]) (by addr_omega [hb]), hm₂, hm₁]; exact hu.m168
      m176 := by rw [kk _ (by addr_omega [hb]) (by addr_omega [hb]), hm₂, hm₁]; exact hu.m176
      x9 := by rw [hreg' _ (by decide), k₂ _ (by decide), hreg _ (by decide), hu.x9]
      x18 := by rw [hreg' _ (by decide), k₂ _ (by decide), hx18]
      x20 := by rw [hreg' _ (by decide), k₂ _ (by decide), hreg _ (by decide), hu.x20]
      x21 := by rw [hreg' _ (by decide), k₂ _ (by decide), hx21]
      x25 := by rw [hreg' _ (by decide), k₂ _ (by decide), hreg _ (by decide), hu.x25]
      sc := Sc.step hpre mid₂ sc₂ hdw (fun a ha ↦ Or.inl (hX a ha)) fun r hr ↦ hreg' r (mem_of_mem hr _)
      buf := by
        rw [← hbuf₁, eListAt_dw hdw (fun a ha hx ↦ by
            have := hX _ hx; addr_omega [this, ha, hb, hab, hPN]) (by omega),
          eListAt_same hm₂]
      prod := by rw [hval, hP', hr_eq] }⟩

theorem inner_loop (hMul : MulSpec) {s : MachineState} (hpre : EqKernelPre s) {C P T nx : Word}
    {k : Nat} {u : MachineState} (hu : IInv s u C P T nx k 0) :
    ∃ v, Reaches Image.code u v ∧ (Done s v C P nx k ∨ Dead Image.code v) := by
  refine Reaches.loop (code := Image.code) (fun v ↦ ∃ j, IInv s v C P T nx k j)
    (fun v ↦ 2 ^ k - (v.getReg .x25).toNat) _ (fun v ⟨j, hv⟩ ↦ ?_) u ⟨0, hu⟩
  have hj := hv.jlt
  have hk := hv.lt
  have h64 : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by have := nm_lt s; omega)
  obtain ⟨w, hr, hw | hd⟩ := inner_body hMul hpre hv
  · obtain ⟨x, hr', hx | hx⟩ := store hpre hw
    · refine Or.inr ⟨x, hr.trans hr', ⟨j + 1, hx⟩, ?_⟩
      rw [hx.x25, hv.x25, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
      have := hx.jlt
      omega
    · exact Or.inl ⟨x, hr.trans hr', Or.inl hx⟩
  · exact Or.inl ⟨w, hr, Or.inr hd⟩

/-! ## The outer loop's tail -/

theorem tail {s : MachineState} (hpre : EqKernelPre s) {C P nx : Word} {k : Nat}
    {u : MachineState} (hu : Done s u C P nx k) :
    ∃ v, Reaches Image.code u v ∧ (OInv s v C P nx (k + 1) ∨ Exit s v C P nx) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hk := hu.lt
  have hkn := nm_le s
  have hsp := hu.inv.sp
  have hpb := ValidMemRange.bounds (pointValid hpre (by omega)) (by omega)
  obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b8000cbf8_spec hu.pc (by
    rv_eval [hsp]; and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000cbf8_keeps h
  have hm := b8000cbf8_mem_same h
  have mid := hu.toMid.same hpre hm fun r hr ↦ k₁ r (mem_of_mem hr _)
  have e40 : u.getMem (u.getReg .x2 + 40) = s.getReg .x11 + BitVec.ofNat 64 (24 * k) := by
    rw [hsp]; rv_eval [hu.m168]
  have e32 : u.getMem (u.getReg .x2 + 32) = BitVec.ofNat 64 k := by rw [hsp]; rv_eval [hu.m176]
  have e16 : u.getMem (u.getReg .x2 + 16) =
      s.getReg .x11 + BitVec.ofNat 64 (24 * (s.getReg .x12).toNat) := by
    rw [hsp]; rv_eval [hu.stop]
  have hbuf := (eListAt_same hm P (2 ^ nm s)).trans hu.buf
  by_cases hlast : k + 1 = (s.getReg .x12).toNat
  · have hnm : nm s = (s.getReg .x12).toNat := nm_of_lt (by have := nm_lt s; omega)
    refine ⟨v, hr, Or.inr {
      toRes := mid.toRes
      pc := b8000cbf8_pc_taken h (by rw [e40, e16]; addr_omega [hpb, hlast])
      buf := ?_ }⟩
    have hl : (pt s).length = (s.getReg .x12).toNat := by rw [pt, eListAt_length]
    rw [hbuf, hlast, ← hl, List.take_of_length_le (Nat.le_refl _), hl, hnm, Nat.sub_self,
      List.replicate_zero, List.append_nil]
  · refine ⟨v, hr, Or.inl {
      toMid := mid
      pc := b8000cbf8_pc_not_taken h (by rw [e40, e16]; addr_omega [hpb, hlast, hk, hkn])
      lt := by omega
      le := hk
      x11 := by rw [b8000cbf8_x11 h, e40]; addr_omega [hpb, hk, hkn]
      x13 := by rw [b8000cbf8_x13 h, e32]; addr_omega [hk, nm_lt s]
      buf := hbuf }⟩

/-! ## The epilogue -/

theorem exit {s u : MachineState} {C P nx : Word} (hpre : EqKernelPre s) (hu : Exit s u C P nx) :
    ∃ t, Reaches Image.code u t ∧
      ((t.pc = returnAddress s ∧ Preserves s t ∧ EqKernelPost s t) ∨ Dead Image.code t) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := hu.inv.sp
  have sl := hu.inv.slots
  simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true] at sl
  rv_eval [] at sl
  obtain ⟨sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, sl10, sl11, sl12, sl13⟩ := sl
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b8000ce24_spec hu.pc (by
    rv_eval [hsp]; and_intros <;> valid_access hst.valid [hb])
  have k := b8000ce24_keeps ht
  have hm := b8000ce24_mem_same ht
  have pc := b8000ce24_pc ht
  have x2 := b8000ce24_x2 ht
  have x8 := b8000ce24_x8 ht
  have x9 := b8000ce24_x9 ht
  have x18 := b8000ce24_x18 ht
  have x19 := b8000ce24_x19 ht
  have x20 := b8000ce24_x20 ht
  have x21 := b8000ce24_x21 ht
  have x22 := b8000ce24_x22 ht
  have x23 := b8000ce24_x23 ht
  have x24 := b8000ce24_x24 ht
  have x25 := b8000ce24_x25 ht
  have x26 := b8000ce24_x26 ht
  have x27 := b8000ce24_x27 ht
  rv_eval [hsp, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, sl10, sl11, sl12, sl13]
    at pc x2 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
  have hnt : t.getMem nextAddr = nx := (hm _).trans hu.inv.next
  have hn : heapNext t = nx.toNat := by simp only [heapNext, hnt]
  have hlo := hpre.heap.lo
  have hmono := hu.inv.mono
  have hfit := hu.inv.fits
  have htop := hu.top
  have hroom := hu.room
  have hPlo := hu.lo
  have hpos := Nat.two_pow_pos (nm s)
  have hN : 2 ^ nm s < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (nm_lt s)
  have hlen : (vecLen t (s.getReg .x10)).toNat = 2 ^ nm s := by
    simp only [vecLen, hm, hu.len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN]
  refine ⟨t, hr, Or.inl ⟨pc.trans (returnAddress_eq s).symm,
    preserves_of x2 x8 x9 x18 x19 fun r hr' ↦ ?_, {
      heap := ⟨by rw [hn]; simp only [heapNext] at hlo hmono ⊢; omega, by rw [hn]; exact hfit⟩
      mono := by rw [hn]; exact hmono
      value := {
        vec := ⟨⟨by simp only [vecPtr, hm, hu.ptr]; exact hu.align, Or.inr ⟨by
            simp only [vecPtr, hm, hu.ptr]; simp only [heapStart, heapNext] at hlo hPlo ⊢; omega,
          by simp only [vecPtr, vecCap, hm, hu.ptr, hu.cap, hn]; omega⟩⟩,
          by rw [hlen]; simp only [vecCap, hm, hu.cap]; exact hroom⟩
        buf := ⟨by simp only [vecPtr, hm, hu.ptr]; exact hu.align, Or.inr ⟨by
            simp only [vecPtr, hm, hu.ptr]; exact hPlo,
          by simp only [vecPtr, vecCap, hm, hu.ptr, hu.cap, hn]; omega⟩⟩
        elems := by
          rw [vecEs, hlen, Model.eqKernelRust_eq]
          simp only [vecPtr, hm, hu.ptr]
          rw [eListAt_same hm, hu.buf]
          rfl }
      frame := fun a ha ↦ ?_ }⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact x20
    · exact x21
    · exact x22
    · exact x23
    · exact x24
    · exact x25
    · exact x26
    · exact x27
  · have hsub (b : Word) (hb' : PW s nx b) : Within b (s.getReg .x10) 24 ∨
        Within b (stackLo s eqKernelStack) eqKernelStack ∨ Within b nextAddr 8 ∨ Fresh s t b := by
      simp only [PW, LW] at hb'
      rcases hb' with hw | hw | hw | hw
      · exact Or.inl hw
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr (Or.inl hw))
      · exact Or.inr (Or.inr (Or.inr (by simp only [Fresh, hn]; exact hw)))
    rw [hm a]
    exact hu.inv.dw a (fun hw ↦ ha 0 (by decide) (by simpa using hsub a hw))
      (Or.inr fun i hi hw ↦ ha i hi (hsub _ hw))

/-! ## `eq_kernel` -/

/-- **`eq_kernel` meets its contract**, given `from_elem`'s, `Scaler::new`'s and `mul`'s. -/
theorem eq_kernel_spec (hF : FromElemSpec) (hS : ScalerSpec) (hMul : MulSpec) : EqKernelSpec := by
  intro s hpc hpre
  obtain ⟨u, hr, ⟨C, P, nx, hu⟩ | ⟨C, P, nx, hu⟩ | hd⟩ := prologue hF hpc hpre
  · obtain ⟨v, hr', hv⟩ := Reaches.loop (code := Image.code) (fun v ↦ ∃ nx k, OInv s v C P nx k)
      (fun v ↦ (s.getReg .x12).toNat - (v.getReg .x13).toNat)
      (fun v ↦ (∃ nx, Exit s v C P nx) ∨ Dead Image.code v) (fun v ⟨nx, k, hv⟩ ↦ by
        have hk := hv.lt
        have hkm := hv.le
        have h64 := nm_lt s
        obtain ⟨w, hr₁, ⟨T, nx', hw⟩ | hd⟩ := outer_head hS hpre hv
        · obtain ⟨x, hr₂, hx | hd⟩ := inner_loop hMul hpre hw
          · obtain ⟨y, hr₃, hy | hy⟩ := tail hpre hx
            · refine Or.inr ⟨y, hr₁.trans (hr₂.trans hr₃), ⟨nx', k + 1, hy⟩, ?_⟩
              rw [hy.x13, hv.x13, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
                Nat.mod_eq_of_lt (by omega)]
              have := hy.lt
              omega
            · exact Or.inl ⟨y, hr₁.trans (hr₂.trans hr₃), Or.inl ⟨nx', hy⟩⟩
          · exact Or.inl ⟨x, hr₁.trans hr₂, Or.inr hd⟩
        · exact Or.inl ⟨w, hr₁, Or.inr hd⟩) u ⟨nx, 0, hu⟩
    rcases hv with ⟨nx', he⟩ | hd
    · obtain ⟨t, hr'', ht⟩ := exit hpre he
      exact ⟨t, hr.trans (hr'.trans hr''), ht⟩
    · exact ⟨v, hr.trans hr', Or.inr hd⟩
  · obtain ⟨t, hr', ht⟩ := exit hpre hu
    exact ⟨t, hr.trans hr', ht⟩
  · exact ⟨u, hr, Or.inr hd⟩

end Rv64Verifier.Proofs.Multilinear.EqKernel
