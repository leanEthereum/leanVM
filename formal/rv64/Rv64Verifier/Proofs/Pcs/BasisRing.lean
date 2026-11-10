import Rv64Verifier.Proofs.Pcs.BasisEval

/-!
# `<StackBasis>::evaluate`: a `Ring` weight, `RingWeight::evaluate(x)` at `0x8000d1cc`

`ringSrc_callee` carries a claim's `RingWeight` over to the callee: what `RingWeight::evaluate`
reads, from its own stack, and the same weight.
-/

namespace Rv64Verifier.Proofs.Pcs.Basis
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.FieldContracts
  Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F55
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- A `Vec<E>` read keeps its elements. -/
theorem Inv.vecEs {s u : MachineState} {nx : Word} (h : Inv s u nx) {a : Word}
    (hs : Src s basisStack a 24) (hb : Src s basisStack (vecPtr s a) (24 * (vecLen s a).toNat)) :
    vecEs u a = vecEs s a ∧ vecPtr u a = vecPtr s a ∧ vecLen u a = vecLen s a := by
  have hbd := hs.bound
  have h8 : vecPtr u a = vecPtr s a :=
    Inv.word h hs (by rcases hbd with h0 | h0 <;> addr_omega [h0]) (by
      rcases hbd with h0 | h0
      · omega
      · addr_omega [h0])
  have h16 : vecLen u a = vecLen s a :=
    Inv.word h hs (by rcases hbd with h0 | h0 <;> addr_omega [h0]) (by
      rcases hbd with h0 | h0
      · omega
      · addr_omega [h0])
  refine ⟨?_, h8, h16⟩
  simp only [Runtime.vecEs]
  rw [h8, h16]
  exact Inv.eList h hb

/-- The `RingWeight` at `a`, inside claim `k`, read by `RingWeight::evaluate` called with `sp`
192 below the entry's. -/
theorem ringSrc_callee {s c : MachineState} {nx : Word} (hpre : BasisPre s) (h : Inv s c nx)
    {a : Word} (hr : RingSrc s basisStack a) :
    RingSrc c ringEvalStack a ∧ ringWeightAt c a = ringWeightAt s a := by
  have hb := bounds hpre
  have hsp := h.sp
  have hn : heapNext s ≤ heapNext c := by
    have := h.mono; simp only [heapNext, h.next] at this ⊢; exact this
  have hlo : (stackLo s basisStack).toNat ≤ (stackLo c ringEvalStack).toNat := by
    simp only [stackLo, hsp, basisStack, ringEvalStack, mulStack]; addr_omega [hb]
  have hhi : (stackLo c ringEvalStack).toNat + ringEvalStack ≤ (stackLo s basisStack).toNat + basisStack := by
    simp only [stackLo, hsp, basisStack, ringEvalStack, mulStack]; addr_omega [hb]
  have hk : (stackLo s basisStack).toNat + basisStack ≤ 2 ^ 64 := by
    simp only [stackLo, basisStack, ringEvalStack, mulStack]; addr_omega [hb]
  have hs24 : Src s basisStack (a + 24) 24 := by
    have := Region.bounds (hr.self.region.resolve_left (by decide))
    exact hr.self.sub (by addr_omega [this]) (by addr_omega [this]) (by addr_omega [this])
  have hs0 : Src s basisStack a 24 := by
    have := Region.bounds (hr.self.region.resolve_left (by decide))
    exact hr.self.sub (Nat.le_refl _) (by omega) this.2.2
  obtain ⟨e0, p0, l0⟩ := Inv.vecEs h hs0 hr.point
  obtain ⟨e1, p1, l1⟩ := Inv.vecEs h hs24 hr.coeffs
  refine ⟨⟨hr.self.callee hlo hhi hk hn, ?_, ?_⟩, ?_⟩
  · rw [p0, l0]; exact hr.point.callee hlo hhi hk hn
  · rw [p1, l1]; exact hr.coeffs.callee hlo hhi hk hn
  · simp only [ringWeightAt, e0, e1]

theorem ring_weight {s : MachineState} {k : Nat} (htag : s.getMem (claimAddr s k) = ringTag) :
    weightOf s k = (ringWeightAt s (claimAddr s k + 8)).evaluate (ptl s) := by
  have hne : ¬ s.getMem (claimAddr s k) = eqTag := by rw [htag]; decide
  simp only [weightOf, stackClaimAt, stackWeightAt]
  rw [ite_neg' hne, ite_pos' htag]
  rfl

theorem evalRing (hR : RingEvalSpec) {s u : MachineState} {nx WP : Word} {k : Nat}
    (hpre : BasisPre s) (hh : Head s u nx WP k 0x8000d1cc)
    (htag : s.getMem (claimAddr s k) = ringTag) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ ∃ nx', Got s v nx' WP k) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hk := hh.lt
  have hsp := hh.inv.sp
  have hne : ¬ s.getMem (claimAddr s k) = eqTag := by rw [htag]; decide
  have hws : WeightSrc s basisStack (claimAddr s k) := hpre.weights k hk
  have hrs : RingSrc s basisStack (claimAddr s k + 8) := by
    have h2 := hws.2
    change (if s.getMem (claimAddr s k) = eqTag then _ else _) at h2
    rw [ite_neg' hne, ite_pos' htag] at h2
    exact h2
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000d1cc_spec hh.pc trivial
  have k₁ := b8000d1cc_keeps h₁
  have hm₁ := b8000d1cc_mem_same h₁
  have inv₁ := hh.inv.same hm₁ (k₁ .x2 (by decide)) (fun r hr ↦ by
    simp only [List.mem_singleton] at hr; subst hr; exact k₁ _ (by decide))
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 192 := inv₁.sp
  have hx10 : t₁.getReg .x10 = s.getReg .x2 - 168 := by rw [b8000d1cc_x10 h₁, hsp]; rv_eval []
  have hx11 : t₁.getReg .x11 = claimAddr s k + 8 := by rw [b8000d1cc_x11 h₁, hh.x20]
  have hx12 : t₁.getReg .x12 = s.getReg .x12 := by rw [b8000d1cc_x12 h₁, hh.x19]
  have hx13 : t₁.getReg .x13 = s.getReg .x13 := by rw [b8000d1cc_x13 h₁, hh.x18]
  obtain ⟨hrc, hrw⟩ := ringSrc_callee hpre inv₁ hrs
  have hmp := hst.mapped (by decide) (by decide)
  have hsl : stackLo t₁ ringEvalStack = s.getReg .x2 - 1392 := by
    simp only [stackLo, hsp₁, ringEvalStack, mulStack, Nat.reduceAdd]; rv_eval []
  have hn₁ : heapNext s ≤ heapNext t₁ := by
    have := inv₁.mono; simp only [heapNext, inv₁.next] at this ⊢; exact this
  have hlo : (stackLo s basisStack).toNat ≤ (stackLo t₁ ringEvalStack).toNat := by
    rw [hsl]; simp only [stackLo, basisStack, ringEvalStack, mulStack]; addr_omega [hb]
  have hhi : (stackLo t₁ ringEvalStack).toNat + ringEvalStack ≤
      (stackLo s basisStack).toNat + basisStack := by
    rw [hsl]; simp only [stackLo, basisStack, ringEvalStack, mulStack]; addr_omega [hb]
  have hkk : (stackLo s basisStack).toNat + basisStack ≤ 2 ^ 64 := by
    simp only [stackLo, basisStack, ringEvalStack, mulStack]; addr_omega [hb]
  have hab := hst.above
  have hnx8 := hst.next
  have hro := hst.rodata
  have hselfS := hrs.self.stack
  have hptS := hrs.point.stack
  have hcoS := hrs.coeffs.stack
  have hpS := hpre.point.stack
  obtain ⟨-, p0, l0⟩ := Inv.vecEs inv₁ (hrs.self.sub (Nat.le_refl _) (by omega)
    (Region.bounds (hrs.self.region.resolve_left (by decide))).2.2) hrs.point
  have hs24 : Src s basisStack (claimAddr s k + 8 + 24) 24 := by
    have := Region.bounds (hrs.self.region.resolve_left (by decide))
    exact hrs.self.sub (by addr_omega [this]) (by addr_omega [this]) (by addr_omega [this])
  obtain ⟨-, p1, l1⟩ := Inv.vecEs inv₁ hs24 hrs.coeffs
  have hpreR : RingEvalPre t₁ := {
    heap := inv₁.heap hpre.heap
    stack := hst.sub 192 hsp₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    rodata := Inv.rodata' hpre inv₁
    out := {
      region := by
        rw [hx10]
        simp only [Region, Mapped]
        simp only [stackLo, basisStack, ringEvalStack, mulStack] at hmp
        constructor
        · right; addr_omega [hmp, hb]
        · addr_omega [hb]
      stack := by rw [hx10, hsl]; addr_omega [hb]
      free := by
        rw [hx10]; simp only [Outside]
        exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
      rodata := by rw [hx10]; addr_omega [hro, hb] }
    self := by rw [hx11]; exact hrc
    rPrime := by rw [hx12, hx13]; exact hpre.point.callee hlo hhi hkk hn₁
    outSelf := by rw [hx10, hx11]; addr_omega [hselfS, hb]
    outPoint := by rw [hx10, hx11, p0, l0]; addr_omega [hptS, hb]
    outCoeffs := by rw [hx10, hx11, p1, l1]; addr_omega [hcoS, hb]
    outRPrime := by rw [hx10, hx12, hx13]; addr_omega [hpS, hb] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hdead⟩ := hR.call hr₁ (b8000d1cc_pc h₁) hpreR
  swap
  · exact ⟨t₂, hr₂, Or.inl hdead⟩
  have hfr₂ := hpost₂.frame
  rw [hx10, hsl] at hfr₂
  have hfit₂ := hpost₂.heap.hi
  have hnt : heapNext t₁ = (u.getMem nextAddr).toNat := by simp only [heapNext, hm₁]
  have inv₂ := Inv.step' hpre inv₁ hfr₂
    (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inr (Or.inl (by simp only [basisStack, ringEvalStack, mulStack, stackLo]; addr_omega [ha, hb]))
      · exact Or.inr (Or.inl (by simp only [basisStack, ringEvalStack, mulStack, stackLo]; addr_omega [ha, hb]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · refine Or.inr (Or.inr (Or.inr ⟨?_, ha.2⟩))
        have := inv₁.mono; have h1 := ha.1
        simp only [heapNext, inv₁.next] at this h1 ⊢; omega)
    (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · addr_omega [ha, hb]
      · addr_omega [ha, hb]
      · addr_omega [ha, hb, hnx8]
      · simp only [Fresh] at ha; addr_omega [ha, hb, hab, hfit₂])
    rfl (by have := hpost₂.mono; simp only [heapNext, inv₁.next] at this ⊢; exact this) hfit₂
    (hpres₂.reg .x2) (hpres₂.reg .x27)
  have hval := hpost₂.value
  rw [hx10, hx11, hx12, hx13, hrw] at hval
  have eX : eListAt t₁ (s.getReg .x12) (s.getReg .x13).toNat = ptl s := by
    rw [ptl, ← Inv.eList hh.inv hpre.point]; simp only [eListAt, eAt, hm₁]
  rw [eX] at hval
  -- the jump back
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 192 := inv₂.sp
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000d1e4_spec
    (by rw [hpc₂, returnAddress_eq, b8000d1cc_x1 h₁]; decide) trivial
  have k₃ := b8000d1e4_keeps h₃
  have hm₃ := b8000d1e4_mem_same h₃
  refine ⟨t₃, hr₂.trans hr₃, Or.inr ⟨_, {
    toRegs := hh.toRegs.of_eq fun r hr ↦ by
      rw [k₃ r (Runtime.mem_of_mem hr _),
        hpres₂ r (by unfold calleeSaved; exact Runtime.mem_of_mem hr _), k₁ r (Runtime.mem_of_mem hr _)]
    inv := inv₂.same hm₃ (k₃ .x2 (by decide)) (fun r hr ↦ by
      simp only [List.mem_singleton] at hr; subst hr; exact k₃ _ (by decide))
    pc := b8000d1e4_pc h₃
    lt := hk
    buf := ⟨hh.buf.align, by
      rcases hh.buf.range with h0 | h0
      · exact Or.inl h0
      · refine Or.inr ⟨h0.1, ?_⟩
        have := hpost₂.mono; simp only [heapNext, inv₁.next] at this; omega⟩
    ws := fun l hl ↦ by
      have e := ws_keep hpre hh.buf hh.inv.fits hk hfr₂ (fun a ha ↦ by
        rcases ha with ha | ha | ha | ha
        · left; simp only [basisStack, ringEvalStack, mulStack, stackLo]; addr_omega [ha, hb]
        · left; simp only [basisStack, ringEvalStack, mulStack, stackLo]; addr_omega [ha, hb]
        · exact Or.inr (Or.inl ha)
        · right; right; have h1 := ha.1; simp only [heapNext, hm₁, hh.inv.next] at h1; exact h1) l hl
      simp only [eAt, hm₃]
      simp only [eAt] at e
      rw [e]
      simp only [hm₁]
      exact hh.ws l hl
    w := by rw [ring_weight htag, hval]; simp only [eAt, hm₃] }⟩⟩

end Rv64Verifier.Proofs.Pcs.Basis
