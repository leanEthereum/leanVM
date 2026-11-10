import Rv64Verifier.Proofs.Pcs.ExtendOld

/-!
# `Vec<StackClaim>::extend_desugared`: the prologue

`0x80009b94` saves the registers and tests for an empty iterator; `0x80009bd8` loads the loop's
registers. To `Done` (no claims) or the first `Head`.
-/

namespace Rv64Verifier.Proofs.Pcs.Extend
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Transcript Rv64Verifier.Pcs
  Rv64Verifier.PcsContracts Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F37 LeanVM.Parameters
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x80009d7c`, every claim done. -/
structure Done (s u : MachineState) : Prop where
  p : PInv s u 240 extendStack slots [] (W s) (u.getMem nextAddr)
  vec : VecOk u (s.getReg .x10) 88 8
  value : stackClaimsAt u (s.getReg .x10) = stackClaimsAt s (s.getReg .x10) ++
    (columnClaimsAt s (itCur s) (itCount s)).filterMap (onStackS s)
  pc : u.pc = 0x80009d7c

theorem Exit.done {s u : MachineState} (h : Exit s u) : Done s u :=
  ⟨h.inv.p, h.inv.vec, h.inv.value, h.pc⟩

/-- The `Vec` and its claims across the saves. -/
theorem entry_keep {s t : MachineState} (hpre : ExtendPre s)
    (hf : DFrame s t fun x ↦ Within x (s.getReg .x2 - 104) 104) :
    VecOk t (s.getReg .x10) 88 8 ∧ vecLen t (s.getReg .x10) = vecLen s (s.getReg .x10) ∧
      vecCap t (s.getReg .x10) = vecCap s (s.getReg .x10) ∧
      vecPtr t (s.getReg .x10) = vecPtr s (s.getReg .x10) ∧ heapNext t = heapNext s ∧
      ∀ i < (vecLen s (s.getReg .x10)).toNat,
        stackClaimAt t (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (88 * i)) =
          stackClaimAt s (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (88 * i)) ∧
        ClaimRegions (Safe s t) t (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (88 * i)) := by
  have hb := sbounds hpre
  have hAb := Region.bounds hpre.self.region
  have hAs := hpre.self.stack
  have hnS := hpre.stack.next
  rw [hK] at hAs hnS
  have w (o : Word) (ho : o.toNat + 8 ≤ 24) : t.getMem (s.getReg .x10 + o) = s.getMem (s.getReg .x10 + o) :=
    hf.word (fun x hx hw ↦ by addr_omega [hx, hw, hAs, hAb, hb, ho]) (by addr_omega [hAb, ho])
  have hC : vecCap t (s.getReg .x10) = vecCap s (s.getReg .x10) := by
    have := w (BitVec.ofNat 64 0) (by decide)
    rw [add_ofNat_zero] at this
    exact this
  have hP : vecPtr t (s.getReg .x10) = vecPtr s (s.getReg .x10) := w 8 (by decide)
  have hL : vecLen t (s.getReg .x10) = vecLen s (s.getReg .x10) := w 16 (by decide)
  have hn : heapNext t = heapNext s := by
    simp only [heapNext]
    rw [hf.word (fun x hx hw ↦ by addr_omega [hx, hw, hnS, hb]) (by decide)]
  have hsl : spareLo t (s.getReg .x10) = spareLo s (s.getReg .x10) := by simp only [spareLo, hP, hL]
  have hsn : spareLen t (s.getReg .x10) = spareLen s (s.getReg .x10) := by simp only [spareLen, hC, hL]
  have hS (a : Word) (n : Nat) (ha : Safe s s a n) : Safe s t a n := by
    simp only [Safe, hn, hsl, hsn]; exact ha
  have hv := hpre.vec
  refine ⟨⟨by simp only [RawVecOk, Buf, hP, hC, hn]; exact hv.raw, by rw [hL, hC]; exact hv.len⟩,
    hL, hC, hP, hn, fun i hi ↦ ?_⟩
  have hcl := claim_pre hpre hi
  have he := hcl.1
  have heb : (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (88 * i)).toNat + 88 ≤ 0xc0000000 := by
    rcases he.bound with h | h
    · omega
    · exact h
  have hst : Apart (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (88 * i)) 88
      (stackLo s extendStack) extendStack := by
    rcases he with h | ⟨-, -, h, -⟩
    · omega
    · exact h
  rw [hK] at hst
  refine claim_move (fun j hj ↦ hf.word (fun x hx hw ↦ by addr_omega [hx, hw, hst, heb, hj, hb])
      (by addr_omega [heb, hj])) hcl (fun a m hm ↦ hf.eList (fun x hx hw ↦ ?_) ?_) hS (hS _ _ he)
  · rcases hm with h0 | ⟨hR, -, h2, -⟩
    · simp only [Within] at hx; omega
    · rw [hK] at h2; have := Region.bounds hR; addr_omega [hx, hw, h2, this, hb]
  · rcases hm.bound with h | h
    · left; omega
    · right; omega

theorem value0 {s t : MachineState}
    (hP : vecPtr t (s.getReg .x10) = vecPtr s (s.getReg .x10))
    (hL : vecLen t (s.getReg .x10) = vecLen s (s.getReg .x10))
    (hcl : ∀ i < (vecLen s (s.getReg .x10)).toNat,
      stackClaimAt t (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (88 * i)) =
        stackClaimAt s (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (88 * i))) :
    stackClaimsAt t (s.getReg .x10) = stackClaimsAt s (s.getReg .x10) ++
      (columnClaimsAt s (itCur s) 0).filterMap (onStackS s) := by
  rw [stackClaimsAt, hP, hL, claimsAt_congr hcl]
  simp only [columnClaimsAt, List.range_zero, List.map_nil, List.filterMap_nil, List.append_nil]
  rfl

theorem prologue {s : MachineState} (hpc : s.pc = 0x80009b94) (hpre : ExtendPre s) :
    ∃ t, Reaches Image.code s t ∧ (Done s t ∨ Head s t 0) := by
  have hb := sbounds hpre
  have hv := hpre.stack.valid
  rw [hK] at hv
  have hIt := hpre.iter
  have hIb := Region.bounds hIt.region
  have hIs := hIt.stack
  rw [hK] at hIs
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80009b94_spec hpc (by
    rv_eval []
    and_intros <;> first
      | valid_access hv [hb]
      | exact Region.valid hIt.region (by addr_omega [hIb]) (by addr_omega [hIb]) (by addr_omega [hIb])
      | addr_omega [hIs, hIb, hb])
  have hf₁ := DFrame.of_memFrame (b80009b94_frame h₁ (by omega))
  obtain ⟨hvec, hL, hC, hP, hn, hcl⟩ := entry_keep hpre hf₁
  have k₁ := b80009b94_keeps h₁
  have hp₁ : PInv s t₁ 240 extendStack slots [] (W s) (t₁.getMem nextAddr) := {
    sp := b80009b94_x2 h₁
    slots := by
      simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact ⟨b80009b94_m_x2_n8 h₁, b80009b94_m_x2_n16 h₁, b80009b94_m_x2_n24 h₁,
        b80009b94_m_x2_n32 h₁, b80009b94_m_x2_n40 h₁, b80009b94_m_x2_n48 h₁, b80009b94_m_x2_n56 h₁,
        b80009b94_m_x2_n64 h₁, b80009b94_m_x2_n72 h₁, b80009b94_m_x2_n80 h₁, b80009b94_m_x2_n88 h₁,
        b80009b94_m_x2_n96 h₁, b80009b94_m_x2_n104 h₁⟩
    kept := fun r hr ↦ by simp at hr
    mem := hf₁.mono fun a h ↦ Or.inr (Or.inl (by rw [hK]; addr_omega [h, hb]))
    next := rfl
    mono := le_of_eq hn.symm
    fits := by have := hpre.heap.hi; rw [← hn] at this; exact this }
  have hbnd := hpre.bounds
  by_cases he : itCur s = itEnd s
  · have h0 : itCount s = 0 := by simp only [itCount, he, Nat.sub_self, Nat.zero_div]
    refine ⟨t₁, hr₁, Or.inl ⟨hp₁, hvec, by rw [h0]; exact value0 hP hL fun i hi ↦ (hcl i hi).1,
      b80009b94_pc_taken h₁ he⟩⟩
  have hne : (itCur s).toNat ≠ (itEnd s).toNat := fun h ↦ he (BitVec.eq_of_toNat_eq h)
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80009bd8_spec (b80009b94_pc_not_taken h₁ he) (by
    rv_eval [k₁ .x11 (by decide)]
    exact Region.valid hIt.region (by addr_omega [hIb]) (by addr_omega [hIb]) (by addr_omega [hIb]))
  have m₂ := b80009bd8_mem_same h₂
  have k₂ := b80009bd8_keeps h₂
  have hf₂ : DFrame s t₂ fun x ↦ Within x (s.getReg .x2 - 104) 104 :=
    hf₁.trans (DFrame.of_same m₂ _) fun _ h ↦ h
  obtain ⟨hvec₂, hL₂, hC₂, hP₂, hn₂, hcl₂⟩ := entry_keep hpre hf₂
  have h16 : t₂.getMem (s.getReg .x11 + 16) = s.getMem (s.getReg .x11 + 16) := by
    rw [m₂]; exact hf₁.word (fun x hx hw ↦ by addr_omega [hx, hw, hIs, hIb, hb]) (by addr_omega [hIb])
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - 240 := (k₂ .x2 (by decide)).trans (b80009b94_x2 h₁)
  refine ⟨t₂, hr₁.trans hr₂, Or.inr ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hvec₂, Or.inl (by rw [hL₂, hC₂]; exact hpre.full),
    fun i hi ↦ by rw [hP₂]; rw [hL₂] at hi; exact (hcl₂ i hi).2,
    value0 hP₂ hL₂ fun i hi ↦ (hcl₂ i hi).1, Nat.zero_le _⟩, b80009bd8_pc h₂, ?_, ?_⟩⟩
  · rw [m₂]; exact hp₁.same m₂ (k₂ .x2 (by decide)) fun r hr ↦ by simp at hr
  · rw [b80009bd8_x8 h₂, k₁ .x11 (by decide)]
  · rw [b80009bd8_x9 h₂, k₁ .x10 (by decide)]
  · rw [k₂ .x19 (by decide), b80009b94_x19 h₁]; rfl
  · rw [b80009bd8_x20 h₂, k₁ .x11 (by decide), ← m₂, h16]; rfl
  · rw [b80009bd8_x21 h₂, b80009b94_x2 h₁]; addr_omega [hb]
  · exact b80009bd8_x22 h₂
  · exact b80009bd8_x23 h₂
  · exact b80009bd8_x24 h₂
  · rw [k₂ .x25 (by decide), b80009b94_x25 h₁]
    simp only [clAt, Nat.mul_zero, add_ofNat_zero]; rfl
  · simp only [itCount]
    omega

end Rv64Verifier.Proofs.Pcs.Extend
