import Rv64Verifier.Proofs.Pcs.VsoOpenCalls

/-!
# `verify_stacked_opening`'s level loop: the opening's first block

`0x8000a304` spills the level's registers, sets up the pending claims' empty `Vec` at `S - 616`,
copies the root's bytes `0..6` to `S - 592`, and branches on the last level (`0x8000a37c`) or not
(`0x8000a534`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The root's bytes `0..6` merged into a doubleword. -/
theorem low7 (old w : Word) :
    Sym.StoreKind.b.merge
      (Sym.StoreKind.h.merge
        (Sym.StoreKind.w.merge old 0
          (BitVec.zeroExtend 64 (extractByte w 3) <<< ((24#64).toNat % 64) |||
              BitVec.zeroExtend 64 (extractByte w 2) <<< ((16#64).toNat % 64) |||
            (BitVec.zeroExtend 64 (extractByte w 1) <<< ((8#64).toNat % 64) |||
              BitVec.zeroExtend 64 (extractByte w 0))))
        4
        (BitVec.zeroExtend 64 (extractByte w 5) <<< ((8#64).toNat % 64) |||
          BitVec.zeroExtend 64 (extractByte w 4)))
      6 (BitVec.zeroExtend 64 (extractByte w 6)) &&& 0x00ffffffffffffff =
    w &&& 0x00ffffffffffffff := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Sym.StoreKind.merge, replaceWord32, replaceHalfword, replaceByte, BitVec.getLsbD_and,
    BitVec.getLsbD_or, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.zeroExtend_eq_setWidth, getLsbD_extractByte]
  interval_cases i <;> simp

/-- A halfword or word access in the stack. -/
theorem stack_valid {s : MachineState} (hpre : VsoPre s) {a : Word} {k : ℕ} (hk : k = 2 ∨ k = 4)
    (h1 : (s.getReg .x2 - 2464).toNat ≤ a.toNat) (h2 : a.toNat + k ≤ (s.getReg .x2).toNat)
    (ha : a.toNat % k = 0) : Sym.validAccess k a = true := by
  have hsm := stack_mapped hpre
  have hv : isValidMemAddr a = true := by
    simp only [isValidMemAddr, MEM_START, MEM_END, INPUT_MEM_START, INPUT_MEM_END,
      RAM_MEM_START, RAM_MEM_END, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    addr_omega [hsm, h1, h2, hk]
  rcases hk with rfl | rfl <;>
    simp only [Sym.validAccess, isValidHalfwordAccess_eq, isValidMemAccess, isAligned2,
      isAligned4, Bool.and_eq_true, beq_iff_eq] <;> exact ⟨hv, ha⟩

/-- The slots the fold rounds keep above `S - 856`. -/
theorem FW.keepHi {s : MachineState} {x : LCtx} {h u : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {fl lfs q : List E} (hpre : VsoPre s)
    (hr : RB s x h u ℓ Wl fl lfs q) {y : Word}
    (hy : (s.getReg .x2 - 848).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 832).toNat) :
    u.getMem y = h.getMem y := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hf := hr.head.facts
  have hhi := hr.heap.hi
  refine hr.fr y fun i hi hw ↦ ?_
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
  · addr_omega [hw, hi, hy, hb]
  · addr_omega [hw, hi, hy, hb]
  · addr_omega [hw, hi, hy, hb]
  · addr_omega [hw, hi, hy, hb]
  · addr_omega [hw, hi, hy, hb]
  · addr_omega [hw, hi, hy, hb]
  · addr_omega [hw, hi, hy, hb, hnx]
  · addr_omega [hw.2, hi, hy, hb, hhi]
  · simp only [W] at hw; addr_omega [hw, hi, hy, hb, hIs, hS]
  · rcases hf.F with h0 | h0
    · simp only [Within] at hw; omega
    · addr_omega [hw, hi, hy, hb, h0.2, hf.hend]

/-- After the fold rounds, the root's address is at `S - 840`. -/
theorem Folded.root {s : MachineState} {x : LCtx} {h t : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf q : List E} (hpre : VsoPre s) (hf : Folded s x h t ℓ Wl lf q) :
    t.getMem (s.getReg .x2 - 840) = s.getReg .x11 := by
  have hb := bounds hpre
  have hh := hf.head
  have hk := LM.kept hpre hh.fr hh.heap.hi hh.cfg.kept
  rw [FW.keepHi hpre hf.toRB (by addr_omega [hb])]
  exact hk.root

/-- After `0x8000a304`, from the fold rounds' end `t`. -/
structure At304 (s : MachineState) (x : LCtx) (h t u : MachineState) (ℓ : ℕ)
    (Wl : Model.Pcs.WhirLocals) (lf q : List E) : Prop where
  fo : Folded s x h t ℓ Wl lf q
  fr : DFrame t u fun a ↦ Within a (s.getReg .x2 - 928) 8 ∨ Within a (s.getReg .x2 - 912) 8 ∨
    Within a (s.getReg .x2 - 896) 8 ∨ Within a (s.getReg .x2 - 872) 8 ∨
    Within a (s.getReg .x2 - 808) 8 ∨ Within a (s.getReg .x2 - 792) 8 ∨
    Within a (s.getReg .x2 - 616) 32
  regs : ∀ r ∈ [Reg.x1, .x2, .x5, .x6, .x8, .x9, .x17, .x22, .x23, .x25, .x26, .x27],
    u.getReg r = t.getReg r
  x13 : u.getReg .x13 = s.getReg .x12 - BitVec.ofNat 64 (Wl.folds ++ lf).length
  x16 : u.getReg .x16 = s.getReg .x11
  m144 : u.getMem (s.getReg .x2 - 896) = t.getReg .x22
  m168 : u.getMem (s.getReg .x2 - 872) = s.getReg .x12 - BitVec.ofNat 64 (Wl.folds ++ lf).length
  m440 : u.getMem (s.getReg .x2 - 600) = 0
  m432 : u.getMem (s.getReg .x2 - 608) = 8
  m424 : u.getMem (s.getReg .x2 - 616) = 0
  m112 : u.getMem (s.getReg .x2 - 928) = BitVec.ofNat 64 (Wl.folds ++ lf).length
  m128 : u.getMem (s.getReg .x2 - 912) = s.getReg .x12
  m248 : u.getMem (s.getReg .x2 - 792) = s.getReg .x10 + 8
  m232 : u.getMem (s.getReg .x2 - 808) = t.getReg .x23
  low : u.getMem (s.getReg .x2 - 592) &&& 0x00ffffffffffffff =
    u.getMem (s.getReg .x11) &&& 0x00ffffffffffffff
  root : digestAt u (s.getReg .x11) = digestAt t (s.getReg .x11)

/-- **`0x8000a304`**: to `0x8000a37c` at the last level, else to `0x8000a534`. -/
theorem open304 {s : MachineState} {x : LCtx} {h t : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf q : List E} (hpre : VsoPre s) (hf : Folded s x h t ℓ Wl lf q) :
    ∃ u, Reaches Image.code t u ∧ At304 s x h t u ℓ Wl lf q ∧
      (ℓ = K0 s + 1 → u.pc = 0x8000a37c) ∧ (ℓ ≠ K0 s + 1 → u.pc = 0x8000a534) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp : t.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := hf.sp
  have h200 := Folded.root hpre hf
  have hr := hpre.root
  have hrst := hr.stack
  rw [stackLo_vso, vso_stack] at hrst
  have hR : Region (s.getReg .x11) 32 := by
    rcases hr.region with h0 | h0
    · cases h0
    · exact h0
  have hRb := Region.bounds hR
  have hM := hR.1
  simp only [Mapped] at hM
  have hK := K0_lt s
  have hsm := stack_mapped hpre
  have hlvl := hf.head.lvl
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000a304_spec hf.pc (by
    rv_eval [hsp, h200]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact validAccess_one (by addr_omega [hM])
      | addr_omega [hRb, hrst, hb]
      | exact validAccess_one (by addr_omega [hsm, hb])
      | exact stack_valid hpre (Or.inl rfl) (by addr_omega [hb]) (by addr_omega [hb])
          (by addr_omega [hb])
      | exact stack_valid hpre (Or.inr rfl) (by addr_omega [hb]) (by addr_omega [hb])
          (by addr_omega [hb]))
  have k₁ := b8000a304_keeps h₁
  have X : DFrame t t₁ fun a ↦ Within a (s.getReg .x2 - 928) 8 ∨ Within a (s.getReg .x2 - 912) 8 ∨
      Within a (s.getReg .x2 - 896) 8 ∨ Within a (s.getReg .x2 - 872) 8 ∨
      Within a (s.getReg .x2 - 808) 8 ∨ Within a (s.getReg .x2 - 792) 8 ∨
      Within a (s.getReg .x2 - 616) 32 :=
    (holds_dframe h₁).mono fun a ⟨k, hk, hw⟩ ↦ by
      simp only [b8000a304, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rv_eval [hsp] at hw
      all_goals first
        | exact Or.inl (by addr_omega [hw, hb])
        | exact Or.inr (Or.inl (by addr_omega [hw, hb]))
        | exact Or.inr (Or.inr (Or.inl (by addr_omega [hw, hb])))
        | exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [hw, hb]))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [hw, hb])))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [hw, hb]))))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [hw, hb]))))))
  have hroot : digestAt t₁ (s.getReg .x11) = digestAt t (s.getReg .x11) :=
    digest_keep X (root_bound hpre) fun y hy hw ↦ by
      rcases hw with hw | hw | hw | hw | hw | hw | hw <;> addr_omega [hy, hw, hrst, hb]
  have r0 : t₁.getMem (s.getReg .x11) = t.getMem (s.getReg .x11) := X _ fun i hi hw ↦ by
    rcases hw with hw | hw | hw | hw | hw | hw | hw <;> addr_omega [hi, hw, hrst, hb, hRb]
  have hlow : t₁.getMem (s.getReg .x2 - 592) &&& 0x00ffffffffffffff =
      t₁.getMem (s.getReg .x11) &&& 0x00ffffffffffffff := by
    have e : t₁.getMem (t.getReg .x2 + 448) = _ := h₁.mem_eq 2 (by decide) (by rv_eval []) rfl
    simp only [reduceMem, List.getElem_cons_succ, List.getElem_cons_zero, Sym.E.eval,
      Sym.BinOp.eval, Sym.UnOp.eval, Sym.LoadKind.fromWord] at e
    rw [show s.getReg .x2 - 592 = t.getReg .x2 + 448 by rw [hsp]; addr_omega [hb], e, r0,
      show t.getReg .x2 + 200#64 = s.getReg .x2 - 840 by rw [hsp]; addr_omega [hb], h200]
    exact low7 _ _
  have hreg (r : Reg) (hr : r ∈ [Reg.x1, .x2, .x5, .x6, .x8, .x9, .x17, .x22, .x23, .x25, .x26,
      .x27]) : t₁.getReg r = t.getReg r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact k₁ _ (by decide)
  have st (o : ℕ) (v : Word) (e : t₁.getMem (t.getReg .x2 + BitVec.ofNat 64 o) = v) (a : Word)
      (ha : a = s.getReg .x2 - 1040 + BitVec.ofNat 64 o) : t₁.getMem a = v := by
    rw [ha, show s.getReg .x2 - 1040 = t.getReg .x2 from hsp.symm]; exact e
  have hx6 : t.getReg .x6 = BitVec.ofNat 64 (Wl.folds ++ lf).length := hf.x6
  refine ⟨t₁, hr₁, {
    fo := hf
    fr := X
    regs := hreg
    x13 := by rw [b8000a304_x13 h₁, hf.x26, hx6]
    x16 := by rw [b8000a304_x16 h₁, hsp]; rv_eval [h200]
    m144 := st 144 _ (b8000a304_m_x2_144 h₁) _ (by addr_omega [hb])
    m168 := by rw [st 168 _ (b8000a304_m_x2_168 h₁) _ (by addr_omega [hb]), hf.x26, hx6]
    m440 := st 440 _ (b8000a304_m_x2_440 h₁) _ (by addr_omega [hb])
    m432 := by rw [st 432 _ (b8000a304_m_x2_432 h₁) _ (by addr_omega [hb]), hf.x17]
    m424 := st 424 _ (b8000a304_m_x2_424 h₁) _ (by addr_omega [hb])
    m112 := by rw [st 112 _ (b8000a304_m_x2_112 h₁) _ (by addr_omega [hb]), hx6]
    m128 := by rw [st 128 _ (b8000a304_m_x2_128 h₁) _ (by addr_omega [hb]), hf.x26]
    m248 := by rw [st 248 _ (b8000a304_m_x2_248 h₁) _ (by addr_omega [hb]), hf.x25]
    m232 := st 232 _ (b8000a304_m_x2_232 h₁) _ (by addr_omega [hb])
    low := hlow
    root := hroot }, fun he ↦ b8000a304_pc_not_taken h₁ ?_, fun he ↦ b8000a304_pc_taken h₁ ?_⟩
  · rw [hf.x5, hf.x1, he]
  · rw [hf.x5, hf.x1]
    intro h0
    exact he (by addr_omega [h0, hK, hlvl])

end Rv64Verifier.Proofs.Pcs.Vso
